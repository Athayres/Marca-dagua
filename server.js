/**
 * Detector de marca d'água – serviço pequeno para o Render (Node.js + ffmpeg).
 * Feito para ser chamado pelo addon da Cloudflare (Worker), que decide o que fazer com a resposta.
 *
 *   GET /health                                   -> { ok: true }   (use para acordar o serviço)
 *   GET /analisar?u=<link do vídeo>[&min=<duração em minutos>]
 *       cabeçalho  X-Segredo: <MARCA_SEGREDO>     (ou ?k=<MARCA_SEGREDO>)
 *   resposta 200: { status: 'marca' | 'limpo' | 'indeterminado', regiao?, score?, texto?, cache: bool, ms }
 *       'marca' = suspeita forte de marca fixa (logo/texto) | 'limpo' = não achou | 'indeterminado' = não deu para analisar
 *   outros: 401 sem/errado segredo | 400 link inválido | 403 endereço interno bloqueado | 429 ocupado (tente depois)
 *
 * Variáveis (Render > Environment):
 *   MARCA_SEGREDO (obrigatória)   MARCA_LIMITE (padrão 0.035)   MARCA_QUADRO_MS (padrão 20000)
 *   MAX_PARALELO (padrão 2: análises ao mesmo tempo)   PERMITIR_LOCAL=1 (só para testes: libera 127.0.0.1)
 *
 * É uma SUSPEITA por imagem, não uma prova: logo de canal e legenda fixa em todos os quadros também podem ser marcados.
 */
import http from 'node:http';
import dns from 'node:dns/promises';
import net from 'node:net';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36';
const SEGREDO = String(process.env.MARCA_SEGREDO || '').trim();
const MARCA_LIMITE = Number(process.env.MARCA_LIMITE) > 0 ? Number(process.env.MARCA_LIMITE) : 0.035;
const MARCA_QUADRO_MS = Number(process.env.MARCA_QUADRO_MS) >= 3000 ? Math.min(60000, Number(process.env.MARCA_QUADRO_MS)) : 20000;
const MAX_PARALELO = Math.max(1, Math.min(6, Number(process.env.MAX_PARALELO) || 2));
const FILA_MAX = 8;
const TTL = 24 * 3600 * 1000;

let FFMPEG = 'ffmpeg';
try { const m = await import('ffmpeg-static'); if (m && m.default) FFMPEG = m.default; } catch { /* usa o ffmpeg do sistema, se houver */ }
let ffmpegPronto;
function ffmpegOk() {
  if (!ffmpegPronto) {
    ffmpegPronto = new Promise((ok) => {
      try { const p = spawn(FFMPEG, ['-version'], { stdio: 'ignore' }); p.on('error', () => ok(false)); p.on('close', (c) => ok(c === 0)); } catch { ok(false); }
    });
  }
  return ffmpegPronto;
}

const WM_W = 320;
const WM_H = 180;

// 1 quadro em tons de cinza, WM_W x WM_H, no segundo "seg" (o ffmpeg busca por Range, sem baixar o filme)
function quadroCinza(u, seg, limiteMs) {
  return new Promise((resolve) => {
    let p;
    try {
      p = spawn(FFMPEG, ['-hide_banner', '-loglevel', 'error', '-nostdin', '-user_agent', UA, '-probesize', '3000000', '-analyzeduration', '3000000',
        '-ss', seg.toFixed(2), '-i', u, '-an', '-sn', '-frames:v', '1', '-vf', `scale=${WM_W}:${WM_H},format=gray`, '-f', 'rawvideo', '-'],
      { stdio: ['ignore', 'pipe', 'ignore'] });
    } catch { return resolve(null); }
    const partes = [];
    const t = setTimeout(() => { try { p.kill('SIGKILL'); } catch { /* já saiu */ } }, limiteMs);
    p.stdout.on('data', (d) => partes.push(d));
    p.on('error', () => { clearTimeout(t); resolve(null); });
    p.on('close', () => { clearTimeout(t); const b = Buffer.concat(partes); resolve(b.length === WM_W * WM_H ? new Uint8Array(b) : null); });
  });
}

// Marca fixa = pixels com BORDA do mesmo tipo (mesma direção) no mesmo lugar em quase todos os quadros, enquanto o centro muda.
// Linhas/colunas inteiras fixas (barras pretas, molduras) são descartadas. Devolve { status: 'marca'|'limpo'|'indeterminado', ... }
function analisarQuadros(quadros, w, h, limite) {
  const n = quadros.length;
  if (n < 5) return { status: 'indeterminado', texto: 'poucos quadros lidos' };
  const N = w * h;
  const soma = new Float32Array(N);
  const soma2 = new Float32Array(N);
  const dirs = new Uint8Array(N * 4); // por pixel: quantos quadros tiveram borda de cada direção (x+, x-, y+, y-)
  for (const f of quadros) {
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const i = y * w + x;
        const v = f[i];
        soma[i] += v; soma2[i] += v * v;
        const dx = x < w - 1 ? f[i + 1] - v : 0;
        const dy = y < h - 1 ? f[i + w] - v : 0;
        if (Math.abs(dx) + Math.abs(dy) >= 14) dirs[i * 4 + (Math.abs(dx) >= Math.abs(dy) ? (dx > 0 ? 0 : 1) : (dy > 0 ? 2 : 3))]++;
      }
    }
  }
  const cx0 = Math.floor(w * 0.25), cx1 = Math.floor(w * 0.75), cy0 = Math.floor(h * 0.30), cy1 = Math.floor(h * 0.70);
  const estavel = new Uint8Array(N);
  let sdCentro = 0, nCentro = 0;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      const m = soma[i] / n;
      const sd = Math.sqrt(Math.max(0, soma2[i] / n - m * m));
      if (Math.max(dirs[i * 4], dirs[i * 4 + 1], dirs[i * 4 + 2], dirs[i * 4 + 3]) >= n - 1) estavel[i] = 1; // borda do mesmo tipo (mesma direção) no mesmo lugar em quase todos os quadros
      if (x >= cx0 && x < cx1 && y >= cy0 && y < cy1) { sdCentro += sd; nCentro++; }
    }
  }
  sdCentro /= nCentro || 1;
  if (sdCentro < 10) return { status: 'indeterminado', texto: 'imagem quase parada nos quadros lidos' };
  for (let y = 0; y < h; y++) { // linhas inteiras fixas
    let c = 0; for (let x = 0; x < w; x++) c += estavel[y * w + x];
    if (c > w * 0.5) for (let x = 0; x < w; x++) estavel[y * w + x] = 0;
  }
  for (let x = 0; x < w; x++) { // colunas inteiras fixas
    let c = 0; for (let y = 0; y < h; y++) c += estavel[y * w + x];
    if (c > h * 0.5) for (let y = 0; y < h; y++) estavel[y * w + x] = 0;
  }
  const contar = (x0, y0, x1, y1) => {
    const ax = Math.floor(w * x0), bx = Math.floor(w * x1), ay = Math.floor(h * y0), by = Math.floor(h * y1);
    let c = 0;
    for (let y = ay; y < by; y++) for (let x = ax; x < bx; x++) c += estavel[y * w + x];
    return { c, area: Math.max(1, (bx - ax) * (by - ay)) };
  };
  const base = (() => { const r = contar(0.25, 0.30, 0.75, 0.70); return r.c / r.area; })();
  const regioes = [
    ['no canto superior esquerdo', 0, 0, 0.32, 0.30], ['no canto superior direito', 0.68, 0, 1, 0.30],
    ['no canto inferior esquerdo', 0, 0.70, 0.32, 1], ['no canto inferior direito', 0.68, 0.70, 1, 1],
    ['no topo, ao centro', 0.34, 0, 0.66, 0.18], ['embaixo, ao centro', 0.34, 0.82, 0.66, 1],
  ];
  let melhor = null;
  for (const [nome, x0, y0, x1, y1] of regioes) {
    const r = contar(x0, y0, x1, y1);
    const score = r.c / r.area;
    if (r.c >= 25 && score >= limite && score >= 4 * Math.max(base, 0.003) && (!melhor || score > melhor.score)) melhor = { regiao: nome, score };
  }
  if (melhor) return { status: 'marca', regiao: melhor.regiao, score: Number(melhor.score.toFixed(3)), texto: `possível marca d'água fixa ${melhor.regiao}` };
  return { status: 'limpo', score: 0 };
}


// ---------- duração (quando o chamador não informa) ----------
function duracaoMin(u) {
  return new Promise((resolve) => {
    let p;
    try { p = spawn(FFMPEG, ['-hide_banner', '-nostdin', '-user_agent', UA, '-i', u], { stdio: ['ignore', 'ignore', 'pipe'] }); } catch { return resolve(null); }
    let err = '';
    const t = setTimeout(() => { try { p.kill('SIGKILL'); } catch { /* já saiu */ } }, 15000);
    p.stderr.on('data', (d) => { if (err.length < 20000) err += d; });
    p.on('error', () => { clearTimeout(t); resolve(null); });
    p.on('close', () => {
      clearTimeout(t);
      const m = /Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)/.exec(err);
      resolve(m ? (Number(m[1]) * 3600 + Number(m[2]) * 60 + Number(m[3])) / 60 : null);
    });
  });
}

// ---------- segurança: não deixa usar o serviço para abrir endereços internos ----------
function ipInterno(ip) {
  if (net.isIPv4(ip)) {
    const [a, b] = ip.split('.').map(Number);
    return a === 10 || a === 127 || a === 0 || (a === 169 && b === 254) || (a === 172 && b >= 16 && b <= 31) || (a === 192 && b === 168) || (a === 100 && b >= 64 && b <= 127);
  }
  const v = ip.toLowerCase();
  return v === '::1' || v === '::' || v.startsWith('fc') || v.startsWith('fd') || v.startsWith('fe80') || v.startsWith('::ffff:127.') || v.startsWith('::ffff:10.') || v.startsWith('::ffff:192.168.');
}
async function hostPermitido(u) {
  if (process.env.PERMITIR_LOCAL === '1') return true;
  try {
    const { hostname } = new URL(u);
    if (net.isIP(hostname)) return !ipInterno(hostname);
    const todos = await dns.lookup(hostname, { all: true });
    return todos.length > 0 && todos.every((x) => !ipInterno(x.address));
  } catch { return false; }
}

// ---------- fila (poucas análises ao mesmo tempo: o plano gratuito é fraco) ----------
let rodando = 0;
const fila = [];
function entrar() {
  if (rodando < MAX_PARALELO) { rodando++; return Promise.resolve(true); }
  if (fila.length >= FILA_MAX) return Promise.resolve(false);
  return new Promise((ok) => fila.push(ok));
}
function sair() {
  const prox = fila.shift();
  if (prox) prox(true); else rodando--;
}

// ---------- cache e análise ----------
const cache = new Map();   // link -> { t, r }
const emAndamento = new Map(); // link -> Promise (pedidos repetidos esperam a mesma análise)
function cacheLer(u) {
  const e = cache.get(u);
  if (e && Date.now() - e.t < TTL) return e.r;
  if (e) cache.delete(u);
  return undefined;
}
function cacheGravar(u, r) { if (cache.size >= 3000) cache.clear(); cache.set(u, { t: Date.now(), r }); }

async function analisar(u, minInformado) {
  const c = cacheLer(u);
  if (c) return Object.assign({}, c, { cache: true });
  if (emAndamento.has(u)) return emAndamento.get(u);
  const tarefa = (async () => {
    if (!(await entrar())) return { status: 'ocupado' };
    try {
      let min = Number(minInformado) > 0 ? Number(minInformado) : await duracaoMin(u);
      if (!(min > 0)) return { status: 'indeterminado', texto: 'não deu para ler a duração do vídeo' };
      const pontos = [0.10, 0.22, 0.34, 0.46, 0.58, 0.70, 0.82];
      const seg = min * 60;
      const quadros = [];
      let k = 0;
      const trab = async () => { while (k < pontos.length) { const i = k++; const q = await quadroCinza(u, seg * pontos[i], MARCA_QUADRO_MS); if (q) quadros.push(q); } };
      await Promise.all([trab(), trab()]);
      const r = analisarQuadros(quadros, WM_W, WM_H, MARCA_LIMITE);
      if (r.status !== 'indeterminado') cacheGravar(u, r); // leitura que falhou não fica guardada
      return Object.assign({}, r, { cache: false });
    } finally { sair(); }
  })();
  emAndamento.set(u, tarefa);
  try { return await tarefa; } finally { emAndamento.delete(u); }
}

// ---------- servidor ----------
function iniciar() {
  if (!SEGREDO) console.warn('ATENÇÃO: defina MARCA_SEGREDO; sem ele o serviço recusa todos os pedidos.');
  const json = (res, cod, obj) => { res.writeHead(cod, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(JSON.stringify(obj)); };
  const servidor = http.createServer(async (req, res) => {
    try {
      const url = new URL(req.url, 'http://x');
      if (url.pathname === '/health') return json(res, 200, { ok: true, ffmpeg: await ffmpegOk(), rodando, fila: fila.length });
      if (url.pathname !== '/analisar') return json(res, 404, { erro: 'não encontrado' });
      const dado = String(req.headers['x-segredo'] || url.searchParams.get('k') || '');
      if (!SEGREDO || dado.length !== SEGREDO.length || !dado.split('').every((ch, i) => ch === SEGREDO[i])) return json(res, 401, { erro: 'segredo inválido' });
      const u = String(url.searchParams.get('u') || '');
      if (!/^https?:\/\//i.test(u) || u.length > 4000) return json(res, 400, { erro: 'link inválido' });
      if (!(await hostPermitido(u))) return json(res, 403, { erro: 'endereço não permitido' });
      if (!(await ffmpegOk())) return json(res, 200, { status: 'indeterminado', texto: 'ffmpeg indisponível no servidor', cache: false });
      const t0 = Date.now();
      const r = await analisar(u, url.searchParams.get('min'));
      if (r.status === 'ocupado') return json(res, 429, { erro: 'ocupado, tente depois' });
      return json(res, 200, Object.assign({}, r, { ms: Date.now() - t0 }));
    } catch (e) {
      console.error(e);
      return json(res, 500, { erro: 'falha interna' });
    }
  });
  const porta = Number(process.env.PORT || 10000);
  servidor.listen(porta, '0.0.0.0', () => {
    console.log(`Detector de marca d'água no ar na porta ${porta}`);
    ffmpegOk().then((ok) => console.log(ok ? `ffmpeg pronto (${FFMPEG})` : 'ffmpeg NÃO encontrado'));
  });
  return servidor;
}

export { analisar, analisarQuadros, iniciar };
if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) iniciar();
