import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// [imm,pops,pushes] per opcode byte; null = unknown opcode (trap 5)
const M = new Array(256).fill(null);
const d = (o, i, p, q) => { M[o] = [i, p, q]; };
d(0, 0, 0, 0); d(1, 1, 0, 1); d(2, 4, 0, 1); d(3, 0, 1, 0); d(4, 0, 1, 2);
d(5, 0, 2, 2); d(6, 0, 2, 3); d(7, 0, 3, 3); d(0x17, 0, 1, 1); d(0x1b, 0, 1, 1);
for (const o of [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]) d(o, 0, 2, 1);
d(0x30, 2, 0, 0); d(0x31, 2, 1, 0); d(0x32, 2, 1, 0); d(0x33, 2, 0, 0); d(0x34, 0, 0, 0);
d(0x40, 0, 1, 1); d(0x41, 0, 2, 0); d(0x50, 0, 1, 0); d(0x51, 0, 1, 0); d(0x52, 0, 0, 1); d(0x53, 0, 1, 0);
function run(P, N) {
  const S = new Int32Array(256), C = new Int32Array(64), E = new Int32Array(256), O = Buffer.allocUnsafe(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const fin = c => ({ o: Buffer.from(O.subarray(0, ol)), c });
  for (;;) {
    if (st === 1e6) return fin(10);
    if (pc < 0 || pc >= P.length) return fin(9);
    const m = M[P[pc]];
    if (!m) return fin(5);
    if (pc + m[0] >= P.length) return fin(9);
    st++;
    const nx = pc + 1 + m[0];
    if (sp < m[1]) return fin(2);
    if (sp - m[1] + m[2] > 256) return fin(3);
    const op = P[pc]; pc = nx;
    if (op === 0) return fin(0);
    if (op === 1) S[sp++] = (P[nx - 1] << 24) >> 24;
    else if (op === 2) S[sp++] = P[nx - 4] | P[nx - 3] << 8 | P[nx - 2] << 16 | P[nx - 1] << 24;
    else if (op === 3) sp--;
    else if (op === 4) { S[sp] = S[sp - 1]; sp++; }
    else if (op === 5) { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; }
    else if (op === 6) { S[sp] = S[sp - 2]; sp++; }
    else if (op === 7) { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; }
    else if (op === 0x17) S[sp - 1] = -S[sp - 1] | 0;
    else if (op === 0x1b) S[sp - 1] = ~S[sp - 1];
    else if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = S[sp - 1], a = S[sp - 2]; let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (!b) return fin(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 0x14) { if (!b) return fin(4); r = b === -1 ? 0 : a % b | 0; }
      else if (op === 0x15) { if (!b) return fin(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 0x16) { if (!b) return fin(4); r = (a >>> 0) % (b >>> 0) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      S[sp - 2] = r; sp--;
    }
    else if (op >= 0x30 && op <= 0x32) {
      const rel = ((P[nx - 2] | P[nx - 1] << 8) << 16) >> 16;
      let take = true;
      if (op !== 0x30) { const v = S[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
      if (take) pc = nx + rel;
    }
    else if (op === 0x33) { if (cp === 64) return fin(7); C[cp++] = nx; pc = P[nx - 2] | P[nx - 1] << 8; }
    else if (op === 0x34) { if (!cp) return fin(8); pc = C[--cp]; }
    else if (op === 0x40) { const a = S[sp - 1]; if (a < 0 || a > 255) return fin(6); S[sp - 1] = E[a]; }
    else if (op === 0x41) { const a = S[sp - 1]; if (a < 0 || a > 255) return fin(6); E[a] = S[sp - 2]; sp -= 2; }
    else if (op === 0x50) {
      const s = String(S[sp - 1]);
      if (ol + s.length > 65536) return fin(11);
      for (let i = 0; i < s.length; i++) O[ol + i] = s.charCodeAt(i);
      ol += s.length; sp--;
    }
    else if (op === 0x51) { if (ol + 1 > 65536) return fin(11); O[ol++] = S[--sp] & 255; }
    else if (op === 0x52) S[sp++] = ip < N.length ? N[ip++] : -1;
    else if (op === 0x53) return fin(S[--sp] & 255);
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let inp; try { inp = readFileSync(join(I, id, 'input.bin')); } catch { inp = Buffer.alloc(0); }
  const r = run(readFileSync(join(I, id, 'program.bin')), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), String(r.c));
}
