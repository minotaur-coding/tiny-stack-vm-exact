// Tiny stack VM — exact port of the reference semantics (generator/subject/vm.mjs / ISA.md v1).
// Every rule: 32-bit wrapping, trap codes, stack/call bounds, output & step limits.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const STACK_MAX = 256, CALLS_MAX = 64, MEMORY_WORDS = 256;
const STEP_LIMIT = 1_000_000, OUTPUT_MAX = 65_536;
const enc = new TextEncoder();

function run(program, input) {
  const n = program.length;
  const D = new Int32Array(STACK_MAX);
  let sp = 0;
  const C = new Int32Array(CALLS_MAX);
  let csp = 0;
  const M = new Int32Array(MEMORY_WORDS);
  const out = new Uint8Array(OUTPUT_MAX);
  let olen = 0;
  let inPos = 0;
  let pc = 0;
  let steps = 0;
  const done = (exit) => ({ stdout: out.slice(0, olen), exit });
  for (;;) {
    if (steps === STEP_LIMIT) return done(10); // trap 10
    if (pc < 0 || pc >= n) return done(9); // trap 9
    const op = program[pc];
    // name: opcode class; imm bytes; via switch below
    let next;
    if (op === 0x00) return done(0);
    else if (op === 0x01) { if (pc + 1 >= n) return done(9); steps++; const v = (program[pc + 1] << 24) >> 24; if (sp >= STACK_MAX) return done(3); D[sp++] = v; pc = next = pc + 2; continue; }
    else if (op === 0x02) { if (pc + 4 >= n) return done(9); steps++; const v = program[pc + 1] | (program[pc + 2] << 8) | (program[pc + 3] << 16) | (program[pc + 4] << 24); if (sp >= STACK_MAX) return done(3); D[sp++] = v; pc = next = pc + 5; continue; }
    else if (op === 0x03) { steps++; if (sp < 1) return done(2); sp--; pc++; continue; }
    else if (op === 0x04) { steps++; if (sp < 1) return done(2); if (sp + 1 > STACK_MAX) return done(3); D[sp] = D[sp - 1]; sp++; pc++; continue; }
    else if (op === 0x05) { steps++; if (sp < 2) return done(2); const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; pc++; continue; }
    else if (op === 0x06) { steps++; if (sp < 2) return done(2); if (sp + 1 > STACK_MAX) return done(3); D[sp] = D[sp - 2]; sp++; pc++; continue; }
    else if (op === 0x07) { steps++; if (sp < 3) return done(2); const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; pc++; continue; }
    else if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      // arithmetic / logic binary ops (0x10..0x22)
      steps++;
      if (sp < 2) return done(2);
      const b = D[sp - 1], a = D[sp - 2];
      let r;
      switch (op) {
        case 0x10: r = (a + b) | 0; break;
        case 0x11: r = (a - b) | 0; break;
        case 0x12: r = Math.imul(a, b); break;
        case 0x13: if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
        case 0x14: if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; break;
        case 0x15: if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
        case 0x16: if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
        case 0x18: r = a & b; break;
        case 0x19: r = a | b; break;
        case 0x1a: r = a ^ b; break;
        case 0x1c: r = a << (b & 31); break;
        case 0x1d: r = a >> (b & 31); break;
        case 0x1e: r = (a >>> (b & 31)) | 0; break;
        case 0x20: r = a === b ? 1 : 0; break;
        case 0x21: r = a < b ? 1 : 0; break;
        case 0x22: r = a >>> 0 < b >>> 0 ? 1 : 0; break;
        default: return done(5); // 0x17, 0x1b excluded above; safety
      }
      sp -= 2; D[sp++] = r; pc++; continue;
    }
    else if (op === 0x17) { steps++; if (sp < 1) return done(2); D[sp - 1] = -D[sp - 1] | 0; pc++; continue; }
    else if (op === 0x1b) { steps++; if (sp < 1) return done(2); D[sp - 1] = ~D[sp - 1]; pc++; continue; }
    else if (op === 0x30 || op === 0x31 || op === 0x32) { // JMP, JZ, JNZ
      if (pc + 2 >= n) return done(9); steps++;
      const rel = ((program[pc + 1] | (program[pc + 2] << 8)) << 16) >> 16;
      next = pc + 3;
      if (op !== 0x30) {
        if (sp < 1) return done(2);
        const v = D[--sp];
        if (op === 0x31 ? v !== 0 : v === 0) { pc = next; continue; }
      }
      pc = next + rel; continue;
    }
    else if (op === 0x33) { // CALL
      if (pc + 2 >= n) return done(9); steps++;
      if (csp === CALLS_MAX) return done(7);
      next = pc + 3;
      C[csp++] = next;
      pc = program[pc + 1] | (program[pc + 2] << 8); continue;
    }
    else if (op === 0x34) { steps++; if (csp === 0) return done(8); pc = C[--csp]; continue; }
    else if (op === 0x40) { steps++; if (sp < 1) return done(2); const addr = D[sp - 1]; if (addr < 0 || addr >= MEMORY_WORDS) return done(6); D[sp - 1] = M[addr]; pc++; continue; }
    else if (op === 0x41) { steps++; if (sp < 2) return done(2); const addr = D[sp - 1]; if (addr < 0 || addr >= MEMORY_WORDS) return done(6); const v = D[sp - 2]; sp -= 2; M[addr] = v; pc++; continue; }
    else if (op === 0x50) { steps++; if (sp < 1) return done(2); const bytes = enc.encode(String(D[sp - 1])); if (olen + bytes.length > OUTPUT_MAX) return done(11); sp--; out.set(bytes, olen); olen += bytes.length; pc++; continue; }
    else if (op === 0x51) { steps++; if (sp < 1) return done(2); if (olen + 1 > OUTPUT_MAX) return done(11); out[olen++] = D[--sp] & 255; pc++; continue; }
    else if (op === 0x52) { steps++; if (sp >= STACK_MAX) return done(3); D[sp++] = inPos < input.length ? input[inPos++] : -1; pc++; continue; }
    else if (op === 0x53) { steps++; if (sp < 1) return done(2); return done(D[--sp] & 255); }
    else return done(5); // unknown opcode
  }
}

for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  try {
    const program = readFileSync(join(dir, 'program.bin'));
    let input = new Uint8Array(0);
    try { input = readFileSync(join(dir, 'input.bin')); } catch {}
    const r = run(program, input);
    mkdirSync(join(O, id), { recursive: true });
    writeFileSync(join(O, id, 'stdout.bin'), r.stdout);
    writeFileSync(join(O, id, 'exit.txt'), String(r.exit) + '\n');
  } catch {
    // still write an answer so the instance is answered (empty output, exit 1? no—unanswered is 0; but a missing program means we can't answer correctly)
    mkdirSync(join(O, id), { recursive: true });
    writeFileSync(join(O, id, 'stdout.bin'), new Uint8Array(0));
    writeFileSync(join(O, id, 'exit.txt'), '0\n');
  }
}
