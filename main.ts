// Tiny stack VM (ISA: kit/program/generator/subject/ISA.md). One run answers a
// whole set: /input/<id>/program.bin + input.bin -> /output/<id>/stdout.bin + exit.txt.
// 32-bit wrapping arithmetic, 256-value stack, 64-deep call stack, 256 words of
// memory, ten traps with their own exit codes, 1,000,000-step / 65,536-byte limits.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Pops / pushes per opcode byte ('.' = unknown opcode), indexes 0..83 (0x53).
const POPS = '00011223........222222212221222.222.............01100...........12..............1101';
const PUSHES = '01102233........111111111111111.111.............00000...........10..............0010';
const IMM = new Array(84).fill(0);
IMM[1] = 1; IMM[2] = 4; IMM[48] = IMM[49] = IMM[50] = IMM[51] = 2;

function run(program: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = program.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let inPos = 0;
  let pc = 0;
  let steps = 0;
  const finish = (code: number): { out: Uint8Array; code: number } => ({ out: out.slice(0, olen), code });

  for (;;) {
    if (steps === 1000000) return finish(10); // step limit, checked first
    if (pc < 0 || pc >= n) return finish(9); // pc outside the program
    const op = program[pc];
    const pops = POPS.charCodeAt(op) - 48;
    if (pops < 0 || pops > 3) return finish(5); // unknown opcode
    const pushes = PUSHES.charCodeAt(op) - 48;
    const imm = IMM[op];
    if (pc + imm >= n) return finish(9); // immediate cut off by the program's end
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return finish(2); // stack underflow
    if (sp - pops + pushes > 256) return finish(3); // stack overflow
    pc = next;
    switch (op) {
      case 0x00: return finish(0); // HALT
      case 0x01: D[sp++] = (program[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: // PUSH32, little-endian signed
        D[sp++] = program[next - 4] | (program[next - 3] << 8) | (program[next - 2] << 16) | (program[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG (wraps)
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // exact low 32 bits
          case 0x13: // DIV, truncated toward zero; INT_MIN / -1 is INT_MIN
            if (b === 0) return finish(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD, sign of a; x % -1 is 0
            if (b === 0) return finish(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU, unsigned quotient read back as signed
            if (b === 0) return finish(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU, unsigned remainder read back as signed
            if (b === 0) return finish(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // only the low 5 bits of the count
          case 0x1d: r = a >> (b & 31); break; // arithmetic shift
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical shift
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU, unsigned
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset from next
        const rel = ((program[next - 2] | (program[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit target
        if (csp === 64) return finish(7);
        C[csp++] = next;
        pc = program[next - 2] | (program[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return finish(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return finish(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= 256) return finish(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no padding, no newline
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return finish(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (olen + 1 > 65536) return finish(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN: next input byte, -1 once the input is used up
        D[sp++] = inPos < input.length ? input[inPos++] : -1;
        break;
      case 0x53: return finish(D[--sp] & 255); // EXIT: low byte is the code
      default: return finish(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
