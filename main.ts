// tiny-stack-vm: an interpreter for make.fun's tiny stack ISA (version 1).
// One run answers the whole set: for every <id> in the input dir it executes
// <id>/program.bin against <id>/input.bin and writes <id>/stdout.bin (the
// exact bytes written) and <id>/exit.txt (the HALT/EXIT code, or a trap's
// code). Machine: wrapping 32-bit integers, data stack <= 256 values, call
// stack <= 64 return addresses, 256 words of memory, <= 1,000,000 steps.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Per-opcode tables indexed by the opcode byte: IMM = immediate length
// (-1: no such opcode), POPN/PUSHN = the stack counts the pre-step check
// uses. The arithmetic block 0x10..0x22 shares one shape (pops 2, pushes
// 1, no immediate) with two unary exceptions; the rest are set by group.
const IMM = new Int8Array(256).fill(-1);
const POPN = new Int8Array(256), PUSHN = new Int8Array(256);
for (let op = 0x10; op <= 0x22; op++) { IMM[op] = 0; POPN[op] = 2; PUSHN[op] = 1; }
IMM[0x1f] = -1; // hole in the block: no such opcode
POPN[0x17] = POPN[0x1b] = 1; // NEG, NOT are unary
for (const op of [0x00, 0x34, 0x52]) IMM[op] = 0;
for (const op of [0x03, 0x04, 0x40, 0x50, 0x51, 0x53]) { IMM[op] = 0; POPN[op] = 1; }
for (const op of [0x05, 0x06, 0x41]) { IMM[op] = 0; POPN[op] = 2; }
IMM[0x07] = 0; POPN[0x07] = 3;
IMM[0x01] = 1; IMM[0x02] = 4;
for (const op of [0x30, 0x31, 0x32, 0x33]) IMM[op] = 2;
POPN[0x31] = POPN[0x32] = 1; // JZ, JNZ pop their condition
PUSHN[0x01] = PUSHN[0x02] = PUSHN[0x40] = PUSHN[0x52] = 1;
PUSHN[0x04] = 2; PUSHN[0x05] = 2; PUSHN[0x06] = 3; PUSHN[0x07] = 3;

// Runs one program to its end; returns its output (kept even when it
// traps) and exit code. dispatch() returns on HALT/EXIT, throws traps.
function execute(prog, input) {
  const size = prog.length;
  const stk = new Int32Array(256), calls = new Int32Array(64);
  const mem = new Int32Array(256), out = new Uint8Array(65_536);
  let sp = 0, csp = 0, pc = 0, used = 0, inAt = 0, steps = 0;

  function dispatch() {
    for (;;) {
      if (steps === 1_000_000) throw 10;
      if (pc < 0 || pc >= size) throw 9;
      const op = prog[pc], imm = IMM[op];
      if (imm < 0) throw 5;
      if (pc + imm >= size) throw 9;
      if (sp < POPN[op]) throw 2;
      if (sp - POPN[op] + PUSHN[op] > 256) throw 3;
      steps++;
      pc += 1 + imm; // fall-through; jumps and calls overwrite pc
      switch (op) {
        case 0x00: return 0;
        case 0x01: stk[sp++] = (prog[pc - 1] << 24) >> 24; break;
        case 0x02:
          stk[sp++] = prog[pc - 4] | (prog[pc - 3] << 8) | (prog[pc - 2] << 16) | (prog[pc - 1] << 24);
          break;
        case 0x03: sp--; break;
        case 0x04: stk[sp] = stk[sp - 1]; sp++; break;
        case 0x05: { // SWAP
          const t = stk[sp - 1]; stk[sp - 1] = stk[sp - 2]; stk[sp - 2] = t; break;
        }
        case 0x06: stk[sp] = stk[sp - 2]; sp++; break;
        case 0x07: { // ROT: ( a b c -- b c a )
          const a = stk[sp - 3];
          stk[sp - 3] = stk[sp - 2]; stk[sp - 2] = stk[sp - 1]; stk[sp - 1] = a;
          break;
        }
        case 0x17: stk[sp - 1] = -stk[sp - 1]; break; // NEG
        case 0x1b: stk[sp - 1] = ~stk[sp - 1]; break; // NOT
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
        case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
        case 0x20: case 0x21: case 0x22: { // binary: ( a b -- r ), b on top
          const b = stk[sp - 1], a = stk[sp - 2];
          let r;
          if (op === 0x10) r = (a + b) | 0;
          else if (op === 0x11) r = (a - b) | 0;
          else if (op === 0x12) r = Math.imul(a, b); // low 32 bits, exact
          else if (op === 0x13) { if (b === 0) throw 4; r = (a / b) | 0; } // DIV: truncates; INT_MIN/-1 wraps back
          else if (op === 0x14) { if (b === 0) throw 4; r = (a % b) | 0; } // MOD: sign of a; x % -1 is 0
          else if (op === 0x15) { if (b === 0) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
          else if (op === 0x16) { if (b === 0) throw 4; r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
          else if (op === 0x18) r = a & b;
          else if (op === 0x19) r = a | b;
          else if (op === 0x1a) r = a ^ b;
          else if (op === 0x1c) r = a << (b & 31);
          else if (op === 0x1d) r = a >> (b & 31);
          else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
          else if (op === 0x20) r = a === b ? 1 : 0;
          else if (op === 0x21) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
          sp--; stk[sp - 1] = r;
          break;
        }
        case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
          const rel = ((prog[pc - 2] | (prog[pc - 1] << 8)) << 16) >> 16;
          let take = op === 0x30;
          if (!take) { const v = stk[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
          if (take) pc += rel;
          break;
        }
        case 0x33: // CALL, unsigned absolute target
          if (csp === 64) throw 7;
          calls[csp++] = pc;
          pc = prog[pc - 2] | (prog[pc - 1] << 8);
          break;
        case 0x34:
          if (csp === 0) throw 8;
          pc = calls[--csp];
          break;
        case 0x40: { // LOAD
          const addr = stk[sp - 1];
          if (addr < 0 || addr >= 256) throw 6;
          stk[sp - 1] = mem[addr];
          break;
        }
        case 0x41: { // STORE
          const addr = stk[sp - 1];
          if (addr < 0 || addr >= 256) throw 6;
          mem[addr] = stk[sp - 2];
          sp -= 2;
          break;
        }
        case 0x50: { // PRINT, decimal; writes nothing when it traps 11
          const text = String(stk[sp - 1]);
          if (used + text.length > 65_536) throw 11;
          sp--;
          for (let i = 0; i < text.length; i++) out[used++] = text.charCodeAt(i);
          break;
        }
        case 0x51: // PUTC, low byte
          if (used === 65_536) throw 11;
          out[used++] = stk[--sp] & 255;
          break;
        case 0x52: stk[sp++] = inAt < input.length ? input[inAt++] : -1; break;
        case 0x53: return stk[--sp] & 255; // EXIT
      }
    }
  }

  let code;
  try { code = dispatch(); } catch (trapCode) { code = trapCode; }
  return { bytes: out.slice(0, used), code };
}

for (const id of readdirSync(IN_DIR).sort()) {
  const prog = readFileSync(join(IN_DIR, id, 'program.bin'));
  const input = readFileSync(join(IN_DIR, id, 'input.bin'));
  const { bytes, code } = execute(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${code}\n`);
}
