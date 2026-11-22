// tiny-stack-vm — an interpreter for make.fun's tiny stack ISA, version 1.
// For every instance <id> in the input directory it writes the answer pair
// (stdout.bin, exit.txt) to the output directory, byte for byte what the
// reference VM produces. Directories: MAKEFUN_INPUT_DIR /
// MAKEFUN_OUTPUT_DIR if set, else /input and /output.

import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";

// Per-opcode facts, indexed by opcode byte: IMM = immediate bytes following
// the opcode (-1: the byte names no opcode), NEED = values popped (checked
// before the instruction runs), NET = pushes minus pops (checked against
// the 256-value stack cap).
const IMM = new Int8Array(256).fill(-1);
const NEED = new Int8Array(256);
const NET = new Int8Array(256);
function spec(op: number, imm: number, pops: number, pushes: number) {
  IMM[op] = imm; NEED[op] = pops; NET[op] = pushes - pops;
}
// HALT, PUSH8, PUSH32, POP, DUP, SWAP, OVER, ROT
spec(0x00, 0, 0, 0); spec(0x01, 1, 0, 1); spec(0x02, 4, 0, 1); spec(0x03, 0, 1, 0);
spec(0x04, 0, 1, 2); spec(0x05, 0, 2, 2); spec(0x06, 0, 2, 3); spec(0x07, 0, 3, 3);
// The two-operand group, listed byte by byte on purpose: 0x10..0x22 is NOT
// all opcodes — 0x1f names nothing and must trap 5, and 0x17 / 0x1b are the
// one-operand NEG / NOT, specified below.
for (const op of [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]) spec(op, 0, 2, 1);
spec(0x17, 0, 1, 1); // NEG
spec(0x1b, 0, 1, 1); // NOT
// JMP, JZ, JNZ, CALL, RET, LOAD, STORE, PRINT, PUTC, IN, EXIT
spec(0x30, 2, 0, 0); spec(0x31, 2, 1, 0); spec(0x32, 2, 1, 0); spec(0x33, 2, 0, 0);
spec(0x34, 0, 0, 0); spec(0x40, 0, 1, 1); spec(0x41, 0, 2, 0); spec(0x50, 0, 1, 0);
spec(0x51, 0, 1, 0); spec(0x52, 0, 0, 1); spec(0x53, 0, 1, 0);

// The two-operand instructions: a is the deeper value, b the top of stack.
function binop(op: number, a: number, b: number): number {
  switch (op) {
    case 0x10: return (a + b) | 0;
    case 0x11: return (a - b) | 0;
    case 0x12: return Math.imul(a, b);
    case 0x13: if (!b) throw 4; return a === -2147483648 && b === -1 ? a : (a / b) | 0;
    case 0x14: if (!b) throw 4; return b === -1 ? 0 : (a % b) | 0;
    case 0x15: if (!b) throw 4; return Math.floor((a >>> 0) / (b >>> 0)) | 0;
    case 0x16: if (!b) throw 4; return ((a >>> 0) % (b >>> 0)) | 0;
    case 0x18: return a & b;
    case 0x19: return a | b;
    case 0x1a: return a ^ b;
    case 0x1c: return a << (b & 31); // shift counts use only the low 5 bits
    case 0x1d: return a >> (b & 31);
    case 0x1e: return (a >>> (b & 31)) | 0;
    case 0x20: return a === b ? 1 : 0;
    case 0x21: return a < b ? 1 : 0;
    case 0x22: return (a >>> 0) < (b >>> 0) ? 1 : 0;
  }
  return 0; // unreachable: only the opcodes above are routed here
}

// Runs one program to its end; returns its output bytes and exit code.
// Traps are thrown as their numeric code and caught at the bottom.
function run(prog: Uint8Array, input: Uint8Array) {
  const n = prog.length;
  const st = new Int32Array(256);
  let sp = 0;
  const ret = new Int32Array(64);
  let rsp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0, ip = 0, pc = 0, steps = 0;
  const finish = (code: number) => ({ bytes: out.slice(0, olen), code });
  try {
    for (;;) {
      // The pre-step checks, in the reference VM's order.
      if (steps === 1000000) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const op = prog[pc];
      const imm = IMM[op];
      if (imm < 0) throw 5;
      if (pc + imm >= n) throw 9; // the immediate would run past the end
      steps++;
      if (sp < NEED[op]) throw 2;
      if (sp + NET[op] > 256) throw 3;
      pc += 1 + imm; // pc now names the next instruction
      switch (op) {
        case 0x00: return finish(0);
        case 0x01: st[sp++] = (prog[pc - 1] << 24) >> 24; break; // PUSH8, sign-extended
        case 0x02: st[sp++] = prog[pc - 4] | (prog[pc - 3] << 8) | (prog[pc - 2] << 16) | (prog[pc - 1] << 24); break;
        case 0x03: sp--; break;
        case 0x04: st[sp] = st[sp - 1]; sp++; break;
        case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
        case 0x06: st[sp] = st[sp - 2]; sp++; break;
        case 0x07: { // ROT: ( a b c -- b c a )
          const a = st[sp - 3];
          st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a;
          break;
        }
        case 0x17: st[sp - 1] = -st[sp - 1] | 0; break;
        case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
        case 0x30: case 0x31: case 0x32: { // jumps: target = next + signed offset
          const off = ((prog[pc - 2] | (prog[pc - 1] << 8)) << 16) >> 16;
          let go = op === 0x30;
          if (!go) { const v = st[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
          if (go) pc += off;
          break;
        }
        case 0x33: // CALL: the immediate is an absolute address, unsigned
          if (rsp === 64) throw 7;
          ret[rsp++] = pc;
          pc = prog[pc - 2] | (prog[pc - 1] << 8);
          break;
        case 0x34: if (rsp === 0) throw 8; pc = ret[--rsp]; break;
        case 0x40: { // LOAD
          const addr = st[sp - 1];
          if (addr < 0 || addr > 255) throw 6;
          st[sp - 1] = mem[addr];
          break;
        }
        case 0x41: { // STORE: ( v addr -- ), the address is on top
          const addr = st[sp - 1];
          if (addr < 0 || addr > 255) throw 6;
          mem[addr] = st[sp - 2];
          sp -= 2;
          break;
        }
        case 0x50: { // PRINT: the value in decimal ASCII, all or nothing
          const s = String(st[sp - 1]);
          if (olen + s.length > 65536) throw 11;
          for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
          sp--;
          break;
        }
        case 0x51: if (olen === 65536) throw 11; out[olen++] = st[--sp] & 255; break;
        case 0x52: st[sp++] = ip < input.length ? input[ip++] : -1; break;
        case 0x53: return finish(st[sp - 1] & 255);
        default: { // every opcode not named above is a two-operand operation
          const b = st[sp - 1], a = st[sp - 2];
          st[sp - 2] = binop(op, a, b);
          sp--;
        }
      }
    }
  } catch (e) {
    if (typeof e === "number") return finish(e); // a trap: its code is the exit code
    throw e;
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const O = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
for (const id of readdirSync(I).sort()) {
  const prog = readFileSync(`${I}/${id}/program.bin`);
  const input = readFileSync(`${I}/${id}/input.bin`);
  const { bytes, code } = run(prog, input);
  mkdirSync(`${O}/${id}`, { recursive: true });
  writeFileSync(`${O}/${id}/stdout.bin`, bytes);
  writeFileSync(`${O}/${id}/exit.txt`, code + "\n");
}
