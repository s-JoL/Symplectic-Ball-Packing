#!/usr/bin/env node
// Static prerequisites only. Kernel proofs and the explicitness audit run separately.
import { readFileSync, readdirSync, existsSync } from 'node:fs';
import { join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../', import.meta.url));
let failures = 0;
const reject = message => { console.error(message); failures++; };

// Preserve offsets and newlines while removing Lean nested comments and strings.
export function leanCode(source) {
  let code = '', depth = 0, string = false;
  for (let i = 0; i < source.length; i++) {
    const c = source[i], pair = source.slice(i, i + 2);
    if (depth) {
      if (pair === '/-') { depth++; code += '  '; i++; }
      else if (pair === '-/') { depth--; code += '  '; i++; }
      else code += c === '\n' ? '\n' : ' ';
    } else if (string) {
      if (c === '\\') { code += '  '; i++; }
      else { if (c === '"') string = false; code += c === '\n' ? '\n' : ' '; }
    } else if (pair === '/-') { depth++; code += '  '; i++; }
    else if (pair === '--') {
      while (i < source.length && source[i] !== '\n') { code += ' '; i++; }
      if (i < source.length) code += '\n';
    } else if (c === '"') { string = true; code += ' '; }
    else code += c;
  }
  if (depth || string) throw new Error('unterminated Lean comment or string');
  return code;
}

if (process.argv[2] === '--self-test') {
  const { strict: assert } = await import('node:assert');
  const tokens = text => [...leanCode(text).matchAll(/[\p{L}\p{N}_']+/gu)].map(m => m[0]);
  assert(!tokens('/- sorry /- admit -/ unsafe -/\n-- axiom\ndef x := "sorry"').some(t =>
    ['sorry', 'admit', 'unsafe', 'axiom'].includes(t)));
  assert(tokens('theorem x : True := by /- nested /- proof -/ -/ sorry').includes('sorry'));
  assert(tokens('opaque hidden : Nat').includes('opaque'));
  assert(!tokens('def sorry_free := "escaped \\\" sorry"').includes('sorry'));
  assert.throws(() => leanCode('/- unfinished'), /unterminated/);
  assert.throws(() => leanCode('"unfinished'), /unterminated/);
  console.log('Publication source lexer regression checks: PASS');
  process.exit(0);
}

function walk(dir) {
  return readdirSync(dir, { withFileTypes: true }).flatMap(entry => {
    const path = join(dir, entry.name);
    return entry.isDirectory() ? walk(path) : entry.isFile() && path.endsWith('.lean') ? [path] : [];
  });
}

const forbidden = new Set(['sorry', 'admit', 'axiom', 'opaque', 'implemented_by', 'native_decide', 'unsafe']);
let count = 0;
for (const dir of ['SymplecticPacking', 'verification', 'test', 'vendor/OAI']) {
  for (const path of walk(join(root, dir))) {
    count++;
    try {
      const code = leanCode(readFileSync(path, 'utf8'));
      for (const match of code.matchAll(/[\p{L}\p{N}_']+/gu)) {
        if (forbidden.has(match[0])) {
          const line = code.slice(0, match.index).split('\n').length;
          reject(`${relative(root, path)}:${line}: forbidden token ${match[0]}`);
        }
      }
    } catch (error) { reject(`${relative(root, path)}: ${error.message}`); }
  }
}
for (const path of ['verification/README.md', 'verification/Problem.lean', 'verification/Statement.lean',
  'verification/Algorithm.lean', 'verification/Computability.lean', 'verification/EpochComputability.lean', 'scripts/verify.sh']) {
  if (!existsSync(join(root, path))) reject(`missing required artifact: ${path}`);
}
const entry = leanCode(readFileSync(join(root, 'verification/Statement.lean'), 'utf8'));
for (const name of ['packingHamiltonian', 'epochHamiltonian']) {
  if (!entry.includes(`#check_explicit SymplecticPacking.General.${name}`)) {
    reject(`verification/Statement.lean: missing active explicitness check for General.${name}`);
  }
}
console.log(`Publication source prerequisites: ${count} Lean files; ${failures} failure(s).`);
process.exitCode = failures ? 1 : 0;
