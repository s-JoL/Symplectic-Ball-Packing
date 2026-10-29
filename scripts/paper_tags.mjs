#!/usr/bin/env node
// Collect the \lean{...} tags of the main paper and supplement.
// Writes verification/Audit/PaperTags.lean (every tagged name must exist and pass the axiom
// gate) and verification/PAPER-INDEX.md (paper statement -> Lean declarations).
// With --check nothing is written; the run fails if either file differs from what the sources give.
import { readFileSync, writeFileSync, readdirSync, statSync, existsSync } from 'node:fs';
import { resolve, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const docs = [['main', 'paper/main'], ['supplement', 'paper/supp']];
const envs = 'theorem|lemma|proposition|corollary|definition|construction|remark|maintheorem|mainproposition|maincorollary';
const coverage = { reference: 'Reference only; scope not classified',
  full: 'Full statement verified', needed: 'Needed consequence verified' };

function parseTags(source, location) {
  const raw = source.split('\n'), lines = [], parsed = [];
  for (let i = 0; i < raw.length; i++) {
    let line = raw[i];
    const start = i;
    while (/\\lean(?:\[[^\]]*\])?\{[^}]*$/.test(line) && i + 1 < raw.length) line += '\n' + raw[++i];
    lines[start] = line;
  }
  let current = null;
  lines.forEach((line, i) => {
    const begin = line.match(new RegExp(`\\\\begin\\{(${envs})\\}(\\[([^\\]]*)\\])?`));
    if (begin) current = { kind: begin[1], title: begin[3] ?? '', label: '' };
    const label = line.match(/\\label\{([^}]*)\}/);
    if (label && current && !current.label) current.label = label[1];
    for (const m of line.matchAll(/\\lean(?:\[([^\]]*)\])?\{([^}]*)\}/g)) {
      const scope = m[1] ?? 'reference';
      if (!Object.hasOwn(coverage, scope) || (m[1] !== undefined && scope === 'reference'))
        throw new Error(`${location}:${i + 1}: invalid Lean coverage: ${scope}`);
      const tagged = m[2].split(',').map(s => s.trim()).filter(Boolean);
      if (!tagged.length) throw new Error(`${location}:${i + 1}: empty Lean tag`);
      parsed.push({ line: i + 1, kind: current?.kind ?? '', label: current?.label ?? '',
        title: current?.title ?? '', scope, names: tagged });
    }
    // A visible main-result marker also classifies its matching source reference.
    const mark = line.match(/\\leanmark\{([^}]*)\}/);
    if (mark && current?.label) {
      const marked = new Set(mark[1].replace(/\\_/g, '_').split(',').map(s => s.trim()));
      for (const tag of parsed.filter(t => t.label === current.label &&
          t.names.every(n => marked.has(n.replace(/^SymplecticPacking\./, ''))))) {
        if (tag.scope === 'needed') throw new Error(`${location}:${i + 1}: conflicting Lean coverage`);
        tag.scope = 'full';
      }
    }
  });
  return parsed;
}

if (process.argv[2] === '--self-test') {
  const { strict: assert } = await import('node:assert');
  const source = String.raw`\begin{theorem}[Transfer]\label{thm:transfer}
\lean[needed]{Example.return,
Example.pullback}
\lean{Example.definition}
\lean[full]{Example.complete}`;
  const tags = parseTags(source, 'fixture');
  assert.deepEqual(tags.map(t => t.scope), ['needed', 'reference', 'full']);
  assert.deepEqual(tags[0].names, ['Example.return', 'Example.pullback']);
  assert.equal(tags[0].label, 'thm:transfer');
  assert.equal(tags[1].line, 4);
  assert.equal(tags[2].line, 5);
  // A typo must not silently upgrade a restricted statement to full coverage.
  assert.throws(() => parseTags(String.raw`\lean[neede]{Example.x}`, 'fixture'), /invalid Lean coverage/);
  assert.throws(() => parseTags(String.raw`\lean[reference]{Example.x}`, 'fixture'), /invalid Lean coverage/);
  assert.throws(() => parseTags(String.raw`\lean[needed]{}`, 'fixture'), /empty Lean tag/);
  const marked = String.raw`\begin{definition}\label{def:spec}
\lean{SymplecticPacking.Example.packing_spec}
\leanmark{Example.packing\_spec}`;
  assert.equal(parseTags(marked, 'fixture')[0].scope, 'full');
  assert.throws(() => parseTags(marked.replace('\\lean{', '\\lean[needed]{'), 'fixture'), /conflicting Lean coverage/);
  console.log('Paper tag coverage regression checks: PASS');
  process.exit(0);
}

const rows = [];
const names = new Set();
for (const [doc, dir] of docs) {
  for (const file of readdirSync(join(root, dir)).filter(f => f.endsWith('.tex')).sort()) {
    for (const tag of parseTags(readFileSync(join(root, dir, file), 'utf8'), `${dir}/${file}`)) {
      tag.names.forEach(n => names.add(n));
      rows.push({ doc, file: `${dir}/${file}`, ...tag });
    }
  }
}
for (const n of names) {
  if (!/^[\p{L}_][\p{L}\p{N}_'.]*$/u.test(n)) throw new Error(`invalid Lean name in \\lean tag: ${n}`);
}
const sorted = [...names].sort();
const modules = [];
const walk = dir => readdirSync(join(root, dir)).sort().forEach(f => {
  const p = `${dir}/${f}`;
  if (statSync(join(root, p)).isDirectory()) walk(p);
  else if (f.endsWith('.lean')) modules.push(p.slice(0, -5).replace(/\//g, '.'));
});
walk('SymplecticPacking');
const check = process.argv[2] === '--check';
let stale = 0;
const emit = (path, text) => {
  const file = join(root, path);
  if (!check) writeFileSync(file, text);
  else if (!existsSync(file) || readFileSync(file, 'utf8') !== text) {
    console.error(`${path} is out of date: run node scripts/paper_tags.mjs`); stale++;
  }
};
emit('verification/Audit/PaperTags.lean', [
  ...modules.map(m => `import ${m}`), 'import verification.PaperFacts', 'import verification.AxiomCheck', '',
  '/-!', '# Paper tags', '',
  'Generated by `scripts/paper_tags.mjs`: every declaration named by a `\\lean{...}` tag in the',
  'main paper or supplement exists and depends only on the three standard axioms.', '-/', '',
  ...sorted.map(n => `#assert_publication_axioms ${n}`), ''].join('\n'));
const md = ['# Paper to Lean index', '',
  'Generated by `scripts/paper_tags.mjs` from the `\\lean{…}` tags in the sources. Every name',
  'listed is checked by `verification/Audit/PaperTags.lean` to exist and to depend only on',
  '`propext`, `Classical.choice` and `Quot.sound`.', '',
  '**Full statement verified** means the complete mathematical counterpart, up to documented',
  'presentation differences. **Needed consequence verified** means only the version used by',
  'the construction; further assertions or a whole-domain version may be proved only in the',
  'text. The supplement appendix “Formal statements that differ in form from the text” gives',
  'the restrictions. Unqualified tags are **references only**, without a full-coverage claim.',
  'Coverage is an editorial comparison for human review; the kernel checks the Lean types,',
  'not equivalence to the prose. Visible main-result markers also state full coverage.', '',
  '| Document | Statement | Coverage | Source | Lean declarations |', '|---|---|---|---|---|',
  ...rows.map(r => `| ${r.doc} | ${r.kind}${r.title ? ` (${r.title.replace(/\|/g, '/')})` : ''}${r.label ? ` \`${r.label}\`` : ''} | ${coverage[r.scope]} | \`${r.file}:${r.line}\` | ${r.names.map(n => `\`${n}\``).join(', ')} |`),
  ''];
emit('verification/PAPER-INDEX.md', md.join('\n'));
console.log(`${rows.length} tags, ${sorted.length} distinct declarations`);
process.exitCode = stale ? 1 : 0;
