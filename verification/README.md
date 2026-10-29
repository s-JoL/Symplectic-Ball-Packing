# Verification

This directory is the entry point to the Lean 4 formalisation. It is meant to let a reader
decide, from a few short files, *what* has been proved; Lean checks *that* it has been proved
by elaborating the full dependency closure.

## What is proved

For every `n ≥ 2`, `k ≥ 1`, `C > 0`, capacities `c₁,…,c_k > 0` and centres `s₁,…,s_k` with
the closed balls `sᵢ + B(cᵢ)` pairwise disjoint and admissible data

* `n ≥ 3`: `Σ cᵢⁿ < Cⁿ` and `cᵢ + cⱼ < C` for `i ≠ j`;
* `n = 2`: `Σ cᵢ² < C²` and `3cᵢ < C` for all `i`,

the concrete Hamiltonian `packingHamiltonian n k C c s` is `C^∞` with compact support, and
every integral curve of its Hamiltonian vector field starting in `sᵢ + B(cᵢ)` is in the open
ball `{π|y|² < C}` at time one (`main_theorem`). Its time-one map is a smooth symplectic
diffeomorphism, so the images are disjoint. In dimension four, for every `k ≥ 10` and
`ε ∈ (0,1)`, the Hamiltonian `epochHamiltonianQ k ε` carries the closed unit balls at
`epochCenter i = (3i,0,0,0)`, `0 ≤ i < k`, into the ball of radius `R = (k/(1−ε/4))^{1/4}`,
with `k/R⁴ = 1−ε/4`, and the construction takes the linear comparison datum
(`four_dim_theorem`). For the Epoch data (`k ≥ 9` unit balls at `epochCenter i`, `C = πR²`,
`R⁴ = k/(1−ε/2)`) the Hamiltonian satisfies the packing
specification with `k/R⁴ = 1−ε/2` (`epoch_packing`); the problem as posed by Epoch (`k ≥ 10`,
closed origin ball `B(R)`, `k/R⁴ > 1−ε`) is `epoch_theorem_ten`. A single oracle machine,
given names of the capacities and centres, halts on every admissible input with a finite code
`(B, P)`, `P` a rational polynomial, whose Hamiltonian `β_B · P` has the same packing property
(`original_name_algorithm`); the Epoch machine reads only a name of `ε` and receives `k` at run
time (`epoch_name_algorithm_packing`, `epoch_name_algorithm`).

## Trusted base

* The Lean 4 kernel, toolchain `leanprover/lean4:v4.34.1` (`lean-toolchain`).
* Mathlib at tag `v4.34.1` (`lake-manifest.json`).
* `verification/Problem.lean` — the definitions the statements use. It imports only Mathlib.
* The axioms `propext`, `Classical.choice`, `Quot.sound`. Every theorem below is guarded by
  `#assert_publication_axioms`, which fails the build if the transitive axiom set contains
  anything else (in particular `sorryAx`, or `Lean.ofReduceBool` from `native_decide`);
  `test/AxiomCheckTest.lean` checks that it rejects `sorryAx`.

The vendored OpenAI library `vendor/OAI` (unmodified, Apache-2.0) contributes lemmas and a few
generic differential-geometric operators (exterior derivative, chart differential) used inside
the definitions; none of its packing constructions or existence results is used. The definitions
of the Hamiltonian and the algorithm are this project's own and are audited below.
Three library files import `verification/Problem.lean` (`SymplecticPacking/General/Interface.lean`,
`SymplecticPacking/HighDim/Phase.lean`, `SymplecticPacking/Effective/PackingCertificateEpochInput.lean`),
so that the construction and the statements use the same definitions.

In module and declaration names of the library, `Raw` and `Native` mark the explicit models
and formulas defined in this development, as opposed to the corresponding abstract interfaces of
the vendored library (`OAI.…`), with which they are shown to agree.

Some library files set `backward.isDefEq.respectTransparency false` (and its `.types` variant).
This toolchain option lets the elaborator's definitional-equality checks unfold definitions
regardless of the transparency setting. It changes which proofs the
elaborator finds, not what is accepted: every proof term is checked by the kernel, which does not
use transparency settings.

## Reading order (five entry files, about 580 lines)

1. `Problem.lean` — phase space `ℝ^{2n}` with coordinates `(q, p)` (the paper's `(x, y)`), `ω₀ = Σ dqⱼ ∧ dpⱼ`, the
   Hamiltonian vector field (`ι_{X_H} ω₀ = dH`), capacity balls `{π‖y−s‖² ≤ c}`, `Admissible`,
   `BallsDisjoint`, `PackingSpec`, and the Epoch specification.
2. `Algorithm.lean` — the top level of `packingHamiltonian`: branch selection and the
   Hamiltonian end, as definitional equalities.
3. `Statement.lean` — Theorems A and C, Proposition B, the time-one map and Corollaries D–G,
   each stated for the exact terms of `Algorithm.lean`.
4. `Computability.lean`, `EpochComputability.lean` — the algorithm. `Computability.lean` also
   shows, by `rfl`, how an output code decodes to `β_B · P`.

`PackingSpec n k C c s H` requires: `H` is jointly `C^∞`; one compact set contains the
support of `H(t,·)` for all `t`; every source point has a global integral curve; and *every*
integral curve on `[0,1]` from a source point ends in the open target. The last condition
quantifies over all solutions, so the statement does not depend on a chosen solution.

The computability theorems use, besides `Problem.lean`, the notion of a *name*: a stream
`q : ℕ → ℚ` names `x` if `|q n − x| ≤ 2⁻ⁿ` for all `n` (`Effective.Names`). Rational inputs
are constant names. The capacity stream lists the target at index `0` and `cᵢ` at index `i`
(entries beyond `k` repeat the target).

## Cases of the construction

Levels L1–L3 are those of Definition 1.3 of the paper; rows are the cases of the
construction (`General.selectEmbeddings`).

| Case | L1: embeddings, Hamiltonian | L2: finite form | L3: algorithm (halting and correctness) |
|---|---|---|---|
| `n = 2`, `k ≥ 10` equal, `(c₁/C)√k > 3/4` (linear datum) | `Branch2.embeddingsEq_spec`, `main_theorem` | `General.Compile.main_finite` | `original_name_algorithm`, `epoch_name_algorithm` |
| `n = 2`, all other admissible data, incl. `k = 9` and unequal (scalar comparator) | `Branch2.embeddingsGen_spec`, `main_theorem` | same | same |
| `n ≥ 3`, all `cᵢ < C/2` | `BranchSmall.embeddings_spec`, `main_theorem` | same | `original_name_algorithm` |
| `n = 3`, one `cⱼ ≥ C/2` | `BranchLarge3.embeddings_spec`, `main_theorem` | same | `original_name_algorithm` |
| `n ≥ 4`, one `cⱼ ≥ C/2` | `BranchLargeHigh.embeddings_spec`, `main_theorem` | same | `original_name_algorithm` |

All names are relative to `SymplecticPacking` except the `verification/` theorems. The
explicitness of every L1 definition is checked by `#check_explicit` (below). `main_finite`
applies to every compilation datum satisfying the inequalities (C1)–(C7) of the
supplement; the L3 theorems state that one machine halts on every admissible input and that
its output satisfies `PackingSpec` (resp. `EpochSpecR`).

## Explicitness and uniformity

`#check_explicit c` walks the non-proof dependency closure of a definition. It accepts
classical case distinctions on propositions, least-element searches over integers, rationals
and finite data whose predicate has a genuine (non-classical) decision procedure, and definite
descriptions after unique existence (`Explicit.the`) over types with no discrete factor. A
definite description over a type such as `ℕ × ℝ` is rejected in project code, since it could
wrap a search over the discrete factor. It rejects any other choice operator in project code.
Choice sites inside Mathlib definitions are accepted only for the reviewed list in
`SymplecticPacking/Explicit/Whitelist.lean`. It is applied to `packingHamiltonian`,
`epochHamiltonian`, `epochHamiltonianQ`, the branch embeddings and the algorithm terms.

The checker cannot rule out every encoding of a search: a definite description over `ℝ` can
characterise an integer defined by an undecidable search. The definite descriptions reached from
`packingHamiltonian` are therefore listed and discussed individually in the supplement (section "The
explicitness check").

`#check_constructive c` is stricter: the non-proof closure of `c` may contain no classical
constant at all, including classical decidability. It is applied to the two oracle machines.
A machine passing it is one fixed program in its oracle arguments and cannot branch on an
undecidable property of the real numbers they name; `Nat.RecursiveIn` then expresses
computability relative to the input streams.

`test/ExplicitTest.lean` contains regression cases that both checkers must reject,
including a search for "the least index whose enumerated Hamiltonian satisfies the
specification" and a machine branching on `x < 1/3` for a real `x`. Both checkers are
metaprograms and are not themselves verified; their reports list every accepted site.

## Independence from packing existence theorems

Two separate grounds support the claim that the proofs use no packing existence theorem.

* **Automatic check.** `Audit/Independence.lean` walks the complete dependency closure,
  including theorem proof bodies, of the packing, stability, flow, corollary and algorithm
  theorems and `General.symplectic_neighbourhood_sufficient`. The batched command
  `#assert_construction_independence` excludes the vendored packing predicate and existence
  theorems, the holomorphic-line and two-ball obstruction proofs, the project's rigidity
  wrapper and the listed curve-analysis modules. Corollary D's converse is checked separately:
  it may use the classical obstructions, but no packing sufficiency theorem. The roots and
  excluded declarations are recorded in the audit source.
* **Vendored usage.** `Audit/VendoredUsage.lean` lists, by module, the vendored
  declarations the main theorems use (charts, forms, primitives, Moser fields, model
  coefficients; 3810 declarations from 112 modules, as logged by the audit) and fails if any
  comes from the library's curve-analysis directories. The supplement's section "The
  explicitness check" summarises the list and discusses each definite description of the
  construction listed by `#check_explicit`. The checked roots include Proposition B and
  `General.symplectic_neighbourhood_sufficient`.

A positive control confirms that Corollary D's converse reaches `adapted_affine_line`, and
`test/DependencyAuditTest.lean` confirms that the traversal detects an obstruction used only
inside a theorem's proof. Thus the no-curve claim applies to the construction and sufficiency;
Corollary D's necessity direction uses the classical obstructions.

## Paper correspondence

The statements of the paper that carry a visible mark `[Lean: …]` are Theorem A and Proposition B
(`four_dim_theorem`, `four_dim_stability`), Definitions 1.1–1.2, Theorem C(i) and (iii), Corollaries D–G and the algorithm theorem of the computability
section. Each Lean statement in this directory agrees with the paper up to the differences of
form listed in the section "Formal verification" of the paper. Corollary D is
`neighbourhood_criterion` together with `flow_neighbourhood_embedding`. Theorem C(ii) is
checked by the metaprogram `#check_explicit`, not by a theorem; uniformity of the machines
(one program for all inputs) by `#check_constructive`.

Further statements carry source tags naming related declarations. Unqualified `\lean{…}`
tags are unprinted references without a claim of complete coverage. `\lean[needed]{…}`
prints **needed consequence verified**; only the version used by the construction is
formalised. `\lean[full]{…}` and the main-result `\leanmark{…}` markers print **full statement
verified**, up to documented presentation differences. `PAPER-INDEX.md` records the scopes;
every tagged name is checked to exist and to use only the three axioms. The supplement
appendix “Formal statements that differ in form from the text” lists the precise
restrictions. Scope correspondence requires human review. The tags are a map of the formal proof; the claim of
formal verification is carried by the theorems in `Statement.lean`, `Computability.lean` and
`EpochComputability.lean`.

`PaperFacts.lean` supplies elementary consequences of the construction's public API
used by these tags (parameter identities, inverse-chart derivatives and limits, strip
estimates and equivariance). It is imported by the paper-tag audit, and its tagged
theorems pass the same axiom gate. The construction does not depend on this file.

## Reproduce

Versions are pinned: Lean `v4.34.1` (`lean-toolchain`), Mathlib `v4.34.1` and every other
dependency at the commits in `lake-manifest.json`. `verify.sh` needs Node.js in every mode,
Elan for the Lean stages and Tectonic for the papers. From a clean checkout:

```sh
lake exe cache get          # Mathlib's prebuilt files only
bash scripts/verify.sh      # builds this project from source, then every check
```

`verify.sh` runs the source and paper-tag checks, builds the library and the verification
entry, including all axiom, explicitness, uniformity and independence gates, runs the checker
regression tests in `test/`, and compiles both papers. Every stage is fatal. The
regression suites are Lake targets, so they run alongside independent build jobs and
reuse their checked artifacts until a source or dependency changes. The verification script
also re-elaborates the three main statement/algorithm entries, the paper-tag and independence
gates, and all three regression suites from source, even when their build artifacts were restored.

**Cost of the build.** A build from an empty `.lake/build` takes several hours; with the
prebuilt project cache below it takes minutes. Once built, `lake build` reuses `.lake/build`
and rebuilds only the modules whose sources changed.

**Faster check with the bundled project cache.** `python3 scripts/project_cache.py restore`
checks the pinned toolchain, the SHA-256 digest of every Lean source and dependency
configuration, and all cache-part checksums before restoring project artifacts. The cache
uses the toolchain's native `leantar` format. It excludes Mathlib, generated C setup files,
executables, local logs, and repository history; see [`cache/README.md`](../cache/README.md).

The bundled cache and the release's kernel-replay receipt are regenerated for 1.0.1.
A later source change, including a Lean comment change, invalidates the raw source digest;
use a source build or regenerate the cache instead of reusing an earlier receipt.

```sh
lake exe cache get
python3 scripts/project_cache.py restore
bash scripts/verify.sh --lean
bash scripts/check_kernel.sh
```

A cache hit alone does not re-check a proof. `check_kernel.sh` uses the built-in
`leanchecker --fresh verification.Kernel` to replay the entry module's full imported
declaration closure into a new Lean kernel environment. This checks stored proof terms,
including dependencies, without rerunning tactic elaboration. It uses the same Lean kernel,
not an independent implementation, and assumes well-formed object files. See
[Lean's proof-validation documentation](https://lean-lang.org/doc/reference/4.34.0/ValidatingProofs/).
Human review must still establish that the formal statements represent the intended problem.

A clean source build (empty `.lake/build`, no project-cache restore) checks the supplied
sources by elaboration. Mathlib's official dependency cache is used in both routes. The
independent project-source workflow is `.github/workflows/full-build.yml`.

**Continuous integration.** `.github/workflows/verify.yml` runs source checks, all Lean and
audit targets, all checker regressions, and both papers. It restores the bundled project
cache when its source digest matches; otherwise it builds from source. Fresh kernel replay
is **not enabled by default**, including on that source-build fallback: a successful default
CI run is not evidence of fresh kernel replay. Its artifacts contain PDFs and verification
logs. The manually dispatched `.github/workflows/full-build.yml` omits the project cache
and enables fresh kernel replay; `.github/workflows/kernel-replay.yml` explicitly enables
replay while allowing the project cache. Those runs save the replay evidence as well.
None of these workflows publishes a release.
