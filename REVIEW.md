# Reviewer guide

## The claim to assess first

The central object is a **specified smooth, compactly supported Hamiltonian**, not an
existence assertion about some embedding. In ℝ⁴, for each k ≥ 10 and 0 < ε < 1, its time-one
flow moves the k closed unit balls at `(3i,0,0,0)`, `0 ≤ i < k`, into the open ball of radius
`(k/(1−ε/4))^(1/4)`. Their occupied volume fraction is exactly `1−ε/4`.

Read the abstract and Theorem A at the start of the [paper](paper/main.pdf), then compare
[`four_dim_theorem`](verification/Statement.lean) with the definitions in
[`Problem.lean`](verification/Problem.lean). This is the shortest route to the principal
statement and its formal meaning.

## Scope and contribution

The general motion theorem assumes n ≥ 2, k ≥ 1, target capacity C > 0, every cᵢ > 0,
and pairwise disjoint prescribed closed source balls, in addition to the dimension-specific
inequalities below.

| Question | Answer and location |
|---|---|
| What is new relative to an existence theorem? | One construction of a Hamiltonian moving prescribed disjoint balls; its explicit formulas, isotopy, and global motion are the subject of the paper. See the introduction and Hamiltonian section. |
| What is the geometric route? | Linear comparison for the equal-ball family → planar rearrangement → twisted Fermat cubic disc bundle → symmetry-controlled return → common isotopy → compactly supported Hamiltonian. The introduction's construction chain and mechanism section explain it. |
| What is covered in higher dimensions? | In ℝ²ⁿ, n ≥ 3, positive capacities with Σcᵢⁿ < Cⁿ and cᵢ+cⱼ < C for i ≠ j. See Theorem C and `main_theorem`. |
| What is covered in dimension four? | Positive capacities with Σcᵢ² < C² and 3cᵢ < C; the equal-ball stability corollary includes k ≥ 9. This is not a classification of every unequal four-dimensional packing. |
| What does the algorithm theorem say? | One program, taking names of real inputs, halts on all admissible data with a finite rational-polynomial-times-cutoff Hamiltonian satisfying the packing specification. It gives no feasible runtime bound and need not approximate the first Hamiltonian. |
| What is the relation to earlier work? | The construction develops the OpenAI twisted disc-bundle mechanism. Attribution and comparison with Biran and earlier constructive work are in the introduction and references. |
| Which proofs avoid curve methods? | Construction and sufficiency. The converse of the higher-dimensional criterion uses classical volume and two-ball obstructions; the dependency audit explicitly detects the latter's holomorphic-line input. |

The radius above is a Euclidean radius. Elsewhere `B(c)` uses capacity c, so the radius is
`√(c/π)`. The source balls are closed; the target in `PackingSpec` is open. The Hamiltonian
convention is `ι_X ω₀ = dH`, hence `X_H = (∂_p H, −∂_q H)` in the formal coordinates.

## A short formal review

Read these files in order; the construction's hundreds of supporting files need not be read
before assessing the stated result.

1. [`verification/Problem.lean`](verification/Problem.lean): phase space, symplectic form,
   balls, admissibility, and packing specifications, from Mathlib alone. Check the hypotheses
   and the quantifier over **every** integral curve.
2. [`verification/Algorithm.lean`](verification/Algorithm.lean): definitional equalities tie
   the named Hamiltonian to branch selection and the common Hamiltonian construction.
3. [`verification/Statement.lean`](verification/Statement.lean): main theorems, flow properties,
   stability, and corollaries for those exact terms.
4. [`verification/Computability.lean`](verification/Computability.lean) and
   [`verification/EpochComputability.lean`](verification/EpochComputability.lean): input names,
   one uniform machine, finite output, halting, and certified packing.
5. [`verification/Executable.lean`](verification/Executable.lean): the compiled
   total reference algorithm, with constructive-runtime and axiom gates. Its
   [program guide](examples/PACKING.md) connects the finite output to the actual
   value, gradient and flow interpreter, explains all-input termination, and
   provides runnable checks. These executable additions postdate v1.0.1.

For a particular geometric step, use [`PAPER-INDEX.md`](verification/PAPER-INDEX.md) to find its
Lean declarations, and the [supplement](paper/supplement.pdf) for the complete mathematical
construction. The PDFs distinguish **full statement verified** from **needed consequence
verified**; the latter covers the version used by the construction, not every assertion of
the printed auxiliary statement. The index records these scopes; an unqualified source tag
is only a reference. The supplement's appendix “Formal statements that differ in form from
the text” gives the precise restrictions, including return/transfer identities along smooth
families and the coarser support bound. These correspondences require human review; the
kernel checks the Lean statements.

## Reproduce the checks

The [README](README.md#verify) gives the complete commands. The checks have distinct roles:

| Check | What it establishes |
|---|---|
| Source hygiene and tag freshness | Active forbidden-token checks, and agreement between paper tags and generated index/audits. |
| Lean build and axiom gates | Accepted proof terms for the specified statements; only the three declared standard axioms. |
| Explicitness and uniformity audits | Defined constructions meet the stated metaprogram criteria; oracle machines do not use classical branching. |
| Independence audit | Construction-side proof dependencies avoid the named upstream packing existence and curve-analysis inputs. |
| Checker regression suites | Known acceptable examples pass and known forbidden examples are detected, including a wrapped obstruction. |
| Fresh kernel replay | Compiled declarations and their imported proof closure are replayed into a fresh environment by the pinned Lean kernel. |
| Paper build | Both PDFs compile with stable references, no undefined citations, no duplicate labels, and no overfull boxes. |

A bundled cache saves elaboration time. Its checksums detect corruption and its source digest
identifies the intended proof sources; neither checksum is a mathematical proof. Kernel
replay adds a check of stored proof terms. A clean source build is the route for checking
that the supplied sources elaborate to accepted proofs without the project's binary cache.

These checks do not certify novelty, exposition, the paper-to-formal-statement interpretation,
or a practical runtime bound or a formal refinement proof of the Python interpreter.
The executable interpreter's correspondence and interval-flow convergence arguments
are in the program guide and remain explicit review questions. There is
no claimed successful time-bounded Epoch program submission in this repository's main line.
