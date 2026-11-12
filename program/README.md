# Programs

Two self-contained single-file programs in the style of the
[Epoch AI problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing): `solution(k, ε)` returns
Python source code. They make complementary trade-offs.

| | [`solution_epoch.py`](solution_epoch.py) | [`solution_embedding.py`](solution_embedding.py) |
|---|---|---|
| Returns | a Hamiltonian `Hamiltonian(Q, P, t)` (PyTorch, float64), Epoch's format | the k embeddings themselves: `Embed(i, X)`, `Preimage(j, Y)` |
| Range | every 10 ≤ k ≤ 10⁵, for ε above an explicit `eps_min(k)` | every k ≥ 10 and every ε ∈ (0, 1) |
| Runtime & RK4 budget | within Epoch's budget: fixed-step float64 RK4, ≤ 0.13 s per Hamiltonian call on 3000–20 000 points | not applicable: evaluates closed-form maps directly, no ODE integration |
| Smoothness | C^∞ near trajectories for k > 10 (exterior branch rays); piecewise C² across one window seam for k = 10; finite-order at time junctions | C⁴ symplectic embeddings |
| Correctness | numerical flow checks (RK4 at N and 2N) | runtime check of parameter hypotheses (H0)–(H15) (exact-arithmetic proof manuscript in preparation), plus float64 and arbitrary-precision checks |
| Checker | [`check_epoch.py`](check_epoch.py) | [`check_embedding.py`](check_embedding.py), [`check_embedding_mp.py`](check_embedding_mp.py) |

The generators and float64 checkers need only Python and PyTorch (`pip install torch`), with no runtime numpy
dependency; [`check_embedding_mp.py`](check_embedding_mp.py) additionally uses `mpmath` (`pip install mpmath`) for
arbitrary-precision verification. Neither program is part of the Lean formalisation. The smooth Hamiltonian of Papers
I–II covers every (k, ε) with a Lean-checked proof, whereas its flow is too stiff for fixed-step float64 integration
within Epoch's time limits.

## 1. `solution_epoch.py`: Epoch's interface, restricted ε

`solution(k, epsilon)` returns the source of a module defining `Hamiltonian(Q, P, t)` whose time-1 flow is designed to
move the k closed unit balls centred at `(3i − 3, 0, 0, 0)` into a ball `B(R)` about the origin with `k / R⁴ > 1 − ε`.
`recommended_steps(k, ε)` gives a step count N for fixed-step RK4.

It implements **elementary constructions of the kind studied in Paper III**: lattice-toric layouts found by computer
search, windows, and for k = 10 the sheared-window configuration of density 360/361 (Paper III, Prop. 3.3); for some k
(e.g. 12) the layout is not the best one of Paper III. The configurations are moved into place by compositions of
explicit Hamiltonian segments. The configurations and motions are explicit; that the time-1 flow packs is supported by
numerical integration, not by a proof.

### Coverage

Inputs outside the covered range raise `NotImplementedError` and report the smallest covered ε; a Hamiltonian that is
not expected to pack is never returned. `eps_min(k)` gives the bound.

| k | smallest ε covered |
|---|---|
| 10 | 0.005 (sheared windows; the limit of this configuration is 1/361 ≈ 0.0028) |
| perfect squares 16 … 10⁵ | ≈ 0.002 |
| other 10 < k ≤ 10⁵ | static deficit `1 − k/A²` of the best lattice layout, plus ≈ 0.002; e.g. k = 11: 0.104, 12: 0.148, 17: 0.097, 50: 0.051, 101: 0.041, 1000: 0.025 |
| k > 10⁵ | not covered |

For fixed non-square k these methods stop at a positive ε; Paper III proves obstructions explaining why.

### Numerical check

[`check_epoch.py`](check_epoch.py) samples points on each unit sphere, integrates the flow with fixed-step RK4 (vector
field by autograd) and reports `R` = the largest image norm, measured about the origin. It runs at
`N = recommended_steps(k, ε)` and at `2N`; both must pass.

```sh
python check_epoch.py solution_epoch.py --k 10 --eps 0.1 --recommended --N 300
```

Results of the release check ([`release-check/`](release-check); CPU, float64, numpy unavailable to the process;
"difference" is the largest pointwise difference between the runs at N and 2N on these samples):

| k | ε | sample points | N, 2N | R at 2N | R needed | margin | difference | longest H call | result |
|---|---|---|---|---|---|---|---|---|---|
| 10 | 0.005 | 3000 | 14160, 28320 | 1.780395 | 1.780509 | 1.1e-04 | 4.8e-05 | 0.07 s | pass |
| 10 | 0.02 | 3000 | 5584, 11168 | 1.786385 | 1.787284 | 9.0e-04 | 1.6e-06 | 0.07 s | pass |
| 10 | 0.1 | 3000 | 2592, 5184 | 1.820626 | 1.825742 | 5.1e-03 | 9.2e-04 | 0.06 s | pass |
| 11 | 0.11 | 3300 | 400, 800 | 1.874150 | 1.874997 | 8.5e-04 | 3.0e-05 | 0.02 s | pass |
| 12 | 0.16 | 3600 | 400, 800 | 1.942488 | 1.944131 | 1.6e-03 | 2.5e-05 | 0.02 s | pass |
| 16 | 0.01 | 4800 | 400, 800 | 2.004045 | 2.005031 | 9.9e-04 | 1.1e-04 | 0.04 s | pass |
| 17 | 0.10 | 5100 | 800, 1600 | 2.084091 | 2.084739 | 6.5e-04 | 7.3e-06 | 0.05 s | pass |
| 25 | 0.005 | 7500 | 800, 1600 | 2.238301 | 2.238872 | 5.7e-04 | 1.7e-05 | 0.06 s | pass |
| 50 | 0.06 | 10000 | 800, 1600 | 2.699189 | 2.700602 | 1.4e-03 | 4.6e-06 | 0.08 s | pass |
| 100 | 0.003 | 10000 | 800, 1600 | 3.164245 | 3.164654 | 4.1e-04 | 7.2e-06 | 0.08 s | pass |
| 101 | 0.05 | 10100 | 800, 1600 | 3.209466 | 3.211068 | 1.6e-03 | 2.7e-05 | 0.08 s | pass |
| 1000 | 0.03 | 20000 | 1600, 3200 | 5.664869 | 5.666398 | 1.5e-03 | 4.3e-06 | 0.13 s | pass |

All twelve pass at both step counts. This checks sampled sphere trajectories under fixed-step float64 RK4; Epoch's
internal verifier settings are not public.

### Smoothness and numerical notes

- **Smoothness scope.** The wrapping segments use an angle coordinate with a branch cut (a ray from the wrapping
  centre); across that ray the Hamiltonian jumps (for example k = 16, ε = 0.01, t = 0.415, Q = (0.2, 0.5),
  P = (0.3, ±δ): H tends to 26.50 and 54.17 as δ → 0). The construction keeps the ball trajectories away from those
  exterior rays, so the flow checks are unaffected. In the k = 10 family one segment is piecewise C² in space across a
  moving surface that intersects the ball images (the seam between the round cap and the straight side of a
  stadium-shaped window, where third derivatives are bounded with a finite jump), and the time dependence has finite
  smoothness order at segment junctions. Accordingly, while the RK4 trajectory and runtime budgets are satisfied, the
  returned function is not globally C^∞ on ℝ⁴ × [0, 1].
- **Pointwise differences between N and 2N in the k = 10 family.** The final windows of six of the ten balls are
  invariant under a circle action, and RK4 makes a phase error along its orbits. In a run with 2000 points per sphere at
  ε = 0.1, a few points differ by up to 2.5 between N = 2592 and 2N, more than 99.99 % of it along the orbits; the
  radius changes by at most 4.6·10⁻⁴ and every point stays in its window. Doubling the steps again reduces the
  difference faster than fourth order (2.5, 0.071, 0.0023). A verifier that demands pointwise agreement at N would see
  this; the packing is unaffected.
- **Finite-difference symplecticity readings of the time-1 map can be large** (up to about 4·10² at k = 10,
  ε = 0.005); they scale with the difference step and come from the steep gradients of the map, not from a failure of
  symplecticity, which holds exactly for a Hamiltonian flow.

## 2. `solution_embedding.py`: every k and ε, as explicit embeddings

`solution(k, eps)` returns the source of a module defining `Embed(i, X)` (the i-th embedding, in coordinates centred at
ball i), `Preimage(j, Y)` (a candidate preimage under the j-th embedding), `STAGES(i)` (the factors of the i-th
embedding with their inverses) and `CONFIG` (parameters, hypothesis margins, a float64 self-test). Nothing is
integrated, so the output is not a Hamiltonian; it is the packing map itself.

**The mathematics.** For every integer k ≥ 10 and every ε ∈ (0, 1) the construction defines r₊ > 1 and C⁴ symplectic
embeddings f₀, …, f_{k−1} of B⁴(r₊) into B⁴(R), R = (k/(1 − ε))^{1/4}, with pairwise disjoint images. Each fᵢ is a
composition of ten maps given by piecewise closed formulas in elementary functions, plus the root of one increasing
scalar function per evaluation of a planar keyhole:

    f_i = S_out ∘ χ ∘ 𝒲 ∘ Π ∘ Φ_g ∘ Ψ_S ∘ F^(i) ∘ C_i ∘ KR ∘ S_in

(scaling; a Knothe–Rosenblatt strip map; cell to flat chart; a keyhole comparator for i ≥ 9; a twist moving three
marked fibres into a free corridor; post chart; corner keyholes, sector and corner charts; the ball chart of CP² minus a
line; scaling). The parameters are explicit functions of (k, ε_c), ε_c = min(ε, 1/100). The geometry is that of Paper I
(a Fermat cubic model, marked fibres, a return to the ball avoiding a line), written here in closed form so that
the packing can be evaluated point by point (the full check at k = 10 takes under a minute) without integrating a stiff
flow. The program evaluates all parameter hypotheses `(H0)–(H15)` at construction time and raises `ValueError` if any
margin fails; an exact-arithmetic proof manuscript for this closed-form chain is in preparation.

### Numerical and arbitrary-precision checks

[`check_embedding.py`](check_embedding.py) evaluates, on random samples in float64: (A) the images lie in B(R);
(B) the Jacobian is symplectic (central differences at fixed step h); (C) `Preimage` inverts `Embed`; (D) no image
point lies in the image of another ball; (E) uniform points in B(R) are covered with the fraction 1 − ε that volume
preservation demands, never twice; (F) wall time; (G) continuity: chords are bisected to separation 10⁻¹¹ to detect
jumps. [`check_embedding_mp.py`](check_embedding_mp.py) re-evaluates the exact map family and any float64-flagged
points in D-digit `mpmath` arithmetic (default D = 100).

```sh
python check_embedding.py solution_embedding.py --k 10 --eps 0.1 --h 1e-7
python check_embedding_mp.py solution_embedding.py --k 101 --eps 0.01 --dps 100
```

Float64 results ([`release-check/embedding/`](release-check/embedding); CPU, float64, numpy unavailable to the process;
`--h 1e-7`, `sym_tol = 1e-5`, `rt_tol = 1e-7`; 500 points on and 500 inside each ball, 100 chords of 3000 points per
ball, 200 000 volume points):

| k | ε | radius margin (A) | overlaps / double cover (D, E) | covered (E; expected 1 − ε) | round-trip > 10⁻⁷ (C) | symplectic defect (B) | G chord flags / Lipschitz est. | time (s) | geometry (A, D, E) | float64 fixed-step flags |
|---|---|---|---|---|---|---|---|---|---|---|
| 10 | 0.1 | 4.30e-02 | 0 / 0 | 0.89999 ± 0.00067 | 0 | 1.6e-08 | 0 / 7.2e+08 | 58 | pass | none |
| 10 | 0.01 | 1.07e-05 | 0 / 0 | 0.98969 ± 0.00023 | 0 | 1.6e-08 | 0 / 7.2e+08 | 58 | pass | none |
| 10 | 0.002 | 4.06e-06 | 0 / 0 | 0.99795 ± 0.00010 | 0 | 4.5e-08 | 2 / 1.3e+11 | 57 | pass | G (2 chords) |
| 10 | 0.0001 | 1.02e-05 | 0 / 0 | 0.99991 ± 0.00002 | 0 | 2.7e-05 | 143 / 1.7e+12 | 49 | pass | G (143), B |
| 11 | 0.01 | 2.19e-05 | 0 / 0 | 0.99020 ± 0.00022 | 0 | 1.4e-08 | 4 / 1.0e+11 | 68 | pass | G (4) |
| 17 | 0.01 | 3.93e-05 | 0 / 0 | 0.98993 ± 0.00022 | 0 | 6.0e-07 | 57 / 6.8e+11 | 162 | pass | G (57) |
| 30 | 0.01 | 1.95e-05 | 0 / 0 | 0.99000 ± 0.00022 | 0 | 3.7e-08 | 207 / 1.2e+12 | 295 | pass | G (207) |
| 50 | 0.01 | 1.26e-05 | 0 / 0 | 0.98977 ± 0.00022 | 0 | 2.3e-02 | 409 / 2.0e+12 | 476 | pass | G (409), B |
| 101 | 0.01 | 6.76e-06 | 0 / 0 | 0.99006 ± 0.00022 | 2 | 8.6e-02 | 938 / 6.0e+12 | 901 | pass | G (938), B, C |

**Interpreting the fixed-step float64 flags.** Sampled containment (A), pairwise disjointness (D), and Monte Carlo
volume coverage (E) pass in all nine runs; `check_embedding.py` exits with `PASS` only when zero fixed-step float64
flags occur (`k = 10, ε ≥ 0.01`). The B, C, and G flags arise where local Lipschitz constants (10¹¹–6·10¹², from
margins of order ε/√k next to coordinates of order 1) and condition numbers (10⁷–3·10⁹) exceed 53-bit float64
resolution at fixed tolerances (`h = 1e-7`, chord separation `1e-11`). Running
[`check_embedding_mp.py`](check_embedding_mp.py) at 100 decimal digits resolves every flagged point:

- **G (continuity):** on all flagged chord intervals (including all 1117 intervals flagged across ten extended test
  runs in 80- to 140-digit arithmetic), image gaps shrink strictly linearly down to separation 10⁻³⁰ (e.g. at `k = 10,
  ε = 0.002`, both flagged intervals shrink to `< 1.4·10⁻¹⁹` at separation `10⁻³⁰` with slope ratio accurate to
  `10⁻¹⁹`).
- **B (symplecticity):** with central-difference step `h = 10⁻³³` in 100-digit arithmetic, the points flagged in
  float64 (such as `2.7·10⁻⁵` at `k = 10, ε = 10⁻⁴` and `8.6·10⁻²` at `k = 101, ε = 0.01`) have symplectic defect
  below `3·10⁻⁵³`.
- **C (round trip):** the points exceeding `10⁻⁷` in float64 at `k = 101, ε = 0.01` invert with round-trip error below
  `5·10⁻⁹²` in 100-digit arithmetic (`< 10⁻⁷³` at 80 digits).

**Float64 operating range.** In standard float64, round-trip residuals stay below 10⁻⁷ for k = 10 down to ε ≈ 3·10⁻⁷
and for k = 30–1000 down to ε ≈ 10⁻⁶; for ε_c = 0.01 they grow gradually with k (about 10⁻⁷ at k = 10⁴, 10⁻³ at
k = 10⁶). Beyond those ranges `Embed` continues to return finite images inside B(R) and records 1000-point round-trip
diagnostics in `CONFIG['float64_selftest']`.
