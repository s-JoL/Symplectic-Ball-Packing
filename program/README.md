# Programs

Two self-contained single-file Python generators inspired by the
[Epoch AI symplectic ball-packing problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing):
`solution(k, ε)` returns Python source code.

| | [`solution_epoch.py`](solution_epoch.py) | [`solution_embedding.py`](solution_embedding.py) (from [`embedding_src/`](embedding_src/)) |
|---|---|---|
| Returns | `Hamiltonian(Q, P, t)` (PyTorch, `float64`), Epoch's ODE format | the k embeddings directly: `Embed(i, X)`, `Preimage(j, Y)`, `STAGES(i)`, `CONFIG` |
| Exact-real parameter range | — | every integer k ≥ 10 and every real ε ∈ (0, 1) ([Paper IV, §§2–7](../paper/p4/main.pdf)) |
| `float64` operating range | every 10 ≤ k ≤ 10⁵ with ε ≥ `eps_min(k)` | tests implementation margin guards grouped as `(H0)–(H15)` and `split`, down to ε ≈ 10⁻¹⁵; this is a parameter check. Accurate `float64` round-trip is documented for moderate k (≲ 200) and ε ≳ 10⁻⁴ (use `mpmath` outside) |
| ODE / grading regime | passes the documented sampled RK4 containment tests (`≤ 0.13 s/call`); global regularity differs from the smooth Hamiltonian required by the published problem | not an ODE Hamiltonian: evaluates closed-form maps and exact-real inverse certificates directly, no flow integration |
| Regularity | C^∞ near trajectories for k > 10 (exterior branch rays); piecewise C² across one window seam for k = 10 | C⁴ symplectic embeddings on B⁰(r₊), r₊ > 1 |
| Mathematical & numerical basis | elementary layouts of [Paper III](../paper/p3/main.pdf); checked numerically (RK4 at N and 2N), not proved | exact-real proof in [Paper IV, Theorem 1.1](../paper/p4/main.pdf); `float64` (`check_embedding.py`) + 100-digit (`check_embedding_mp.py`) |
| Checker | [`check_epoch.py`](check_epoch.py) | [`check_embedding.py`](check_embedding.py), [`check_embedding_mp.py`](check_embedding_mp.py) |

**Relation to the Epoch problem as posed.** Papers I–II solve the mathematical construction and computability parts of
Epoch's problem for all k ≥ 10 and ε ∈ (0, 1) with globally `C^∞` Hamiltonians, and Lean 4 also proves uniform eventual
target containment for perturbed fixed-step RK4 (`epoch_rk4_convergence` in
[`verification/RK4Convergence.lean`](../verification/RK4Convergence.lean)). Producing a single submission that meets
Epoch's published `float64` interface, global smoothness requirement, and runtime limits across all `(k, ε)` remains a
separate implementation objective (see [`EPOCH.md`](../EPOCH.md)). Accordingly:
- `solution_epoch.py` passes the documented sampled fixed-step `float64` RK4 and per-call timing checks in its
  elementary `(k, ε)` regime. Paper III proves density gaps for specified elementary classes; `eps_min(k)` is the
  threshold for the implementation’s chosen layouts, including practical numerical margins;
- `solution_embedding.py` evaluates Paper IV's closed-form `C⁴` symplectic embeddings and non-membership-certifying left
  inverses directly without ODE integration for every `k ≥ 10` and `ε ∈ (0, 1)`.

*(Note on experimental work: an unfinished prototype exploring a multi-stage global Hamiltonian lift of `Chain3` is
archived outside `program/` in [`../experiments/hamiltonian_lift/`](../experiments/hamiltonian_lift/README.md) with a
minimal reproducer and honest failure logs for its collar branch-sheet jump; it is included in the archive solely as
experimental research material and is not part of the certified deliverables.)*

The generators and `float64` checkers need only Python ≥ 3.11 and PyTorch (`pip install torch`), with no runtime `numpy`
dependency; [`check_embedding_mp.py`](check_embedding_mp.py) additionally uses `mpmath` (`pip install mpmath`). None of
the Python programs is formalised in Lean 4.

## 1. `solution_epoch.py`: Epoch's ODE interface, restricted ε

`solution(k, epsilon)` returns the source of a module defining `Hamiltonian(Q, P, t)` whose time-1 flow moves the k
closed unit balls centred at `(3i − 3, 0, 0, 0)` into a ball `B(R)` about the origin with `k / R⁴ > 1 − ε`.
`recommended_steps(k, ε)` gives a step count N for fixed-step RK4.

It implements **elementary constructions of the kind studied in Paper III**: lattice-toric layouts found by computer
search, windows, and for k = 10 the sheared-window configuration of density 360/361 (Paper III, Prop. 3.3); for some k
(e.g. 12) the layout is not the best one of Paper III. The configurations are moved into place by compositions of
explicit Hamiltonian segments. That the time-1 flow packs is supported by numerical integration, not by a proof.

### Coverage

Inputs outside the covered range raise `NotImplementedError` and report `eps_min(k)`.

| k | smallest ε covered |
|---|---|
| 10 | 0.005 (sheared windows; the limit of this configuration is 1/361 ≈ 0.0028) |
| perfect squares 16 … 10⁵ | ≈ 0.002 |
| other 10 < k ≤ 10⁵ | static deficit `1 − k/A²` of the best lattice layout, plus ≈ 0.002; e.g. k = 11: 0.104, 12: 0.148, 17: 0.097, 50: 0.051, 101: 0.041, 1000: 0.025 |
| k > 10⁵ | not covered |

For fixed non-square k these methods stop at a positive ε; Paper III proves three obstructions explaining why.

### Numerical check

[`check_epoch.py`](check_epoch.py) samples points on each unit sphere, integrates the flow with fixed-step RK4 (vector
field by autograd) and reports `R` = the largest image norm about the origin, at `N = recommended_steps(k, ε)` and `2N`.

```sh
python check_epoch.py solution_epoch.py --k 10 --eps 0.1 --recommended --N 300
```

Results ([`release-check/`](release-check); CPU, float64, numpy blocked):

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

### Smoothness and numerical notes

- **Smoothness scope.** Wrapping segments use an angle coordinate with a branch cut along an exterior ray; the
  construction keeps the ball trajectories away from those rays. In the k = 10 family one segment is piecewise C² in
  space across a moving surface that intersects the ball images (the seam between the round cap and straight side of a
  stadium-shaped window, where third derivatives are bounded with a finite jump), and time junctions have finite
  smoothness order. Thus the returned function passes the documented sampled RK4 containment and runtime tests, while its
  global regularity on ℝ⁴ × [0, 1] differs from the globally smooth Hamiltonian required by the published problem.
- **Pointwise N vs. 2N phase differences in k = 10.** Six final windows are invariant under a circle action, along whose
  orbits RK4 accumulates phase differences (up to 2.5 at ε = 0.1 on dense sphere samples, > 99.99 % tangential to the
  window, changing radius by ≤ 4.6·10⁻⁴ and converging faster than fourth order upon further halving).
- **Steep time-1 gradients.** Finite-difference symplecticity readings of the time-1 flow can reach ~4·10² at k = 10,
  ε = 0.005 due to large spatial derivatives; symplecticity of the exact Hamiltonian flow holds automatically.

## 2. `solution_embedding.py` & `embedding_src/`: closed-form C⁴ embeddings for every (k, ε)

### Readable modular sources and deterministic bundle

For human review, the implementation is organised into six short, documented modules in [`embedding_src/`](embedding_src/),
with zero dead classes:

- [`embedding_src/primitives.py`](embedding_src/primitives.py) — trigonometric step `S_m`, antiderivative `I_m`, ramp `R_m`, plateau bump, polar helpers, safeguarded scalar Newton solver (`Paper IV, §2.1–2.2`).
- [`embedding_src/keyhole.py`](embedding_src/keyhole.py) — generating-function planar keyhole `SmoothKeyhole`, closed-form datum `keyhole_star`, and fibrewise Knothe–Rosenblatt strip map `KRStrip` (`Paper IV, §2.3 & §3`).
- [`embedding_src/comparator.py`](embedding_src/comparator.py) — non-iterative parameter tuple `PiStar` and 4D keyhole comparator `Comparator3` (`Paper IV, §4 & §7.1`).
- [`embedding_src/twists.py`](embedding_src/twists.py) — deck-equivariant C⁴ toric twists `SpiralShear` routing the three marked fibres into the free corridor (`Paper IV, §5`).
- [`embedding_src/transfer.py`](embedding_src/transfer.py) — post-chart corner keyhole `Band`, simplex gluing `W`, rotated ball chart, and cancellation-free left inverse (`Paper IV, §6`).
- [`embedding_src/chain.py`](embedding_src/chain.py) — composite chain `Chain3`, grid-free analytic margin checks `(H0)–(H15)`, stage table, and deterministic special-point self-test (`Paper IV, §7.2`).

[`build_embedding.py`](build_embedding.py) packs these six modules deterministically into the standalone single-file
generator [`solution_embedding.py`](solution_embedding.py); `scripts/verify.sh` runs `python3 program/build_embedding.py --check`
to guarantee byte-for-byte agreement.

### Mathematical theorem vs. float64 evaluation

[**Paper IV**](../paper/p4/main.pdf) (*Closed-form symplectic packings of the four-ball by equal balls*) proves in full
(Theorem 1.1 & Lemma 7.4) that over exact real numbers, for **every** integer k ≥ 10 and **every** real ε ∈ (0, 1),
there is `r₊ > 1` such that `f₀, …, f_{k−1}` are C⁴ symplectic embeddings of `B⁰(r₊)` into `B⁰(R)`,
`R = (k/(1 − ε))^{1/4}`, with pairwise disjoint images, and `Preimage(j, ·)` is an exact left inverse on `f_j(B⁰(r₊))`
that certifies non-membership whenever `Y ∉ f_j(B(1))`.

In IEEE-754 **float64**, two numerical effects apply and are explicitly separated:
1. **Parameter underflow guard:** Rounding can erase strict parameter margins. The constructor evaluates all 42 named
   implementation guards on the rounded `float64` parameters and rejects inputs (`ValueError`) whenever a required strict
   inequality is lost (for example at tiny `ε ≲ 10⁻¹⁶`, whereas `solution(10, 1e-15)` succeeds).
2. **Conditioning and local Lipschitz scale:** because `ε_c = min(ε, 0.01)`, gaps of width `O(ε_c / √k)` sit next to
   coordinates of order `1`, so local Lipschitz constants reach `10⁸–10¹⁶` and condition numbers grow with `k` and
   `1 / ε_c`. In IEEE-754 `float64`:
   - for `k = 10` and `ε ≥ 0.01`, `check_embedding.py` passes all checks A–G outright;
   - for moderate `k` (`10 ≤ k ≲ 200`) and `10⁻⁴ ≤ ε < 0.01` (or `ε > 0.01` at `k ≥ 11`, which shares `ε_c = 0.01`),
     fixed-step `float64` finite differences (B) or chord bisections at `10⁻¹¹` (G) can hit 53-bit resolution limits
     (e.g. at `k = 10, ε = 0.002` the centre `X = 0` of ball 9 maps to `|Z₀| ≈ 6.2·10⁻⁵`, giving a `float64` round-trip
     error of `4.86·10⁻⁷` that drops to `4.66·10⁻⁹³` in 100-digit arithmetic);
   - for very large `k` (`k ≳ 10³`) or tiny `ε` (`ε ≲ 10⁻⁶`), 53-bit `float64` conditioning saturates on wild-stack
     cells, so multi-precision evaluation (`check_embedding_mp.py`, e.g. `--dps 100`) is required for accurate round-trip
     and Jacobian evaluation. Every sector and band moment in `transfer.py` is recovered from non-negative coordinates
     without `1 − X₁ − X₂` cancellation.

The `mpmath` checker first constructs and cross-checks a `float64` submission. Its CLI therefore requires
`float64`-admissible parameters (typically `ε ≳ 10⁻¹⁵`); accepting a decimal string does not remove this entry
restriction. Positivity of analytic parameter margins at this scale does not establish accurate `float64` inverses.

### Checkers and verification logs

1. **[`check_embedding.py`](check_embedding.py)** (`float64`; exits with code `1` on any failure, with explicit
   non-finiteness gates on outputs, preimages, and finite-difference Jacobians): tests **17 deterministic special points
   per ball** (ball centre `0`, `±e₁..±e₄`, and 8 zero-fibre/zero-base unit diagonals) plus random sphere and interior
   samples for (A) containment `|Y| < R`, (B) **normalised** symplectic residual `max |JᵀΩJ − Ω| / max(1, ‖J‖_F²)` via
   Richardson central differences at `h` and `h/2`, (C) round-trip `‖Preimage(i, Embed(i, X)) − X‖ ≤ rt_tol`,
   (D) pairwise disjointness, (E) Monte Carlo volume coverage `1 − ε`, (F) wall time, and (G) chord-bisection continuity
   down to separation `10⁻¹¹`.
2. **[`check_embedding_mp.py`](check_embedding_mp.py)** (arbitrary-precision `mpmath`, default `D = 100` digits; exits
   with code `1` on any failure): **transforms the submitted Python source via Python's `ast` module and executes it
   directly on a D-digit `mpmath` tensor backend** (converting all float literals to exact `mpf` strings, raising
   `newton_bracket` default iterations from `60` to `max(180, 3D)`, and skipping redundant load-time float64 self-tests;
   note that `randn`/`rand` inside the lightweight `_MpTorch` shim draw initial test coordinates in `float64` before
   converting to `mpf`). Every run enforces in its final `PASS` gate:
   - **0. Source consistency:** `‖Y_f64 − Y_mp64‖ / max(1, ‖J‖_F) ≤ 10⁻¹⁰` across all `k` balls. For non-representative
     balls at `k > 25`, the denominator uses the running maximum Jacobian norm from representative balls, rather than
     a pointwise local norm;
   - **1–3. Containment, round-trip (`≤ 10⁻⁷⁵`), disjointness, and Richardson symplecticity (`h = 10⁻³³` at `D = 100`,
     `≤ 10⁻⁵⁰`):** for `k ≤ 25` (or with `--full-balls`), evaluates all `17 × k` special points + `mp_random` points,
     all `k × (k − 1)` disjointness pairs, and chords on all `k` balls; for `k > 25` without `--full-balls`, evaluates
     full special + random sets, disjointness, and chords on representative balls `{0, 4, 8, 9, k − 1}` plus centre + 1
     random point on every other ball, **together with 100 % of points across all `k` balls flagged by B or C in the
     `float64` scan**;
   - **4. Interval-preserving continuity diagnostic:** on **100 %** of chord intervals flagged by G in the `float64`
     chord scan above, retains the larger-gap half-interval at every bisection step down to separation `10⁻³⁰`
     (avoiding midpoint re-centring; this is a targeted numerical diagnostic rather than a formal proof, which is given
     in Paper IV) and requires end-to-end image gap `≤ 10⁻¹⁰` with linear shrinkage.

```sh
python check_embedding.py solution_embedding.py --k 10 --eps 0.1 --h 1e-7
python check_embedding_mp.py solution_embedding.py --k 10 --eps 0.002 --dps 100 --chords 100
```

Float64 results ([`release-check/embedding/`](release-check/embedding); `--h 1e-7`, `sym_tol = 1e-5`, `rt_tol = 1e-7`):

| k | ε | radius margin (A) | overlaps / double cover (D, E) | covered (E; expected 1 − ε) | random round-trip > 10⁻⁷ | norm. symp. residual (B) | G chord flags / Lipschitz est. | geometry (A, D, E) | float64 fixed-step flags |
|---|---|---|---|---|---|---|---|---|---|
| 10 | 0.1 | 4.30e-02 | 0 / 0 | 0.89999 ± 0.00067 | 0 | 1.6e-08 | 0 / 7.2e+08 | pass | none (`PASS`) |
| 10 | 0.01 | 1.07e-05 | 0 / 0 | 0.98969 ± 0.00023 | 0 | 1.6e-08 | 0 / 7.2e+08 | pass | none (`PASS`) |
| 10 | 0.002 | 4.06e-06 | 0 / 0 | 0.99795 ± 0.00010 | 0 (ball 9 centre: 4.9e-07) | 4.5e-08 | 2 / 1.3e+11 | pass | G (2), special C (1) |
| 10 | 0.0001 | 1.02e-05 | 0 / 0 | 0.99991 ± 0.00002 | 0 | 2.7e-05 | 143 / 1.7e+12 | pass | G (143), B, special C |
| 11 | 0.01 | 2.19e-05 | 0 / 0 | 0.99020 ± 0.00022 | 0 | 1.4e-08 | 4 / 1.0e+11 | pass | G (4) |
| 17 | 0.01 | 3.93e-05 | 0 / 0 | 0.98993 ± 0.00022 | 0 | 6.0e-07 | 57 / 6.8e+11 | pass | G (57) |
| 30 | 0.01 | 1.95e-05 | 0 / 0 | 0.99000 ± 0.00022 | 0 | 3.7e-08 | 207 / 1.2e+12 | pass | G (207) |
| 50 | 0.01 | 1.26e-05 | 0 / 0 | 0.98977 ± 0.00022 | 0 | 2.3e-02 | 409 / 2.0e+12 | pass | G (409), B |
| 101 | 0.01 | 6.76e-06 | 0 / 0 | 0.99006 ± 0.00022 | 2 | 8.6e-02 | 938 / 6.0e+12 | pass | G (938), B, C |

Reproducible 100-digit `check_embedding_mp.py` logs ([`release-check/embedding_mp/`](release-check/embedding_mp); AST loader `target_iters = 300`, `h = 10⁻³³`):

| k | ε | chords / ball scope | f64 vs mp64 consistency | MP round-trip | re-checked f64 C flags | MP symp. & re-checked f64 B (`h = 10⁻³³`) | re-checked f64 G flags (sep ≤ 10⁻³⁰) | MP result |
|---|---|---|---|---|---|---|---|---|
| 10 | 0.1 | 100 × all 10 balls | 1.73e-15 | ≤ 8.79e-88 | 0 flags | max 3.81e-62 (0 flags) | 0 flags | `PASS` |
| 10 | 0.002 | 100 × all 10 balls | 1.88e-15 | ≤ 8.92e-88 | 1/1 → 4.66e-93 | max 2.73e-63 (0 flags) | 2/2 → gap ≤ 9.66e-20 | `PASS` |
| 10 | 0.0001 | 5 × all 10 balls | 9.21e-15 | ≤ 1.38e-87 | 5/5 → ≤ 8.36e-90 | max 2.52e-63 (1/1 → 3.08e-75) | 21/21 → gap ≤ 1.07e-14 | `PASS` |
| 11 | 0.01 | 100 × all 11 balls | 2.06e-15 | ≤ 2.20e-88 | 0 flags | max 1.97e-62 (0 flags) | 4/4 → gap ≤ 5.80e-20 | `PASS` |
| 101 | 0.01 | 10 × 5 rep. balls (B/C all 101) | 9.38e-15 | ≤ 4.39e-88 | 3/3 → ≤ 1.30e-92 | max 1.18e-62 (1/1 → 2.66e-75) | 11/11 → gap ≤ 5.92e-16 | `PASS` |
