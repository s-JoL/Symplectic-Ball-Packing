# Programs

Two self-contained single-file generators inspired by the
[Epoch AI symplectic ball-packing problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing):
`solution(k, ε)` returns Python source code. They take complementary computational routes.

| | [`solution_epoch.py`](solution_epoch.py) | [`solution_embedding.py`](solution_embedding.py) (built from [`embedding_src/`](embedding_src/)) |
|---|---|---|
| Returns | a Hamiltonian `Hamiltonian(Q, P, t)` (PyTorch, float64), Epoch's ODE format | the k embeddings directly: `Embed(i, X)`, `Preimage(j, Y)`, `STAGES(i)`, `CONFIG` |
| Exact-real parameter range | — | every integer k ≥ 10 and every real ε ∈ (0, 1) (proved in [Paper IV](../paper/p4/main.pdf)) |
| Float64 operating range | every 10 ≤ k ≤ 10⁵ with ε ≥ `eps_min(k)` | checks analytic margins `(H0)–(H15)` in float64 (accepts down to ε ≈ 10⁻¹⁵; round-trip `< 10⁻⁷` for ε ≳ 10⁻⁶ and moderate k) |
| Runtime & RK4 budget | within Epoch's budget: fixed-step float64 RK4, ≤ 0.13 s per Hamiltonian call on 3000–20 000 points | not an ODE Hamiltonian: evaluates closed-form maps directly, no flow integration |
| Smoothness | C^∞ near trajectories for k > 10 (exterior branch rays); piecewise C² across one window seam for k = 10; finite-order at time junctions | C⁴ symplectic embeddings on B⁰(r₊), r₊ > 1 |
| Mathematical & numerical basis | elementary layouts of [Paper III](../paper/p3/main.pdf); correctness checked numerically (RK4 at N and 2N), not proved | complete exact-real proof in [Paper IV](../paper/p4/main.pdf), plus float64 (`check_embedding.py`) and 100-digit (`check_embedding_mp.py`) checks |
| Checker | [`check_epoch.py`](check_epoch.py) | [`check_embedding.py`](check_embedding.py), [`check_embedding_mp.py`](check_embedding_mp.py) |

**Relation to the Epoch problem as posed.** Epoch asks for a single algorithm that, for every k ≥ 10 and ε ∈ (0, 1),
outputs a globally smooth `Hamiltonian(Q, P, t)` integrable within fixed runtime limits. Papers I–II solve the
mathematical and computability parts (with Lean 4 proofs), whereas their smooth non-toric flow is too stiff for
fixed-step float64 RK4 integration. Here `solution_epoch.py` keeps the fast RK4 Hamiltonian interface over the
elementary `(k, ε)` regime (with the smoothness caveats below), while `solution_embedding.py` covers all `(k, ε)` in
exact arithmetic by evaluating the symplectic packing maps directly without ODEs.

The generators and float64 checkers need only Python and PyTorch (`pip install torch`), with no runtime numpy
dependency; [`check_embedding_mp.py`](check_embedding_mp.py) additionally uses `mpmath` (`pip install mpmath`). Neither
program is part of the Lean 4 formalisation.

## 1. `solution_epoch.py`: Epoch's interface, restricted ε

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
  smoothness order. Thus the returned function satisfies the RK4 trajectory and runtime checks, but is not globally
  C^∞ on ℝ⁴ × [0, 1].
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
- [`embedding_src/chain.py`](embedding_src/chain.py) — composite chain `Chain3`, grid-free analytic margin checks `(H0)–(H15)`, stage table, and deterministic special-point self-test (`Paper IV, §7.2–8`).

[`build_embedding.py`](build_embedding.py) packs these six modules deterministically into the standalone single-file
generator [`solution_embedding.py`](solution_embedding.py); `scripts/verify.sh` runs `python3 program/build_embedding.py --check`
to guarantee byte-for-byte agreement.

### Mathematical theorem vs. float64 evaluation

[**Paper IV**](../paper/p4/main.pdf) (*Closed-form symplectic packings of the four-ball by equal balls*) proves in full
(Theorem 1.1) that over exact real numbers, for **every** integer k ≥ 10 and **every** real ε ∈ (0, 1), there is
`r₊ > 1` such that `f₀, …, f_{k−1}` are C⁴ symplectic embeddings of `B⁰(r₊)` into `B⁰(R)`, `R = (k/(1 − ε))^{1/4}`,
with pairwise disjoint images, and `Preimage(i, ·)` is an exact left inverse on `fᵢ(B⁰(r₊))`.

In IEEE-754 **float64**, two numerical effects apply and are explicitly separated:
1. **Parameter underflow guard:** `solution(k, eps)` evaluates all 42 analytic margins `(H0)–(H15)` on the float64
   parameters and raises `ValueError` if rounding zeroes a strict margin (for example `solution(10, 1e-16)`, where
   `1.0 - 1e-16 == 1.0` in float64 makes `η = 0` and `a − ρ_b = 0`; `solution(10, 1e-15)` succeeds).
2. **Conditioning and local Lipschitz scale:** gaps of width `O(ε_c / √k)` sit next to coordinates of order `1`, so
   local Lipschitz constants reach `10⁸–10¹⁵` and condition numbers reach `10⁷–3·10⁹` (for instance, at `k = 10,
   ε = 0.002` the centre `X = 0` of ball 9 maps to `|Z₀| ≈ 6.2·10⁻⁵`, amplifying 53-bit `1 − |y|²` rounding in
   `unchart` to a float64 round-trip residual of `4.86·10⁻⁷`, which drops to `4.66·10⁻⁹³` in 100-digit arithmetic).
   Every sector and band moment in `transfer.py` is recovered from non-negative coordinates without `1 − X₁ − X₂`
   cancellation, so ball centres, axis boundary points `±e_a`, and zero-fibre points never produce `NaN`.

### Checkers and verification logs

1. **[`check_embedding.py`](check_embedding.py)** (float64; exits with code `1` on any failure): tests **17 deterministic
   special points per ball** (ball centre `0`, `±e₁..±e₄`, and 8 zero-fibre/zero-base unit diagonals) plus random sphere
   and interior samples for (A) containment `|Y| < R`, (B) **normalised** symplectic residual
   `max |JᵀΩJ − Ω| / max(1, ‖J‖_F²)` via Richardson-extrapolated central differences at `h` and `h/2` (note: normalised
   by `max(1, ‖J‖_F²)` because `‖J‖_F` is large), (C) round-trip `‖Preimage(i, Embed(i, X)) − X‖ ≤ rt_tol`,
   (D) pairwise disjointness, (E) Monte Carlo volume coverage `1 − ε`, (F) wall time, and (G) chord-bisection continuity
   down to separation `10⁻¹¹`.
2. **[`check_embedding_mp.py`](check_embedding_mp.py)** (arbitrary-precision `mpmath`, default `D = 100` digits; exits
   with code `1` on any failure): **executes the submitted Python source directly on a D-digit `mpmath` tensor backend**
   (not an uncoupled model). Every run enforces in its final `PASS` gate:
   - **0. Source consistency:** `‖Y_f64 − Y_mp64‖ / max(1, ‖J‖_F) ≤ 10⁻¹⁰` across all `k` balls;
   - **1–3. Containment, round-trip (`≤ 10⁻⁸⁰`), disjointness, and Richardson symplecticity (`≤ 10⁻⁵⁰`)** on all
     special points, random samples, and **100 %** of points flagged by B or C in float64;
   - **4. Interval-preserving continuity bisection:** on **100 %** of chord intervals flagged by G in float64, retains
     the larger-gap half-interval at every bisection step all the way down to separation `10⁻³⁰` (never switching to a
     midpoint perturbation that could step to one side of a jump) and requires end-to-end image gap `≤ 10⁻¹⁰` with
     linear shrinkage.

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

Reproducible 100-digit `check_embedding_mp.py` logs ([`release-check/embedding_mp/`](release-check/embedding_mp)):

| k | ε | chords/ball | f64 vs mp64 consistency | 17×k special + random round-trip | re-checked f64 C flags | re-checked f64 B flags (h = 10⁻³³) | re-checked f64 G flags (sep ≤ 10⁻³⁰) | MP result |
|---|---|---|---|---|---|---|---|---|
| 10 | 0.1 | 100 | 1.7e-15 | ≤ 4.4e-88 | 0 flags | 0 flags (max 6.5e-71) | 0 flags | `PASS` |
| 10 | 0.002 | 100 | 1.9e-15 | ≤ 4.5e-88 | 1/1 → 4.7e-93 | 0 flags (max 1.4e-61) | 2/2 → gap ≤ 9.7e-20 | `PASS` |
| 10 | 0.0001 | 5 | 9.2e-15 | ≤ 1.4e-87 | 5/5 → ≤ 8.4e-90 | 1/1 → 3.1e-75 | 21/21 → gap ≤ 1.1e-14 | `PASS` |
| 11 | 0.01 | 100 | 2.1e-15 | ≤ 2.2e-88 | 0 flags | 0 flags (max 4.5e-69) | 4/4 → gap ≤ 5.8e-20 | `PASS` |
| 101 | 0.01 | 10 (rep.) | 9.4e-15 | ≤ 4.4e-88 | 3/3 → ≤ 1.3e-92 | 1/1 → 2.7e-75 | 11/11 → gap ≤ 5.9e-16 | `PASS` |
