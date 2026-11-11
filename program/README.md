# Program: Hamiltonian packings for the Epoch AI interface

[`solution_epoch.py`](solution_epoch.py) is a single self-contained file in the format of the
[Epoch AI problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing):
`solution(k, epsilon)` returns the source of a module defining `Hamiltonian(Q, P, t)` (PyTorch, float64),
whose time-1 flow is designed to move the k closed unit balls centred at `(3i − 3, 0, 0, 0)` into a ball
`B(R)` about the origin with `k / R⁴ > 1 − ε`.

It implements **elementary constructions of the kind studied in Paper III** (lattice-toric layouts found by
computer search, windows, and for k = 10 the sheared-window configuration of density 360/361 of Paper III, Prop. 3.3);
for some k (e.g. 12) the layout is not the best one of Paper III. The configurations are moved into place by compositions of explicit
Hamiltonian segments. It does **not** implement the construction of Papers I–II, which covers every ε but
is designed for proof; its flow is too stiff to integrate within Epoch's time limits.

**Status.** The configurations and the motions are explicit. That the time-1 flow packs is supported by
numerical integration (below), not by a proof, and the program is not part of the formal verification.

**Known limitation: the returned Hamiltonian is not globally smooth.** The wrapping segments use an angle
coordinate with a branch cut (a ray from the wrapping centre); across that ray the Hamiltonian jumps (for example
k = 16, ε = 0.01, t = 0.415, Q = (0.2, 0.5), P = (0.3, ±δ): H tends to 26.50 and 54.17 as δ → 0). The
construction keeps the ball trajectories away from the cuts, which is why the flow checks pass, but the function
is only piecewise smooth in space, and its time dependence is only finitely smooth at the junctions of the
segments. It therefore does not meet the smoothness requirement of the Epoch problem as stated; a global smooth
extension that agrees with it near the trajectories is not yet implemented.

## Coverage

Inputs outside the covered range raise `NotImplementedError` and report the smallest covered ε; a
Hamiltonian that is not expected to pack is never returned. `eps_min(k)` gives the bound.

| k | smallest ε covered |
|---|---|
| 10 | 0.005 (sheared windows; the limit of this configuration is 1/361 ≈ 0.0028) |
| perfect squares 16 … 10⁵ | ≈ 0.002 |
| other 10 < k ≤ 10⁵ | static deficit `1 − k/A²` of the best lattice layout, plus ≈ 0.002; e.g. k = 11: 0.104, 12: 0.148, 17: 0.097, 50: 0.051, 101: 0.041, 1000: 0.025 |
| k > 10⁵ | not covered |

For fixed non-square k these methods stop at a positive ε; Paper III proves obstructions explaining why.

## Numerical check

[`check.py`](check.py) samples points on each unit sphere, integrates the flow with fixed-step RK4 (vector
field by autograd) and reports `R` = the largest image norm, measured about the origin. It runs at
`N = recommended_steps(k, ε)` and at `2N`; both must pass.

```sh
pip install torch numpy
python check.py solution_epoch.py --k 10 --eps 0.1 --recommended --N 300
```

Results of the release check (CPU, float64; "difference" is the largest pointwise difference between the
runs at N and 2N):

| k | ε | sample points | N, 2N | R at 2N | R needed | margin | difference | longest H call |
|---|---|---|---|---|---|---|---|---|
| 10 | 0.1 | 3000 | 2592, 5184 | 1.820626 | 1.825742 | 5.1e-3 | 9.2e-4 | 0.07 s |
| 10 | 0.02 | 3000 | 5584, 11168 | 1.786385 | 1.787284 | 9.0e-4 | 1.6e-6 | 0.05 s |
| 10 | 0.005 | 3000 | 14160, 28320 | 1.780395 | 1.780509 | 1.1e-4 | 4.8e-5 | 0.06 s |
| 11 | 0.11 | 3300 | 400, 800 | 1.874150 | 1.874997 | 8.5e-4 | 3.0e-5 | 0.01 s |
| 12 | 0.16 | 3600 | 400, 800 | 1.942488 | 1.944131 | 1.6e-3 | 2.6e-5 | 0.01 s |
| 16 | 0.01 | 4800 | 400, 800 | 2.004045 | 2.005031 | 9.9e-4 | 1.1e-4 | 0.02 s |
| 17 | 0.10 | 5100 | 800, 1600 | 2.084091 | 2.084739 | 6.5e-4 | 7.3e-6 | 0.03 s |
| 25 | 0.005 | 7500 | 800, 1600 | 2.238301 | 2.238872 | 5.7e-4 | 1.7e-5 | 0.04 s |
| 50 | 0.06 | 10000 | 800, 1600 | 2.699189 | 2.700602 | 1.4e-3 | 4.6e-6 | 0.05 s |
| 100 | 0.003 | 10000 | 800, 1600 | 3.164245 | 3.164654 | 4.1e-4 | 7.2e-6 | 0.05 s |
| 101 | 0.05 | 10100 | 800, 1600 | 3.209466 | 3.211068 | 1.6e-3 | 2.7e-5 | 0.05 s |
| 1000 | 0.03 | 20000 | 1600, 3200 | 5.664869 | 5.666398 | 1.5e-3 | 4.3e-6 | 0.09 s |

All twelve pass at both step counts. The longest single Hamiltonian call is under 0.1 s for the 3000–20000
points evaluated per call. Limits of this evidence: finitely many sample points per sphere, one integrator,
float64 only; Epoch's own verification settings are not public.

The module-level strings `SRC`, `PLAN_SRC` and `EXT_SRC` in `solution_epoch.py` are generated source code of
the building blocks and are executed as they are.
