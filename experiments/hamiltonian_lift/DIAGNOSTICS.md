# Additional transfer-phase diagnostics

Cross-review of the archived prototype identified an algebraic seam-normalisation issue in
[`hamiltonian_src/chain_primitive.py`](hamiltonian_src/chain_primitive.py), in addition to the finite-resolution
ray-unwrapping behaviour described in the [original diagnostic record](README.md). The source and its failure logs
are preserved as tested; the following correction has **not** been applied to the executable prototype.

The prototype uses the reduction primitive `S_red = -3*n*psi` and the sector constant `_SEC_CONST['2s'] = 1/4`.
These choices leave an additive `1/6` discrepancy at the `c_2 = +m` band/sector seam. Matching the local potentials
across all six band boundaries and the fundamental-strip cut instead gives

```text
S_red = -n * (3*psi + 1/6)
sector constants: 0 -> 0, 1 -> 1/12, 2s -> 1/12, 2c -> 0
strip constants: 0 -> 0, 1 -> 0, 2 -> -1/12
```

These are local potential-matching identities, with the projective phase gauge included. They do not establish a
global branch-selection algorithm or certify the Hamiltonian lift. A follow-up must first derive compatible local
potentials and their additive constants, then rerun scalar continuity, trajectory and collar-clearance checks; a
remaining jump should not be attributed solely to missed turns in a finite radial sampling scheme.

Paper IV, §8 defines its mathematical primitive by the global radial Poincaré integral, so its generator theorem
does not depend on these experimental constants. The experimental implementation remains unfinished and outside
the passed deliverables.
