# Experimental Archive: Closed-Form Hamiltonian Lift (`solution_hamiltonian.py`)

> **Status: Experimental / Unfinished Research Prototype — NOT a passed or certified deliverable.**
> Kept outside `program/` in `experiments/hamiltonian_lift/` and included in the `1.2.0` archive solely for transparency
> and reproducibility of known failure cases and diagnostics. Do **not** cite `solution_hamiltonian.py` as a verified
> global `C³` Hamiltonian implementation.

## Contents

- [`hamiltonian_src/`](hamiltonian_src/) and [`build_hamiltonian.py`](build_hamiltonian.py) → [`solution_hamiltonian.py`](solution_hamiltonian.py):
  prototype 6-stage Hamiltonian lift built on Paper IV's closed-form embedding chain `Chain3(k, eps)`.
- [`check_hamiltonian.py`](check_hamiltonian.py): checks trajectory velocity residuals, boundary/junction values,
  spatial support, two-sided `±10⁻¹⁰` scalar continuity across the plateau/collar boundary `|u| = r_1`, and radial
  collar step continuity.
- [`repro_branch_jump.py`](repro_branch_jump.py) & [`logs/repro_branch_jump.log`](logs/repro_branch_jump.log): minimal
  standalone fixed-offset (`±10⁻¹⁰`) neighbour probe illustrating both the resolved `fast_plateau` normalization bug and
  the remaining unresolved collar jump (alongside the local seam-constant diagnostic in [`DIAGNOSTICS.md`](DIAGNOSTICS.md)).
- [`logs/current_honest_check.log`](logs/current_honest_check.log) & [`logs/current_honest_check.json`](logs/current_honest_check.json):
  current honest checker output (`k ∈ {11, 12}, ε ∈ {0.05, 0.001}`: `2 PASS / 2 FAIL`), replacing stale pre-audit logs
  that checked gradients only on `|u| ≤ 1`.

## Summary of known correctness issues and diagnostics

1. **Resolved plateau/collar normalization bug (`k = 11, ε = 0.05, t = 0.6`, ball 9):**
   - Previously, `fast_plateau=True` inside `|u| ≤ r_1 √0.999999` evaluated raw un-unwrapped primitives whereas the
     collar branch evaluated radially unwrapped primitives, creating an `O(scale² / v³)` constant offset that spatial
     cutoff multiplication `χ(|u|²)` turned into a true discontinuity (`H = −83.29` vs. `+81175.70` across `±10⁻¹⁰`).
   - Evaluating both branches with the same basepoint-anchored primitive fixes `(k = 11, ε = 0.05)` (`H = −83.29216339`
     vs. `−83.29216337`, `H_switch_jump = 3.64e-8`, `PASS` in `logs/current_honest_check.log`).
2. **Remaining unresolved integer-turn sheet jump in cutoff collars (`k = 11, ε = 0.001` and `k = 12, ε = 0.001`):**
   - Stages 1–8 of `Chain3` have single-valued closed-form primitives on `B⁰(r₊)`, whereas Stages 9–11 (`Transfer3`:
     sector action-angles and projective phase `arg(Z₀)/(2π)`) require continuous sheet unwrapping from `a_i` to `w`.
   - Along straight Euclidean rays `a_i → w` in `B(r_dom)`, `f_i` winds rapidly when a collar ray passes near small
     `|Z₀|`, so finite-depth ray bisection misses integer turns: in `repro_branch_jump.py` (`k = 12, ε = 0.001, t = 0.85`,
     ball 11), points separated by `2·10⁻¹⁰` across `|u| = r_1` evaluate to `H = −10.37766161` and `H = +7.46159517`
     (`FAIL` in `logs/current_honest_check.log`).
3. **Methodological boundary on branch-continuity diagnostics:**
   - Large second differences on a fixed radial grid do not by themselves prove a discontinuity (steep smooth gradients
     also produce large coarse steps), and conversely repeating `round`-based unwrapping on a denser finite grid or
     halting adaptive subdivision at a `tiny-span` threshold is only a numerical heuristic—not a rigorous certificate
     that zero `±1` winding pairs were missed between sample nodes.
   - Establishing a genuine discontinuity vs. continuity requires two-sided shrinking-distance limits (`e → 0±`; note
     that `repro_branch_jump.py` evaluates a fixed `±10⁻¹⁰` neighbour probe) for refutation, compatible local seam
     constants (see [`DIAGNOSTICS.md`](DIAGNOSTICS.md)), and an analytic single-valuedness / winding-free domain proof
     (for instance interpolating the tail in convex post-comparator coordinates `(G − J(p), v, w)` bounded away from
     `Z₀ = 0`) for all-`(k, ε)` certification. Fixing an individual counterexample does not prove global `C³` regularity.
4. **Other unproved heuristics in Stages 0–4:**
   - `box_radii`, `tau`, and the 4D translation lift amplitudes `A_lift0, A_lift4` rely on finite directional/time
     sampling (and an empirical formula for `k > 500`), and the small-`ρ` trajectory diagnostic (`0 < ρ ≤ 10⁻⁴`) uses
     6-point Gauss–Legendre quadrature rather than analytic higher-derivative bounds.
