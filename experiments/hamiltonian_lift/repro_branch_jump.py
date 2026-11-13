"""Minimal fixed-offset (`+-1e-10`) neighbour failure probe for experimental `solution_hamiltonian.py`.

Evaluates scalar `H(Q, P, t)` at fixed offsets `e = +-1e-10` straddling the `|u| = r_1 * sqrt(0.999999)` boundary:
  1. Former plateau/collar normalization probe (`k=11, eps=0.05, t=0.6, ball 9`, resolved in current prototype):
     An earlier `fast_plateau` branch used un-unwrapped local primitives inside `|u| <= r_1 * sqrt(0.999999)`
     and ray-unwrapped primitives outside (`-83.29` vs `+81175.70`). Evaluating both sides with the same
     basepoint-anchored primitive removes that mismatch (`H = -83.2921633895` vs `-83.2921633673` at `e = +-1e-10`).
  2. Remaining unresolved neighbour jump probe (`k=12, eps=0.001, t=0.85, ball 11`):
     At fixed `e = +-1e-10`, the prototype evaluates to `H = -10.3776616129` vs `+7.4615951668` across neighbouring
     collar rays near small `|Z_0|` (see also `DIAGNOSTICS.md` on local seam-constant matching).
"""
from __future__ import annotations

import math
from pathlib import Path
import sys
import torch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import solution_hamiltonian as gen  # type: ignore


def main() -> None:
    torch.set_num_threads(2)

    print("=== 1. Former plateau/collar switch reproducer (k=11, eps=0.05, t=0.6, ball 9) ===")
    ns11: dict = {}
    exec(gen.solution(11, 0.05), ns11)
    h11, H11 = ns11["_H_OBJ"], ns11["Hamiltonian"]
    t = 0.6
    _, s, _ = h11._stage_clock(t)
    v, _ = h11.tail_clock.evaluate(s)
    r1, _ = h11._radii_for_v(v)
    d = torch.tensor(
        [-0.14216543802532278, -0.3387938475081023, -0.9183258638487032, -0.14725937969534547],
        dtype=torch.float64,
    )
    for e in (-1e-10, 1e-10):
        u = (r1 * 0.999999 ** 0.5 * (1.0 + e) * d).unsqueeze(0)
        w = (1.0 - v) * h11.base_a[9] + v * u
        y = h11.cp.batched_local_pass(torch.tensor([9]), w)[0] / v
        print(f"  e={e:+.1e}: H = {float(H11(y[:, :2], y[:, 2:], t)):.10f}")

    print("\n=== 2. Remaining unresolved ray-bisection sheet jump (k=12, eps=0.001, t=0.85, ball 11) ===")
    ns12: dict = {}
    exec(gen.solution(12, 0.001), ns12)
    h12, H12 = ns12["_H_OBJ"], ns12["Hamiltonian"]
    g = torch.Generator().manual_seed(2026 + 17)
    for _ in range(3):
        _ = torch.randn(32, 4, generator=g, dtype=torch.float64)
    _ = torch.randn(7, 4, generator=g, dtype=torch.float64)
    d_rand = torch.randn(5, 4, generator=g, dtype=torch.float64)
    d_rand = d_rand / d_rand.norm(dim=-1, keepdim=True)
    d_bad = d_rand[2:3]
    t85 = 0.85
    _, s85, _ = h12._stage_clock(t85)
    v85, _ = h12.tail_clock.evaluate(s85)
    r1_85, _ = h12._radii_for_v(v85)
    r_sw = r1_85 * math.sqrt(0.999999)
    for e in (-1e-10, 1e-10):
        u = (r_sw * (1.0 + e)) * d_bad
        w = (1.0 - v85) * h12.base_a[11] + v85 * u
        y = h12.cp.batched_local_pass(torch.tensor([11]), w)[0] / v85
        print(f"  e={e:+.1e}: H = {float(H12(y[:, :2], y[:, 2:], t85)):.10f}")


if __name__ == "__main__":
    main()
