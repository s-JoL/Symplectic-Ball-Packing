"""Numerical check of solution_epoch.py in the format of the Epoch AI problem.

Epoch's own verification script is not public; this script follows the problem statement and takes the
strict reading where it is ambiguous (radius measured about the origin, two step counts compared).

For each (k, eps):
  1. solution(k, eps) returns the source of a module defining Hamiltonian(Q, P, t) (PyTorch, float64);
  2. points on each unit sphere about (3i - 3, 0, 0, 0) are flowed to time 1 with fixed-step RK4,
     the vector field (dq/dt, dp/dt) = (dH/dp, -dH/dq) obtained by autograd;
  3. R is the largest norm of the image points (ball about the origin); the check passes if k / R^4 > 1 - eps
     at every requested step count. The largest pointwise difference between the last two step counts is reported
     as an integration-error estimate, together with the longest single Hamiltonian call.
A final line `RESULT {json}` summarises the run.

    python check.py solution_epoch.py --k 10 --eps 0.1 --steps 2592 5184 --N 500
    python check.py solution_epoch.py --k 16 --eps 0.01 --recommended --N 500     # N_rec and 2 N_rec

Sampling the sphere is evidence, not proof: points between samples are not checked.
Coordinates: R^4 = (q1, q2, p1, p2), omega = dq1 ^ dp1 + dq2 ^ dp2.
"""
import argparse
import importlib.util
import json
import os
import shutil
import tempfile
import time
import types

import torch

torch.set_default_dtype(torch.float64)
DIM = 2


def load_module(path):
    """Load the submission from an empty temporary directory, so that it cannot read neighbouring files."""
    tmp = tempfile.mkdtemp(prefix="packing_submission_")
    path = shutil.copy(path, os.path.join(tmp, "solution.py"))
    os.chdir(tmp)
    spec = importlib.util.spec_from_file_location("submission", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def hamiltonian_from_source(src):
    m = types.ModuleType("hamiltonian_module")
    exec(compile(src, "<hamiltonian>", "exec"), m.__dict__)
    return m.Hamiltonian


def sample_spheres(k, n_per_sphere, radius=1.0, seed=0, device="cpu"):
    g = torch.Generator().manual_seed(seed)
    x = torch.randn(k, n_per_sphere, 2 * DIM, generator=g)
    x = radius * x / x.norm(dim=-1, keepdim=True)
    x[:, :, 0] += 3.0 * torch.arange(k).unsqueeze(1)
    return x.reshape(k * n_per_sphere, 2 * DIM).to(device)


def vector_field(H, x, t, timing):
    q = x[:, :DIM].detach().requires_grad_(True)
    p = x[:, DIM:].detach().requires_grad_(True)
    t0 = time.time()
    h = H(q, p, float(t))
    timing.append(time.time() - t0)
    if h.dtype != torch.float64 or h.shape != (x.shape[0],):
        raise ValueError(f"Hamiltonian must return float64 of shape (N,), got {h.dtype} {tuple(h.shape)}")
    dq, dp = torch.autograd.grad(h.sum(), (q, p))
    return torch.cat([dp, -dq], dim=1)


def rk4_flow(H, x, steps, timing):
    dt = 1.0 / steps
    for s in range(steps):
        t = s * dt
        k1 = vector_field(H, x, t, timing)
        k2 = vector_field(H, x + 0.5 * dt * k1, t + 0.5 * dt, timing)
        k3 = vector_field(H, x + 0.5 * dt * k2, t + 0.5 * dt, timing)
        k4 = vector_field(H, x + dt * k3, t + dt, timing)
        x = (x + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)).detach()
    return x


def check(mod, k, eps, steps_list, n_per_sphere, device):
    t0 = time.time()
    src = mod.solution(k, eps)
    t_solution = time.time() - t0
    H = hamiltonian_from_source(src)
    x0 = sample_spheres(k, n_per_sphere, device=device)
    r_needed = (k / (1 - eps)) ** 0.25
    summary = dict(k=k, eps=eps, R_needed=r_needed, solution_seconds=round(t_solution, 2),
                   points=int(x0.shape[0]), runs={})
    images = {}
    for steps in steps_list:
        timing = []
        t1 = time.time()
        y = rk4_flow(H, x0, steps, timing)
        r = y.norm(dim=1).max().item()
        ok = (k / r ** 4 > 1 - eps) and not torch.isnan(y).any().item()
        images[steps] = y
        summary["runs"][steps] = dict(R=r, density=k / r ** 4, passed=ok,
                                      longest_H_call_s=round(max(timing), 3), seconds=round(time.time() - t1, 1))
        print(f"k={k} eps={eps} steps={steps}: R={r:.6f} (need < {r_needed:.6f}), k/R^4={k / r ** 4:.6f}, "
              f"{'PASS' if ok else 'FAIL'}, longest H call {max(timing):.3f}s", flush=True)
    if len(steps_list) > 1:
        a, b = images[steps_list[-2]], images[steps_list[-1]]
        summary["max_point_difference"] = (a - b).norm(dim=1).max().item()
    summary["passed"] = all(v["passed"] for v in summary["runs"].values())
    summary["margin"] = r_needed - max(v["R"] for v in summary["runs"].values())
    print("RESULT " + json.dumps(summary), flush=True)
    return summary


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("solution")
    ap.add_argument("--k", type=int, nargs="+", default=[10])
    ap.add_argument("--eps", type=float, nargs="+", default=[0.1])
    ap.add_argument("--steps", type=int, nargs="+", default=None)
    ap.add_argument("--recommended", action="store_true", help="use N_rec and 2 N_rec from recommended_steps")
    ap.add_argument("--N", type=int, default=500, help="sample points per sphere")
    ap.add_argument("--device", default="cpu")
    a = ap.parse_args()
    module = load_module(os.path.abspath(a.solution))
    for k in a.k:
        for e in a.eps:
            steps = a.steps
            if a.recommended or not steps:
                n_rec = module.recommended_steps(k, e)
                steps = [n_rec, 2 * n_rec]
            check(module, k, e, steps, a.N, a.device)
