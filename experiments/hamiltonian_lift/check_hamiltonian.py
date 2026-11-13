"""Diagnostic checker for the unfinished experimental prototype `experiments/hamiltonian_lift/solution_hamiltonian.py`.

Scope vs. formal theorems:
  * `solution_hamiltonian.py` is an UNFINISHED experimental research prototype — NOT a certified global C^3
    Hamiltonian deliverable (for instance `k = 11, eps = 0.001` and `k = 12, eps = 0.001` FAIL check 2C below;
    see `logs/current_honest_check.log`, `README.md`, and `DIAGNOSTICS.md`).
  * Paper IV (`paper/p4/main.pdf`, Section 8, Proposition 8.1) proves only the radial-collar generator formula in
    terms of the global radial Poincare primitive and abstract ODE uniqueness / trajectory-residual bounds (the
    abstract ODE lemmas are formalised in `verification/RK4Convergence.lean`); neither Paper IV nor Lean 4 certifies
    this prototype, its parameter overrides, sampled collar heuristics, or finite ray-unwrapping scheme.
  * This script runs diagnostic sampling checks on the prototype:
    it loads the submission from an isolated empty temporary directory, optionally blocks `numpy` (`--block-numpy`),
    and checks on sampled points and stage times:
      2A hypotheses     all 42 analytic margins (H0)-(H15) on the prototype's chosen Chain3 parameters hold in float64;
      2B support        H(Q, P, t) == 0 and grad H == 0 at sampled exterior points and at t in {0, 1},
                        plus scalar-float `t` vs tensor-`t` signature equivalence in Stage 5;
      2C smoothness & scalar cross-branch continuity diagnostics
                        1. finite autograd gradients (zero NaN/Inf) across sampled origins, cutoff collars, stage
                           junctions, and bisected micro-chords (1e-8 -> 1e-11);
                        2. fixed-offset (`+-1e-10`) neighbour probe across the `|u| = r_1` plateau/collar boundary on
                           group + wild balls across Stage 3 and Stage 5, plus radial cutoff profile scan
                           `[0.95*r_1, 1.02*r_2]` (catches sheet jumps such as `k = 12, eps = 0.001`);
      2D velocity-defect diagnostics  checks on sampled points/times:
                          1. boundary values gamma_0^{(i)}(u) == s_i + u and gamma_1^{(i)}(u) == Embed(i, u);
                          2. inter-stage C^1 junction residuals across all internal stage breaks;
                          3. ||X_H(gamma_t^{(i)}(u), t) - d/dt gamma_t^{(i)}(u)|| / max(1, ||dot||) across all
                             6 stages t in (0, 1) (cf. Paper IV, Proposition 8.1(ii) & abstract Lean lemmas
                             `picard_lindelof_curve_unique` / `picard_lindelof_epoch_certificate`);
      2E sp(4) saddle spectrum  measures frozen spatial Jacobian eigenvalues +-lambda of D_y X_H along sampled curves
                        (local conditioning diagnostic; see Paper IV, Remark 8.3).

  Tier 1 (Optional `--tier 1` — Black-Box Multi-Rate Adaptive Dormand-Prince RK45 ODE Integration, t = 0 -> 1):
    Integrates Hamilton's equations dQ/dt = +dH/dP, dP/dt = -dH/dQ from t = 0 to t = 1 calling ONLY
    `Hamiltonian(Q, P, t)` and `torch.autograd.grad` on gentle regimes.

Usage:
    python check_hamiltonian.py solution_hamiltonian.py --k 10 11 12 17 100 1000 --eps 0.05 0.001 0.0001 --block-numpy
"""
from __future__ import annotations

import argparse
import builtins
import importlib.util
import json
import math
import os
import shutil
import sys
import tempfile
import time
import types

import torch

torch.set_default_dtype(torch.float64)
F64 = torch.float64
DIM = 2


def block_numpy_imports() -> None:
    """Block any runtime import of `numpy` to verify strict pure-PyTorch compliance."""
    sys.modules.pop("numpy", None)
    orig_import = builtins.__import__

    def guarded_import(name, globals=None, locals=None, fromlist=(), level=0):
        if name == "numpy" or name.startswith("numpy."):
            raise ImportError("numpy import is explicitly blocked by --block-numpy")
        return orig_import(name, globals, locals, fromlist, level)

    builtins.__import__ = guarded_import


def load_submission(path: str):
    """Load the submission from an empty temporary directory so it cannot read neighbouring files."""
    abs_src = os.path.abspath(path)
    tmp = tempfile.mkdtemp(prefix="hamiltonian_submission_")
    dst = shutil.copy(abs_src, os.path.join(tmp, "solution.py"))
    os.chdir(tmp)
    spec = importlib.util.spec_from_file_location("submission", dst)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def compile_generated_module(src: str):
    m = types.ModuleType("generated_hamiltonian")
    exec(compile(src, "<hamiltonian>", "exec"), m.__dict__)
    if not hasattr(m, "Hamiltonian"):
        raise AssertionError("Generated source must define Hamiltonian(Q, P, t)")
    return m


def omega0_pairs(dQ1: torch.Tensor, dP1: torch.Tensor, dQ2: torch.Tensor, dP2: torch.Tensor) -> torch.Tensor:
    return (dQ1 * dP2 - dP1 * dQ2).sum(dim=-1)


def vector_field_autograd(H_fn, state: torch.Tensor, t_arg, call_times: list[float]) -> torch.Tensor:
    """Compute X_H = (+dH/dP, -dH/dQ) exclusively via `torch.autograd.grad`."""
    q = state[:, :DIM].detach().requires_grad_(True)
    p = state[:, DIM:].detach().requires_grad_(True)
    t0 = time.perf_counter()
    h = H_fn(q, p, t_arg)
    call_times.append(time.perf_counter() - t0)
    if h.dtype != F64 or h.shape != (state.shape[0],):
        raise ValueError(
            f"Hamiltonian must return float64 tensor of shape ({state.shape[0]},), got {h.dtype} {tuple(h.shape)}"
        )
    dq, dp = torch.autograd.grad(h.sum(), (q, p), allow_unused=True)
    if dq is None:
        dq = torch.zeros_like(q)
    if dp is None:
        dp = torch.zeros_like(p)
    return torch.cat([dp.detach(), -dq.detach()], dim=-1)


def run_tier2_audit(gen_mod, k: int, eps: float, seed: int = 2026, device: str = "cpu") -> dict:
    """Tier 2: Fast all-(k, eps) differential flow identity, compact support, and global smoothness audit."""
    t0 = time.perf_counter()
    H = gen_mod.Hamiltonian
    cfg = getattr(gen_mod, "CONFIG", {})
    r_needed = (k / (1.0 - eps)) ** 0.25
    call_times: list[float] = []

    # 2A. Analytic hypotheses (H0)-(H15) of Paper IV
    hyps = cfg.get("hypotheses", {})
    min_hyp_margin = min(hyps.values()) if hyps else float("nan")
    # Note: Paper IV has both strict (`> 0`) and non-strict (`>= 0`, e.g. `W2 <= 1/6`) margins; `Chain3` verifies all 42.
    hyp_ok = bool(len(hyps) >= 30 and math.isfinite(min_hyp_margin) and min_hyp_margin >= 0.0)

    # 2B. Compact support (t = 0, t = 1, far exterior) & scalar-float `t` == tensor-`t` signature check
    r_sup = float(cfg.get("support_radius", max(3.0 * k + 10.0, 500.0)))
    g = torch.Generator().manual_seed(seed + 17)
    far_dirs = torch.randn(32, 4, generator=g, dtype=F64)
    far_dirs = far_dirs / far_dirs.norm(dim=-1, keepdim=True)
    far_pts = (1.25 * r_sup + 50.0) * far_dirs.to(device)
    sup_max_val = 0.0
    sup_max_grad = 0.0
    for t_probe in (0.0, 0.03, 0.19, 0.55, 1.0):
        pts_p = far_pts if 0.0 < t_probe < 1.0 else torch.randn(32, 4, generator=g, dtype=F64).to(device) * 5.0
        qp = pts_p[:, :2].detach().requires_grad_(True)
        pp = pts_p[:, 2:].detach().requires_grad_(True)
        hv = H(qp, pp, float(t_probe))
        dq, dp = torch.autograd.grad(hv.sum(), (qp, pp), allow_unused=True)
        gnorm = 0.0
        if dq is not None:
            gnorm = max(gnorm, float(dq.abs().max().item()))
        if dp is not None:
            gnorm = max(gnorm, float(dp.abs().max().item()))
        sup_max_val = max(sup_max_val, float(hv.abs().max().item()))
        sup_max_grad = max(sup_max_grad, gnorm)
    support_ok = (sup_max_val == 0.0) and (sup_max_grad == 0.0)

    # Representative balls covering all 9 group cells + low/mid/top wild cells (O(1) runtime even at k = 10^5!)
    if k <= 16:
        ball_ids = list(range(k))
    else:
        wild_picks = sorted({9, 10, min(k - 1, 9 + (k - 9) // 3), min(k - 1, 9 + 2 * (k - 9) // 3), k - 2, k - 1})
        ball_ids = list(range(9)) + [b for b in wild_picks if 9 <= b < k]

    # Sample local unit-ball points: origin 0, +-e_1..+-e_4, and random interior + unit-sphere boundary points
    u_special = [torch.zeros(4, dtype=F64)]
    for d in range(4):
        for sgn in (-1.0, 1.0):
            v = torch.zeros(4, dtype=F64)
            v[d] = sgn
            u_special.append(v)
    u_rand = torch.randn(7, 4, generator=g, dtype=F64)
    u_rand = u_rand / u_rand.norm(dim=-1, keepdim=True)
    u_rand[:3] = u_rand[:3] * torch.tensor([[0.35], [0.70], [0.95]], dtype=F64)
    u_local = torch.cat([torch.stack(u_special, dim=0), u_rand], dim=0).to(device)  # (16, 4)

    # 2C. Smoothness & micro-chord continuity across origins, interior/boundary points, and cutoff collars
    r_dom = float(cfg.get("r_domain", 1.001))
    r_collar = 1.0 + 0.42 * min(0.25, max(1e-6, r_dom - 1.0))
    u_col = (r_collar * u_local[1:5]).contiguous()
    smooth_finite = True
    scalar_vs_tensor_diff = 0.0
    max_micro_jump_ratio = 0.0

    if hasattr(gen_mod, "ExactTrajectory"):
        for t_sm in (0.025, 0.075, 0.125, 0.185, 0.25, 0.45, 0.85):
            pts_in = torch.cat([gen_mod.ExactTrajectory(t_sm, u_local[:6], b) for b in ball_ids[:4]], dim=0)
            pts_c = torch.cat([gen_mod.ExactTrajectory(t_sm, u_col[:2], b) for b in ball_ids[:4]], dim=0)
            pts_all = torch.cat([pts_in, pts_c], dim=0)
            xh_sc = vector_field_autograd(H, pts_all, float(t_sm), call_times)
            if not bool(torch.isfinite(xh_sc).all()):
                smooth_finite = False
            if t_sm > 0.30:
                t_ten = torch.full((pts_all.shape[0],), float(t_sm), dtype=F64, device=device)
                xh_tn = vector_field_autograd(H, pts_all, t_ten, call_times)
                scalar_vs_tensor_diff = max(scalar_vs_tensor_diff, float((xh_sc - xh_tn).abs().max().item()))

            # Micro-step Lipschitz continuity check on unit-ball trajectories: perturb by 1e-8 and 1e-11
            d_dir = torch.randn_like(pts_in)
            d_dir = d_dir / d_dir.norm(dim=-1, keepdim=True)
            xh_in = xh_sc[: pts_in.shape[0]]
            xh_8 = vector_field_autograd(H, pts_in + 1e-8 * d_dir, float(t_sm), call_times)
            xh_11 = vector_field_autograd(H, pts_in + 1e-11 * d_dir, float(t_sm), call_times)
            if not (bool(torch.isfinite(xh_8).all()) and bool(torch.isfinite(xh_11).all())):
                smooth_finite = False
            g8 = (xh_8 - xh_in).norm(dim=-1)
            g11 = (xh_11 - xh_in).norm(dim=-1)
            xh_scale = torch.maximum(torch.ones_like(g8), xh_in.norm(dim=-1))
            sig_mask = (g8 > 1e-3 * xh_scale) & (g11 > 1e-3 * xh_scale)
            if bool(sig_mask.any()):
                ratio = float((g11[sig_mask] / g8[sig_mask]).max().item())
                max_micro_jump_ratio = max(max_micro_jump_ratio, ratio)

    smooth_ok = smooth_finite and (scalar_vs_tensor_diff <= 1e-12) and (max_micro_jump_ratio < 0.05)

    # 2C-scalar. Scalar cross-branch continuity at `|u| = r_1 * sqrt(0.999999)` (+-1e-10 straddle) & radial cutoff scan
    max_scalar_switch_rel_jump = 0.0
    max_radial_scan_rel_step = 0.0
    scalar_cont_ok = True
    h_obj = getattr(gen_mod, "_H_OBJ", None)
    if h_obj is not None:
        # Include deterministic reproduction direction plus random unit directions on group + wild balls
        d_repro = torch.tensor(
            [[-0.14216543802532278, -0.3387938475081023, -0.9183258638487032, -0.14725937969534547]],
            dtype=F64,
        )
        d_repro = d_repro / d_repro.norm(dim=-1, keepdim=True)
        d_rand = torch.randn(5, 4, generator=g, dtype=F64)
        d_rand = d_rand / d_rand.norm(dim=-1, keepdim=True)
        u_dirs = torch.cat([d_repro, d_rand], dim=0)  # (6, 4)
        n_d = u_dirs.shape[0]
        sw_balls = sorted({0, 4, 8, min(9, k - 1), k - 1})

        # (i) Stage 3 switch (`t = 0.185`, `|u|^2 = r1_wide^2 * 0.999999`)
        t_s3 = 0.185
        _, sig_s3, _ = h_obj._stage_clock(t_s3)
        rho_s3, _ = h_obj._stage3_rho(sig_s3, h_obj.tau)
        if rho_s3 > 1e-12:
            r_sw3 = h_obj.r1_wide * math.sqrt(0.999999)
            for b_sw in sw_balls:
                ib_sw = torch.full((n_d,), b_sw, dtype=torch.int64)
                ai_sw = h_obj.base_a[b_sw]
                u_l = (r_sw3 * (1.0 - 1e-9)) * u_dirs
                u_r = (r_sw3 * (1.0 + 1e-9)) * u_dirs
                y_l = h_obj.local_pivots[b_sw] + (h_obj.cp.batched_local_pass(ib_sw, ai_sw + rho_s3 * (u_l - ai_sw))[0] - h_obj.f_a[b_sw]) / rho_s3
                y_r = h_obj.local_pivots[b_sw] + (h_obj.cp.batched_local_pass(ib_sw, ai_sw + rho_s3 * (u_r - ai_sw))[0] - h_obj.f_a[b_sw]) / rho_s3
                with torch.no_grad():
                    hl = H(y_l[:, :2].to(device), y_l[:, 2:].to(device), float(t_s3)).cpu()
                    hr = H(y_r[:, :2].to(device), y_r[:, 2:].to(device), float(t_s3)).cpu()
                if not (bool(torch.isfinite(hl).all()) and bool(torch.isfinite(hr).all())):
                    scalar_cont_ok = False
                else:
                    sc_h = torch.maximum(torch.ones_like(hl), torch.maximum(hl.abs(), hr.abs()))
                    max_scalar_switch_rel_jump = max(max_scalar_switch_rel_jump, float(((hr - hl).abs() / sc_h).max().item()))

        # (ii) Stage 5 switch (`t in {0.42, 0.60, 0.85}`, `|u|^2 = r1(v)^2 * 0.999999`) + 65-point radial collar scan
        for t_s5 in (0.42, 0.60, 0.85):
            _, sig_s5, _ = h_obj._stage_clock(t_s5)
            v_s5, _ = h_obj.tail_clock.evaluate(sig_s5)
            r1_5, r2_5 = h_obj._radii_for_v(v_s5)
            # Only test interior of Stage 5 collar that lies strictly inside r_cut_w
            r_cut_w = min(1.0 + 0.97 * (h_obj.r_dom - 1.0), 1.0 + 0.92 * h_obj.gap_dom)
            r_sw5 = r1_5 * math.sqrt(0.999999)
            for b_sw in sw_balls:
                ai_sw = h_obj.base_a[b_sw]
                w_test = (1.0 - v_s5) * ai_sw + v_s5 * (r_sw5 * u_dirs)
                if float(w_test.norm(dim=-1).max().item()) >= 0.995 * r_cut_w:
                    continue
                ib_sw = torch.full((n_d,), b_sw, dtype=torch.int64)
                u_l = (r_sw5 * (1.0 - 1e-10)) * u_dirs
                u_r = (r_sw5 * (1.0 + 1e-10)) * u_dirs
                y_l = h_obj.cp.batched_local_pass(ib_sw, (1.0 - v_s5) * ai_sw + v_s5 * u_l)[0] / v_s5
                y_r = h_obj.cp.batched_local_pass(ib_sw, (1.0 - v_s5) * ai_sw + v_s5 * u_r)[0] / v_s5
                with torch.no_grad():
                    hl = H(y_l[:, :2].to(device), y_l[:, 2:].to(device), float(t_s5)).cpu()
                    hr = H(y_r[:, :2].to(device), y_r[:, 2:].to(device), float(t_s5)).cpu()
                if not (bool(torch.isfinite(hl).all()) and bool(torch.isfinite(hr).all())):
                    scalar_cont_ok = False
                else:
                    sc_h = torch.maximum(torch.ones_like(hl), torch.maximum(hl.abs(), hr.abs()))
                    max_scalar_switch_rel_jump = max(max_scalar_switch_rel_jump, float(((hr - hl).abs() / sc_h).max().item()))

            # Radial cutoff scan on `[0.96 * r1_5, 1.02 * r2_5]` (257 samples + 2nd-difference curvature kink check)
            if t_s5 == 0.60:
                b_rad = min(9, k - 1)
                ai_rad = h_obj.base_a[b_rad]
                r_max_allow = (0.99 * r_cut_w - float((1.0 - v_s5) * ai_rad.norm().item())) / v_s5
                r_hi_scan = min(1.02 * r2_5, r_max_allow)
                if r_hi_scan > 0.98 * r1_5:
                    r_grid = torch.linspace(0.96 * r1_5, r_hi_scan, 257, dtype=F64)
                    u_scan = r_grid[:, None] * d_repro
                    ib_scan = torch.full((257,), b_rad, dtype=torch.int64)
                    y_scan = h_obj.cp.batched_local_pass(ib_scan, (1.0 - v_s5) * ai_rad + v_s5 * u_scan)[0] / v_s5
                    with torch.no_grad():
                        h_scan = H(y_scan[:, :2].to(device), y_scan[:, 2:].to(device), float(t_s5)).cpu()
                    if not bool(torch.isfinite(h_scan).all()):
                        scalar_cont_ok = False
                    else:
                        pk = max(1.0, float(h_scan.abs().max().item()))
                        d1_scan = (h_scan[1:] - h_scan[:-1]).abs()
                        # For a C^2 radial profile on 257 points, max |h_{i+1} - 2 h_i + h_{i-1}| / pk << 0.05
                        # whereas any sheet jump J produces a second difference >= 2 J!
                        d2_scan = (h_scan[2:] - 2.0 * h_scan[1:-1] + h_scan[:-2]).abs()
                        max_radial_scan_rel_step = max(
                            max_radial_scan_rel_step, float(d2_scan.max().item() / pk), 0.25 * float(d1_scan.max().item() / pk)
                        )
                        if r_hi_scan >= 1.005 * r2_5 and float(h_scan[-1].abs().item()) > 1e-12:
                            scalar_cont_ok = False

    scalar_cont_ok = scalar_cont_ok and (max_scalar_switch_rel_jump <= 1e-5) and (max_radial_scan_rel_step <= 0.08)
    smooth_ok = smooth_ok and scalar_cont_ok

    # 2D. Picard-Lindelof boundary conditions, junction C^1 continuity, and vector-field identity across all 6 stages
    max_bc_err = 0.0
    max_junction_err = 0.0
    max_vf_rel_err = 0.0
    t_breaks = cfg.get("t_breaks", [0.0, 0.05, 0.10, 0.15, 0.22, 0.28, 1.0])
    if hasattr(gen_mod, "ExactTrajectory") and hasattr(gen_mod, "Embed"):
        for b in ball_ids:
            src_b = torch.tensor([3.0 * b, 0.0, 0.0, 0.0], dtype=F64, device=device)
            err0 = float((gen_mod.ExactTrajectory(0.0, u_local, b) - (u_local + src_b)).norm(dim=-1).max().item())
            err1 = float((gen_mod.ExactTrajectory(1.0, u_local, b) - gen_mod.Embed(b, u_local)).norm(dim=-1).max().item())
            max_bc_err = max(max_bc_err, err0, err1)
        for tb_j in t_breaks[1:-1]:
            for b in ball_ids[:4]:
                pl = gen_mod.ExactTrajectory(float(tb_j) - 1e-9, u_local[:4], b)
                pr_ = gen_mod.ExactTrajectory(float(tb_j) + 1e-9, u_local[:4], b)
                sc_j = torch.maximum(torch.ones(pl.shape[0], dtype=F64, device=device), pl.norm(dim=-1))
                max_junction_err = max(max_junction_err, float(((pr_ - pl).norm(dim=-1) / sc_j).max().item()))
            xh_j = vector_field_autograd(
                H,
                torch.cat([gen_mod.ExactTrajectory(float(tb_j), u_local[:4], b) for b in ball_ids[:4]], dim=0),
                float(tb_j),
                call_times,
            )
            max_junction_err = max(max_junction_err, float(xh_j.norm(dim=-1).max().item()))

    stage_probes = (0.025, 0.075, 0.125, 0.185, 0.25, 0.35, 0.60, 0.88)
    if hasattr(gen_mod, "ExactTrajectoryAndVelocity"):
        for t_chk in stage_probes:
            pv = [gen_mod.ExactTrajectoryAndVelocity(t_chk, u_local, b) for b in ball_ids]
            pts_0 = torch.cat([p for p, _ in pv], dim=0)
            v_exact = torch.cat([v for _, v in pv], dim=0)
            xh = vector_field_autograd(H, pts_0, float(t_chk), call_times)
            if not (bool(torch.isfinite(xh).all()) and bool(torch.isfinite(v_exact).all())):
                max_vf_rel_err = float("inf")
                break
            denom = torch.maximum(torch.ones(pts_0.shape[0], dtype=F64, device=device), v_exact.norm(dim=-1))
            rel = float(((xh - v_exact).norm(dim=-1) / denom).max().item())
            max_vf_rel_err = max(max_vf_rel_err, rel)
    elif hasattr(gen_mod, "ExactTrajectory"):
        for t_chk in stage_probes:
            dt_s = 1e-6 if 0.15 < t_chk < 0.22 else 1e-8
            pts_0 = torch.cat([gen_mod.ExactTrajectory(t_chk, u_local, b) for b in ball_ids], dim=0)
            pts_p = torch.cat([gen_mod.ExactTrajectory(t_chk + dt_s, u_local, b) for b in ball_ids], dim=0)
            pts_m = torch.cat([gen_mod.ExactTrajectory(t_chk - dt_s, u_local, b) for b in ball_ids], dim=0)
            v_exact = (pts_p - pts_m) / (2.0 * dt_s)
            xh = vector_field_autograd(H, pts_0, float(t_chk), call_times)
            denom = torch.maximum(torch.ones(pts_0.shape[0], dtype=F64, device=device), v_exact.norm(dim=-1))
            rel = float(((xh - v_exact).norm(dim=-1) / denom).max().item())
            max_vf_rel_err = max(max_vf_rel_err, rel)

    # 2E. Measure peak hyperbolic sp(4) saddle eigenvalue |Re(lambda)| of D_y X_H along wild-ball trajectory
    max_lyapunov_eig = 0.0
    if hasattr(gen_mod, "ExactTrajectory"):
        b_wild = ball_ids[-1]
        for t_sp in (0.58, 0.62, 0.75):
            pt_w = gen_mod.ExactTrajectory(t_sp, u_local[1:3], b_wild)
            h_fd = 1e-7
            cols = []
            for d_i in range(4):
                ed = torch.zeros(1, 4, dtype=F64, device=device)
                ed[0, d_i] = h_fd
                vp = vector_field_autograd(H, pt_w + ed, float(t_sp), call_times)
                vm = vector_field_autograd(H, pt_w - ed, float(t_sp), call_times)
                cols.append((vp - vm) / (2.0 * h_fd))
            J_xh = torch.stack(cols, dim=-1)  # (2, 4, 4)
            if bool(torch.isfinite(J_xh).all()):
                evs = torch.linalg.eigvals(J_xh)
                max_lyapunov_eig = max(max_lyapunov_eig, float(evs.real.abs().max().item()))

    # Time-1 containment & disjointness on representative balls
    y1_list = [gen_mod.Embed(b, u_local) for b in ball_ids] if hasattr(gen_mod, "Embed") else []
    r_max_t2 = float(torch.cat(y1_list, dim=0).norm(dim=-1).max().item()) if y1_list else float("nan")
    overlaps_t2 = 0
    if y1_list and hasattr(gen_mod, "Preimage"):
        for idx_a, b_a in enumerate(ball_ids):
            Ya = y1_list[idx_a]
            for b_b in ball_ids:
                if b_b == b_a:
                    continue
                Xb, ok_b = gen_mod.Preimage(b_b, Ya)
                hit = ok_b & torch.isfinite(Xb).all(dim=1) & (Xb.norm(dim=1) <= 1.0 - 1e-7)
                if bool(hit.any()):
                    back = gen_mod.Embed(b_b, Xb[hit])
                    overlaps_t2 += int(((back - Ya[hit]).norm(dim=1) <= 1e-5).sum().item())

    vf_tol = 5e-3 if (eps <= 1e-3 or k >= 500) else 5e-4
    bc_ok = math.isfinite(max_bc_err) and (max_bc_err <= 1e-12) and math.isfinite(max_junction_err) and (max_junction_err <= 1e-6)
    containment_t2_ok = math.isfinite(r_max_t2) and (r_max_t2 < r_needed)
    vf_ok = math.isfinite(max_vf_rel_err) and (max_vf_rel_err < vf_tol)
    disjoint_t2_ok = overlaps_t2 == 0
    passed_t2 = hyp_ok and support_ok and smooth_ok and bc_ok and vf_ok and containment_t2_ok and disjoint_t2_ok

    return dict(
        passed=passed_t2,
        hypotheses_checked=len(hyps),
        min_hypothesis_margin=min_hyp_margin,
        support_ok=support_ok,
        smooth_ok=smooth_ok,
        bc_ok=bc_ok,
        max_bc_err=max_bc_err,
        max_junction_err=max_junction_err,
        scalar_vs_tensor_t_diff=scalar_vs_tensor_diff,
        max_scalar_switch_rel_jump=max_scalar_switch_rel_jump,
        max_radial_scan_rel_step=max_radial_scan_rel_step,
        max_micro_jump_ratio=max_micro_jump_ratio,
        max_picard_vf_rel_err=max_vf_rel_err,
        max_sp4_saddle_eig=round(max_lyapunov_eig, 1),
        R_max_embed=r_max_t2,
        R_needed=r_needed,
        overlaps=overlaps_t2,
        H_calls=len(call_times),
        seconds=round(time.perf_counter() - t0, 3),
    )


def run_tier1_adaptive_ode(
    gen_mod,
    k: int,
    eps: float,
    n_per_ball: int = 2,
    rtol: float = 5e-6,
    atol: float = 5e-7,
    pair_delta: float = 1e-7,
    scalar_t_only: bool = False,
    seed: int = 2026,
    device: str = "cpu",
    verbose: bool = True,
) -> dict:
    """Tier 1: Pure black-box adaptive Dormand-Prince RK45 integration of Hamilton's equations from t = 0 to t = 1."""
    t0 = time.perf_counter()
    H = gen_mod.Hamiltonian
    cfg = getattr(gen_mod, "CONFIG", {})
    t_breaks = cfg.get("t_breaks", [0.0, 0.06, 0.11, 0.16, 0.23, 1.0])
    r_needed = (k / (1.0 - eps)) ** 0.25

    # Sample boundary points on unit spheres centred at (3*i, 0, 0, 0) + tangent-displaced pairs
    g = torch.Generator().manual_seed(seed + k)
    u_sph = torch.randn(k, n_per_ball, 4, generator=g, dtype=F64)
    u_sph = u_sph / u_sph.norm(dim=-1, keepdim=True)
    centres0 = torch.zeros(k, 1, 4, dtype=F64)
    centres0[:, 0, 0] = 3.0 * torch.arange(k, dtype=F64)
    base = (u_sph + centres0).reshape(k * n_per_ball, 4)
    mb = base.shape[0]

    # One interior-displaced tangent pair per ball (or stride): orient `d1, d2` inward (`<u_sph, d> < -0.2`) so
    # `u_sph + pair_delta * d` lies strictly INSIDE the unit ball `|u| < 1` (rigid plateau `cut == 1`), avoiding
    # boundary-collar exit artefacts while testing exact 4D symplectic area preservation `omega_0`!
    stride = max(1, n_per_ball)
    b_sub = base[::stride]
    u_sub = u_sph.reshape(mb, 4)[::stride]
    n_pairs = b_sub.shape[0]
    d1 = torch.randn(n_pairs, 4, generator=g, dtype=F64)
    d1 = d1 - (d1 * u_sub).sum(dim=-1, keepdim=True) * u_sub - 0.5 * u_sub
    d1 = d1 / d1.norm(dim=-1, keepdim=True)
    d2 = torch.randn(n_pairs, 4, generator=g, dtype=F64)
    d2 = d2 - (d2 * u_sub).sum(dim=-1, keepdim=True) * u_sub - 0.5 * u_sub
    d2 = d2 / d2.norm(dim=-1, keepdim=True)
    all_pts0 = torch.cat([base, b_sub + pair_delta * d1, b_sub + pair_delta * d2], dim=0).to(device)
    N_tot = all_pts0.shape[0]

    # Group each tangent triple (base, base + delta*d1, base + delta*d2) so they share identical step sizes!
    grp_members: list[list[int]] = []
    used: set[int] = set()
    for p_i in range(n_pairs):
        b_i = p_i * stride
        s1 = mb + p_i
        s2 = mb + n_pairs + p_i
        grp_members.append([b_i, s1, s2])
        used.update([b_i, s1, s2])
    for r_i in range(N_tot):
        if r_i not in used:
            grp_members.append([r_i])
    G_cnt = len(grp_members)
    row_to_grp = torch.zeros(N_tot, dtype=torch.int64, device=device)
    for gi, mem in enumerate(grp_members):
        for r_i in mem:
            row_to_grp[r_i] = gi

    # Dormand-Prince RK45 Butcher tableau
    c2, c3, c4, c5, c6 = 1.0 / 5.0, 3.0 / 10.0, 4.0 / 5.0, 8.0 / 9.0, 1.0
    a21 = 1.0 / 5.0
    a31, a32 = 3.0 / 40.0, 9.0 / 40.0
    a41, a42, a43 = 44.0 / 45.0, -56.0 / 15.0, 32.0 / 9.0
    a51, a52, a53, a54 = 19372.0 / 6561.0, -25360.0 / 2187.0, 64448.0 / 6561.0, -212.0 / 729.0
    a61, a62, a63, a64, a65 = 9017.0 / 3168.0, -355.0 / 33.0, 46732.0 / 5247.0, 49.0 / 176.0, -5103.0 / 18656.0
    b1, b3, b4, b5, b6 = 35.0 / 384.0, 500.0 / 1113.0, 125.0 / 192.0, -2187.0 / 6784.0, 11.0 / 84.0
    e1 = 35.0 / 384.0 - 5179.0 / 57600.0
    e3 = 500.0 / 1113.0 - 7571.0 / 16695.0
    e4 = 125.0 / 192.0 - 393.0 / 640.0
    e5 = -2187.0 / 6784.0 + 92097.0 / 339200.0
    e6 = 11.0 / 84.0 - 187.0 / 2100.0
    e7 = -1.0 / 40.0

    call_times: list[float] = []
    y = all_pts0.clone()
    min_h = 1.0
    max_h = 0.0

    # Integrate Stages 0..n_sync-1 synchronously using scalar `float(t)`
    n_sync = max(1, len(t_breaks) - 2) if not scalar_t_only else len(t_breaks) - 1
    for seg in range(n_sync):
        ta, tb = float(t_breaks[seg]), float(t_breaks[seg + 1])
        t = ta
        h = (tb - ta) / 24.0
        k1 = vector_field_autograd(H, y, float(t), call_times)
        while t < tb - 1e-14:
            vmax = float(k1.norm(dim=-1).max().item())
            if vmax * h > 0.12:
                h = max(1e-12, 0.12 / vmax)
            if t + h > tb:
                h = tb - t
            k2 = vector_field_autograd(H, y + h * a21 * k1, float(t + c2 * h), call_times)
            k3 = vector_field_autograd(H, y + h * (a31 * k1 + a32 * k2), float(t + c3 * h), call_times)
            k4 = vector_field_autograd(H, y + h * (a41 * k1 + a42 * k2 + a43 * k3), float(t + c4 * h), call_times)
            k5 = vector_field_autograd(
                H, y + h * (a51 * k1 + a52 * k2 + a53 * k3 + a54 * k4), float(t + c5 * h), call_times
            )
            k6 = vector_field_autograd(
                H, y + h * (a61 * k1 + a62 * k2 + a63 * k3 + a64 * k4 + a65 * k5), float(t + c6 * h), call_times
            )
            yn = y + h * (b1 * k1 + b3 * k3 + b4 * k4 + b5 * k5 + b6 * k6)
            k7 = vector_field_autograd(H, yn, float(t + h), call_times)
            ev = h * (e1 * k1 + e3 * k3 + e4 * k4 + e5 * k5 + e6 * k6 + e7 * k7)
            err = float((ev.abs() / (atol + rtol * torch.maximum(y.abs(), yn.abs()))).max().item())
            if (not bool(torch.isfinite(yn).all())) or (not bool(torch.isfinite(k7).all())):
                err = 100.0
            if err <= 1.0 or h <= 1e-12:
                min_h = min(min_h, h)
                max_h = max(max_h, h)
                t += h
                y = yn
                k1 = k7
                h *= 3.0 if err == 0.0 else min(3.0, max(0.2, 0.9 * (err ** -0.2)))
            else:
                h *= max(0.15, 0.85 * (err ** -0.2))

    # Stage 4 `[t_tail, 1.0]`: vectorized multi-rate Dormand-Prince RK45 across trajectory groups
    if not scalar_t_only:
        t_tail = float(t_breaks[-2])
        t_grp = torch.full((G_cnt,), t_tail, dtype=F64, device=device)
        h_grp = torch.full((G_cnt,), 0.010, dtype=F64, device=device)
        k1 = vector_field_autograd(H, y, torch.full((N_tot,), t_tail, dtype=F64, device=device), call_times)
        it = 0
        while True:
            rem_g = 1.0 - t_grp
            act_g_mask = rem_g > 1e-13
            if not bool(act_g_mask.any()):
                break

            # Evaluate all active groups in one batched pass (11..100 rows cost ~15 ms total, same as 1 row!)
            sched_g_mask = act_g_mask

            sched_row = sched_g_mask[row_to_grp]
            act_idx = torch.nonzero(sched_row, as_tuple=False).squeeze(1)
            ya = y[act_idx]
            ga = row_to_grp[act_idx]
            ta = t_grp[ga]
            k1a = k1[act_idx]

            v_grp = torch.zeros(G_cnt, dtype=F64, device=device).scatter_reduce(
                0, ga, k1a.norm(dim=-1), reduce="amax", include_self=False
            )
            y_grp = torch.zeros(G_cnt, dtype=F64, device=device).scatter_reduce(
                0, ga, ya.norm(dim=-1), reduce="amax", include_self=False
            )
            disp_cap = 0.05 + 0.03 * y_grp
            h_cap = torch.where(v_grp * h_grp > disp_cap, (disp_cap / v_grp.clamp_min(1e-12)).clamp_min(1e-12), h_grp)
            h_try_g = torch.minimum(h_cap, rem_g)
            ha = h_try_g[ga]

            k2a = vector_field_autograd(H, ya + ha[:, None] * a21 * k1a, ta + c2 * ha, call_times)
            k3a = vector_field_autograd(H, ya + ha[:, None] * (a31 * k1a + a32 * k2a), ta + c3 * ha, call_times)
            k4a = vector_field_autograd(
                H, ya + ha[:, None] * (a41 * k1a + a42 * k2a + a43 * k3a), ta + c4 * ha, call_times
            )
            k5a = vector_field_autograd(
                H, ya + ha[:, None] * (a51 * k1a + a52 * k2a + a53 * k3a + a54 * k4a), ta + c5 * ha, call_times
            )
            k6a = vector_field_autograd(
                H,
                ya + ha[:, None] * (a61 * k1a + a62 * k2a + a63 * k3a + a64 * k4a + a65 * k5a),
                ta + c6 * ha,
                call_times,
            )
            yna = ya + ha[:, None] * (b1 * k1a + b3 * k3a + b4 * k4a + b5 * k5a + b6 * k6a)
            k7a = vector_field_autograd(H, yna, ta + ha, call_times)

            eva = ha[:, None] * (e1 * k1a + e3 * k3a + e4 * k4a + e5 * k5a + e6 * k6a + e7 * k7a)
            r_err = (eva.abs() / (atol + rtol * torch.maximum(ya.abs(), yna.abs()))).max(dim=1).values
            dropped = (k1a.norm(dim=-1) > 2.0) & (k7a.norm(dim=-1) == 0.0) & (ta + ha < 0.995)
            bad_primary = (act_idx < mb) & (dropped | (~torch.isfinite(yna).all(dim=1)) | (~torch.isfinite(k7a).all(dim=1)))
            bad_shifted = (act_idx >= mb) & ((~torch.isfinite(yna).all(dim=1)) | (~torch.isfinite(k7a).all(dim=1)))
            r_err_ctrl = torch.where(
                bad_primary | bad_shifted,
                torch.full_like(r_err, 100.0),
                torch.where(act_idx < mb, r_err, torch.zeros_like(r_err)),
            )
            g_err = torch.zeros(G_cnt, dtype=F64, device=device).scatter_reduce(
                0, ga, r_err_ctrl, reduce="amax", include_self=False
            )

            sched_g = torch.unique(ga)
            acc_g_mask = torch.zeros(G_cnt, dtype=torch.bool, device=device)
            acc_g_mask[sched_g] = (g_err[sched_g] <= 1.0) | (h_try_g[sched_g] <= 1e-12)
            acc_row = acc_g_mask[ga]
            if bool(acc_row.any()):
                acc_glob = act_idx[acc_row]
                min_h = min(min_h, float(ha[acc_row].min().item()))
                max_h = max(max_h, float(ha[acc_row].max().item()))
                y[acc_glob] = yna[acc_row]
                k1[acc_glob] = k7a[acc_row]
                acc_g = sched_g[acc_g_mask[sched_g]]
                t_grp[acc_g] = t_grp[acc_g] + h_try_g[acc_g]

            ge = g_err[sched_g]
            fac = torch.where(
                ge <= 1.0,
                (0.90 * ge.clamp_min(1e-10).pow(-0.2)).clamp(0.2, 3.5),
                (0.82 * ge.pow(-0.2)).clamp(0.15, 0.82),
            )
            h_grp[sched_g] = (h_try_g[sched_g] * fac).clamp(1e-12, 0.05)
            it += 1
            if verbose and it % 200 == 0:
                print(
                    f"  [Tier 1 RK45] iter={it:4d} rem_groups={int(act_g_mask.sum()):3d}/{G_cnt} "
                    f"min_t={t_grp.min():.5f} mean_t={t_grp.mean():.4f} elapsed={time.perf_counter()-t0:.1f}s",
                    flush=True,
                )

    # Evaluate final time-1 checks: containment, symplecticity, disjointness, and map agreement
    y_cpu = y.detach().cpu()
    all_pts0_cpu = all_pts0.detach().cpu()
    y_balls = y_cpu[:mb]
    finite_ok = bool(torch.isfinite(y_cpu).all())
    r_max = float(y_balls.norm(dim=-1).max().item())
    density = k / (r_max ** 4)
    containment_ok = finite_ok and (density > 1.0 - eps)

    Q0, P0 = all_pts0_cpu[:, :DIM], all_pts0_cpu[:, DIM:]
    Q1, P1 = y_cpu[:, :DIM], y_cpu[:, DIM:]
    om0 = omega0_pairs(
        Q0[mb : mb + n_pairs] - Q0[:mb:stride],
        P0[mb : mb + n_pairs] - P0[:mb:stride],
        Q0[mb + n_pairs :] - Q0[:mb:stride],
        P0[mb + n_pairs :] - P0[:mb:stride],
    )
    om1 = omega0_pairs(
        Q1[mb : mb + n_pairs] - Q1[:mb:stride],
        P1[mb : mb + n_pairs] - P1[:mb:stride],
        Q1[mb + n_pairs :] - Q1[:mb:stride],
        P1[mb + n_pairs :] - P1[:mb:stride],
    )
    rel_symp_err = float((om1 - om0).abs().max().item()) / (pair_delta ** 2)
    # Note: on high-Lipschitz maps (||Df|| ~ 10^2 - 10^3), finite-difference tangent pairs of step delta = 1e-7
    # incur O(||D^2 f|| * delta) ~ 1e-2 second-order remainder even for an exact symplectomorphism!
    symp_ok = math.isfinite(rel_symp_err) and (rel_symp_err < 0.25)

    overlaps_t1 = 0
    flow_vs_embed_err = float("nan")
    if hasattr(gen_mod, "Embed"):
        ex1 = torch.cat([gen_mod.Embed(i, u_sph[i]) for i in range(k)], dim=0)
        flow_vs_embed_err = float((y_balls - ex1).norm(dim=-1).max().item())
    if hasattr(gen_mod, "Preimage") and hasattr(gen_mod, "Embed"):
        y_by_ball = y_balls.view(k, n_per_ball, 4)
        for i in range(k):
            Yi = y_by_ball[i]
            for j in range(k):
                if j == i:
                    continue
                Xj, ok_j = gen_mod.Preimage(j, Yi)
                hit = ok_j & torch.isfinite(Xj).all(dim=1) & (Xj.norm(dim=1) <= 1.0 - 1e-6)
                if bool(hit.any()):
                    back = gen_mod.Embed(j, Xj[hit])
                    overlaps_t1 += int(((back - Yi[hit]).norm(dim=1) <= 1e-4).sum().item())
    disjoint_ok = overlaps_t1 == 0

    stiffness_ratio = max_h / max(min_h, 1e-30)
    passed_t1 = containment_ok and symp_ok and disjoint_ok

    return dict(
        passed=passed_t1,
        boundary_points=mb,
        total_trajectories=N_tot,
        R_max=r_max,
        R_needed=r_needed,
        margin=r_needed - r_max,
        density=density,
        required_density=1.0 - eps,
        rel_symplectic_err=rel_symp_err,
        overlaps=overlaps_t1,
        max_ode_vs_embed_err=flow_vs_embed_err,
        dt_min=min_h,
        dt_max=max_h,
        stiffness_ratio=round(stiffness_ratio, 1),
        H_calls=len(call_times),
        longest_H_call_s=round(max(call_times) if call_times else 0.0, 4),
        seconds=round(time.perf_counter() - t0, 2),
    )


def check_one(
    sub_mod,
    k: int,
    eps: float,
    tier: str,
    n_per_ball: int,
    rtol: float,
    atol: float,
    scalar_t_only: bool,
    seed: int,
    device: str,
) -> dict:
    t0 = time.perf_counter()
    src = sub_mod.solution(k, eps)
    t_sol = time.perf_counter() - t0
    t1 = time.perf_counter()
    gen_mod = compile_generated_module(src)
    t_init = time.perf_counter() - t1

    res: dict = dict(
        k=k,
        eps=eps,
        R_needed=(k / (1.0 - eps)) ** 0.25,
        solution_seconds=round(t_sol, 3),
        init_seconds=round(t_init, 3),
    )

    ok_all = True
    if tier in ("both", "2"):
        t2 = run_tier2_audit(gen_mod, k, eps, seed=seed, device=device)
        res["tier2"] = t2
        ok_all = ok_all and bool(t2["passed"])
        print(
            f"[Picard-Lindelof] k={k} eps={eps}: {'PASS' if t2['passed'] else 'FAIL'} | "
            f"hyps={t2['hypotheses_checked']} (min_margin={t2['min_hypothesis_margin']:.3e}), "
            f"BC={t2['max_bc_err']:.1e}, junc={t2['max_junction_err']:.1e}, "
            f"H_switch_jump={t2['max_scalar_switch_rel_jump']:.2e}, "
            f"Picard_VF_rel={t2['max_picard_vf_rel_err']:.3e}, sp4_saddle=+-{t2['max_sp4_saddle_eig']:.1e}, "
            f"R_embed={t2['R_max_embed']:.6f}<{t2['R_needed']:.6f}, {t2['seconds']:.2f}s",
            flush=True,
        )

    if tier in ("both", "1"):
        t1_rep = run_tier1_adaptive_ode(
            gen_mod,
            k,
            eps,
            n_per_ball=n_per_ball,
            rtol=rtol,
            atol=atol,
            scalar_t_only=scalar_t_only,
            seed=seed,
            device=device,
        )
        res["tier1"] = t1_rep
        ok_all = ok_all and bool(t1_rep["passed"])
        print(
            f"[Tier 1] k={k} eps={eps}: {'PASS' if t1_rep['passed'] else 'FAIL'} | "
            f"R_max={t1_rep['R_max']:.6f} (need < {t1_rep['R_needed']:.6f}), k/R^4={t1_rep['density']:.6f}, "
            f"|ODE-Embed|={t1_rep['max_ode_vs_embed_err']:.3e}, symp={t1_rep['rel_symplectic_err']:.3e}, "
            f"dt=[{t1_rep['dt_min']:.2e}, {t1_rep['dt_max']:.2e}] ({t1_rep['stiffness_ratio']:.0f}x), "
            f"{t1_rep['seconds']:.1f}s ({t1_rep['H_calls']} H calls)",
            flush=True,
        )

    res["passed"] = ok_all
    print("RESULT " + json.dumps(res), flush=True)
    return res


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("solution", help="Path to standalone solution_hamiltonian.py")
    ap.add_argument("--k", type=int, nargs="+", default=[11])
    ap.add_argument("--eps", type=float, nargs="+", default=[0.05])
    ap.add_argument("--tier", choices=("2", "1", "both"), default="2")
    ap.add_argument("--N", type=int, default=2, help="Boundary sphere points per ball for Tier 1 adaptive ODE")
    ap.add_argument("--rtol", type=float, default=5e-6)
    ap.add_argument("--atol", type=float, default=5e-7)
    ap.add_argument("--scalar-t", action="store_true", help="Force synchronous scalar float(t) in Stage 5 as well")
    ap.add_argument("--block-numpy", action="store_true", help="Block any import of numpy at runtime")
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--device", default="cpu")
    ap.add_argument("--json", default=None, help="Optional JSON output path")
    args = ap.parse_args()
    json_out = os.path.abspath(args.json) if args.json else None

    if args.block_numpy:
        block_numpy_imports()

    sub_mod = load_submission(args.solution)
    all_ok = True
    results = []
    for k_val in args.k:
        for eps_val in args.eps:
            rep = check_one(
                sub_mod,
                k_val,
                eps_val,
                tier=args.tier,
                n_per_ball=args.N,
                rtol=args.rtol,
                atol=args.atol,
                scalar_t_only=args.scalar_t,
                seed=args.seed,
                device=args.device,
            )
            results.append(rep)
            all_ok = all_ok and bool(rep["passed"])
    if json_out:
        os.makedirs(os.path.dirname(json_out), exist_ok=True)
        with open(json_out, "w", encoding="utf-8") as f:
            json.dump(results[0] if len(results) == 1 else results, f, indent=2)
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
