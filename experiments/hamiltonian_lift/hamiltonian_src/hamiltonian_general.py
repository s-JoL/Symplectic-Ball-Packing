"""Experimental / unfinished 6-stage PyTorch Hamiltonian prototype `H(Q, P, t)` (NOT a certified deliverable).

Explores lifting Paper IV's closed-form packing chain `Chain3(k, epsilon)` into a 6-stage isotopy
(see `experiments/hamiltonian_lift/README.md` and `DIAGNOSTICS.md` for unfinished status and known failure probes):
  - **Stage 0 `[0.00, 0.05]`**: Rigid Euclidean translation from initial separated `sources` `(3*i, 0, 0, 0)`
    to O(1)-spaced local pivots `local_pivots[i]` (`local_park = local_pivots - a_i`, lift amplitudes chosen by sampling).
  - **Stage 1 `[0.05, 0.10]`**: Symplectic unitary polar factor `U_i(sigma)` around `local_pivots[i]`.
  - **Stage 2 `[0.10, 0.15]`**: Symplectic SPD stretch factor `P_i(sigma) U_i` around `local_pivots[i]`,
    matching `Df_i(a_i)` at `sigma = 1`.
  - **Stage 3 `[0.15, 0.22]`**: Local Alexander germ nonlinearization `rho = tau * sigma in [0, tau]`
    around `local_pivots[i]`, using Gauss-Legendre quadrature when `0 < rho <= 1e-4`.
  - **Stage 4 `[0.22, 0.28]`**: Rigid 4D-lifted Euclidean translation from `local_pivots[i]` to the radial
    entry pivots `park_pivots[i] = f_i(a_i) / tau` (lift amplitudes chosen by sampling).
  - **Stage 5 `[0.28, 1.00]`**: Global radial-Alexander dilation `v(t): tau -> 1`,
    `gamma_v^{(i)}(u) = f_i((1 - v)a_i + v u) / v`, reparametrized by a quadratic clock; while open-ball images
    `f_i(B^0(r_dom)) / v` are pairwise disjoint for `v > 0`, straight-ray sheet unwrapping in Stages 9-11 still
    exhibits unresolved scalar jumps in cutoff collars near small `|Z_0|` (e.g. `k = 12, eps = 0.001`).
"""
from __future__ import annotations

import math
import torch

try:
    from .chain_primitive import ChainWithPrimitive, load_embedding_modules
    from .h_primitives import flat_step, flat_step_scalar, gauss_legendre_01
except ImportError:
    from chain_primitive import ChainWithPrimitive, load_embedding_modules  # type: ignore
    from h_primitives import flat_step, flat_step_scalar, gauss_legendre_01  # type: ignore

PI = math.pi
F64 = torch.float64

_OM4 = torch.tensor(
    [[0.0, 0.0, 1.0, 0.0], [0.0, 0.0, 0.0, 1.0], [-1.0, 0.0, 0.0, 0.0], [0.0, -1.0, 0.0, 0.0]],
    dtype=F64,
)
_JC4 = torch.tensor(
    [[0.0, 0.0, -1.0, 0.0], [0.0, 0.0, 0.0, -1.0], [1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0]],
    dtype=F64,
)


def sin4_clock(u: float) -> tuple[float, float]:
    """Moderate-derivative C^4 smooth clock `S(u), S'(u)` on `[0, 1]` with `S'(u) = (8/3) sin^4(pi*u)`."""
    if u <= 0.0:
        return 0.0, 0.0
    if u >= 1.0:
        return 1.0, 0.0
    a = 2.0 * PI * u
    s = u - 2.0 * math.sin(a) / (3.0 * PI) + math.sin(2.0 * a) / (12.0 * PI)
    ds = 1.0 - (4.0 / 3.0) * math.cos(a) + (1.0 / 3.0) * math.cos(2.0 * a)
    return s, ds


def _omega_vec(a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
    return a[..., 0] * b[..., 2] + a[..., 1] * b[..., 3] - a[..., 2] * b[..., 0] - a[..., 3] * b[..., 1]


class AnalyticStage4Clock:
    """Closed-form `C^inf` real-analytic clock `s in [0, 1] -> (v(s), dv/ds(s))` on `[tau, 1.0]`.

    Inverts the exact convex combination of radial (`1/v`) and interior (`v`) arc-length
        `s(v) = ((v - tau) / (1 - tau)) * (alpha / v + (1 - alpha))`
    via its unique positive quadratic root, completely eliminating spline-knot `v''(s)` discontinuities
    so adaptive 5th-order Dormand-Prince RK45 achieves full `O(h^5)` accuracy everywhere on `[0, 1]`.
    """

    def __init__(self, tau: float, alpha: float = 0.35):
        self.tau = float(tau)
        self.alpha = float(alpha)
        self.A = 1.0 - self.alpha
        self.om_tau = 1.0 - self.tau
        self.c_prod = 4.0 * self.A * self.alpha * self.tau

    def evaluate(self, s: float) -> tuple[float, float]:
        sc = min(max(float(s), 0.0), 1.0)
        B = self.alpha - self.tau * self.A - self.om_tau * sc
        disc = math.sqrt(B * B + self.c_prod)
        # Cancellation-free positive root for both signs of B:
        v = (2.0 * self.alpha * self.tau) / (B + disc) if B >= 0.0 else (-B + disc) / (2.0 * self.A)
        dv_ds = self.om_tau / (self.alpha * self.tau / (v * v) + self.A)
        return v, dv_ds

    def evaluate_tensor(self, s: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        sc = s.clamp(0.0, 1.0)
        B = self.alpha - self.tau * self.A - self.om_tau * sc
        disc = torch.sqrt(B * B + self.c_prod)
        v_posB = (2.0 * self.alpha * self.tau) / (B + disc).clamp_min(1e-300)
        v_negB = (-B + disc) / (2.0 * self.A)
        v = torch.where(B >= 0.0, v_posB, v_negB)
        dv_ds = self.om_tau / (self.alpha * self.tau / (v * v) + self.A)
        return v, dv_ds


class ExactPolarSymplecticPath:
    """Exact left-polar `Sp(4)` path `M(sigma)` from `I_4` to `A in Sp(4)`."""

    def __init__(self, A_raw: torch.Tensor):
        I4 = torch.eye(4, dtype=F64)
        self.I4 = I4
        A = A_raw.to(F64).clone()
        for _ in range(5):
            res = A.T @ _OM4 @ A - _OM4
            if float(res.abs().max().item()) < 1e-15:
                break
            A = A - 0.5 * (A @ (-_OM4 @ res))
        self.A = A

        evals, evecs = torch.linalg.eigh(A @ A.T)
        evals = torch.clamp(evals, min=1e-30)
        log_s0 = 0.25 * (torch.log(evals[3]) - torch.log(evals[0]))
        log_s1 = 0.25 * (torch.log(evals[2]) - torch.log(evals[1]))

        w0 = evecs[:, 3] / torch.linalg.norm(evecs[:, 3])
        z0 = -(_OM4 @ w0)
        w1 = evecs[:, 2].clone()
        w1 = w1 - torch.dot(w1, w0) * w0 - torch.dot(w1, z0) * z0
        w1 = w1 / torch.linalg.norm(w1)
        z1 = -(_OM4 @ w1)
        self.W_sp = torch.stack([w0, w1, z0, z1], dim=1)
        self.log_sp = torch.stack([log_s0, log_s1, -log_s0, -log_s1])

        P_L_inv = (self.W_sp * torch.exp(-self.log_sp).unsqueeze(0)) @ self.W_sp.T
        U = P_L_inv @ A
        for _ in range(3):
            U = 0.5 * U @ (3.0 * I4 - U.T @ U)
            res_u = U.T @ _OM4 @ U - _OM4
            U = U - 0.5 * (U @ (-_OM4 @ res_u))
        self.U = U

        best_m = 0
        best_det = -1.0
        for m in range(3):
            th = PI * m / 3.0
            Vm = (math.cos(th) * I4 + math.sin(th) * _JC4) @ U
            dv = abs(float(torch.linalg.det(Vm + I4).item()))
            if dv > best_det:
                best_det = dv
                best_m = m
        self.theta = PI * best_m / 3.0
        V_best = (math.cos(self.theta) * I4 + math.sin(self.theta) * _JC4) @ U
        X_raw = (V_best - I4) @ torch.linalg.inv(V_best + I4)
        self.X = 0.5 * (X_raw - X_raw.T)
        self.norm_bound = float(torch.exp(self.log_sp.abs().max()).item())

    def evaluate_unitary(self, sigma: float) -> tuple[torch.Tensor, torch.Tensor]:
        I4 = self.I4
        ang = -sigma * self.theta
        R_s = math.cos(ang) * I4 + math.sin(ang) * _JC4
        R_dot = -self.theta * (_JC4 @ R_s)
        inv_X = torch.linalg.inv(I4 - sigma * self.X)
        C_s = (I4 + sigma * self.X) @ inv_X
        C_dot = (I4 + C_s) @ self.X @ inv_X
        return R_s @ C_s, R_dot @ C_s + R_s @ C_dot

    def evaluate_stretch(self, sigma: float) -> tuple[torch.Tensor, torch.Tensor]:
        p_diag = torch.exp(sigma * self.log_sp)
        pdot_diag = self.log_sp * p_diag
        P_s = (self.W_sp * p_diag.unsqueeze(0)) @ self.W_sp.T
        P_dot = (self.W_sp * pdot_diag.unsqueeze(0)) @ self.W_sp.T
        return P_s @ self.U, P_dot @ self.U


class GeneralPackingHamiltonian:
    """Experimental / unfinished 6-stage Hamiltonian-lift prototype (not certified; see README.md & DIAGNOSTICS.md)."""

    T_BREAKS = (0.0, 0.05, 0.10, 0.15, 0.22, 0.28, 1.0)

    def __init__(self, k: int, epsilon: float, tau_max: float = 0.05):
        if isinstance(k, bool) or int(k) != k or k < 10 or not (0.0 < float(epsilon) < 1.0):
            raise ValueError("Require integer k >= 10 and float epsilon in (0, 1)")
        self.k = int(k)
        self.epsilon = float(epsilon)
        self.R_needed = (self.k / (1.0 - self.epsilon)) ** 0.25

        mods = load_embedding_modules()
        cmp_mod = mods["comparator"]
        tr_mod = mods["transfer"]
        ch_mod = mods["chain"]

        # Use balanced transfer collar (`fd2 = 0.28, fsig = 0.20`) and wider cell budget up to `0.06`
        # whenever all 36 analytic hypotheses `(H0)-(H15)` of Paper IV pass (strictly verified by `Chain3`),
        # simultaneously keeping `sig0 = 0.20 * D` (high `L_kappa` boundary clearance) and wider `d2 = 0.28 * D`.
        chain = None
        orig_cap = cmp_mod.EPS_C_MAX
        orig_fr = dict(tr_mod.FR)
        try:
            for fr_try in (
                dict(fm=0.32, fd2=0.28, fsig=0.20, fdel=0.10),
                orig_fr,
            ):
                tr_mod.FR.update(fr_try)
                for cap_try in (0.06, 0.04, 0.02, 0.01):
                    try:
                        cmp_mod.EPS_C_MAX = cap_try
                        chain = ch_mod.Chain3(self.k, self.epsilon)
                        break
                    except ValueError:
                        continue
                if chain is not None:
                    break
        finally:
            cmp_mod.EPS_C_MAX = orig_cap
            tr_mod.FR.update(orig_fr)
        if chain is None:
            chain = ch_mod.Chain3(self.k, self.epsilon)

        self.cp = ChainWithPrimitive(chain)
        self.r_dom = self.cp.r_dom
        if not (self.r_dom > 1.0):
            raise RuntimeError(f"Expected domain radius r_dom > 1, got {self.r_dom}")

        self.gap_dom = min(0.25, self.r_dom - 1.0)
        self.r1 = 1.0 + 0.35 * self.gap_dom
        self.r2 = 1.0 + 0.70 * self.gap_dom
        self.r3_wide = 1.48

        # Separated initial Euclidean balls along +q_1 axis at official Epoch centers `(3*i, 0, 0, 0)`!
        self.sources = torch.zeros((self.k, 4), dtype=F64)
        self.sources[:, 0] = 3.0 * torch.arange(self.k, dtype=F64)
        self.r1_stage0 = 1.15
        self.r2_stage0 = 1.40

        # Vectorized ray-speed-and-clearance interior basepoint selection across all k balls in O(1) passes!
        g_cand = torch.Generator().manual_seed(20261112)
        M_cand = 160 if self.k <= 40 else (48 if self.k <= 200 else 16)
        cands = torch.randn((M_cand, 4), generator=g_cand, dtype=F64)
        cands = cands / torch.linalg.norm(cands, dim=1, keepdim=True) * (
            0.42 * torch.rand((M_cand, 1), generator=g_cand, dtype=F64) ** 0.25
        )
        cands[0] = 0.0

        i_grid = torch.repeat_interleave(torch.arange(self.k, dtype=torch.int64), M_cand)
        a_grid = cands.repeat(self.k, 1).detach().requires_grad_(True)
        y_grid, _, _, _, _, _ = self.cp.batched_local_pass(i_grid, a_grid)
        J_all = torch.stack(
            [torch.autograd.grad(y_grid[:, r].sum(), a_grid, retain_graph=(r < 3))[0] for r in range(4)],
            dim=1,
        ).detach().view(self.k, M_cand, 4, 4)
        nrm_all = torch.linalg.matrix_norm(J_all, ord=2)  # (k, M_cand)

        # Rank top K_top small-Jacobian candidates per ball (note: at large k, ||Df_i||_2 scales as O(k^{3/4}),
        # so penalize only non-finite Jacobians instead of a fixed <= 14 cutoff!)
        K_top = min(M_cand, 32 if self.k <= 40 else (8 if self.k <= 200 else 6))
        pen_nrm = torch.where(torch.isfinite(nrm_all), nrm_all, torch.full_like(nrm_all, 1e30))
        top_idx = torch.argsort(pen_nrm, dim=1)[:, :K_top]  # (k, K_top)
        top_a = cands[top_idx]  # (k, K_top, 4)
        top_J = J_all[torch.arange(self.k)[:, None], top_idx]  # (k, K_top, 4, 4)
        top_nrm = nrm_all[torch.arange(self.k)[:, None], top_idx]  # (k, K_top)

        n_u_cl = 32 if self.k <= 60 else 6
        n_v_cl = 40 if self.k <= 60 else 6
        u_cl = torch.randn((n_u_cl, 4), generator=g_cand, dtype=F64)
        u_cl = u_cl / torch.linalg.norm(u_cl, dim=1, keepdim=True)
        v_cl = torch.linspace(0.05, 0.995, n_v_cl, dtype=F64)
        with torch.no_grad():
            # Evaluate in chunks to keep peak memory small while testing candidates along rays
            ws_cl = (
                (1.0 - v_cl[None, None, :, None, None]) * top_a[:, :, None, None, :]
                + v_cl[None, None, :, None, None] * u_cl[None, None, None, :, :]
            )
            P_cl = n_v_cl * n_u_cl
            total_pts = self.k * K_top * P_cl
            ws_flat = ws_cl.reshape(total_pts, 4)
            iv_flat = torch.repeat_interleave(torch.arange(self.k, dtype=torch.int64), K_top * P_cl)
            chunk_sz = 32768
            yw_chunks = [
                self.cp.batched_local_pass(iv_flat[s : s + chunk_sz], ws_flat[s : s + chunk_sz])[0]
                for s in range(0, total_pts, chunk_sz)
            ]
            yw_cl = torch.cat(yw_chunks, dim=0).view(self.k, K_top, n_v_cl, n_u_cl, 4)
            gaps_cl = (
                1.0 - torch.linalg.norm(yw_cl, dim=-1).amax(dim=(2, 3)) / chain.Rs
            )  # (k, K_top)
            yv_cl = yw_cl / v_cl[None, None, :, None, None]
            dv_cl = (v_cl[1:] - v_cl[:-1])[None, None, :, None, None]
            ray_spd = torch.linalg.norm((yv_cl[:, :, 1:] - yv_cl[:, :, :-1]) / dv_cl, dim=-1).amax(dim=(2, 3))  # (k, K_top)

        min_nrm_per_ball = top_nrm.min(dim=1, keepdim=True).values.clamp_min(5.0)
        bad_cand = (~torch.isfinite(ray_spd)) | (gaps_cl <= 0.0) | (top_nrm > 3.0 * min_nrm_per_ball + 8.0)
        # Prioritize strict boundary clearance `1 - |Y|/Rs` FIRST so no ray approaches `L_kappa` (`|Z_0| -> 0`),
        # with gentle tie-breaking toward lower ray speed and smaller relative `||Df_i(a_i)||_2`.
        scores = (
            1000.0 * gaps_cl
            - 0.15 * torch.log(ray_spd.clamp_min(1.0))
            - 0.20 * (top_nrm / min_nrm_per_ball)
            - torch.where(bad_cand, torch.full_like(top_nrm, 1e6), torch.zeros_like(top_nrm))
        )
        best_sub = torch.argmax(scores, dim=1)
        self.base_a = top_a[torch.arange(self.k), best_sub].contiguous()
        J_best_all = top_J[torch.arange(self.k), best_sub].contiguous()

        with torch.no_grad():
            i_all = torch.arange(self.k, dtype=torch.int64)
            fa_all, sa_all = self.cp.batched_embed_and_action(i_all, self.base_a, fast_plateau=False)
        self.f_a = fa_all.detach()
        self.S_a_tensor = sa_all.detach()
        self.S_a = self.S_a_tensor.tolist()
        self.paths = [ExactPolarSymplecticPath(J_best_all[i]) for i in range(self.k)]

        # Precompute batched Stage 1 / Stage 2 polar path tensors across all k balls
        self.path_theta = torch.tensor([p.theta for p in self.paths], dtype=F64)
        self.path_X = torch.stack([p.X for p in self.paths], dim=0)
        self.path_W = torch.stack([p.W_sp for p in self.paths], dim=0)
        self.path_log_sp = torch.stack([p.log_sp for p in self.paths], dim=0)
        self.path_U = torch.stack([p.U for p in self.paths], dim=0)
        norm_bounds = torch.tensor([p.norm_bound for p in self.paths], dtype=F64)

        # Compute Stage 1-3 bounding radii `box_radii[i]` uniformly over `rho in (0, tau_max]`
        u_samp = torch.randn((64, 4), generator=g_cand, dtype=F64)
        u_samp = self.r3_wide * u_samp / torch.linalg.norm(u_samp, dim=1, keepdim=True)
        u_samp[:8] = torch.cat([torch.eye(4, dtype=F64), -torch.eye(4, dtype=F64)], dim=0) * self.r3_wide
        du_all = u_samp[None, :, :] - self.base_a[:, None, :]  # (k, 64, 4)
        max_du = torch.linalg.norm(du_all, dim=-1).max(dim=1).values  # (k,)
        lin_rad = norm_bounds * max_du
        # Fixed-point `tau` search: converge `tau_cur` so `shape_rad` validated on `(0, tau_cur]` satisfies `tau_cur <= _choose_disjoint_tau`
        self.box_radii = 1.45 * torch.maximum(lin_rad, max_du) + 3.5
        tau_cur = self._choose_disjoint_tau(float(tau_max))
        iv_samp = torch.repeat_interleave(torch.arange(self.k, dtype=torch.int64), 64)
        with torch.no_grad():
            for _ in range(12):
                shape_rad = max_du.clone()
                for rho_p in (0.35 * tau_cur, 0.70 * tau_cur, tau_cur):
                    w_p = (self.base_a[:, None, :] + rho_p * du_all).reshape(-1, 4)
                    yw_p = self.cp.batched_local_pass(iv_samp, w_p)[0].view(self.k, 64, 4)
                    disp = torch.linalg.norm((yw_p - self.f_a[:, None, :]) / rho_p, dim=-1).max(dim=1).values
                    shape_rad = torch.maximum(shape_rad, disp)
                self.box_radii = 1.45 * torch.maximum(lin_rad, shape_rad) + 3.5
                tau_adm = self._choose_disjoint_tau(float(tau_max))
                if tau_adm >= 0.98 * tau_cur and (tau_adm <= 1.20 * tau_cur or tau_cur >= 0.99 * float(tau_max)):
                    tau_cur = min(tau_cur, tau_adm)
                    break
                if tau_adm > 1.20 * tau_cur:
                    tau_cur = min(float(tau_max), math.sqrt(tau_cur * tau_adm))
                else:
                    tau_cur = max(0.75 * tau_adm, 1e-10)
            # Final validation pass on `[0, tau_cur]` so `box_radii` strictly bounds `(0, self.tau]`
            shape_rad = max_du.clone()
            for rho_p in (0.35 * tau_cur, 0.70 * tau_cur, tau_cur):
                w_p = (self.base_a[:, None, :] + rho_p * du_all).reshape(-1, 4)
                yw_p = self.cp.batched_local_pass(iv_samp, w_p)[0].view(self.k, 64, 4)
                disp = torch.linalg.norm((yw_p - self.f_a[:, None, :]) / rho_p, dim=-1).max(dim=1).values
                shape_rad = torch.maximum(shape_rad, disp)
            self.box_radii = 1.45 * torch.maximum(lin_rad, shape_rad) + 3.5
        self.tau = min(tau_cur, self._choose_disjoint_tau(float(tau_max)))
        self.r1_wide, self.r2_wide = self._radii_for_v(self.tau)

        # Radial parking pivots `f_a / tau` => Stage 4 ends IDENTICALLY at Stage 5's `v = tau` start!
        self.park_pivots = self.f_a / self.tau
        self.park = self.park_pivots - self.base_a

        # Well-conditioned O(1)-spaced local pivots along +q_1 (with +q_2 offset) for Stages 1-3:
        # Cumulative spacing `2.6 * box_radii + 6.0` guarantees pairwise disjoint boxes of radius `box_radii`
        # while keeping coordinates O(sum box_radii) instead of O(1 / tau), preventing float64 cancellation!
        half_steps = 1.35 * self.box_radii + 3.5
        cum_x = torch.cumsum(2.0 * half_steps, dim=0) - half_steps
        self.local_pivots = torch.zeros((self.k, 4), dtype=F64)
        self.local_pivots[:, 0] = cum_x
        self.local_pivots[:, 1] = 8.0 + float(self.box_radii.max().item())
        self.local_park = self.local_pivots - self.base_a

        # Orthogonal `(q_2, p_1, p_2)` lift directions for Stage 0 and Stage 4 translations
        idx_f = torch.arange(self.k, dtype=F64)
        p1 = 2.0 * PI * idx_f * 0.6180339887498949 + 0.3
        p2 = 2.0 * PI * idx_f * 0.3819660112501051 + 1.1
        self.lift0_dirs = torch.stack(
            [torch.zeros(self.k, dtype=F64), torch.cos(p1), torch.sin(p1), 0.7 * torch.cos(p2)], dim=1
        )
        self.lift0_dirs = self.lift0_dirs / torch.linalg.norm(self.lift0_dirs, dim=1, keepdim=True)
        self.A_lift0 = self._find_safe_lift(
            self.sources, self.local_park, self.lift0_dirs, 2.0 * self.r2_stage0 + 0.08
        )
        self.A_lift4 = self._find_safe_lift_boxes(
            self.local_pivots, self.park_pivots, self.lift0_dirs, self.box_radii
        )

        self.tail_clock = AnalyticStage4Clock(self.tau, alpha=0.35)
        self.support_radius = float(
            max(
                (torch.linalg.norm(self.sources, dim=1) + self.r3_wide).max().item(),
                (torch.linalg.norm(self.local_pivots, dim=1) + self.box_radii).max().item() + self.A_lift0 + 25.0,
                (torch.linalg.norm(self.park_pivots, dim=1) + self.box_radii).max().item() + self.A_lift4 + 25.0,
            )
        )

    def _choose_disjoint_tau(self, tau_max: float) -> float:
        if self.k <= 2000:
            dmat = torch.cdist(self.f_a, self.f_a)
            req = 1.25 * (self.box_radii[:, None] + self.box_radii[None, :]) + 4.0
            eye = torch.eye(self.k, dtype=torch.bool)
            ratios = (dmat / req).masked_fill(eye, math.inf)
            return min(tau_max, float(ratios.min().item()))
        # Large-k O(k) check: group balls vs all + sliding action window of width 48
        ng = min(self.k, 32)
        d_grp = torch.cdist(self.f_a[:ng], self.f_a)
        req_grp = 1.25 * (self.box_radii[:ng, None] + self.box_radii[None, :]) + 4.0
        for bi in range(ng):
            d_grp[bi, bi] = math.inf
        best = float((d_grp / req_grp).min().item())
        for shift in range(1, min(48, self.k)):
            d_sh = torch.linalg.norm(self.f_a[:-shift] - self.f_a[shift:], dim=1)
            req_sh = 1.25 * (self.box_radii[:-shift] + self.box_radii[shift:]) + 4.0
            best = min(best, float((d_sh / req_sh).min().item()))
        return min(tau_max, best)

    def _radii_for_v(self, v: float) -> tuple[float, float]:
        g_raw = (0.52 * (1.0 - v) + 0.80 * self.gap_dom) / max(v, 1e-12)
        g_cap = 0.48 * g_raw / math.hypot(0.48, g_raw)
        return 1.0 + (0.30 / 0.48) * g_cap, 1.0 + g_cap

    def _radii_for_v_tensor(self, v: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        g_raw = (0.52 * (1.0 - v) + 0.80 * self.gap_dom) / v.clamp_min(1e-12)
        g_cap = 0.48 * g_raw / torch.hypot(torch.full_like(g_raw, 0.48), g_raw)
        return 1.0 + (0.30 / 0.48) * g_cap, 1.0 + g_cap

    def _find_safe_lift(
        self, start: torch.Tensor, end: torch.Tensor, dirs: torch.Tensor, min_dist_req: float
    ) -> float:
        if self.k > 500:
            return 2.0 * float(torch.maximum(torch.linalg.norm(start, dim=1), torch.linalg.norm(end, dim=1)).max().item()) + 40.0
        amp = 0.0
        sg = torch.linspace(0.0, 1.0, 401, dtype=F64)[:, None, None]
        eye = torch.eye(self.k, dtype=torch.bool).unsqueeze(0).expand(401, self.k, self.k)
        for _ in range(12):
            pos = (1.0 - sg) * start[None] + sg * end[None] + (4.0 * sg * (1.0 - sg) * amp) * dirs[None]
            dmat = torch.cdist(pos, pos).masked_fill(eye, math.inf)
            if float(dmat.min().item()) > min_dist_req:
                return amp
            amp = 12.0 if amp == 0.0 else amp * 2.0
        return amp

    def _find_safe_lift_boxes(
        self, start: torch.Tensor, end: torch.Tensor, dirs: torch.Tensor, radii: torch.Tensor
    ) -> float:
        if self.k > 500:
            return 0.25 * float(torch.maximum(torch.linalg.norm(start, dim=1), torch.linalg.norm(end, dim=1)).max().item()) + 80.0
        amp = 0.0
        sg = torch.linspace(0.0, 1.0, 201, dtype=F64)[:, None, None]
        req = (1.05 * (radii[:, None] + radii[None, :]) + 0.5)[None, :, :]
        eye = torch.eye(self.k, dtype=torch.bool).unsqueeze(0).expand(201, self.k, self.k)
        for _ in range(14):
            pos = (1.0 - sg) * start[None] + sg * end[None] + (4.0 * sg * (1.0 - sg) * amp) * dirs[None]
            dmat = torch.cdist(pos, pos).masked_fill(eye, math.inf)
            if bool((dmat > req).all()):
                return amp
            amp = 25.0 if amp == 0.0 else amp * 2.0
        return amp

    def _stage_clock(self, t: float) -> tuple[int | None, float, float]:
        if t <= 0.0 or t >= 1.0:
            return None, 0.0, 0.0
        tb = self.T_BREAKS
        for m in range(len(tb) - 1):
            if t < tb[m + 1] or m == len(tb) - 2:
                span = tb[m + 1] - tb[m]
                u = (t - tb[m]) / span
                sig, dsig = sin4_clock(u)
                return m, sig, dsig / span
        return None, 0.0, 0.0

    def _cutoff(self, r_sq: torch.Tensor, r1: float | torch.Tensor | None = None, r2: float | torch.Tensor | None = None) -> torch.Tensor:
        r1_v = self.r1 if r1 is None else r1
        r2_v = self.r2 if r2 is None else r2
        r1_sq = r1_v * r1_v
        r2_sq = r2_v * r2_v
        return 1.0 - flat_step((r_sq - r1_sq) / (r2_sq - r1_sq))

    @staticmethod
    def _stage3_rho(sig: float, tau: float) -> tuple[float, float]:
        """Exact C^inf-blended germ clock `rho(sig), drho/dsig` vanishing near `sig -> 0+`."""
        if sig <= 1e-5:
            return 0.0, 0.0
        if sig >= 4e-4:
            return tau * sig, tau
        u_b = (sig - 1e-5) / (4e-4 - 1e-5)
        b_val = flat_step_scalar(u_b, 0)
        db_dsig = flat_step_scalar(u_b, 1) / (4e-4 - 1e-5)
        return tau * sig * b_val, tau * (b_val + sig * db_dsig)

    def _germ_disp_and_deriv(self, ib: torch.Tensor, ai: torch.Tensor, fa_b: torch.Tensor, du: torch.Tensor, rho: float) -> tuple[torch.Tensor, torch.Tensor]:
        """Evaluate `(f_i(a_i + rho du) - f_i(a_i)) / rho` and `d/drho [...]` for the trajectory diagnostic.

        For `rho > 1e-4`, evaluates `(f_i(w) - f_i(a_i)) / rho` and `(rho Df_i(w) du - (f_i(w) - f_i(a_i))) / rho^2`
        directly via PyTorch autograd JVP. For `0 < rho <= 1e-4`, evaluates the integral representation
        `int_0^1 Df_i(a_i + s rho du) du ds` and `int_0^1 ((Df_i(a_i + rho du) - Df_i(a_i + s rho du)) / rho) du ds`
        using six-point Gauss-Legendre quadrature on `[0, 1]`; its numerical error requires bounds on the relevant
        higher derivatives, so this small-`rho` branch is a numerical diagnostic rather than an exact closed-form certificate.
        """
        def _jvp_at(r_val: float) -> tuple[torch.Tensor, torch.Tensor]:
            w_r = (ai + r_val * du).detach().requires_grad_(True)
            yw_r = self.cp.batched_local_pass(ib, w_r)[0]
            j_mat = torch.stack(
                [torch.autograd.grad((yw_r[:, c_i]).sum(), w_r, retain_graph=(c_i < 3))[0] for c_i in range(4)],
                dim=1,
            )
            return yw_r.detach(), torch.bmm(j_mat.detach(), du[:, :, None]).squeeze(-1)

        if rho > 1e-4:
            yw, df_end = _jvp_at(rho)
            disp = (yw - fa_b) / rho
            d_disp = (rho * df_end - (yw - fa_b)) / (rho * rho)
            return disp, d_disp

        _, df_end = _jvp_at(rho)
        gl_nodes, gl_weights = gauss_legendre_01(6)
        disp = torch.zeros_like(du)
        d_disp = torch.zeros_like(du)
        for s_t, w_t in zip(gl_nodes.tolist(), gl_weights.tolist()):
            _, df_s = _jvp_at(s_t * rho)
            disp = disp + w_t * df_s
            d_disp = d_disp + w_t * ((df_end - df_s) / rho)
        return disp, d_disp

    def exact_trajectory_and_velocity(
        self, t: float, u_local: torch.Tensor, ball_idx: int
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """Evaluate `(gamma_t^{(i)}(u_local), d/dt gamma_t^{(i)}(u_local))` for trajectory residual checks
        (closed-form via PyTorch autograd for `rho > 1e-4` and Stage 5; six-point Gauss-Legendre quadrature
        of the integral representation when `0 < rho <= 1e-4`).
        """
        u_d = u_local.to(F64)
        z_v = torch.zeros_like(u_d)
        if t <= 0.0:
            return u_d + self.sources[ball_idx], z_v
        if t >= 1.0:
            return self.cp.ch.Embed(ball_idx, u_d), z_v
        stage, sig, dsig = self._stage_clock(t)
        if stage is None:
            return u_d + self.sources[ball_idx], z_v
        ai = self.base_a[ball_idx]
        ib = torch.full((u_d.shape[0],), int(ball_idx), dtype=torch.int64, device=u_d.device)
        if stage == 0:
            src, prk, l0 = self.sources[ball_idx], self.local_park[ball_idx], self.lift0_dirs[ball_idx]
            c = (1.0 - sig) * src + sig * prk + 4.0 * sig * (1.0 - sig) * self.A_lift0 * l0
            dc = dsig * ((prk - src) + 4.0 * (1.0 - 2.0 * sig) * self.A_lift0 * l0)
            return u_d + c, dc.unsqueeze(0).expand_as(u_d)
        if stage in (1, 2):
            M, Mdot = (
                self.paths[ball_idx].evaluate_unitary(sig)
                if stage == 1
                else self.paths[ball_idx].evaluate_stretch(sig)
            )
            du = u_d - ai
            return self.local_pivots[ball_idx] + du @ M.T, dsig * (du @ Mdot.T)
        if stage == 3:
            rho, drho_dsig = self._stage3_rho(sig, self.tau)
            drho = drho_dsig * dsig
            du = u_d - ai
            if rho <= 1e-14:
                return self.local_pivots[ball_idx] + du @ self.paths[ball_idx].A.T, z_v
            disp, d_disp = self._germ_disp_and_deriv(ib, ai, self.f_a[ball_idx], du, rho)
            return self.local_pivots[ball_idx] + disp, (drho * d_disp if abs(drho) > 1e-30 else z_v)
        if stage == 4:
            du = u_d - ai
            shape_tau, _ = self._germ_disp_and_deriv(ib, ai, self.f_a[ball_idx], du, self.tau)
            loc_p, prk_p, l0 = self.local_pivots[ball_idx], self.park_pivots[ball_idx], self.lift0_dirs[ball_idx]
            c4 = (1.0 - sig) * loc_p + sig * prk_p + 4.0 * sig * (1.0 - sig) * self.A_lift4 * l0
            dc4 = dsig * ((prk_p - loc_p) + 4.0 * (1.0 - 2.0 * sig) * self.A_lift4 * l0)
            return c4 + shape_tau, dc4.unsqueeze(0).expand_as(u_d)
        # Stage 5: radial-Alexander dilation `v: tau -> 1`
        v, dv_ds = self.tail_clock.evaluate(sig)
        dv = dv_ds * dsig
        du = u_d - ai
        w_req = ((1.0 - v) * ai + v * u_d).detach().requires_grad_(True)
        yw = self.cp.batched_local_pass(ib, w_req)[0]
        jvp = torch.stack(
            [torch.autograd.grad((yw[:, c_i]).sum(), w_req, retain_graph=(c_i < 3))[0] for c_i in range(4)],
            dim=1,
        )
        df_du = torch.bmm(jvp, du[:, :, None]).squeeze(-1)
        pos = yw.detach() / v
        vel = dv * (v * df_du - yw.detach()) / (v * v)
        return pos, vel

    def exact_trajectory(self, t: float, u_local: torch.Tensor, ball_idx: int) -> torch.Tensor:
        """Closed-form trajectory `gamma_t(u_local + sources[ball_idx])` on `|u_local| <= 1` for `t in [0, 1]`."""
        return self.exact_trajectory_and_velocity(t, u_local, ball_idx)[0]

    def _eval_stage4_tensor_t(self, y: torch.Tensor, out: torch.Tensor, t_vec: torch.Tensor) -> torch.Tensor:
        """Vectorized O(1) Stage 5 (`t in [0.28, 1.0]`) evaluation supporting per-row tensor `t_vec`."""
        dev = y.device
        t4_lo = self.T_BREAKS[5]
        span4 = 1.0 - t4_lo
        u_clk = ((t_vec - t4_lo) / span4).clamp(0.0, 1.0)
        a_clk = 2.0 * PI * u_clk
        sig_v = u_clk - 2.0 * torch.sin(a_clk) / (3.0 * PI) + torch.sin(2.0 * a_clk) / (12.0 * PI)
        dsig_v = (1.0 - (4.0 / 3.0) * torch.cos(a_clk) + (1.0 / 3.0) * torch.cos(2.0 * a_clk)) / span4
        v_vec, dv_ds = self.tail_clock.evaluate_tensor(sig_v)
        dv_vec = dv_ds * dsig_v * ((t_vec > t4_lo) & (t_vec < 1.0)).to(F64)
        if not bool((dv_vec.abs() > 1e-18).any()):
            return out

        r1_vec, r2_vec = self._radii_for_v_tensor(v_vec)
        r1_sq_vec, r2_sq_vec = r1_vec * r1_vec, r2_vec * r2_vec
        r_cut_w = min(1.0 + 0.97 * (self.r_dom - 1.0), 1.0 + 0.92 * self.gap_dom)
        Y_sc = v_vec[:, None] * y

        act_glob, j_act, wd = self.cp.preimage_active_batched(Y_sc, r_cutoff=r_cut_w)
        if act_glob.numel() == 0:
            return out

        base_dev = self.base_a.to(dev)
        sa_dev = self.S_a_tensor.to(dev)
        va_g = v_vec[act_glob]
        dva_g = dv_vec[act_glob]
        ud = (wd - (1.0 - va_g)[:, None] * base_dev[j_act]) / va_g[:, None]
        rsq = torch.sum(ud * ud, dim=-1)
        in_col = (rsq.detach() < r2_sq_vec[act_glob]) & (dva_g.abs() > 1e-18)
        if not bool(in_col.any()):
            return out

        act_sub = act_glob[in_col]
        j_sub = j_act[in_col]
        w_sub = wd[in_col]
        rsq_sub = rsq[in_col]
        va_sub = va_g[in_col]
        dva_sub = dva_g[in_col]
        r1sq_s = r1_sq_vec[act_sub]
        r2sq_s = r2_sq_vec[act_sub]

        pl_mask = rsq_sub.detach() <= r1sq_s * 0.999999
        with torch.no_grad():
            _, dS_val = self.cp.batched_embed_and_action(j_sub, w_sub.detach(), base_pts=base_dev[j_sub])
        Y_sub = Y_sc[act_sub]
        dS_w = (
            dS_val
            + 0.5 * _omega_vec(Y_sub.detach(), Y_sub - Y_sub.detach())
            - 0.5 * _omega_vec(w_sub.detach(), w_sub - w_sub.detach())
        )
        if bool(pl_mask.all()):
            cut = torch.ones_like(rsq_sub)
        else:
            cut = torch.where(
                pl_mask, torch.ones_like(rsq_sub), 1.0 - flat_step((rsq_sub - r1sq_s) / (r2sq_s - r1sq_s))
            )

        gen_s = 2.0 * dS_w + _omega_vec(base_dev[j_sub], w_sub)
        vals = cut * ((-dva_sub / (va_sub ** 3)) * gen_s)
        return out + torch.zeros_like(out).index_add(0, act_sub, vals)

    def __call__(self, Q: torch.Tensor, P: torch.Tensor, t: float | torch.Tensor) -> torch.Tensor:
        y = torch.cat([Q, P], dim=-1)
        out = 0.0 * torch.sum(y, dim=-1)
        dev = y.device

        if torch.is_tensor(t):
            return self._eval_stage4_tensor_t(y, out, t.to(dtype=F64, device=dev))

        stage, sig, dsig = self._stage_clock(float(t))
        if stage is None or abs(dsig) <= 1e-18:
            return out

        if stage == 5:
            t_vec = torch.full((Q.shape[0],), float(t), dtype=F64, device=dev)
            return self._eval_stage4_tensor_t(y, out, t_vec)

        r1_w = self.r1_wide
        r2_w = self.r2_wide
        r1_w_sq = r1_w * r1_w
        r2_w_sq = r2_w * r2_w
        ch = self.cp.ch
        base_dev = self.base_a.to(dev)

        if stage == 0:
            r1_0, r2_0 = self.r1_stage0, self.r2_stage0
            r1_0_sq, r2_0_sq = r1_0 * r1_0, r2_0 * r2_0
            src_d = self.sources.to(dev)
            prk_d = self.local_park.to(dev)
            l0_d = self.lift0_dirs.to(dev)
            c_all = (1.0 - sig) * src_d + sig * prk_d + (4.0 * sig * (1.0 - sig) * self.A_lift0) * l0_d
            v_all = dsig * ((prk_d - src_d) + (4.0 * (1.0 - 2.0 * sig) * self.A_lift0) * l0_d)
            ni, bi = torch.nonzero(
                torch.sum((y.detach()[:, None, :] - c_all[None, :, :]) ** 2, dim=-1) < r2_0_sq, as_tuple=True
            )
            if ni.numel() == 0:
                return out
            u_act = y[ni] - c_all[bi]
            rsq = torch.sum(u_act * u_act, dim=-1)
            pl_m = rsq.detach() <= r1_0_sq * 0.999999
            cut = (
                torch.ones_like(rsq)
                if bool(pl_m.all())
                else torch.where(pl_m, torch.ones_like(rsq), self._cutoff(rsq, r1_0, r2_0))
            )
            vals = cut * _omega_vec(v_all[bi], u_act)
            return out + torch.zeros_like(out).index_add(0, ni, vals)

        if stage == 4:
            loc_d = self.local_pivots.to(dev)
            prk_p_d = self.park_pivots.to(dev)
            l0_d = self.lift0_dirs.to(dev)
            c4_all = (1.0 - sig) * loc_d + sig * prk_p_d + (4.0 * sig * (1.0 - sig) * self.A_lift4) * l0_d
            v4_all = dsig * ((prk_p_d - loc_d) + (4.0 * (1.0 - 2.0 * sig) * self.A_lift4) * l0_d)
            box_sq4 = (self.box_radii.to(dev) ** 2)[None, :]
            ni, bi = torch.nonzero(
                torch.sum((y.detach()[:, None, :] - c4_all[None, :, :]) ** 2, dim=-1) < box_sq4, as_tuple=True
            )
            if ni.numel() == 0:
                return out
            fa_d = self.f_a.to(dev)
            max_r = (1.0 - 1e-11) * ch.Rs
            with torch.no_grad():
                zd4 = fa_d[bi] + self.tau * (y[ni].detach() - c4_all[bi])
                in_b4 = torch.sum(zd4 * zd4, dim=1) < max_r * max_r
                if not bool(in_b4.any()):
                    return out
                ni, bi, zd4 = ni[in_b4], bi[in_b4], zd4[in_b4]
                wc4 = self.cp.batched_preimage_known_balls(bi, zd4)
                uc4 = base_dev[bi] + (wc4 - base_dev[bi]) / self.tau
                r_dom_safe = 1.0 + 0.97 * (self.r_dom - 1.0)
                plaus4 = (
                    torch.isfinite(wc4).all(dim=1)
                    & (torch.linalg.norm(wc4, dim=1) < r_dom_safe)
                    & (torch.sum(uc4 * uc4, dim=1) < r2_w_sq)
                )
                if not bool(plaus4.any()):
                    return out
                ni, bi, zd4, wc4 = ni[plaus4], bi[plaus4], zd4[plaus4], wc4[plaus4]
                ychk4, _, _, _, _, _ = self.cp.batched_local_pass(bi, wc4)
                rt_ok4 = torch.isfinite(ychk4).all(dim=1) & (torch.linalg.norm(ychk4 - zd4, dim=1) < 1e-3)
                if not bool(rt_ok4.any()):
                    return out
                ni, bi = ni[rt_ok4], bi[rt_ok4]
            dy4 = y[ni] - c4_all[bi]
            z4 = fa_d[bi] + self.tau * dy4
            zn4 = torch.linalg.norm(z4.detach(), dim=1, keepdim=True)
            zs4 = torch.where(zn4 >= max_r, z4 * (max_r / torch.clamp(zn4, min=1e-30)), z4)
            wd4 = self.cp.batched_preimage_known_balls(bi, zs4)
            ud4 = base_dev[bi] + (wd4 - base_dev[bi]) / self.tau
            rsq4 = torch.sum(ud4 * ud4, dim=-1)
            pl_m4 = rsq4.detach() <= r1_w_sq * 0.999999
            cut4 = (
                torch.ones_like(rsq4)
                if bool(pl_m4.all())
                else torch.where(pl_m4, torch.ones_like(rsq4), self._cutoff(rsq4, r1_w, r2_w))
            )
            vals4 = cut4 * _omega_vec(v4_all[bi], dy4)
            return out + torch.zeros_like(out).index_add(0, ni, vals4)

        piv_d = self.local_pivots.to(dev)
        box_sq = (self.box_radii.to(dev) ** 2)[None, :]
        near = torch.sum((y.detach()[:, None, :] - piv_d[None, :, :]) ** 2, dim=-1) < box_sq
        ni, bi = torch.nonzero(near, as_tuple=True)
        if ni.numel() == 0:
            return out

        if stage in (1, 2):
            om_d = _OM4.to(dev)
            I4_d = torch.eye(4, dtype=F64, device=dev)
            if stage == 1:
                ang = -sig * self.path_theta.to(dev)  # (k,)
                ca, sa = torch.cos(ang), torch.sin(ang)
                jc_d = _JC4.to(dev)
                R_s = ca[:, None, None] * I4_d[None] + sa[:, None, None] * jc_d[None]
                R_dot = -self.path_theta.to(dev)[:, None, None] * torch.matmul(jc_d[None], R_s)
                X_d = self.path_X.to(dev)
                inv_X = torch.linalg.inv(I4_d[None] - sig * X_d)
                C_s = torch.matmul(I4_d[None] + sig * X_d, inv_X)
                C_dot = torch.matmul(torch.matmul(I4_d[None] + C_s, X_d), inv_X)
                M_all = torch.matmul(R_s, C_s)
                Mdot_all = torch.matmul(R_dot, C_s) + torch.matmul(R_s, C_dot)
            else:
                W_d = self.path_W.to(dev)
                lsp_d = self.path_log_sp.to(dev)
                U_d = self.path_U.to(dev)
                p_diag = torch.exp(sig * lsp_d)
                pdot_diag = lsp_d * p_diag
                P_s = torch.matmul(W_d * p_diag[:, None, :], W_d.transpose(1, 2))
                P_dot = torch.matmul(W_d * pdot_diag[:, None, :], W_d.transpose(1, 2))
                M_all = torch.matmul(P_s, U_d)
                Mdot_all = torch.matmul(P_dot, U_d)

            Minv_b = torch.matmul(torch.matmul(-om_d[None], M_all[bi].transpose(1, 2)), om_d[None])
            dy = y[ni] - piv_d[bi]
            du = torch.bmm(Minv_b, dy[:, :, None]).squeeze(-1)
            u_act = du + base_dev[bi]
            rsq = torch.sum(u_act * u_act, dim=-1)
            in_col = rsq.detach() < r2_w_sq
            if not bool(in_col.any()):
                return out
            ni_c, dy_c, du_c, rsq_c, Mdot_c = ni[in_col], dy[in_col], du[in_col], rsq[in_col], Mdot_all[bi[in_col]]
            pl_m = rsq_c.detach() <= r1_w_sq * 0.999999
            cut = (
                torch.ones_like(rsq_c)
                if bool(pl_m.all())
                else torch.where(pl_m, torch.ones_like(rsq_c), self._cutoff(rsq_c, r1_w, r2_w))
            )
            Mdot_du = torch.bmm(Mdot_c, du_c[:, :, None]).squeeze(-1)
            vals = cut * (0.5 * dsig * _omega_vec(Mdot_du, dy_c))
            return out + torch.zeros_like(out).index_add(0, ni_c, vals)

        # Stage 3: local germ homotopy `rho(sig) in [0, tau]` around O(1) `local_pivots`
        rho, drho_dsig = self._stage3_rho(sig, self.tau)
        drho_dt = drho_dsig * dsig
        if rho <= 0.0 or abs(drho_dt) <= 1e-30:
            return out

        fa_d = self.f_a.to(dev)
        sa_d = self.S_a_tensor.to(dev)
        max_r = (1.0 - 1e-11) * ch.Rs
        with torch.no_grad():
            zd = fa_d[bi] + rho * (y[ni].detach() - piv_d[bi])
            in_b = torch.sum(zd * zd, dim=1) < max_r * max_r
            if not bool(in_b.any()):
                return out
            ni, bi, zd = ni[in_b], bi[in_b], zd[in_b]
            wc = self.cp.batched_preimage_known_balls(bi, zd)
            uc = base_dev[bi] + (wc - base_dev[bi]) / rho
            r_dom_safe = 1.0 + 0.97 * (self.r_dom - 1.0)
            plaus = (
                torch.isfinite(wc).all(dim=1)
                & (torch.linalg.norm(wc, dim=1) < r_dom_safe)
                & (torch.sum(uc * uc, dim=1) < r2_w_sq)
            )
            if not bool(plaus.any()):
                return out
            ni, bi, zd, wc = ni[plaus], bi[plaus], zd[plaus], wc[plaus]
            ychk, _, _, _, _, _ = self.cp.batched_local_pass(bi, wc)
            rt_ok = torch.isfinite(ychk).all(dim=1) & (torch.linalg.norm(ychk - zd, dim=1) < 1e-3)
            if not bool(rt_ok.any()):
                return out
            ni, bi = ni[rt_ok], bi[rt_ok]

        dy_s3 = y[ni] - piv_d[bi]
        z_act = fa_d[bi] + rho * dy_s3
        zn = torch.linalg.norm(z_act.detach(), dim=1, keepdim=True)
        zs = torch.where(zn >= max_r, z_act * (max_r / torch.clamp(zn, min=1e-30)), z_act)
        wd = self.cp.batched_preimage_known_balls(bi, zs)
        ud = base_dev[bi] + (wd - base_dev[bi]) / rho
        rsq = torch.sum(ud * ud, dim=-1)
        pl_m = rsq.detach() <= r1_w_sq * 0.999999
        cut = (
            torch.ones_like(rsq)
            if bool(pl_m.all())
            else torch.where(pl_m, torch.ones_like(rsq), self._cutoff(rsq, r1_w, r2_w))
        )
        # Exact single-branch closed-form generator for ALL `rho > 0` (ZERO finite differences, ZERO Taylor truncation):
        # Algebraically, `2(S_i(w) - S_i(a_i)) + omega_0(a_i, w) - omega_0(f_i(a_i), z)` with `z = f_i(a_i) + rho dy`,
        # `w = a_i + dw` decomposes at `y_0 = y.detach()` into exact scalar value `gen_0` plus exact tangent `gen_tan`:
        #   `gen_0   = 2(S_i(w_0) - S_i(a_i)) + omega_0(a_i, dw_0) - rho omega_0(f_i(a_i), dy_0)`,
        #   `gen_tan = rho^2 omega_0(dy_0, dy) - omega_0(dw_0, dw)`  (vanishes at `y_0`, exact O(rho^2) derivative!).
        with torch.no_grad():
            _, dS_val = self.cp.batched_embed_and_action(bi, wd.detach(), base_pts=base_dev[bi])
        dw = wd - base_dev[bi]
        dw0 = dw.detach()
        dy0 = dy_s3.detach()
        gen_0 = 2.0 * dS_val + _omega_vec(base_dev[bi], dw0) - rho * _omega_vec(fa_d[bi], dy0)
        gen_tan = (rho * rho) * _omega_vec(dy0, dy_s3) - _omega_vec(dw0, dw)
        vals = cut * ((-drho_dt / (rho ** 3)) * (gen_0 + gen_tan))
        return out + torch.zeros_like(out).index_add(0, ni, vals)
