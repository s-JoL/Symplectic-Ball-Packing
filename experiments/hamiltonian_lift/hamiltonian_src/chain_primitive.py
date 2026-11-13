"""Experimental local potential evaluator and autograd patches for the unfinished Hamiltonian-lift prototype.

Patches `primitives`, `keyhole`, `comparator`, `transfer`, and `chain` in-place for PyTorch `autograd`
differentiation and evaluates candidate local stage potentials + finite radial ray-unwrapping heuristics.
NOTE: This module is part of the unfinished experimental prototype (NOT certified by Paper IV or Lean 4):
straight-ray unwrapping misses integer turns near small `|Z_0|` and has an unapplied seam-constant discrepancy
documented in `experiments/hamiltonian_lift/DIAGNOSTICS.md`.
"""
from __future__ import annotations

import cmath
import math
from pathlib import Path
import sys
import torch

PI = math.pi
F64 = torch.float64
C128 = torch.complex128

_PATCHED = False


def _safe_atan2_turns(y: torch.Tensor, x: torch.Tensor) -> torch.Tensor:
    z_mask = (x.detach() == 0.0) & (y.detach() == 0.0)
    x_s = torch.where(z_mask, torch.ones_like(x), x)
    y_s = torch.where(z_mask, torch.zeros_like(y), y)
    ang = torch.atan2(y_s, x_s) / (2.0 * PI)
    return torch.where(z_mask, torch.zeros_like(ang), ang)


def _safe_sqrt(x: torch.Tensor) -> torch.Tensor:
    return torch.where(x > 1e-30, torch.sqrt(torch.clamp(x, min=1e-30)), torch.zeros_like(x))


def _mom(w: torch.Tensor) -> torch.Tensor:
    return PI * (w[..., 0] ** 2 + w[..., 1] ** 2)


def _polar0(w: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
    return _mom(w), _safe_atan2_turns(w[..., 1], w[..., 0])


def _patch_transfer_float64(pr_mod, kh_mod, cmp_mod, tr_mod, ch_mod):
    """Patch Paper IV modules in-place so `w == 0`, `psi == 0`, `X == 0` have smooth autograd and zero cancellation."""
    if getattr(tr_mod, "_h_float64_patched", False):
        return
    tr_mod._h_float64_patched = True

    def fast_newton_bracket(f, lo, hi, x0, iters=32):
        with torch.no_grad():
            x = x0.detach().clone()
            lo_d, hi_d = lo.detach().clone(), hi.detach().clone()
            for step in range(iters):
                v_d, dv_d = f(x)
                lo_d = torch.where(v_d < 0.0, x, lo_d)
                hi_d = torch.where(v_d >= 0.0, x, hi_d)
                xn_d = x - v_d / torch.clamp(dv_d, min=1e-300)
                bad = ~((xn_d > lo_d) & (xn_d < hi_d))
                x_next = torch.where(bad, 0.5 * (lo_d + hi_d), xn_d)
                if step >= 5 and (step & 1):
                    tol_x = 1e-15 * (1.0 + x_next.abs())
                    if bool(((x_next - x).abs() <= tol_x).all()):
                        x = x_next
                        break
                x = x_next
            # One guaranteed full-precision Newton polish at exit
            v_p, dv_p = f(x)
            xn_p = x - v_p / torch.clamp(dv_p, min=1e-300)
            x = torch.where((xn_p > lo_d) & (xn_p < hi_d), xn_p, x)
        v, dv = f(x)
        return x - v / dv.detach()

    pr_mod.newton_bracket = fast_newton_bracket
    pr_mod.polar0 = _polar0

    def smooth_Pmi(self, psi: torch.Tensor) -> torch.Tensor:
        ap = psi.abs()
        D = self.W2 - self.W1
        u = (ap - self.W1) / D
        outer = torch.where(psi >= 0.0, 1.0, -1.0) * (
            (self.rho1 - 1.0) * ap + (self.rho_out - self.rho1) * (D * self.st.I(u) + (ap - self.W2).clamp_min(0.0))
        )
        return torch.where(ap <= self.W1, (self.rho1 - 1.0) * psi, outer)

    def smooth_kh_fwd(self, w: torch.Tensor, tau: torch.Tensor | float | None = None):
        X, phi = self.polar_c(w)
        Mv, dM = self.M(X)
        tt = dM if tau is None else tau * dM
        with torch.no_grad():
            ap = phi.detach().abs()
            psi_abs = fast_newton_bracket(
                lambda x: (x + tt.detach() * self.Pmi(x) - ap, 1.0 + tt.detach() * (self.dPsi(x) - 1.0)),
                torch.zeros_like(ap),
                torch.full_like(ap, 0.5),
                ap.clamp(0.0, 0.5),
            )
            psi_star = psi_abs * torch.where(phi.detach() >= 0.0, 1.0, -1.0)
        res_phi = psi_star + tt * self.Pmi(psi_star) - phi
        denom_phi = 1.0 + tt * (self.dPsi(psi_star) - 1.0)
        psi = psi_star - res_phi / denom_phi.detach()
        t = 1.0 if tau is None else tau
        Xn = X + t * Mv * (self.dPsi(psi) - 1.0)
        return self.cart_c(Xn, psi), Mv * self.Pmi(psi)

    def smooth_kh_inv(self, w: torch.Tensor, tau: torch.Tensor | float | None = None):
        Xn, psi = self.polar_c(w)
        t = torch.ones_like(Xn) if tau is None else tau + 0.0 * Xn
        a = t * (self.dPsi(psi) - 1.0)
        Xlin = (Xn + 0.5 * a * self.Xw) / (1.0 + a)
        inner = Xlin.detach() < self.Xw
        X = Xlin
        if bool(inner.any()):
            ai, Xi = a[inner], Xn[inner]
            Xr = fast_newton_bracket(
                lambda x: (x + ai * self.M(x)[0] - Xi, 1.0 + ai * self.M(x)[1]),
                torch.zeros_like(Xi.detach()),
                torch.full_like(Xi.detach(), self.Xw),
                Xi.detach().clamp(0.0, self.Xw),
            )
            X = X.clone()
            X[inner] = Xr
        Mv, dM = self.M(X)
        phi = psi + t * dM * self.Pmi(psi)
        near_c = (Xn.detach() < 1e-20) & (X.detach() < 0.1 * self.Xw)
        w_out = torch.where(near_c[:, None], w, self.cart_c(X, phi))
        return w_out, Mv * self.Pmi(psi)

    def safe_polar_c(self, w: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        dq = w[..., 0] + self.d
        return PI * (dq * dq + w[..., 1] ** 2), _safe_atan2_turns(w[..., 1], dq)

    def safe_cart_c(self, X: torch.Tensor, psi: torch.Tensor) -> torch.Tensor:
        r = _safe_sqrt(X / PI)
        return torch.stack((r * torch.cos(2.0 * PI * psi) - self.d, r * torch.sin(2.0 * PI * psi)), -1)

    kh_mod.SmoothKeyhole.Pmi = smooth_Pmi
    kh_mod.SmoothKeyhole.polar_c = safe_polar_c
    kh_mod.SmoothKeyhole.cart_c = safe_cart_c
    kh_mod.SmoothKeyhole.fwd = smooth_kh_fwd
    kh_mod.SmoothKeyhole.inv = smooth_kh_inv

    def fast_kr_inv(self, yl: torch.Tensor) -> torch.Tensor:
        X, T, w = yl[:, 0], yl[:, 1], yl[:, 2:]
        r2 = torch.clamp((self.a - _mom(w)) / PI, min=1e-30)
        r = torch.sqrt(r2)
        m2 = (2.0 * (X / r2 - 0.5 * PI)).clamp(-PI + 1e-15, PI - 1e-15)
        with torch.no_grad():
            md = m2.detach()
            lo = torch.full_like(md, -0.5 * PI)
            hi = torch.full_like(md, 0.5 * PI)
            rem = (0.75 * (PI - md.abs()).clamp_min(0.0)).pow(1.0 / 3.0)
            al_edge = torch.where(md >= 0.0, 0.5 * PI - rem, -0.5 * PI + rem)
            al = torch.where(md.abs() > 2.0, al_edge, 0.25 * md).clamp(-0.5 * PI + 1e-15, 0.5 * PI - 1e-15)
            for step in range(36):
                v = 2.0 * al + torch.sin(2.0 * al) - md
                dv = 2.0 + 2.0 * torch.cos(2.0 * al)
                lo = torch.where(v < 0.0, al, lo)
                hi = torch.where(v >= 0.0, al, hi)
                an = al - v / torch.clamp(dv, min=1e-30)
                bad = ~((an > lo) & (an < hi))
                al_next = torch.where(bad, 0.5 * (lo + hi), an)
                if step >= 8 and bool((v.abs() <= 1e-15).all()):
                    al = al_next
                    break
                al = al_next
        v = 2.0 * al + torch.sin(2.0 * al) - m2
        dv = (2.0 + 2.0 * torch.cos(2.0 * al)).detach().clamp_min(1e-30)
        al = al - v / dv
        x, c = r * torch.sin(al), torch.clamp(r * torch.cos(al), min=1e-30)
        y = (2.0 * T - 1.0) * c
        C = (X - x * c) / (PI * r2) * (T - 0.5)
        return torch.cat((x[:, None], y[:, None], pr_mod.rot(w, -C)), dim=1)

    kh_mod.KRStrip.inv = fast_kr_inv

    def smooth_comp2(self, y: torch.Tensor, inverse: bool = False) -> torch.Tensor:
        G, v, w = y[:, 0], y[:, 1], y[:, 2:]
        c, dc = self.cG(G)
        act = c > 0.0
        out = y.clone()
        if bool(act.any()):
            wa = w[act]
            x = _mom(wa)
            vt = _safe_atan2_turns(-wa[:, 1], -wa[:, 0])
            sgn = -1.0 if inverse else 1.0
            out[act, 1] = v[act] - sgn * dc[act] * vt
            scale_r = torch.sqrt(torch.clamp((x + sgn * c[act]) / torch.clamp(x, min=1e-30), min=0.0))
            out[act, 2:] = wa * scale_r[:, None]
        return out

    cmp_mod.Comparator3.comp2 = smooth_comp2

    def cart_post(self, y: torch.Tensor) -> torch.Tensor:
        G, v, w = y[:, 0], y[:, 1], y[:, 2:]
        p = _mom(w)
        hb = 3.0 - 9.0 * p
        ua = G / hb + self.lift
        ang = -9.0 * (ua - self.lift) * v
        return torch.cat(((hb * v)[:, None], (self.psi0 - ua)[:, None], pr_mod.rot(w, ang)), dim=1)

    def cart_post_inv(self, x: torch.Tensor) -> torch.Tensor:
        sig, psi, w = x[:, 0], x[:, 1], x[:, 2:]
        p = _mom(w)
        hb = 3.0 - 9.0 * p
        ua = self.psi0 - psi
        v = sig / hb
        ang = 9.0 * (ua - self.lift) * v
        return torch.cat((((ua - self.lift) * hb)[:, None], v[:, None], pr_mod.rot(w, ang)), dim=1)

    ch_mod.Chain3._post = cart_post
    ch_mod.Chain3._post_inv = cart_post_inv

    def cart_band(self, x: torch.Tensor, inverse: bool) -> torch.Tensor:
        sig0, psi0, w0 = x[:, 0], x[:, 1], x[:, 2:]
        p0 = _mom(w0)
        n = torch.floor((sig0 / (3.0 - 9.0 * p0) + 1.0 / 6.0).detach())
        sig, psi = sig0 - n * (3.0 - 9.0 * p0), psi0
        out = x.clone()
        for j in range(3):
            c = sig - j * (1.0 - 3.0 * p0)
            mk = c.detach().abs() < self.m
            if not bool(mk.any()):
                continue
            cm = c[mk]
            a_, b_ = self.left[j]
            kj = self.kstep(cm, j)
            ps = psi[mk] + a_ + kj
            nn = n[mk]
            ang_in = -nn * (9.0 * psi[mk] + 0.5) + b_ - 3.0 * j * (psi[mk] + a_)
            w_in = pr_mod.rot(w0[mk], ang_in)
            T_v, dT = self.tau(cm)
            if not inverse:
                w2, gen = self.kh.fwd(w_in, T_v)
                ps2 = ps - dT * gen
            else:
                w2, gen = self.kh.inv(w_in, T_v)
                ps2 = ps + dT * gen
            p2 = _mom(w2)
            so = cm + j * (1.0 - 3.0 * p2)
            po = ps2 - a_ - kj
            ang_out = 3.0 * j * ps2 - b_ - 3.0 * j * kj + nn * (9.0 * po + 0.5)
            w_out = pr_mod.rot(w2, ang_out)
            out[mk] = torch.cat(((so + nn * (3.0 - 9.0 * p2))[:, None], po[:, None], w_out), dim=1)
        return out

    tr_mod.Transfer3._band = cart_band

    def exact_post_W(self, sig0, psi0, p0, vt0, w_cart=None):
        """Post-Band homogeneous vector W without polar singularity at `w_cart == 0`."""
        n = torch.floor((sig0 / (3.0 - 9.0 * p0) + 1.0 / 6.0).detach())
        sig = sig0 - n * (3.0 - 9.0 * p0)
        psi = psi0
        p = p0
        vt = vt0 - n * (9.0 * psi0 + 0.5)
        if w_cart is None:
            r_p = _safe_sqrt(p0 / PI)
            w_cpx0 = torch.complex(r_p * torch.cos(2.0 * PI * vt0), r_p * torch.sin(2.0 * PI * vt0))
        else:
            w_cpx0 = torch.complex(w_cart[:, 0], w_cart[:, 1])
        u_f = math.sqrt(PI) * w_cpx0 * torch.exp(-2j * PI * n * (9.0 * psi0 + 0.5))

        N = len(sig)
        dev = sig.device
        W = torch.zeros(N, 3, dtype=C128, device=dev)
        vc = sig / (3.0 - 9.0 * p)
        mus = [sig, sig - (1.0 - 3.0 * p), sig - 2.0 * (1.0 - 3.0 * p)]
        instrip = [mu.detach().abs() < self.m for mu in mus]
        anys = instrip[0] | instrip[1] | instrip[2]
        secs = [
            (vc.detach() >= 0.0) & (vc.detach() < 1.0 / 3.0) & (~anys),
            (vc.detach() >= 1.0 / 3.0) & (vc.detach() < 2.0 / 3.0) & (~anys),
            (vc.detach() >= 2.0 / 3.0) & (~anys),
            (vc.detach() < 0.0) & (~anys),
        ]
        for mk, key in zip(secs, (0, 1, "2s", "2c")):
            if not bool(mk.any()):
                continue
            a_, b_ = self.off[key]
            ps, pp, sg = psi[mk] + a_, p[mk], sig[mk]
            uf = u_f[mk]
            if key == "2c":
                W[mk] = torch.stack(
                    (
                        _safe_sqrt(1.0 - 2.0 * pp + sg).to(C128),
                        uf * torch.exp(2j * PI * (b_ + ps)),
                        _safe_sqrt(pp - sg) * torch.exp(-2j * PI * ps),
                    ),
                    dim=1,
                )
            elif key == 0:
                W[mk] = torch.stack(
                    (
                        _safe_sqrt(1.0 - 2.0 * pp - sg).to(C128),
                        _safe_sqrt(pp + sg) * torch.exp(2j * PI * ps),
                        uf * torch.exp(2j * PI * (b_ - ps)),
                    ),
                    dim=1,
                )
            elif key == 1:
                # Projectively identical to multiplying by e^{2*pi*i * vv} (since chart9 uses W W^*)!
                W[mk] = torch.stack(
                    (
                        uf * cmath.exp(2j * PI * b_),
                        _safe_sqrt(2.0 - 5.0 * pp - sg) * torch.exp(2j * PI * (4.0 * ps)),
                        _safe_sqrt(4.0 * pp + sg - 1.0) * torch.exp(2j * PI * (5.0 * ps)),
                    ),
                    dim=1,
                )
            else:
                W[mk] = torch.stack(
                    (
                        _safe_sqrt(7.0 * pp + sg - 2.0).to(C128),
                        uf * torch.exp(2j * PI * (b_ - 8.0 * ps)),
                        _safe_sqrt(3.0 - 8.0 * pp - sg) * torch.exp(-2j * PI * ps),
                    ),
                    dim=1,
                )

        for j in range(3):
            mk = instrip[j]
            if not bool(mk.any()):
                continue
            c = mus[j][mk]
            a_, b_ = self.left[j]
            kj = self.kstep(c, j)
            ps = psi[mk] + a_ + kj
            rot_cpx = (u_f[mk] / math.sqrt(PI)) * torch.exp(2j * PI * (b_ - 3.0 * j * (psi[mk] + a_)))
            w2 = torch.stack((rot_cpx.real, rot_cpx.imag), dim=-1)
            p2, ang = _polar0(w2)
            vl = ang - torch.floor(ang.detach())
            lp, lm, lamp = self.lam_split(c)
            xa = p2 + lp
            xb = p2 + lm
            xr = 1.0 - xa - xb
            Ta = ps + lamp * vl
            Wb_pol = _safe_sqrt(xb) * torch.exp(2j * PI * (vl - Ta))
            Wb_cart = math.sqrt(PI) * torch.complex(w2[:, 0], w2[:, 1]) * torch.exp(-2j * PI * Ta)
            Wb = torch.where((lm.detach() == 0.0) & (p2.detach() < 1e-24), Wb_cart, Wb_pol)
            loc = torch.stack((_safe_sqrt(xr).to(C128), _safe_sqrt(xa) * torch.exp(2j * PI * Ta), Wb), dim=1)
            perm = ((0, 1, 2), (1, 2, 0), (2, 0, 1))[j]
            Wg = torch.zeros_like(loc)
            for li, gi in enumerate(perm):
                Wg[:, gi] = loc[:, li]
            W[mk] = Wg
        return W

    def exact_post_invert_cart(self, W):
        """Cancellation-free Cartesian left inverse of `_PostChartW.W` (prior to `band_inv`)."""
        W = W / W.abs().pow(2).sum(1, keepdim=True).sqrt()
        X = W.abs() ** 2
        ang = _safe_atan2_turns(W.imag, W.real)
        N = len(W)
        dev = W.device
        nan = torch.full((N,), float("nan"), dtype=F64, device=dev)
        sig, psi, wx, wy = nan.clone(), nan.clone(), nan.clone(), nan.clone()
        done = torch.zeros(N, dtype=torch.bool, device=dev)

        for j in range(3):
            a, b = (j + 1) % 3, (j + 2) % 3
            mu = X[:, a] - X[:, b]
            mk = (mu.detach().abs() < self.m) & (X[:, j].detach() > 1.0 / 3.0)
            if not bool(mk.any()):
                continue
            c = mu[mk]
            lp, lm, dl = self.lam_split(c)
            p2 = torch.where(c >= 0.0, X[mk, b] - lm, X[mk, a] - lp).clamp_min(0.0)
            Ta = ang[mk, a] - ang[mk, j]
            Tb = ang[mk, b] - ang[mk, j]
            vl = torch.remainder(Ta + Tb, 1.0)
            ps2 = Ta - dl * vl
            kj = self.kstep(c, j)
            a_, b_ = self.left[j]
            psi_o = ps2 - kj - a_
            ph_j = W[mk, j].conj() / torch.clamp(W[mk, j].abs(), min=1e-30)
            w2_pol = pr_mod.cart0(p2, vl)
            cpx_dir = (W[mk, b] * ph_j / math.sqrt(PI)) * torch.exp(2j * PI * ps2)
            w2 = torch.where(
                ((lm.detach() == 0.0) & (X[mk, b].detach() < 1e-24))[:, None],
                torch.stack((cpx_dir.real, cpx_dir.imag), dim=-1),
                w2_pol,
            )
            pp = _mom(w2)
            cpx0 = torch.complex(w2[:, 0], w2[:, 1]) * torch.exp(-2j * PI * (b_ - 3.0 * j * (psi_o + a_)))
            sig[mk], psi[mk], wx[mk], wy[mk] = c + j * (1.0 - 3.0 * pp), psi_o, cpx0.real, cpx0.imag
            done |= mk

        e = torch.argmin(X.detach(), dim=1)
        for key, edge in ((0, 2), (1, 0), ("2s", 1)):
            mk = (~done) & (e == edge)
            if not bool(mk.any()):
                continue
            a_, b_ = self.off[key]
            if key == 0:
                ph0 = W[mk, 0].conj() / torch.clamp(W[mk, 0].abs(), min=1e-30)
                W1n, W2n = W[mk, 1] * ph0, W[mk, 2] * ph0
                pp = X[mk, 2]
                sg = X[mk, 1] - pp
                ps = _safe_atan2_turns(W1n.imag, W1n.real)
                psi_o = ps - a_
                w_cpx = (W2n / math.sqrt(PI)) * torch.exp(-2j * PI * (b_ - ps))
            elif key == 1:
                ph1 = W[mk, 1].conj() / torch.clamp(W[mk, 1].abs(), min=1e-30)
                ph2 = W[mk, 2] / torch.clamp(W[mk, 2].abs(), min=1e-30)
                rel21 = ph2 * ph1
                ps = _safe_atan2_turns(rel21.imag, rel21.real)
                psi_o = ps - a_
                pp = X[mk, 0]
                sg = 1.0 + X[mk, 2] - 4.0 * pp
                g_inv = ph1 * torch.exp(2j * PI * (4.0 * ps))
                w_cpx = (W[mk, 0] * g_inv / math.sqrt(PI)) * cmath.exp(-2j * PI * b_)
            else:
                ph0 = W[mk, 0].conj() / torch.clamp(W[mk, 0].abs(), min=1e-30)
                W1n, W2n = W[mk, 1] * ph0, W[mk, 2] * ph0
                ps = -_safe_atan2_turns(W2n.imag, W2n.real)
                psi_o = ps - a_
                pp = X[mk, 1]
                sg = 3.0 - X[mk, 2] - 8.0 * pp
                w_cpx = (W1n / math.sqrt(PI)) * torch.exp(-2j * PI * (b_ - 8.0 * ps))

            pp_c = PI * (w_cpx.real ** 2 + w_cpx.imag ** 2)
            nr = torch.floor((sg / (3.0 - 9.0 * pp_c) + 1.0 / 6.0).detach())
            sg_r = sg - nr * (3.0 - 9.0 * pp_c)
            w_r = w_cpx * torch.exp(-2j * PI * nr * (9.0 * psi_o + 0.5))
            sig[mk], psi[mk], wx[mk], wy[mk] = sg_r, psi_o, w_r.real, w_r.imag

        return sig, psi, wx, wy

    def patched_unchart(self, y):
        yy = torch.complex(y[:, :2], y[:, 2:]) * math.sqrt(PI)
        rad2 = (yy.real ** 2 + yy.imag ** 2).sum(dim=1)
        Z0 = torch.sqrt(torch.clamp(1.0 - rad2, min=1e-30)).to(C128)
        kap = self.kappa_line
        W1 = (yy[:, 0] - kap.conjugate() * Z0) / math.sqrt(2.0)
        W2 = (Z0 + kap * yy[:, 0]) / math.sqrt(2.0)
        return torch.stack((yy[:, 1], W1, W2), dim=1)

    def patched_wproj(self, x):
        p, vt = _polar0(x[:, 2:])
        return self._proj(self._Z(self.post.W(x[:, 0], x[:, 1], p, vt, w_cart=x[:, 2:])))

    def patched_wpost_inv(self, y):
        sig, psi, wx, wy = self.post._exact_invert_cart(self.post.unchart(y))
        return torch.stack((sig, psi, wx, wy), dim=1)

    def S(self, c):
        ac = torch.sqrt(c * c + 1e-60)
        u = ac / self.d2
        q = self.sig0 * (1.0 - self.st(u))
        dq = -self.sig0 * self.st.d(u) / self.d2 * torch.where(c >= 0.0, 1.0, -1.0) * (u < 1.0)
        S = torch.hypot(c, q)
        dS = torch.where(S > 0.0, (c + q * dq) / S, torch.ones_like(c))
        return S, dS

    def lam_split(self, c):
        """Cancellation-free decomposition (lp, lm, lam') with lp = c - lam(c) >= 0, lm = -lam(c) >= 0.

        Uses `S = sqrt(c^2 + q^2)` so `lp = 0.5*(S + c)` and `lm = 0.5*(S - c)` have smooth derivatives at `c == 0`!
        (Notice `q(0) = sig0 > 0`, so `S(0) = sig0 > 0` has NO cancellation near `c == 0`, while for `|c| >= d2`,
        `q == 0` identically so `rem = q^2 / (2*(S + |c|)) == 0` has NO cancellation for `|c| >= d2`!)
        """
        ac = torch.sqrt(c * c + 1e-60)
        u = ac / self.d2
        q = self.sig0 * (1.0 - self.st(u))
        dq = -self.sig0 * self.st.d(u) / self.d2 * torch.where(c >= 0.0, 1.0, -1.0) * (u < 1.0)
        S = torch.hypot(c, q)
        dS = (c + q * dq) / S
        # Near c == 0 (|c| < 0.5 * d2), S + c >= sig0 - 0.5*d2 > 0 has zero cancellation AND smooth C^inf derivative across c == 0!
        near0 = c.detach().abs() < 0.5 * self.d2
        denom = 2.0 * (S + ac)
        rem = (q * q) / denom.clamp_min(1e-300)
        lp_far = torch.where(c.detach() >= 0.0, c + rem, rem)
        lm_far = torch.where(c.detach() >= 0.0, rem, -c + rem)
        lp = torch.where(near0, 0.5 * (S + c), lp_far)
        lm = torch.where(near0, 0.5 * (S - c), lm_far)
        return lp, lm, 0.5 * (1.0 - dS)

    tr_mod._PostChartW.S = S
    tr_mod._PostChartW.lam_split = lam_split
    tr_mod._PostChartW.W = exact_post_W
    tr_mod._PostChartW._exact_invert_cart = exact_post_invert_cart
    tr_mod._PostChartW.unchart = patched_unchart
    tr_mod.Transfer3.wproj = patched_wproj
    tr_mod.Transfer3.wpost_inv = patched_wpost_inv


def load_embedding_modules():
    """Load and float64-patch the pure-PyTorch Paper IV modules (from memory if bundled, else `solution_embedding.py`)."""
    req = ("primitives", "keyhole", "comparator", "twists", "transfer", "chain")
    if all(name in sys.modules for name in req):
        pr_mod = sys.modules["primitives"]
        kh_mod = sys.modules["keyhole"]
        cmp_mod = sys.modules["comparator"]
        tw_mod = sys.modules["twists"]
        tr_mod = sys.modules["transfer"]
        r3 = sys.modules["chain"]
        _patch_transfer_float64(pr_mod, kh_mod, cmp_mod, tr_mod, r3)
        return {
            "primitives": pr_mod,
            "keyhole": kh_mod,
            "comparator": cmp_mod,
            "twists": tw_mod,
            "transfer": tr_mod,
            "chain": r3,
            "chain_theorem": r3,
        }

    repo_root = Path(__file__).resolve().parents[1]
    prog_dir = str(repo_root / "program")
    if prog_dir not in sys.path:
        sys.path.insert(0, prog_dir)
    import solution_embedding as se  # type: ignore

    r3 = se._load()
    mods_map = se._probe["mods"]
    pr_mod = mods_map["primitives"]
    kh_mod = mods_map["keyhole"]
    cmp_mod = mods_map["comparator"]
    tw_mod = mods_map["twists"]
    tr_mod = mods_map["transfer"]
    _patch_transfer_float64(pr_mod, kh_mod, cmp_mod, tr_mod, r3)
    return {
        "solution_embedding": se,
        "primitives": pr_mod,
        "keyhole": kh_mod,
        "comparator": cmp_mod,
        "twists": tw_mod,
        "transfer": tr_mod,
        "chain": r3,
        "chain_theorem": r3,
    }


def _keyhole_fwd_with_prim(K, w: torch.Tensor, tau: torch.Tensor | None = None):
    w1, gen = K.fwd(w, tau)
    X, _ = K.polar_c(w)
    _, psi = K.polar_c(w1)
    Mv, dM = K.M(X)
    pmi = K.Pmi(psi)
    t = 1.0 if tau is None else tau
    S_kh = t * (Mv - X * dM) * pmi - 0.5 * K.d * (w1[..., 1] - w[..., 1])
    return w1, gen, S_kh


class ChainWithPrimitive:
    """Wraps a Paper IV `Chain3` instance with exact normalized primitives S_i(X) and vectorized O(1) Preimage."""

    _SEC_CONST = {0: 0.0, 1: 1.0 / 12.0, "2s": 1.0 / 4.0, "2c": 0.0}
    _STRIP_CONST = {0: 0.0, 1: 0.0, 2: -1.0 / 12.0}

    def __init__(self, chain, n_unwrap_init: int = 32):
        self.ch = chain
        self.k = chain.k
        self.scale = chain.scale
        self.scale_sq = chain.scale ** 2
        self.n_unwrap_init = n_unwrap_init
        self.r_dom = math.sqrt(chain.P.a / chain.rho_b)

        z0 = torch.zeros((self.k, 4), dtype=F64)
        i_all = torch.arange(self.k, dtype=torch.int64)
        with torch.no_grad():
            y0_all, sn0_all, _, _, _, _ = self.batched_local_pass(i_all, z0)
        self.centres = y0_all.detach()
        self.sn0_offsets = sn0_all.detach().tolist()
        self.sn0_tensor = sn0_all.detach()

        z_req = torch.zeros((self.k, 4), dtype=F64, requires_grad=True)
        y_req, _, _, _, _, _ = self.batched_local_pass(i_all, z_req)
        self.jac0 = torch.stack(
            [torch.autograd.grad(y_req[:, r].sum(), z_req, retain_graph=(r < 3))[0] for r in range(4)],
            dim=1,
        ).detach()

    def batched_local_pass(
        self, i_vec: torch.Tensor, pts: torch.Tensor
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """Vectorized single-pass `(f_{i}(X), Sn_{i}(X), piece, n_red, vt_br, alpha0)` across mixed ball indices."""
        ch = self.ch
        P = ch.P
        scale = self.scale
        T_tr = ch.T
        tw = ch.tw
        dev = pts.device
        i_f = i_vec.to(F64)
        is_grp = i_vec < ch.ngroup
        has_wild = bool((~is_grp).any())

        z = pts[:, [0, 2, 1, 3]] / scale
        x_s, y_s, w_s = z[:, 0], z[:, 1], z[:, 2:]
        p_s = _mom(w_s)
        th_cur = _safe_atan2_turns(w_s[:, 1], w_s[:, 0])

        yl = ch.strip.fwd(z)
        X_c, T_c = yl[:, 0], yl[:, 1]
        r2_val = torch.clamp((ch.strip.a - p_s) / PI, min=1e-30)
        c_s = torch.sqrt(torch.clamp(r2_val - x_s * x_s, min=1e-30))
        C_s = (X_c - x_s * c_s) / (PI * r2_val) * (T_c - 0.5)
        th_cur = th_cur + C_s
        S_norm = X_c * (T_c - 0.5) + p_s * C_s - 0.5 * x_s * y_s

        S_norm = S_norm + torch.where(is_grp, -T_c / 3.0, (-3.0 + i_f * P.a) * T_c)
        th_cur = th_cur + torch.where(is_grp, -(P.s / 3.0) * T_c, -(3.0 * P.s - i_f) * T_c)

        p_yl = _mom(yl[:, 2:])
        G_yl = torch.where(is_grp, ch.J(p_yl) + 9.0 * X_c, X_c + ch.J(p_yl) + i_f * (P.a - p_yl))
        v_yl = torch.where(is_grp, (i_f - 4.0 + T_c) / 9.0, T_c + ch.vcut)
        ang_yl = torch.where(is_grp, -3.0 * P.s * T_c / 9.0, -(3.0 * P.s - i_f) * T_c)
        ca_y, sa_y = torch.cos(2.0 * PI * ang_yl), torch.sin(2.0 * PI * ang_yl)
        w_yl = torch.stack((ca_y * yl[:, 2] - sa_y * yl[:, 3], sa_y * yl[:, 2] + ca_y * yl[:, 3]), dim=-1)
        y = torch.cat((G_yl[:, None], v_yl[:, None], w_yl), dim=1)

        vt_br = torch.zeros_like(th_cur)
        if has_wild:
            C = ch.C
            wm = ~is_grp
            G0, v0, w0 = y[:, 0], y[:, 1], y[:, 2:]
            tau, dtau = C.tauG(G0)
            act1 = wm & (tau > 0.0)
            y1 = y.clone()
            if bool(act1.any()):
                w1, gen, S_kh = _keyhole_fwd_with_prim(C.K, w0[act1], tau[act1])
                y1[act1, 1] = v0[act1] - dtau[act1] * gen
                y1[act1, 2:] = w1
                S_norm = S_norm.clone()
                S_norm[act1] = S_norm[act1] + (S_kh - G0[act1] * dtau[act1] * gen)
                th1_raw = _safe_atan2_turns(w1[:, 1], w1[:, 0])
                th_cur = th_cur.clone()
                th_cur[act1] = th1_raw
                vt_br = vt_br.clone()
                vt_br[act1] = th1_raw
            G1, v1_all, w1_all = y1[:, 0], y1[:, 1], y1[:, 2:]
            c_val, dc_val = C.cG(G1)
            act2 = wm & (c_val > 0.0)
            y2 = y1.clone()
            if bool(act2.any()):
                wa2 = w1_all[act2]
                x1 = _mom(wa2)
                vt1 = _safe_atan2_turns(-wa2[:, 1], -wa2[:, 0])
                y2[act2, 1] = v1_all[act2] - dc_val[act2] * vt1
                # Smooth Cartesian shift along `wa2` even when `wa2 == (q, 0)` with `q < 0`:
                # notice for `wa2 != 0`, `wa2 / sqrt(x1 / PI)` is unit vector `(cos 2pi th, sin 2pi th)`!
                # At `x1 == 0` (which NEVER occurs when `c_val > 0` because `tau == 1` maps `D(a)` outside `D(x_0)` with `x_1 >= x_0 > 0`!):
                r1 = _safe_sqrt(x1 / PI)
                r2 = _safe_sqrt((x1 + c_val[act2]) / PI)
                u_dir = wa2 / torch.clamp(r1[:, None], min=1e-30)
                y2[act2, 2:] = u_dir * r2[:, None]
                S_norm = S_norm.clone()
                S_norm[act2] = S_norm[act2] + (c_val[act2] - G1[act2] * dc_val[act2]) * vt1
                th2_raw = _safe_atan2_turns(y2[act2, 3], y2[act2, 2])
                th_cur = th_cur.clone()
                th_cur[act2] = th2_raw
                vt_br = vt_br.clone()
                vt_br[act2] = th2_raw
            y = y2

        if tw is not None:
            p5, v5 = _mom(y[:, 2:]), y[:, 1]
            _, Sp_tw = tw.S(p5, v5)
            # Exact periodic primitive S_tw(p, v) = -(3 - 9p)/9 * Sp + c0 * v (zero jump at v == vlo!)
            S_tw = -(3.0 - 9.0 * p5) / 9.0 * Sp_tw + tw.c0 * v5
            S_norm = S_norm + (S_tw - p5 * Sp_tw)
            th_cur = th_cur - Sp_tw
            y = tw.psiS(y, 1.0)

            p5b = _mom(y[:, 2:])
            hb5b = 3.0 - 9.0 * p5b
            u5b = y[:, 0] / hb5b
            g_u, Gg_u = tw.g(u5b)
            S_norm = S_norm + 3.0 * (Gg_u - u5b * g_u)
            th_cur = th_cur + 9.0 * (Gg_u - u5b * g_u)
            y = tw.phiG(y, 1.0)

        G6, v6, w6 = y[:, 0], y[:, 1], y[:, 2:]
        p6 = _mom(w6)
        hb6 = 3.0 - 9.0 * p6
        ua0 = G6 / hb6
        S_norm = S_norm - 3.0 * ua0 * v6
        th_cur = th_cur - 9.0 * ua0 * v6

        sig0 = hb6 * v6
        psi0_v = ch.psi0 - (ua0 + ch.lift)
        ang_post = -9.0 * ua0 * v6
        cp_a, sp_a = torch.cos(2.0 * PI * ang_post), torch.sin(2.0 * PI * ang_post)
        w0_p = torch.stack((cp_a * w6[:, 0] - sp_a * w6[:, 1], sp_a * w6[:, 0] + cp_a * w6[:, 1]), dim=-1)

        p0_p = _mom(w0_p)
        n_red = torch.floor((sig0 / (3.0 - 9.0 * p0_p) + 1.0 / 6.0).detach())
        sig = sig0 - n_red * (3.0 - 9.0 * p0_p)
        psi = psi0_v
        p = p0_p
        vt = th_cur - n_red * (9.0 * psi0_v + 0.5)
        S_norm = S_norm - 3.0 * n_red * psi0_v

        u_f = math.sqrt(PI) * torch.complex(w0_p[:, 0], w0_p[:, 1]) * torch.exp(
            -2j * PI * n_red * (9.0 * psi0_v + 0.5)
        )

        vc = sig / (3.0 - 9.0 * p)
        mus = [sig, sig - (1.0 - 3.0 * p), sig - 2.0 * (1.0 - 3.0 * p)]
        instrip = [mu.detach().abs() < T_tr.m for mu in mus]
        anys = instrip[0] | instrip[1] | instrip[2]
        secs = [
            (vc.detach() >= 0.0) & (vc.detach() < 1.0 / 3.0) & (~anys),
            (vc.detach() >= 1.0 / 3.0) & (vc.detach() < 2.0 / 3.0) & (~anys),
            (vc.detach() >= 2.0 / 3.0) & (~anys),
            (vc.detach() < 0.0) & (~anys),
        ]

        dS_W = torch.zeros_like(sig0)
        W_vec = torch.zeros((pts.shape[0], 3), dtype=C128, device=dev)
        piece = torch.full((pts.shape[0],), -1, dtype=torch.int64, device=dev)

        for idx_s, (mk, key) in enumerate(zip(secs, [0, 1, "2s", "2c"])):
            if not bool(mk.any()):
                continue
            a_, b_ = T_tr.off[key]
            ps, pp, sg = psi[mk] + a_, p[mk], sig[mk]
            uf = u_f[mk]
            if key == "2c":
                W_vec[mk] = torch.stack(
                    (
                        _safe_sqrt(1.0 - 2.0 * pp + sg).to(C128),
                        uf * torch.exp(2j * PI * (b_ + ps)),
                        _safe_sqrt(pp - sg) * torch.exp(-2j * PI * ps),
                    ),
                    dim=1,
                )
            elif key == 0:
                W_vec[mk] = torch.stack(
                    (
                        _safe_sqrt(1.0 - 2.0 * pp - sg).to(C128),
                        _safe_sqrt(pp + sg) * torch.exp(2j * PI * ps),
                        uf * torch.exp(2j * PI * (b_ - ps)),
                    ),
                    dim=1,
                )
            elif key == 1:
                W_vec[mk] = torch.stack(
                    (
                        uf * cmath.exp(2j * PI * b_),
                        _safe_sqrt(2.0 - 5.0 * pp - sg) * torch.exp(2j * PI * (4.0 * ps)),
                        _safe_sqrt(4.0 * pp + sg - 1.0) * torch.exp(2j * PI * (5.0 * ps)),
                    ),
                    dim=1,
                )
                dS_W[mk] = 3.0 * ps + self._SEC_CONST[1]
            else:
                W_vec[mk] = torch.stack(
                    (
                        _safe_sqrt(sg + 7.0 * pp - 2.0).to(C128),
                        uf * torch.exp(2j * PI * (b_ - 8.0 * ps)),
                        _safe_sqrt(3.0 - 8.0 * pp - sg) * torch.exp(-2j * PI * ps),
                    ),
                    dim=1,
                )
                dS_W[mk] = -3.0 * ps + self._SEC_CONST["2s"]
            piece[mk] = 10 + idx_s

        for j_st in range(3):
            mk = instrip[j_st]
            if not bool(mk.any()):
                continue
            c_mu = mus[j_st][mk]
            a_, b_ = T_tr.left[j_st]
            kj = T_tr.kstep(c_mu, j_st)
            rot_cpx = (u_f[mk] / math.sqrt(PI)) * torch.exp(2j * PI * (b_ - 3.0 * j_st * (psi[mk] + a_)))
            w0_sub = torch.stack((rot_cpx.real, rot_cpx.imag), dim=-1)
            T_tau, dT_tau = T_tr.tau(c_mu)
            w2, gen_kh, S_kh = _keyhole_fwd_with_prim(T_tr.kh, w0_sub, T_tau)
            p2 = _mom(w2)
            # Exact Band + W_noKH composition of Paper IV, Section 6 (Theorem 6.1):
            # Band preserves c_mu = sig - j*(1 - 3*p2) and shifts psi by -dT_tau * gen_kh;
            # under the split inequality 2m < D - 3*delta_kh, reduce preserves n_red across Band.
            ang2 = _safe_atan2_turns(w2[:, 1], w2[:, 0])
            vl = ang2 - torch.floor(ang2.detach())
            lp, lm, lamp = T_tr.lam_split(c_mu)
            lam = -lm
            xa = p2 + lp
            xb = p2 + lm
            xr = 1.0 - xa - xb
            ps2 = psi[mk] + a_ + kj - dT_tau * gen_kh
            Ta = ps2 + lamp * vl
            Wb_pol = _safe_sqrt(xb) * torch.exp(2j * PI * (vl - Ta))
            Wb_cart = math.sqrt(PI) * torch.complex(w2[:, 0], w2[:, 1]) * torch.exp(-2j * PI * Ta)
            Wb = torch.where((lm.detach() == 0.0) & (p2.detach() < 1e-24), Wb_cart, Wb_pol)
            loc = torch.stack((_safe_sqrt(xr).to(C128), _safe_sqrt(xa) * torch.exp(2j * PI * Ta), Wb), dim=1)
            perm = [(0, 1, 2), (1, 2, 0), (2, 0, 1)][j_st]
            Wg = torch.zeros_like(loc)
            for li, gi in enumerate(perm):
                Wg[:, gi] = loc[:, li]
            W_vec[mk] = Wg
            u_kj = ((c_mu + T_tr.m) / (2.0 * T_tr.m)).clamp(0.0, 1.0)
            int_kj = T_tr.kap[j_st] * (2.0 * T_tr.m) * T_tr.st.I(u_kj)
            dS_W[mk] = (
                (-j_st * psi[mk] + c_mu * kj - int_kj)
                + (S_kh - c_mu * dT_tau * gen_kh)
                + (c_mu * lamp - lam) * vl
                + self._STRIP_CONST[j_st]
            )
            piece[mk] = j_st

        kap = T_tr.kappa_line
        Z0 = (W_vec[:, 2] - kap * W_vec[:, 1]) / math.sqrt(2.0)
        Z1 = (W_vec[:, 1] + kap.conjugate() * W_vec[:, 2]) / math.sqrt(2.0)
        Z2 = W_vec[:, 0]
        alpha0 = _safe_atan2_turns(Z0.imag, Z0.real)
        nrm = torch.sqrt(
            (Z0.real ** 2 + Z0.imag ** 2) + (Z1.real ** 2 + Z1.imag ** 2) + (Z2.real ** 2 + Z2.imag ** 2)
        )
        ph = torch.conj(Z0) / torch.clamp(torch.abs(Z0), min=1e-30)
        yy = torch.stack((Z1, Z2), dim=1) * ph[:, None] / (math.sqrt(PI) * torch.clamp(nrm[:, None], min=1e-30))
        Y_out = torch.cat((yy.real, yy.imag), dim=1) * scale
        return Y_out, S_norm + dS_W - alpha0, piece, n_red, vt_br, alpha0

    def _raw_local_pass(self, i: int, pts: torch.Tensor):
        i_vec = torch.full((pts.shape[0],), int(i), dtype=torch.int64, device=pts.device)
        return self.batched_local_pass(i_vec, pts)

    def batched_embed_and_action(
        self,
        i_vec: torch.Tensor,
        Xb: torch.Tensor,
        fast_plateau: torch.Tensor | bool = False,
        base_pts: torch.Tensor | None = None,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """Vectorized `(f_i(Xb), S_i(Xb) - S_i(base_i))` satisfying `dS_i = f_i^* lambda_0 - lambda_0`.

        Unwraps multi-sheeted angular branches along straight rays `base_i -> Xb` (`base_i = 0` by default,
        or well-conditioned interior basepoints `base_pts = a_i[i_vec]` avoiding near-line `|Z_0| -> 0` sheets)
        uniformly on ALL rows, with adaptive bisection up to 34 levels (`span <= 2^-38`).
        """
        N = Xb.shape[0]
        if N == 0:
            return Xb.clone(), torch.zeros(0, dtype=F64, device=Xb.device)

        Y_end, Sn_end, _, _, _, _ = self.batched_local_pass(i_vec, Xb)

        with torch.no_grad():
            Xc = Xb.detach()
            B0 = torch.zeros_like(Xc) if base_pts is None else base_pts.detach().to(Xc.device)
            ic = i_vec
            M = N
            n_init = self.n_unwrap_init
            r_sc = self.ch.Rs
            t_grid = torch.linspace(0.0, 1.0, n_init + 1, dtype=F64, device=Xb.device)
            ray_pts = ((1.0 - t_grid)[:, None, None] * B0[None, :, :] + t_grid[:, None, None] * Xc[None, :, :]).reshape(
                (n_init + 1) * M, 4
            )
            ray_i = ic.unsqueeze(0).expand(n_init + 1, M).reshape(-1)
            Y_ray, Sn_ray, pc_ray, nr_ray, vtb_ray, al_ray = self.batched_local_pass(ray_i, ray_pts)
            Y_ray = Y_ray.view(n_init + 1, M, 4)
            Sn_ray = Sn_ray.view(n_init + 1, M)
            pc_ray = pc_ray.view(n_init + 1, M)
            nr_ray = nr_ray.view(n_init + 1, M)
            vtb_ray = vtb_ray.view(n_init + 1, M)
            al_ray = al_ray.view(n_init + 1, M)

            steps = Sn_ray[1:] - Sn_ray[:-1]
            dy_ray = (Y_ray[1:] - Y_ray[:-1]).norm(dim=-1)
            need_sub = (
                (steps.abs() > 0.12)
                | (dy_ray > 0.15 * r_sc)
                | (pc_ray[1:] != pc_ray[:-1])
                | (nr_ray[1:] != nr_ray[:-1])
                | ((vtb_ray[1:] - vtb_ray[:-1]).abs() > 0.20)
                | ((al_ray[1:] - al_ray[:-1]).abs() > 0.20)
            )
            jumps = torch.zeros_like(steps)
            if bool(need_sub.any()):
                ia, ip = torch.nonzero(need_sub, as_tuple=True)
                ta, tb = t_grid[ia], t_grid[ia + 1]
                ya, yb = Y_ray[ia, ip], Y_ray[ia + 1, ip]
                va, vb = Sn_ray[ia, ip], Sn_ray[ia + 1, ip]
                pca, pcb = pc_ray[ia, ip], pc_ray[ia + 1, ip]
                nra, nrb = nr_ray[ia, ip], nr_ray[ia + 1, ip]
                vtba, vtbb = vtb_ray[ia, ip], vtb_ray[ia + 1, ip]
                ala, alb = al_ray[ia, ip], al_ray[ia + 1, ip]
                bp = B0[ip]
                xp = Xc[ip]
                ib = ic[ip]
                corr = torch.zeros_like(va)
                orig_idx = torch.arange(ia.shape[0], device=Xb.device)
                for _ in range(38):
                    tm = 0.5 * (ta + tb)
                    t1 = 0.75 * ta + 0.25 * tb
                    t3 = 0.25 * ta + 0.75 * tb
                    pts_all = torch.cat(
                        [
                            (1.0 - tm).unsqueeze(1) * bp + tm.unsqueeze(1) * xp,
                            (1.0 - t1).unsqueeze(1) * bp + t1.unsqueeze(1) * xp,
                            (1.0 - t3).unsqueeze(1) * bp + t3.unsqueeze(1) * xp,
                        ],
                        dim=0,
                    )
                    ib_3 = torch.cat([ib, ib, ib], dim=0)
                    y_all, v_all, pc_all, nr_all, vtb_all, al_all = self.batched_local_pass(ib_3, pts_all)
                    L_cur = ta.shape[0]
                    ym, y1q, y3q = y_all[:L_cur], y_all[L_cur : 2 * L_cur], y_all[2 * L_cur :]
                    vm, v1q, v3q = v_all[:L_cur], v_all[L_cur : 2 * L_cur], v_all[2 * L_cur :]
                    pcm, pc1q, pc3q = pc_all[:L_cur], pc_all[L_cur : 2 * L_cur], pc_all[2 * L_cur :]
                    nrm_v, nr1q, nr3q = nr_all[:L_cur], nr_all[L_cur : 2 * L_cur], nr_all[2 * L_cur :]
                    vtbm, vtb1q, vtb3q = vtb_all[:L_cur], vtb_all[L_cur : 2 * L_cur], vtb_all[2 * L_cur :]
                    alm, al1q, al3q = al_all[:L_cur], al_all[L_cur : 2 * L_cur], al_all[2 * L_cur :]

                    d1, d2 = vm - va, vb - vm
                    dy1 = torch.maximum((ym - ya).norm(dim=-1), (y1q - ya).norm(dim=-1))
                    dy2 = torch.maximum((yb - ym).norm(dim=-1), (yb - y3q).norm(dim=-1))
                    dv1 = torch.maximum(d1.abs(), (v1q - va).abs())
                    dv2 = torch.maximum(d2.abs(), (vb - v3q).abs())
                    span = 0.5 * (tb - ta)
                    sm1 = (
                        (dv1 <= 0.12)
                        & (dy1 <= 0.15 * r_sc)
                        & (pcm == pca)
                        & (pc1q == pca)
                        & (nrm_v == nra)
                        & (nr1q == nra)
                        & ((vtbm - vtba).abs() <= 0.20)
                        & ((vtb1q - vtba).abs() <= 0.20)
                        & ((alm - ala).abs() <= 0.20)
                        & ((al1q - ala).abs() <= 0.20)
                    )
                    sm2 = (
                        (dv2 <= 0.12)
                        & (dy2 <= 0.15 * r_sc)
                        & (pcb == pcm)
                        & (pcb == pc3q)
                        & (nrb == nrm_v)
                        & (nrb == nr3q)
                        & ((vtbb - vtbm).abs() <= 0.20)
                        & ((vtbb - vtb3q).abs() <= 0.20)
                        & ((alb - alm).abs() <= 0.20)
                        & ((alb - al3q).abs() <= 0.20)
                    )
                    tiny = span <= 1e-11
                    dn1, dn2 = sm1 | tiny, sm2 | tiny
                    corr.index_add_(0, orig_idx[dn1], torch.where(sm1, torch.zeros_like(d1), torch.round(d1))[dn1])
                    corr.index_add_(0, orig_idx[dn2], torch.where(sm2, torch.zeros_like(d2), torch.round(d2))[dn2])
                    r1, r2 = ~dn1, ~dn2
                    if not bool(r1.any() or r2.any()):
                        ta = ta[:0]
                        break
                    ta = torch.cat([ta[r1], tm[r2]])
                    tb = torch.cat([tm[r1], tb[r2]])
                    ya = torch.cat([ya[r1], ym[r2]])
                    yb = torch.cat([ym[r1], yb[r2]])
                    va = torch.cat([va[r1], vm[r2]])
                    vb = torch.cat([vm[r1], vb[r2]])
                    pca = torch.cat([pca[r1], pcm[r2]])
                    pcb = torch.cat([pcm[r1], pcb[r2]])
                    nra = torch.cat([nra[r1], nrm_v[r2]])
                    nrb = torch.cat([nrm_v[r1], nrb[r2]])
                    vtba = torch.cat([vtba[r1], vtbm[r2]])
                    vtbb = torch.cat([vtbm[r1], vtbb[r2]])
                    ala = torch.cat([ala[r1], alm[r2]])
                    alb = torch.cat([alm[r1], alb[r2]])
                    bp = torch.cat([bp[r1], bp[r2]])
                    xp = torch.cat([xp[r1], xp[r2]])
                    ib = torch.cat([ib[r1], ib[r2]])
                    orig_idx = torch.cat([orig_idx[r1], orig_idx[r2]])
                else:
                    if ta.numel() > 0:
                        corr.index_add_(0, orig_idx, torch.round(vb - va))
                jumps[ia, ip] = corr
            tot_jump = torch.sum(jumps, dim=0)
            s0_val = Sn_ray[0]

        S_out = (Sn_end - tot_jump - s0_val) * self.scale_sq
        return Y_end, S_out

    def embed_and_action(self, i: int, Xb: torch.Tensor, fast_plateau: bool = False) -> tuple[torch.Tensor, torch.Tensor]:
        i_vec = torch.full((Xb.shape[0],), int(i), dtype=torch.int64, device=Xb.device)
        return self.batched_embed_and_action(i_vec, Xb, fast_plateau=fast_plateau)

    def batched_preimage_known_balls(self, j_vec: torch.Tensor, Z_in: torch.Tensor) -> torch.Tensor:
        """Differentiable O(1) batched preimage `f_{j}^{-1}(Z_in)` for known ball indices `j_vec`."""
        ch = self.ch
        fla = ch.target_to_flat(Z_in)[0]
        yin = fla.clone()
        wm = j_vec >= ch.ngroup
        if bool(wm.any()):
            yin[wm] = ch.C.comp1(ch.C.comp2(fla[wm], True), True)
        Ga, va, wa = yin[:, 0], yin[:, 1], yin[:, 2:]
        pa = _mom(wa)
        jfa = j_vec.to(F64)
        isga = j_vec < ch.ngroup
        Tg = 9.0 * va - (jfa - 4.0)
        Tg = Tg - 9.0 * torch.floor((Tg / 9.0).detach())
        Tw = va - ch.vcut
        Tw = Tw - torch.floor(Tw.detach())
        Xo = torch.where(isga, (Ga - ch.J(pa)) / 9.0, Ga - ch.J(pa) - jfa * (ch.P.a - pa))
        To = torch.where(isga, Tg, Tw)
        anga = torch.where(isga, 3.0 * ch.P.s * Tg / 9.0, (3.0 * ch.P.s - jfa) * Tw)
        caa, saa = torch.cos(2.0 * PI * anga), torch.sin(2.0 * PI * anga)
        wra = torch.stack((caa * wa[:, 0] - saa * wa[:, 1], saa * wa[:, 0] + caa * wa[:, 1]), dim=-1)
        zd = ch.strip.inv(torch.cat((Xo[:, None], To[:, None], wra), dim=1))
        return zd[:, [0, 2, 1, 3]] * self.scale

    def preimage_active_batched(
        self, Y_target: torch.Tensor, r_cutoff: float
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """O(1) k-independent preimage returning `(active_global_idx, ball_idx, X_diff)` across ALL balls at once."""
        ch = self.ch
        dev = Y_target.device
        empty_i = torch.empty(0, dtype=torch.int64, device=dev)
        if Y_target.shape[0] == 0:
            return empty_i, empty_i, Y_target[:0]

        r_safe = min(r_cutoff, 1.0 + 0.98 * (self.r_dom - 1.0))
        with torch.no_grad():
            Yd = Y_target.detach()
            in_b = torch.sum(Yd * Yd, dim=1) < (ch.Rs * (1.0 - 1e-11)) ** 2
            cg = torch.nonzero(in_b, as_tuple=False).squeeze(1)
            if cg.numel() == 0:
                return empty_i, empty_i, Y_target[:0]
            Ys_d = Yd[cg]
            fl_d = ch.target_to_flat(Ys_d)[0]
            Gf, vf_t, wf = fl_d[:, 0], fl_d[:, 1], fl_d[:, 2:]
            pf = _mom(wf)
            Jf = ch.J(pf)
            av = ch.P.a
            in_g = (pf < av) & (Gf > Jf) & (Gf < Jf + ch.ngroup * (av - pf))
            gj = torch.floor(torch.remainder(9.0 * vf_t + 4.0, 9.0)).to(torch.int64)

            assigned_j = torch.where(in_g, gj, torch.full_like(gj, -1))
            not_g = torch.nonzero(~in_g, as_tuple=False).squeeze(1)
            if not_g.numel() > 0 and self.k > ch.ngroup:
                yw0 = ch.C.comp1(ch.C.comp2(fl_d[not_g], True), True)
                Gw, ww = yw0[:, 0], yw0[:, 2:]
                pw = _mom(ww)
                Jw = ch.J(pw)
                wj = torch.floor((Gw - Jw) / torch.clamp(av - pw, min=1e-30)).to(torch.int64)
                in_w = (pw < av) & (wj >= ch.ngroup) & (wj < self.k)
                assigned_j[not_g[in_w]] = wj[in_w]

            cand_loc = torch.nonzero(assigned_j >= 0, as_tuple=False).squeeze(1)
            if cand_loc.numel() == 0:
                return empty_i, empty_i, Y_target[:0]
            cand_glob = cg[cand_loc]
            j_cand = assigned_j[cand_loc]

        # Single differentiable preimage pass; filter by `|X| < r_safe` + round-trip without duplicating `target_to_flat`!
        X_cand = self.batched_preimage_known_balls(j_cand, Y_target[cand_glob])
        with torch.no_grad():
            Xd = X_cand.detach()
            ok = torch.isfinite(Xd).all(dim=1) & (torch.linalg.norm(Xd, dim=1) < r_safe)
            if not bool(ok.any()):
                return empty_i, empty_i, Y_target[:0]
            sub_ok = torch.nonzero(ok, as_tuple=False).squeeze(1)
            ychk_s, _, _, _, _, _ = self.batched_local_pass(j_cand[sub_ok], Xd[sub_ok])
            rt_ok = torch.isfinite(ychk_s).all(dim=1) & (
                torch.linalg.norm(ychk_s - Y_target.detach()[cand_glob[sub_ok]], dim=1) < 1e-3
            )
            if not bool(rt_ok.any()):
                return empty_i, empty_i, Y_target[:0]
            keep = sub_ok[rt_ok]

        return cand_glob[keep], j_cand[keep], X_cand[keep]

    def preimage_all_balls_differentiable(
        self, Y_target: torch.Tensor, r_cutoff: float
    ) -> list[tuple[torch.Tensor, torch.Tensor]]:
        dev = Y_target.device
        empty_idx = torch.empty(0, dtype=torch.int64, device=dev)
        act_glob, j_act, X_diff = self.preimage_active_batched(Y_target, r_cutoff)
        if act_glob.numel() == 0:
            return [(empty_idx, Y_target[:0]) for _ in range(self.k)]
        out = []
        for j in range(self.k):
            mj = j_act == j
            if bool(mj.any()):
                out.append((act_glob[mj], X_diff[mj]))
            else:
                out.append((empty_idx, Y_target[:0]))
        return out
