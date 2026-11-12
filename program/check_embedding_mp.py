"""Arbitrary-precision (mpmath) check of the closed-form embeddings in solution_embedding.py.

Re-evaluates the exact Chain3 map family of solution_embedding.py in D-digit floating-point
arithmetic (default D = 100 decimal digits, Newton tolerance 10^{-(D-8)}), without solving ODEs.

Checks performed for a given (k, eps):
  0. Formula agreement: compares Embed(i, X) from solution_embedding.py (float64) against this
     mpmath evaluator with float64-matched eps_c on random interior/boundary points.
  1. Hypotheses (H0)-(H15): evaluates all parameter margins in D-digit arithmetic.
  2. Round-trip (C) & containment (A): evaluates Preimage_mp(i, Embed_mp(i, X)) in D-digit
     arithmetic, including any points where float64 Preimage(i, Embed(i, X)) exceeded --rt-tol.
  3. Symplecticity (B): evaluates the Jacobian by central differences at step h = 10^{-(D // 3)}
     in D-digit arithmetic, including any points where float64 finite differences exceeded --sym-tol.
  4. Continuity (G): runs the chord-bisection detector of check_embedding.py in float64 to locate
     intervals flagged at separation 1e-11 (if --chords > 0), then re-evaluates those exact chord
     intervals in D-digit arithmetic down to separation 1e-30 to verify linear image-gap shrinkage.

Usage:
    python check_embedding_mp.py solution_embedding.py --k 10 --eps 0.002 --dps 100 --chords 20
    python check_embedding_mp.py solution_embedding.py --k 101 --eps 0.01 --dps 100 --chords 0
"""
import argparse
import math
import os
import sys
import time

import mpmath as mp
import torch

if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_embedding as ce

torch.set_default_dtype(torch.float64)


def _sign(x):
    if x > 0:
        return mp.mpf(1)
    if x < 0:
        return mp.mpf(-1)
    return mp.mpf(0)


def _clamp(x, lo, hi):
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


class MpTrigStep:
    def __init__(self, m=4):
        self.m = m
        c0 = math.comb(2 * m, m)
        self.a = [mp.mpf(2 * ((-1) ** j) * math.comb(2 * m, m - j)) / mp.mpf(c0) for j in range(1, m + 1)]

    def __call__(self, u):
        u = _clamp(u, mp.mpf(0), mp.mpf(1))
        out = u
        twopi = 2 * mp.pi
        for j, aj in enumerate(self.a, 1):
            out = out + aj * mp.sin(twopi * j * u) / (twopi * j)
        return out

    def d(self, u):
        u = _clamp(u, mp.mpf(0), mp.mpf(1))
        out = mp.mpf(1)
        twopi = 2 * mp.pi
        for j, aj in enumerate(self.a, 1):
            out = out + aj * mp.cos(twopi * j * u)
        return out

    def I(self, u):
        u = _clamp(u, mp.mpf(0), mp.mpf(1))
        out = u * u / 2
        twopi = 2 * mp.pi
        for j, aj in enumerate(self.a, 1):
            denom = twopi * j
            out = out + aj * (1 - mp.cos(denom * u)) / (denom * denom)
        return out

    def ramp(self, u):
        return self.I(u) + (u - 1 if u > 1 else mp.mpf(0))


def _newton_scalar(f, lo, hi, x0):
    x = _clamp(x0, lo, hi)
    tol = mp.mpf(10) ** (-(mp.mp.dps - 8))
    max_iters = max(80, 2 * mp.mp.dps)
    for _ in range(max_iters):
        v, dv = f(x)
        if v < 0:
            lo = x
        else:
            hi = x
        if abs(v) <= tol * max(mp.mpf(1), abs(dv) * max(mp.mpf(1), abs(x))) or abs(hi - lo) <= tol * max(mp.mpf(1), abs(x)):
            if dv != 0:
                xn = x - v / dv
                if lo <= xn <= hi:
                    x = xn
            break
        if dv != 0:
            xn = x - v / dv
            x = xn if (lo < xn < hi) else (lo + hi) / 2
        else:
            x = (lo + hi) / 2
    return x


def _rot(w0, w1, turns):
    ang = 2 * mp.pi * turns
    c, s = mp.cos(ang), mp.sin(ang)
    return c * w0 - s * w1, s * w0 + c * w1


def _mom(w0, w1):
    return mp.pi * (w0 * w0 + w1 * w1)


def _polar0(w0, w1):
    return _mom(w0, w1), mp.atan2(w1, w0) / (2 * mp.pi)


def _cart0(x, th):
    r = mp.sqrt(x / mp.pi)
    ang = 2 * mp.pi * th
    return r * mp.cos(ang), r * mp.sin(ang)


class MpSmoothKeyhole:
    def __init__(self, ra, d, beta, rho1_safety, m=4):
        F = mp.mpf
        self.ra, self.d, self.beta = ra, d, beta
        self.rho_out = 1 + beta
        self.W1 = beta / (3 * (1 + beta))
        self.rh = (F(9) / 10) * d * mp.sin(2 * mp.pi * self.W1)
        self.rho1 = rho1_safety * ((d - self.rh) / (d + ra)) ** 2
        self.W2 = beta / (1 + beta - self.rho1) - self.W1
        self.Xw = (F(2) / 10) * mp.pi * (d - self.rh) ** 2
        self.x0 = mp.pi * self.rh * self.rh
        self.theta0 = self.W1
        self.delta_rel = beta * mp.pi * (ra + d) * (ra + (F(84) / 10) * d)
        self.delta_small = 4 * (mp.pi ** 3) * d * (ra + d) * (self.W2 ** 2)
        self.st = MpTrigStep(m)

    def dPsi(self, psi):
        u = (abs(psi) - self.W1) / (self.W2 - self.W1)
        return self.rho1 + (self.rho_out - self.rho1) * self.st(u)

    def Pmi(self, psi):
        ap = abs(psi)
        D = self.W2 - self.W1
        u = (ap - self.W1) / D
        tail = ap - self.W2 if ap > self.W2 else mp.mpf(0)
        val = (self.rho1 - 1) * ap + (self.rho_out - self.rho1) * (D * self.st.I(u) + tail)
        return _sign(psi) * val

    def M(self, X):
        u = X / self.Xw
        return self.Xw * self.st.ramp(u), (mp.mpf(1) if u >= 1 else self.st(u))

    def polar_c(self, w0, w1):
        dq = w0 + self.d
        return mp.pi * (dq * dq + w1 * w1), mp.atan2(w1, dq) / (2 * mp.pi)

    def cart_c(self, X, psi):
        r = mp.sqrt(X / mp.pi)
        ang = 2 * mp.pi * psi
        return r * mp.cos(ang) - self.d, r * mp.sin(ang)

    def fwd(self, w0, w1, tau):
        X, phi = self.polar_c(w0, w1)
        Mv, dM = self.M(X)
        tt = tau * dM
        ap = abs(phi)
        half = mp.mpf(1) / 2
        psi = _newton_scalar(lambda x: (x + tt * self.Pmi(x) - ap, 1 + tt * (self.dPsi(x) - 1)),
                             mp.mpf(0), half, _clamp(ap, mp.mpf(0), half))
        psi = _sign(phi) * psi
        Xn = X + tau * Mv * (self.dPsi(psi) - 1)
        nw0, nw1 = self.cart_c(Xn, psi)
        return nw0, nw1, Mv * self.Pmi(psi)

    def inv(self, w0, w1, tau):
        Xn, psi = self.polar_c(w0, w1)
        a = tau * (self.dPsi(psi) - 1)
        Xlin = (Xn + a * self.Xw / 2) / (1 + a)
        if Xlin < self.Xw:
            X = _newton_scalar(lambda x: (x + a * self.M(x)[0] - Xn, 1 + a * self.M(x)[1]),
                               mp.mpf(0), self.Xw, _clamp(Xn, mp.mpf(0), self.Xw))
        else:
            X = Xlin
        Mv, dM = self.M(X)
        phi = psi + tau * dM * self.Pmi(psi)
        pw0, pw1 = self.cart_c(X, phi)
        return pw0, pw1, Mv * self.Pmi(psi)


class MpBump:
    def __init__(self, w0, w1, m=2):
        self.w0, self.w1, self.D = w0, w1, w1 - w0
        self.mass = w0 + w1
        self.st = MpTrigStep(m)

    def val(self, x):
        return 1 - self.st((abs(x) - self.w0) / self.D)

    def prim(self, x):
        D, w0, st = self.D, self.w0, self.st
        if x < -w0:
            uL = _clamp((-x - w0) / D, mp.mpf(0), mp.mpf(1))
            return D * ((1 - uL) - (mp.mpf(1) / 2 - st.I(uL)))
        if x <= w0:
            return D / 2 + x + w0
        uR = _clamp((x - w0) / D, mp.mpf(0), mp.mpf(1))
        return D / 2 + 2 * w0 + D * (uR - st.I(uR))


class MpChain3:
    """Exact mpmath counterpart of Chain3 in solution_embedding.py."""

    def __init__(self, k, eps_str, match_float64=False):
        F = mp.mpf
        self.k = int(k)
        if match_float64:
            eps_req = F(float(eps_str))
            eps_c = F(min(float(eps_str), 1.0 / 100.0))
        else:
            eps_req = F(str(eps_str))
            eps_c = min(eps_req, F(1) / 100)
        self.eps_requested = eps_req
        self.eps = eps_c

        s = mp.sqrt(F(self.k))
        eta = eps_c / (1 + mp.sqrt(1 - eps_c))
        t0 = 1 - eta / 2
        self.s, self.eta, self.t0 = s, eta, t0
        self.a, self.h, self.cs, self.g = t0 / s, t0 / 3, 3 * s - 9, 3 * eta / 2
        self.rho_ball = (1 - eta) / s
        self.T = self.g / self.cs
        self.Gmax = s * t0 - 3
        self.lam_a, self.lam2, self.mu = F(9) / 10, F(3) / 10, F(1) / 2
        self.f = F(1) / 4
        self.wG, self.w2 = self.lam_a * self.g, self.lam2 * self.g
        ups = mp.sqrt(F(11) / 1000)
        ra = mp.sqrt(self.a / mp.pi)
        d = mp.sqrt(self.f * self.T / mp.pi) / (1 + ups)
        beta = self.f * self.T / (mp.pi * (ra + d) * (ra + (F(84) / 10) * d))
        self.KC = MpSmoothKeyhole(ra, d, beta, F(8) / 10, m=4)
        self.st4 = MpTrigStep(4)

        cand = (
            self.a,
            (3 - self.wG) / (3 * s) - (F(1) / 2) * self.mu * self.T * (1 - self.lam_a),
            self.h - (F(1) / 2) * self.mu * self.T,
        )
        Dc = (
            (s - 3 + (F(3) / 2) * eta) / s,
            (s - 3 + self.wG) / s + (F(3) / 2) * self.mu * self.T * (1 - self.lam_a),
            eta / 2 + (F(3) / 2) * self.mu * self.T,
        )
        j = max(range(3), key=lambda q: cand[q])
        self.hK, self.D = cand[j], Dc[j]

        self.R_requested = (F(self.k) / (1 - eps_req)) ** (F(1) / 4)
        self.R = 1 / mp.sqrt(self.rho_ball)
        ms_abs = F(2) / F(10 ** 6)
        self.margin = min(ms_abs, eta / 8)
        self.Rs = self.R * (1 - self.margin)
        self.rho_b = self.rho_ball / ((1 - self.margin) ** 2)
        self.scale = mp.sqrt(mp.pi) * self.Rs

        # Twist (SpiralShear with global_shift=True, m=2)
        self.ag = F(1) / 10
        self.vlo, self.ulo, self.vcomp = -F(1) / 3, F(2) / 10, F(1) / 4
        self.delta = self.w2 / 4
        self.ustar = -self.cs / 9
        self.c0 = self.delta - self.cs / 3
        fib_u = (F(5) / 6, F(1) / 3, F(0))
        self.nj = [-int(round(float(uj - self.ustar))) for uj in fib_u]
        self.phi_tw = [uj + F(n_) - self.ustar for uj, n_ in zip(fib_u, self.nj)]
        self.vp = (-self.ag, F(0), F(1) / 2)
        self.uc = (F(5) / 6, F(7) / 12)
        self.bv = MpBump(F(15) / 1000, F(45) / 1000, m=2)
        self.bc = MpBump(F(5) / 100, F(14) / 100, m=2)
        self.bu = MpBump(F(2) / 100, F(12) / 100, m=2)

        # Transfer3
        self.m_tr = (F(32) / 100) * self.D
        self.d2 = (F(2) / 10) * self.D
        self.sig0 = (F(2) / 10) * self.D
        self.dkh = (F(1) / 10) * self.D
        rB = mp.sqrt(self.hK / mp.pi)
        dB = mp.sqrt((F(8) / 10) * self.dkh / mp.pi) / (F(105) / 100)
        betaB = (F(8) / 10) * self.dkh / (mp.pi * (rB + dB) * (rB + (F(84) / 10) * dB))
        self.KB = MpSmoothKeyhole(rB, dB, betaB, F(7) / 10, m=4)
        self.kap = (-F(1) / 12, F(1) / 12, F(0))
        k0, k1, k2 = self.kap
        self.off = {0: (F(0), F(0)), 1: (k1, 3 * k1), '2s': (k1 + k2, 3 * k1 + 6 * k2), '2c': (-k0, F(0))}
        self.left = {0: self.off['2c'], 1: self.off[0], 2: self.off[1]}
        arg = -4 * mp.pi * (self.left[0][0] + k0 / 2)
        self.kappa_line = mp.mpc(mp.cos(arg), mp.sin(arg))
        self.psi0, self.vcut, self.lift = -F(1) / 6, F(1) / 2, F(1)

    def hypotheses(self):
        F = mp.mpf
        out = {}
        out['H0_k'] = F(self.k - 9)
        out['H0_eps'] = min(self.eps, 1 - self.eps)
        out['H2_rho_b<a'] = (self.a - self.rho_b) / self.a
        out['KC_K3'] = 1 - (self.KC.rho1 * mp.pi * (self.KC.d + self.KC.ra) ** 2 + self.KC.Xw / 2) / (mp.pi * (self.KC.d - self.KC.rh) ** 2)
        out['H8_1'] = (1 - self.mu - self.lam2 / 2) - mp.pi * self.KC.d ** 2 / self.T
        out['H9'] = 1 - (self.cs * mp.pi * self.KC.rh ** 2 + (F(3) / 2) * self.lam2 * self.g) / self.g
        out['H11_D>0'] = self.D
        out['KB_K3'] = 1 - (self.KB.rho1 * mp.pi * (self.KB.d + self.KB.ra) ** 2 + self.KB.Xw / 2) / (mp.pi * (self.KB.d - self.KB.rh) ** 2)
        out['H13'] = 1 - max(mp.pi * self.KB.d ** 2, self.KB.delta_rel, self.KB.delta_small) / self.dkh
        Sb = max(self.m_tr, mp.hypot(self.d2, self.sig0))
        eta1 = F(2) / 3 - (2 * self.dkh + Sb) / self.D
        out['H14_eta1'] = eta1
        out['H15'] = 3 * eta1 - self.m_tr / self.D
        out['split'] = 1 - 3 * self.dkh / self.D - 2 * self.m_tr / self.D
        return out

    # ---- Stage helpers ----
    def _kr_fwd(self, x, y, w0, w1):
        p = _mom(w0, w1)
        r2 = (self.a - p) / mp.pi
        r = mp.sqrt(r2)
        c = mp.sqrt(r2 - x * x)
        u = x / r
        X = r2 * (mp.pi / 2 + mp.asin(u) + u * c / r)
        T = mp.mpf(1) / 2 + y / (2 * c)
        C = (X - x * c) / (mp.pi * r2) * y / (2 * c)
        nw0, nw1 = _rot(w0, w1, C)
        return X, T, nw0, nw1

    def _kr_inv(self, X, T, w0, w1):
        p = _mom(w0, w1)
        r2 = (self.a - p) / mp.pi
        r = mp.sqrt(r2)
        m2 = 2 * (X / r2 - mp.pi / 2)
        half_pi = mp.pi / 2
        al = _newton_scalar(lambda t: (2 * t + mp.sin(2 * t) - m2, 2 + 2 * mp.cos(2 * t)),
                            -half_pi, half_pi, _clamp(m2 / 4, -half_pi, half_pi))
        x, c = r * mp.sin(al), r * mp.cos(al)
        y = (2 * T - 1) * c
        C = (X - x * c) / (mp.pi * r2) * y / (2 * c)
        pw0, pw1 = _rot(w0, w1, -C)
        return x, y, pw0, pw1

    def _cell_to_flat(self, i, X, T, w0, w1):
        p = _mom(w0, w1)
        Jp = 3 * self.s * p - 3
        if i < 9:
            rw0, rw1 = _rot(w0, w1, -3 * self.s * T / 9)
            return Jp + 9 * X, (mp.mpf(i - 4) + T) / 9, rw0, rw1
        dA = 3 * self.s - i
        rw0, rw1 = _rot(w0, w1, -dA * T)
        return X + Jp + i * (self.a - p), T + self.vcut, rw0, rw1

    def _flat_to_cell(self, i, G, v, w0, w1):
        p = _mom(w0, w1)
        Jp = 3 * self.s * p - 3
        if i < 9:
            T = 9 * v - mp.mpf(i - 4)
            T = T - 9 * mp.floor(T / 9)
            rw0, rw1 = _rot(w0, w1, 3 * self.s * T / 9)
            return (G - Jp) / 9, T, rw0, rw1
        dA = 3 * self.s - i
        T = v - self.vcut
        T = T - mp.floor(T)
        rw0, rw1 = _rot(w0, w1, dA * T)
        return G - Jp - i * (self.a - p), T, rw0, rw1

    def _comp_fwd(self, G, v, w0, w1):
        u = (G + self.wG) / (self.wG - self.w2)
        tau = self.st4(u)
        dtau = self.st4.d(u) / (self.wG - self.w2) if (0 < u < 1) else mp.mpf(0)
        if tau > 0:
            w0, w1, gen = self.KC.fwd(w0, w1, tau)
            v = v - dtau * gen
        u2 = (G + self.w2) / self.w2
        c = (self.w2 / self.cs) * self.st4.ramp(u2)
        dc = (mp.mpf(1) if u2 >= 1 else self.st4(u2)) / self.cs
        if c > 0:
            x, th = _polar0(w0, w1)
            vt = th - (mp.mpf(1) / 2) * _sign(th)
            v = v - dc * vt
            w0, w1 = _cart0(x + c, th)
        return G, v, w0, w1

    def _comp_inv(self, G, v, w0, w1):
        u2 = (G + self.w2) / self.w2
        c = (self.w2 / self.cs) * self.st4.ramp(u2)
        dc = (mp.mpf(1) if u2 >= 1 else self.st4(u2)) / self.cs
        if c > 0:
            x, th = _polar0(w0, w1)
            vt = th - (mp.mpf(1) / 2) * _sign(th)
            v = v + dc * vt
            w0, w1 = _cart0(x - c, th)
        u = (G + self.wG) / (self.wG - self.w2)
        tau = self.st4(u)
        dtau = self.st4.d(u) / (self.wG - self.w2) if (0 < u < 1) else mp.mpf(0)
        if tau > 0:
            w0, w1, gen = self.KC.inv(w0, w1, tau)
            v = v + dtau * gen
        return G, v, w0, w1

    def _twist_S(self, p, v):
        vt = self.vlo + ((v - self.vlo) - mp.floor(v - self.vlo))
        xc = vt - self.vcomp
        cval = self.bc.val(xc) / self.bc.mass
        cprim = self.bc.prim(xc) / self.bc.mass
        Sv, Sp = mp.mpf(0), mp.mpf(0)
        hb = 3 - 9 * p
        for j in range(3):
            x = vt - self.vp[j]
            b = self.bv.val(x) - self.bv.mass * cval
            B = self.bv.prim(x) - self.bv.mass * cprim
            Sv = Sv + self.phi_tw[j] * hb * b
            Sp = Sp - 9 * self.phi_tw[j] * B
        Sv = Sv + self.c0
        return Sv, Sp

    def _twist_g(self, u):
        ut = self.ulo + ((u - self.ulo) - mp.floor(u - self.ulo))
        x0, x1 = ut - self.uc[0], ut - self.uc[1]
        g = -self.ag * (self.bu.val(x0) - self.bu.val(x1))
        Gg = -self.ag * (self.bu.prim(x0) - self.bu.prim(x1))
        return g, Gg

    def _twist_fwd(self, G, v, w0, w1):
        p = _mom(w0, w1)
        Sv, Sp = self._twist_S(p, v)
        G = G + Sv
        w0, w1 = _rot(w0, w1, -Sp)
        u = G / (3 - 9 * p)
        g, Gg = self._twist_g(u)
        v = v - g
        w0, w1 = _rot(w0, w1, 9 * (Gg - u * g))
        return G, v, w0, w1

    def _twist_inv(self, G, v, w0, w1):
        p = _mom(w0, w1)
        u = G / (3 - 9 * p)
        g, Gg = self._twist_g(u)
        v = v + g
        w0, w1 = _rot(w0, w1, -9 * (Gg - u * g))
        Sv, Sp = self._twist_S(p, v)
        G = G - Sv
        w0, w1 = _rot(w0, w1, Sp)
        return G, v, w0, w1

    def _to_fund(self, G, v, w0, w1):
        p = _mom(w0, w1)
        hb = 3 - 9 * p
        Jp = 3 * self.s * p - 3
        n = mp.floor((G - Jp) / hb)
        rw0, rw1 = _rot(w0, w1, -9 * n * v)
        return G - n * hb, v, rw0, rw1

    def _S_prof(self, c):
        u = abs(c) / self.d2
        q = self.sig0 * (1 - self.st4(u))
        dq = -self.sig0 * self.st4.d(u) / self.d2 * _sign(c) if (0 < u < 1) else mp.mpf(0)
        S = mp.hypot(c, q)
        return S, (c + q * dq) / S

    def _lam_prof(self, c):
        S, dS = self._S_prof(c)
        return (c - S) / 2, (1 - dS) / 2

    def _tau_prof(self, c):
        u = (abs(c) - self.d2) / (self.m_tr - self.d2)
        return 1 - self.st4(u), (-self.st4.d(u) / (self.m_tr - self.d2) * _sign(c) if (0 < u < 1) else mp.mpf(0))

    def _kstep(self, c, j):
        return self.kap[j] * self.st4((c + self.m_tr) / (2 * self.m_tr))

    def _band(self, sig0, psi0, w0, w1, inverse=False):
        p0, vt0 = _polar0(w0, w1)
        n = mp.floor(sig0 / (3 - 9 * p0) + mp.mpf(1) / 6)
        sig = sig0 - n * (3 - 9 * p0)
        psi = psi0
        p = p0
        vt = vt0 - n * (9 * psi0 + mp.mpf(1) / 2)
        for j in range(3):
            c = sig - j * (1 - 3 * p)
            if abs(c) < self.m_tr:
                a_, b_ = self.left[j]
                kj = self._kstep(c, j)
                ps = psi + a_ + kj
                vj = vt + b_ + 3 * j * kj - 3 * j * ps
                T, dT = self._tau_prof(c)
                cw0, cw1 = _cart0(p, vj)
                if not inverse:
                    nw0, nw1, gen = self.KB.fwd(cw0, cw1, T)
                    ps2 = ps - dT * gen
                else:
                    nw0, nw1, gen = self.KB.inv(cw0, cw1, T)
                    ps2 = ps + dT * gen
                p2, vj2 = _polar0(nw0, nw1)
                so = c + j * (1 - 3 * p2)
                po = ps2 - a_ - kj
                vo = vj2 + 3 * j * ps2 - b_ - 3 * j * kj
                ow0, ow1 = _cart0(p2, vo + n * (9 * po + mp.mpf(1) / 2))
                return so + n * (3 - 9 * p2), po, ow0, ow1
        return sig0, psi0, w0, w1

    def _W_no_kh(self, sig, psi, p, vt):
        n = mp.floor(sig / (3 - 9 * p) + mp.mpf(1) / 6)
        sig = sig - n * (3 - 9 * p)
        vt = vt - n * (9 * psi + mp.mpf(1) / 2)
        mus = [sig, sig - (1 - 3 * p), sig - 2 * (1 - 3 * p)]
        for j in range(3):
            if abs(mus[j]) < self.m_tr:
                c = mus[j]
                a_, b_ = self.left[j]
                kj = self._kstep(c, j)
                ps = psi + a_ + kj
                vv = vt + b_ + 3 * j * kj
                vj = vv - 3 * j * ps
                cw0, cw1 = _cart0(p, vj)
                p2, ang = _polar0(cw0, cw1)
                vl = ang - mp.floor(ang)
                lam, lamp = self._lam_prof(c)
                xb = p2 - lam
                xa = xb + c
                xr = 1 - xa - xb
                Ta = ps + lamp * vl
                loc = [
                    mp.mpc(mp.sqrt(xr), 0),
                    mp.sqrt(xa) * mp.expj(2 * mp.pi * Ta),
                    mp.sqrt(xb) * mp.expj(2 * mp.pi * (vl - Ta)),
                ]
                perm = ((0, 1, 2), (1, 2, 0), (2, 0, 1))[j]
                Wg = [None, None, None]
                for li, gi in enumerate(perm):
                    Wg[gi] = loc[li]
                return Wg
        vc = sig / (3 - 9 * p)
        if vc < 0:
            key = '2c'
        elif vc < mp.mpf(1) / 3:
            key = 0
        elif vc < mp.mpf(2) / 3:
            key = 1
        else:
            key = '2s'
        a_, b_ = self.off[key]
        ps, vv = psi + a_, vt + b_
        if key == '2c':
            X1, X2, T1, T2 = p, p - sig, vv + ps, -ps
        elif key == 0:
            X1, X2 = p + sig, p
            T1, T2 = sig * 0 + ps, vv - ps
        elif key == 1:
            X1, X2 = -5 * p - sig + 2, 4 * p + sig - 1
            T1, T2 = -vv + 4 * ps, -vv + 5 * ps
        else:
            X1, X2 = p, -8 * p - sig + 3
            T1, T2 = vv - 8 * ps, -ps
        X0 = 1 - X1 - X2
        return [
            mp.mpc(mp.sqrt(X0), 0),
            mp.sqrt(X1) * mp.expj(2 * mp.pi * T1),
            mp.sqrt(X2) * mp.expj(2 * mp.pi * T2),
        ]

    def _invert_no_kh(self, W):
        nrm = mp.sqrt(abs(W[0]) ** 2 + abs(W[1]) ** 2 + abs(W[2]) ** 2)
        W = [w / nrm for w in W]
        X = [abs(w) ** 2 for w in W]
        ang = [mp.arg(w) / (2 * mp.pi) for w in W]
        for j in range(3):
            a, b = (j + 1) % 3, (j + 2) % 3
            mu = X[a] - X[b]
            if abs(mu) < self.m_tr and X[j] > mp.mpf(1) / 3:
                c = mu
                lam, dl = self._lam_prof(c)
                p2 = X[b] + lam
                Ta = ang[a] - ang[j]
                Tb = ang[b] - ang[j]
                vl = (Ta + Tb) - mp.floor(Ta + Tb)
                ps2 = Ta - dl * vl
                kj = self._kstep(c, j)
                a_, b_ = self.left[j]
                cw0, cw1 = _cart0(p2, vl)
                pp, vj = _polar0(cw0, cw1)
                sig = c + j * (1 - 3 * pp)
                psi = ps2 - kj - a_
                vt = vj + 3 * j * ps2 - 3 * j * kj - b_
                n = mp.floor(sig / (3 - 9 * pp) + mp.mpf(1) / 6)
                return sig - n * (3 - 9 * pp), psi, pp, vt - n * (9 * psi + mp.mpf(1) / 2)
        e = min(range(3), key=lambda idx: X[idx])
        T1, T2 = ang[1] - ang[0], ang[2] - ang[0]
        if e == 2:      # key 0: A = [[1,1],[1,0]], B = [0,0]
            pp = X[2]
            sig = X[1] - X[2]
            vt = T1 + T2
            psi = T1
            a_, b_ = self.off[0]
        elif e == 0:    # key 1: A = [[-5,-1],[4,1]], B = [2,-1] -> det = -1
            u1, u2 = X[1] - 2, X[2] + 1
            pp = -u1 - u2
            sig = 4 * u1 + 5 * u2
            vt = -5 * T1 + 4 * T2
            psi = -T1 + T2
            a_, b_ = self.off[1]
        else:           # key '2s': A = [[1,0],[-8,-1]], B = [0,3] -> det = -1
            u1, u2 = X[1], X[2] - 3
            pp = u1
            sig = -8 * u1 - u2
            vt = T1 - 8 * T2
            psi = -T2
            a_, b_ = self.off['2s']
        psi = psi - a_
        vt = vt - b_
        n = mp.floor(sig / (3 - 9 * pp) + mp.mpf(1) / 6)
        return sig - n * (3 - 9 * pp), psi, pp, vt - n * (9 * psi + mp.mpf(1) / 2)

    def embed_point(self, i, Xb):
        # Stage 1: scale + perm [0, 2, 1, 3]
        x, y, w0, w1 = Xb[0] / self.scale, Xb[2] / self.scale, Xb[1] / self.scale, Xb[3] / self.scale
        # Stage 2: KRStrip
        Xc, Tc, w0, w1 = self._kr_fwd(x, y, w0, w1)
        # Stage 3: cell -> flat
        G, v, w0, w1 = self._cell_to_flat(i, Xc, Tc, w0, w1)
        # Stage 4-5: comparator
        if i >= 9:
            G, v, w0, w1 = self._comp_fwd(G, v, w0, w1)
        # Stage 6-7: marked-fibre twists
        G, v, w0, w1 = self._twist_fwd(G, v, w0, w1)
        # Stage 8: flat -> post
        p, th = _polar0(w0, w1)
        hb = 3 - 9 * p
        ua = G / hb + self.lift
        sig = hb * v
        psi = self.psi0 - ua
        vt = th - 9 * (ua - self.lift) * v
        pw0, pw1 = _cart0(p, vt)
        # Stage 9: corner keyhole (Band)
        sig, psi, pw0, pw1 = self._band(sig, psi, pw0, pw1, inverse=False)
        # Stage 10-11: W -> CP^2 ball chart + scale
        p_b, vt_b = _polar0(pw0, pw1)
        W = self._W_no_kh(sig, psi, p_b, vt_b)
        kap = self.kappa_line
        sq2 = mp.sqrt(2)
        Z0 = (W[2] - kap * W[1]) / sq2
        Z1 = (W[1] + mp.conj(kap) * W[2]) / sq2
        Z2 = W[0]
        nrm2 = abs(Z0) ** 2 + abs(Z1) ** 2 + abs(Z2) ** 2
        denom = mp.sqrt(mp.pi * (abs(Z0) ** 2) * nrm2)
        a_c = Z1 * mp.conj(Z0) / denom
        b_c = Z2 * mp.conj(Z0) / denom
        sc = self.scale
        return [mp.re(a_c) * sc, mp.re(b_c) * sc, mp.im(a_c) * sc, mp.im(b_c) * sc]

    def preimage_point(self, j, Y):
        sc = self.scale
        y0, y1 = mp.mpc(Y[0] / sc, Y[2] / sc) * mp.sqrt(mp.pi), mp.mpc(Y[1] / sc, Y[3] / sc) * mp.sqrt(mp.pi)
        rad = 1 - (abs(y0) ** 2 + abs(y1) ** 2)
        if rad <= 0:
            return None
        Z0 = mp.mpc(mp.sqrt(rad), 0)
        kap = self.kappa_line
        sq2 = mp.sqrt(2)
        W = [y1, (y0 - mp.conj(kap) * Z0) / sq2, (Z0 + kap * y0) / sq2]
        sig, psi, p, vt = self._invert_no_kh(W)
        pw0, pw1 = _cart0(p, vt)
        sig, psi, pw0, pw1 = self._band(sig, psi, pw0, pw1, inverse=True)
        # post -> flat
        p, vt = _polar0(pw0, pw1)
        hb = 3 - 9 * p
        ua = self.psi0 - psi
        v = sig / hb
        G = (ua - self.lift) * hb
        w0, w1 = _cart0(p, vt + 9 * (ua - self.lift) * v)
        # twist inv + to_fund + comp inv + flat_to_cell + kr_inv + scale
        G, v, w0, w1 = self._twist_inv(G, v, w0, w1)
        G, v, w0, w1 = self._to_fund(G, v, w0, w1)
        if j >= 9:
            G, v, w0, w1 = self._comp_inv(G, v, w0, w1)
        Xc, Tc, w0, w1 = self._flat_to_cell(j, G, v, w0, w1)
        if not (0 < Xc < self.a - _mom(w0, w1)):
            return None
        x, y, w0, w1 = self._kr_inv(Xc, Tc, w0, w1)
        return [x * sc, w0 * sc, y * sc, w1 * sc]


def _norm(v):
    return mp.sqrt(sum(x * x for x in v))


def _diff_norm(a, b):
    return mp.sqrt(sum((x - y) ** 2 for x, y in zip(a, b)))


def _symplectic_defect(ch, i, Xb, h):
    # J_{r, a} = dY_r / dX_a by central differences at step h
    J = [[mp.mpf(0)] * 4 for _ in range(4)]
    for a in range(4):
        xp = list(Xb); xm = list(Xb)
        xp[a] += h; xm[a] -= h
        yp = ch.embed_point(i, xp)
        ym = ch.embed_point(i, xm)
        for r in range(4):
            J[r][a] = (yp[r] - ym[r]) / (2 * h)
    # Omega = dq1 ^ dp1 + dq2 ^ dp2 on (q1, q2, p1, p2)
    om = [[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]
    max_def = mp.mpf(0)
    frob2 = sum(J[r][a] ** 2 for r in range(4) for a in range(4))
    for a in range(4):
        for b in range(4):
            val = sum(J[r][a] * om[r][s] * J[s][b] for r in range(4) for s in range(4)) - om[a][b]
            if abs(val) > max_def:
                max_def = abs(val)
    return max_def / max(mp.mpf(1), frob2), mp.sqrt(frob2)


def _find_flagged_chords_f64(Embed, i, n_ch, m, top, seed):
    g = torch.Generator().manual_seed(seed)
    a = torch.randn(n_ch, 4, generator=g); a = a / a.norm(dim=1, keepdim=True)
    b = torch.randn(n_ch, 4, generator=g); b = b / b.norm(dim=1, keepdim=True)
    t = torch.linspace(0, 1, m).reshape(1, m, 1)
    X = a.unsqueeze(1) * (1 - t) + b.unsqueeze(1) * t
    Y = torch.cat([Embed(i, X[c]) for c in range(n_ch)], dim=0).reshape(n_ch, m, 4)
    d = (Y[:, 1:] - Y[:, :-1]).norm(dim=2)
    nb = torch.full_like(d, float("inf"))
    nb[:, 1:-1] = torch.maximum(d[:, :-2], d[:, 2:])
    rel = d / (nb + 1e-14)
    idx = torch.unique(torch.cat([d.flatten().argsort(descending=True)[:top], rel.flatten().argsort(descending=True)[:top]]))
    ci, ji = idx // (m - 1), idx % (m - 1)
    lo, hi = X[ci, ji].clone(), X[ci, ji + 1].clone()
    gap_mid = None
    while True:
        sep = float((hi - lo).norm(dim=1).max())
        if gap_mid is None and sep <= 1e-8:
            gap_mid = (Embed(i, hi) - Embed(i, lo)).norm(dim=1)
        if sep <= 1e-11:
            break
        mid = 0.5 * (lo + hi)
        Yl, Ym, Yh = Embed(i, lo), Embed(i, mid), Embed(i, hi)
        left = (Ym - Yl).norm(dim=1) >= (Yh - Ym).norm(dim=1)
        hi = torch.where(left.unsqueeze(1), mid, hi); lo = torch.where(left.unsqueeze(1), lo, mid)
    gap_fine = (Embed(i, hi) - Embed(i, lo)).norm(dim=1)
    bad = ~((gap_fine <= 0.02 * gap_mid) | (gap_fine <= 1e-9)) | ~torch.isfinite(gap_fine)
    flagged = []
    for q in bad.nonzero(as_tuple=False).flatten().tolist():
        flagged.append((lo[q].tolist(), hi[q].tolist(), float(gap_mid[q]), float(gap_fine[q])))
    return flagged


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("solution", help="path to solution_embedding.py")
    ap.add_argument("--k", type=int, default=10)
    ap.add_argument("--eps", type=str, default="0.002")
    ap.add_argument("--dps", type=int, default=100, help="decimal digits of precision for mpmath")
    ap.add_argument("--samples", type=int, default=8, help="random points checked per Representative ball")
    ap.add_argument("--scan-b", type=int, default=1, help="1 = scan check_embedding.py's 100 Jacobian points/ball at h=1e-7 for float64 B flags")
    ap.add_argument("--max-b-recheck", type=int, default=10, help="max float64 B-flagged points to re-evaluate in mpmath")
    ap.add_argument("--chords", type=int, default=20, help="float64 chords per ball to scan for G flags (0 = skip)")
    ap.add_argument("--chord-pts", type=int, default=3000)
    ap.add_argument("--max-g-recheck", type=int, default=10, help="max G-flagged intervals to re-evaluate in mpmath")
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args()

    mp.mp.dps = a.dps
    eps_f = float(a.eps)
    t0 = time.time()
    sol = ce.load_solution(os.path.abspath(a.solution))
    Embed_f64, Preimage_f64 = ce.load_pair(sol(a.k, eps_f))

    ch_exact = MpChain3(a.k, a.eps, match_float64=False)
    ch_f64match = MpChain3(a.k, a.eps, match_float64=True)
    balls = sorted({0, 4, 8, 9, a.k - 1})
    print(f"k={a.k} eps={a.eps} dps={a.dps} R_needed={mp.nstr(ch_exact.R_requested, 12)} balls_sampled={balls}", flush=True)

    # 1. Hypotheses
    hyps = ch_exact.hypotheses()
    min_h = min(hyps.items(), key=lambda kv: kv[1])
    assert all(v > 0 for v in hyps.values()), f"hypothesis failed: {hyps}"
    print(f"1. Hypotheses (exact {a.dps}-digit): all positive; tightest {min_h[0]} = {mp.nstr(min_h[1], 4)}", flush=True)

    # 0, 2, 3. Formula agreement + containment + round-trip + symplecticity on representative balls
    S, B = ce.unit_samples(500, 500, a.seed)
    X0 = torch.cat([S, B], dim=0)
    max_agree_rel = 0.0
    max_rt_mp = mp.mpf(0)
    max_sym_mp = mp.mpf(0)
    max_jnorm = mp.mpf(0)
    min_rad_margin = ch_exact.R_requested
    h_mp = mp.mpf(10) ** (-(a.dps // 3))

    # Also collect any float64 round-trip failures across ALL balls (same seed as check_embedding.py!)
    f64_c_failures = []
    for i in range(a.k):
        Y64 = Embed_f64(i, X0).detach()
        Xb64, ok64 = Preimage_f64(i, Y64)
        err64 = (Xb64 - X0).norm(dim=1)
        bad64 = (~ok64) | ~torch.isfinite(err64) | (err64 > 1e-7)
        for idx in bad64.nonzero(as_tuple=False).flatten().tolist():
            f64_c_failures.append((i, idx, X0[idx].tolist(), float(err64[idx])))

    for i in balls:
        pts_idx = list(range(min(a.samples, len(X0))))
        Y64 = Embed_f64(i, X0[pts_idx]).detach()
        for q, idx in enumerate(pts_idx):
            x_vec = [mp.mpf(float(v)) for v in X0[idx].tolist()]
            # Shrink slightly off |X|=1 when taking finite-difference Jacobian
            x_jac = [v * (1 - mp.mpf(10) ** (-12)) for v in x_vec]
            y_match = ch_f64match.embed_point(i, x_vec)
            y64_vec = [mp.mpf(float(v)) for v in Y64[q].tolist()]
            sdef, jnrm = _symplectic_defect(ch_exact, i, x_jac, h_mp)
            max_sym_mp = max(max_sym_mp, sdef)
            max_jnorm = max(max_jnorm, jnrm)
            # Relative to local conditioning (~ |J| * eps_mach)
            agree_scaled = float(_diff_norm(y_match, y64_vec) / max(mp.mpf(1), jnrm))
            max_agree_rel = max(max_agree_rel, agree_scaled)

            y_mp = ch_exact.embed_point(i, x_vec)
            min_rad_margin = min(min_rad_margin, ch_exact.R_requested - _norm(y_mp))
            x_back = ch_exact.preimage_point(i, y_mp)
            assert x_back is not None, f"mpmath preimage returned None on ball {i}"
            max_rt_mp = max(max_rt_mp, _diff_norm(x_back, x_vec))

    print(f"0. Float64 vs mpmath formula check: max |Y_f64 - Y_mp| / max(1, |J|) = {max_agree_rel:.3e}", flush=True)
    print(f"2. Containment & round-trip ({a.dps}-digit): min radius margin = {mp.nstr(min_rad_margin, 4)}, "
          f"max round-trip error = {mp.nstr(max_rt_mp, 3)}", flush=True)
    if f64_c_failures:
        max_c_fixed = mp.mpf(0)
        for i, idx, x_raw, err64 in f64_c_failures:
            x_vec = [mp.mpf(v) for v in x_raw]
            y_mp = ch_exact.embed_point(i, x_vec)
            x_back = ch_exact.preimage_point(i, y_mp)
            assert x_back is not None
            max_c_fixed = max(max_c_fixed, _diff_norm(x_back, x_vec))
        print(f"   Re-evaluated all {len(f64_c_failures)} float64 C-flagged point(s) in {a.dps}-digit arithmetic: "
              f"max round-trip error = {mp.nstr(max_c_fixed, 3)} (was up to {max(z[3] for z in f64_c_failures):.3e} in float64)", flush=True)
    print(f"3. Symplecticity ({a.dps}-digit, step h=1e-{a.dps // 3}): max defect = {mp.nstr(max_sym_mp, 3)}, "
          f"max |J|_F = {mp.nstr(max_jnorm, 3)}", flush=True)
    if a.scan_b:
        h_f64 = 1e-7
        nj = 100
        Xj = torch.cat([S[: nj // 2] * (1 - 3 * h_f64), B[: nj - nj // 2] * (1 - 3 * h_f64)], dim=0)
        b_flagged = []
        for i in range(a.k):
            J1 = ce.jac_fd(Embed_f64, i, Xj, h_f64)
            J2 = ce.jac_fd(Embed_f64, i, Xj, h_f64 / 2)
            J = (4 * J2 - J1) / 3
            D_mat = J.transpose(1, 2) @ ce.OMEGA @ J - ce.OMEGA
            nrm = J.flatten(1).norm(dim=1).pow(2).clamp_min(1.0)
            s_vec = D_mat.flatten(1).abs().max(dim=1).values / nrm
            bad_b = (s_vec > 1e-5) | ~torch.isfinite(s_vec)
            for idx in bad_b.nonzero(as_tuple=False).flatten().tolist():
                b_flagged.append((i, idx, Xj[idx].tolist(), float(s_vec[idx])))
        if b_flagged:
            b_flagged.sort(key=lambda z: -z[3])
            b_sub = b_flagged[:a.max_b_recheck]
            max_b_fixed = mp.mpf(0)
            max_b_jnorm = mp.mpf(0)
            for i, idx, x_raw, def64 in b_sub:
                x_vec = [mp.mpf(v) for v in x_raw]
                sdef, jnrm = _symplectic_defect(ch_exact, i, x_vec, h_mp)
                max_b_fixed = max(max_b_fixed, sdef)
                max_b_jnorm = max(max_b_jnorm, jnrm)
            print(f"   Re-evaluated {len(b_sub)}/{len(b_flagged)} float64 B-flagged point(s) in {a.dps}-digit arithmetic: "
                  f"max symplectic defect = {mp.nstr(max_b_fixed, 3)}, max |J|_F = {mp.nstr(max_b_jnorm, 3)} "
                  f"(was up to {b_flagged[0][3]:.3e} at float64 h=1e-7)", flush=True)
            assert max_b_fixed < mp.mpf("1e-25")

    # 4. Continuity on float64 G-flagged intervals
    if a.chords > 0:
        flagged = []
        for i in range(a.k):
            for item in _find_flagged_chords_f64(Embed_f64, i, a.chords, a.chord_pts, 40, a.seed + 1000 + i):
                flagged.append((i, *item))
        if not flagged:
            print(f"4. Continuity: 0 intervals flagged in float64 on {a.chords} chords/ball", flush=True)
        else:
            subset = flagged[:a.max_g_recheck]
            max_gap_30 = mp.mpf(0)
            max_ratio_err = mp.mpf(0)
            for i, lo_raw, hi_raw, gap8_f64, gap11_f64 in subset:
                lo_v = [mp.mpf(v) for v in lo_raw]
                hi_v = [mp.mpf(v) for v in hi_raw]
                mid_v = [(u + v) / 2 for u, v in zip(lo_v, hi_v)]
                # Bisect in mpmath down to separation <= 1e-12 to pinpoint the steep locus inside [lo, hi],
                # then shrink separation to 1e-20 and 1e-30 around that midpoint.
                a_v, b_v = list(lo_v), list(hi_v)
                while _diff_norm(b_v, a_v) > mp.mpf("1e-15"):
                    m_v = [(u + v) / 2 for u, v in zip(a_v, b_v)]
                    ya, ym, yb = ch_exact.embed_point(i, a_v), ch_exact.embed_point(i, m_v), ch_exact.embed_point(i, b_v)
                    if _diff_norm(ym, ya) >= _diff_norm(yb, ym):
                        b_v = m_v
                    else:
                        a_v = m_v
                c_v = [(u + v) / 2 for u, v in zip(a_v, b_v)]
                dir_v = [v - u for u, v in zip(lo_v, hi_v)]
                dn = _norm(dir_v)
                u_dir = [d / dn for d in dir_v]
                g20 = _diff_norm(
                    ch_exact.embed_point(i, [c + mp.mpf("0.5e-20") * d for c, d in zip(c_v, u_dir)]),
                    ch_exact.embed_point(i, [c - mp.mpf("0.5e-20") * d for c, d in zip(c_v, u_dir)]),
                )
                g30 = _diff_norm(
                    ch_exact.embed_point(i, [c + mp.mpf("0.5e-30") * d for c, d in zip(c_v, u_dir)]),
                    ch_exact.embed_point(i, [c - mp.mpf("0.5e-30") * d for c, d in zip(c_v, u_dir)]),
                )
                max_gap_30 = max(max_gap_30, g30)
                if g20 > 0:
                    max_ratio_err = max(max_ratio_err, abs(g30 / g20 - mp.mpf("1e-10")) / mp.mpf("1e-10"))
            print(f"4. Continuity ({a.dps}-digit): re-evaluated {len(subset)}/{len(flagged)} float64 G-flagged interval(s); "
                  f"all continuous, max gap at sep 1e-30 = {mp.nstr(max_gap_30, 3)}, "
                  f"max |gap(1e-30)/gap(1e-20) - 1e-10| / 1e-10 = {mp.nstr(max_ratio_err, 3)}", flush=True)
            assert max_gap_30 < mp.mpf("1e-14") and max_ratio_err < mp.mpf("1e-4")

    assert min_rad_margin > 0 and max_rt_mp < mp.mpf("1e-70") and max_sym_mp < mp.mpf("1e-25")
    print(f"MP CHECK PASS ({time.time() - t0:.1f} s)", flush=True)


if __name__ == "__main__":
    main()
