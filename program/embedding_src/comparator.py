"""Explicit parameter set Pi*(k, eps_c; f) and the 4D keyhole comparator F = F_2 o F_1.

Mathematical counterparts in Paper IV (paper/p4/main.pdf):
  * PiStar      : Section 7.1 (Definition 7.1 — non-iterative parameter formulas without cancellation).
  * Comparator3 : Section 4 (Proposition 4.2, Theorem 4.3 — 4D C^7 symplectic comparator on the flat model).
"""
import math
import torch

import primitives as pr
import keyhole as kh

F64, PI = pr.F64, pr.PI

EPS_C_MAX = 1.0 / 100.0
F_STAR = 0.25
LAM_A, LAM2, MU = 9.0 / 10.0, 3.0 / 10.0, 0.5
UPS = math.sqrt(11.0 / 1000.0)
M_ST = 4


class PiStar:
    """Explicit parameter set Pi*(k, eps_c; f) for k >= 10 and 0 < eps_c <= 1/100."""

    def __init__(self, k, eps_c, f=F_STAR):
        self.k, self.eps, self.kappa_b = int(k), float(eps_c), 1.0
        s = math.sqrt(self.k)
        eta = eps_c / (1.0 + math.sqrt(1.0 - eps_c))
        t0 = 1.0 - 0.5 * eta
        self.s, self.eta, self.t0 = s, eta, t0
        self.a, self.h, self.cs, self.g = t0 / s, t0 / 3.0, 3.0 * s - 9.0, 1.5 * eta
        self.rho_ball = (1.0 - eta) / s
        self.T = self.g / self.cs
        self.Gmax = s * t0 - 3.0
        self.kk = self.k - 3.0 * s
        self.lam_a, self.lam2, self.mu, self.f0, self.f1, self.m = LAM_A, LAM2, MU, f, f, M_ST
        self.wG, self.w2 = LAM_A * self.g, LAM2 * self.g
        ra = math.sqrt(self.a / PI)
        d = math.sqrt(f * self.T / PI) / (1.0 + UPS)
        beta = f * self.T / (PI * (ra + d) * (ra + 8.4 * d))
        K = kh.keyhole_star(ra, d, beta, 0.8, M_ST)
        self.ra, self.d, self.beta, self.rho_out = ra, d, beta, 1.0 + beta
        self.W1, self.W2, self.Ws, self.rh, self.rho1, self.Xw = K.W1, K.W2, K.W1 + K.W2, K.rh, K.rho1, K.Xw
        self.x0, self.theta0 = K.x0, K.theta0
        self.delta_rel, self.delta_small = K.delta_rel, K.delta_small
        self.KC = K
        # h_K and D = 1 - 3 h_K evaluated from the three linear candidates without cancellation:
        cand = (self.a, self.O(-self.wG) - 0.5 * MU * self.T * (1.0 - LAM_A), self.h - 0.5 * MU * self.T)
        Dc = (
            (s - 3.0 + 1.5 * eta) / s,
            (s - 3.0 + self.wG) / s + 1.5 * MU * self.T * (1.0 - LAM_A),
            0.5 * eta + 1.5 * MU * self.T,
        )
        j = max(range(3), key=lambda q: cand[q])
        self.hK, self.D, self.hK_case = cand[j], Dc[j], j

    def O(self, G):
        return (G + 3.0) / (3.0 * self.s)

    def E(self, G):
        return (G / self.cs).clamp_min(0.0) if torch.is_tensor(G) else max(G / self.cs, 0.0)

    def Ptop(self, G):
        return (self.k * self.a - 3.0 - G) / self.kk

    def slack(self, G):
        if torch.is_tensor(G):
            return self.T * (1.0 + G.clamp(max=0.0) / self.g)
        return self.T * (1.0 + min(G, 0.0) / self.g)

    def n_wild(self):
        return self.k - math.floor((3.0 - self.wG) / self.a)


class Comparator3:
    """4D keyhole comparator F = F_2 o F_1 on the flat chart (G, v, w), Omega = dG ^ dv + dw_x ^ dw_y.

    Where c(G) > 0 (i.e. G > -w_2), tau(G) == 1 identically, so KS_1(w) maps the stack disc D(P_top(G))
    strictly outside the origin hole D(x_0) and outside the slit |theta| <= theta_0. On C \\ [0, +inf),
    vartheta(theta) = theta - 1/2 sign(theta) = arg(-w_1) / (2 pi) is real-analytic across the negative real axis.
    """

    def __init__(self, P):
        self.P = P
        self.st = pr.TrigStep(P.m)
        self.K = P.KC

    def tauG(self, G):
        P = self.P
        u = (G + P.wG) / (P.wG - P.w2)
        return self.st(u), self.st.d(u) / (P.wG - P.w2) * ((u > 0.0) & (u < 1.0))

    def cG(self, G):
        P = self.P
        u = (G + P.w2) / P.w2
        return (P.w2 / P.cs) * self.st.ramp(u), torch.where(u >= 1.0, torch.ones_like(u), self.st(u)) / P.cs

    @staticmethod
    def vartheta(th):
        return th - 0.5 * torch.sign(th)

    def comp1(self, y, inverse=False):
        G, v, w = y[:, 0], y[:, 1], y[:, 2:]
        tau, dtau = self.tauG(G)
        act = tau > 0.0
        out = y.clone()
        if act.any():
            if not inverse:
                w1, gen = self.K.fwd(w[act], tau[act])
                out[act, 1] = v[act] - dtau[act] * gen
            else:
                w1, gen = self.K.inv(w[act], tau[act])
                out[act, 1] = v[act] + dtau[act] * gen
            out[act, 2:] = w1
        return out

    def comp2(self, y, inverse=False):
        G, v, w = y[:, 0], y[:, 1], y[:, 2:]
        c, dc = self.cG(G)
        act = c > 0.0
        out = y.clone()
        if act.any():
            x, th = pr.polar0(w[act])
            sgn = -1.0 if inverse else 1.0
            out[act, 1] = v[act] - sgn * dc[act] * self.vartheta(th)
            out[act, 2:] = pr.cart0(x + sgn * c[act], th)
        return out
