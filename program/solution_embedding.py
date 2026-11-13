"""Explicit closed-form C^4 symplectic packings of the four-ball by k unit balls.

Generated deterministically from the modular sources in program/embedding_src/ by program/build_embedding.py.
Complete mathematical proofs of all stages and parameter bounds are given in Paper IV (paper/p4/main.pdf).

Interface (a direct-map counterpart of the Epoch AI format: embeddings instead of an ODE Hamiltonian):
    solution(k, eps) returns self-contained Python source defining
        Embed(i, X) -> Y           the i-th embedding f_i, i = 0..k-1; X of shape (n, 4) in coordinates centred at
                                   ball i, |X| <= 1; Y of shape (n, 4) in the target R^4.
        Preimage(j, Y) -> (X, ok)  left inverse of f_j on B^o(R_s); ok = False means Y has no preimage in B^o(r_+).
        STAGES(i)                  the conformally symplectic stage factors of f_i with their inverses.
        CONFIG                     parameters, analytic margins of (H0)-(H15), and float64 self-test diagnostics.
    Coordinates (q1, q2, p1, p2), omega_0 = dq1 ^ dp1 + dq2 ^ dp2, R = (k / (1 - eps))^(1/4).

Mathematical scope vs. float64 scope:
  * Over exact real numbers (with exact scalar roots in KR^-1 and KS_tau), Theorem 1.1 of Paper IV proves that for
    every integer k >= 10 and every real eps in (0, 1), there is r_+ = sqrt(a / rho_b) > 1 such that f_0, ..., f_{k-1}
    are C^4 symplectic embeddings of B^o(r_+) into B^o(R) with pairwise disjoint images, and Preimage(i, .) is an
    exact left inverse on f_i(B^o(r_+)).
  * In IEEE-754 float64, solution(k, eps) evaluates the analytic margins of (H0)-(H15) on the float64 parameters and
    raises ValueError if rounding underflows any strict margin (e.g. eps <= 1e-16 where 1.0 - eps == 1.0). Because
    the maps have steep local Lipschitz constants (~ 10^8 - 10^15 as eps -> 0 or k grows), float64 evaluation loses
    precision for extreme (k, eps); see program/README.md and program/check_embedding_mp.py.
"""
_ORDER = ['primitives', 'keyhole', 'comparator', 'twists', 'transfer', 'chain']

_SRC = {
    'primitives': r'''"""Elementary smooth steps, periodic bumps, polar helpers, and safeguarded scalar root-finding.

Mathematical counterparts in Paper IV (paper/p4/main.pdf):
  * TrigStep       : Section 2.1, trigonometric step S_m in C^{2m}(R), antiderivative I_m, ramp R_m in C^{2m+1}(R).
  * Bump           : Section 2.1, symmetric plateau bump beta_{w_0, w_1, m} in C^{2m}(R) and primitive.
  * rot/mom/polar0 : Section 1.2, fibre action p = pi |w|^2 and normalised angle theta = arg(w) / (2 pi).
  * newton_bracket : Section 2.2, safeguarded Newton solver for strictly increasing scalar functions on [lo, hi].
"""
import math
import torch

F64 = torch.float64
C128 = torch.complex128
PI = math.pi


class TrigStep:
    """Smooth step S_m on [0, 1] with S_m'(u) = sin^{2m}(pi u) / c_0, c_0 = C(2m, m) / 2^{2m}.

    Clamped to 0 on (-inf, 0] and 1 on [1, +inf), S_m lies in C^{2m}(R), S_m' in C^{2m-1}(R),
    and the convex ramp R_m(u) = I_m(clamp(u, 0, 1)) + max(u - 1, 0) lies in C^{2m+1}(R) with I_m(1) = 1/2.
    """

    def __init__(self, m=4):
        self.m = m
        c0 = float(math.comb(2 * m, m))
        self.a = [2 * ((-1) ** j) * math.comb(2 * m, m - j) / c0 for j in range(1, m + 1)]

    def __call__(self, u):
        u = u.clamp(0.0, 1.0)
        out = u.clone()
        for j, aj in enumerate(self.a, 1):
            out = out + aj * torch.sin(2.0 * PI * j * u) / (2.0 * PI * j)
        return out

    def d(self, u):
        u = u.clamp(0.0, 1.0)
        out = torch.ones_like(u)
        for j, aj in enumerate(self.a, 1):
            out = out + aj * torch.cos(2.0 * PI * j * u)
        return out

    def I(self, u):
        """Antiderivative int_0^u S_m(t) dt for u in [0, 1] (clamped); I(1) = 1/2."""
        u = u.clamp(0.0, 1.0)
        out = 0.5 * u * u
        for j, aj in enumerate(self.a, 1):
            denom = 2.0 * PI * j
            out = out + aj * (1.0 - torch.cos(denom * u)) / (denom * denom)
        return out

    def ramp(self, u):
        """C^{2m+1} convex ramp: 0 (u <= 0), I_m(u) (0 <= u <= 1), u - 1/2 (u >= 1)."""
        return self.I(u) + (u - 1.0).clamp_min(0.0)


class Bump:
    """Symmetric C^{2m} plateau bump: 1 on |x| <= w0, 1 - S_m((|x| - w0)/(w1 - w0)) on [w0, w1], 0 on |x| >= w1.

    Since S_m(u) = O(u^{2m+1}) as u -> 0+, the composition with |x| is C^{2m} across x = +-w0 and x = +-w1.
    prim(x) = int_{-inf}^x beta(t) dt has total mass w0 + w1.
    """

    def __init__(self, w0, w1, m=2):
        self.w0, self.w1, self.D = w0, w1, w1 - w0
        self.st = TrigStep(m)
        self.mass = w0 + w1

    def val(self, x):
        return 1.0 - self.st((x.abs() - self.w0) / self.D)

    def prim(self, x):
        D, w0, st = self.D, self.w0, self.st
        uL = ((-x - w0) / D).clamp(0.0, 1.0)
        uR = ((x - w0) / D).clamp(0.0, 1.0)
        left = D * ((1.0 - uL) - (0.5 - st.I(uL)))
        mid = 0.5 * D + x.clamp(-w0, w0) + w0
        right = 0.5 * D + 2.0 * w0 + D * (uR - st.I(uR))
        return torch.where(x < -w0, left, torch.where(x <= w0, mid, right))


def rot(w, turns):
    c, s = torch.cos(2.0 * PI * turns), torch.sin(2.0 * PI * turns)
    return torch.stack((c * w[..., 0] - s * w[..., 1], s * w[..., 0] + c * w[..., 1]), -1)


def mom(w):
    return PI * (w[..., 0] ** 2 + w[..., 1] ** 2)


def polar0(w):
    return mom(w), torch.atan2(w[..., 1], w[..., 0]) / (2.0 * PI)


def cart0(x, th):
    r = torch.sqrt(x.clamp_min(0.0) / PI)
    return torch.stack((r * torch.cos(2.0 * PI * th), r * torch.sin(2.0 * PI * th)), -1)


def newton_bracket(f, lo, hi, x0, iters=60):
    """Safeguarded Newton root-finder for a strictly increasing function f -> (val, deriv) on [lo, hi]."""
    x = x0.clone()
    lo, hi = lo.clone(), hi.clone()
    for _ in range(iters):
        v, dv = f(x)
        lo = torch.where(v < 0.0, x, lo)
        hi = torch.where(v >= 0.0, x, hi)
        xn = x - v / dv
        bad = ~((xn > lo) & (xn < hi))
        x = torch.where(bad, 0.5 * (lo + hi), xn)
    v, dv = f(x)
    xn = x - v / dv
    return torch.where((xn >= lo) & (xn <= hi), xn, x)
''',
    'keyhole': r'''"""Planar smooth symplectic keyhole KS_tau and fibrewise Knothe-Rosenblatt strip map KR.

Mathematical counterparts in Paper IV (paper/p4/main.pdf):
  * SmoothKeyhole : Section 3 (Construction 3.1, Proposition 3.2, Theorem 3.3 — C^8 global symplectomorphism,
                    disc nesting with constant 8.4 > 2 + 2*pi, hole clearance > x0, slit clearance |theta| > theta0).
  * keyhole_star  : Section 7.1, closed-form keyhole datum (r_a; d, W_1, W_2, rho_1, beta, X_w, r_h).
  * KRStrip       : Section 2.3 (Proposition 2.3 — real-analytic symplectomorphism of open ball B(a) onto open cell).
"""
import math
import torch

import primitives as pr

F64, PI = pr.F64, pr.PI


class SmoothKeyhole:
    """Planar C^8 symplectomorphism family KS_tau generated by S(X, psi) = X psi + tau M(X)(Psi(psi) - psi)
    in polar action-angle coordinates (X, phi) about the eccentric centre c* = (-d, 0).
    """

    def __init__(self, d, W1, W2, rho1, rho_out, Xw, m=4):
        self.d, self.W1, self.W2 = d, W1, W2
        self.rho1, self.rho_out, self.Xw = rho1, rho_out, Xw
        self.st = pr.TrigStep(m)
        self.rh = None

    def dPsi(self, psi):
        u = (psi.abs() - self.W1) / (self.W2 - self.W1)
        return self.rho1 + (self.rho_out - self.rho1) * self.st(u)

    def Pmi(self, psi):
        """Psi(psi) - psi on [-1/2, 1/2]: odd, C^9, vanishes identically at psi = 0 and psi = +-1/2."""
        ap = psi.abs()
        D = self.W2 - self.W1
        u = (ap - self.W1) / D
        val = (self.rho1 - 1.0) * ap + (self.rho_out - self.rho1) * (D * self.st.I(u) + (ap - self.W2).clamp_min(0.0))
        return torch.sign(psi) * val

    def M(self, X):
        u = X / self.Xw
        return self.Xw * self.st.ramp(u), torch.where(u >= 1.0, torch.ones_like(u), self.st(u))

    def polar_c(self, w):
        dq = w[..., 0] + self.d
        return PI * (dq * dq + w[..., 1] ** 2), torch.atan2(w[..., 1], dq) / (2.0 * PI)

    def cart_c(self, X, psi):
        r = torch.sqrt(X.clamp_min(0.0) / PI)
        return torch.stack((r * torch.cos(2.0 * PI * psi) - self.d, r * torch.sin(2.0 * PI * psi)), -1)

    def fwd(self, w, tau=None):
        """Forward map KS_tau(w); returns (w', gen) with gen = dS/dtau = M(X)(Psi(psi) - psi)."""
        X, phi = self.polar_c(w)
        Mv, dM = self.M(X)
        tt = dM if tau is None else tau * dM
        ap = phi.abs()
        psi = pr.newton_bracket(
            lambda x: (x + tt * self.Pmi(x) - ap, 1.0 + tt * (self.dPsi(x) - 1.0)),
            torch.zeros_like(ap),
            torch.full_like(ap, 0.5),
            ap.clamp(0.0, 0.5),
        )
        psi = psi * torch.sign(phi)
        t = 1.0 if tau is None else tau
        Xn = X + t * Mv * (self.dPsi(psi) - 1.0)
        return self.cart_c(Xn, psi), Mv * self.Pmi(psi)

    def inv(self, w, tau=None):
        """Exact inverse KS_tau^{-1}(w'); closed-form for X >= X_w, scalar Newton on [0, X_w] inside."""
        Xn, psi = self.polar_c(w)
        t = torch.ones_like(Xn) if tau is None else tau + 0.0 * Xn
        a = t * (self.dPsi(psi) - 1.0)
        Xlin = (Xn + 0.5 * a * self.Xw) / (1.0 + a)
        inner = Xlin < self.Xw
        X = Xlin
        if inner.any():
            ai, Xi = a[inner], Xn[inner]
            Xr = pr.newton_bracket(
                lambda x: (x + ai * self.M(x)[0] - Xi, 1.0 + ai * self.M(x)[1]),
                torch.zeros_like(Xi),
                torch.full_like(Xi, self.Xw),
                Xi.clamp(0.0, self.Xw),
            )
            X = X.clone()
            X[inner] = Xr
        Mv, dM = self.M(X)
        phi = psi + t * dM * self.Pmi(psi)
        return self.cart_c(X, phi), Mv * self.Pmi(psi)


def keyhole_star(ra, d, beta, rho1_safety, m_st=4):
    """Closed-form keyhole datum (r_a; d, W_1, W_2, rho_1, beta, X_w, r_h) of Paper IV, Section 7.1."""
    W1 = beta / (3.0 * (1.0 + beta))
    rh = 0.9 * d * math.sin(2.0 * PI * W1)
    rho1 = rho1_safety * ((d - rh) / (d + ra)) ** 2
    W2 = beta / (1.0 + beta - rho1) - W1
    Xw = 0.2 * PI * (d - rh) ** 2
    K = SmoothKeyhole(d, W1, W2, rho1, 1.0 + beta, Xw, m_st)
    K.ra, K.rh, K.x0, K.theta0, K.beta = ra, rh, PI * rh * rh, W1, beta
    K.delta_rel = beta * PI * (ra + d) * (ra + 8.4 * d)
    K.delta_small = 4.0 * (PI ** 3) * d * (ra + d) * (W2 ** 2)
    return K


class KRStrip:
    """Fibrewise Knothe-Rosenblatt symplectomorphism of the open ball B(a) onto {0 < X < a - p, 0 < T < 1, p < a}.

    Forward evaluation is purely algebraic/trigonometric (no root-finding); the inverse solves Kepler's
    strictly monotone equation 2 alpha + sin(2 alpha) = 2(X / r^2 - pi / 2) on (-pi/2, pi/2).
    """

    def __init__(self, a):
        self.a = a

    def fwd(self, z):
        x, y, w = z[:, 0], z[:, 1], z[:, 2:]
        r2 = (self.a - pr.mom(w)) / PI
        r = torch.sqrt(r2)
        c = torch.sqrt(r2 - x * x)
        u = x / r
        X = r2 * (0.5 * PI + torch.asin(u) + u * c / r)
        C = (X - x * c) / (PI * r2) * y / (2.0 * c)
        return torch.cat((X[:, None], (0.5 + y / (2.0 * c))[:, None], pr.rot(w, C)), 1)

    def inv(self, yl):
        X, T, w = yl[:, 0], yl[:, 1], yl[:, 2:]
        p = pr.mom(w)
        in_cell = (p < self.a) & (X > 0.0) & (X < self.a - p) & (T > 0.0) & (T < 1.0)
        out = torch.full_like(yl, float("nan"))
        if not in_cell.any():
            return out
        Xm, Tm, wm, pm = X[in_cell], T[in_cell], w[in_cell], p[in_cell]
        r2 = (self.a - pm) / PI
        r = torch.sqrt(r2)
        m2 = 2.0 * (Xm / r2 - 0.5 * PI)
        al = pr.newton_bracket(
            lambda t: (2.0 * t + torch.sin(2.0 * t) - m2, 2.0 + 2.0 * torch.cos(2.0 * t)),
            torch.full_like(Xm, -0.5 * PI),
            torch.full_like(Xm, 0.5 * PI),
            (0.25 * m2).clamp(-0.5 * PI, 0.5 * PI),
        )
        x, c = r * torch.sin(al), r * torch.cos(al)
        y = (2.0 * Tm - 1.0) * c
        C = (Xm - x * c) / (PI * r2) * y / (2.0 * c)
        out[in_cell] = torch.cat((x[:, None], y[:, None], pr.rot(wm, -C)), 1)
        return out
''',
    'comparator': r'''"""Explicit parameter set Pi*(k, eps_c; f) and the 4D keyhole comparator F = F_2 o F_1.

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
''',
    'twists': r'''"""Deck-equivariant C^4 toric twists Psi = Phi_g o Psi_S routing the three marked fibres into the free corridor.

Mathematical counterparts in Paper IV (paper/p4/main.pdf):
  * SpiralShear : Section 5 (Construction 5.1, Proposition 5.2 — exact identity
                  Psi^{-1}(deck(M_j)) = {G = K(p) - delta (mod P(p)), v = v_j' (mod 1)}).
"""
import torch

import primitives as pr

TWIST = dict(ag=0.1, om0=0.015, om1=0.045, ou0=0.02, ou1=0.12, vcomp=0.25, oc0=0.05, oc1=0.14)


def _wrap(x, lo):
    return lo + torch.remainder(x - lo, 1.0)


class SpiralShear:
    """Closed-form C^4 symplectomorphisms Psi_S (B-twist) and Phi_g (A-twist) preserving p = pi |w|^2 pointwise."""

    FIB = (("M1", 5.0 / 6.0, 0.0, -1), ("M2", 1.0 / 3.0, 0.0, 0), ("M3", 0.0, 0.5, 0))

    def __init__(self, P, ag=0.1, om0=0.015, om1=0.045, ou0=0.02, ou1=0.12,
                 vcomp=0.25, oc0=0.05, oc1=0.14, vlo=-1.0 / 3.0, ulo=0.2, delta_frac=0.25, m=2):
        self.P = P
        self.global_shift = True
        self.ustar = -P.cs / 9.0
        self.delta = delta_frac * P.w2
        self.c0 = self.delta - P.cs / 3.0
        self.nj = [-round(uj - self.ustar) for (_, uj, _, _) in self.FIB]
        self.phi = [uj + n_ - self.ustar for (_, uj, _, _), n_ in zip(self.FIB, self.nj)]
        self.ag, self.vlo, self.ulo, self.vcomp = ag, vlo, ulo, vcomp
        self.bv = pr.Bump(om0, om1, m)
        self.bc = pr.Bump(oc0, oc1, m)
        self.bu = pr.Bump(ou0, ou1, m)
        self.vp = (-ag, 0.0, 0.5)
        self.uc = (5.0 / 6.0, 7.0 / 12.0)

    def S(self, p, v):
        vt = _wrap(v, self.vlo)
        xc = vt - self.vcomp
        cval = self.bc.val(xc) / self.bc.mass
        cprim = self.bc.prim(xc) / self.bc.mass
        Sv = torch.zeros_like(p)
        Sp = torch.zeros_like(p)
        hb = 3.0 - 9.0 * p
        for j in range(3):
            x = vt - self.vp[j]
            b = self.bv.val(x) - self.bv.mass * cval
            B = self.bv.prim(x) - self.bv.mass * cprim
            Sv = Sv + self.phi[j] * hb * b
            Sp = Sp - 9.0 * self.phi[j] * B
        Sv = Sv + self.c0
        return Sv, Sp

    def psiS(self, y, sign=1.0):
        G, v, w = y[..., 0], y[..., 1], y[..., 2:]
        Sv, Sp = self.S(pr.mom(w), v)
        return torch.cat(((G + sign * Sv)[..., None], v[..., None], pr.rot(w, -sign * Sp)), -1)

    def g(self, u):
        ut = _wrap(u, self.ulo)
        x0, x1 = ut - self.uc[0], ut - self.uc[1]
        g_val = -self.ag * (self.bu.val(x0) - self.bu.val(x1))
        Gg = -self.ag * (self.bu.prim(x0) - self.bu.prim(x1))
        return g_val, Gg

    def phiG(self, y, sign=1.0):
        G, v, w = y[..., 0], y[..., 1], y[..., 2:]
        u = G / (3.0 - 9.0 * pr.mom(w))
        g_val, Gg = self.g(u)
        return torch.cat((G[..., None], (v - sign * g_val)[..., None], pr.rot(w, sign * 9.0 * (Gg - u * g_val))), -1)

    def inv(self, y):
        return self.psiS(self.phiG(y, -1.0), -1.0)
''',
    'transfer': r'''"""Closed-form transfer K_post = b_{ball, kappa} o W_{noKH} o Band from the post chart into B(1).

Mathematical counterparts in Paper IV (paper/p4/main.pdf):
  * Transfer3 : Section 6 (Construction 6.1, Proposition 6.2, Theorem 6.4 — C^7 deck-invariant symplectic embedding
                of {p < h_K} \\ deck({M_1, M_2, M_3}) into B^o(1) = CP^2 \\ L_kappa, with cancellation-free inverse).
"""
import math
import torch

import primitives as pr

F64, C128, PI = pr.F64, pr.C128, pr.PI

FR = dict(fm=0.32, fd2=0.2, fsig=0.2, fdel=0.1)


class _PostChartW:
    """Piecewise closed-form map W (with corner keyhole set to identity, evaluated after Band) and its left inverse."""

    def __init__(self, hK, D, khB, fr=FR, kappa=(-1.0 / 12.0, 1.0 / 12.0, 0.0), m_st=4):
        self.hK, self.D = hK, D
        self.m, self.d2 = fr["fm"] * D, fr["fd2"] * D
        self.sig0, self.dkh = fr["fsig"] * D, fr["fdel"] * D
        self.kh = khB
        self.st = pr.TrigStep(m_st)
        self.kap = kappa
        k0, k1, k2 = kappa
        self.off = {0: (0.0, 0.0), 1: (k1, 3.0 * k1), "2s": (k1 + k2, 3.0 * k1 + 6.0 * k2), "2c": (-k0, 0.0)}
        self.left = {0: self.off["2c"], 1: self.off[0], 2: self.off[1]}
        arg = -4.0 * PI * (self.left[0][0] + 0.5 * k0)
        self.kappa_line = complex(math.cos(arg), math.sin(arg))

    def S(self, c):
        u = c.abs() / self.d2
        q = self.sig0 * (1.0 - self.st(u))
        dq = -self.sig0 * self.st.d(u) / self.d2 * torch.sign(c) * (u < 1.0)
        S = torch.hypot(c, q)
        dS = torch.where(S > 0.0, (c + q * dq) / S, torch.ones_like(c))
        return S, dS

    def lam_split(self, c):
        """Cancellation-free decomposition (lp, lm, lam') with lp = c - lam(c) >= 0, lm = -lam(c) >= 0."""
        u = c.abs() / self.d2
        q = self.sig0 * (1.0 - self.st(u))
        dq = -self.sig0 * self.st.d(u) / self.d2 * torch.sign(c) * (u < 1.0)
        S = torch.hypot(c, q)
        dS = torch.where(S > 0.0, (c + q * dq) / S, torch.ones_like(c))
        denom = 2.0 * (S + c.abs())
        rem = torch.where(denom > 0.0, (q * q) / denom.clamp_min(1e-300), torch.zeros_like(c))
        lp = torch.where(c >= 0.0, c + rem, rem)
        lm = torch.where(c >= 0.0, rem, -c + rem)
        return lp, lm, 0.5 * (1.0 - dS)

    def kstep(self, c, j):
        return self.kap[j] * self.st((c + self.m) / (2.0 * self.m))

    @staticmethod
    def reduce(sig, psi, p, vt, lo=1.0 / 6.0):
        n = torch.floor(sig / (3.0 - 9.0 * p) + lo)
        return sig - n * (3.0 - 9.0 * p), psi, p, vt - n * (9.0 * psi + 0.5)

    def W(self, sig, psi, p, vt):
        """Evaluate homogeneous unit vector W in C^3 after Band (no second corner keyhole)."""
        sig, psi, p, vt = self.reduce(sig, psi, p, vt)
        N = len(sig)
        W = torch.zeros(N, 3, dtype=C128)
        vc = sig / (3.0 - 9.0 * p)
        mus = [sig, sig - (1.0 - 3.0 * p), sig - 2.0 * (1.0 - 3.0 * p)]
        instrip = [mu.abs() < self.m for mu in mus]
        anys = instrip[0] | instrip[1] | instrip[2]
        secs = [
            (vc >= 0.0) & (vc < 1.0 / 3.0) & ~anys,
            (vc >= 1.0 / 3.0) & (vc < 2.0 / 3.0) & ~anys,
            (vc >= 2.0 / 3.0) & ~anys,
            (vc < 0.0) & ~anys,
        ]
        for mk, key in zip(secs, (0, 1, "2s", "2c")):
            if not mk.any():
                continue
            a_, b_ = self.off[key]
            ps, vv, pp, sg = psi[mk] + a_, vt[mk] + b_, p[mk], sig[mk]
            if key == "2c":
                X0, X1, X2 = 1.0 - 2.0 * pp + sg, pp, pp - sg
                T1, T2 = vv + ps, -ps
            elif key == 0:
                X0, X1, X2 = 1.0 - 2.0 * pp - sg, pp + sg, pp
                T1, T2 = ps, vv - ps
            elif key == 1:
                X0, X1, X2 = pp, 2.0 - 5.0 * pp - sg, 4.0 * pp + sg - 1.0
                T1, T2 = -vv + 4.0 * ps, -vv + 5.0 * ps
            else:
                X0, X1, X2 = 7.0 * pp + sg - 2.0, pp, 3.0 - 8.0 * pp - sg
                T1, T2 = vv - 8.0 * ps, -ps
            W[mk] = torch.stack(
                (
                    torch.sqrt(X0.clamp_min(0.0)).to(C128),
                    torch.sqrt(X1.clamp_min(0.0)) * torch.exp(2j * PI * T1),
                    torch.sqrt(X2.clamp_min(0.0)) * torch.exp(2j * PI * T2),
                ),
                1,
            )
        for j in range(3):
            mk = instrip[j]
            if not mk.any():
                continue
            c = mus[j][mk]
            a_, b_ = self.left[j]
            kj = self.kstep(c, j)
            ps = psi[mk] + a_ + kj
            vv = vt[mk] + b_ + 3.0 * j * kj
            vj = vv - 3.0 * j * ps
            # In Band + W_noKH, Band has already applied the corner keyhole; here p2 = p, ang = vj (mod 1).
            w2 = pr.cart0(p[mk], vj)
            p2, ang = pr.polar0(w2)
            vl = ang - torch.floor(ang)
            lp, lm, lamp = self.lam_split(c)
            xa = p2 + lp
            xb = p2 + lm
            xr = (1.0 - xa - xb).clamp_min(0.0)
            Ta = ps + lamp * vl
            loc = torch.stack(
                (
                    torch.sqrt(xr).to(C128),
                    torch.sqrt(xa) * torch.exp(2j * PI * Ta),
                    torch.sqrt(xb) * torch.exp(2j * PI * (vl - Ta)),
                ),
                1,
            )
            perm = ((0, 1, 2), (1, 2, 0), (2, 0, 1))[j]
            Wg = torch.zeros_like(loc)
            for li, gi in enumerate(perm):
                Wg[:, gi] = loc[:, li]
            W[mk] = Wg
        return W

    def invert(self, W):
        """Cancellation-free left inverse of W (prior to Band_inv), recovering non-negative moments directly."""
        W = W / W.abs().pow(2).sum(1, keepdim=True).sqrt()
        X = W.abs() ** 2
        ang = torch.angle(W) / (2.0 * PI)
        N = len(W)
        nan = torch.full((N,), float("nan"), dtype=F64)
        sig, psi, p, vt = nan.clone(), nan.clone(), nan.clone(), nan.clone()
        piece = torch.full((N,), -1)
        done = torch.zeros(N, dtype=torch.bool)
        for j in range(3):
            a, b = (j + 1) % 3, (j + 2) % 3
            mu = X[:, a] - X[:, b]
            mk = (mu.abs() < self.m) & (X[:, j] > 1.0 / 3.0)
            if not mk.any():
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
            pp, vj = pr.polar0(pr.cart0(p2, vl))
            sig[mk] = c + j * (1.0 - 3.0 * pp)
            psi[mk] = ps2 - kj - a_
            p[mk] = pp
            vt[mk] = vj + 3.0 * j * ps2 - 3.0 * j * kj - b_
            piece[mk] = j
            done |= mk
        e = torch.argmin(X, 1)
        # Recover non-negative fibre moment p directly from X_2, X_0, X_1 (never via 1 - X_1 - X_2 cancellation).
        for key, edge in ((0, 2), (1, 0), ("2s", 1)):
            mk = ~done & (e == edge)
            if not mk.any():
                continue
            jj = 2 if key == "2s" else key
            T1 = ang[mk, 1] - ang[mk, 0]
            T2 = ang[mk, 2] - ang[mk, 0]
            if key == 0:
                pp = X[mk, 2]
                sg = X[mk, 1] - X[mk, 2]
                vv, ps = T1 + T2, T1
            elif key == 1:
                pp = X[mk, 0]
                sg = 1.0 + X[mk, 2] - 4.0 * X[mk, 0]
                vv, ps = -5.0 * T1 + 4.0 * T2, -T1 + T2
            else:
                pp = X[mk, 1]
                sg = 3.0 - X[mk, 2] - 8.0 * X[mk, 1]
                vv, ps = T1 - 8.0 * T2, -T2
            a_, b_ = self.off[key]
            sig[mk], p[mk], vt[mk], psi[mk] = sg, pp, vv - b_, ps - a_
            piece[mk] = 10 + jj
        return self.reduce(sig, psi, p, vt), piece

    def unchart(self, y):
        yy = torch.complex(y[:, :2], y[:, 2:]) * math.sqrt(PI)
        rad = 1.0 - yy.abs().pow(2).sum(1)
        Z0 = torch.sqrt(rad).to(C128)  # NaN when |y|^2 > 1/pi (outside B(R_s)) -> Preimage marks ok=False
        kap = self.kappa_line
        W1 = (yy[:, 0] - kap.conjugate() * Z0) / math.sqrt(2.0)
        W2 = (Z0 + kap * yy[:, 0]) / math.sqrt(2.0)
        return torch.stack((yy[:, 1], W1, W2), 1)


class Transfer3(_PostChartW):
    """Split transfer K_post = chart9 o wproj o band, with explicit stage inverses."""

    def __init__(self, hK, D, khB, fr=FR, kappa=(-1.0 / 12.0, 1.0 / 12.0, 0.0), m_st=4):
        super().__init__(hK, D, khB, fr, kappa, m_st)
        self.post = _PostChartW(hK, D, khB, fr, kappa, m_st)

    def tau(self, c):
        u = (c.abs() - self.d2) / (self.m - self.d2)
        return 1.0 - self.st(u), -self.st.d(u) / (self.m - self.d2) * torch.sign(c) * ((u > 0.0) & (u < 1.0))

    def _band(self, x, inverse):
        sig0, psi0, w0 = x[:, 0], x[:, 1], x[:, 2:]
        p0, vt0 = pr.polar0(w0)
        n = torch.floor(sig0 / (3.0 - 9.0 * p0) + 1.0 / 6.0)
        sig, psi, p, vt = sig0 - n * (3.0 - 9.0 * p0), psi0, p0, vt0 - n * (9.0 * psi0 + 0.5)
        out = x.clone()
        for j in range(3):
            c = sig - j * (1.0 - 3.0 * p)
            mk = c.abs() < self.m
            if not mk.any():
                continue
            c = c[mk]
            a_, b_ = self.left[j]
            kj = self.kstep(c, j)
            ps = psi[mk] + a_ + kj
            vj = vt[mk] + b_ + 3.0 * j * kj - 3.0 * j * ps
            T_v, dT = self.tau(c)
            if not inverse:
                w2, gen = self.kh.fwd(pr.cart0(p[mk], vj), T_v)
                ps2 = ps - dT * gen
            else:
                w2, gen = self.kh.inv(pr.cart0(p[mk], vj), T_v)
                ps2 = ps + dT * gen
            p2, vj2 = pr.polar0(w2)
            so = c + j * (1.0 - 3.0 * p2)
            po = ps2 - a_ - kj
            vo = vj2 + 3.0 * j * ps2 - b_ - 3.0 * j * kj
            nn = n[mk]
            out[mk] = torch.cat(((so + nn * (3.0 - 9.0 * p2))[:, None], po[:, None], pr.cart0(p2, vo + nn * (9.0 * po + 0.5))), 1)
        return out

    def band(self, x):
        return self._band(x, False)

    def band_inv(self, x):
        return self._band(x, True)

    def _Z(self, W):
        kap = self.kappa_line
        return torch.stack(((W[:, 2] - kap * W[:, 1]) / math.sqrt(2.0), (W[:, 1] + kap.conjugate() * W[:, 2]) / math.sqrt(2.0), W[:, 0]), 1)

    @staticmethod
    def _proj(Z):
        Z = Z / Z.abs().pow(2).sum(1, keepdim=True).sqrt()
        a, b, c = Z[:, 1] * Z[:, 0].conj(), Z[:, 2] * Z[:, 0].conj(), Z[:, 1] * Z[:, 2].conj()
        return torch.stack((Z[:, 0].abs() ** 2, Z[:, 1].abs() ** 2, Z[:, 2].abs() ** 2, a.real, a.imag, b.real, b.imag, c.real, c.imag), 1)

    def wproj(self, x):
        """Gauge-free rank-one projector Z Z^* in R^9 representing [Z] in CP^2."""
        p, vt = pr.polar0(x[:, 2:])
        return self._proj(self._Z(self.post.W(x[:, 0], x[:, 1], p, vt)))

    def wproj_inv(self, q):
        a, b, c = torch.complex(q[:, 3], q[:, 4]), torch.complex(q[:, 5], q[:, 6]), torch.complex(q[:, 7], q[:, 8])
        d = q[:, :3].to(C128)
        cols = [torch.stack((d[:, 0], a, b), 1), torch.stack((a.conj(), d[:, 1], c.conj()), 1), torch.stack((b.conj(), c, d[:, 2]), 1)]
        j = torch.argmax(q[:, :3], 1)
        Z = torch.where((j == 0)[:, None], cols[0], torch.where((j == 1)[:, None], cols[1], cols[2]))
        kap = self.kappa_line
        W = torch.stack((Z[:, 2], (Z[:, 1] - kap.conjugate() * Z[:, 0]) / math.sqrt(2.0), (Z[:, 0] + kap * Z[:, 1]) / math.sqrt(2.0)), 1)
        (sig, psi, p, vt), _ = self.post.invert(W)
        return torch.cat((sig[:, None], psi[:, None], pr.cart0(p, vt)), 1)

    @staticmethod
    def chart9(q):
        nrm = torch.sqrt(PI * q[:, 0] * (q[:, 0] + q[:, 1] + q[:, 2]))
        return torch.stack((q[:, 3] / nrm, q[:, 5] / nrm, q[:, 4] / nrm, q[:, 6] / nrm), 1)

    def chart9_inv(self, y):
        yy = torch.complex(y[:, :2], y[:, 2:]) * math.sqrt(PI)
        Z0 = torch.sqrt(1.0 - yy.abs().pow(2).sum(1)).to(C128)
        return self._proj(torch.stack((Z0, yy[:, 0], yy[:, 1]), 1))

    def wpost_inv(self, y):
        (sig, psi, p, vt), _ = self.post.invert(self.post.unchart(y))
        return torch.cat((sig[:, None], psi[:, None], pr.cart0(p, vt)), 1)
''',
    'chain': r'''"""Assembled closed-form C^4 packing chain Chain3, analytic hypothesis checks (H0)-(H15), and self-test.

Mathematical counterparts in Paper IV (paper/p4/main.pdf):
  * hypotheses : Section 7.2 (Proposition 7.3 — exact analytic inequalities for (H0)-(H15) and split,
                 replacing grid checks on (H6), (H7), and S_max by closed-form convexity/concavity bounds).
  * Chain3     : Theorem 1.1 & Section 8 (composition f_i = S_out o chi o W o Band o post o Phi_g o Psi_S o F o cell o KR o S_in,
                 with explicit inverse Preimage).
"""
import math
import torch

import primitives as pr
import keyhole as kh
import comparator as cmp
import twists as tw_mod
import transfer as tr_mod

F64, PI = pr.F64, pr.PI

PROOF = "Paper IV: Closed-form symplectic packings of the four-ball by equal balls (paper/p4/main.pdf)"
MS_ABS, MS_FRAC = 2e-6, 1.0 / 8.0

CHARTS = {
    "scale": ("ball", "norm"),
    "strip (KR)": ("norm", "cell"),
    "cell -> flat": ("cell", "flat"),
    "comparator keyhole": ("flat", "flat"),
    "comparator shift": ("flat", "flat"),
    "twist B (Psi_S)": ("flat", "flat"),
    "twist A (Phi_g)": ("flat", "flat"),
    "post chart": ("flat", "post"),
    "corner keyhole (Band)": ("post", "post"),
    "CP2 point (projector)": ("post", "cp2"),
    "ball chart of CP2 minus L + scale": ("cp2", "target"),
}


def _circ(x):
    x = abs(x) % 1.0
    return min(x, 1.0 - x)


def hypotheses(ch):
    """Evaluate all hypotheses (H0)-(H15) and split of Paper IV, Section 7, using analytic margins (no grids).

    In float64, extremely small eps (<~ 1e-15) or extreme k can underflow strict margins such as H2 (a - rho_b > 0);
    Chain3 raises ValueError whenever any float64 margin ceases to hold.
    """
    P, T, KB, tw = ch.P, ch.T, ch.T.kh, ch.tw
    st = pr.TrigStep(cmp.M_ST)
    out = {}

    def put(name, margin, strict=True):
        ok = (margin > 0.0) if strict else (margin >= 0.0)
        out[name] = (bool(ok and math.isfinite(margin)), float(margin))

    put("H0 k>=10 integer", 1.0 if (int(P.k) == P.k and P.k >= 10) else -1.0)
    put("H0 0<eps_c<1", min(P.eps, 1.0 - P.eps))
    put("H1 0<lam2<lam_a<=1", min(P.lam2, P.lam_a - P.lam2) if P.lam_a <= 1.0 else -1.0)
    put("H1 0<mu<1", min(P.mu, 1.0 - P.mu))
    put("H2 0<rho_b<a", min(ch.rho_b, (P.a - ch.rho_b) / P.a))

    def check_kh(tag, K):
        put(tag + " positive", min(K.ra, K.d, K.W1, K.W2, K.rho1, K.beta, K.Xw, K.rh))
        put(tag + " (K1) W1<W2", (K.W2 - K.W1) / K.W2)
        put(tag + " (K1) W2<=1/6", 1.0 / 6.0 - K.W2, strict=False)
        put(tag + " (K1) rho1<1", 1.0 - K.rho1)
        put(tag + " (K1) (W1+W2)(1+beta-rho1)=beta", 1e-12 - abs((K.W1 + K.W2) * (1.0 + K.beta - K.rho1) / K.beta - 1.0), strict=False)
        put(tag + " (K2) rh<=d sin(2 pi W1)", 1.0 - K.rh / (K.d * math.sin(2.0 * PI * K.W1)), strict=False)
        put(tag + " (K3)", 1.0 - (K.rho1 * PI * (K.d + K.ra) ** 2 + 0.5 * K.Xw) / (PI * (K.d - K.rh) ** 2))

    KC = P.KC
    put("H3 K_C r_a=sqrt(a/pi)", 1e-12 - abs(KC.ra / math.sqrt(P.a / PI) - 1.0), strict=False)
    check_kh("H3-H5 K_C", KC)

    # Analytic (grid-free) lower bound for (H6) on [0, 1] (Paper IV, Lemma 7.2):
    #   * On [0, 1/2], convexity of S_4 gives S_4(u) <= u, so (1-mu)(1-lam_a + u(lam_a-lam2)) - r_rel S_4(u)
    #     >= (1-mu)(1-lam_a) + u ((1-mu)(lam_a-lam2) - r_rel).
    #   * On [1/2, 1], concavity of S_4 bounds S_4(u) <= S_4(2/3) + S_4'(2/3)(u - 2/3), reducing to the two endpoints u = 1/2, 1.
    Tt = P.T
    r_rel = KC.delta_rel / Tt
    r_sm = KC.delta_small / Tt
    u0 = torch.tensor(2.0 / 3.0, dtype=F64)
    st_u0, dst_u0 = float(st(u0)), float(st.d(u0))
    c_a0 = (1.0 - P.mu) * (1.0 - P.lam_a)
    c_a1 = (1.0 - P.mu) * (P.lam_a - P.lam2)
    h6_left = min(c_a0, c_a0 + 0.5 * (c_a1 - r_rel))
    h6_right = min(
        c_a0 + 0.5 * c_a1 - r_rel * (st_u0 + dst_u0 * (0.5 - 2.0 / 3.0)),
        c_a0 + c_a1 - r_rel * (st_u0 + dst_u0 * (1.0 - 2.0 / 3.0)),
    )
    h6_analytic = min(h6_left, h6_right, c_a0 - r_sm)
    put("H6 (analytic)", h6_analytic, strict=False)

    # Analytic (grid-free) lower bound for (H7) on [0, 1] (Paper IV, Lemma 7.2):
    #   When lam2 <= 2(1 - mu), ((1-mu) lam2 u - lam2 I_4(u))' = lam2 ((1-mu) - S_4(u)) switches sign at most once (+ then -),
    #   so its global minimum on [0, 1] is attained at the endpoints u = 0 and u = 1 (recall I_4(0) = 0, I_4(1) = 1/2).
    rmax_kc = max(r_rel, r_sm)
    if P.lam2 <= 2.0 * (1.0 - P.mu):
        h7_analytic = min(
            (1.0 - P.mu) * (1.0 - P.lam2) - rmax_kc,
            (1.0 - P.mu) - (rmax_kc + 0.5 * P.lam2),
        )
    else:
        h7_analytic = -1.0
    put("H7 (analytic)", h7_analytic, strict=False)

    put("H8 pi d^2<=T(1-mu-lam2/2)", (1.0 - P.mu - 0.5 * P.lam2) - PI * KC.d ** 2 / Tt, strict=False)
    put("H8 pi d^2+lam2 T/2+mu T<=O(-lam_a g)", P.O(-P.wG) - (PI * KC.d ** 2 + 0.5 * P.lam2 * Tt + P.mu * Tt), strict=False)
    put("H9", 1.0 - (P.cs * PI * KC.rh ** 2 + 1.5 * P.lam2 * P.g) / P.g, strict=False)
    # Corridor separation between group region top K(p) - (3 - 9a) and marked-fibre spiral K(p) - delta:
    put("H9b corridor (3-9a)>delta", (3.0 - 9.0 * P.a) - tw.delta)

    c = ch.twist_const
    put("H10 constants ordered", min(c["ag"], c["om0"], c["om1"] - c["om0"], c["ou0"], c["ou1"] - c["ou0"], c["oc0"], c["oc1"] - c["oc0"]))
    iv = [(-c["ag"], c["om1"]), (0.0, c["om1"]), (0.5, c["om1"]), (c["vcomp"], c["oc1"])]
    put("H10 (T-a)", min(_circ(iv[i][0] - iv[j][0]) - iv[i][1] - iv[j][1] for i in range(4) for j in range(i)))
    lobes = (5.0 / 6.0, 7.0 / 12.0)
    put("H10 (T-b) lobes disjoint", _circ(lobes[0] - lobes[1]) - 2.0 * c["ou1"])
    put("H10 (T-b) distance to 1/3 and 0", min(_circ(l - q) - c["ou1"] for l in lobes for q in (1.0 / 3.0, 0.0)) - c["ou0"], strict=False)
    put("H10 n_j integers", 1.0 if all(float(n) == int(n) for n in tw.nj) else -1.0)
    put(
        "H10 code constants = checked constants",
        1.0
        if (
            tw.ag == c["ag"]
            and tw.vcomp == c["vcomp"]
            and tw.bv.w0 == c["om0"]
            and tw.bv.w1 == c["om1"]
            and tw.bu.w0 == c["ou0"]
            and tw.bu.w1 == c["ou1"]
            and tw.bc.w0 == c["oc0"]
            and tw.bc.w1 == c["oc1"]
            and tw.global_shift
            and tw.delta == 0.25 * P.w2
            and tuple(tw.vp) == (-c["ag"], 0.0, 0.5)
        )
        else -1.0,
    )

    put("H11 a<=hK", T.hK - P.a, strict=False)
    put("H11 hK<1/3", T.D)
    Gs = [((P.s - 3.0 + P.wG) / P.s, P.T * (1.0 - P.lam_a)), (0.5 * P.eta, P.T)] + ([((P.s - 3.0) / P.s, P.T)] if P.Gmax > 0.0 else [])
    put("H11 hK>O-mu slack", min((q - T.D) / 3.0 + P.mu * sl for q, sl in Gs))
    put("H11 D consistent with hK", 1e-9 - abs((1.0 - 3.0 * T.hK) - T.D) / max(T.D, 1e-300) if T.D > 1e-6 else 1.0, strict=False)

    put("H12 K_B r_a=sqrt(hK/pi)", 1e-12 - abs(KB.ra / math.sqrt(T.hK / PI) - 1.0), strict=False)
    check_kh("H12 K_B", KB)
    put("H13", 1.0 - max(PI * KB.d ** 2, KB.delta_rel, KB.delta_small) / T.dkh, strict=False)

    # Analytic S_max bound on [-m, m]: for |c| <= d2, 0 <= q(c) <= sig0 so S(c) <= hypot(d2, sig0); for d2 <= |c| <= m, q(c) = 0 so S(c) = |c| <= m.
    put("H14 d2<m", (T.m - T.d2) / T.m)
    Sb = max(T.m, math.hypot(T.d2, T.sig0))
    eta1 = 2.0 / 3.0 - (2.0 * T.dkh + Sb) / T.D
    put("H14 2 delta_kh+S_max<2D/3 (eta_1)", eta1)
    put("H15 m<=3 eta_1 D", 3.0 * eta1 - T.m / T.D, strict=False)
    put("split 2m<D-3 delta_kh", 1.0 - 3.0 * T.dkh / T.D - 2.0 * T.m / T.D)
    return out


class Chain3:
    """Closed-form C^4 symplectic packing chain for (k, eps), using eps_c = min(eps, 1/100) and Pi*(k, eps_c; 1/4)."""

    def __init__(self, k, eps, f=cmp.F_STAR, check=True):
        if int(k) != k or k < 10 or not (0.0 < float(eps) < 1.0):
            raise ValueError("need an integer k >= 10 and 0 < eps < 1")
        self.k, self.eps_requested = int(k), float(eps)
        self.eps = min(self.eps_requested, cmp.EPS_C_MAX)
        try:
            self._build(f)
        except (AssertionError, ZeroDivisionError, OverflowError) as ex:
            raise ValueError(
                "float64 break-down while evaluating parameters for k=%r eps=%r: %s: %s"
                % (k, eps, type(ex).__name__, str(ex)[:200])
            )
        bad = [n for n, (ok, _) in self.hyp.items() if not ok]
        if check and bad:
            raise ValueError(
                "hypotheses fail in float64 for k=%r eps=%r (eps_c=%r): %s"
                % (k, eps, self.eps, "; ".join("%s [%.3e]" % (n, self.hyp[n][1]) for n in bad))
            )

    def _build(self, f):
        self.P = P = cmp.PiStar(self.k, self.eps, f)
        self.R_requested = (self.k / (1.0 - self.eps_requested)) ** 0.25
        self.R = 1.0 / math.sqrt(P.rho_ball)
        self.margin = min(MS_ABS, MS_FRAC * P.eta)
        self.Rs = self.R * (1.0 - self.margin)
        self.rho_b = P.rho_ball / ((1.0 - self.margin) ** 2)
        self.r_dom = math.sqrt(P.a / self.rho_b)
        self.strip = kh.KRStrip(P.a)
        self.C = cmp.Comparator3(P)
        self.twist_const = dict(tw_mod.TWIST)
        self.tw = tw_mod.SpiralShear(P, **tw_mod.TWIST)
        self.psi0, self.vcut, self.lift = -1.0 / 6.0, 0.5, 1
        d2k = tr_mod.FR["fdel"] * P.D
        rB = math.sqrt(P.hK / PI)
        dB = math.sqrt(0.8 * d2k / PI) / 1.05
        KB = kh.keyhole_star(rB, dB, 0.8 * d2k / (PI * (rB + dB) * (rB + 8.4 * dB)), 0.7, cmp.M_ST)
        self.T = tr_mod.Transfer3(P.hK, P.D, KB)
        self.scale = math.sqrt(PI) * self.Rs
        self.ngroup = 9
        self.config = dict(
            eps_c=self.eps,
            f=f,
            margin=self.margin,
            r_domain=self.r_dom,
            hK=P.hK,
            D=P.D,
            twist="narrow_g",
            strip="kr",
            proof=PROOF,
        )
        self.hyp = hypotheses(self)

    def J(self, p):
        return 3.0 * self.P.s * p - 3.0

    def cell_to_flat(self, i, yl):
        P = self.P
        X, T, w = yl[..., 0], yl[..., 1], yl[..., 2:]
        p = pr.mom(w)
        if i < self.ngroup:
            return torch.cat(((self.J(p) + 9.0 * X)[..., None], ((i - 4 + T) / 9.0)[..., None], pr.rot(w, -3.0 * P.s * T / 9.0)), -1)
        dA = 3.0 * P.s - i
        return torch.cat(((X + self.J(p) + i * (P.a - p))[..., None], (T + self.vcut)[..., None], pr.rot(w, -dA * T)), -1)

    def flat_to_cell(self, i, y):
        P = self.P
        G, v, w = y[..., 0], y[..., 1], y[..., 2:]
        p = pr.mom(w)
        if i < self.ngroup:
            T = 9.0 * v - (i - 4)
            T = T - 9.0 * torch.floor(T / 9.0)
            return torch.cat((((G - self.J(p)) / 9.0)[..., None], T[..., None], pr.rot(w, 3.0 * P.s * T / 9.0)), -1)
        dA = 3.0 * P.s - i
        T = v - self.vcut
        T = T - torch.floor(T)
        return torch.cat(((G - self.J(p) - i * (P.a - p))[..., None], T[..., None], pr.rot(w, dA * T)), -1)

    def to_fund(self, y):
        G, v, w = y[..., 0], y[..., 1], y[..., 2:]
        hb = 3.0 - 9.0 * pr.mom(w)
        n = torch.floor((G - self.J(pr.mom(w))) / hb)
        return torch.cat(((G - n * hb)[..., None], v[..., None], pr.rot(w, -9.0 * n * v)), -1)

    def _post(self, y):
        G, v, w = y[:, 0], y[:, 1], y[:, 2:]
        p, th = pr.polar0(w)
        hb = 3.0 - 9.0 * p
        ua = G / hb + self.lift
        sig, psi, vt = hb * v, self.psi0 - ua, th - 9.0 * (ua - self.lift) * v
        return torch.cat((sig[:, None], psi[:, None], pr.cart0(p, vt)), 1)

    def _post_inv(self, x):
        sig, psi = x[:, 0], x[:, 1]
        p, vt = pr.polar0(x[:, 2:])
        hb = 3.0 - 9.0 * p
        ua = self.psi0 - psi
        v = sig / hb
        w = pr.cart0(p, vt + 9.0 * (ua - self.lift) * v)
        return torch.cat((((ua - self.lift) * hb)[:, None], v[:, None], w), 1)

    def stages(self, i):
        sc = self.scale
        perm = [0, 2, 1, 3]
        S = [
            ("scale", lambda X: X[:, perm] / sc, lambda z: z[:, perm] * sc),
            ("strip (KR)", self.strip.fwd, self.strip.inv),
            ("cell -> flat", lambda yl: self.cell_to_flat(i, yl), lambda y: self.flat_to_cell(i, y)),
        ]
        if i >= self.ngroup:
            S.append(("comparator keyhole", self.C.comp1, lambda y: self.C.comp1(y, True)))
            S.append(("comparator shift", self.C.comp2, lambda y: self.C.comp2(y, True)))
        S.extend(
            [
                ("twist B (Psi_S)", self.tw.psiS, lambda y: self.tw.psiS(y, -1.0)),
                ("twist A (Phi_g)", self.tw.phiG, lambda y: self.tw.phiG(y, -1.0)),
                ("post chart", self._post, self._post_inv),
                ("corner keyhole (Band)", self.T.band, self.T.band_inv),
                ("CP2 point (projector)", self.T.wproj, self.T.wproj_inv),
                ("ball chart of CP2 minus L + scale", lambda q: self.T.chart9(q) * sc, lambda Y: self.T.chart9_inv(Y / sc)),
            ]
        )
        return S

    def Embed(self, i, Xb):
        y = Xb
        for _, f, _ in self.stages(i):
            y = f(y)
        return y

    def target_to_flat(self, Y):
        x = self.T.band_inv(self.T.wpost_inv(Y / self.scale))
        y = self._post_inv(x)
        return self.to_fund(self.tw.inv(y)), None

    def Preimage(self, j, Y, flat=None):
        y = self.target_to_flat(Y)[0] if flat is None else flat
        st = self.stages(j)
        hi = [s[0] for s in st].index("twist B (Psi_S)")
        for _, _, g in reversed(st[:hi]):
            y = g(y)
        return y, torch.isfinite(y).all(dim=1)


def stage_dicts(ch, i):
    out = []
    for nm, f, g in ch.stages(i):
        ci, co = CHARTS[nm]
        conf = 1.0 / ch.scale ** 2 if nm == "scale" else (ch.scale ** 2 if co == "target" else 1.0)
        out.append(dict(name=nm, fwd=f, inv=g, chart_in=ci, chart_out=co, conf=conf))
    return out


def special_points():
    """Deterministic test points: ball centre, +-e_a axis boundary points, and zero-fibre/zero-base diagonals."""
    pts = [torch.zeros(4, dtype=F64)]
    for d in range(4):
        for sgn in (-1.0, 1.0):
            v = torch.zeros(4, dtype=F64)
            v[d] = sgn
            pts.append(v)
    rt2 = 1.0 / math.sqrt(2.0)
    for s1 in (-rt2, rt2):
        for s2 in (-rt2, rt2):
            pts.append(torch.tensor([s1, 0.0, s2, 0.0], dtype=F64))
            pts.append(torch.tensor([0.0, s1, 0.0, s2], dtype=F64))
    return torch.stack(pts)


def selftest(ch, n=200, seed=7):
    """Float64 sanity diagnostics on deterministic special points + n random points of representative balls."""
    g = torch.Generator().manual_seed(seed)
    X_rnd = torch.randn(n, 4, generator=g, dtype=F64)
    X_rnd = X_rnd / X_rnd.norm(dim=1, keepdim=True)
    X_rnd[n // 2 :] *= torch.rand(n - n // 2, 1, generator=g, dtype=F64) ** 0.25
    X = torch.cat([special_points(), X_rnd], dim=0)
    fin, rmax, rt = True, 0.0, 0.0
    balls = sorted({0, 4, 8, 9, ch.k - 1})
    for i in balls:
        Y = ch.Embed(i, X)
        Xb, ok = ch.Preimage(i, Y)
        fin = fin and bool(torch.isfinite(Y).all()) and bool(torch.isfinite(Xb).all()) and bool(ok.all())
        rmax = max(rmax, float(torch.nan_to_num(Y.norm(dim=1), nan=float("inf")).max()))
        rt = max(rt, float(torch.nan_to_num((Xb - X).norm(dim=1), nan=float("inf")).max()))
    return dict(points=len(X), balls=balls, finite=fin, max_radius_over_R=rmax / ch.R_requested, roundtrip_max=rt)
''',
}

_RUNTIME = r"""
import sys as _sys, types as _types
import torch
torch.set_default_dtype(torch.float64)
for _name in _ORDER:
    _m = _types.ModuleType(_name)
    _m.__file__ = '/nonexistent/embedded/' + _name + '.py'
    _sys.modules[_name] = _m
    exec(compile(_SRC[_name], '<embedded ' + _name + '>', 'exec'), _m.__dict__)
_ch_mod = _sys.modules['chain']
_CH = _ch_mod.Chain3(_K, _EPS)
CONFIG = dict(
    _CH.config,
    k=_K,
    eps=_EPS,
    R_needed=_CH.R_requested,
    R_cell=_CH.R,
    R_image_bound=_CH.Rs,
    hypotheses={n: m for n, (ok, m) in _CH.hyp.items()},
    theorem='Theorem 1.1 of ' + _ch_mod.PROOF,
)
CONFIG['float64_selftest'] = _ch_mod.selftest(_CH)
_cache = {}


def Embed(i, X):
    return _CH.Embed(int(i), X.to(torch.float64))


def Preimage(j, Y):
    Y = Y.to(torch.float64)
    hit = _cache.get('Y')
    if hit is None or hit.shape != Y.shape or not torch.equal(hit, Y):
        _cache['Y'] = Y.detach().clone()
        _cache['flat'] = _CH.target_to_flat(Y)[0]
    return _CH.Preimage(int(j), Y, flat=_cache['flat'])


def STAGES(i):
    return _ch_mod.stage_dicts(_CH, int(i))
"""

_probe = {}


def _load():
    if "chain" not in _probe:
        import sys, types
        saved = {name: sys.modules.get(name) for name in _ORDER}
        try:
            for name in _ORDER:
                m = types.ModuleType(name)
                m.__file__ = "/nonexistent/embedded/" + name + ".py"
                sys.modules[name] = m
                exec(compile(_SRC[name], "<embedded " + name + ">", "exec"), m.__dict__)
            _probe["chain"] = sys.modules["chain"]
            _probe["mods"] = {name: sys.modules[name] for name in _ORDER}
        finally:
            for name, prev in saved.items():
                if prev is None:
                    sys.modules.pop(name, None)
                else:
                    sys.modules[name] = prev
    return _probe["chain"]


def solution(k, eps):
    if int(k) != k or k < 10 or not (0.0 < float(eps) < 1.0):
        raise ValueError("need an integer k >= 10 and 0 < eps < 1")
    k = int(k)
    eps = float(eps)
    _load().Chain3(k, eps)  # raises ValueError if any float64 hypothesis margin fails
    return ("_K = %d\n_EPS = %r\n_ORDER = %r\n_SRC = %r\n" % (k, eps, _ORDER, _SRC)) + _RUNTIME
