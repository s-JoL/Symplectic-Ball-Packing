"""EXPERIMENTAL / UNFINISHED RESEARCH PROTOTYPE: multi-stage Hamiltonian-lift exploration (`solution_hamiltonian.py`).

STATUS: Experimental / Unfinished — NOT a passed or certified deliverable (do NOT cite as a verified global C^3
Hamiltonian implementation; see experiments/hamiltonian_lift/README.md and DIAGNOSTICS.md).

Generated deterministically from program/embedding_src/ and experiments/hamiltonian_lift/hamiltonian_src/ by
experiments/hamiltonian_lift/build_hamiltonian.py. Explores lifting Paper IV's closed-form C^4 symplectic packing
chain (`Chain3`, paper/p4/main.pdf, Section 8) into Epoch AI's `Hamiltonian(Q, P, t)` PyTorch float64 interface.

Interface:
    solution(k, eps) returns self-contained Python source defining
        Hamiltonian(Q, P, t) -> H            Epoch AI interface: Q, P of shape (N, 2) in torch.float64, scalar float t
                                             (also accepts per-row 1D tensor t of shape (N,) for multi-rate solvers);
                                             returns H of shape (N,) in torch.float64. Spatial vector field
                                             (dQ/dt, dP/dt) = (+dH/dP, -dH/dQ) is computed via torch.autograd.grad.
        CONFIG                               parameters, analytic margins of (H0)-(H15), stage breaks, and support radius.
        Embed(i, X) / Preimage(j, Y)         underlying Paper IV time-1 closed-form symplectic maps (with experimental
                                             parameter overrides when selected by GeneralPackingHamiltonian).
        ExactTrajectory(t, X_local, i)       candidate isotopy curve gamma_t^{(i)}(X_local) on |X_local| <= 1.
        ExactTrajectoryAndVelocity(t, X, i)  candidate (gamma_t^{(i)}(X), d/dt gamma_t^{(i)}(X)) diagnostic
                                             (six-point Gauss-Legendre integral evaluation for 0 < rho <= 1e-4).
    Coordinates (q1, q2, p1, p2) with Q = (q1, q2), P = (p1, p2), omega_0 = dq1 ^ dp1 + dq2 ^ dp2;
    initial unit balls are centred at (3*i, 0, 0, 0) for i = 0..k-1, and target radius is R = (k / (1 - eps))^(1/4).

Scope and known limitations (see README.md & DIAGNOSTICS.md):
  * Paper IV, Proposition 8.1 proves the radial-collar Liouville generator formula in terms of the global radial
    Poincare primitive and abstract ODE trajectory certificates (also formalised abstractly in Lean 4 in
    verification/RK4Convergence.lean); neither Paper IV nor Lean 4 certifies this 6-stage prototype or its modified
    implementation parameters, sampled collar radii, autograd patches, or finite ray-bisection sheet unwrapping.
  * In Stages 0-4, collar radii, tau, and 4D translation lift amplitudes are selected by finite directional/time
    sampling heuristics rather than analytic all-(k, eps) disjointness bounds; only Stage 5's open-ball image
    disjointness follows from dividing f_i(B^0(r_dom)) by v > 0.
  * In Stages 9-11 (`Transfer3`), straight radial ray unwrapping exhibits unresolved integer-turn scalar jumps across
    cutoff collars near small |Z_0| (e.g. k = 12, eps = 0.001, ball 11 in repro_branch_jump.py and
    logs/current_honest_check.log), in addition to the local seam-constant discrepancy recorded in DIAGNOSTICS.md.
"""
_ORDER = ['primitives', 'keyhole', 'comparator', 'twists', 'transfer', 'chain', 'h_primitives', 'chain_primitive', 'hamiltonian_general']

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
    'h_primitives': r'''"""Autograd-safe C-infinity bump/step functions and Gauss-Legendre utilities in PyTorch."""
from __future__ import annotations

import math
import torch


def flat_step(x: torch.Tensor) -> torch.Tensor:
    """Autograd-safe C^inf flat step S(x) on R with S=0 on (-inf,0] and S=1 on [1,+inf).

    Uses the reflection identity S(x) = 1 - S(1 - x) on x >= 1/2 and safe interior
    clamping BEFORE evaluating 1/x and exp(...) so PyTorch backward never produces
    0 * inf = NaN at the boundary seams x <= 0 or x >= 1.
    """
    interior = (x > 1e-12) & (x < 1.0 - 1e-12)
    # Clamp strictly inside (0, 1) so inactive autograd branches remain finite
    xc = torch.clamp(x, min=1e-12, max=1.0 - 1e-12)
    # Use log-space difference delta = 1/(1-x) - 1/x; S(x) = sigmoid(delta) = 1/(1 + exp(-delta))
    # Note: -delta = 1/x - 1/(1-x). Clamping -delta to [-700, 700] avoids exp overflow cleanly!
    neg_delta = torch.clamp(1.0 / xc - 1.0 / (1.0 - xc), min=-700.0, max=700.0)
    s_in = 1.0 / (1.0 + torch.exp(neg_delta))
    return torch.where(interior, s_in, torch.where(x >= 1.0 - 1e-12, torch.ones_like(x), torch.zeros_like(x)))


def flat_step_jet(x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Return (S(x), S'(x), S''(x)) in an autograd-safe vectorized form."""
    interior = (x > 1e-12) & (x < 1.0 - 1e-12)
    xc = torch.clamp(x, min=1e-12, max=1.0 - 1e-12)
    omx = 1.0 - xc
    neg_delta = torch.clamp(1.0 / xc - 1.0 / omx, min=-700.0, max=700.0)
    s = 1.0 / (1.0 + torch.exp(neg_delta))
    # Use min(s, 1-s) via exp(-|neg_delta|) / (1 + exp(-|neg_delta|))^2 for catastrophic-cancellation-free S*(1-S)
    abs_d = torch.clamp(torch.abs(neg_delta), max=700.0)
    em = torch.exp(-abs_d)
    s_one_minus_s = em / ((1.0 + em) ** 2)

    kp = 1.0 / (xc * xc) + 1.0 / (omx * omx)
    kpp = -2.0 / (xc * xc * xc) + 2.0 / (omx * omx * omx)

    sp = s_one_minus_s * kp
    spp = s_one_minus_s * ((1.0 - 2.0 * s) * kp * kp + kpp)

    z = torch.zeros_like(x)
    s_out = torch.where(interior, s, torch.where(x >= 1.0 - 1e-12, torch.ones_like(x), z))
    sp_out = torch.where(interior, sp, z)
    spp_out = torch.where(interior, spp, z)
    return s_out, sp_out, spp_out


def flat_step_scalar(x: float, derivative: int = 0) -> float:
    """Fast scalar float64 evaluation of S(x), S'(x), or S''(x)."""
    if x <= 1e-13:
        return 0.0
    if x >= 1.0 - 1e-13:
        return 1.0 if derivative == 0 else 0.0
    omx = 1.0 - x
    neg_delta = 1.0 / x - 1.0 / omx
    if neg_delta > 700.0:
        return 0.0
    if neg_delta < -700.0:
        return 1.0 if derivative == 0 else 0.0
    s = 1.0 / (1.0 + math.exp(neg_delta))
    if derivative == 0:
        return s
    em = math.exp(-abs(neg_delta))
    prod = em / ((1.0 + em) ** 2)
    kp = 1.0 / (x * x) + 1.0 / (omx * omx)
    if derivative == 1:
        return prod * kp
    kpp = -2.0 / (x * x * x) + 2.0 / (omx * omx * omx)
    if derivative == 2:
        return prod * ((1.0 - 2.0 * s) * kp * kp + kpp)
    raise ValueError(f"Unsupported scalar derivative order: {derivative}")


def gauss_legendre_01(n: int = 32) -> tuple[torch.Tensor, torch.Tensor]:
    """Return (nodes, weights) of n-point Gauss-Legendre quadrature on [0, 1] in float64."""
    # Golub-Welsch tridiagonal eigenvalue algorithm in pure torch.float64
    idx = torch.arange(1, n, dtype=torch.float64)
    beta = idx / torch.sqrt(4.0 * idx * idx - 1.0)
    J = torch.diag(beta, 1) + torch.diag(beta, -1)
    evals, evecs = torch.linalg.eigh(J)
    nodes = 0.5 * (evals + 1.0)
    weights = evecs[0, :] ** 2
    return nodes, weights
''',
    'chain_primitive': r'''"""Experimental local potential evaluator and autograd patches for the unfinished Hamiltonian-lift prototype.

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
''',
    'hamiltonian_general': r'''"""Experimental / unfinished 6-stage PyTorch Hamiltonian prototype `H(Q, P, t)` (NOT a certified deliverable).

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
''',
}

_RUNTIME = r"""
import sys as _sys, types as _types
import torch
torch.set_default_dtype(torch.float64)
_saved_mods = {_n: _sys.modules.get(_n) for _n in _ORDER}
try:
    for _name in _ORDER:
        _m = _types.ModuleType(_name)
        _m.__file__ = '/nonexistent/embedded/' + _name + '.py'
        _sys.modules[_name] = _m
        exec(compile(_SRC[_name], '<embedded ' + _name + '>', 'exec'), _m.__dict__)
    _hg_mod = _sys.modules['hamiltonian_general']
    _H_OBJ = _hg_mod.GeneralPackingHamiltonian(_K, _EPS)
finally:
    for _name, _prev in _saved_mods.items():
        if _prev is None:
            _sys.modules.pop(_name, None)
        else:
            _sys.modules[_name] = _prev

_CH = _H_OBJ.cp.ch
CONFIG = dict(
    _CH.config,
    k=_K,
    eps=_EPS,
    R_needed=_H_OBJ.R_needed,
    R_cell=_CH.R,
    R_image_bound=_CH.Rs,
    r_domain=_H_OBJ.r_dom,
    tau=_H_OBJ.tau,
    support_radius=_H_OBJ.support_radius,
    t_breaks=list(_H_OBJ.T_BREAKS),
    hypotheses={n: m for n, (ok, m) in _CH.hyp.items()},
    theorem='Theorem 1.1 of ' + _CH.config['proof'],
)


def Hamiltonian(Q, P, t):
    if not torch.is_tensor(t):
        t = float(t)
    return _H_OBJ(Q.to(torch.float64), P.to(torch.float64), t)


def Embed(i, X):
    return _CH.Embed(int(i), X.to(torch.float64))


def Preimage(j, Y):
    return _CH.Preimage(int(j), Y.to(torch.float64))


def ExactTrajectory(t, X_local, i):
    return _H_OBJ.exact_trajectory(float(t), X_local.to(torch.float64), int(i))


def ExactTrajectoryAndVelocity(t, X_local, i):
    return _H_OBJ.exact_trajectory_and_velocity(float(t), X_local.to(torch.float64), int(i))
"""

_probe = {}


def _load():
    if "chain" not in _probe:
        import sys, types
        saved = {name: sys.modules.get(name) for name in _ORDER}
        try:
            for name in _ORDER[:6]:
                m = types.ModuleType(name)
                m.__file__ = "/nonexistent/embedded/" + name + ".py"
                sys.modules[name] = m
                exec(compile(_SRC[name], "<embedded " + name + ">", "exec"), m.__dict__)
            _probe["chain"] = sys.modules["chain"]
        finally:
            for name, prev in saved.items():
                if prev is None:
                    sys.modules.pop(name, None)
                else:
                    sys.modules[name] = prev
    return _probe["chain"]


def solution(k, epsilon):
    if isinstance(k, bool) or int(k) != k or k < 10 or not (0.0 < float(epsilon) < 1.0):
        raise ValueError("need an integer k >= 10 and 0 < epsilon < 1")
    k = int(k)
    epsilon = float(epsilon)
    _load().Chain3(k, epsilon)  # raises ValueError if any float64 hypothesis margin (H0)-(H15) fails
    return ("_K = %d\n_EPS = %r\n_ORDER = %r\n_SRC = %r\n" % (k, epsilon, _ORDER, _SRC)) + _RUNTIME
