"""Elementary smooth steps, periodic bumps, polar helpers, and safeguarded scalar root-finding.

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
