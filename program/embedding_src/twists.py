"""Deck-equivariant C^4 toric twists Psi = Phi_g o Psi_S routing the three marked fibres into the free corridor.

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
