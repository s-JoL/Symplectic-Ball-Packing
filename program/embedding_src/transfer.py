"""Closed-form transfer K_post = b_{ball, kappa} o W_{noKH} o Band from the post chart into B(1).

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
