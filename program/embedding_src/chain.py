"""Assembled closed-form C^4 packing chain Chain3, analytic hypothesis checks (H0)-(H15), and self-test.

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
