"""Sampling checks of an explicit packing given as embeddings (solution_embedding.py).

solution(k, eps) returns Python source defining Embed(i, X) -> Y and Preimage(j, Y) -> (X, ok) (see that file).
Nothing is integrated; every check is evaluated on random samples:
  A containment   images of points on and inside each unit ball satisfy |Y| < R = (k / (1 - eps))^(1/4).
  B symplecticity the Jacobian J (central differences at h and h/2, Richardson) satisfies J^T Omega J = Omega; reported
                  as max |J^T Omega J - Omega| / max(1, |J|^2), with the difference of the two step sizes.
  C round trip    Preimage(i, Embed(i, X)) is found (ok) and within rt_tol of X.
  D disjointness  no image point of ball i is in the image of another ball j ("in": ok, |X_j| <= 1 and
                  |Embed(j, X_j) - Y| <= cert_tol).
  E volume        M uniform points in B(R): none may lie in two images, and the covered fraction must equal
                  k / R^4 = 1 - eps (symplectic maps preserve volume), within 4 standard errors. This catches a
                  Preimage that misses members and would hide an overlap.
  F time          total wall-clock time (default limit 3600 s).
  G continuity    A-E cannot see a map that cuts a ball into pieces and moves them separately, so Embed is checked
                  for jumps: on random chords, the intervals with the largest image gaps (absolute and relative to
                  their neighbours) are bisected to separations 1e-8 and 1e-11. A continuous map's gap shrinks; a jump
                  does not. Flagged: gap(1e-11) > 0.02 gap(1e-8) and > 1e-9. The largest gap / separation is reported
                  (a lower estimate of the local Lipschitz constant).
PASS: G flags nothing; A finite and inside; B defect <= sym_tol; C all pass; D no overlap; E no multiple membership and
coverage within 4 standard errors (+ cover_tol); F within time_limit.
In float64 a flag of G can also come from a continuous map whose local Lipschitz constant exceeds about 1e11 (the
interval cannot be resolved at separation 1e-11); README.md explains how such flags were examined in higher precision.

    python check_embedding.py solution_embedding.py --k 10 --eps 0.1 --h 1e-7
"""
import argparse, importlib.util, json, math, os, shutil, sys, tempfile, time, types
import torch


torch.set_default_dtype(torch.float64)
OMEGA = torch.tensor([[0., 0., 1., 0.], [0., 0., 0., 1.], [-1., 0., 0., 0.], [0., -1., 0., 0.]])


def load_solution(path):
    """Load the submission from an empty temporary directory, so that it cannot read neighbouring files."""
    tmp = tempfile.mkdtemp(prefix="packing_submission_")
    path = shutil.copy(path, os.path.join(tmp, "solution.py"))
    os.chdir(tmp)
    spec = importlib.util.spec_from_file_location("submission", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.solution


def load_pair(src):
    m = types.ModuleType("embedding_module")
    exec(compile(src, "<embedding>", "exec"), m.__dict__)
    assert hasattr(m, "Embed") and hasattr(m, "Preimage"), "the source must define Embed and Preimage"
    return m.Embed, m.Preimage


def unit_samples(N, N_int, seed):
    g = torch.Generator().manual_seed(seed)
    s = torch.randn(N, 4, generator=g); s = s / s.norm(dim=1, keepdim=True)
    b = torch.randn(N_int, 4, generator=g); b = b / b.norm(dim=1, keepdim=True)
    b = b * torch.rand(N_int, 1, generator=g) ** 0.25
    return s, b


def member(Embed, Preimage, j, Y, cert_tol):
    X, ok = Preimage(j, Y)
    ok = ok.clone() & torch.isfinite(X).all(dim=1)
    ok &= (X.norm(dim=1) <= 1.0)
    if ok.any():
        idx = ok.nonzero().squeeze(1)
        back = Embed(j, X[idx])
        good = torch.isfinite(back).all(dim=1) & ((back - Y[idx]).norm(dim=1) <= cert_tol)
        ok[idx[~good]] = False
    return ok


def jac_fd(Embed, i, X, h):
    cols = []
    for a in range(4):
        e = torch.zeros(4); e[a] = h
        cols.append((Embed(i, X + e) - Embed(i, X - e)) / (2 * h))
    return torch.stack(cols, dim=2)  # (n, 4, 4): d Y_r / d X_a


def continuity_check(Embed, i, n_ch, m, top, seed):
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
    sepv = (hi - lo).norm(dim=1)
    bad = ~((gap_fine <= 0.02 * gap_mid) | (gap_fine <= 1e-9)) | ~torch.isfinite(gap_fine)
    return int(bad.sum()), float(gap_fine.max()), float((gap_fine / sepv).max()), float(d.max())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("solution")
    ap.add_argument("--k", type=int, default=10)
    ap.add_argument("--eps", type=float, default=0.1)
    ap.add_argument("--N", type=int, default=500, help="sample points on each unit sphere")
    ap.add_argument("--N-int", type=int, default=500, help="sample points inside each unit ball")
    ap.add_argument("--N-jac", type=int, default=100, help="Jacobian points per ball (half on the sphere, half inside; shrunk to radius <= 1 - 3h)")
    ap.add_argument("--M", type=int, default=200000, help="random points of the volume check")
    ap.add_argument("--h", type=float, default=1e-5)
    ap.add_argument("--chords", type=int, default=100, help="G: random chords per ball (0 = skip G)")
    ap.add_argument("--chord-pts", type=int, default=3000, help="G: points per chord")
    ap.add_argument("--sym-tol", type=float, default=1e-5)
    ap.add_argument("--rt-tol", type=float, default=1e-7)
    ap.add_argument("--cert-tol", type=float, default=1e-6)
    ap.add_argument("--cover-tol", type=float, default=0.0)
    ap.add_argument("--time-limit", type=float, default=3600.0)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    torch.set_num_threads(a.threads)
    if a.json:
        a.json = os.path.abspath(a.json)
    t_all = time.time()
    sol = load_solution(os.path.abspath(a.solution))
    src = sol(a.k, a.eps)
    t_sol = time.time() - t_all
    Embed, Preimage = load_pair(src)
    k = a.k
    R_need = (k / (1 - a.eps)) ** 0.25
    log = lambda s: print(s, flush=True)
    log(f"k={k} eps={a.eps} R_needed={R_need:.6f}  per ball: {a.N} on the sphere + {a.N_int} inside, Jacobian {a.N_jac}; volume check {a.M} points; solution() {t_sol:.1f}s")
    S, B = unit_samples(a.N, a.N_int, a.seed)
    X0 = torch.cat([S, B], dim=0)
    res = dict(k=k, eps=a.eps, R_needed=R_need)
    # A, C
    Ys, R_max, finite, rt_max, rt_bad = [], 0.0, True, 0.0, 0
    for i in range(k):
        Y = Embed(i, X0).detach()
        Ys.append(Y)
        finite &= bool(torch.isfinite(Y).all())
        R_max = max(R_max, float(Y.norm(dim=1).max()))
        Xb, ok = Preimage(i, Y)
        d = (Xb - X0).norm(dim=1)
        bad = (~ok) | ~torch.isfinite(d) | (d > a.rt_tol)
        rt_bad += int(bad.sum())
        if (~bad).any():
            rt_max = max(rt_max, float(d[~bad].max()))
    res.update(R_origin=R_max, margin=R_need - R_max, finite=finite, roundtrip_bad=rt_bad, roundtrip_max=rt_max)
    log(f"A containment: R_origin = {R_max:.6f}, margin {R_need - R_max:.3e}, finite = {finite}")
    log(f"C round trip: failed {rt_bad} / {k * X0.shape[0]}, largest error among the others {rt_max:.3e}")
    # B
    sym_max, fd_max = 0.0, 0.0
    nj = max(2, a.N_jac)
    for i in range(k):
        Xj = torch.cat([S[: nj // 2] * (1 - 3 * a.h), B[: nj - nj // 2] * (1 - 3 * a.h)], dim=0)
        J1 = jac_fd(Embed, i, Xj, a.h); J2 = jac_fd(Embed, i, Xj, a.h / 2)
        J = (4 * J2 - J1) / 3
        D = J.transpose(1, 2) @ OMEGA @ J - OMEGA
        nrm = J.flatten(1).norm(dim=1).pow(2).clamp_min(1.0)
        sym_max = max(sym_max, float((D.flatten(1).abs().max(dim=1).values / nrm).max()))
        fd_max = max(fd_max, float(((J2 - J1).flatten(1).abs().max(dim=1).values / nrm.sqrt()).max()))
    res.update(sym_defect=sym_max, fd_resolution=fd_max)
    log(f"B symplecticity: largest defect {sym_max:.3e} (difference of the two step sizes / |J|: {fd_max:.3e})")
    # G
    g_bad, g_gap, g_lip, g_coarse = 0, 0.0, 0.0, 0.0
    if a.chords > 0:
        for i in range(k):
            nb_, gp_, lp_, dc_ = continuity_check(Embed, i, a.chords, a.chord_pts, 40, a.seed + 1000 + i)
            g_bad += nb_; g_gap = max(g_gap, gp_); g_lip = max(g_lip, lp_); g_coarse = max(g_coarse, dc_)
        log(f"G continuity: flagged intervals {g_bad}; largest image gap at separation 1e-11 {g_gap:.3e}; largest Lipschitz estimate {g_lip:.3e}; largest neighbour gap on the coarse grid {g_coarse:.3e}")
    res.update(cont_bad=g_bad, cont_gap_fine=g_gap, cont_lipschitz=g_lip)
    # D
    overlaps = 0
    for i in range(k):
        for j in range(k):
            if j != i:
                overlaps += int(member(Embed, Preimage, j, Ys[i], a.cert_tol).sum())
    res.update(overlap_points=overlaps)
    log(f"D disjointness: image points in another ball {overlaps} / {k * (k - 1) * X0.shape[0]} tests")
    # E
    g = torch.Generator().manual_seed(a.seed + 99)
    P = torch.randn(a.M, 4, generator=g); P = P / P.norm(dim=1, keepdim=True)
    P = P * R_need * torch.rand(a.M, 1, generator=g) ** 0.25
    mult = torch.zeros(a.M, dtype=torch.long)
    for j in range(k):
        mult += member(Embed, Preimage, j, P, a.cert_tol).long()
    cov = float((mult >= 1).double().mean()); multi = int((mult >= 2).sum())
    se = math.sqrt(max(cov * (1 - cov), 1e-12) / a.M)
    res.update(cover=cov, cover_expected=1 - a.eps, cover_se=se, multi_member=multi)
    log(f"E volume: covered fraction {cov:.5f} +- {se:.5f} (expected {1 - a.eps:.5f}), points in two or more balls {multi}")
    wall = time.time() - t_all
    res.update(wall_s=wall)
    log(f"F time: {wall:.0f} s")
    ok = (g_bad == 0 and finite and R_max < R_need and sym_max <= a.sym_tol and rt_bad == 0 and overlaps == 0 and multi == 0
          and abs(cov - (1 - a.eps)) <= 4 * se + a.cover_tol and wall <= a.time_limit)
    res["pass"] = bool(ok)
    log("RESULT " + json.dumps(res))
    log("PASS" if ok else "FAIL")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=1)


if __name__ == "__main__":
    main()
