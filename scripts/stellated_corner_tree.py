#!/usr/bin/env python3
"""Build the 36 corner blow-up tables in the exact Lean format.

Every accepted leaf is checked by an exact mirror of the Lean checkers
(`CornerCertificate.Row.Valid`, `CornerTree.Leaf.Valid`,
`CornerHandoff.HandoffValid`), and the output is the packed stream read by
`PackedCornerTree.decodeTables`.

    stellated_corner_tree.py OUTDIR [--eps0 1/8] [--jobs 14] [--max-boxes N]
"""
import argparse
import itertools
import json
import math
import multiprocessing
import os
import random
import sys
import time
from fractions import Fraction
from fractions import Fraction as Q
import os as _os
if _os.environ.get("CORNER_GMPY2", "1") != "0":
    # gmpy2.mpq: same exact rationals, several times faster than Fraction;
    # Lean re-checks every emitted row either way
    from gmpy2 import mpq as Q  # noqa: F811
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import stellated_corner as sc  # noqa: E402
import stellated_corner_search as cs  # noqa: E402

KINDS = ("plain", "tube", "wedge", "wtube", "skew", "atube", "btube+", "btube-",
         "askew", "bskew+", "bskew-", "aplain", "bplain+", "bplain-")
PLAIN_A_KINDS = ("aplain", "bplain+", "bplain-")
SKEW_KINDS = ("skew", "askew", "bskew+", "bskew-")
RHO_KINDS = ("tube", "atube", "btube+", "btube-")
AMODE = {"atube": "eps", "btube+": "+", "btube-": "-",
         "askew": "eps", "bskew+": "+", "bskew-": "-",
         "aplain": "eps", "bplain+": "+", "bplain-": "-"}
RHO0, ALPHA0, ETA0 = Q(1, 16), Q(1, 8), Q(1, 8)
TAU0, TAU1, SIGMA0 = Q(1, 8), Q(3, 4), Q(1, 16)
SKEW_K = cs.SKEW_K
SKEW_B0, SKEW_B1, SKEW_DELTA = Q(1, 64), Q(5, 12), Q(1, 8)


def face_sign(k):
    return Q(1) if k % 2 == 0 else Q(-1)


# ---------------------------------------------------------------------------
# root frames (mirror `CornerHandoff`)

def plain_root(e0, face):
    if face == 0:
        return ([e0 / 2, Q(1), Q(1, 2), Q(0), Q(0), Q(0)],
                [e0 / 2, Q(0), Q(1, 2), Q(1), Q(1), Q(1)])
    k = face - 1
    c = [e0 / 2, Q(1, 2), Q(1, 2), Q(0), Q(0), Q(0)]
    r = [e0 / 2, Q(1, 2), Q(1, 2), Q(1), Q(1), Q(1)]
    c[3 + k // 2], r[3 + k // 2] = face_sign(k), Q(0)
    return c, r


def tube_root(e0, face):
    c = [e0 / 2, Q(1), Q(1, 2), Q(0), Q(0), Q(0), RHO0 / 2]
    r = [e0 / 2, Q(0), Q(1, 2), Q(1), Q(1), Q(1), RHO0 / 2]
    c[3 + face // 2], r[3 + face // 2] = face_sign(face), Q(0)
    return c, r


def wedge_root(e0):
    return ([e0 / 2, Q(1), Q(1, 2), Q(0), (TAU0 + TAU1) / 2, Q(0)],
            [e0 / 2, Q(0), Q(1, 2), ALPHA0, (TAU1 - TAU0) / 2, ETA0])


def wtube_root(e0, face):
    c = [e0 / 2, Q(1), Q(1, 2), Q(0), (TAU0 + TAU1) / 2, Q(0), SIGMA0 / 2]
    r = [e0 / 2, Q(0), Q(1, 2), Q(1), (TAU1 - TAU0) / 2, Q(1), SIGMA0 / 2]
    v = 3 + 2 * (face // 2)
    c[v], r[v] = face_sign(face), Q(0)
    return c, r


def skew_root(e0):
    return ([e0 / 2, Q(1), Q(1, 2), Q(0), (SKEW_B0 + SKEW_B1) / 2, Q(0)],
            [e0 / 2, Q(0), Q(1, 2), Q(1), (SKEW_B1 - SKEW_B0) / 2, SKEW_DELTA])


def zero_root(e0, face):
    c = [e0 / 2, Q(0), Q(0), Q(0), Q(0), Q(0)]
    r = [e0 / 2, Q(0), Q(0), Q(1), Q(1), Q(1)]
    c[3 + face // 2], r[3 + face // 2] = face_sign(face), Q(0)
    return c, r


def all_roots(e0):
    """(seg, kind, center, radius) in `PackedCornerTree.tablesOf` order."""
    out = []
    for seg in (False, True):
        out += [(seg, "plain") + plain_root(e0, f) for f in range(7)]
        out += [(seg, "tube") + tube_root(e0, f) for f in range(6)]
        out += [(seg, "wedge") + wedge_root(e0)]
        out += [(seg, "wtube") + wtube_root(e0, f) for f in range(4)]
    out += [(True, "skew") + skew_root(e0)]
    out += [(False, "plain") + zero_root(e0, f) for f in range(6)]
    out += [(False, "cone") + cone_root(e0) for k in range(16)]
    for k in range(3):
        for m in range(3):
            out += [(POCKETS[k][0], POCKET_KINDS[m]) + pocket_root(e0, k, m)]
    for m in range(3):
        out += [(True, ("askew", "bskew+", "bskew-")[m]) + spocket_root(e0, m)]
    for k in range(2):
        for m in range(3):
            out += [(PPOCKETS[k][0], PLAIN_A_KINDS[m]) + ppocket_root(e0, k, m)]
    for face in range(2):
        for m in range(3):
            out += [(False, POCKET_KINDS[m]) + tpocket_root(e0, face, m)]
    for m in range(3):       # 83..85: the c < 0 plain pocket on segment B
        out += [(PPOCKETS[2][0], PLAIN_A_KINDS[m]) + ppocket_root(e0, 2, m)]
    return out


# tie pockets reached from cone frames (mirror `tpocketRoot`): the tube faces
# b = +1 (face 0, c in [0, 1]) and c = +1 (face 1, b in [0, 1]) for
# u in [9/11, 9/11 + 1/64]
TPOCKET_DU = Q(1)      # mirror `tpocketDU`: stellar sub-cones near the pocket line reach past u = 1
TPOCKET_W = Q(1)       # mirror `tpocketW`: the tie pockets' a-range, |a| <= W rho


def tpocket_var3(m):
    a = cs.ATUBE_A
    return [(-a, a), (Q(0), TPOCKET_W), (-TPOCKET_W, Q(0))][m]


def tpocket_root(e0, face, m):
    w0, w1 = tpocket_var3(m)
    h = Q(1, 2)
    v4, v5 = ((Q(1), Q(0)), (h, h)) if face == 0 else ((h, h), (Q(1), Q(0)))
    c = [e0 / 2, Q(1), CONE_TIE + TPOCKET_DU / 2, (w0 + w1) / 2, v4[0], v5[0], RHO0 / 2]
    r = [e0 / 2, Q(0), TPOCKET_DU / 2, (w1 - w0) / 2, v4[1], v5[1], RHO0 / 2]
    return c, r


def aff_poly(row):
    return sc.p_add(sc.p_const(row[0]),
                    *[sc.p_var(k + 2, row[k + 1]) for k in range(4) if row[k + 1] != 0])


def cpocket_ineqs(aff):
    """Mirror of `cpocketIneqs`: the cone frame's points have u in the tie
    pocket range, 0 <= b, c <= rho0, and |a| <= TPOCKET_W (b + c) / 2."""
    U, A, B, C = (aff_poly(row) for row in aff)
    neg = lambda p: sc.p_scale(p, -1)
    S = sc.p_scale(sc.p_add(B, C), TPOCKET_W / 2)
    return [sc.p_add(U, sc.p_const(-CONE_TIE)), sc.p_add(sc.p_const(CONE_TIE + TPOCKET_DU), neg(U)),
            B, C, sc.p_add(sc.p_const(RHO0), neg(B)), sc.p_add(sc.p_const(RHO0), neg(C)),
            sc.p_add(S, A), sc.p_add(S, neg(A))]


def cpocket_ok(aff, centers, radii, e0):
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]
    if not (aff and len(aff) == 4 and len(centers) == 6 and lo[1] == 1 and hi[1] == 1 and
            lo[0] >= 0 and hi[0] <= e0):
        return False
    sc.set_nvars(6)
    return all(nonneg_ok(q, centers, radii) for q in cpocket_ineqs(aff))


# plain pockets: (segment, u0, u1) — mirror `ppocketSpec`
# (segment, u0, u1, c center): c in [center - 31/64, center + 31/64]
PPOCKETS = [(True, Q(0), Q(1), Q(33, 64)), (False, Q(9, 11) + Q(1, 64), Q(1), Q(33, 64)),
            (True, Q(0), Q(1), Q(-33, 64))]


def ppocket_root(e0, k, m):
    seg, u0, u1, cc = PPOCKETS[k]
    w0, w1 = pocket_var3(m)
    return ([e0 / 2, Q(1), (u0 + u1) / 2, (w0 + w1) / 2, Q(1, 2), cc],
            [e0 / 2, Q(0), (u1 - u0) / 2, (w1 - w0) / 2, Q(1, 2), Q(31, 64)])


def spocket_root(e0, m):
    w0, w1 = pocket_var3(m)
    return ([e0 / 2, Q(1), Q(1, 2), (w0 + w1) / 2, (SKEW_B0 + SKEW_B1) / 2, Q(0)],
            [e0 / 2, Q(0), Q(1, 2), (w1 - w0) / 2, (SKEW_B1 - SKEW_B0) / 2, SKEW_DELTA])


# pockets: a ~ eps on the tube faces c = +-1 near b = 9/22 (mirror `CornerHandoff`)
POCKET_B0, POCKET_B1, POCKET_W = Q(9, 22) - Q(1, 32), Q(1), Q(1, 64)
POCKET_KINDS = ("atube", "btube+", "btube-")


def pockets():
    tie, du = Q(9, 11), Q(1, 64)
    return [(False, 4, tie + du, Q(1)), (True, 4, Q(0), Q(1)), (True, 5, Q(0), Q(1))]


POCKETS = pockets()


def pocket_var3(m):
    a = cs.ATUBE_A
    return [(-a, a), (Q(0), POCKET_W), (-POCKET_W, Q(0))][m]


def pocket_root(e0, k, m):
    seg, face, u0, u1 = pockets()[k]
    w0, w1 = pocket_var3(m)
    c = [e0 / 2, Q(1), (u0 + u1) / 2, (w0 + w1) / 2, (POCKET_B0 + POCKET_B1) / 2,
         face_sign(face), RHO0 / 2]
    r = [e0 / 2, Q(0), (u1 - u0) / 2, (w1 - w0) / 2, (POCKET_B1 - POCKET_B0) / 2,
         Q(0), RHO0 / 2]
    return c, r


# cone charts at the view tie u = 9/11 of segment A (mirror `CornerHandoff`)
CONE_TIE, CONE_DU, CONE_R = Q(9, 11), Q(1, 64), Q(1, 16)


def cone_aff(k):
    sg = [Q(-1) if (k >> b) & 1 else Q(1) for b in range(4)]
    z = Q(0)
    return [[CONE_TIE, sg[0] * CONE_DU, z, z, z],
            [z, z, sg[1] * CONE_R, z, z],
            [z, z, z, sg[2] * CONE_R, z],
            [z, z, z, z, sg[3] * CONE_R]]


def cone_root(e0):
    h = Q(1, 2)
    return [e0 / 2, Q(1), h, h, h, h], [e0 / 2, Q(0), h, h, h, h]


def root_aff(index):
    return cone_aff(index - 43) if 43 <= index < 59 else []  # pockets: none


def stellar_aff(aff, i, j, al, be):
    """Mirror of `stellarAff`: column j becomes al * column i + be * column j."""
    return [[al * row[i - 1] + be * row[j - 1] if k == j - 1 else row[k]
             for k in range(5)] for row in aff]


def stellar_frame(c, r, aff, i, j, al, be):
    """Mirror of `Frame.stellar`."""
    hi = [ci + ri for ci, ri in zip(c, r)]
    top = min(hi[i] / al, hi[j] / be)
    c2, r2 = list(c), list(r)
    c2[j], r2[j] = top / 2, top / 2
    return c2, r2, stellar_aff(aff, i, j, al, be)


# ---------------------------------------------------------------------------
# exact mirrors of the Lean checks

def normalize(p):
    return {e: c for e, c in p.items() if c != 0}


_BINOM = np.array([[math.comb(n, k) for k in range(64)] for n in range(64)], dtype=float)


def _fshift(E, C, a, b):
    """Float Taylor shift `x_i = a_i + b_i u_i` of the polynomial (E, C);
    returns (is-constant mask, merged coefficients)."""
    for i in range(E.shape[1]):
        k = E[:, i]
        if not k.any() or (a[i] == 0 and b[i] == 1):
            continue
        reps = k + 1
        idx = np.repeat(np.arange(len(k)), reps)
        j = np.arange(reps.sum()) - np.repeat(np.cumsum(reps) - reps, reps)
        kk = k[idx]
        C = C[idx] * _BINOM[kk, j] * np.power(a[i], kk - j) * np.power(b[i], j)
        E = E[idx]
        E[:, i] = j
    keys = E @ (64 ** np.arange(E.shape[1], dtype=np.int64))
    uniq, inv = np.unique(keys, return_inverse=True)
    return uniq == 0, np.bincount(inv, weights=C, minlength=len(uniq))


def float_box_lower(p, centers, radii):
    """Float version of `box_lower` with an error scale."""
    E = np.array(list(p.keys()), dtype=np.int64)
    C = np.array([float(c) for c in p.values()])
    c = np.array([float(x) for x in centers])
    r = np.array([float(x) for x in radii])
    best, scale = -np.inf, 0.0
    for a, b, centered in ((c, r, True), (c - r, 2 * r, False), (c + r, -2 * r, False)):
        zero, C2 = _fshift(E, C, a, b)
        const = C2[zero].sum()
        rest = C2[~zero]
        bound = const - np.abs(rest).sum() if centered else const + rest[rest < 0].sum()
        best = max(best, bound)
        scale = max(scale, np.abs(C2).sum())
    return best, scale


if os.environ.get("CORNER_NUMBA", "1") != "0":
    try:   # compiled prefilter (6x on table 74; same screening decisions)
        from stellated_fastbound import float_box_lower  # noqa: F811
    except ImportError:
        pass

FLOAT_ONLY = False   # screening pass: float bounds with a tolerance


def box_lower(p, centers, radii):
    if not p:
        return Q(0)
    # reject-only float prefilter; acceptance is always decided exactly
    fb, scale = float_box_lower(p, centers, radii)
    tol = 1e-9 * scale + 1e-300
    if fb < -tol:
        return Q(-1)
    if FLOAT_ONLY:
        return Q(1) if fb > tol else Q(0)
    return cs.box_lower(p, centers, radii)


def strip(p, allowed):
    p = normalize(p)
    if not p:
        return p
    n = len(next(iter(p)))
    common = [min(e[v] for e in p) if allowed(v) else 0 for v in range(n)]
    if not any(common):
        return p
    return {tuple(a - b for a, b in zip(e, common)): c for e, c in p.items()}


def pin_poly(p, centers, radii):
    """Mirror of `pinPoly box.pin`: set the box's fixed variables."""
    out = {}
    for e, c in p.items():
        coef = Q(c)
        e2 = list(e)
        for v, k in enumerate(e):
            if k and v < len(radii) and radii[v] == 0:
                coef *= Q(centers[v]) ** k
                e2[v] = 0
        key = tuple(e2)
        out[key] = out.get(key, 0) + coef
    return normalize(out)


def _nonneg0(p, centers, radii):
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]
    q = strip(p, lambda v: v < len(lo) and lo[v] >= 0 and hi[v] > 0)
    return box_lower(q, centers, radii) >= 0


def nonneg_ok(p, centers, radii):
    """Mirror of `NonnegOk`: directly, or after pinning fixed variables."""
    return (_nonneg0(p, centers, radii) or
            (any(r == 0 for r in radii) and _nonneg0(pin_poly(p, centers, radii), centers, radii)))


def _pos0(p, centers, radii, tube):
    lo = [c - r for c, r in zip(centers, radii)]
    hi1 = centers[1] + radii[1]
    q = strip(p, lambda v: v < len(lo) and
              (v == 0 or (tube and v == 6) or (v == 1 and hi1 > 0))
              and lo[v] >= 0)
    return box_lower(q, centers, radii) > 0


def pos_ok(p, centers, radii, tube):
    """Mirror of `PosOk r.positiveVars`: eps, rho in a tube, and lambda when
    the box reaches lambda > 0 (Covered then supplies lambda > 0); directly or
    after pinning fixed variables."""
    return (_pos0(p, centers, radii, tube) or
            (any(r == 0 for r in radii) and
             _pos0(pin_poly(p, centers, radii), centers, radii, tube)))


def split_parts(F, vars_):
    parts = []
    rest = dict(F)
    for v in vars_:
        part, keep = {}, {}
        for e, c in rest.items():
            if e[v] >= 1:
                e2 = list(e)
                e2[v] -= 1
                part[tuple(e2)] = part.get(tuple(e2), 0) + c
            else:
                keep[e] = c
        parts.append(part)
        rest = keep
    return parts, rest


def shift_poly(F, shift):
    """Mirror of `shiftPoly`: the polynomial `y ↦ F(shift + y)`."""
    from math import comb
    out = {}
    for e, c in F.items():
        terms = {(): c}
        for v, k in enumerate(e):
            sv = shift[v] if v < len(shift) else 0
            new = {}
            for pre, a in terms.items():
                if sv == 0 or k == 0:
                    new[pre + (k,)] = new.get(pre + (k,), 0) + a
                else:
                    for i in range(k + 1):
                        key = pre + (i,)
                        new[key] = new.get(key, 0) + a * comb(k, i) * sv ** (k - i)
            terms = new
        for key, a in terms.items():
            out[key] = out.get(key, 0) + a
    return normalize(out)


def disp_F(D, kind, lo):
    """`Row.F` (`lo` = box lower corner), or None when the base monomial
    does not divide `D`."""
    base = [1] + [0] * (len(lo) - 1)
    D = normalize(D)
    if kind in RHO_KINDS and lo[6] <= 0 and all(e[0] >= 1 and e[6] >= 1 for e in D):
        base[6] = 1
    if any(any(a < b for a, b in zip(e, base)) for e in D):
        return None
    return {tuple(a - b for a, b in zip(e, base)): c for e, c in D.items()}


def split_ok(F, centers, radii, split):
    """The split and rest checks of `Row.DispOk` for `G = F` on the box."""
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]
    for v, sign in split:
        if (sign and lo[v] < 0) or (not sign and hi[v] > 0):
            return False
    parts, rest = split_parts(F, [v for v, _ in split])
    for part, (v, sign) in zip(parts, split):
        if not nonneg_ok(part if sign else sc.p_scale(part, -1), centers, radii):
            return False
    return nonneg_ok(rest, centers, radii)


def disp_ok(D, kind, centers, radii, split, shift=()):
    """Mirror of `Row.DispOk`."""
    F = disp_F(D, kind, [c - r for c, r in zip(centers, radii)])
    if F is None:
        return False
    if shift:
        F = shift_poly(F, shift)
        centers = [c - sv for c, sv in zip(centers, shift)]
    return split_ok(F, centers, radii, split)


def candidate_splits(kind, centers, radii):
    """Split lists to try, most specific first."""
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]

    def signed(vs):
        out = []
        for v in vs:
            if lo[v] >= 0:
                out.append((v, True))
            elif hi[v] <= 0:
                out.append((v, False))
        return out
    eps = [(0, True)]
    if kind == "cone":
        out = [[], eps]
        for perm in itertools.permutations([2, 3, 4, 5]):
            out.append(signed(list(perm)) + eps)
            out.append(eps + signed(list(perm)))
        return out
    if kind == "plain" or kind in PLAIN_A_KINDS:
        return [[], signed([3]) + eps, eps]
    if kind in RHO_KINDS:
        return [[], eps, signed([3]) + eps, signed([3, 6]) + eps,
                signed([6, 3]) + eps, signed([3]) + eps + signed([6]),
                eps + signed([3, 6])]
    if kind == "wedge":
        return [[], signed([3, 5]) + eps, eps]
    if kind in SKEW_KINDS:
        return [[], signed([5, 3]) + eps, signed([3, 5]) + eps, eps]
    return [[], signed([3, 6]) + eps, signed([6]) + eps, eps]


PENDING = []   # triples whose only failing check was the displacement


# Rust float screen (rust/corner-kernel): the same checks as the FLOAT_ONLY pass
# below, with exact (i128) certificate polynomials; the exact Python pass still
# decides every acceptance.  Falls back to Python on i128 overflow (deep cone
# charts) or when CORNER_RUST=0.
_CK = None
if os.environ.get("CORNER_RUST", "1") != "0":
    try:
        import corner_kernel as _CK
    except ImportError:
        _CK = None


def _poly_py(p):
    return [(list(e), int(c.numerator), int(c.denominator)) for e, c in p.items()]


def _rust_chart(chart):
    rk = getattr(chart, "_rk", None)
    if rk is None:
        try:
            rk = _CK.Chart([_poly_py(w) for w in chart.W],
                           [[_poly_py(x) for x in row] for row in chart.N],
                           _poly_py(chart.d),
                           [[(int(Q(x).numerator), int(Q(x).denominator)) for x in v]
                            for v in sc.VQ],
                           [[(list(e), float(c)) for e, c in f.items()] for f in chart.flip])
        except OverflowError:
            rk = False
        chart._rk = rk
    return rk


def _family(kind):
    if kind == "cone":
        return 0
    if kind == "plain" or kind in PLAIN_A_KINDS:
        return 1
    if kind in RHO_KINDS:
        return 2
    if kind == "wedge":
        return 3
    if kind in SKEW_KINDS:
        return 4
    return 5


def _box_flags(centers, radii):
    out = []
    for c, r in zip(centers, radii):
        lo, hi = c - r, c + r
        out.append((lo >= 0) | (lo > 0) << 1 | (lo == 0) << 2 | (hi > 0) << 3 |
                   (hi <= 0) << 4 | (hi == 0) << 5 | (r == 0) << 6)
    return out


def _rust_screen(chart, kind, triple, centers, radii, allow_shift):
    """0 / 1 (PENDING) / 2 (passed) as the Python screen, or None to fall back."""
    rk = _rust_chart(chart) if _CK is not None else False
    if not rk:
        return None
    try:
        return rk.screen(_family(kind), kind in RHO_KINDS,
                         [tuple(int(x) for x in t) for t in triple],
                         [float(x) for x in centers], [float(x) for x in radii],
                         _box_flags(centers, radii), allow_shift)
    except OverflowError:
        chart._rk = False
        return None


def _rust_flip_mask(chart, kind, centers, radii):
    """Flips that the exact `pos_ok` could accept (the rest fail Python's own
    float prefilter on every variant), or None to check all of them."""
    rk = _rust_chart(chart) if _CK is not None else False
    if not rk or not hasattr(rk, "flip_prefilter"):
        return None
    mask = rk.flip_prefilter(kind in RHO_KINDS, [float(x) for x in centers],
                             [float(x) for x in radii], _box_flags(centers, radii))
    return mask if len(mask) == len(chart.flip) else None


def cert_valid(chart, kind, triple, centers, radii, allow_shift=False):
    """Mirror of `Row.Valid`; returns `(split, shift)` on success.  A float
    screening pass runs first; the exact pass decides."""
    global FLOAT_ONLY
    if any(r < 0 for r in radii):
        return None
    code = _rust_screen(chart, kind, triple, centers, radii, allow_shift)
    if code is not None:
        if code == 1 and not allow_shift:
            PENDING.append(triple)
        if code != 2:
            return None
        return _cert_valid(chart, kind, triple, centers, radii, allow_shift, True)
    FLOAT_ONLY = True
    try:
        screen = _cert_valid(chart, kind, triple, centers, radii, allow_shift, False)
    finally:
        FLOAT_ONLY = False
    if screen is None:
        return None
    return _cert_valid(chart, kind, triple, centers, radii, allow_shift, True)


def _cert_valid(chart, kind, triple, centers, radii, allow_shift, record):
    if any(r < 0 for r in radii):
        return None
    mus, supports, D = chart.certificate(triple)
    tube = kind in RHO_KINDS
    # mirror of `weights` / `weightsPos`: all weights >= 0, and each contact
    # has a strictly positive weight among the other two
    if not all(nonneg_ok(m, centers, radii) for m in mus):
        return None
    pos = [pos_ok(m, centers, radii, tube) for m in mus]
    if not all(any(pos[j] for j in range(3) if j != i) for i in range(3)):
        return None
    if not all(nonneg_ok(sc.p_scale(g, -1), centers, radii) for g in supports):
        return None
    F = disp_F(D, kind, [c - r for c, r in zip(centers, radii)])
    if F is None:
        return None
    for split in candidate_splits(kind, centers, radii):
        if split_ok(F, centers, radii, split):
            return split, []
    if not allow_shift:
        if not record:
            PENDING.append(triple)
        return None
    # translate one coordinate to a box face, where the displacement may
    # carry a factor like `c - 1` that interval evaluation cannot see
    for v in SHIFT_VARS:
        if v >= len(centers) or radii[v] == 0:
            continue
        for m in (centers[v] + radii[v], centers[v] - radii[v]):
            if m == 0:
                continue
            shift = [Q(0)] * len(centers)
            shift[v] = m
            G = shift_poly(F, shift)
            sc_ = [c - sv for c, sv in zip(centers, shift)]
            sign = [(v, sc_[v] - radii[v] >= 0)]
            for split in candidate_splits(kind, sc_, radii):
                for cand in (sign + split, split + sign):
                    if split_ok(G, sc_, radii, cand):
                        return cand, shift
    return None


SHIFT_VARS = (5, 4, 2, 3)


def _prechecked(chart, kind, triple, centers, radii):
    """The per-triple checks of a combination row (weights, positivity,
    gaps); returns the displacement polynomial or None."""
    mus, supports, D = chart.certificate(triple)
    tube = kind in RHO_KINDS
    if not all(nonneg_ok(m, centers, radii) for m in mus):
        return None
    pos = [pos_ok(m, centers, radii, tube) for m in mus]
    if not all(any(pos[j] for j in range(3) if j != i) for i in range(3)):
        return None
    if not all(nonneg_ok(sc.p_scale(g, -1), centers, radii) for g in supports):
        return None
    return normalize(D)


def _sample_points(centers, radii, n, rng):
    lo = [float(c - r) for c, r in zip(centers, radii)]
    hi = [float(c + r) for c, r in zip(centers, radii)]
    pts = [list(x) for x in itertools.product(*zip(lo, hi))]
    for _ in range(n):
        x = [l + rng.random() * (h - l) for l, h in zip(lo, hi)]
        if hi[0] > 0:
            x[0] = hi[0] * 10 ** rng.uniform(-8, 0)
        if len(x) > 6 and lo[6] == 0 and hi[6] > 0:
            x[6] = hi[6] * 10 ** rng.uniform(-8, 0)
        pts.append(x)
    return pts


def try_combo(chart, kind, triples, centers, radii, max_terms=4):
    """A nonnegative rational combination of valid triples whose summed
    displacement passes the `DispOk` checks; returns (terms, split, shift)."""
    from scipy.optimize import linprog
    rng = random.Random(1)
    good = []
    for tri in triples:
        D = _prechecked(chart, kind, tri, centers, radii)
        if D is not None and all(e[0] >= 1 for e in D):
            good.append((tri, D))
    if len(good) < 2:
        return None
    pts = _sample_points(centers, radii, 400, rng)
    vals = np.array([[sc.p_eval(D, x) for _, D in good] for x in pts])
    norm = np.maximum(np.abs(vals).max(axis=1), 1e-300)
    A = vals / norm[:, None]
    n = len(good)
    res = linprog(np.r_[np.zeros(n), -1.0],
                  A_ub=np.c_[-A, np.ones(len(pts))], b_ub=np.zeros(len(pts)),
                  A_eq=np.r_[np.ones(n), 0.0][None, :], b_eq=[1.0],
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    if res.status != 0 or -res.fun < -1e-9:
        return None
    theta = res.x[:n]
    order = [i for i in np.argsort(-theta) if theta[i] > 1e-7][:max_terms]
    if len(order) < 2:
        return None
    terms = [(good[i][0], Q(Fraction(float(theta[i])).limit_denominator(1 << 20))) for i in order]
    total = {}
    for (tri, w), i in zip(terms, order):
        for e, c in good[i][1].items():
            total[e] = total.get(e, 0) + w * c
    total = normalize(total)
    F = disp_F(total, kind, [c - r for c, r in zip(centers, radii)])
    if F is None:
        return None
    for split in candidate_splits(kind, centers, radii):
        if split_ok(F, centers, radii, split):
            return terms, split, []
    for v in SHIFT_VARS:
        if v >= len(centers) or radii[v] == 0:
            continue
        for m in (centers[v] + radii[v], centers[v] - radii[v]):
            if m == 0:
                continue
            shift = [Q(0)] * len(centers)
            shift[v] = m
            G = shift_poly(F, shift)
            sc_ = [c - sv for c, sv in zip(centers, shift)]
            sign = [(v, sc_[v] - radii[v] >= 0)]
            for split in candidate_splits(kind, sc_, radii):
                for cand in (sign + split, split + sign):
                    if split_ok(G, sc_, radii, cand):
                        return terms, cand, shift
    return None


def lean_triple(triple):
    """(P, A, B, Q, sigma) entries → Lean `Triple` data."""
    edges, inner, outer = [], [], []
    for P, A, B, Qv, s in triple:
        edges.append([s * (b - a) for a, b in zip(sc.VQ[A], sc.VQ[B])])
        inner.append(P)
        outer.append(Qv)
    return edges, inner, outer


def flip_ok(chart, k, centers, radii, tube):
    return pos_ok(chart.flip[k], centers, radii, tube)


def handoff_ok(h, seg, kind, centers, radii, e0):
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]
    if h == "ppocket":
        return (kind == "plain" and len(centers) == 6 and lo[1] == 1 and hi[1] == 1 and
                lo[0] >= 0 and hi[0] <= e0 and
                -POCKET_W <= lo[3] and hi[3] <= POCKET_W and lo[4] >= 0 and hi[4] <= 1 and
                any(s == seg and u0 <= lo[2] and hi[2] <= u1 and
                    cc - Q(31, 64) <= lo[5] and hi[5] <= cc + Q(31, 64)
                    for s, u0, u1, cc in PPOCKETS))
    if h == "spocket":
        return (kind == "skew" and seg and len(centers) == 6 and lo[1] == 1 and hi[1] == 1 and
                lo[0] >= 0 and hi[0] <= e0 and lo[2] >= 0 and hi[2] <= 1 and
                -POCKET_W <= lo[3] and hi[3] <= POCKET_W and SKEW_B0 <= lo[4] and
                hi[4] <= SKEW_B1 and -SKEW_DELTA <= lo[5] and hi[5] <= SKEW_DELTA)
    if h == "pocket":
        if kind != "tube" or len(centers) != 7:
            return False
        if not (lo[1] == 1 and hi[1] == 1 and lo[0] >= 0 and hi[0] <= e0 and
                -POCKET_W <= lo[3] and hi[3] <= POCKET_W and POCKET_B0 <= lo[4] and
                hi[4] <= POCKET_B1 and lo[6] >= 0 and hi[6] <= RHO0):
            return False
        return any(pseg == seg and u0 <= lo[2] and hi[2] <= u1 and
                   lo[5] == face_sign(face) and hi[5] == face_sign(face)
                   for pseg, face, u0, u1 in POCKETS)
    if h == "cone":
        if seg or kind not in ("plain", "tube"):
            return False
        if not (lo[1] == 1 and hi[1] == 1 and lo[0] >= 0 and hi[0] <= e0 and
                CONE_TIE - CONE_DU <= lo[2] and hi[2] <= CONE_TIE + CONE_DU):
            return False
        if kind == "plain":
            return all(-CONE_R <= lo[v] and hi[v] <= CONE_R for v in (3, 4, 5))
        return (all(-1 <= lo[v] and hi[v] <= 1 for v in (3, 4, 5)) and
                lo[6] >= 0 and hi[6] <= CONE_R)
    if len(centers) != 6:
        return False
    base = (lo[1] == 1 and hi[1] == 1 and lo[0] >= 0 and hi[0] <= e0 and
            lo[2] >= 0 and hi[2] <= 1)
    if not base:
        return False
    if h == "tube":
        return kind == "plain" and all(-RHO0 <= lo[v] and hi[v] <= RHO0
                                       for v in (3, 4, 5))
    if h == "skew":
        return (kind == "plain" and seg and lo[4] >= SKEW_B0 and hi[4] <= SKEW_B1 and
                -1 <= lo[3] and hi[3] <= 1 and
                lo[5] + SKEW_K * lo[4] >= -SKEW_DELTA and
                hi[5] + SKEW_K * hi[4] <= SKEW_DELTA)
    if h == "wtube":
        return (kind == "wedge" and TAU0 <= lo[4] and hi[4] <= TAU1 and
                all(-SIGMA0 <= lo[v] and hi[v] <= SIGMA0 for v in (3, 5)))
    # wedge
    if kind != "plain" or not (-ALPHA0 <= lo[3] and hi[3] <= ALPHA0):
        return False
    if any(r < 0 for r in radii):
        return False
    sc.set_nvars(6)
    s_poly = sc.p_var(1) if not seg else sc.p_mul(sc.p_var(1), sc.p_var(2))
    t_poly = (sc.p_scale(sc.p_mul(sc.p_var(1), sc.p_var(2)), -1) if not seg
              else sc.p_scale(sc.p_var(1), -1))
    norm = sc.p_add(sc.p_mul(s_poly, s_poly),
                    sc.p_scale(sc.p_mul(t_poly, t_poly), Q(1, 4)))
    tau = sc.p_add(sc.p_mul(sc.p_var(4), sc.p_scale(t_poly, Q(-1, 2))),
                   sc.p_mul(sc.p_var(5), sc.p_scale(s_poly, -1)))
    eta = sc.p_add(sc.p_mul(sc.p_var(4), s_poly),
                   sc.p_mul(sc.p_var(5), sc.p_scale(t_poly, Q(-1, 2))))
    ineqs = [sc.p_add(tau, sc.p_scale(norm, -TAU0)),
             sc.p_add(sc.p_scale(norm, TAU1), sc.p_scale(tau, -1)),
             sc.p_add(sc.p_scale(norm, ETA0), sc.p_scale(eta, -1)),
             sc.p_add(sc.p_scale(norm, ETA0), eta)]
    return all(nonneg_ok(q, centers, radii) for q in ineqs)


# ---------------------------------------------------------------------------
# search

TIES = {False: [Q(9, 20), Q(9, 11)], True: [Q(1, 2)]}


_CHARTS = {}


def charts_for(seg, kind, aff=None):
    segment = "B" if seg else "A"
    if kind == "cone":
        key = (seg, tuple(tuple(row) for row in aff))
        if key not in _CHARTS:
            if len(_CHARTS) > 2000:
                _CHARTS.clear()
            _CHARTS[key] = cs.Chart(segment, aff=aff)
        return _CHARTS[key]
    if kind in AMODE:
        if kind in SKEW_KINDS:
            return cs.Chart(segment, skew=True, amode=AMODE[kind])
        if kind in PLAIN_A_KINDS:
            return cs.Chart(segment, amode=AMODE[kind])
        return cs.Chart(segment, tube=True, amode=AMODE[kind])
    return cs.Chart(segment, tube=kind == "tube", wedge=kind == "wedge",
                    wtube=kind == "wtube", skew=kind == "skew")


def probes(kind, centers, radii, eps0):
    if kind == "cone":
        lo = [c - r for c, r in zip(centers, radii)]
        out = [(list(centers), float(centers[0]))]
        small = list(centers)
        small[0] = min(centers[0], eps0 / 1000)
        out.append((small, float(small[0])))
        for scale in (Q(1, 100), Q(1, 10000)):
            pt = list(centers)
            pt[2:6] = [l + (c - l) * scale for l, c in zip(lo[2:6], centers[2:6])]
            for e in (1e-4, 1e-7):
                pt2 = list(pt)
                pt2[0] = Q(e)
                out.append((pt2, e))
        return out
    out = [(list(centers), float(eps0) / 4)]
    small = list(centers)
    small[0] = min(centers[0], eps0 / 1000)
    out.append((small, float(small[0])))
    lo_u = list(centers)
    lo_u[2] = centers[2] - radii[2]
    out.append((lo_u, float(eps0) / 4))
    if radii[1] > 0:
        # at lambda = 0 (the exact corner view) edges 0-3 and 4-7 project to
        # points; the LP there picks contacts whose weights stay positive
        lo_l = list(centers)
        lo_l[1] = centers[1] - radii[1]
        out.append((lo_l, float(min(centers[0], eps0 / 1000))))
    if kind in RHO_KINDS:
        # inside the degenerate sector (a = 0) the certificate must be the
        # one active at first order: probe with eps << rho
        out.append((list(centers), 1e-8))
    if kind in ("tube", "plain", "skew") and centers[3] - radii[3] <= 0 <= centers[3] + radii[3]:
        # on the plane a = 0 the first-order term vanishes in the degenerate
        # sector; take the triple that is optimal there at second order
        on_plane = list(centers)
        on_plane[3] = Q(0)
        out.append((on_plane, float(centers[0])))
        out.append((on_plane, float(centers[0]) / 16))
    if kind == "tube" and (centers[3] - radii[3] == 0 or centers[3] + radii[3] == 0):
        # boxes against the plane a = 0: the certificate valid up to the plane
        # is the one optimal slightly off it, on the box's side
        side = Q(-1, 100) if centers[3] <= 0 else Q(1, 100)
        for rho in (centers[6], Q(1, 5)):
            off = list(centers)
            off[3], off[6] = side, rho
            for eps in (1e-3, 1e-4):
                out.append((off, eps))
    if kind == "wtube":
        tiny = list(centers)
        tiny[6] = Q(1, 10**4)
        out.append((tiny, 1e-8))
    return out


RECENT = []          # triples that recently certified a box in this table


def broad_triples(chart, kind, centers, radii):
    """LP triples over a small grid of probe points around the box (a last
    resort before splitting a small box)."""
    out = []
    n = len(centers)
    for da, db, dc in [(da, Q(0), Q(0)) for da in
                       (Q(-1, 100), Q(-1, 1000), Q(0), Q(1, 1000), Q(1, 100))] + \
                      [(Q(0), db, dc) for db in (Q(-1, 50), Q(0), Q(1, 50))
                       for dc in (Q(-1, 50), Q(0), Q(1, 50)) if db or dc]:
        for eps in (1e-6, 1e-4, 1e-3, float(centers[0])):
            pc = list(centers)
            pc[3] = centers[3] + da
            pc[4] = centers[4] + db
            if radii[5] > 0:
                pc[5] = centers[5] + dc
            rhos = [centers[6], Q(1, 5)] if n == 7 else [None]
            for rho in rhos:
                if rho is not None:
                    pc[6] = rho
                s, t, X = chart.float_point(pc)
                if s == 0 and t == 0 and np.abs(X).max() == 0:
                    continue
                try:
                    tri, _ = sc.choose_triple(max(eps, 1e-9), s, t, X)
                except Exception:
                    continue
                if len(tri) == 3:
                    out.append(tri)
    return out


def try_leaf(chart, seg, kind, centers, radii, e0):
    """Return a leaf description or None."""
    tube = kind in RHO_KINDS
    if kind == "cone" and not seg and cpocket_ok(chart.aff, centers, radii, e0):
        return ("handoff", "cpocket")
    for h in ("cone", "pocket", "spocket", "tube", "ppocket", "wedge", "wtube", "skew"):
        if handoff_ok(h, seg, kind, centers, radii, e0):
            return ("handoff", h)
    sc.set_nvars(chart.nvars)
    mask = _rust_flip_mask(chart, kind, centers, radii)
    for k in range(12):
        if (mask is None or mask[k]) and flip_ok(chart, k, centers, radii, tube):
            return ("flip", k)
    seen = set()
    del PENDING[:]
    for probe_centers, probe_eps in probes(kind, centers, radii, e0):
        s, t, Xv = chart.float_point(probe_centers)
        if s == 0 and t == 0 and np.abs(Xv).max() == 0:
            continue
        try:
            triple, _ = sc.choose_triple(max(probe_eps, 1e-9), s, t, Xv)
        except Exception:
            continue
        if len(triple) != 3:
            continue
        variants = [triple, [triple[0], triple[2], triple[1]]]
        # the tube displacement must vanish at X = 0, i.e. each contact
        # pairs a vertex with itself; the LP can pair near-coincident
        # vertices (0 and 3 project together at the corner view), which
        # also matters for the other charts near the corner view
        same = [(Qv, A, B, Qv, sg) for (P, A, B, Qv, sg) in triple]
        variants += [same, [same[0], same[2], same[1]]]
        for tri in variants:
            key = tuple(tri)
            if key in seen:
                continue
            seen.add(key)
            ok = cert_valid(chart, kind, tri, centers, radii)
            if ok is not None:
                RECENT.append(tri)
                del RECENT[:-50]
                return ("cert", tri, ok[0], ok[1])
    for tri in list(PENDING)[:SHIFT_MAX]:
        ok = cert_valid(chart, kind, tri, centers, radii, allow_shift=True)
        if ok is not None:
            RECENT.append(tri)
            del RECENT[:-50]
            return ("cert", tri, ok[0], ok[1])
    del PENDING[:]
    if kind == "cone":
        for tri in cone_pool(chart, centers, radii):
            key = tuple(tri)
            if key in seen:
                continue
            seen.add(key)
            ok = cert_valid(chart, kind, tri, centers, radii, allow_shift=True)
            if ok is not None:
                RECENT.append(tri)
                del RECENT[:-50]
                return ("cert", tri, ok[0], ok[1])
    fallback = list(reversed(RECENT))
    if max(radii[2:]) <= Q(1, 1024):
        fallback += broad_triples(chart, kind, centers, radii)
    for triple in fallback:
        variants = [triple, [triple[0], triple[2], triple[1]]]
        same = [(Qv, A, B, Qv, sg) for (P, A, B, Qv, sg) in triple]
        variants += [same, [same[0], same[2], same[1]]]
        for tri in variants:
            key = tuple(tri)
            if key in seen:
                continue
            seen.add(key)
            ok = cert_valid(chart, kind, tri, centers, radii)
            if ok is not None:
                RECENT.append(tri)
                del RECENT[:-50]
                return ("cert", tri, ok[0], ok[1])
    for tri in list(PENDING)[:SHIFT_MAX]:
        ok = cert_valid(chart, kind, tri, centers, radii, allow_shift=True)
        if ok is not None:
            RECENT.append(tri)
            del RECENT[:-50]
            return ("cert", tri, ok[0], ok[1])
    if COMBOS:
        combo = try_combo(chart, kind, [list(k) for k in seen], centers, radii)
        if combo is not None:
            return ("combo",) + combo
    return None


COMBOS = False
# Shifted retries (a coordinate moved to a box face) cost ~10x a plain check and
# rarely succeed (table 74: 615 tries, 1 success, 81% of leaf time); retry only
# the first few pending triples, in the order the probes found them.
SHIFT_MAX = int(os.environ.get("CORNER_SHIFT_MAX", "2"))


def choose_cut(seg, kind, centers, radii, eps0, min_radius):
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]
    if kind == "cone":
        # cone coordinates are already scaled to the tie; allow finer boxes
        k = max(range(len(centers)),
                key=lambda i: radii[i] / eps0 if i == 0 else radii[i])
        if (radii[k] / eps0 if k == 0 else radii[k]) <= min_radius / 16:
            return None
        return k, centers[k]
    cuts = list(TIES[seg])
    if kind in ("tube", "plain") and not seg:
        cuts += [CONE_TIE - CONE_DU, CONE_TIE + CONE_DU]
    tie = next((x for x in cuts if lo[2] < x < hi[2]), None)
    if tie is not None:
        return 2, tie
    if kind in RHO_KINDS and radii[5] == 0:
        # the degenerate lines c = +-SKEW_K b meet the faces c = +-1 at
        # b = +-1/SKEW_K; split there exactly
        for x in (1 / SKEW_K, -1 / SKEW_K):
            if lo[4] < x < hi[4]:
                return 4, x
    zero_vars = {"plain": (3,), "tube": (3,), "wedge": (3, 5), "wtube": (3,),
                 "skew": (5, 3), "atube": (3,), "btube+": (), "btube-": (),
                 "askew": (5, 3), "bskew+": (5,), "bskew-": (5,),
                 "aplain": (3,), "bplain+": (), "bplain-": ()}[kind]
    for v in zero_vars:
        if lo[v] < 0 < hi[v] and radii[v] <= Q(1, 4):
            return v, Q(0)
    k = max(range(len(centers)),
            key=lambda i: radii[i] / eps0 if i == 0 else radii[i])
    if (radii[k] / eps0 if k == 0 else radii[k]) <= min_radius:
        return None
    return k, centers[k]


def stellar_choice(chart, centers, radii):
    """At a cone apex box: an edge (i, j) of the cone and the generator
    weights (al, be) at which the first-order optimal triple changes."""
    hi = [c + r for c, r in zip(centers, radii)]

    def best(t):
        pt = [Q(1, 10**7), Q(1)] + [Q(x) for x in t]
        s_, t_, X = chart.float_point(pt)
        tri, m = sc.choose_triple(1e-7, s_, t_, X)
        return tuple(tri), m

    def point(i, j, th):
        t = [0.0] * 4
        t[i - 2] = (1 - th) * float(hi[i]) * 1e-3
        t[j - 2] = th * float(hi[j]) * 1e-3
        return t
    choice = None
    for i, j in itertools.combinations(range(2, 6), 2):
        prev = None
        for th in np.linspace(0, 1, 33):
            key, m = best(point(i, j, th))
            if prev is not None and key != prev[0]:
                a0, a1 = prev[1], th
                for _ in range(20):
                    mid = (a0 + a1) / 2
                    if best(point(i, j, mid))[0] == prev[0]:
                        a0 = mid
                    else:
                        a1 = mid
                th0 = Q(Fraction((a0 + a1) / 2).limit_denominator(256))
                score = min(prev[2], m)
                if Q(1, 50) < th0 < Q(49, 50) and (choice is None or score < choice[0]):
                    choice = (score, i, j, (1 - th0) * hi[i], th0 * hi[j])
                break
            prev = (key, th, m)
    return None if choice is None else choice[1:]


def first_order(chart, triple, lo):
    """Exact first-order coefficients (of t₂..t₅, at ε = 0, λ = 1) of the
    displacement `D / ε` of a triple in a cone chart, or None."""
    _, _, D = chart.certificate(triple)
    F = disp_F(normalize(D), "cone", lo)
    if F is None:
        return None
    coef = [Q(0)] * 4
    const = Q(0)
    for e, v in F.items():
        if e[0] != 0:
            continue
        deg = sum(e[2:6])
        if deg == 0:
            const += v
        elif deg == 1:
            k = next(k for k in range(4) if e[2 + k])
            coef[k] += v
    return coef if const == 0 else None


CONE_FACE_SPLIT = os.environ.get("CONE_FACE_SPLIT") == "1"


def _uaxis_gens(aff):
    """Generators (indices 0..3 into t2..t5) whose (a, b, c) part is zero: the
    clearance vanishes along them (X = 0), so pairing them in a stellar split
    only pulls generators toward the u-axis without refining directions."""
    if not CONE_FACE_SPLIT or not aff:
        return set()
    return {k for k in range(4) if all(row[k + 1] == 0 for row in aff[1:])}


def stellar_choice_exact(chart, centers, radii):
    """Split the cone along the zero plane of the first-order part of a
    triple: the one optimal at the cone's center, or else one optimal along a
    generator where that triple's first-order coefficient vanishes."""
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]

    def lp_triple(t):
        s_, t_, X = chart.float_point([Q(1, 10**4), Q(1)] + list(t))
        return sc.choose_triple(1e-4, s_, t_, X)[0]

    def split_of(T):
        c = first_order(chart, T, lo)
        if c is None:
            return None, None
        best = None
        for i, j in (p for p in itertools.permutations(range(4), 2) if not set(p) & _uaxis_gens(chart.aff)):
            if c[i] > 0 > c[j]:
                score = min(c[i], -c[j]) / max(c[i], -c[j])
                if best is None or score > best[0]:
                    best = (score, i + 2, j + 2, -c[j], c[i])
        return c, best

    def same(T):
        return [(Qv, A, B, Qv, sg) for (P, A, B, Qv, sg) in T]
    T0 = lp_triple(centers[2:6])
    c0, best = split_of(T0)
    if best is None:
        c1, best = split_of(same(T0))
        if c0 is None:
            c0 = c1
    if best is None and c0 is not None:
        for k in range(4):
            if c0[k] > 0:
                continue
            t = [Q(0)] * 4
            t[k] = hi[2 + k] / 2
            Tk = lp_triple(t)
            for T in (Tk, same(Tk)):
                ck, b = split_of(T)
                if b is not None and ck[k] > 0:
                    best = b
                    break
            if best is not None:
                break
    if best is None:
        return None
    _, i, j, al, be = best
    # keep the new ray's coordinate range [0, 1]: scale (al, be) to hi
    sc_ = min(hi[i] / al, hi[j] / be)
    return i, j, al * sc_, be * sc_


def first_two_orders(chart, triple, lo):
    """Exact coefficients of t₂..t₅ in `D / ε` at orders ε⁰ and ε¹ (λ = 1)."""
    _, _, D = chart.certificate(triple)
    F = disp_F(normalize(D), "cone", lo)
    if F is None:
        return None
    c, d = [Q(0)] * 4, [Q(0)] * 4
    for e, v in F.items():
        deg = sum(e[2:6])
        if deg == 0 and e[0] <= 1 and v != 0:
            return None
        if deg == 1 and e[0] <= 1:
            k = next(k for k in range(4) if e[2 + k])
            (c if e[0] == 0 else d)[k] += v
    return c, d


def cone_pool(chart, centers, radii):
    """Candidate triples for a cone box: LP choices at its center and along
    each generator, at several scales of eps, with same-vertex variants."""
    hi = [c + r for c, r in zip(centers, radii)]
    points = [list(centers[2:6])]
    for k in range(4):
        t = [Q(0)] * 4
        t[k] = hi[2 + k] / 2
        points.append(t)
    pool = []
    for t in points:
        for e in (1e-2, 1e-3, 1e-4):
            s_, t_, X = chart.float_point([Q(e), Q(1)] + list(t))
            try:
                tri = sc.choose_triple(e, s_, t_, X)[0]
            except Exception:
                continue
            same = [(Qv, A, B, Qv, sg) for (P, A, B, Qv, sg) in tri]
            for T in (tri, same):
                if T not in pool:
                    pool.append(T)
    return pool


def first_order_eps(chart, triple, lo):
    """The t-linear coefficients of `D / ε` as polynomials in ε (λ = 1):
    a list of 4 dicts {power: coefficient}, or None."""
    _, _, D = chart.certificate(triple)
    F = disp_F(normalize(D), "cone", lo)
    if F is None:
        return None
    polys = [dict() for _ in range(4)]
    for e, v in F.items():
        deg = sum(e[2:6])
        if deg == 0:
            if v != 0:
                return None
            continue
        if deg == 1:
            k = next(k for k in range(4) if e[2 + k])
            polys[k][e[0]] = polys[k].get(e[0], 0) + v
    return polys


def _poly_sign_on(poly, e0, e1):
    """+1 if poly(ε) / ε^m > 0 on [e0, e1] (m = lowest power), -1 if < 0,
    0 if undecided (crude interval bound)."""
    poly = {k: v for k, v in poly.items() if v != 0}
    if not poly:
        return 0
    m = min(poly)
    q = {k - m: v for k, v in poly.items()}
    c = (e0 + e1) / 2
    r = (e1 - e0) / 2
    val = sum(v * c ** k for k, v in q.items())
    slack = sum(abs(v) * ((abs(c) + r) ** k - abs(c) ** k) for k, v in q.items() if k > 0)
    if val - slack > 0:
        return 1
    if val + slack < 0:
        return -1
    return 0


def stellar_choice_pool(chart, kind, centers, radii):
    """Pick the valid triple that is already good (first-order positive, or
    zero with a positive ε-order term) on the most generators, and split the
    cone along its first-order zero plane."""
    lo = [c - r for c, r in zip(centers, radii)]
    hi = [c + r for c, r in zip(centers, radii)]
    pool = cone_pool(chart, centers, radii)
    best = None
    e0, e1 = lo[0], hi[0]
    ec = (e0 + e1) / 2
    for T in pool:
        if _prechecked(chart, kind, T, centers, radii) is None:
            continue
        polys = first_order_eps(chart, T, lo)
        if polys is None:
            continue
        if e0 == 0:
            # boxes reaching eps = 0: the small-eps behaviour decides
            # (first order, or zero with a positive eps-order term)
            c = [pk.get(0, 0) for pk in polys]
            d = [pk.get(1, 0) for pk in polys]
            good = [c[k] > 0 or (c[k] == 0 and d[k] > 0) for k in range(4)]
        else:
            # boxes away from eps = 0: the coefficients over the eps range,
            # and the zero plane at its middle
            good = [_poly_sign_on(pk, e0, e1) > 0 for pk in polys]
            c = [sum(v * ec ** k for k, v in pk.items()) for pk in polys]
        if all(good):
            return "axis"
        for i, j in (p for p in itertools.permutations(range(4), 2) if not set(p) & _uaxis_gens(chart.aff)):
            if c[i] > 0 > c[j]:
                ratio = min(c[i], -c[j]) / max(c[i], -c[j])
                key = (sum(good), ratio)
                if best is None or key > best[0]:
                    best = (key, i + 2, j + 2, -c[j], c[i])
    if best is None:
        return None
    _, i, j, al, be = best
    sc_ = min(hi[i] / al, hi[j] / be)
    return i, j, al * sc_, be * sc_


def stellar_midpoint(aff, centers, radii):
    """Refine directions: split the cone's widest edge at its midpoint."""
    hi = [c + r for c, r in zip(centers, radii)]
    scale = [1 / float(CONE_DU), 1 / float(CONE_R), 1 / float(CONE_R), 1 / float(CONE_R)]
    ends = []
    for k in range(4):
        v = np.array([float(row[k + 1]) * float(hi[2 + k]) * sc_ for row, sc_ in zip(aff, scale)])
        n = np.linalg.norm(v)
        ends.append(v / n if n > 0 else v)
    best = None
    for i, j in (p for p in itertools.combinations(range(4), 2) if not set(p) & _uaxis_gens(aff)):
        ang = float(np.arccos(np.clip(ends[i] @ ends[j], -1, 1)))
        if best is None or ang > best[0]:
            best = (ang, i + 2, j + 2)
    _, i, j = best
    # r = (hi_i v_i + hi_j v_j) / 2, with the new coordinate in [0, 2]
    return i, j, hi[i] / 2, hi[j] / 2


MAX_STELLAR = 24
CPOCKET_DEPTH = 10
# extra stellar depth for splits that peel off the `cpocket` region
CPOCKET_EXTRA = 24


def cpocket_split(aff, centers, radii):
    """A stellar split that peels off the `cpocket` region: along the zero
    plane of a homogeneous pocket inequality that the frame's generators
    straddle (none may be negative on every generator)."""
    # only once the bound-type conditions (u <= tie + du, b, c <= rho0) hold:
    # those need box cuts, not stellar splits
    sc.set_nvars(6)
    ineqs = cpocket_ineqs(aff)
    if not all(nonneg_ok(ineqs[k], centers, radii) for k in (1, 4, 5)):
        return None
    hi = [c + r for c, r in zip(centers, radii)]
    U, A, B, C = ([row[k + 1] * hi[2 + k] for k in range(4)] for row in aff)
    S = [TPOCKET_W / 2 * (b + c) for b, c in zip(B, C)]
    forms = [U, B, C, [x + a for x, a in zip(S, A)], [x - a for x, a in zip(S, A)]]
    bad = [c for c in forms if any(x < 0 for x in c)]
    if any(all(x <= 0 for x in c) for c in bad):
        return None
    best = None
    for c in bad:
        for i, j in itertools.permutations(range(4), 2):
            if c[i] > 0 > c[j]:
                ratio = min(c[i], -c[j]) / max(c[i], -c[j])
                if best is None or ratio > best[0]:
                    best = (ratio, i + 2, j + 2, -c[j], c[i])
    if best is None:
        return None
    _, i, j, al, be = best
    sc_ = min(hi[i] / al, hi[j] / be)
    return i, j, al * sc_, be * sc_


def _step(ctx, nodes, stack, counts, stuck, item):
    """Process one open frame: a leaf, a stuck box, or a split whose children
    are pushed onto `stack`.  Returns the tree weight completed."""
    global SHIFT_MAX
    seg, kind, e0, min_radius, chart0 = ctx
    nid, c, r, aff, sdepth, w = item
    chart = charts_for(seg, kind, aff) if kind == "cone" else chart0
    leaf = try_leaf(chart, seg, kind, c, r, e0)
    if leaf is not None:
        nodes[nid] = (nid, c, r, leaf, aff)
        counts[leaf[0]] = counts.get(leaf[0], 0) + 1
        return w
    if kind == "cone" and sdepth < MAX_STELLAR + CPOCKET_EXTRA and all(
            ci - ri == 0 for ci, ri in zip(c[2:6], r[2:6])):
        ch = cpocket_split(aff, c, r) if not seg and sdepth >= CPOCKET_DEPTH else None
        if ch is None and sdepth < MAX_STELLAR:
            ch = stellar_choice_pool(chart, kind, c, r)
            if ch != "axis":
                ch = stellar_choice_exact(chart, c, r) or ch or stellar_midpoint(aff, c, r)
            else:
                ch = None
        if ch is not None:
            i, j, al, be = ch
            lower_id, upper_id = len(nodes), len(nodes) + 1
            nodes += [None, None]
            cl, rl, affl = stellar_frame(c, r, aff, i, j, al, be)
            cu, ru, affu = stellar_frame(c, r, aff, j, i, be, al)
            nodes[nid] = (nid, c, r, ("stellar", i, j, al, be, lower_id, upper_id), aff)
            stack.append((upper_id, cu, ru, affu, sdepth + 1, w / 2))
            stack.append((lower_id, cl, rl, affl, sdepth + 1, w / 2))
            counts["stellar"] = counts.get("stellar", 0) + 1
            return 0.0
    cut = choose_cut(seg, kind, c, r, e0, min_radius)
    if cut is None and SHIFT_MAX < 10**6:
        # at the minimum size: retry with every shifted variant before giving up
        saved, SHIFT_MAX = SHIFT_MAX, 10**6
        try:
            leaf = try_leaf(chart, seg, kind, c, r, e0)
        finally:
            SHIFT_MAX = saved
        if leaf is not None:
            nodes[nid] = (nid, c, r, leaf, aff)
            counts[leaf[0]] = counts.get(leaf[0], 0) + 1
            return w
    if cut is None:
        stuck.append(([float(x) for x in c], [float(x) for x in r],
                      [[str(x) for x in row] for row in aff], sdepth))
        counts["stuck"] = counts.get("stuck", 0) + 1
        nodes[nid] = (nid, c, r, ("stuck",), aff)
        return w
    v, m = cut
    lo, hi = c[v] - r[v], c[v] + r[v]
    lower_id, upper_id = len(nodes), len(nodes) + 1
    nodes += [None, None]
    cl, rl = list(c), list(r)
    cl[v], rl[v] = (lo + m) / 2, (m - lo) / 2
    cu, ru = list(c), list(r)
    cu[v], ru[v] = (m + hi) / 2, (hi - m) / 2
    nodes[nid] = (nid, c, r, ("split", v, m, lower_id, upper_id), aff)
    stack.append((upper_id, cu, ru, aff, sdepth, w / 2))
    stack.append((lower_id, cl, rl, aff, sdepth, w / 2))
    counts["split"] = counts.get("split", 0) + 1
    return 0.0


_CHART0 = {}


def _explore(args):
    """Worker: explore the subtree under one open frame for up to `budget`
    seconds; returns its nodes (local ids, root 0) and leftover frontier."""
    index, seg, kind, e0, min_radius, item, budget, recent = args
    # the leaf search falls back on recently successful triples; seed them
    # from the coordinator so a slice sees its neighbourhood's certificates
    RECENT[:] = [list(t) for t in recent]
    if index not in _CHART0:
        _CHART0[index] = charts_for(seg, kind, root_aff(index))
    ctx = (seg, kind, e0, min_radius, _CHART0[index])
    nodes = [None]
    stack = [(0,) + tuple(item[1:])]
    counts, stuck, done = {}, [], 0.0
    t0 = time.time()
    while stack and time.time() - t0 < budget:
        done += _step(ctx, nodes, stack, counts, stuck, stack.pop())
    return item[0], nodes, stack, counts, stuck, done, [tuple(t) for t in RECENT]


def _merge(nodes, gid, local_nodes, local_stack):
    """Splice a worker's subtree into the global node list."""
    base = len(nodes)
    nodes.extend([None] * (len(local_nodes) - 1))

    def g(i):
        return gid if i == 0 else base + i - 1
    for node in local_nodes:
        if node is None:
            continue
        i, c, r, leaf, aff = node
        if leaf[0] == "split":
            leaf = leaf[:3] + (g(leaf[3]), g(leaf[4]))
        elif leaf[0] == "stellar":
            leaf = leaf[:5] + (g(leaf[5]), g(leaf[6]))
        nodes[g(i)] = (g(i), c, r, leaf, aff)
    return [(g(it[0]),) + tuple(it[1:]) for it in local_stack]


# Slices run depth-first from the deepest pending frame, so subtrees close and
# the frontier stays bounded.  Heaviest-first dispatch (alternating) makes the
# tree fraction move early but explores breadth-first: on cone table 45 it grew
# the frontier to ~1,700 full-size apex cones with no hand-offs.  Opt in only.
PAR_SLICE = float(os.environ.get("CORNER_PAR_SLICE", "300"))
HEAVY_FIRST = os.environ.get("CORNER_HEAVY_FIRST") == "1"
PAR_MAX = int(os.environ.get("CORNER_PAR_MAX", "12"))
SEED_TOP = int(os.environ.get("CORNER_SEED_TOP", "15"))
SEED_RECENT = int(os.environ.get("CORNER_SEED_RECENT", "15"))


def build_table(job, par=1):
    index, seg, kind, center, radius, e0, max_boxes, min_radius = job
    in_flight = {}
    aff0 = root_aff(index)
    chart0 = charts_for(seg, kind, aff0)
    nodes = [None]
    stack = [(0, center, radius, aff0, 0, 1.0)]
    stuck = []
    counts = {}
    done_weight = 0.0      # tree fraction: each split gives half its weight to each child
    start = last_report = last_ckpt = time.time()
    elapsed0 = 0.0
    ckpt = os.path.join(PROGRESS_DIR, f"ckpt-{index:02d}.json") if PROGRESS_DIR else None
    if ckpt and os.path.exists(ckpt):
        saved = json.load(open(ckpt))
        nodes = [decode_node(n) for n in saved["nodes"]]
        stack = [(int(nid), [Q(x) for x in c], [Q(x) for x in r],
                  [[Q(x) for x in row] for row in aff], int(sd), float(w))
                 for nid, c, r, aff, sd, w in saved["stack"]]
        counts, done_weight = saved["counts"], saved["done_weight"]
        elapsed0 = saved.get("elapsed", 0.0)
        # retry boxes recorded as stuck (the checker may have improved since)
        for node in nodes:
            if node is not None and node[3][0] == "stuck":
                nid, c, r, _, aff = node
                nodes[nid] = None
                stack.append((nid, c, r, aff, 0, 0.0))
                counts["stuck"] = counts.get("stuck", 0) - 1
        if counts.get("stuck", 0) <= 0:
            counts.pop("stuck", None)

    def checkpoint():
        if not ckpt:
            return
        with open(ckpt + ".tmp", "w") as out:
            json.dump({"index": index, "nodes": nodes,
                       "stack": stack + list(in_flight.values()), "counts": counts,
                       "done_weight": done_weight,
                       "elapsed": elapsed0 + time.time() - start}, out, default=str)
        os.replace(ckpt + ".tmp", ckpt)

    def report(final=False):
        path = os.path.join(PROGRESS_DIR, f"progress-{index:02d}.json") if PROGRESS_DIR else None
        if path:
            with open(path + ".tmp", "w") as out:
                json.dump({"index": index, "kind": kind, "nodes": len(nodes),
                           "open": len(stack) + len(in_flight), "par": par,
                           "stuck": counts.get("stuck", 0), "counts": counts,
                           "stuck_at": stuck[:5],
                           "done_fraction": done_weight,
                           "elapsed": elapsed0 + time.time() - start,
                           "updated": time.time(), "final": final}, out)
            os.replace(path + ".tmp", path)
    ctx = (seg, kind, e0, min_radius, chart0)
    if par <= 1:
        while stack:
            if time.time() - last_report > 30:
                last_report = time.time()
                report()
            if time.time() - last_ckpt > CKPT_SECONDS:
                last_ckpt = time.time()
                checkpoint()
            if len(nodes) > max_boxes:
                return index, None, {"error": "budget", **counts}, stuck[:5]
            done_weight += _step(ctx, nodes, stack, counts, stuck, stack.pop())
    else:
        import queue
        results = queue.Queue()
        # table-wide certificate statistics: slices fall back on the triples
        # that certified most boxes so far, not only on their own recent ones
        dispatched = 0
        freq = {}
        for node in nodes:
            if node is not None and node[3][0] == "cert":
                key = tuple(tuple(x) for x in node[3][1])
                freq[key] = freq.get(key, 0) + 1

        def seed_triples():
            # a short list: every leaf that fails tries them all (measured on
            # table 74: 90 seeds 98 s / 20 seeds 57 s per 10 boxes, same certs)
            top = sorted(freq, key=lambda k: -freq[k])[:SEED_TOP]
            recent = [tuple(tuple(x) for x in t) for t in RECENT[-SEED_RECENT:]]
            return top[::-1] + [t for t in recent if t not in top]
        # the worker count can be changed while running: write N to
        # <outdir>/par-XX (XX = table index); idle pool processes just wait
        par_file = os.path.join(PROGRESS_DIR, f"par-{index:02d}") if PROGRESS_DIR else None
        if par_file and not os.path.exists(par_file):
            with open(par_file, "w") as out:
                out.write(f"{par}\n")
        pool = multiprocessing.get_context("fork").Pool(max(par, PAR_MAX))
        last_par_check = 0.0
        try:
            while stack or in_flight:
                if time.time() - last_report > 30:
                    last_report = time.time()
                    report()
                if time.time() - last_ckpt > CKPT_SECONDS:
                    last_ckpt = time.time()
                    checkpoint()
                if len(nodes) > max_boxes:
                    return index, None, {"error": "budget", **counts}, stuck[:5]
                if par_file and time.time() - last_par_check > 10:
                    last_par_check = time.time()
                    try:
                        par = max(1, min(PAR_MAX, int(open(par_file).read().split()[0])))
                    except (OSError, ValueError, IndexError):
                        pass
                while stack and len(in_flight) < par:
                    # alternate: deepest frame (depth-first, bounded memory)
                    # and heaviest pending frame (early view of big subtrees)
                    if HEAVY_FIRST and dispatched % 2 and len(stack) > 1:
                        k = max(range(len(stack)), key=lambda q: stack[q][5])
                        item = stack.pop(k)
                    else:
                        item = stack.pop()
                    dispatched += 1
                    in_flight[item[0]] = item
                    pool.apply_async(
                        _explore, ((index, seg, kind, e0, min_radius, item, PAR_SLICE,
                                    seed_triples()),),
                        callback=results.put,
                        error_callback=lambda e: results.put(("error", e)))
                try:
                    res = results.get(timeout=10)
                except queue.Empty:
                    continue
                if res[0] == "error":
                    raise res[1]
                gid, lnodes, lstack, lcounts, lstuck, ldone, lrecent = res
                for t in lrecent:
                    if list(t) not in RECENT:
                        RECENT.append(list(t))
                del RECENT[:-50]
                del in_flight[gid]
                for node in lnodes:
                    if node is not None and node[3][0] == "cert":
                        key = tuple(tuple(x) for x in node[3][1])
                        freq[key] = freq.get(key, 0) + 1
                stack.extend(_merge(nodes, gid, lnodes, lstack))
                for k, v in lcounts.items():
                    counts[k] = counts.get(k, 0) + v
                stuck.extend(lstuck)
                done_weight += ldone
        finally:
            pool.terminate()
    report(final=True)
    if ckpt and os.path.exists(ckpt) and not stuck:
        os.remove(ckpt)
    return index, nodes, counts, stuck[:5]


PROGRESS_DIR = None
CKPT_SECONDS = int(os.environ.get("CORNER_CKPT_SECONDS", "900"))


# ---------------------------------------------------------------------------
# packing

def zz(n):
    return 2 * n if n >= 0 else -2 * n - 1


def rat(q):
    q = Q(q)
    return [zz(q.numerator), q.denominator]


def encode_frame(seg, kind, c, r, aff=()):
    out = [1 if seg else 0, 0 if kind == "cone" else KINDS.index(kind), len(c)]
    for x in c:
        out += rat(x)
    for x in r:
        out += rat(x)
    out.append(len(aff))
    for row in aff:
        for x in row:
            out += rat(x)
    return out


def encode_table(seg, kind, nodes):
    out = [len(nodes)]
    for node in nodes:
        nid, c, r, leaf = node[:4]
        aff = node[4] if len(node) > 4 else []
        frame = encode_frame(seg, kind, c, r, aff)
        if leaf[0] == "stellar":
            _, i, j, al, be, lo_id, hi_id = leaf
            out += [5, nid] + frame + [i, j] + rat(al) + rat(be) + [lo_id, hi_id]
        elif leaf[0] == "split":
            _, v, m, lo_id, hi_id = leaf
            out += [0, nid] + frame + [v] + rat(m) + [lo_id, hi_id]
        elif leaf[0] == "cert":
            _, tri, split, shift = leaf
            edges, inner, outer = lean_triple(tri)
            out += [4 if shift else 1, nid] + frame
            for e in edges:
                for x in e:
                    out += rat(x)
            out += inner + outer + [len(split)]
            for v, s in split:
                out += [v, 1 if s else 0]
            if shift:
                out += [len(shift)]
                for x in shift:
                    out += rat(x)
        elif leaf[0] == "flip":
            out += [2, nid] + frame + [leaf[1]]
        elif leaf[0] == "handoff":
            out += [3, nid] + frame + [("tube", "wedge", "wtube", "skew", "cone", "pocket", "spocket",
                                         "ppocket", "cpocket").index(leaf[1])]
        else:
            raise ValueError("stuck leaf")
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("outdir")
    parser.add_argument("--eps0", default="1/8")
    parser.add_argument("--jobs", type=int, default=14)
    parser.add_argument("--max-boxes", type=int, default=2_000_000)
    parser.add_argument("--min-radius", default="1/4096")
    parser.add_argument("--only")
    parser.add_argument("--par", type=int, default=1,
                        help="workers per table (tables then run one after another)")
    args = parser.parse_args()
    e0 = Q(args.eps0)
    os.makedirs(args.outdir, exist_ok=True)
    global PROGRESS_DIR
    PROGRESS_DIR = args.outdir
    roots = all_roots(e0)
    only = ([int(i) for i in args.only.split(",")] if args.only
            else range(len(roots)))
    jobs = [(i,) + roots[i] + (e0, args.max_boxes, Q(args.min_radius))
            for i in only]
    jobs.sort(key=lambda j: j[2] != "plain")   # the big ones first
    start = time.time()
    if args.par > 1:
        results = (build_table(job, args.par) for job in jobs)
    else:
        pool = multiprocessing.get_context("fork").Pool(args.jobs)
        results = pool.imap_unordered(build_table, jobs)
    if True:
        for index, nodes, counts, stuck in results:
            seg, kind = roots[index][0], roots[index][1]
            summary = {"index": index, "seg": "B" if seg else "A", "kind": kind,
                       "counts": counts, "stuck": stuck,
                       "seconds": round(time.time() - start)}
            print(json.dumps(summary), flush=True)
            if nodes is not None and "stuck" not in counts:
                with open(os.path.join(args.outdir, f"table-{index:02d}.json"),
                          "w") as out:
                    json.dump({"index": index, "seg": seg, "kind": kind,
                               "nodes": nodes}, out, default=str)




def decode_node(node):
    """A node as written by `json.dump(..., default=str)` (None stays None)."""
    if node is None:
        return None
    nid, c, r, leaf = node[:4]
    aff = [[Q(x) for x in row] for row in node[4]] if len(node) > 4 else []
    c = [Q(x) for x in c]
    r = [Q(x) for x in r]
    if leaf[0] == "stellar":
        leaf = ("stellar", int(leaf[1]), int(leaf[2]), Q(leaf[3]), Q(leaf[4]),
                int(leaf[5]), int(leaf[6]))
    elif leaf[0] == "split":
        leaf = ("split", int(leaf[1]), Q(leaf[2]), int(leaf[3]), int(leaf[4]))
    elif leaf[0] == "cert":
        leaf = ("cert", [tuple(int(x) for x in t) for t in leaf[1]],
                [(int(v), bool(s)) for v, s in leaf[2]],
                [Q(x) for x in leaf[3]] if len(leaf) > 3 else [])
    elif leaf[0] == "flip":
        leaf = ("flip", int(leaf[1]))
    elif leaf[0] == "handoff":
        leaf = ("handoff", leaf[1])
    elif leaf[0] == "stuck":
        leaf = ("stuck",)
    return (int(nid), c, r, leaf, aff)


def load_nodes(path):
    data = json.load(open(path))
    return data["seg"], data["kind"], [decode_node(n) for n in data["nodes"]]


def pack(outdir, path):
    """Concatenate the 36 tables into `path` (all must be present)."""
    values = []
    missing = []
    for index in range(86):
        path_i = os.path.join(outdir, f"table-{index:02d}.json")
        if not os.path.exists(path_i):
            # placeholder (invalid) table, for partial checks only
            missing.append(index)
            values += [1] + [2, 0] + encode_frame(False, "plain", [], []) + [0]
            continue
        seg, kind, nodes = load_nodes(path_i)
        values += encode_table(seg, kind, nodes)
    if missing:
        print(f"placeholders for missing tables {missing}")
    with open(path, "w") as out:
        out.write(",".join(str(v) for v in values) + ",")
    print(f"packed {len(values)} naturals into {path}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "pack":
        pack(sys.argv[2], sys.argv[3])
    else:
        main()
