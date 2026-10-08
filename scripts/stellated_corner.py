#!/usr/bin/env python3
"""Blow-up certificates at the corner view of the stellated tetrahedron.

The corner is the view m = (1,1,0)/sqrt2 (projective point b = (1/2,1/2,0))
with relative rotation I.  Blown-up coordinates (eps, s, t, X^):

    w = b + eps * (s * F1 + t * F2),     X = eps * X^,

where w is the unnormalized view (on x+y+z = 1) and X the Cayley vector of
the relative rotation.  A certificate is a balanced triple of contacts
(inner vertex P_i, outer edge (A_i, B_i) with support vertex Q_i in {A_i,B_i},
orientation sigma_i): with e_i = x_B - x_A,

    <u_i, pi y>  = sigma_i * w . (e_i x y)                  (u_i outward normal)
    mu_1 = sigma_2 sigma_3 w . (e_2 x e_3)  (cyclic)         (sum mu_i u_i = 0)
    support:  sigma_i * w . (e_i x (x_j - x_Q_i)) <= 0  for all j
    D = sum_i mu_i sigma_i w . (e_i x (N(X) x_P_i - d(X) x_Q_i)) >= 0

with N, d the Cayley numerator and denominator.  D vanishes to second order
at eps = 0, so we certify E = D / eps^2 >= 0 on the box (exact division).
This module is the exact Python prototype of the future Lean checker.
"""
import itertools
import math
import sys
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
import stellated_certificate_search as st  # noqa: E402

VQ = [tuple(Q(c) for c in v) for v in st.VERTICES_Q]
VF = np.array([[float(c) for c in v] for v in VQ])
B0 = (Q(1, 2), Q(1, 2), Q(0))
F1 = (Q(1, 2), Q(-1, 2), Q(0))
F2 = (Q(1, 4), Q(1, 4), Q(-1, 2))
# variables: 0 eps, 1 s, 2 t, 3 x, 4 y, 5 z
NVARS = 6


# ---------------------------------------------------------------------------
# exact sparse polynomials: dict exponent-tuple -> Fraction

def p_const(c):
    return {(0,) * NVARS: Q(c)} if c != 0 else {}


def p_var(i, c=1):
    e = [0] * NVARS
    e[i] = 1
    return {tuple(e): Q(c)}


def p_add(*ps):
    out = {}
    for p in ps:
        for e, c in p.items():
            v = out.get(e, 0) + c
            if v == 0:
                out.pop(e, None)
            else:
                out[e] = v
    return out


def p_scale(p, c):
    c = Q(c)
    return {} if c == 0 else {e: c * v for e, v in p.items()}


def p_mul(p, q):
    out = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            v = out.get(e, 0) + c1 * c2
            if v == 0:
                out.pop(e, None)
            else:
                out[e] = v
    return out


def p_divide_monomial(p, exponent):
    """Exact division by a monomial, or None if some term is not divisible."""
    out = {}
    for e, c in p.items():
        if any(a < b for a, b in zip(e, exponent)):
            return None
        out[tuple(a - b for a, b in zip(e, exponent))] = c
    return out


def p_eval(p, x):
    return sum(float(c) * math.prod(x[i] ** k for i, k in enumerate(e))
               for e, c in p.items())


def p_shift(p, centers, radii):
    """Rewrite p(x) as a polynomial in u with x_i = c_i + r_i u_i."""
    out = {}
    for e, c in p.items():
        term = p_const(c)
        for i, k in enumerate(e):
            if k == 0:
                continue
            lin = p_add(p_const(centers[i]), p_var(i, radii[i]))
            power = p_const(1)
            for _ in range(k):
                power = p_mul(power, lin)
            term = p_mul(term, power)
        out = p_add(out, term)
    return out


def p_box_lower(p, centers, radii):
    """Exact lower bound over the box: constant minus sum |coefficients|."""
    shifted = p_shift(p, centers, radii)
    zero = (0,) * NVARS
    return shifted.get(zero, Q(0)) - sum(
        abs(c) for e, c in shifted.items() if e != zero)


# ---------------------------------------------------------------------------
# geometry as polynomials

def view_poly():
    """w(eps, s, t) = B0 + eps (s F1 + t F2), per coordinate."""
    eps_s = p_mul(p_var(0), p_var(1))
    eps_t = p_mul(p_var(0), p_var(2))
    return [p_add(p_const(B0[c]), p_scale(eps_s, F1[c]), p_scale(eps_t, F2[c]))
            for c in range(3)]


def cayley_polys():
    """N(X) and d(X) with X = eps * X^."""
    X = [p_mul(p_var(0), p_var(3 + k)) for k in range(3)]
    x, y, z = X
    one = p_const(1)

    def sq(a):
        return p_mul(a, a)

    def m2(a, b):
        return p_scale(p_mul(a, b), 2)
    N = [[p_add(one, sq(x), p_scale(sq(y), -1), p_scale(sq(z), -1)),
          p_add(m2(x, y), p_scale(z, -2)), p_add(m2(x, z), p_scale(y, 2))],
         [p_add(m2(x, y), p_scale(z, 2)),
          p_add(one, p_scale(sq(x), -1), sq(y), p_scale(sq(z), -1)),
          p_add(m2(y, z), p_scale(x, -2))],
         [p_add(m2(x, z), p_scale(y, -2)), p_add(m2(y, z), p_scale(x, 2)),
          p_add(one, p_scale(sq(x), -1), p_scale(sq(y), -1), sq(z))]]
    d = p_add(one, sq(x), sq(y), sq(z))
    return N, d


W = view_poly()
N_POLY, D_POLY = cayley_polys()


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def w_dot(vec_polys):
    """w . v for v a list of 3 polynomials."""
    return p_add(*(p_mul(W[c], vec_polys[c]) for c in range(3)))


def w_dot_const(vec):
    return p_add(*(p_scale(W[c], vec[c]) for c in range(3)))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def certificate_polys(triple):
    """triple: list of 3 (P, A, B, Q, sigma).  Returns (mus, supports, D)."""
    edges = [sub(VQ[B], VQ[A]) for (_, A, B, _, _) in triple]
    sig = [s for (*_, s) in triple]
    mus = []
    for i in range(3):
        j, k = (i + 1) % 3, (i + 2) % 3
        mus.append(p_scale(w_dot_const(cross(edges[j], edges[k])),
                           sig[j] * sig[k]))
    supports = []
    for i, (_, A, B, Qv, s) in enumerate(triple):
        for j in range(len(VQ)):
            if j == Qv:
                continue
            supports.append(p_scale(
                w_dot_const(cross(edges[i], sub(VQ[j], VQ[Qv]))), s))
    D = {}
    for i, (P, A, B, Qv, s) in enumerate(triple):
        # N(X) x_P - d(X) x_Q, as 3 polynomials
        inner = [p_add(*(p_scale(N_POLY[r][c], VQ[P][c]) for c in range(3)))
                 for r in range(3)]
        vec = [p_add(inner[r], p_scale(D_POLY, -VQ[Qv][r])) for r in range(3)]
        e = edges[i]
        crossed = [p_add(p_scale(vec[2], e[1]), p_scale(vec[1], -e[2])),
                   p_add(p_scale(vec[0], e[2]), p_scale(vec[2], -e[0])),
                   p_add(p_scale(vec[1], e[0]), p_scale(vec[0], -e[1]))]
        D = p_add(D, p_scale(p_mul(mus[i], w_dot(crossed)), s))
    return mus, supports, D


# ---------------------------------------------------------------------------
# float certificate selection at a box center

def float_pose(eps, s, t, X):
    w = np.array([float(B0[c] + 0) + eps * (s * float(F1[c]) + t * float(F2[c]))
                  for c in range(3)])
    v = w / np.linalg.norm(w)
    x, y, z = [eps * float(q) for q in X]
    d = 1 + x * x + y * y + z * z
    C = np.array([[1 + x*x - y*y - z*z, 2*(x*y - z), 2*(x*z + y)],
                  [2*(x*y + z), 1 - x*x + y*y - z*z, 2*(y*z - x)],
                  [2*(x*z - y), 2*(y*z + x), 1 - x*x - y*y + z*z]]) / d
    return v, C


def float_pose_delta(eps, s, t, X):
    """The view and `C - I`, computed without cancellation."""
    v, _ = float_pose(eps, s, t, X)
    x, y, z = [eps * float(q) for q in X]
    d = 1 + x * x + y * y + z * z
    CmI = np.array([[-2 * (y*y + z*z), 2*(x*y - z), 2*(x*z + y)],
                    [2*(x*y + z), -2 * (x*x + z*z), 2*(y*z - x)],
                    [2*(x*z - y), 2*(y*z + x), -2 * (x*x + y*y)]]) / d
    return v, CmI


def choose_triple(eps, s, t, X):
    """LP dual at the given pose: maximize margin m over translation."""
    from scipy.optimize import linprog
    from scipy.spatial import ConvexHull
    v, CmI = float_pose_delta(eps, s, t, X)
    C = np.eye(3) + CmI
    # screen basis orthogonal to v
    a = np.cross(v, [0, 0, 1.0])
    if np.linalg.norm(a) < 1e-9:
        a = np.cross(v, [0, 1.0, 0])
    a /= np.linalg.norm(a)
    b = np.cross(v, a)
    proj = lambda y: np.array([a @ y, b @ y])
    outer = np.array([proj(p) for p in VF])
    delta = np.array([proj(CmI @ p) for p in VF])
    inner = outer + delta
    # solve in units of the displacement scale, so that HiGHS tolerances do not
    # swamp margins of order eps * |delta|
    scale = max(np.abs(delta).max() * max(eps, np.abs(delta).max()), 1e-300)
    hull = ConvexHull(outer)
    order = list(hull.vertices)          # counterclockwise
    contacts, rows, rhs = [], [], []
    for k in range(len(order)):
        A_, B_ = order[k], order[(k + 1) % len(order)]
        e = outer[B_] - outer[A_]
        n = np.array([e[1], -e[0]])
        n /= np.linalg.norm(n)
        for P in range(len(VF)):
            for Qv in (A_, B_):
                contacts.append((P, A_, B_, Qv))
                # n . (inner_P + t) + m <= n . outer_Q
                rows.append([1.0, n[0], n[1]])
                rhs.append((n @ (outer[Qv] - outer[P]) - n @ delta[P]) / scale)
    res = linprog([-1, 0, 0], A_ub=rows, b_ub=rhs,
                  bounds=[(None, None)] * 3, method="highs")
    duals = -res.ineqlin.marginals
    pool = [i for i in np.argsort(-duals)[:8] if duals[i] > 1e-12]
    if len(pool) < 3:
        pool = list(np.argsort(-duals)[:8])

    def score(ids):
        """Balanced-triple displacement with determinant weights (float)."""
        us, disp = [], []
        for i in ids:
            P, A_, B_, Qv = contacts[i]
            e = outer[B_] - outer[A_]
            n = np.array([e[1], -e[0]])
            n /= np.linalg.norm(n)
            us.append(n)
            disp.append(n @ (inner[P] - outer[Qv]))
        det = lambda a, b: a[0] * b[1] - a[1] * b[0]
        mu = [det(us[1], us[2]), det(us[2], us[0]), det(us[0], us[1])]
        if min(mu) <= 0:
            if max(mu) >= 0:
                return -np.inf
            mu = [-m for m in mu]
        norm = sum(mu)
        return sum(m * d for m, d in zip(mu, disp)) / norm
    best = max(itertools.combinations(pool, 3), key=score)
    chosen = list(best)
    triple = []
    for i in chosen:
        P, A_, B_, Qv = contacts[i]
        # orientation: sigma with sigma * v.(e x y) = <n, pi y>
        e3 = VF[B_] - VF[A_]
        test = VF[0] + VF[1] * 0.3
        lhs = v @ np.cross(e3, test)
        e = outer[B_] - outer[A_]
        n = np.array([e[1], -e[0]])
        sigma = 1 if np.sign(lhs) == np.sign(n @ proj(test)) else -1
        triple.append((int(P), int(A_), int(B_), int(Qv), sigma))
    return triple, -res.fun * scale


def check_box(triple, centers, radii):
    """Exact check of a triple on a blown-up box (with eps radius/center)."""
    mus, supports, D = certificate_polys(triple)
    E = p_divide_monomial(D, (2, 0, 0, 0, 0, 0))
    if E is None:
        return {"ok": False, "reason": "D not divisible by eps^2"}
    # all weights must share a sign; support gaps <= 0; E >= 0
    mu_lows = [p_box_lower(mu, centers, radii) for mu in mus]
    neg = [p_box_lower(p_scale(mu, -1), centers, radii) for mu in mus]
    sign = 1 if min(mu_lows) >= 0 else (-1 if min(neg) >= 0 else 0)
    if sign == 0:
        return {"ok": False, "reason": "weights", "mu": mu_lows}
    sup = max(-p_box_lower(p_scale(g, -1), centers, radii) for g in supports)
    elow = p_box_lower(p_scale(E, sign), centers, radii)
    return {"ok": sup <= 0 and elow >= 0, "support_upper": float(sup),
            "E_lower": float(elow), "sign": sign}


# ---------------------------------------------------------------------------
# Rotated Cayley coordinates and charts.
#
# Variables (6): 0 eps, 1 s, 2 t, 3 a, 4 b, 5 c with
#     w = B0 + eps (s F1 + t F2),
#     X = eps * scale(a, b, c) . (a M1 + b M2 + c M3)
# where M1 = (1,1,0) (the corner direction m, up to scale), M2 = (1,-1,0),
# M3 = (0,0,1).  In a tube chart the relative part carries an extra factor
# rho, encoded by giving the chart a `tube` flag: then variable 3..5 are the
# unit direction and variable 6 is rho.

M1 = (Q(1), Q(1), Q(0))
M2 = (Q(1), Q(-1), Q(0))
M3 = (Q(0), Q(0), Q(1))


def set_nvars(n):
    global NVARS
    NVARS = n


def chart_polys(tube):
    """Return (W, N, d) polynomials for a chart (tube adds variable 6 = rho)."""
    set_nvars(7 if tube else 6)
    eps_s = p_mul(p_var(0), p_var(1))
    eps_t = p_mul(p_var(0), p_var(2))
    Wp = [p_add(p_const(B0[c]), p_scale(eps_s, F1[c]), p_scale(eps_t, F2[c]))
          for c in range(3)]
    scale = p_var(0) if not tube else p_mul(p_var(0), p_var(6))
    X = []
    for c in range(3):
        lin = p_add(p_scale(p_var(3), M1[c]), p_scale(p_var(4), M2[c]),
                    p_scale(p_var(5), M3[c]))
        X.append(p_mul(scale, lin))
    x, y, z = X
    one = p_const(1)

    def sq(a):
        return p_mul(a, a)

    def m2(a, b):
        return p_scale(p_mul(a, b), 2)
    N = [[p_add(one, sq(x), p_scale(sq(y), -1), p_scale(sq(z), -1)),
          p_add(m2(x, y), p_scale(z, -2)), p_add(m2(x, z), p_scale(y, 2))],
         [p_add(m2(x, y), p_scale(z, 2)),
          p_add(one, p_scale(sq(x), -1), sq(y), p_scale(sq(z), -1)),
          p_add(m2(y, z), p_scale(x, -2))],
         [p_add(m2(x, z), p_scale(y, -2)), p_add(m2(y, z), p_scale(x, 2)),
          p_add(one, p_scale(sq(x), -1), p_scale(sq(y), -1), sq(z))]]
    d = p_add(one, sq(x), sq(y), sq(z))
    return Wp, N, d


def chart_certificate_polys(triple, tube):
    global W, N_POLY, D_POLY
    W, N_POLY, D_POLY = chart_polys(tube)
    return certificate_polys(triple)


def float_point(point, tube):
    """Chart coordinates -> (eps, s, t, X-vector in original Cayley coords)."""
    eps, s, t, a, b, c = point[:6]
    rho = point[6] if tube else 1.0
    Xv = rho * (a * np.array([1, 1, 0.0]) + b * np.array([1, -1, 0.0]) +
                c * np.array([0, 0, 1.0]))
    return eps, s, t, Xv


def eps_parts(p):
    """Split p = sum_k eps^k q_k (eps is variable 0)."""
    parts = {}
    for e, c in p.items():
        k = e[0]
        q = parts.setdefault(k, {})
        q[(0,) + e[1:]] = q.get((0,) + e[1:], 0) + c
    return parts


def p_lower_eps(p, centers, radii):
    """Sound lower bound using eps in [0, eps0]: strip the common eps power
    (only the sign matters then) and bound the powers separately."""
    parts = eps_parts(p)
    if not parts:
        return Q(0)
    low = min(parts)
    eps0 = centers[0] + radii[0]
    c0 = [Q(0)] + list(centers[1:])
    r0 = [Q(0)] + list(radii[1:])
    total = p_box_lower(parts[low], c0, r0)
    for k, q in parts.items():
        if k == low:
            continue
        total += min(Q(0), eps0 ** (k - low) * p_box_lower(q, c0, r0))
    return total


def exact_check(triple, tube, centers, radii, split_var=None):
    """Exact check on a chart box.

    The displacement is divided by eps (and rho in a tube).  With
    `split_var` (the alpha coordinate, index 3), the quotient F is split as
    F = alpha * A + eps * B and both parts must be nonnegative with
    alpha, eps >= 0 on the box."""
    mus, supports, D = chart_certificate_polys(triple, tube)
    monomial = [1] + [0] * (NVARS - 1)
    if tube:
        monomial[6] = 1
    F = p_divide_monomial(D, tuple(monomial))
    if F is None:
        return {"ok": False, "reason": "division"}
    mu_lows = [p_lower_eps(mu, centers, radii) for mu in mus]
    neg = [p_lower_eps(p_scale(mu, -1), centers, radii) for mu in mus]
    sign = 1 if min(mu_lows) >= 0 else (-1 if min(neg) >= 0 else 0)
    if sign == 0:
        return {"ok": False, "reason": "weights"}
    sup = max(-p_lower_eps(p_scale(g, -1), centers, radii) for g in supports)
    if sup > 0:
        return {"ok": False, "reason": "support", "support_upper": float(sup)}
    F = p_scale(F, sign)
    if split_var is None:
        low = p_lower_eps(F, centers, radii)
        return {"ok": low >= 0, "reason": "F", "lower": float(low)}
    # F = alpha * A + eps * B: terms divisible by alpha go to A (first).
    # On a box with alpha <= 0 we use (-alpha) * (-A) instead.
    alpha_sign = 1 if centers[split_var] - radii[split_var] >= 0 else -1
    if alpha_sign == -1 and centers[split_var] + radii[split_var] > 0:
        return {"ok": False, "reason": "split-straddle"}
    A, Bp = {}, {}
    for e, c in F.items():
        if e[split_var] >= 1:
            e2 = list(e)
            e2[split_var] -= 1
            A[tuple(e2)] = A.get(tuple(e2), 0) + c
        elif e[0] >= 1:
            e2 = list(e)
            e2[0] -= 1
            Bp[tuple(e2)] = Bp.get(tuple(e2), 0) + c
        else:
            return {"ok": False, "reason": "split"}
    la = p_lower_eps(p_scale(A, alpha_sign), centers, radii)
    lb = p_lower_eps(Bp, centers, radii)
    return {"ok": la >= 0 and lb >= 0, "reason": "split",
            "lower": (float(la), float(lb))}


# ---------------------------------------------------------------------------
# Corner search (prototype): cover the faces of the normalized blow-up cube.

FACES = [(1, Q(1)), (2, Q(-1)), (3, Q(1)), (3, Q(-1)), (4, Q(1)), (4, Q(-1)),
         (5, Q(1)), (5, Q(-1))]
# the view offset lives in the chamber quadrant s >= 0, t <= 0
RANGES = {1: (Q(0), Q(1)), 2: (Q(-1), Q(0)), 3: (Q(-1), Q(1)),
          4: (Q(-1), Q(1)), 5: (Q(-1), Q(1))}


def face_root(face, eps0):
    k, value = face
    centers, radii = [eps0 / 2], [eps0 / 2]
    for v in range(1, 6):
        if v == k:
            centers.append(value)
            radii.append(Q(0))
        else:
            lo, hi = RANGES[v]
            centers.append((lo + hi) / 2)
            radii.append((hi - lo) / 2)
    return centers, radii


def flip_prune_polys():
    """G_k = l_k(X, w)^2 - 2 |w|^2 in chart coordinates (non-tube)."""
    global W, N_POLY, D_POLY
    W, N_POLY, D_POLY = chart_polys(False)
    X = []
    for c in range(3):
        lin = p_add(p_scale(p_var(3), M1[c]), p_scale(p_var(4), M2[c]),
                    p_scale(p_var(5), M3[c]))
        X.append(p_mul(p_var(0), lin))
    one = p_const(1)
    out = []
    for k in range(12):
        coeff = st.FLIP_COEFF[k]
        ell = {}
        for c in range(3):
            lin = p_add(p_const(coeff[c][0]), p_scale(X[0], coeff[c][1]),
                        p_scale(X[1], coeff[c][2]), p_scale(X[2], coeff[c][3]))
            ell = p_add(ell, p_mul(W[c], lin))
        norm = p_add(*(p_mul(W[c], W[c]) for c in range(3)))
        out.append(p_add(p_mul(ell, ell), p_scale(norm, -2)))
    return out


_FLIP_POLYS = None


def flip_pruned(centers, radii):
    """Some G_k > 0 on the box: outside the flip Dirichlet cell."""
    global _FLIP_POLYS
    if _FLIP_POLYS is None:
        _FLIP_POLYS = flip_prune_polys()
    for G in _FLIP_POLYS:
        if p_lower_eps(G, centers, radii) > 0:
            return True
    return False


def try_box(centers, radii, eps_probe):
    if flip_pruned(centers, radii):
        return {"ok": True, "reason": "flip"}
    point = [float(x) for x in centers]
    eps, s, t, Xv = float_point(point, False)
    if max(abs(x) for x in Xv) < 1e-12 and s == 0 and t == 0:
        return {"ok": False, "reason": "degenerate"}
    triple, margin = choose_triple(eps_probe, s, t, Xv)
    if len(triple) < 3:
        return {"ok": False, "reason": "lp"}
    result = exact_check(triple, False, centers, radii)
    if not result["ok"]:
        lo, hi = centers[3] - radii[3], centers[3] + radii[3]
        if lo == 0 or hi == 0:
            split = exact_check(triple, False, centers, radii, split_var=3)
            if split["ok"]:
                result = split
    result["triple"] = triple
    result["margin"] = margin / eps_probe
    return result


def corner_search(eps0, max_boxes=20000, min_radius=Q(1, 512)):
    import collections
    stack = [face_root(face, eps0) for face in FACES]
    counts = collections.Counter()
    stuck = []
    while stack and sum(counts.values()) < max_boxes:
        centers, radii = stack.pop()
        result = try_box(centers, radii, float(eps0) / 4)
        if result["ok"]:
            counts["ok"] += 1
            continue
        lo3, hi3 = centers[3] - radii[3], centers[3] + radii[3]
        if lo3 < 0 < hi3 and abs(centers[3]) < radii[3] / 2 and radii[3] <= Q(1, 8):
            # split at alpha = 0 exactly so the degenerate plane is a face
            for (a, b) in ((lo3, Q(0)), (Q(0), hi3)):
                c2, r2 = list(centers), list(radii)
                c2[3], r2[3] = (a + b) / 2, (b - a) / 2
                stack.append((c2, r2))
            counts["split"] += 1
            continue
        k = max(range(1, 6), key=lambda i: radii[i])
        if radii[k] <= min_radius:
            counts["stuck"] += 1
            if len(stuck) < 30:
                stuck.append(([float(x) for x in centers], result["reason"],
                              result.get("margin")))
            continue
        counts["split"] += 1
        for sign in (-1, 1):
            c2, r2 = list(centers), list(radii)
            r2[k] = radii[k] / 2
            c2[k] = centers[k] + sign * r2[k]
            stack.append((c2, r2))
    return counts, stuck, len(stack)


if __name__ == "__main__":
    eps0 = Q(sys.argv[1]) if len(sys.argv) > 1 else Q(1, 1000)
    counts, stuck, pending = corner_search(eps0, int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
    print(dict(counts), "pending", pending)
    for s in stuck:
        print(s)
