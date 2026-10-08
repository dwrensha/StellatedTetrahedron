#!/usr/bin/env python3
"""Corner blow-up search (prototype) for the stellated tetrahedron.

Variables: 0 eps, 1 lam, 2 u, 3 a, 4 b, 5 c.  The view offset from the
corner b = (1/2,1/2,0) is eps * lam * uhat, where uhat runs along the outer
boundary of the chamber quadrant, split into two segments:

    segment "A": uhat = (1, -u),   segment "B": uhat = (u, -1),   u in [0,1]

(in the (s,t) basis F1, F2 of stellated_corner).  The Cayley vector is
X = eps (a M1 + b M2 + c M3).  Normalization: lam = 1 with (a,b,c) in the
cube, or (a,b,c) on a cube face with lam in [0,1].

Every check is exact: support gaps and weights by sign after stripping the
powers of the anchored variables eps and lam; the displacement divided by
eps, optionally split as alpha*A + eps*B on boxes anchored at a = 0; the
flip prune by sign of l^2 - 2|w|^2.
"""
import collections
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
import stellated_corner as sc  # noqa: E402
import stellated_certificate_search as st  # noqa: E402

p_add, p_mul, p_scale, p_var, p_const = (sc.p_add, sc.p_mul, sc.p_scale,
                                         sc.p_var, sc.p_const)
TIES = {"A": [Q(9, 20), Q(9, 11)], "B": [Q(1, 2)]}
ANCHORED = (0, 1)


# Second first-order-degenerate line on segment B (the other edge of the
# degenerate sector at a = 0): c + SKEW_K b = 0.  The skew chart uses
# eta' = c + SKEW_K b as its last coordinate.
SKEW_K = Q(682, 279)


# The tie tube chart follows the collinear-triple tie as the rotation moves it:
# u = tie + U' + rho * (ell . (a, b, c)), variable 2 being U'.
TIE_ELL = {Q(9, 11): (Q(12587, 6820), Q(2), Q(9, 11))}


def u_poly(tie):
    if tie is None:
        return p_var(2)
    la, lb, lc = TIE_ELL[tie]
    ell = p_add(p_scale(p_var(3), la), p_scale(p_var(4), lb), p_scale(p_var(5), lc))
    return p_add(p_const(tie), p_var(2), p_mul(p_var(6), ell))


ATUBE_A = Q(8)


def chart(segment, tube=False, wedge=False, wtube=False, skew=False, tie=None,
          lin=None, amode=None):
    """`lin = (u, a, b, c)` polynomials reparametrize the plain chart."""
    sc.set_nvars(7 if (tube or wtube) else 6)
    lam_u = p_mul(p_var(1), lin[0] if lin else u_poly(tie))
    if segment == "A":
        s_poly, t_poly = p_var(1), p_scale(lam_u, -1)
    else:
        s_poly, t_poly = lam_u, p_scale(p_var(1), -1)
    W = [p_add(p_const(sc.B0[c]),
               p_mul(p_var(0), p_add(p_scale(s_poly, sc.F1[c]),
                                     p_scale(t_poly, sc.F2[c]))))
         for c in range(3)]
    scale = p_mul(p_var(0), p_var(6)) if tube else p_var(0)
    if wtube:
        # X^ = sigma (abar M1 + ebar D2) + tau D1   (variables 3 abar, 4 tau,
        # 5 ebar, 6 sigma)
        half_t = p_scale(t_poly, Q(1, 2))
        d1b, d1c = p_scale(half_t, -1), p_scale(s_poly, -1)
        d2b, d2c = s_poly, p_scale(half_t, -1)
        sig = p_var(6)
        a_poly = p_mul(sig, p_var(3))
        b_poly = p_add(p_mul(p_var(4), d1b), p_mul(sig, p_mul(p_var(5), d2b)))
        c_poly = p_add(p_mul(p_var(4), d1c), p_mul(sig, p_mul(p_var(5), d2c)))
        X = [p_mul(p_var(0), p_add(p_scale(a_poly, sc.M1[c]),
                                   p_scale(b_poly, sc.M2[c]),
                                   p_scale(c_poly, sc.M3[c]))) for c in range(3)]
    elif wedge:
        # (b, c) = tau * D1 + eta * D2 with D1 = (-t/2, -s), D2 = (s, -t/2)
        half_t = p_scale(t_poly, Q(1, 2))
        b_poly = p_add(p_mul(p_var(4), p_scale(half_t, -1)), p_mul(p_var(5), s_poly))
        c_poly = p_add(p_mul(p_var(4), p_scale(s_poly, -1)),
                       p_mul(p_var(5), p_scale(half_t, -1)))
        X = [p_mul(scale, p_add(p_scale(p_var(3), sc.M1[c]),
                                p_scale(b_poly, sc.M2[c]),
                                p_scale(c_poly, sc.M3[c]))) for c in range(3)]
    elif amode:
        # tube with a = eps * alpha ("eps") or a = +-ATUBE_A eps + w ("+", "-")
        a3 = lin[1] if lin else p_var(3)
        b4 = lin[2] if lin else p_var(4)
        c5 = lin[3] if lin else p_var(5)
        if amode == "eps":
            a_poly = p_mul(p_var(0), a3)
        else:
            sgn = 1 if amode == "+" else -1
            a_poly = p_add(p_scale(p_var(0), sgn * ATUBE_A), a3)
        c_poly = (p_add(c5, p_scale(b4, -SKEW_K)) if skew else c5)
        X = [p_mul(scale, p_add(p_scale(a_poly, sc.M1[c]),
                                p_scale(b4, sc.M2[c]),
                                p_scale(c_poly, sc.M3[c]))) for c in range(3)]
    elif lin:
        X = [p_mul(scale, p_add(p_scale(lin[1], sc.M1[c]),
                                p_scale(lin[2], sc.M2[c]),
                                p_scale(lin[3], sc.M3[c]))) for c in range(3)]
    elif skew:
        c_poly = p_add(p_var(5), p_scale(p_var(4), -SKEW_K))
        X = [p_mul(scale, p_add(p_scale(p_var(3), sc.M1[c]),
                                p_scale(p_var(4), sc.M2[c]),
                                p_scale(c_poly, sc.M3[c]))) for c in range(3)]
    else:
        X = [p_mul(scale, p_add(p_scale(p_var(3), sc.M1[c]),
                                p_scale(p_var(4), sc.M2[c]),
                                p_scale(p_var(5), sc.M3[c]))) for c in range(3)]
    x, y, z = X
    one = p_const(1)

    def sq(v):
        return p_mul(v, v)

    def m2(v, w):
        return p_scale(p_mul(v, w), 2)
    N = [[p_add(one, sq(x), p_scale(sq(y), -1), p_scale(sq(z), -1)),
          p_add(m2(x, y), p_scale(z, -2)), p_add(m2(x, z), p_scale(y, 2))],
         [p_add(m2(x, y), p_scale(z, 2)),
          p_add(one, p_scale(sq(x), -1), sq(y), p_scale(sq(z), -1)),
          p_add(m2(y, z), p_scale(x, -2))],
         [p_add(m2(x, z), p_scale(y, -2)), p_add(m2(y, z), p_scale(x, 2)),
          p_add(one, p_scale(sq(x), -1), p_scale(sq(y), -1), sq(z))]]
    d = p_add(one, sq(x), sq(y), sq(z))
    return W, N, d, X


def corner_lower(p, centers, radii, from_low=True):
    """Expand around a box corner: x = corner +- width * tau, tau in [0,1]^n.
    Then p >= constant + sum of negative coefficients."""
    n = len(centers)
    corner = [c - r if from_low else c + r for c, r in zip(centers, radii)]
    step = [2 * r if from_low else -2 * r for r in radii]
    shifted = sc.p_shift(p, corner, step)
    zero = (0,) * n
    return shifted.get(zero, Q(0)) + sum(
        c for e, c in shifted.items() if e != zero and c < 0)


def box_lower(p, centers, radii):
    return max(sc.p_box_lower(p, centers, radii),
               corner_lower(p, centers, radii, True),
               corner_lower(p, centers, radii, False))


SIMPLE_BOUNDS = bool(__import__("os").environ.get("CORNER_SIMPLE_BOUNDS"))


def lower_simple(p, centers, radii):
    """Mirror of the planned Lean checker: strip the common monomial in
    variables nonnegative on the box, then the best of the centered bound
    and the two corner-expansion bounds."""
    if not p:
        return Q(0)
    n = len(centers)
    nonneg = [v for v in range(n) if centers[v] - radii[v] >= 0]
    common = {v: min(e[v] for e in p) for v in nonneg}
    q = {tuple(e[v] - common.get(v, 0) for v in range(n)): c
         for e, c in p.items()}
    return box_lower(q, centers, radii)


def lower(p, centers, radii):
    if SIMPLE_BOUNDS:
        return lower_simple(p, centers, radii)
    return lower_full(p, centers, radii)


def lower_full(p, centers, radii):
    """Sign-sound bound (the result has the sign-relevant meaning: if it is
    >= 0 then p >= 0 on the box, and if > 0 then p > 0 wherever the stripped
    nonnegative variables are nonzero).  Sound lower bound: strip common powers of anchored variables (those
    whose box starts at 0), then bound the anchored-power parts separately."""
    if not p:
        return Q(0)
    # Sign checks only: common powers of variables that are >= 0 on the box
    # are positive factors and can be divided out.
    n = len(centers)
    nonneg = [v for v in range(n) if centers[v] - radii[v] >= 0]
    common = {v: min(e[v] for e in p) for v in nonneg}
    if any(common.values()):
        p = {tuple(e[v] - common.get(v, 0) for v in range(n)): c
             for e, c in p.items()}
    anchored = [v for v in ANCHORED if centers[v] - radii[v] == 0]
    mins = {v: min(e[v] for e in p) for v in anchored}
    parts = collections.defaultdict(dict)
    for e, c in p.items():
        key = tuple(e[v] - mins[v] for v in anchored)
        rest = list(e)
        for v in anchored:
            rest[v] = 0
        parts[key][tuple(rest)] = parts[key].get(tuple(rest), 0) + c
    c0, r0 = list(centers), list(radii)
    for v in anchored:
        c0[v], r0[v] = Q(0), Q(0)
    total = Q(0)
    for key, q in parts.items():
        bound = box_lower(q, c0, r0)
        if all(k == 0 for k in key):
            total += bound
        else:
            scale = Q(1)
            for v, k in zip(anchored, key):
                scale *= (centers[v] + radii[v]) ** k
            total += min(Q(0), scale * bound)
    return total


class Chart:
    def __init__(self, segment, tube=False, wedge=False, wtube=False,
                 skew=False, tie=None, aff=None, amode=None):
        self.segment = segment
        self.amode = amode
        self.tie = tie
        self.aff = aff
        lin = None
        if aff:
            sc.set_nvars(6)
            lin = []
            for row in aff:
                pm = p_const(row[0]) if row[0] else {}
                for k in range(4):
                    if row[k + 1]:
                        pm = p_add(pm, p_scale(p_var(2 + k), row[k + 1]))
                lin.append(pm)
            lin = tuple(lin)
        self.skew = skew
        self.tube = tube
        self.wedge = wedge
        self.wtube = wtube
        self.nvars = 7 if (tube or wtube) else 6
        self.W, self.N, self.d, self.X = chart(segment, tube, wedge, wtube,
                                               skew, tie, lin, amode)
        self.flip = []
        norm = p_add(*(p_mul(self.W[c], self.W[c]) for c in range(3)))
        for k in range(12):
            coeff = st.FLIP_COEFF[k]
            ell = {}
            for c in range(3):
                lin = p_add(p_const(coeff[c][0]),
                            p_scale(self.X[0], coeff[c][1]),
                            p_scale(self.X[1], coeff[c][2]),
                            p_scale(self.X[2], coeff[c][3]))
                ell = p_add(ell, p_mul(self.W[c], lin))
            self.flip.append(p_add(p_mul(ell, ell), p_scale(norm, -2)))

    def certificate(self, triple):
        sc.set_nvars(self.nvars)
        sc.W, sc.N_POLY, sc.D_POLY = self.W, self.N, self.d
        return sc.certificate_polys(triple)

    def float_point(self, centers):
        eps, lam, u, a, b, c = (float(x) for x in centers[:6])
        rho = float(centers[6]) if self.tube else 1.0

        if self.aff:
            t = [u, a, b, c]
            u, a, b, c = (float(row[0]) + sum(float(row[k + 1]) * t[k] for k in range(4))
                          for row in self.aff)
        if self.amode == "eps":
            a = eps * a
        elif self.amode in ("+", "-"):
            a = (1 if self.amode == "+" else -1) * float(ATUBE_A) * eps + a
        if self.tie is not None:
            la, lb, lc = (float(x) for x in TIE_ELL[self.tie])
            u = float(self.tie) + u + rho * (la * a + lb * b + lc * c)
        s, t = (lam, -lam * u) if self.segment == "A" else (lam * u, -lam)
        if self.skew:
            c = c - float(SKEW_K) * b
        if self.wedge:
            tau, eta = b, c
            b = -tau * t / 2 + eta * s
            c = -tau * s - eta * t / 2
        if self.wtube:
            sig = float(centers[6])
            abar, tau, ebar = a, b, c
            a = sig * abar
            eta = sig * ebar
            b = -tau * t / 2 + eta * s
            c = -tau * s - eta * t / 2
            rho = 1.0
        Xv = rho * (a * np.array([1, 1, 0.0]) + b * np.array([1, -1, 0.0]) +
                    c * np.array([0, 0, 1.0]))
        return s, t, Xv


def check(chart_, triple, centers, radii):
    mus, supports, D = chart_.certificate(triple)
    mono = [1] + [0] * (chart_.nvars - 1)
    if chart_.tube:
        mono[6] = 1
    F = sc.p_divide_monomial(D, tuple(mono))
    if F is None:
        return "division"
    mu_low = [lower(mu, centers, radii) for mu in mus]
    mu_neg = [lower(p_scale(mu, -1), centers, radii) for mu in mus]
    sign = 1 if min(mu_low) >= 0 else (-1 if min(mu_neg) >= 0 else 0)
    if sign == 0:
        return "weights"
    if any(lower(p_scale(g, -1), centers, radii) < 0 for g in supports):
        return "support"
    F = p_scale(F, sign)
    if lower(F, centers, radii) >= 0:
        return "ok"
    if chart_.wedge:
        return check_multi_split(F, centers, radii)
    if chart_.wtube:
        return check_multi_split(F, centers, radii, split_vars=(3, 6))
    lo, hi = centers[3] - radii[3], centers[3] + radii[3]
    if lo == 0 or hi == 0:
        alpha_sign = 1 if lo == 0 else -1
        A, B = {}, {}
        for e, c in F.items():
            if e[3] >= 1:
                e2 = list(e)
                e2[3] -= 1
                A[tuple(e2)] = A.get(tuple(e2), 0) + c
            elif e[0] >= 1:
                e2 = list(e)
                e2[0] -= 1
                B[tuple(e2)] = B.get(tuple(e2), 0) + c
            else:
                return "F"
        if (lower(p_scale(A, alpha_sign), centers, radii) >= 0 and
                lower(B, centers, radii) >= 0):
            return "ok-split"
    return "F"


SPLIT_VARS = (3, 5)      # alpha, eta in the wedge chart


def check_multi_split(F, centers, radii, split_vars=SPLIT_VARS):
    """F = alpha*A + eta*B + eps*C (first divisible factor wins); each part
    times the sign of its factor on the box must be nonnegative."""
    SPLIT = split_vars
    signs = {}
    for v in SPLIT:
        lo, hi = centers[v] - radii[v], centers[v] + radii[v]
        signs[v] = 1 if lo >= 0 else (-1 if hi <= 0 else 0)
    parts = {v: {} for v in SPLIT + (0,)}
    rest = {}
    for e, c in F.items():
        for v in SPLIT + (0,):
            if e[v] >= 1:
                e2 = list(e)
                e2[v] -= 1
                parts[v][tuple(e2)] = parts[v].get(tuple(e2), 0) + c
                break
        else:
            rest[e] = rest.get(e, 0) + c
    if rest and lower(rest, centers, radii) < 0:
        return "F"
    for v in SPLIT:
        if parts[v] and signs[v] == 0:
            low = lower(F, centers, radii)
            return "ok" if low >= 0 else "F"
    for v in SPLIT:
        if parts[v] and lower(p_scale(parts[v], signs[v]), centers, radii) < 0:
            return "F"
    if parts[0] and lower(parts[0], centers, radii) < 0:
        return "F"
    return "ok-split"


ALPHA0 = Q(1, 8)
ETA0 = Q(1, 8)
TAU0, TAU1 = Q(1, 8), Q(3, 4)


def wedge_roots(eps0):
    out = []
    for a_lo, a_hi in ((-ALPHA0, Q(0)), (Q(0), ALPHA0)):
        for e_lo, e_hi in ((-ETA0, Q(0)), (Q(0), ETA0)):
            c = [eps0 / 2, Q(1), Q(1, 2), (a_lo + a_hi) / 2, (TAU0 + TAU1) / 2,
                 (e_lo + e_hi) / 2]
            r = [eps0 / 2, Q(0), Q(1, 2), (a_hi - a_lo) / 2, (TAU1 - TAU0) / 2,
                 (e_hi - e_lo) / 2]
            out.append((c, r))
    return out


SIGMA0 = Q(1, 16)
EPS_SPLIT = bool(__import__("os").environ.get("CORNER_EPS_SPLIT"))


def wtube_roots(eps0):
    out = []
    for v in (3, 5):
        for value in (Q(1), Q(-1)):
            c = [eps0 / 2, Q(1), Q(1, 2), Q(0), (TAU0 + TAU1) / 2, Q(0), SIGMA0 / 2]
            r = [eps0 / 2, Q(0), Q(1, 2), Q(1), (TAU1 - TAU0) / 2, Q(1), SIGMA0 / 2]
            c[v], r[v] = value, Q(0)
            out.append((c, r))
    return out


def inside_wtube(centers, radii):
    """Wedge-chart boxes with |alpha|, |eta| <= SIGMA0 go to the wedge tube."""
    return all(abs(centers[v]) + radii[v] <= SIGMA0 for v in (3, 5))


def inside_wedge(segment, centers, radii):
    """Float hand-off test for plain lambda=1 boxes (prototype only)."""
    if radii[1] != 0 or centers[1] != 1:
        return False
    if abs(centers[3]) + radii[3] > ALPHA0:
        return False
    for u in np.linspace(float(centers[2] - radii[2]), float(centers[2] + radii[2]), 5):
        s, t = (1.0, -u) if segment == "A" else (u, -1.0)
        d1 = np.array([-t / 2, -s])
        d2 = np.array([s, -t / 2])
        n2 = d1 @ d1
        for b in (centers[4] - radii[4], centers[4] + radii[4]):
            for c in (centers[5] - radii[5], centers[5] + radii[5]):
                v = np.array([float(b), float(c)])
                tau, eta = v @ d1 / n2, v @ d2 / n2
                if not (float(TAU0) <= tau <= float(TAU1) and abs(eta) <= float(ETA0)):
                    return False
    return True


def roots(segment, eps0):
    """Faces of the normalized blow-up for one view segment."""
    out = []
    base_c = [eps0 / 2, Q(1, 2), Q(1, 2), Q(0), Q(0), Q(0)]
    base_r = [eps0 / 2, Q(1, 2), Q(1, 2), Q(1), Q(1), Q(1)]
    c, r = list(base_c), list(base_r)
    c[1], r[1] = Q(1), Q(0)                     # lam = 1 face
    out.append((c, r))
    for v in (3, 4, 5):
        for value in (Q(1), Q(-1)):
            c, r = list(base_c), list(base_r)
            c[v], r[v] = value, Q(0)
            out.append((c, r))
    return out


RHO0 = Q(1, 16)


def tube_roots(eps0):
    out = []
    for v in (3, 4, 5):
        for value in (Q(1), Q(-1)):
            c = [eps0 / 2, Q(1), Q(1, 2), Q(0), Q(0), Q(0), RHO0 / 2]
            r = [eps0 / 2, Q(0), Q(1, 2), Q(1), Q(1), Q(1), RHO0 / 2]
            c[v], r[v] = value, Q(0)
            out.append((c, r))
    return out


def inside_tube(centers, radii, tube):
    return (not tube and radii[1] == 0 and centers[1] == 1 and
            all(abs(centers[v]) + radii[v] <= RHO0 for v in (3, 4, 5)))


def search_root(job):
    segment, tube, root, eps0, max_boxes, min_radius, probe = job[:7]
    wedge = len(job) > 7 and job[7] == True
    wtube = len(job) > 7 and job[7] == "wtube"
    counts = collections.Counter()
    stuck = []
    chart_ = Chart(segment, tube, wedge, wtube)
    stack = [root]
    if True:
        while stack and sum(counts.values()) < max_boxes:
            centers, radii = stack.pop()
            if inside_tube(centers, radii, tube):
                counts["tube-handoff"] += 1
                continue
            if not tube and not wedge and not wtube and \
                    inside_wedge(segment, centers, radii):
                counts["wedge-handoff"] += 1
                continue
            if wedge and inside_wtube(centers, radii):
                counts["wtube-handoff"] += 1
                continue
            if any(lower(G, centers, radii) > 0 for G in chart_.flip):
                counts["flip"] += 1
                continue
            probes = [(list(centers), probe)]
            if wtube:
                # The triple active on the wedge line with the best
                # directional derivative: sigma -> 0 with eps << sigma.
                tiny = list(centers)
                tiny[6] = Q(1, 10**4)
                probes.append((tiny, 1e-8))
                small = list(centers)
                small[6] = Q(2) * Q(Fraction(probe).limit_denominator(10**9))
                probes.append((small, probe))
            result = "degenerate"
            for probe_centers, probe_eps in probes:
                s, t, Xv = chart_.float_point(probe_centers)
                if s == 0 and t == 0 and np.abs(Xv).max() == 0:
                    continue
                triple, _ = sc.choose_triple(probe_eps, s, t, Xv)
                result = (check(chart_, triple, centers, radii)
                          if len(triple) == 3 else "lp")
                if result.startswith("ok"):
                    break
            if result.startswith("ok"):
                counts[result] += 1
                continue
            # forced exact splits: u at tie points, a at 0
            lo, hi = centers[2] - radii[2], centers[2] + radii[2]
            tie = next((x for x in TIES[segment] if lo < x < hi), None)
            lo3, hi3 = centers[3] - radii[3], centers[3] + radii[3]
            if tie is not None:
                cuts = (2, [(lo, tie), (tie, hi)])
            elif lo3 < 0 < hi3 and radii[3] <= Q(1, 4):
                cuts = (3, [(lo3, Q(0)), (Q(0), hi3)])
            elif wedge and (centers[5] - radii[5]) < 0 < (centers[5] + radii[5]):
                cuts = (5, [(centers[5] - radii[5], Q(0)), (Q(0), centers[5] + radii[5])])
            else:
                # eps is split too (relative to eps0) when EPS_SPLIT is set
                k = max(range(0 if EPS_SPLIT else 1, len(centers)),
                        key=lambda i: radii[i] / eps0 if i == 0 else radii[i])
                if k == 0 and radii[0] / eps0 <= min_radius:
                    k = max(range(1, len(centers)), key=lambda i: radii[i])
                if radii[k] <= min_radius:
                    counts["stuck-" + result] += 1
                    if len(stuck) < 20:
                        stuck.append((segment, [float(x) for x in centers],
                                      result, list(centers), list(radii)))
                    continue
                m = centers[k]
                cuts = (k, [(m - radii[k], m), (m, m + radii[k])])
            counts["split"] += 1
            k, pieces = cuts
            for a, b in pieces:
                c2, r2 = list(centers), list(radii)
                c2[k], r2[k] = (a + b) / 2, (b - a) / 2
                stack.append((c2, r2))
        counts["pending"] = len(stack)
    return counts, stuck


def search(eps0, max_boxes=50000, min_radius=Q(1, 1024), probe=None,
           jobs=14):
    import multiprocessing
    probe = probe or float(eps0) / 4
    tasks = [(segment, False, root, eps0, max_boxes, min_radius, probe)
             for segment in ("A", "B") for root in roots(segment, eps0)]
    tasks += [(segment, True, root, eps0, max_boxes, min_radius, probe)
              for segment in ("A", "B") for root in tube_roots(eps0)]
    tasks += [(segment, False, root, eps0, max_boxes, min_radius, probe, True)
              for segment in ("A", "B") for root in wedge_roots(eps0)]
    tasks += [(segment, False, root, eps0, max_boxes, min_radius, probe, "wtube")
              for segment in ("A", "B") for root in wtube_roots(eps0)]
    total = collections.Counter()
    stuck = []
    with multiprocessing.get_context("fork").Pool(jobs) as pool:
        for counts, s in pool.imap_unordered(search_root, tasks):
            total.update(counts)
            stuck.extend(s[:3])
            print(dict(counts), flush=True)
    return total, stuck


if __name__ == "__main__":
    eps0 = Q(sys.argv[1]) if len(sys.argv) > 1 else Q(1, 1000)
    counts, stuck = search(eps0, int(sys.argv[2]) if len(sys.argv) > 2
                           else 50000)
    print(dict(counts))
    for item in stuck:
        print(item)
