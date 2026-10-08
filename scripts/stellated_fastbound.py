"""numba version of `stellated_corner_tree.float_box_lower`: the float Taylor
shift of a sparse polynomial to a box and its reject-only lower bound.  Only a
screening heuristic — every acceptance is decided by the exact check — so it
needs to agree with the numpy version up to rounding, not bit for bit."""
import math

import numba
import numpy as np


_BINOM = np.array([[math.comb(n, k) for k in range(64)] for n in range(64)], dtype=float)


@numba.njit(cache=True)
def _shift_bound(E, C, a, b, centered, binom):
    n, m = E.shape
    E = E.copy()
    C = C.copy()
    for i in range(m):
        if a[i] == 0.0 and b[i] == 1.0:
            continue
        total = 0
        anyk = False
        for t in range(n):
            total += E[t, i] + 1
            if E[t, i] > 0:
                anyk = True
        if not anyk:
            continue
        E2 = np.empty((total, m), dtype=np.int64)
        C2 = np.empty(total)
        p = 0
        for t in range(n):
            k = E[t, i]
            for j in range(k + 1):
                coef = binom[k, j] * a[i] ** (k - j) * b[i] ** j
                for q in range(m):
                    E2[p, q] = E[t, q]
                E2[p, i] = j
                C2[p] = C[t] * coef
                p += 1
        E, C, n = E2, C2, total
    keys = np.zeros(n, dtype=np.int64)
    for t in range(n):
        key = 0
        mult = 1
        for q in range(m):
            key += E[t, q] * mult
            mult *= 64
        keys[t] = key
    order = np.argsort(keys, kind="mergesort")
    const = 0.0
    rest_abs = 0.0
    rest_neg = 0.0
    scale = 0.0
    t = 0
    while t < n:
        key = keys[order[t]]
        s = 0.0
        while t < n and keys[order[t]] == key:
            s += C[order[t]]
            t += 1
        scale += abs(s)
        if key == 0:
            const += s
        else:
            rest_abs += abs(s)
            if s < 0:
                rest_neg += s
    bound = const - rest_abs if centered else const + rest_neg
    return bound, scale


@numba.njit(cache=True)
def box_lower(E, C, c, r, binom):
    b1, s1 = _shift_bound(E, C, c, r, True, binom)
    b2, s2 = _shift_bound(E, C, c - r, 2.0 * r, False, binom)
    b3, s3 = _shift_bound(E, C, c + r, -2.0 * r, False, binom)
    return max(b1, b2, b3), max(s1, s2, s3)


def float_box_lower(p, centers, radii):
    E = np.array(list(p.keys()), dtype=np.int64)
    C = np.array([float(v) for v in p.values()])
    c = np.array([float(x) for x in centers])
    r = np.array([float(x) for x in radii])
    return box_lower(E, C, c, r, _BINOM)
