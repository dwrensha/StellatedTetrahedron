//! Float screening pass of the stellated corner certificate check
//! (`stellated_corner_tree._cert_valid` with `FLOAT_ONLY = True`).
//!
//! The certificate polynomials are built exactly (i128 rationals, checked;
//! overflow raises and the caller falls back to Python), so every structural
//! decision (terms present, common monomials, base-monomial divisibility) is
//! exact.  The box bounds are floats with the Python screen's tolerance.  The
//! screen only decides which candidates reach the exact Python pass, which
//! alone accepts certificates; Lean re-checks every emitted row.

use pyo3::exceptions::PyOverflowError;
use pyo3::prelude::*;
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

static FBOX_CALLS: AtomicU64 = AtomicU64::new(0);
static FBOX_NS: AtomicU64 = AtomicU64::new(0);
static FBOX_TERMS_IN: AtomicU64 = AtomicU64::new(0);
static FBOX_TERMS_PEAK: AtomicU64 = AtomicU64::new(0);
static MEMO_HITS: AtomicU64 = AtomicU64::new(0);
static STAGE_NS: [AtomicU64; 4] = [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)];

const MAXV: usize = 8;
type Exp = [u8; MAXV];

// ------------------------------------------------------------ rationals ---

#[derive(Clone, Copy, Debug, PartialEq)]
struct R {
    n: i128,
    d: i128,
}

fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl R {
    fn new(n: i128, d: i128) -> Option<R> {
        if d == 0 {
            return None;
        }
        let (mut n, mut d) = if d < 0 { (n.checked_neg()?, d.checked_neg()?) } else { (n, d) };
        if n == 0 {
            return Some(R { n: 0, d: 1 });
        }
        let g = gcd(n, d);
        if g > 1 {
            n /= g;
            d /= g;
        }
        Some(R { n, d })
    }
    fn zero() -> R {
        R { n: 0, d: 1 }
    }
    fn is_zero(self) -> bool {
        self.n == 0
    }
    fn add(self, o: R) -> Option<R> {
        if self.n == 0 {
            return Some(o);
        }
        if o.n == 0 {
            return Some(self);
        }
        let g = gcd(self.d, o.d);
        let l = (self.d / g).checked_mul(o.d)?;
        let a = self.n.checked_mul(l / self.d)?;
        let b = o.n.checked_mul(l / o.d)?;
        R::new(a.checked_add(b)?, l)
    }
    fn sub(self, o: R) -> Option<R> {
        self.add(o.neg())
    }
    fn mul(self, o: R) -> Option<R> {
        if self.n == 0 || o.n == 0 {
            return Some(R::zero());
        }
        let g1 = gcd(self.n, o.d).max(1);
        let g2 = gcd(o.n, self.d).max(1);
        let n = (self.n / g1).checked_mul(o.n / g2)?;
        let d = (self.d / g2).checked_mul(o.d / g1)?;
        R::new(n, d)
    }
    fn neg(self) -> R {
        R { n: -self.n, d: self.d }
    }
    fn f(self) -> f64 {
        self.n as f64 / self.d as f64
    }
}

// ---------------------------------------------------- exact polynomials ---

type EP = Vec<(Exp, R)>; // sorted by exponent, no zero coefficients

fn ep_from_map(m: BTreeMap<Exp, R>) -> EP {
    m.into_iter().filter(|(_, c)| !c.is_zero()).collect()
}

fn ep_add(a: &EP, b: &EP) -> Option<EP> {
    let mut m: BTreeMap<Exp, R> = a.iter().cloned().collect();
    for (e, c) in b {
        let v = m.get(e).copied().unwrap_or(R::zero()).add(*c)?;
        m.insert(*e, v);
    }
    Some(ep_from_map(m))
}

fn ep_scale(a: &EP, c: R) -> Option<EP> {
    if c.is_zero() {
        return Some(Vec::new());
    }
    a.iter().map(|(e, v)| Some((*e, v.mul(c)?))).collect()
}

fn ep_mul(a: &EP, b: &EP) -> Option<EP> {
    let mut m: BTreeMap<Exp, R> = BTreeMap::new();
    for (e1, c1) in a {
        for (e2, c2) in b {
            let mut e = [0u8; MAXV];
            for i in 0..MAXV {
                e[i] = e1[i] + e2[i];
            }
            let p = c1.mul(*c2)?;
            let v = m.get(&e).copied().unwrap_or(R::zero()).add(p)?;
            m.insert(e, v);
        }
    }
    Some(ep_from_map(m))
}

fn ep_sum(ps: &[EP]) -> Option<EP> {
    let mut out: EP = Vec::new();
    for p in ps {
        out = ep_add(&out, p)?;
    }
    Some(out)
}

// ---------------------------------------------------- float polynomials ---

type FP = Vec<(Exp, f64)>;

fn to_fp(p: &EP) -> FP {
    p.iter().map(|(e, c)| (*e, c.f())).collect()
}

/// Merge terms with equal exponents; a merged coefficient that cancels to
/// within rounding of its contributions counts as exactly zero (the exact
/// Python version drops exact zeros).
fn merge(terms: Vec<(Exp, f64)>) -> FP {
    let mut m: BTreeMap<Exp, (f64, f64)> = BTreeMap::new();
    for (e, c) in terms {
        let ent = m.entry(e).or_insert((0.0, 0.0));
        ent.0 += c;
        ent.1 += c.abs();
    }
    m.into_iter()
        .filter(|(_, (s, a))| *s != 0.0 && s.abs() > 1e-12 * a)
        .map(|(e, (s, _))| (e, s))
        .collect()
}

// --------------------------------------------------------------- boxes ---

#[derive(Clone)]
struct BoxF {
    n: usize,
    c: Vec<f64>,
    r: Vec<f64>,
    lo_nonneg: Vec<bool>,
    lo_pos: Vec<bool>,
    lo_zero: Vec<bool>,
    hi_pos: Vec<bool>,
    hi_nonpos: Vec<bool>,
    hi_zero: Vec<bool>,
    rzero: Vec<bool>,
}

fn binom(n: u32, k: u32) -> f64 {
    let mut r = 1.0f64;
    for i in 0..k {
        r = r * (n - i) as f64 / (i + 1) as f64;
    }
    r
}

const MAXDEG: usize = 24;

fn binom_table() -> &'static [[f64; MAXDEG]; MAXDEG] {
    use std::sync::OnceLock;
    static T: OnceLock<[[f64; MAXDEG]; MAXDEG]> = OnceLock::new();
    T.get_or_init(|| {
        let mut t = [[0.0f64; MAXDEG]; MAXDEG];
        for n in 0..MAXDEG {
            t[n][0] = 1.0;
            for k in 1..=n {
                t[n][k] = t[n - 1][k - 1] + if k < n { t[n - 1][k] } else { 0.0 };
            }
        }
        t
    })
}

/// Float Taylor shift `x_i = a_i + b_i u_i` and the constant / rest sums
/// (mirror of `stellated_fastbound._shift_bound`), merging equal monomials
/// after each variable.
fn shift_bound(p: &FP, n: usize, a: &[f64; MAXV], b: &[f64; MAXV], centered: bool,
               buf: &mut Vec<(Exp, f64)>, next: &mut Vec<(Exp, f64)>) -> (f64, f64) {
    let bt = binom_table();
    buf.clear();
    buf.extend_from_slice(p);
    for i in 0..n {
        if a[i] == 0.0 && b[i] == 1.0 {
            continue;
        }
        let kmax = buf.iter().map(|(e, _)| e[i] as usize).max().unwrap_or(0);
        if kmax == 0 {
            continue;
        }
        if kmax >= MAXDEG {
            return (f64::NEG_INFINITY, f64::INFINITY);
        }
        let mut apow = [1.0f64; MAXDEG];
        let mut bpow = [1.0f64; MAXDEG];
        for k in 1..=kmax {
            apow[k] = apow[k - 1] * a[i];
            bpow[k] = bpow[k - 1] * b[i];
        }
        next.clear();
        if b[i] == 0.0 {
            // x_i fixed: only the u^0 term survives
            for (e, c) in buf.iter() {
                let k = e[i] as usize;
                let mut e2 = *e;
                e2[i] = 0;
                next.push((e2, c * apow[k]));
            }
        } else {
            for (e, c) in buf.iter() {
                let k = e[i] as usize;
                for j in 0..=k {
                    let mut e2 = *e;
                    e2[i] = j as u8;
                    next.push((e2, c * bt[k][j] * apow[k - j] * bpow[j]));
                }
            }
        }
        next.sort_unstable_by(|x, y| x.0.cmp(&y.0));
        buf.clear();
        for &(e, c) in next.iter() {
            match buf.last_mut() {
                Some(last) if last.0 == e => last.1 += c,
                _ => buf.push((e, c)),
            }
        }
    }
    let (mut cst, mut rest_abs, mut rest_neg, mut scale) = (0.0, 0.0, 0.0, 0.0);
    // buf is merged unless no variable was shifted; merge defensively
    buf.sort_unstable_by(|x, y| x.0.cmp(&y.0));
    let mut t = 0;
    while t < buf.len() {
        let key = buf[t].0;
        let mut s = 0.0;
        while t < buf.len() && buf[t].0 == key {
            s += buf[t].1;
            t += 1;
        }
        scale += s.abs();
        if key.iter().all(|&k| k == 0) {
            cst += s;
        } else {
            rest_abs += s.abs();
            if s < 0.0 {
                rest_neg += s;
            }
        }
    }
    (if centered { cst - rest_abs } else { cst + rest_neg }, scale)
}

/// Dense version of the three Taylor-shift bounds: coefficients live in an
/// array indexed by the exponent vector, and each variable's shift is an
/// in-place 1-D Taylor shift along its axis (no sorting, few allocations).
fn dense_bounds(p: &FP, n: usize, bx: &BoxF) -> Option<(f64, f64)> {
    let mut degs = [0usize; MAXV];
    for (e, _) in p {
        for v in 0..n {
            degs[v] = degs[v].max(e[v] as usize);
        }
    }
    let mut stride = [0usize; MAXV];
    let mut size = 1usize;
    for v in 0..n {
        stride[v] = size;
        size = size.checked_mul(degs[v] + 1)?;
        if size > 1 << 20 {
            return None;
        }
    }
    let mut base = vec![0.0f64; size];
    for (e, c) in p {
        let idx: usize = (0..n).map(|v| e[v] as usize * stride[v]).sum();
        base[idx] += c;
    }
    let mut best = f64::NEG_INFINITY;
    let mut scale = 0.0f64;
    let mut fiber = [0.0f64; 32];
    let mut out = [0.0f64; 32];
    for mode in 0..3 {
        let mut arr = base.clone();
        for v in 0..n {
            let (a, b) = match mode {
                0 => (bx.c[v], bx.r[v]),
                1 => (bx.c[v] - bx.r[v], 2.0 * bx.r[v]),
                _ => (bx.c[v] + bx.r[v], -2.0 * bx.r[v]),
            };
            let len = degs[v] + 1;
            if len == 1 || (a == 0.0 && b == 1.0) || len > 32 {
                if len > 32 {
                    return None;
                }
                continue;
            }
            let mut apow = [1.0f64; 32];
            let mut bpow = [1.0f64; 32];
            for k in 1..len {
                apow[k] = apow[k - 1] * a;
                bpow[k] = bpow[k - 1] * b;
            }
            let s = stride[v];
            let block = s * len;
            let mut start = 0;
            while start < size {
                for off in 0..s {
                    let i0 = start + off;
                    for k in 0..len {
                        fiber[k] = arr[i0 + k * s];
                    }
                    for j in 0..len {
                        let mut acc = 0.0;
                        for k in j..len {
                            acc += binom(k as u32, j as u32) * apow[k - j] * fiber[k];
                        }
                        out[j] = acc * bpow[j];
                    }
                    for j in 0..len {
                        arr[i0 + j * s] = out[j];
                    }
                }
                start += block;
            }
        }
        let cst = arr[0];
        let (mut rest_abs, mut rest_neg, mut sc) = (0.0, 0.0, cst.abs());
        for &x in &arr[1..] {
            rest_abs += x.abs();
            sc += x.abs();
            if x < 0.0 {
                rest_neg += x;
            }
        }
        let bound = if mode == 0 { cst - rest_abs } else { cst + rest_neg };
        best = best.max(bound);
        scale = scale.max(sc);
    }
    Some((best, scale))
}

const USE_DENSE: bool = false;

/// FLOAT_ONLY `box_lower`: -1 (reject), 0 (inconclusive), 1 (positive).
fn fbox(p: &FP, bx: &BoxF) -> i8 {
    if p.is_empty() {
        return 0;
    }
    let t0 = std::time::Instant::now();
    let r = fbox_inner(p, bx);
    FBOX_CALLS.fetch_add(1, Relaxed);
    FBOX_TERMS_IN.fetch_add(p.len() as u64, Relaxed);
    FBOX_NS.fetch_add(t0.elapsed().as_nanos() as u64, Relaxed);
    r
}

fn fbox_inner(p: &FP, bx: &BoxF) -> i8 {
    if USE_DENSE {
        if let Some((fb, scale)) = dense_bounds(p, bx.n, bx) {
            let tol = 1e-9 * scale + 1e-300;
            return if fb < -tol { -1 } else if fb > tol { 1 } else { 0 };
        }
    }
    let n = bx.n;
    let mut c = [0.0f64; MAXV];
    let mut r = [0.0f64; MAXV];
    let mut lo = [0.0f64; MAXV];
    let mut hi = [0.0f64; MAXV];
    let mut tr = [0.0f64; MAXV];
    let mut mtr = [0.0f64; MAXV];
    for i in 0..n {
        c[i] = bx.c[i];
        r[i] = bx.r[i];
        lo[i] = c[i] - r[i];
        hi[i] = c[i] + r[i];
        tr[i] = 2.0 * r[i];
        mtr[i] = -2.0 * r[i];
    }
    thread_local! {
        static BUFS: std::cell::RefCell<(Vec<(Exp, f64)>, Vec<(Exp, f64)>)> =
            std::cell::RefCell::new((Vec::new(), Vec::new()));
    }
    let (b1, s1, b2, s2, b3, s3) = BUFS.with(|cell| {
        let mut bufs = cell.borrow_mut();
        let (buf, next) = &mut *bufs;
        let (b1, s1) = shift_bound(p, n, &c, &r, true, buf, next);
        let (b2, s2) = shift_bound(p, n, &lo, &tr, false, buf, next);
        let (b3, s3) = shift_bound(p, n, &hi, &mtr, false, buf, next);
        (b1, s1, b2, s2, b3, s3)
    });
    let fb = b1.max(b2).max(b3);
    let scale = s1.max(s2).max(s3);
    let tol = 1e-9 * scale + 1e-300;
    if fb < -tol {
        -1
    } else if fb > tol {
        1
    } else {
        0
    }
}

fn strip(p: &FP, n: usize, allowed: &dyn Fn(usize) -> bool) -> FP {
    if p.is_empty() {
        return Vec::new();
    }
    let mut common = [0u8; MAXV];
    let mut any = false;
    for v in 0..MAXV {
        if v < n && allowed(v) {
            common[v] = p.iter().map(|(e, _)| e[v]).min().unwrap();
            any |= common[v] > 0;
        }
    }
    if !any {
        return p.clone();
    }
    p.iter()
        .map(|(e, c)| {
            let mut e2 = *e;
            for v in 0..MAXV {
                e2[v] -= common[v];
            }
            (e2, *c)
        })
        .collect()
}

fn pin(p: &FP, bx: &BoxF) -> FP {
    let terms = p
        .iter()
        .map(|(e, c)| {
            let mut coef = *c;
            let mut e2 = *e;
            for v in 0..MAXV {
                if e[v] > 0 && v < bx.n && bx.rzero[v] {
                    coef *= bx.c[v].powi(e[v] as i32);
                    e2[v] = 0;
                }
            }
            (e2, coef)
        })
        .collect();
    merge(terms)
}

fn nonneg0(p: &FP, bx: &BoxF) -> bool {
    let q = strip(p, bx.n, &|v| bx.lo_nonneg[v] && bx.hi_pos[v]);
    fbox(&q, bx) >= 0
}

fn nonneg_ok(p: &FP, bx: &BoxF) -> bool {
    nonneg0(p, bx) || (bx.rzero.iter().any(|&z| z) && nonneg0(&pin(p, bx), bx))
}

fn pos0(p: &FP, bx: &BoxF, tube: bool) -> bool {
    let q = strip(p, bx.n, &|v| {
        (v == 0 || (tube && v == 6) || (v == 1 && bx.hi_pos[1])) && bx.lo_nonneg[v]
    });
    fbox(&q, bx) > 0
}

fn pos_ok(p: &FP, bx: &BoxF, tube: bool) -> bool {
    pos0(p, bx, tube) || (bx.rzero.iter().any(|&z| z) && pos0(&pin(p, bx), bx, tube))
}

fn neg(p: &FP) -> FP {
    p.iter().map(|(e, c)| (*e, -c)).collect()
}

type Memo = HashMap<u64, bool>;

fn poly_key(p: &FP) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for (e, c) in p {
        e.hash(&mut h);
        c.to_bits().hash(&mut h);
    }
    h.finish()
}

/// `nonneg_ok` memoized per box (the screen re-checks identical polynomials
/// across split lists and their orderings).
fn nonneg_memo(p: &FP, bx: &BoxF, memo: &mut Memo) -> bool {
    let k = poly_key(p);
    if let Some(&v) = memo.get(&k) {
        MEMO_HITS.fetch_add(1, Relaxed);
        return v;
    }
    let v = nonneg_ok(p, bx);
    memo.insert(k, v);
    v
}

/// `split_parts` + the sign and part/rest checks of `split_ok`.
fn split_ok(f: &FP, bx: &BoxF, split: &[(usize, bool)], memo: &mut Memo) -> bool {
    for &(v, sign) in split {
        if (sign && !bx.lo_nonneg[v]) || (!sign && bx.hi_pos[v]) {
            return false;
        }
    }
    let mut rest: FP = f.clone();
    for &(v, sign) in split {
        let mut part: FP = Vec::new();
        let mut keep: FP = Vec::new();
        for (e, c) in &rest {
            if e[v] >= 1 {
                let mut e2 = *e;
                e2[v] -= 1;
                part.push((e2, *c));
            } else {
                keep.push((*e, *c));
            }
        }
        rest = keep;
        let part = if sign { part } else { neg(&part) };
        if !nonneg_memo(&part, bx, memo) {
            return false;
        }
    }
    nonneg_memo(&rest, bx, memo)
}

/// `candidate_splits` (family: 0 cone, 1 plain-like, 2 rho, 3 wedge, 4 skew, 5 other).
fn candidate_splits(family: u8, bx: &BoxF) -> Vec<Vec<(usize, bool)>> {
    let signed = |vs: &[usize]| -> Vec<(usize, bool)> {
        let mut out = Vec::new();
        for &v in vs {
            if bx.lo_nonneg[v] {
                out.push((v, true));
            } else if bx.hi_nonpos[v] {
                out.push((v, false));
            }
        }
        out
    };
    let eps = vec![(0usize, true)];
    let cat = |a: Vec<(usize, bool)>, b: Vec<(usize, bool)>| -> Vec<(usize, bool)> {
        let mut x = a;
        x.extend(b);
        x
    };
    match family {
        0 => {
            let mut out = vec![vec![], eps.clone()];
            // itertools.permutations order (lexicographic on positions)
            let perms = permutations();
            for p in perms {
                out.push(cat(signed(&p), eps.clone()));
                out.push(cat(eps.clone(), signed(&p)));
            }
            out
        }
        1 => vec![vec![], cat(signed(&[3]), eps.clone()), eps.clone()],
        2 => vec![
            vec![],
            eps.clone(),
            cat(signed(&[3]), eps.clone()),
            cat(signed(&[3, 6]), eps.clone()),
            cat(signed(&[6, 3]), eps.clone()),
            cat(cat(signed(&[3]), eps.clone()), signed(&[6])),
            cat(eps.clone(), signed(&[3, 6])),
        ],
        3 => vec![vec![], cat(signed(&[3, 5]), eps.clone()), eps.clone()],
        4 => vec![
            vec![],
            cat(signed(&[5, 3]), eps.clone()),
            cat(signed(&[3, 5]), eps.clone()),
            eps.clone(),
        ],
        _ => vec![vec![], cat(signed(&[3, 6]), eps.clone()), cat(signed(&[6]), eps.clone()), eps],
    }
}

/// All permutations of `[2,3,4,5]` in `itertools.permutations` order.
fn permutations() -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let base = [2usize, 3, 4, 5];
    for i in 0..4 {
        for j in 0..4 {
            if j == i {
                continue;
            }
            for k in 0..4 {
                if k == i || k == j {
                    continue;
                }
                let l = 6 - i - j - k;
                out.push(vec![base[i], base[j], base[k], base[l]]);
            }
        }
    }
    out
}

/// `shift_poly` in one variable: `y ↦ F(.., m + y_v, ..)`.
fn shift_var(f: &FP, v: usize, m: f64) -> FP {
    let mut terms = Vec::new();
    for (e, c) in f {
        let k = e[v] as u32;
        if k == 0 {
            terms.push((*e, *c));
            continue;
        }
        for i in 0..=k {
            let mut e2 = *e;
            e2[v] = i as u8;
            terms.push((e2, c * binom(k, i) * m.powi((k - i) as i32)));
        }
    }
    merge(terms)
}

fn make_box(c: &[f64], r: &[f64], flags: &[u8]) -> BoxF {
    let bit = |k: u8| -> Vec<bool> { flags.iter().map(|f| f & k != 0).collect() };
    BoxF {
        n: c.len(),
        c: c.to_vec(),
        r: r.to_vec(),
        lo_nonneg: bit(1),
        lo_pos: bit(2),
        lo_zero: bit(4),
        hi_pos: bit(8),
        hi_nonpos: bit(16),
        hi_zero: bit(32),
        rzero: bit(64),
    }
}

// ---------------------------------------------------------------- chart ---

struct Cert {
    mus: [FP; 3],
    supports: Vec<FP>,
    d: EP,
}

#[pyclass]
struct Chart {
    w: [EP; 3],
    nm: [[EP; 3]; 3],
    dd: EP,
    vq: Vec<[R; 3]>,
    cache: HashMap<[i16; 15], std::sync::Arc<Cert>>,
    flips: Vec<FP>,
}


type PyPoly = Vec<(Vec<u8>, i128, i128)>;

fn ep_from_py(p: &PyPoly) -> PyResult<EP> {
    let mut m = BTreeMap::new();
    for (e, n, d) in p {
        let mut ex = [0u8; MAXV];
        for (i, k) in e.iter().enumerate() {
            ex[i] = *k;
        }
        let c = R::new(*n, *d).ok_or_else(|| PyOverflowError::new_err("bad rational"))?;
        m.insert(ex, c);
    }
    Ok(ep_from_map(m))
}

fn ovf<T>(x: Option<T>) -> PyResult<T> {
    x.ok_or_else(|| PyOverflowError::new_err("i128 overflow"))
}

impl Chart {
    fn w_dot_const(&self, v: [R; 3]) -> Option<EP> {
        ep_sum(&[ep_scale(&self.w[0], v[0])?, ep_scale(&self.w[1], v[1])?, ep_scale(&self.w[2], v[2])?])
    }

    fn certificate(&self, triple: &[(usize, usize, usize, usize, i32)]) -> Option<Cert> {
        let sub = |a: [R; 3], b: [R; 3]| -> Option<[R; 3]> {
            Some([a[0].sub(b[0])?, a[1].sub(b[1])?, a[2].sub(b[2])?])
        };
        let cross = |a: [R; 3], b: [R; 3]| -> Option<[R; 3]> {
            Some([
                a[1].mul(b[2])?.sub(a[2].mul(b[1])?)?,
                a[2].mul(b[0])?.sub(a[0].mul(b[2])?)?,
                a[0].mul(b[1])?.sub(a[1].mul(b[0])?)?,
            ])
        };
        let sr = |s: i32| R { n: s as i128, d: 1 };
        let mut edges = Vec::new();
        for &(_, a, b, _, _) in triple {
            edges.push(sub(self.vq[b], self.vq[a])?);
        }
        let sig: Vec<i32> = triple.iter().map(|t| t.4).collect();
        let mut mus: Vec<EP> = Vec::new();
        for i in 0..3 {
            let (j, k) = ((i + 1) % 3, (i + 2) % 3);
            mus.push(ep_scale(&self.w_dot_const(cross(edges[j], edges[k])?)?, sr(sig[j] * sig[k]))?);
        }
        let mut supports = Vec::new();
        for (i, &(_, _, _, qv, s)) in triple.iter().enumerate() {
            for j in 0..self.vq.len() {
                if j == qv {
                    continue;
                }
                let g = ep_scale(&self.w_dot_const(cross(edges[i], sub(self.vq[j], self.vq[qv])?)?)?, sr(s))?;
                supports.push(to_fp(&ep_scale(&g, sr(-1))?)); // nonneg_ok(-g)
            }
        }
        let mut dpoly: EP = Vec::new();
        for (i, &(p, _, _, qv, s)) in triple.iter().enumerate() {
            let mut vec: Vec<EP> = Vec::new();
            for r in 0..3 {
                let inner = ep_sum(&[
                    ep_scale(&self.nm[r][0], self.vq[p][0])?,
                    ep_scale(&self.nm[r][1], self.vq[p][1])?,
                    ep_scale(&self.nm[r][2], self.vq[p][2])?,
                ])?;
                vec.push(ep_add(&inner, &ep_scale(&self.dd, self.vq[qv][r].neg())?)?);
            }
            let e = edges[i];
            let crossed = [
                ep_add(&ep_scale(&vec[2], e[1])?, &ep_scale(&vec[1], e[2].neg())?)?,
                ep_add(&ep_scale(&vec[0], e[2])?, &ep_scale(&vec[2], e[0].neg())?)?,
                ep_add(&ep_scale(&vec[1], e[0])?, &ep_scale(&vec[0], e[1].neg())?)?,
            ];
            let wd = ep_sum(&[
                ep_mul(&self.w[0], &crossed[0])?,
                ep_mul(&self.w[1], &crossed[1])?,
                ep_mul(&self.w[2], &crossed[2])?,
            ])?;
            dpoly = ep_add(&dpoly, &ep_scale(&ep_mul(&mus[i], &wd)?, sr(s))?)?;
        }
        Some(Cert {
            mus: [to_fp(&mus[0]), to_fp(&mus[1]), to_fp(&mus[2])],
            supports,
            d: dpoly,
        })
    }
}

#[pymethods]
impl Chart {
    #[new]
    #[pyo3(signature = (w, nm, d, vq, flips=Vec::new()))]
    fn new(w: Vec<PyPoly>, nm: Vec<Vec<PyPoly>>, d: PyPoly, vq: Vec<Vec<(i128, i128)>>,
           flips: Vec<Vec<(Vec<u8>, f64)>>) -> PyResult<Self> {
        let w = [ep_from_py(&w[0])?, ep_from_py(&w[1])?, ep_from_py(&w[2])?];
        let mut rows: Vec<[EP; 3]> = Vec::new();
        for r in 0..3 {
            rows.push([ep_from_py(&nm[r][0])?, ep_from_py(&nm[r][1])?, ep_from_py(&nm[r][2])?]);
        }
        let nm = [rows[0].clone(), rows[1].clone(), rows[2].clone()];
        let mut vqr = Vec::new();
        for v in &vq {
            vqr.push([ovf(R::new(v[0].0, v[0].1))?, ovf(R::new(v[1].0, v[1].1))?, ovf(R::new(v[2].0, v[2].1))?]);
        }
        let flips = flips
            .iter()
            .map(|p| {
                p.iter()
                    .map(|(e, c)| {
                        let mut ex = [0u8; MAXV];
                        for (i, k) in e.iter().enumerate() {
                            ex[i] = *k;
                        }
                        (ex, *c)
                    })
                    .filter(|(_, c)| *c != 0.0)
                    .collect()
            })
            .collect();
        Ok(Chart { w, nm, dd: ep_from_py(&d)?, vq: vqr, cache: HashMap::new(), flips })
    }

    /// The float screen.  Returns 0 (rejected before the displacement
    /// stage), 1 (rejected at the displacement stage: a PENDING candidate),
    /// 2 (passed: run the exact check).  Raises OverflowError when the exact
    /// certificate does not fit in i128.
    #[allow(clippy::too_many_arguments)]
    fn screen(
        &mut self,
        family: u8,
        tube: bool,
        triple: Vec<(usize, usize, usize, usize, i32)>,
        c: Vec<f64>,
        r: Vec<f64>,
        flags: Vec<u8>,
        allow_shift: bool,
    ) -> PyResult<u8> {
        let n = c.len();
        let bx = make_box(&c, &r, &flags);
        let mut key = [0i16; 15];
        for (i, t) in triple.iter().enumerate() {
            key[5 * i] = t.0 as i16;
            key[5 * i + 1] = t.1 as i16;
            key[5 * i + 2] = t.2 as i16;
            key[5 * i + 3] = t.3 as i16;
            key[5 * i + 4] = t.4 as i16;
        }
        let cert = match self.cache.get(&key) {
            Some(c) => c.clone(),
            None => {
                let c = std::sync::Arc::new(ovf(self.certificate(&triple))?);
                self.cache.insert(key, c.clone());
                c
            }
        };
        let t_stage = std::time::Instant::now();
        // weights and their positivity
        if !cert.mus.iter().all(|m| nonneg_ok(m, &bx)) {
            STAGE_NS[0].fetch_add(t_stage.elapsed().as_nanos() as u64, Relaxed);
            return Ok(0);
        }
        let pos: Vec<bool> = cert.mus.iter().map(|m| pos_ok(m, &bx, tube)).collect();
        if !(0..3).all(|i| (0..3).any(|j| j != i && pos[j])) {
            return Ok(0);
        }
        if !cert.supports.iter().all(|g| nonneg_ok(g, &bx)) {
            STAGE_NS[0].fetch_add(t_stage.elapsed().as_nanos() as u64, Relaxed);
            return Ok(0);
        }
        STAGE_NS[0].fetch_add(t_stage.elapsed().as_nanos() as u64, Relaxed);
        let t_split = std::time::Instant::now();
        // disp_F: divide by eps (and rho in a tube when it divides D)
        let mut base = [0u8; MAXV];
        base[0] = 1;
        let lo6_le0 = n > 6 && !bx.lo_pos[6];
        if tube && lo6_le0 && cert.d.iter().all(|(e, _)| e[0] >= 1 && e[6] >= 1) {
            base[6] = 1;
        }
        if cert.d.iter().any(|(e, _)| (0..MAXV).any(|v| e[v] < base[v])) {
            return Ok(0);
        }
        let f: FP = cert
            .d
            .iter()
            .map(|(e, c)| {
                let mut e2 = *e;
                for v in 0..MAXV {
                    e2[v] -= base[v];
                }
                (e2, c.f())
            })
            .collect();
        let mut memo = Memo::new();
        for split in candidate_splits(family, &bx) {
            if split_ok(&f, &bx, &split, &mut memo) {
                return Ok(2);
            }
        }
        STAGE_NS[1].fetch_add(t_split.elapsed().as_nanos() as u64, Relaxed);
        if !allow_shift {
            return Ok(1);
        }
        let t_shift = std::time::Instant::now();
        for &v in &[5usize, 4, 2, 3] {
            if v >= n || bx.rzero[v] {
                continue;
            }
            for upper in [true, false] {
                // m = c + r (box becomes [-2r, 0]) or c - r (box [0, 2r])
                if (upper && bx.hi_zero[v]) || (!upper && bx.lo_zero[v]) {
                    continue;
                }
                let m = if upper { bx.c[v] + bx.r[v] } else { bx.c[v] - bx.r[v] };
                let g = shift_var(&f, v, m);
                let mut sb = bx.clone();
                sb.c[v] = if upper { -bx.r[v] } else { bx.r[v] };
                sb.lo_nonneg[v] = !upper;
                sb.lo_pos[v] = false;
                sb.lo_zero[v] = !upper;
                sb.hi_pos[v] = !upper;
                sb.hi_nonpos[v] = upper;
                sb.hi_zero[v] = upper;
                let sign = vec![(v, !upper)];
                let mut memo = Memo::new();
                let mut tried: Vec<Vec<(usize, bool)>> = Vec::new();
                for split in candidate_splits(family, &sb) {
                    let mut a = sign.clone();
                    a.extend(split.iter().cloned());
                    let mut b = split.clone();
                    b.extend(sign.iter().cloned());
                    for cand in [a, b] {
                        if tried.contains(&cand) {
                            continue;
                        }
                        if split_ok(&g, &sb, &cand, &mut memo) {
                            return Ok(2);
                        }
                        tried.push(cand);
                    }
                }
            }
        }
        STAGE_NS[2].fetch_add(t_shift.elapsed().as_nanos() as u64, Relaxed);
        Ok(1)
    }

    /// For each flip polynomial: false when the exact `pos_ok` is certain to
    /// fail because every variant is rejected by the float prefilter that the
    /// Python exact path applies first (so the result is unchanged).
    fn flip_prefilter(&self, tube: bool, c: Vec<f64>, r: Vec<f64>, flags: Vec<u8>) -> Vec<bool> {
        let bx = make_box(&c, &r, &flags);
        let pinned = bx.rzero.iter().any(|&z| z);
        self.flips
            .iter()
            .map(|p| {
                let strip_pos = |q: &FP| {
                    strip(q, bx.n, &|v| {
                        (v == 0 || (tube && v == 6) || (v == 1 && bx.hi_pos[1])) && bx.lo_nonneg[v]
                    })
                };
                fbox(&strip_pos(p), &bx) >= 0 || (pinned && fbox(&strip_pos(&pin(p, &bx)), &bx) >= 0)
            })
            .collect()
    }

    #[staticmethod]
    fn stats() -> Vec<u64> {
        let mut v = vec![FBOX_CALLS.load(Relaxed), FBOX_NS.load(Relaxed), FBOX_TERMS_IN.load(Relaxed),
                         FBOX_TERMS_PEAK.load(Relaxed), MEMO_HITS.load(Relaxed)];
        for s in &STAGE_NS { v.push(s.load(Relaxed)); }
        v
    }

    fn cache_size(&self) -> usize {
        self.cache.len()
    }
}

#[pymodule]
fn corner_kernel(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Chart>()?;
    Ok(())
}
