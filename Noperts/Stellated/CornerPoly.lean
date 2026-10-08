module

public import Noperts.Stellated.SparsePoly
public import Noperts.Stellated.AtlasProjectiveGlobalRigidity

@[expose] public section

/-!
# Blow-up chart polynomials at the corner view

The corner is the projective view `b = (1/2, 1/2, 0)` (the edge-on view
`(1,1,0)/√2`) with relative rotation `I`.  Chart variables:

* `0` `ε` (scale), `1` `λ`, `2` `u` (view direction along a quadrant
  edge), `3,4,5` `a, b, c` (relative Cayley direction), `6` `ρ` (tube
  radius, tube charts only).

The normalized projective view and the Cayley vector are

    w = b + ε (s F₁ + t F₂),       X = ε·(ρ)·(a M₁ + b M₂ + c M₃),

with `(s, t) = (λ, -λu)` on segment A and `(λu, -λ)` on segment B.  All are
exact rational polynomials in the chart variables (`SparsePoly`).
-/

namespace Noperts.Stellated.CornerPoly

open SparsePoly

def B0 : Fin 3 → ℚ := ![1 / 2, 1 / 2, 0]
def F1 : Fin 3 → ℚ := ![1 / 2, -1 / 2, 0]
def F2 : Fin 3 → ℚ := ![1 / 4, 1 / 4, -1 / 2]
def M1 : Fin 3 → ℚ := ![1, 1, 0]
def M2 : Fin 3 → ℚ := ![1, -1, 0]
def M3 : Fin 3 → ℚ := ![0, 0, 1]

/-- The view-offset coefficient `s` (segment B iff `seg = true`). -/
def sPoly (seg : Bool) : Poly := if seg then mul (var 1) (var 2) else var 1

/-- The view-offset coefficient `t`. -/
def tPoly (seg : Bool) : Poly :=
  if seg then scale (-1) (var 1) else scale (-1) (mul (var 1) (var 2))

noncomputable def sVal (seg : Bool) (y : ℕ → ℝ) : ℝ :=
  if seg then y 1 * y 2 else y 1

noncomputable def tVal (seg : Bool) (y : ℕ → ℝ) : ℝ :=
  if seg then -y 1 else -(y 1 * y 2)

theorem eval_sPoly (seg : Bool) (y : ℕ → ℝ) :
    eval y (sPoly seg) = sVal seg y := by
  cases seg <;> simp [sPoly, sVal, eval_mul]

theorem eval_tPoly (seg : Bool) (y : ℕ → ℝ) :
    eval y (tPoly seg) = tVal seg y := by
  cases seg <;> simp [tPoly, tVal, eval_scale, eval_mul]

def wPoly (seg : Bool) (c : Fin 3) : Poly :=
  add (const (B0 c))
    (mul (var 0) (add (scale (F1 c) (sPoly seg)) (scale (F2 c) (tPoly seg))))

noncomputable def wVal (seg : Bool) (y : ℕ → ℝ) (c : Fin 3) : ℝ :=
  (B0 c : ℝ) + y 0 * ((F1 c : ℝ) * sVal seg y + (F2 c : ℝ) * tVal seg y)

theorem eval_wPoly (seg : Bool) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (wPoly seg c) = wVal seg y c := by
  simp [wPoly, wVal, eval_add, eval_mul, eval_scale, eval_sPoly, eval_tPoly]

def scalePoly (tube : Bool) : Poly := if tube then mul (var 0) (var 6) else var 0

noncomputable def scaleVal (tube : Bool) (y : ℕ → ℝ) : ℝ :=
  if tube then y 0 * y 6 else y 0

theorem eval_scalePoly (tube : Bool) (y : ℕ → ℝ) :
    eval y (scalePoly tube) = scaleVal tube y := by
  cases tube <;> simp [scalePoly, scaleVal, eval_mul]

def xPoly (tube : Bool) (c : Fin 3) : Poly :=
  mul (scalePoly tube)
    (add (add (scale (M1 c) (var 3)) (scale (M2 c) (var 4))) (scale (M3 c) (var 5)))

noncomputable def xVal (tube : Bool) (y : ℕ → ℝ) (c : Fin 3) : ℝ :=
  scaleVal tube y * ((M1 c : ℝ) * y 3 + (M2 c : ℝ) * y 4 + (M3 c : ℝ) * y 5)

theorem eval_xPoly (tube : Bool) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (xPoly tube c) = xVal tube y c := by
  simp [xPoly, xVal, eval_add, eval_mul, eval_scale, eval_scalePoly]

/-! ## Chart kinds

* `plain`: `X = ε (a M₁ + b M₂ + c M₃)` (variables 3, 4, 5);
* `tube`: `X = ε ρ (a M₁ + b M₂ + c M₃)` (ρ is variable 6);
* `wedge`: `X = ε (α M₁ + (τ D₁ + η D₂)·(M₂, M₃))` (variables α 3, τ 4, η 5), with
  `D₁ = (-t/2, -s)` and `D₂ = (s, -t/2)` in the `(M₂, M₃)` coordinates;
* `wtube`: as `wedge` with `α = σ ᾱ`, `η = σ η̄` (variables ᾱ 3, τ 4,
  η̄ 5, σ 6).
-/

inductive ChartKind where
  | plain | tube | wedge | wtube | skew
  /-- The tube with `a = ε α` (variable 3 is `α`). -/
  | atube
  /-- The tube with `a = ±atubeA ε + w` (variable 3 is `w`; `-` when `neg`). -/
  | btube (neg : Bool)
  /-- The skew chart with `a = ε α`. -/
  | askew
  /-- The skew chart with `a = ±atubeA ε + w`. -/
  | bskew (neg : Bool)
  /-- The plain chart with `a = ε α`. -/
  | aplain
  /-- The plain chart with `a = ±atubeA ε + w`. -/
  | bplain (neg : Bool)
deriving DecidableEq, Repr

/-- Charts with a tube radius `ρ` (variable 6). -/
@[simp] def ChartKind.hasRho : ChartKind → Bool
  | .tube | .atube | .btube _ => true
  | _ => false

def atubeA : ℚ := 8

/-- `ε (a M₁ + b M₂ + c M₃)` for a polynomial `a`. -/
def plainX (a : Poly) (c : Fin 3) : Poly :=
  mul (var 0) (add (add (scale (M1 c) a) (scale (M2 c) (var 4))) (scale (M3 c) (var 5)))

/-- `ε ρ (a M₁ + b M₂ + c M₃)` for a polynomial `a`. -/
def tubeX (a : Poly) (c : Fin 3) : Poly :=
  mul (mul (var 0) (var 6))
    (add (add (scale (M1 c) a) (scale (M2 c) (var 4))) (scale (M3 c) (var 5)))

/-- The second first-order-degenerate line of segment B is `c + skewK b = 0`;
the `skew` chart uses `η' = c + skewK b` as its last coordinate. -/
def skewK : ℚ := 682 / 279

/-- `ε (a M₁ + b M₂ + (η' - skewK b) M₃)` for a polynomial `a`. -/
def skewX (a : Poly) (c : Fin 3) : Poly :=
  mul (var 0) (add (add (scale (M1 c) a) (scale (M2 c) (var 4)))
    (scale (M3 c) (add (var 5) (scale (-skewK) (var 4)))))

/-- The `(M₂, M₃)` coefficients `(b, c)` of the wedge-type charts. -/
def wedgeB (seg : Bool) (tau eta : Poly) : Poly :=
  add (mul tau (scale (-1 / 2) (tPoly seg))) (mul eta (sPoly seg))

def wedgeC (seg : Bool) (tau eta : Poly) : Poly :=
  add (mul tau (scale (-1) (sPoly seg))) (mul eta (scale (-1 / 2) (tPoly seg)))

def xPolyK (seg : Bool) : ChartKind → Fin 3 → Poly
  | .plain => xPoly false
  | .tube => xPoly true
  | .wedge => fun c => mul (var 0)
      (add (add (scale (M1 c) (var 3)) (scale (M2 c) (wedgeB seg (var 4) (var 5))))
        (scale (M3 c) (wedgeC seg (var 4) (var 5))))
  | .skew => fun c => mul (var 0)
      (add (add (scale (M1 c) (var 3)) (scale (M2 c) (var 4)))
        (scale (M3 c) (add (var 5) (scale (-skewK) (var 4)))))
  | .atube => tubeX (mul (var 0) (var 3))
  | .btube neg => tubeX (add (scale ((if neg then -1 else 1) * atubeA) (var 0)) (var 3))
  | .aplain => plainX (mul (var 0) (var 3))
  | .bplain neg => plainX (add (scale ((if neg then -1 else 1) * atubeA) (var 0)) (var 3))
  | .askew => skewX (mul (var 0) (var 3))
  | .bskew neg => skewX (add (scale ((if neg then -1 else 1) * atubeA) (var 0)) (var 3))
  | .wtube => fun c => mul (var 0)
      (add (add (scale (M1 c) (mul (var 6) (var 3)))
          (scale (M2 c) (wedgeB seg (var 4) (mul (var 6) (var 5)))))
        (scale (M3 c) (wedgeC seg (var 4) (mul (var 6) (var 5)))))

/-! ## The Cayley numerator and denominator -/

def numPolyOf (X : Fin 3 → Poly) : Fin 3 → Fin 3 → Poly :=
  let x := X 0
  let y := X 1
  let z := X 2
  let one := const 1
  let sq := fun p => mul p p
  let two := fun p q => scale 2 (mul p q)
  ![![add (add (add one (sq x)) (scale (-1) (sq y))) (scale (-1) (sq z)),
      add (two x y) (scale (-2) z),
      add (two x z) (scale 2 y)],
    ![add (two x y) (scale 2 z),
      add (add (add one (scale (-1) (sq x))) (sq y)) (scale (-1) (sq z)),
      add (two y z) (scale (-2) x)],
    ![add (two x z) (scale (-2) y),
      add (two y z) (scale 2 x),
      add (add (add one (scale (-1) (sq x))) (scale (-1) (sq y))) (sq z)]]

def denPolyOf (X : Fin 3 → Poly) : Poly :=
  add (add (add (const 1) (mul (X 0) (X 0))) (mul (X 1) (X 1))) (mul (X 2) (X 2))

theorem eval_numPolyOf (X : Fin 3 → Poly) (y : ℕ → ℝ) (i j : Fin 3) :
    eval y (numPolyOf X i j) =
      cayleyNumeratorMatrix (eval y (X 0)) (eval y (X 1)) (eval y (X 2)) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [numPolyOf, cayleyNumeratorMatrix, eval_add, eval_mul, eval_scale] <;> ring

theorem eval_denPolyOf (X : Fin 3 → Poly) (y : ℕ → ℝ) :
    eval y (denPolyOf X) =
      cayleyDenom (eval y (X 0)) (eval y (X 1)) (eval y (X 2)) := by
  simp [denPolyOf, cayleyDenom, eval_add, eval_mul]
  ring

/-! ## Linear values against the view -/

/-- `w · v` for a vector of polynomials `v`. -/
def lvPoly (seg : Bool) (v : Fin 3 → Poly) : Poly :=
  add (add (mul (wPoly seg 0) (v 0)) (mul (wPoly seg 1) (v 1)))
    (mul (wPoly seg 2) (v 2))

theorem eval_lvPoly (seg : Bool) (y : ℕ → ℝ) (v : Fin 3 → Poly) :
    eval y (lvPoly seg v) = ∑ c, wVal seg y c * eval y (v c) := by
  simp [lvPoly, eval_add, eval_mul, eval_wPoly, Fin.sum_univ_three]

def constVec (v : Fin 3 → ℚ) : Fin 3 → Poly := fun c => const (v c)

def crossQ (a b : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- `e × v` for a rational `e` and a polynomial vector `v`. -/
def crossPoly (e : Fin 3 → ℚ) (v : Fin 3 → Poly) : Fin 3 → Poly :=
  ![add (scale (e 1) (v 2)) (scale (-(e 2)) (v 1)),
    add (scale (e 2) (v 0)) (scale (-(e 0)) (v 2)),
    add (scale (e 0) (v 1)) (scale (-(e 1)) (v 0))]

/-- `N(X) p - d(X) q` for rational vectors `p, q`. -/
def innerMinusOuterPoly (X : Fin 3 → Poly) (p q : Fin 3 → ℚ) : Fin 3 → Poly :=
  fun r => add
    (add (add (scale (p 0) (numPolyOf X r 0)) (scale (p 1) (numPolyOf X r 1)))
      (scale (p 2) (numPolyOf X r 2)))
    (scale (-(q r)) (denPolyOf X))

end Noperts.Stellated.CornerPoly

end
