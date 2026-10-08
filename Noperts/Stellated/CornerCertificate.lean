module

public import Noperts.Stellated.CornerPoly

@[expose] public section

/-!
# Balanced-triple certificates in blow-up coordinates

A corner certificate is a triple of oriented rational edge directions with
inner and outer contact vertices.  Its determinant weights, support gaps and
denominator-cleared displacement are polynomials in the chart variables
(`CornerPoly`).  This file first states the certificate in terms of the view
(`not_rupertPose_of_corner_triple`), then identifies the polynomial values
with those quantities.
-/

namespace Noperts.Stellated.CornerCertificate

open scoped RealInnerProductSpace
open SparsePoly CornerPoly
open AtlasProjectiveLocalRigidity AtlasProjectiveView
open Noperts.ProjectiveView
open Noperts.BalancedSupport

structure Triple where
  edge : Fin 3 → Fin 3 → ℚ
  inner : Fin 3 → VertexIndex
  outer : Fin 3 → VertexIndex
deriving DecidableEq

noncomputable def Triple.edgeR (T : Triple) : EdgeTriple := fun i => toR3 (T.edge i)

/-- The relative rotation applied to a body vertex. -/
noncomputable def innerImage (p : AtlasPose ℝ) (k : VertexIndex) : ℝ³ :=
  (cayleyMatrix p.x p.y p.z).toEuclideanLin (exactVertex k)

/-- A contact direction is nonzero as soon as one of the other two weights
(a determinant involving it) is positive. -/
theorem direction_ne_zero_of_weights {p : AtlasPose ℝ} {edge : EdgeTriple}
    (hscale : viewScale 0 p ≠ 0) (i : Fin 3)
    (hw : ∃ j, j ≠ i ∧ 0 < weight 0 p edge j) :
    direction 0 p (edge i) ≠ 0 := by
  intro h0
  obtain ⟨j, hji, hj⟩ := hw
  have hdet := weight_eq_viewScale_mul_determinantWeights 0 p edge hscale j
  rw [hdet] at hj
  fin_cases i <;> fin_cases j <;> simp at hji <;>
    simp_all [determinantWeights, det2]

theorem outerProjection_eq_rotM (p : AtlasPose ℝ) (offset : ℝ²) (v : ℝ³) :
    outerProjectionLinear (p.matrixPoseWithOffset 0 offset) v = rotM p.θ p.φ v := by
  simpa [outerProjectionLinear, ContinuousLinearMap.comp_apply] using
    p.matrixPoseWithOffset_outer_rotation_project 0 offset v

theorem innerProjection_eq (p : AtlasPose ℝ) (offset : ℝ²) (k : VertexIndex) :
    proj_xyL ((p.matrixPoseWithOffset 0 offset).innerRot.val.toEuclideanLin
        (exactVertex k)) =
      outerProjectionLinear (p.matrixPoseWithOffset 0 offset) (innerImage p k) := by
  rw [outerProjection_eq_rotM, p.matrixPoseWithOffset_inner_rotation_project 0 offset]
  have h0 : CayleyAtlas.chartMatrix 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [CayleyAtlas.chartMatrix]
  simp [innerImage, h0]

/-- The semantic corner certificate. -/
theorem not_rupertPose_of_corner_triple (p : AtlasPose ℝ) (offset : ℝ²)
    (T : Triple) (hscale : 1 ≤ viewScale 0 p)
    (hw : ∀ i, 0 ≤ weight 0 p T.edgeR i)
    (hpos : ∀ i, ∃ j, j ≠ i ∧ 0 < weight 0 p T.edgeR j)
    (hgap : ∀ i k, linearValue (normalizedView 0 p)
      (cross3 (T.edgeR i) (exactVertex k - exactVertex (T.outer i))) ≤ 0)
    (hdisp : 0 ≤ ∑ i, weight 0 p T.edgeR i *
      linearValue (normalizedView 0 p)
        (cross3 (T.edgeR i) (innerImage p (T.inner i) - exactVertex (T.outer i)))) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hscale0 : viewScale 0 p ≠ 0 := by linarith
  apply AtlasProjectiveGlobalRigidity.not_rupertPose_of_projective_global_certificate
    0 p 0 offset T.edgeR T.inner T.outer hscale0
  · exact fun i => direction_ne_zero_of_weights hscale0 i (hpos i)
  · exact hw
  · obtain ⟨j, -, hj⟩ := hpos 0
    exact ⟨j, hj⟩
  · intro i k
    have h := hgap i k
    rw [← inner_direction_outerProjection_eq_support 0 p 0 offset _ _ hscale0,
      map_sub, inner_sub_right] at h
    linarith
  · convert hdisp using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← inner_direction_outerProjection_eq_support 0 p 0 offset _ _ hscale0,
      map_sub, innerProjection_eq]

/-! ## Certificate polynomials -/

def weightCoeff (T : Triple) : Fin 3 → Fin 3 → ℚ :=
  ![crossQ (T.edge 1) (T.edge 2), crossQ (T.edge 2) (T.edge 0),
    crossQ (T.edge 0) (T.edge 1)]

def weightPoly (seg : Bool) (T : Triple) (i : Fin 3) : Poly :=
  lvPoly seg (constVec (weightCoeff T i))

def gapCoeff (T : Triple) (i : Fin 3) (k : VertexIndex) : Fin 3 → ℚ :=
  crossQ (T.edge i) (fun c => rationalVertex k c - rationalVertex (T.outer i) c)

def gapPoly (seg : Bool) (T : Triple) (i : Fin 3) (k : VertexIndex) : Poly :=
  lvPoly seg (constVec (gapCoeff T i k))

/-- `lvPoly (crossPoly e v)` for the vector `![v₀, v₁, v₂]`, merged.  Taking the
three components as separate arguments of a non-inlined function makes each
one be computed exactly once: passed as a `Fin 3 → Poly` closure, the costly
inner vector of `termPoly` was rebuilt about nine times per term (the
compiler floats it back into the closures that read it). -/
@[noinline] def lvCrossOf (seg : Bool) (e : Fin 3 → ℚ) (v₀ v₁ v₂ : Poly) : Poly :=
  normalize (lvPoly seg (crossPoly e ![v₀, v₁, v₂]))

/-- Both factors are merged before multiplying: unmerged, the three terms of
`dispPoly` carry ~39k raw products for ~50 distinct monomials. -/
def termPoly (seg : Bool) (kind : ChartKind) (T : Triple) (i : Fin 3) : Poly :=
  let v := innerMinusOuterPoly (xPolyK seg kind) (rationalVertex (T.inner i))
    (rationalVertex (T.outer i))
  mul (normalize (weightPoly seg T i))
    (lvCrossOf seg (T.edge i) (normalize (v 0)) (normalize (v 1)) (normalize (v 2)))

def dispPoly (seg : Bool) (kind : ChartKind) (T : Triple) : Poly :=
  add (add (termPoly seg kind T 0) (termPoly seg kind T 1)) (termPoly seg kind T 2)

/-- Chart coordinates `y` describe the atlas pose `p`. -/
structure Coords (seg : Bool) (kind : ChartKind) (p : AtlasPose ℝ) (y : ℕ → ℝ) :
    Prop where
  view : ∀ c, normalizedView 0 p c = wVal seg y c
  cx : p.x = eval y (xPolyK seg kind 0)
  cy : p.y = eval y (xPolyK seg kind 1)
  cz : p.z = eval y (xPolyK seg kind 2)

theorem cross3_toR3 (a b : Fin 3 → ℚ) (c : Fin 3) :
    cross3 (toR3 a) (toR3 b) c = (crossQ a b c : ℝ) := by
  fin_cases c <;> simp [cross3, cross_apply, toR3, crossQ]

theorem linearValue_eq_sum (w v : Fin 3 → ℝ) :
    linearValue w v = ∑ c, w c * v c := by
  simp [linearValue, Fin.sum_univ_three]

theorem eval_weightPoly {seg : Bool} {kind : ChartKind} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (h : Coords seg kind p y) (T : Triple) (i : Fin 3) :
    eval y (weightPoly seg T i) = weight 0 p T.edgeR i := by
  simp only [weightPoly, eval_lvPoly, constVec, eval_const]
  fin_cases i <;>
    simp [weight, weightCoeff, Triple.edgeR, linearValue_eq_sum, cross3_toR3,
      h.view]

theorem eval_gapPoly {seg : Bool} {kind : ChartKind} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (h : Coords seg kind p y) (T : Triple) (i : Fin 3) (k : VertexIndex) :
    eval y (gapPoly seg T i k) = linearValue (normalizedView 0 p)
      (cross3 (T.edgeR i) (exactVertex k - exactVertex (T.outer i))) := by
  have hsub : exactVertex k - exactVertex (T.outer i) =
      toR3 (fun c => rationalVertex k c - rationalVertex (T.outer i) c) := by
    ext c; simp [exactVertex, toR3]
  rw [hsub]
  simp only [gapPoly, eval_lvPoly, constVec, eval_const, linearValue_eq_sum,
    Triple.edgeR, cross3_toR3, gapCoeff, h.view]

theorem eval_innerMinusOuter {seg : Bool} {kind : ChartKind} {p : AtlasPose ℝ}
    {y : ℕ → ℝ} (h : Coords seg kind p y) (P Q : VertexIndex) (r : Fin 3) :
    eval y (innerMinusOuterPoly (xPolyK seg kind) (rationalVertex P)
        (rationalVertex Q) r) =
      cayleyDenom p.x p.y p.z * (innerImage p P - exactVertex Q) r := by
  have hN := cayleyNumeratorMatrix_eq_denom_smul p.x p.y p.z
  simp only [innerMinusOuterPoly, eval_add, eval_scale, eval_numPolyOf,
    eval_denPolyOf, ← h.cx, ← h.cy, ← h.cz, hN]
  simp [innerImage, exactVertex, toR3, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

theorem eval_lvCross {seg : Bool} {kind : ChartKind} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (h : Coords seg kind p y) (e : Fin 3 → ℚ) (v : Fin 3 → Poly) (D : ℝ)
    (V : ℝ³) (hv : ∀ r, eval y (v r) = D * V r) :
    eval y (lvPoly seg (crossPoly e v)) =
      D * linearValue (normalizedView 0 p) (cross3 (toR3 e) V) := by
  simp only [eval_lvPoly, linearValue_eq_sum, h.view]
  simp [crossPoly, eval_add, eval_scale, hv, cross3, cross_apply, toR3,
    Fin.sum_univ_three]
  ring

theorem eval_dispPoly {seg : Bool} {kind : ChartKind} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (h : Coords seg kind p y) (T : Triple) :
    eval y (dispPoly seg kind T) = cayleyDenom p.x p.y p.z *
      ∑ i, weight 0 p T.edgeR i * linearValue (normalizedView 0 p)
        (cross3 (T.edgeR i) (innerImage p (T.inner i) - exactVertex (T.outer i))) := by
  have hterm : ∀ i, eval y (termPoly seg kind T i) =
      cayleyDenom p.x p.y p.z * (weight 0 p T.edgeR i *
        linearValue (normalizedView 0 p)
          (cross3 (T.edgeR i) (innerImage p (T.inner i) - exactVertex (T.outer i)))) := by
    intro i
    rw [termPoly, eval_mul, eval_normalize, eval_weightPoly h, lvCrossOf, eval_normalize,
      eval_lvCross h _ _ (cayleyDenom p.x p.y p.z)
        (innerImage p (T.inner i) - exactVertex (T.outer i)) (fun r => by
        have := eval_innerMinusOuter h (T.inner i) (T.outer i) r
        fin_cases r <;> simpa [eval_normalize] using this)]
    simp only [Triple.edgeR]
    ring
  simp only [dispPoly, eval_add, hterm, Fin.sum_univ_three]
  ring

/-! ## Rational row checker -/

def stripped (allowed : ℕ → Bool) (q : Poly) : Poly :=
  divByMono (normalize q) (gcdMono allowed (normalize q))

def strippedOk (allowed : ℕ → Bool) (q : Poly) : Bool :=
  dividesAll (gcdMono allowed (normalize q)) (normalize q)

/-- `q ≥ 0` on the box, after dividing out a monomial in `allowed` variables. -/
def NonnegOk0 (allowed : ℕ → Bool) (box : Box) (q : Poly) : Prop :=
  strippedOk allowed q = true ∧ 0 ≤ boxLower box (stripped allowed q)

def PosOk0 (allowed : ℕ → Bool) (box : Box) (q : Poly) : Prop :=
  strippedOk allowed q = true ∧ 0 < boxLower box (stripped allowed q)

/-- `q ≥ 0` on the box: directly, or after setting the box's fixed variables
(where cancellations become visible). -/
def NonnegOk (allowed : ℕ → Bool) (box : Box) (q : Poly) : Prop :=
  NonnegOk0 allowed box q ∨ NonnegOk0 allowed box (pinPoly box.pin q)

/-- `q > 0` on the box wherever the `allowed` variables are positive. -/
def PosOk (allowed : ℕ → Bool) (box : Box) (q : Poly) : Prop :=
  PosOk0 allowed box q ∨ PosOk0 allowed box (pinPoly box.pin q)

instance (allowed : ℕ → Bool) (box : Box) (q : Poly) :
    Decidable (NonnegOk0 allowed box q) := by unfold NonnegOk0; infer_instance

instance (allowed : ℕ → Bool) (box : Box) (q : Poly) :
    Decidable (PosOk0 allowed box q) := by unfold PosOk0; infer_instance

instance (allowed : ℕ → Bool) (box : Box) (q : Poly) :
    Decidable (NonnegOk allowed box q) := by unfold NonnegOk; infer_instance

instance (allowed : ℕ → Bool) (box : Box) (q : Poly) :
    Decidable (PosOk allowed box q) := by unfold PosOk; infer_instance

/-! ## Affine reparametrization of the chart variables -/

/-- Chart variables `2, 3, 4, 5` (`u, a, b, c`) as affine functions of new
variables `2, 3, 4, 5` (rows `[o, c₂, c₃, c₄, c₅]`); the empty list is the
identity. -/
def affPoly (aff : List (List ℚ)) (i : ℕ) : Poly :=
  if 2 ≤ i ∧ i ≤ 5 ∧ aff ≠ [] then
    let row := aff.getD (i - 2) []
    add (const (row.getD 0 0))
      (add (add (scale (row.getD 1 0) (var 2)) (scale (row.getD 2 0) (var 3)))
        (add (scale (row.getD 3 0) (var 4)) (scale (row.getD 4 0) (var 5))))
  else var i

noncomputable def affY (aff : List (List ℚ)) (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  eval y (affPoly aff i)

theorem affY_nil (y : ℕ → ℝ) : affY [] y = y := by
  funext i
  simp [affY, affPoly]

theorem affY_of_not_mem (aff : List (List ℚ)) (y : ℕ → ℝ) {i : ℕ}
    (hi : i < 2 ∨ 5 < i) : affY aff y i = y i := by
  simp only [affY, affPoly]
  rw [ite_eq_right (by omega)]
  simp

/-- A chart polynomial in the reparametrized variables. -/
def cmp (aff : List (List ℚ)) (q : Poly) : Poly :=
  if aff = [] then q else comp (normalize q) (affPoly aff)

theorem eval_cmp (aff : List (List ℚ)) (y : ℕ → ℝ) (q : Poly) :
    eval y (cmp aff q) = eval (affY aff y) q := by
  unfold cmp
  split_ifs with h
  · subst h
    rw [affY_nil]
  · rw [eval_comp, eval_normalize]
    rfl

structure Row where
  seg : Bool
  kind : ChartKind
  center : List ℚ
  radius : List ℚ
  triple : Triple
  /-- Split variables with their signs on the box (`true`: `≥ 0`); `ε` is
usually the last one. -/
  split : List (ℕ × Bool)
  /-- The displacement is checked in translated coordinates `y = shift + y'`
  (so a factor like `c - 1` at a box face becomes a split variable). -/
  shift : List ℚ := []
  /-- An affine reparametrization of `u, a, b, c` (see `affPoly`). -/
  aff : List (List ℚ) := []
deriving DecidableEq

def Row.box (r : Row) : Box := ⟨fun i => r.center.getD i 0, fun i => r.radius.getD i 0⟩

def Row.lo (r : Row) (i : ℕ) : ℚ := r.box.center i - r.box.radius i

def Row.hi (r : Row) (i : ℕ) : ℚ := r.box.center i + r.box.radius i

/-- Variables that are `≥ 0` on the box and not identically zero there (a
variable pinned at `0` is better substituted than divided out). -/
def Row.nonnegVars (r : Row) : ℕ → Bool := fun v => decide (0 ≤ r.lo v ∧ 0 < r.hi v)

def Row.isTube (r : Row) : Bool := r.kind.hasRho

/-- Variables known to be strictly positive: `ε`, `ρ` in a tube, and `λ`
whenever the box reaches `λ > 0` (the exact corner view `λ = 0` has its own
tables). -/
def Row.positiveVars (r : Row) : ℕ → Bool :=
  fun v => (v == 0 || (r.isTube && v == 6) || (v == 1 && decide (0 < r.hi 1))) &&
    decide (0 ≤ r.lo v)

/-- The normalized displacement. -/
def Row.D (r : Row) : Poly := normalize (cmp r.aff (dispPoly r.seg r.kind r.triple))

/-- The displacement is divided by `ε`, and in a tube box touching `ρ = 0`
also by `ρ` when it is divisible (it vanishes at `X = 0` when inner and outer
contacts agree, or at a view tie). -/
def Row.baseMono (r : Row) : Mono :=
  if r.isTube && decide (r.lo 6 ≤ 0) && dividesAll [1, 0, 0, 0, 0, 0, 1] r.D then
    [1, 0, 0, 0, 0, 0, 1] else [1]

def Row.F (r : Row) : Poly := divByMono r.D r.baseMono

def Row.shiftFn (r : Row) (i : ℕ) : ℚ := r.shift.getD i 0

/-- The box in the translated coordinates. -/
def Row.sbox (r : Row) : Box := ⟨fun i => r.box.center i - r.shiftFn i, r.box.radius⟩

/-- `F` in the translated coordinates. -/
def Row.G (r : Row) : Poly := if r.shift.isEmpty then r.F else shiftPoly r.shiftFn r.F

/-- Split a polynomial: terms divisible by the first split variable, the
remaining terms by the next, …; the rest is left over. -/
def splitParts : List ℕ → Poly → List Poly × Poly
  | [], p => ([], p)
  | v :: vs, p =>
      let (parts, rest) := splitParts vs (withoutVar v p)
      (divByMono (withVar v p) (varMono v) :: parts, rest)

def splitDivOk : List ℕ → Poly → Bool
  | [], _ => true
  | v :: vs, p => dividesAll (varMono v) (withVar v p) && splitDivOk vs (withoutVar v p)

theorem eval_splitParts (y : ℕ → ℝ) :
    ∀ (vs : List ℕ) (p : Poly), splitDivOk vs p = true →
      eval y p = ((splitParts vs p).1.zip vs).foldr
          (fun q acc => y q.2 * eval y q.1 + acc) 0 + eval y (splitParts vs p).2
  | [], p, _ => by
      simp only [splitParts, List.zip_nil_left, List.foldr_nil, zero_add]
  | v :: vs, p, h => by
      simp only [splitDivOk, Bool.and_eq_true] at h
      have ih := eval_splitParts y vs (withoutVar v p) h.2
      simp only [splitParts, List.zip_cons_cons, List.foldr_cons]
      rw [eval_withVar_add y v p, eval_divByMono y _ _ h.1, monoEval_varMono, ih]
      ring

def signQ (b : Bool) : ℚ := if b then 1 else -1

def Row.DispOk (r : Row) : Prop :=
  dividesAll r.baseMono r.D = true ∧
  splitDivOk (r.split.map Prod.fst) r.G = true ∧
  (∀ q ∈ r.split, if q.2 then 0 ≤ r.sbox.lo q.1 else r.sbox.hi q.1 ≤ 0) ∧
  (∀ q ∈ ((splitParts (r.split.map Prod.fst) r.G).1.zip r.split),
    NonnegOk r.sbox.nonnegVars r.sbox (scale (signQ q.2.2) q.1)) ∧
  NonnegOk r.sbox.nonnegVars r.sbox (splitParts (r.split.map Prod.fst) r.G).2

/-- `DispOk` with its intermediate polynomials passed in, so the checker
computes each of them once. -/
def Row.DispOkWith (r : Row) (D : Poly) (bm : Mono) (G : Poly)
    (parts : List Poly × Poly) : Prop :=
  dividesAll bm D = true ∧
  splitDivOk (r.split.map Prod.fst) G = true ∧
  (∀ q ∈ r.split, if q.2 then 0 ≤ r.sbox.lo q.1 else r.sbox.hi q.1 ≤ 0) ∧
  (∀ q ∈ (parts.1.zip r.split),
    NonnegOk r.sbox.nonnegVars r.sbox (scale (signQ q.2.2) q.1)) ∧
  NonnegOk r.sbox.nonnegVars r.sbox parts.2

instance (r : Row) (D : Poly) (bm : Mono) (G : Poly) (parts : List Poly × Poly) :
    Decidable (r.DispOkWith D bm G parts) := by
  unfold Row.DispOkWith; infer_instance

/-! The staged checker: `DispOk` mentions `r.D` four times (directly and via
`baseMono`, `F`, `G`) and `G` three times, and the compiled decision procedure
recomputed each occurrence; `D` alone is most of the row's cost.  Each stage
computes one intermediate value and hands it to the next (non-inlined) stage. -/

@[noinline] def Row.dispB4 (r : Row) (D : Poly) (bm : Mono) (G : Poly)
    (parts : List Poly × Poly) : Bool :=
  decide (r.DispOkWith D bm G parts)

@[noinline] def Row.dispB3 (r : Row) (D : Poly) (bm : Mono) (G : Poly) : Bool :=
  r.dispB4 D bm G (splitParts (r.split.map Prod.fst) G)

@[noinline] def Row.dispB2 (r : Row) (D : Poly) (bm : Mono) : Bool :=
  r.dispB3 D bm (if r.shift.isEmpty then divByMono D bm
    else shiftPoly r.shiftFn (divByMono D bm))

@[noinline] def Row.dispB1 (r : Row) (D : Poly) : Bool :=
  r.dispB2 D (if r.isTube && decide (r.lo 6 ≤ 0) &&
    dividesAll [1, 0, 0, 0, 0, 0, 1] D then [1, 0, 0, 0, 0, 0, 1] else [1])

def Row.dispB (r : Row) : Bool := r.dispB1 r.D

theorem Row.dispB_iff (r : Row) : r.dispB = true ↔ r.DispOk := by
  change decide (r.DispOkWith r.D r.baseMono r.G
    (splitParts (r.split.map Prod.fst) r.G)) = true ↔ _
  rw [decide_eq_true_iff]
  rfl

instance (r : Row) : Decidable r.DispOk := decidable_of_iff _ r.dispB_iff

structure Row.Valid (r : Row) : Prop where
  radius : ∀ x ∈ r.radius, 0 ≤ x
  /-- Weights are nonnegative, and each contact has a positive weight among
  the other two (so a two-contact "width" certificate with one zero weight
  is allowed). -/
  weights : ∀ i, NonnegOk r.nonnegVars r.box (cmp r.aff (weightPoly r.seg r.triple i))
  weightsPos : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧
    PosOk r.positiveVars r.box (cmp r.aff (weightPoly r.seg r.triple j))
  gaps : ∀ i k, NonnegOk r.nonnegVars r.box
    (scale (-1) (cmp r.aff (gapPoly r.seg r.triple i k)))
  disp : r.DispOk

instance (r : Row) : Decidable r.Valid :=
  decidable_of_iff (( ∀ x ∈ r.radius, 0 ≤ x) ∧
      (∀ i, NonnegOk r.nonnegVars r.box (cmp r.aff (weightPoly r.seg r.triple i))) ∧
      (∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧
        PosOk r.positiveVars r.box (cmp r.aff (weightPoly r.seg r.triple j))) ∧
      (∀ i k, NonnegOk r.nonnegVars r.box
        (scale (-1) (cmp r.aff (gapPoly r.seg r.triple i k)))) ∧
      r.DispOk)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-! ## Soundness -/

theorem Row.radius_nonneg (r : Row) (h : ∀ x ∈ r.radius, 0 ≤ x) (i : ℕ) :
    0 ≤ r.box.radius i := by
  simp only [Row.box, List.getD_eq_getElem?_getD]
  cases hi : r.radius[i]? with
  | none => simp
  | some x => simpa using h x (List.mem_of_getElem? hi)

theorem stripped_eval (allowed : ℕ → Bool) (q : Poly) (y : ℕ → ℝ)
    (h : strippedOk allowed q = true) :
    eval y q = monoEval y (gcdMono allowed (normalize q)) * eval y (stripped allowed q) := by
  rw [← eval_normalize y q]
  exact eval_divByMono y _ _ h

theorem NonnegOk0.sound {allowed : ℕ → Bool} {box : Box} {q : Poly}
    (h : NonnegOk0 allowed box q) {y : ℕ → ℝ} (hmem : box.Mem y)
    (hrad : ∀ i, 0 ≤ box.radius i) (hvars : ∀ v, allowed v = true → 0 ≤ y v) :
    0 ≤ eval y q := by
  rw [stripped_eval allowed q y h.1]
  apply mul_nonneg
  · exact monoEval_nonneg_of y _ fun i hi => hvars i (gcdMono_getD_pos allowed _ i hi)
  · exact le_trans (by exact_mod_cast h.2) (boxLower_le box _ hmem hrad)

theorem PosOk0.sound {allowed : ℕ → Bool} {box : Box} {q : Poly}
    (h : PosOk0 allowed box q) {y : ℕ → ℝ} (hmem : box.Mem y)
    (hrad : ∀ i, 0 ≤ box.radius i) (hvars : ∀ v, allowed v = true → 0 < y v) :
    0 < eval y q := by
  rw [stripped_eval allowed q y h.1]
  apply mul_pos
  · exact monoEval_pos_of y _ fun i hi => hvars i (gcdMono_getD_pos allowed _ i hi)
  · exact lt_of_lt_of_le (by exact_mod_cast h.2) (boxLower_le box _ hmem hrad)

theorem NonnegOk.sound {allowed : ℕ → Bool} {box : Box} {q : Poly}
    (h : NonnegOk allowed box q) {y : ℕ → ℝ} (hmem : box.Mem y)
    (hrad : ∀ i, 0 ≤ box.radius i) (hvars : ∀ v, allowed v = true → 0 ≤ y v) :
    0 ≤ eval y q := by
  rcases h with h | h
  · exact h.sound hmem hrad hvars
  · rw [← eval_pinPoly _ y (Box.pin_spec hmem) q]
    exact h.sound hmem hrad hvars

theorem PosOk.sound {allowed : ℕ → Bool} {box : Box} {q : Poly}
    (h : PosOk allowed box q) {y : ℕ → ℝ} (hmem : box.Mem y)
    (hrad : ∀ i, 0 ≤ box.radius i) (hvars : ∀ v, allowed v = true → 0 < y v) :
    0 < eval y q := by
  rcases h with h | h
  · exact h.sound hmem hrad hvars
  · rw [← eval_pinPoly _ y (Box.pin_spec hmem) q]
    exact h.sound hmem hrad hvars

theorem Row.nonnegVars_sound (r : Row) {y : ℕ → ℝ} (hmem : r.box.Mem y) (v : ℕ)
    (hv : r.nonnegVars v = true) : 0 ≤ y v := by
  simp only [Row.nonnegVars, Row.lo] at hv
  replace hv := (of_decide_eq_true hv).1
  have := abs_le.mp (hmem v)
  have hv' : (0 : ℝ) ≤ (r.box.center v : ℝ) - r.box.radius v := by exact_mod_cast hv
  linarith [this.1]

theorem Row.positiveVars_sound (r : Row) {y : ℕ → ℝ} (hε : 0 < y 0)
    (hρ : r.isTube = true → 0 < y 6) (hlam : 0 < r.hi 1 → 0 < y 1) (v : ℕ)
    (hv : r.positiveVars v = true) : 0 < y v := by
  simp only [Row.positiveVars, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hv
  rcases hv.1 with (h0 | ⟨ht, h6⟩) | ⟨h1, hhi⟩
  · exact h0 ▸ hε
  · exact h6 ▸ hρ ht
  · exact h1 ▸ hlam hhi

theorem monoEval_varMono (y : ℕ → ℝ) (i : ℕ) : monoEval y (varMono i) = y i := by
  simpa [var, eval] using eval_var y i

theorem _root_.Noperts.Stellated.SparsePoly.Box.split_sign_sound (b : Box) {y : ℕ → ℝ}
    (hmem : b.Mem y)
    (q : ℕ × Bool) (hq : if q.2 then 0 ≤ b.lo q.1 else b.hi q.1 ≤ 0) :
    0 ≤ (signQ q.2 : ℝ) * y q.1 := by
  have hb := abs_le.mp (hmem q.1)
  cases h2 : q.2 <;> simp only [h2, ite_true, ite_false, Bool.false_eq_true] at hq <;>
    simp only [signQ, ite_true, ite_false, Bool.false_eq_true]
  · have : ((b.hi q.1 : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hq
    simp only [Box.hi] at this
    push_cast at this ⊢
    linarith [hb.2]
  · have : (0 : ℝ) ≤ ((b.lo q.1 : ℚ) : ℝ) := by exact_mod_cast hq
    simp only [Box.lo] at this
    push_cast at this ⊢
    linarith [hb.1]

theorem foldr_nonneg_aux (y : ℕ → ℝ) (r : Box) (hmem : r.Mem y)
    (hrad : ∀ i, 0 ≤ r.radius i) :
    ∀ (parts : List Poly) (sp : List (ℕ × Bool)),
      (∀ q ∈ sp, if q.2 then 0 ≤ r.lo q.1 else r.hi q.1 ≤ 0) →
      (∀ q ∈ parts.zip sp, NonnegOk r.nonnegVars r (scale (signQ q.2.2) q.1)) →
      0 ≤ (parts.zip (sp.map Prod.fst)).foldr (fun q acc => y q.2 * eval y q.1 + acc) 0
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | part :: parts, q :: sp, hs, hok => by
      simp only [List.map_cons, List.zip_cons_cons, List.foldr_cons]
      apply add_nonneg
      · have hsign := r.split_sign_sound hmem q (hs q (by simp))
        have hpart := NonnegOk.sound (hok (part, q) (by simp)) hmem hrad
          (r.nonnegVars_sound hmem)
        rw [eval_scale] at hpart
        have : 0 ≤ ((signQ q.2 : ℝ) * y q.1) * ((signQ q.2 : ℝ) * eval y part) :=
          mul_nonneg hsign (by exact_mod_cast hpart)
        have hsq : (signQ q.2 : ℝ) * (signQ q.2 : ℝ) = 1 := by
          unfold signQ; split_ifs <;> norm_num
        nlinarith [this, hsq]
      · exact foldr_nonneg_aux y r hmem hrad parts sp
          (fun q' hq' => hs q' (by simp [hq']))
          (fun q' hq' => hok q' (by simp [hq']))

theorem Row.eval_G (r : Row) (y : ℕ → ℝ) :
    eval y r.G = eval (fun i => r.shiftFn i + y i) r.F := by
  unfold Row.G
  split_ifs with h
  · congr 1
    funext i
    simp [Row.shiftFn, List.isEmpty_iff.mp h]
  · exact eval_shiftPoly y _ _

theorem Row.eval_F_nonneg (r : Row) (hd : r.DispOk) {y : ℕ → ℝ}
    (hmem : r.box.Mem y) (hrad : ∀ i, 0 ≤ r.box.radius i) :
    0 ≤ eval y r.F := by
  obtain ⟨-, hdiv, hsigns, hparts, hrest⟩ := hd
  set y' : ℕ → ℝ := fun i => y i - r.shiftFn i
  have hmem' : r.sbox.Mem y' := by
    intro i
    have := hmem i
    simp only [Row.sbox, y']
    push_cast
    convert this using 2
    ring
  have hy : (fun i => (r.shiftFn i : ℝ) + y' i) = y := by
    funext i
    simp [y']
  rw [← hy, ← r.eval_G, eval_splitParts y' _ _ hdiv]
  have hsum := foldr_nonneg_aux y' r.sbox hmem' hrad
    (splitParts (r.split.map Prod.fst) r.G).1 r.split hsigns hparts
  have h2 := NonnegOk.sound hrest hmem' hrad (r.sbox.nonnegVars_sound hmem')
  linarith

/-- A valid row rules out every pose whose chart coordinates lie in its box. -/
theorem Row.not_rupert (r : Row) (hv : r.Valid) (p : AtlasPose ℝ) (offset : ℝ²)
    (y : ℕ → ℝ) (hc : Coords r.seg r.kind p (affY r.aff y)) (hmem : r.box.Mem y)
    (hε : 0 < y 0) (hρ : r.isTube = true → 0 < y 6) (hlam : 0 < r.hi 1 → 0 < y 1)
    (hscale : 1 ≤ viewScale 0 p) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hrad := r.radius_nonneg hv.radius
  apply not_rupertPose_of_corner_triple p offset r.triple hscale
  · intro i
    rw [← eval_weightPoly hc, ← eval_cmp]
    exact NonnegOk.sound (hv.weights i) hmem hrad (r.nonnegVars_sound hmem)
  · intro i
    obtain ⟨j, hji, hj⟩ := hv.weightsPos i
    refine ⟨j, hji, ?_⟩
    rw [← eval_weightPoly hc, ← eval_cmp]
    exact PosOk.sound hj hmem hrad (r.positiveVars_sound hε hρ hlam)
  · intro i k
    rw [← eval_gapPoly hc, ← eval_cmp]
    have := NonnegOk.sound (hv.gaps i k) hmem hrad (r.nonnegVars_sound hmem)
    rw [eval_scale] at this
    push_cast at this
    linarith
  · have hdisp := eval_dispPoly hc r.triple
    have hD : 0 ≤ eval (affY r.aff y) (dispPoly r.seg r.kind r.triple) := by
      rw [← eval_cmp, ← eval_normalize y, ← Row.D, eval_divByMono y _ _ hv.disp.1]
      apply mul_nonneg
      · apply monoEval_nonneg_of
        intro i hi
        unfold Row.baseMono at hi
        split_ifs at hi with ht
        · simp only [Bool.and_eq_true] at ht
          rcases i with _ | _ | _ | _ | _ | _ | _ | i
          · exact hε.le
          all_goals first | exact (hρ ht.1.1).le | simp at hi
        · rcases i with _ | i
          · exact hε.le
          · simp at hi
      · exact r.eval_F_nonneg hv.disp hmem hrad
    rw [hdisp] at hD
    have hd := cayleyDenom_pos p.x p.y p.z
    exact nonneg_of_mul_nonneg_right (by linarith) hd |>.trans_eq' rfl

/-! ## Rows sharing a table's root-frame facts

The weight and gap conditions depend only on the triple (and chart), and in
practice hold on a whole table's root frame.  A row whose box lies in that
frame can cite them from a shared `KeyFacts` row instead of re-checking them. -/

/-- The weight and gap conditions of `Row.Valid`, on the row's own box. -/
structure Row.KeyFacts (r : Row) : Prop where
  radius : ∀ x ∈ r.radius, 0 ≤ x
  weights : ∀ i, NonnegOk r.nonnegVars r.box (cmp r.aff (weightPoly r.seg r.triple i))
  weightsPos : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧
    PosOk r.positiveVars r.box (cmp r.aff (weightPoly r.seg r.triple j))
  gaps : ∀ i k, NonnegOk r.nonnegVars r.box
    (scale (-1) (cmp r.aff (gapPoly r.seg r.triple i k)))

instance (r : Row) : Decidable r.KeyFacts :=
  decidable_of_iff (( ∀ x ∈ r.radius, 0 ≤ x) ∧
      (∀ i, NonnegOk r.nonnegVars r.box (cmp r.aff (weightPoly r.seg r.triple i))) ∧
      (∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧
        PosOk r.positiveVars r.box (cmp r.aff (weightPoly r.seg r.triple j))) ∧
      (∀ i k, NonnegOk r.nonnegVars r.box
        (scale (-1) (cmp r.aff (gapPoly r.seg r.triple i k)))))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- The number of coordinates either row's box mentions. -/
def Row.boxDim (r f : Row) : ℕ :=
  max (max r.center.length r.radius.length) (max f.center.length f.radius.length)

/-- The box of `r` lies inside the box of `f`. -/
def Row.SubBox (r f : Row) : Prop :=
  ∀ i < r.boxDim f, |r.box.center i - f.box.center i| + r.box.radius i ≤ f.box.radius i

instance (r f : Row) : Decidable (r.SubBox f) := by unfold Row.SubBox; infer_instance

theorem Row.SubBox.mem {r f : Row} (h : r.SubBox f) {y : ℕ → ℝ} (hy : r.box.Mem y) :
    f.box.Mem y := by
  intro i
  by_cases hi : i < r.boxDim f
  · have hsub : ((|r.box.center i - f.box.center i| + r.box.radius i : ℚ) : ℝ) ≤
        (f.box.radius i : ℝ) := by exact_mod_cast h i hi
    push_cast at hsub
    have hyi := hy i
    calc |y i - (f.box.center i : ℝ)|
        ≤ |y i - (r.box.center i : ℝ)| + |(r.box.center i : ℝ) - f.box.center i| := by
          simpa using abs_sub_le (y i) (r.box.center i : ℝ) (f.box.center i : ℝ)
      _ ≤ f.box.radius i := by linarith
  · have hge : r.boxDim f ≤ i := Nat.le_of_not_lt hi
    simp only [Row.boxDim] at hge
    have h1 : r.center.length ≤ i := by omega
    have h2 : r.radius.length ≤ i := by omega
    have h3 : f.center.length ≤ i := by omega
    have h4 : f.radius.length ≤ i := by omega
    have hyi := hy i
    simp only [Row.box, List.getD_eq_getElem?_getD, List.getElem?_eq_none h1,
      List.getElem?_eq_none h2, Option.getD_none, Rat.cast_zero] at hyi
    simp only [Row.box, List.getD_eq_getElem?_getD, List.getElem?_eq_none h3,
      List.getElem?_eq_none h4, Option.getD_none, Rat.cast_zero]
    exact hyi

/-- A row validated against a shared fact row (normally the table's root frame
with the row's triple). -/
structure Row.SharedValid (r f : Row) : Prop where
  seg : r.seg = f.seg
  kind : r.kind = f.kind
  triple : r.triple = f.triple
  aff : r.aff = []
  faff : f.aff = []
  sub : r.SubBox f
  lam : 0 < f.hi 1 → 0 < r.hi 1
  radius : ∀ x ∈ r.radius, 0 ≤ x
  disp : r.DispOk

instance (r f : Row) : Decidable (r.SharedValid f) :=
  decidable_of_iff (r.seg = f.seg ∧ r.kind = f.kind ∧ r.triple = f.triple ∧ r.aff = [] ∧
      f.aff = [] ∧ r.SubBox f ∧ (0 < f.hi 1 → 0 < r.hi 1) ∧ (∀ x ∈ r.radius, 0 ≤ x) ∧
      r.DispOk)
    ⟨fun ⟨a, b, c, d, e, g, h, i, j⟩ => ⟨a, b, c, d, e, g, h, i, j⟩,
      fun ⟨a, b, c, d, e, g, h, i, j⟩ => ⟨a, b, c, d, e, g, h, i, j⟩⟩

/-- A fact row certifies every point of its box where the displacement is
nonnegative. -/
theorem Row.not_rupert_fact (f : Row) (hf : f.KeyFacts) (hfaff : f.aff = [])
    (p : AtlasPose ℝ) (offset : ℝ²)
    (y : ℕ → ℝ) (hc : Coords f.seg f.kind p y) (hmemF : f.box.Mem y)
    (hε : 0 < y 0) (hρ : f.isTube = true → 0 < y 6) (hlam : 0 < f.hi 1 → 0 < y 1)
    (hscale : 1 ≤ viewScale 0 p) (hD : 0 ≤ eval y f.D) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hradF := f.radius_nonneg hf.radius
  have hcf : Coords f.seg f.kind p (affY f.aff y) := by rw [hfaff, affY_nil]; exact hc
  apply not_rupertPose_of_corner_triple p offset f.triple hscale
  · intro i
    rw [← eval_weightPoly hcf, ← eval_cmp]
    exact NonnegOk.sound (hf.weights i) hmemF hradF (f.nonnegVars_sound hmemF)
  · intro i
    obtain ⟨j, hji, hj⟩ := hf.weightsPos i
    refine ⟨j, hji, ?_⟩
    rw [← eval_weightPoly hcf, ← eval_cmp]
    exact PosOk.sound hj hmemF hradF (f.positiveVars_sound hε hρ hlam)
  · intro i k
    rw [← eval_gapPoly hcf, ← eval_cmp]
    have := NonnegOk.sound (hf.gaps i k) hmemF hradF (f.nonnegVars_sound hmemF)
    rw [eval_scale] at this
    push_cast at this
    linarith
  · have hdisp := eval_dispPoly hcf f.triple
    have hD' : 0 ≤ eval (affY f.aff y) (dispPoly f.seg f.kind f.triple) := by
      rw [← eval_cmp, ← eval_normalize y, ← Row.D]
      exact hD
    rw [hdisp] at hD'
    have hd := cayleyDenom_pos p.x p.y p.z
    exact nonneg_of_mul_nonneg_right (by linarith) hd |>.trans_eq' rfl
      |> fun h => (le_of_mul_le_mul_left (by simpa using hD') hd)

/-- A row sharing `f`'s key facts, given the displacement's sign at the point. -/
theorem Row.not_rupert_sharedD (r f : Row) (hf : f.KeyFacts) (hseg : r.seg = f.seg)
    (hkind : r.kind = f.kind) (htriple : r.triple = f.triple) (haff : r.aff = [])
    (hfaff : f.aff = []) (hsub : r.SubBox f) (hlamI : 0 < f.hi 1 → 0 < r.hi 1)
    (p : AtlasPose ℝ) (offset : ℝ²)
    (y : ℕ → ℝ) (hc : Coords r.seg r.kind p (affY r.aff y)) (hmem : r.box.Mem y)
    (hε : 0 < y 0) (hρ : r.isTube = true → 0 < y 6) (hlam : 0 < r.hi 1 → 0 < y 1)
    (hscale : 1 ≤ viewScale 0 p) (hD : 0 ≤ eval y r.D) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hradF := f.radius_nonneg hf.radius
  have hmemF := hsub.mem hmem
  have hcf : Coords f.seg f.kind p (affY f.aff y) := by
    rw [hfaff, ← haff, ← hseg, ← hkind]; exact hc
  have hρF : f.isTube = true → 0 < y 6 := fun h =>
    hρ (by simpa [Row.isTube, hkind] using h)
  apply not_rupertPose_of_corner_triple p offset r.triple hscale
  · intro i
    rw [htriple, ← eval_weightPoly hcf, ← eval_cmp]
    exact NonnegOk.sound (hf.weights i) hmemF hradF (f.nonnegVars_sound hmemF)
  · intro i
    obtain ⟨j, hji, hj⟩ := hf.weightsPos i
    refine ⟨j, hji, ?_⟩
    rw [htriple, ← eval_weightPoly hcf, ← eval_cmp]
    exact PosOk.sound hj hmemF hradF (f.positiveVars_sound hε hρF (fun h => hlam (hlamI h)))
  · intro i k
    rw [htriple, ← eval_gapPoly hcf, ← eval_cmp]
    have := NonnegOk.sound (hf.gaps i k) hmemF hradF (f.nonnegVars_sound hmemF)
    rw [eval_scale] at this
    push_cast at this
    linarith
  · have hdisp := eval_dispPoly hc r.triple
    have hD' : 0 ≤ eval (affY r.aff y) (dispPoly r.seg r.kind r.triple) := by
      rw [← eval_cmp, ← eval_normalize y, ← Row.D]
      exact hD
    rw [hdisp] at hD'
    have hd := cayleyDenom_pos p.x p.y p.z
    exact nonneg_of_mul_nonneg_right (by linarith) hd |>.trans_eq' rfl
      |> fun h => (le_of_mul_le_mul_left (by simpa using hD') hd)

theorem Row.not_rupert_shared (r f : Row) (hf : f.KeyFacts) (hv : r.SharedValid f)
    (p : AtlasPose ℝ) (offset : ℝ²)
    (y : ℕ → ℝ) (hc : Coords r.seg r.kind p (affY r.aff y)) (hmem : r.box.Mem y)
    (hε : 0 < y 0) (hρ : r.isTube = true → 0 < y 6) (hlam : 0 < r.hi 1 → 0 < y 1)
    (hscale : 1 ≤ viewScale 0 p) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hrad := r.radius_nonneg hv.radius
  refine r.not_rupert_sharedD f hf hv.seg hv.kind hv.triple hv.aff hv.faff hv.sub hv.lam
    p offset y hc hmem hε hρ hlam hscale ?_
  rw [eval_divByMono y _ _ hv.disp.1]
  apply mul_nonneg
  · apply monoEval_nonneg_of
    intro i hi
    unfold Row.baseMono at hi
    split_ifs at hi with ht
    · simp only [Bool.and_eq_true] at ht
      rcases i with _ | _ | _ | _ | _ | _ | _ | i
      · exact hε.le
      all_goals first | exact (hρ ht.1.1).le | simp at hi
    · rcases i with _ | i
      · exact hε.le
      · simp at hi
  · exact r.eval_F_nonneg hv.disp hmem hrad

end Noperts.Stellated.CornerCertificate

end
