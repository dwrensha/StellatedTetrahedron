module

public import Noperts.Stellated.CornerKernelFast
public import Noperts.Stellated.CornerCertificate

@[expose] public section

/-!
# Kernel-friendly shared corner leaves

A shared fact row `f` gets a `FactPoly`: integer data `S`, a monomial `m` and
a scale `K` with `D / ε = m · S / K` identically (`FactPoly.Ok`, checked once
per fact).  A leaf row then only needs `S ≥ 0` on its box, which `cheapRow`
certifies with the packed Nat cheap bound (`cheapP`), and the variables of `m`
nonnegative there.
-/

namespace Noperts.Stellated.CornerKernel

open scoped RealInnerProductSpace
open SparsePoly CornerCertificate CornerPoly
open AtlasProjectiveLocalRigidity AtlasProjectiveView
open Noperts.ProjectiveView

structure FactPoly where
  S : List (Mono × ℕ × Bool)
  m : Mono
  K : ℕ
deriving DecidableEq

def FactPoly.residual (fp : FactPoly) (f : Row) : Poly :=
  normalize (add (divByMono f.D [1])
    (scale (-(1 / (fp.K : ℚ))) (mul [(fp.m, 1)] (toIPoly fp.S).toPoly)))

/-- `D / ε = m · S / K` for the fact's displacement `D`. -/
def FactPoly.Ok (fp : FactPoly) (f : Row) : Prop :=
  0 < fp.K ∧ dividesAll [1] f.D = true ∧ fp.residual f = []

instance (fp : FactPoly) (f : Row) : Decidable (fp.Ok f) := by
  unfold FactPoly.Ok; infer_instance

theorem FactPoly.Ok.eval_D {fp : FactPoly} {f : Row} (h : fp.Ok f) (y : ℕ → ℝ) :
    eval y f.D = y 0 * (monoEval y fp.m * eval y (toIPoly fp.S).toPoly / fp.K) := by
  obtain ⟨hK, hdiv, hres⟩ := h
  have h0 := congrArg (eval y) hres
  simp only [FactPoly.residual, eval_normalize, eval_add, eval_scale, eval_mul, eval_nil,
    eval_cons] at h0
  rw [eval_divByMono y _ _ hdiv]
  have hm1 : monoEval y [1] = y 0 := by simp [monoEval, monoEvalFrom]
  have hKr : (0 : ℝ) < fp.K := by exact_mod_cast hK
  rw [hm1]
  congr 1
  push_cast at h0
  field_simp
  field_simp at h0
  linarith

/-! ## Leaf boxes as integers -/

/-- `L · q` as an integer, for `q.den ∣ L`. -/
def qScale (L : ℕ) (q : ℚ) : ℤ := q.num * ((L / q.den : ℕ) : ℤ)

theorem qScale_cast (L : ℕ) (q : ℚ) (h : q.den ∣ L) : (qScale L q : ℚ) = L * q := by
  obtain ⟨m, rfl⟩ := h
  simp only [qScale, Nat.mul_div_cancel_left m q.den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num q]
  ring

/-- A common denominator of the box's first seven centers and radii. -/
def boxLcm (r : Row) : ℕ :=
  (List.range 7).foldr (fun i acc =>
    Nat.lcm (Nat.lcm (r.box.center i).den (r.box.radius i).den) acc) 1

theorem boxLcm_pos (r : Row) : 0 < boxLcm r := by
  unfold boxLcm
  induction (List.range 7) with
  | nil => simp
  | cons i l ih =>
      simp only [List.foldr_cons]
      exact Nat.lcm_pos (Nat.lcm_pos (Rat.den_pos _) (Rat.den_pos _)) ih

theorem dvd_foldr_lcm (r : Row) (i : ℕ) : ∀ l : List ℕ, i ∈ l →
    (r.box.center i).den ∣ l.foldr (fun i acc =>
      Nat.lcm (Nat.lcm (r.box.center i).den (r.box.radius i).den) acc) 1 ∧
    (r.box.radius i).den ∣ l.foldr (fun i acc =>
      Nat.lcm (Nat.lcm (r.box.center i).den (r.box.radius i).den) acc) 1
  | [], h => by simp at h
  | j :: l, h => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨(Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _),
          (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _)⟩
      · obtain ⟨h1, h2⟩ := dvd_foldr_lcm r i l h
        exact ⟨h1.trans (Nat.dvd_lcm_right _ _), h2.trans (Nat.dvd_lcm_right _ _)⟩

theorem dvd_boxLcm (r : Row) (i : ℕ) (hi : i < 7) :
    (r.box.center i).den ∣ boxLcm r ∧ (r.box.radius i).den ∣ boxLcm r :=
  dvd_foldr_lcm r i _ (List.mem_range.mpr hi)

def boxX (r : Row) : List ℤ := (List.range 7).map fun i => qScale (boxLcm r) (r.box.center i)

def boxH (r : Row) : List ℕ :=
  (List.range 7).map fun i => (qScale (boxLcm r) (r.box.radius i)).toNat

def boxY (r : Row) : List ℤ := (List.range 7).map fun i =>
  qScale (boxLcm r) (r.box.center i) - qScale (boxLcm r) (r.box.radius i)

/-- `S ≥ 0` on the row's box, by the cheap bound at the center or at the
lower corner. -/
def cheapRow (S : List (Mono × ℕ × Bool)) (r : Row) : Bool :=
  Nat.ble r.center.length 7 && Nat.ble r.radius.length 7 &&
    (cheapP S (boxLcm r) ((boxX r).map Int.natAbs) ((boxX r).map fun x => decide (x < 0))
        (boxH r) true ||
      cheapP S (boxLcm r) ((boxY r).map Int.natAbs) ((boxY r).map fun x => decide (x < 0))
        ((boxH r).map (2 * ·)) false)

theorem xI_map (l : List ℤ) (i : ℕ) :
    xI (l.map Int.natAbs) (l.map fun x => decide (x < 0)) i = l.getD i 0 := by
  simp only [xI, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => simp
  | some x =>
      simp only [Option.map_some, Option.getD_some]
      split_ifs with h
      · simp only [decide_eq_true_eq] at h; omega
      · simp only [decide_eq_true_eq, not_lt] at h; omega

theorem box_beyond (r : Row) (hc : r.center.length ≤ 7) (hr : r.radius.length ≤ 7) (i : ℕ)
    (hi : ¬ i < 7) : r.box.center i = 0 ∧ r.box.radius i = 0 := by
  simp [Row.box, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : r.center.length ≤ i),
    List.getElem?_eq_none (by omega : r.radius.length ≤ i)]

/-- The scaled coordinates. -/
theorem boxX_getD (r : Row) (hc : r.center.length ≤ 7) (hr : r.radius.length ≤ 7) (i : ℕ) :
    ((boxX r).getD i 0 : ℝ) = boxLcm r * (r.box.center i : ℝ) := by
  by_cases hi : i < 7
  · have h := qScale_cast _ _ (dvd_boxLcm r i hi).1
    simp only [boxX, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    exact_mod_cast h
  · simp [boxX, List.getD_eq_getElem?_getD, hi, (box_beyond r hc hr i hi).1]

theorem boxH_getD (r : Row) (hc : r.center.length ≤ 7) (hr : r.radius.length ≤ 7)
    (hrad : ∀ i, 0 ≤ r.box.radius i) (i : ℕ) :
    ((natI (boxH r) i : ℤ) : ℝ) = boxLcm r * (r.box.radius i : ℝ) := by
  by_cases hi : i < 7
  · have h := qScale_cast _ _ (dvd_boxLcm r i hi).2
    have hnn : 0 ≤ qScale (boxLcm r) (r.box.radius i) := by
      have : (0 : ℚ) ≤ qScale (boxLcm r) (r.box.radius i) := by
        rw [h]; exact mul_nonneg (by positivity) (hrad i)
      exact_mod_cast this
    simp only [natI, boxH, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some, Int.toNat_of_nonneg hnn]
    exact_mod_cast h
  · simp [natI, boxH, List.getD_eq_getElem?_getD, hi, (box_beyond r hc hr i hi).2]

theorem natI_map_two (l : List ℕ) (i : ℕ) : natI (l.map (2 * ·)) i = 2 * natI l i := by
  simp only [natI, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem boxY_getD (r : Row) (i : ℕ) :
    (boxY r).getD i 0 = (boxX r).getD i 0 - qScale (boxLcm r) (r.box.radius i) * (if i < 7 then 1 else 0) := by
  by_cases hi : i < 7
  · simp [boxY, boxX, List.getD_eq_getElem?_getD, hi]
  · simp [boxY, boxX, List.getD_eq_getElem?_getD, hi]

theorem cheapRow_sound (S : List (Mono × ℕ × Bool)) (r : Row) (h : cheapRow S r = true)
    (hrad : ∀ i, 0 ≤ r.box.radius i) (y : ℕ → ℝ) (hmem : r.box.Mem y) :
    0 ≤ eval y (toIPoly S).toPoly := by
  simp only [cheapRow, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hc, hr⟩, h⟩ := h
  have hL : (0 : ℝ) < boxLcm r := by exact_mod_cast boxLcm_pos r
  have hX := boxX_getD r hc hr
  have hH := boxH_getD r hc hr hrad
  rcases h with h | h
  · refine cheapI_sound _ _ _ _ _ (cheapP_imp _ _ _ _ _ _ h) y fun i => ?_
    rw [xI_map]
    have hm := abs_le.mp (hmem i)
    simp only [loI, ite_true]
    push_cast
    rw [hX, hH]
    constructor
    · rw [neg_div, mul_div_cancel_left₀ _ hL.ne', mul_div_cancel_left₀ _ hL.ne']; linarith
    · rw [mul_div_cancel_left₀ _ hL.ne', mul_div_cancel_left₀ _ hL.ne']; linarith
  · refine cheapI_sound _ _ _ _ _ (cheapP_imp _ _ _ _ _ _ h) y fun i => ?_
    rw [xI_map]
    have hm := abs_le.mp (hmem i)
    simp only [loI, Bool.false_eq_true, ite_false, natI_map_two]
    have hY : ((boxY r).getD i 0 : ℝ) = boxLcm r * ((r.box.center i : ℝ) - r.box.radius i) := by
      by_cases hi : i < 7
      · have h2 := qScale_cast _ _ (dvd_boxLcm r i hi).2
        have h1 := hX i
        rw [boxY_getD, ite_eq_left hi]
        push_cast
        rw [h1]
        have : ((qScale (boxLcm r) (r.box.radius i) : ℤ) : ℝ) = boxLcm r * (r.box.radius i : ℝ) := by
          exact_mod_cast h2
        rw [this]; ring
      · obtain ⟨h1, h2⟩ := box_beyond r hc hr i hi
        simp [boxY, List.getD_eq_getElem?_getD, hi, h1, h2]
    push_cast
    rw [hY, hH]
    constructor
    · rw [mul_div_cancel_left₀ _ hL.ne']; simp; linarith
    · rw [mul_div_cancel_left₀ _ hL.ne', show (2 : ℝ) * (boxLcm r * (r.box.radius i : ℝ)) /
          boxLcm r = 2 * r.box.radius i by field_simp]
      linarith

/-! ## The leaf -/

/-- A row validated against a shared fact row with polynomial data. -/
structure SharedPValid (r f : Row) (fp : FactPoly) : Prop where
  seg : r.seg = f.seg
  kind : r.kind = f.kind
  triple : r.triple = f.triple
  aff : r.aff = []
  faff : f.aff = []
  sub : r.SubBox f
  lam : 0 < f.hi 1 → 0 < r.hi 1
  radius : ∀ x ∈ r.radius, 0 ≤ x
  mpos : ∀ i < fp.m.length, 0 < fp.m.getD i 0 → 0 ≤ r.lo i
  cheap : cheapRow fp.S r = true

instance (r f : Row) (fp : FactPoly) : Decidable (SharedPValid r f fp) :=
  decidable_of_iff (r.seg = f.seg ∧ r.kind = f.kind ∧ r.triple = f.triple ∧ r.aff = [] ∧
      f.aff = [] ∧ r.SubBox f ∧ (0 < f.hi 1 → 0 < r.hi 1) ∧ (∀ x ∈ r.radius, 0 ≤ x) ∧
      (∀ i < fp.m.length, 0 < fp.m.getD i 0 → 0 ≤ r.lo i) ∧ cheapRow fp.S r = true)
    ⟨fun ⟨a, b, c, d, e, g, h, i, j, k⟩ => ⟨a, b, c, d, e, g, h, i, j, k⟩,
      fun ⟨a, b, c, d, e, g, h, i, j, k⟩ => ⟨a, b, c, d, e, g, h, i, j, k⟩⟩

theorem not_rupert_sharedP (r f : Row) (fp : FactPoly) (hf : f.KeyFacts) (hfp : fp.Ok f)
    (hv : SharedPValid r f fp) (p : AtlasPose ℝ) (offset : ℝ²)
    (y : ℕ → ℝ) (hc : Coords r.seg r.kind p (affY r.aff y)) (hmem : r.box.Mem y)
    (hε : 0 < y 0) (hρ : r.isTube = true → 0 < y 6) (hlam : 0 < r.hi 1 → 0 < y 1)
    (hscale : 1 ≤ viewScale 0 p) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hrad := r.radius_nonneg hv.radius
  refine r.not_rupert_sharedD f hf hv.seg hv.kind hv.triple hv.aff hv.faff hv.sub hv.lam
    p offset y hc hmem hε hρ hlam hscale ?_
  have hD : r.D = f.D := by
    unfold Row.D; rw [hv.seg, hv.kind, hv.triple, hv.aff, hv.faff]
  rw [hD, hfp.eval_D]
  have hK : (0 : ℝ) < fp.K := by exact_mod_cast hfp.1
  have hmono : 0 ≤ monoEval y fp.m := by
    apply monoEval_nonneg_of
    intro i hi
    have hlen : i < fp.m.length := by
      by_contra h
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : fp.m.length ≤ i)] at hi
    have hlo := hv.mpos i hlen hi
    have := abs_le.mp (hmem i)
    have hlo' : (0 : ℝ) ≤ (r.box.center i : ℝ) - r.box.radius i := by
      have : (0 : ℚ) ≤ r.box.center i - r.box.radius i := hlo
      exact_mod_cast this
    linarith [this.1]
  have hS := cheapRow_sound fp.S r hv.cheap hrad y hmem
  exact mul_nonneg hε.le (div_nonneg (mul_nonneg hmono hS) hK.le)

end Noperts.Stellated.CornerKernel
