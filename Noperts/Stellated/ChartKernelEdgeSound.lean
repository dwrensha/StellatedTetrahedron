module

public import Noperts.Stellated.ChartKernelEdge
public import Noperts.Stellated.PackedSlots

@[expose] public section

/-!
# Soundness of the integer projective edge-cycle checker

`validEdgeN_sound : validEdgeN box = true → box.Valid`.  Each integer quantity
is a fixed positive multiple of its rational counterpart: quadratics by
`1600` (vertices are scaled by `40`), supports by `1600 L`, Bernstein
coefficients by `4 E²` and the adjusted quadratic by `1600 L μ.den`.
-/

namespace Noperts.Stellated.ChartKernel

open Noperts.Checker AtlasProjectiveEdgeCertificate AtlasProjectiveView
open AtlasQuadratic

/-! ## Quadratics -/

def IQ.toQ (a : IQ) : RatQuadratic3 :=
  ⟨a.c0, a.cx, a.cy, a.cz, a.cxx, a.cxy, a.cxz, a.cyy, a.cyz, a.czz⟩

theorem IQ.toQ_add (a b : IQ) : (IQ.add a b).toQ = a.toQ + b.toQ := by
  simp only [IQ.add, IQ.toQ]; push_cast; rfl

theorem IQ.toQ_smul (k : ℤ) (a : IQ) : (IQ.smul k a).toQ = RatQuadratic3.scale k a.toQ := by
  simp only [IQ.smul, IQ.toQ, RatQuadratic3.scale]; push_cast; rfl

theorem IQ.toQ_sub (a b : IQ) : (IQ.sub a b).toQ = a.toQ - b.toQ := by
  simp only [IQ.sub, IQ.toQ_add, IQ.toQ_smul]
  cases a.toQ; cases b.toQ
  simp only [RatQuadratic3.scale]
  show RatQuadratic3.add _ _ = RatQuadratic3.add _ (RatQuadratic3.neg _)
  simp [RatQuadratic3.add, RatQuadratic3.neg]

theorem RatQuadratic3.ext' {a b : RatQuadratic3} (h0 : a.c0 = b.c0) (h1 : a.cx = b.cx)
    (h2 : a.cy = b.cy) (h3 : a.cz = b.cz) (h4 : a.cxx = b.cxx) (h5 : a.cxy = b.cxy)
    (h6 : a.cxz = b.cxz) (h7 : a.cyy = b.cyy) (h8 : a.cyz = b.cyz) (h9 : a.czz = b.czz) :
    a = b := by
  cases a; cases b; simp_all

/-! ## Vertices and Cayley quadratics -/

theorem vI_cast (k : VertexIndex) (c : Fin 3) :
    (vI k c : ℚ) = 40 * rationalVertex k c := by
  fin_cases k <;> fin_cases c <;> simp [vI, rationalVertex] <;> norm_num

theorem numI_toQ (c j : Fin 3) :
    (numI c j).toQ = Noperts.CayleyEdgeCertificate.numeratorQuadratic c j := by
  fin_cases c <;> fin_cases j <;>
    simp [numI, IQ.toQ, Noperts.CayleyEdgeCertificate.numeratorQuadratic,
      Noperts.CayleyEdgeCertificate.qOne,
      Noperts.CayleyEdgeCertificate.qx,
      Noperts.CayleyEdgeCertificate.qy,
      Noperts.CayleyEdgeCertificate.qz,
      Noperts.CayleyEdgeCertificate.qxx,
      Noperts.CayleyEdgeCertificate.qxy,
      Noperts.CayleyEdgeCertificate.qxz,
      Noperts.CayleyEdgeCertificate.qyy,
      Noperts.CayleyEdgeCertificate.qyz,
      Noperts.CayleyEdgeCertificate.qzz, RatQuadratic3.scale] <;>
    (apply RatQuadratic3.ext' <;> simp)

theorem denomI_toQ : denomI.toQ = Noperts.CayleyEdgeCertificate.denomQuadratic := by
  simp [denomI, IQ.toQ, Noperts.CayleyEdgeCertificate.denomQuadratic,
    Noperts.CayleyEdgeCertificate.qOne,
    Noperts.CayleyEdgeCertificate.qxx,
    Noperts.CayleyEdgeCertificate.qyy,
    Noperts.CayleyEdgeCertificate.qzz]
  apply RatQuadratic3.ext' <;> simp

theorem chartSignI_cast (chart : CayleyAtlas.ChartIndex) (c : Fin 3) :
    (chartSignI chart c : ℚ) = chartSign chart c := by
  simp only [chartSignI, chartSign]; split_ifs <;> simp

theorem dispI_toQ (chart : CayleyAtlas.ChartIndex) (inner outer : VertexIndex) (c : Fin 3) :
    (dispI chart inner outer c).toQ =
      RatQuadratic3.scale 40 (displacementQuadratic chart inner outer c) := by
  have h := fun j => numI_toQ c j
  simp only [dispI, IQ.toQ_sub, IQ.toQ_add, IQ.toQ_smul, displacementQuadratic, sum3Q,
    numeratorQuadratic, denomI_toQ]
  apply RatQuadratic3.ext' <;>
    simp [← h, IQ.toQ, vI_cast, chartSignI_cast] <;> ring

theorem contactI_toQ (chart : CayleyAtlas.ChartIndex) (start finish inner : VertexIndex)
    (c : Fin 3) :
    (contactI chart start finish inner c).toQ =
      RatQuadratic3.scale 1600 (contactQuadratic chart start finish inner c) := by
  have hd := fun c => dispI_toQ chart inner start c
  fin_cases c <;>
    simp only [contactI, IQ.toQ_sub, IQ.toQ_smul, contactQuadratic, hd, edgeQ] <;>
    (apply RatQuadratic3.ext' <;>
      simp [vI_cast, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring)

theorem contactFast_eq (chart : CayleyAtlas.ChartIndex) (start finish inner : VertexIndex)
    (c : Fin 3) : contactFast chart start finish inner c = contactI chart start finish inner c := by
  fin_cases c <;>
    simp only [contactFast, contactI, dispI, IQ.sub, IQ.add, IQ.smul, numI, denomI, IQ.mk.injEq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-! ## Totals and the adjusted quadratic -/

theorem toQ_foldr {α : Type} (g : α → IQ) (l : List α) :
    (l.foldr (fun i acc => IQ.add (g i) acc) IQ.zero).toQ =
      l.foldr (fun i acc => (g i).toQ + acc) 0 := by
  induction l with
  | nil => simp [IQ.zero, IQ.toQ]; rfl
  | cons a l ih => simp only [List.foldr_cons, IQ.toQ_add, ih]

theorem foldr_field {n : ℕ} (f : Fin n → RatQuadratic3) (pr : RatQuadratic3 → ℚ)
    (hadd : ∀ a b, pr (a + b) = pr a + pr b) (h0 : pr 0 = 0) :
    pr ((List.finRange n).foldr (fun i acc => f i + acc) 0) = ∑ i, pr (f i) := by
  rw [Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp [h0]
  | cons a l ih => simp only [List.foldr_cons, hadd, ih, List.map_cons, List.sum_cons]

theorem foldr_eq_sum {n : ℕ} (f : Fin n → RatQuadratic3) :
    (List.finRange n).foldr (fun i acc => f i + acc) 0 =
      ⟨∑ i, (f i).c0, ∑ i, (f i).cx, ∑ i, (f i).cy, ∑ i, (f i).cz, ∑ i, (f i).cxx,
        ∑ i, (f i).cxy, ∑ i, (f i).cxz, ∑ i, (f i).cyy, ∑ i, (f i).cyz, ∑ i, (f i).czz⟩ := by
  apply RatQuadratic3.ext'
  · exact foldr_field f (·.c0) (fun a b => by simp) rfl
  · exact foldr_field f (·.cx) (fun a b => by simp) rfl
  · exact foldr_field f (·.cy) (fun a b => by simp) rfl
  · exact foldr_field f (·.cz) (fun a b => by simp) rfl
  · exact foldr_field f (·.cxx) (fun a b => by simp) rfl
  · exact foldr_field f (·.cxy) (fun a b => by simp) rfl
  · exact foldr_field f (·.cxz) (fun a b => by simp) rfl
  · exact foldr_field f (·.cyy) (fun a b => by simp) rfl
  · exact foldr_field f (·.cyz) (fun a b => by simp) rfl
  · exact foldr_field f (·.czz) (fun a b => by simp) rfl

theorem totalI_toQ (box : Box) (c : Fin 3) :
    (totalI box c).toQ = RatQuadratic3.scale 1600 (box.edgeShell.totalQuadratic c) := by
  unfold totalI
  rw [toQ_foldr]
  simp only [contactFast_eq, contactI_toQ]
  rw [foldr_eq_sum]
  apply RatQuadratic3.ext' <;>
    simp [AtlasEdgeCertificate.Box.totalQuadratic, AtlasEdgeCertificate.Box.contactQuadratic,
      Finset.mul_sum] <;> rfl

theorem qScale_cast (L : ℕ) (q : ℚ) (h : q.den ∣ L) : (qScale L q : ℚ) = L * q := by
  obtain ⟨m, rfl⟩ := h
  simp only [qScale, Nat.mul_div_cancel_left m q.den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num q]
  ring

theorem dvd_lcmList (qs : List ℚ) (q : ℚ) (h : q ∈ qs) : q.den ∣ lcmList qs := by
  induction qs with
  | nil => simp at h
  | cons a l ih =>
      simp only [lcmList, List.foldr_cons] at ih ⊢
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.dvd_lcm_left _ _
      · exact (ih h).trans (Nat.dvd_lcm_right _ _)

theorem lcmList_pos (qs : List ℚ) : 0 < lcmList qs := by
  induction qs with
  | nil => simp [lcmList]
  | cons a l ih => exact Nat.lcm_pos a.den_pos ih

theorem T_cast (box : Box) (j c : Fin 3) : (T box j c : ℚ) = triL box * box.triangle j c :=
  qScale_cast _ _ (dvd_lcmList _ _ (by
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨j, c, rfl⟩))

theorem lo_cast (box : Box) (c : Fin 3) :
    (lo box c : ℚ) = boxE box * box.interval.min.get ⟨c.val + 2, by omega⟩ :=
  qScale_cast _ _ (dvd_lcmList _ _ (by
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons]
    exact ⟨c, Or.inl rfl⟩))

theorem hi_cast (box : Box) (c : Fin 3) :
    (hi box c : ℚ) = boxE box * box.interval.max.get ⟨c.val + 2, by omega⟩ :=
  qScale_cast _ _ (dvd_lcmList _ _ (by
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons]
    exact ⟨c, Or.inr (Or.inl rfl)⟩))

theorem adjI_toQ (box : Box) (j : Fin 3) :
    (adjI box j).toQ = RatQuadratic3.scale (1600 * triL box * (box.ballMultiplier j).den)
      (box.adjustedQuadratic j) := by
  have hμ := Rat.mul_den_eq_num (box.ballMultiplier j)
  simp only [adjI, IQ.toQ_add, IQ.toQ_smul, totalI_toQ, Box.adjustedQuadratic,
    Box.viewQuadratic, T_cast, cayleyConstraintQuadratic]
  apply RatQuadratic3.ext' <;> simp [IQ.toQ] <;> first | ring1 | (rw [← hμ]; ring1)

/-! ## Bernstein coefficients -/

theorem edgeShell_interval (box : Box) : box.edgeShell.interval = box.interval := rfl

set_option maxHeartbeats 2000000 in
theorem bernI_cast (box : Box) (q : IQ) (i j k : Fin 3) :
    (bernI box q i.val j.val k.val : ℚ) = 4 * (boxE box : ℚ) ^ 2 *
      QuadraticBernstein.coefficient box.edgeShell.variableBalls q.toQ i j k := by
  have hE : (boxE box : ℚ) ≠ 0 := by
    have := lcmList_pos ((List.finRange 3).flatMap fun c =>
      [box.interval.min.get ⟨c.val + 2, by omega⟩, box.interval.max.get ⟨c.val + 2, by omega⟩])
    exact_mod_cast this.ne'
  have l0 : (lo box 0 : ℚ) = boxE box * box.interval.min.get 2 := lo_cast box 0
  have l1 : (lo box 1 : ℚ) = boxE box * box.interval.min.get 3 := lo_cast box 1
  have l2 : (lo box 2 : ℚ) = boxE box * box.interval.min.get 4 := lo_cast box 2
  have h0 : (hi box 0 : ℚ) = boxE box * box.interval.max.get 2 := hi_cast box 0
  have h1 : (hi box 1 : ℚ) = boxE box * box.interval.max.get 3 := hi_cast box 1
  have h2 : (hi box 2 : ℚ) = boxE box * box.interval.max.get 4 := hi_cast box 2
  have two : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [bernI, QuadraticBernstein.coefficient, AtlasEdgeCertificate.Box.variableBalls,
    AtlasInterval.coordinateBall, RatBall.ofEndpoints, RatQuadratic3.evalQ, IQ.toQ,
    edgeShell_interval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  simp only [l0, l1, l2, h0, h1, h2, Fin.ext_iff, two]
  split_ifs with g1 g2 g3 <;>
    (try rw [show ((i : ℕ) : ℚ) = 2 by exact_mod_cast g1]) <;>
    (try rw [show ((j : ℕ) : ℚ) = 2 by exact_mod_cast g2]) <;>
    (try rw [show ((k : ℕ) : ℚ) = 2 by exact_mod_cast g3]) <;>
    field_simp <;> ring

/-! ## Supports -/

theorem edgeShell_outerIndex (box : Box) : box.edgeShell.outerIndex = box.outerIndex := rfl

theorem supportI_cast (box : Box) (i : Fin (box.edgePred + 1)) (j : Fin 3) (k : VertexIndex) :
    (supportI box i j k : ℚ) = 1600 * triL box * box.supportAt j i k := by
  simp only [supportI, mI, Box.supportAt, dotQ, AtlasEdgeCertificate.crossQ,
    AtlasEdgeCertificate.Box.edgeQ,
    AtlasEdgeCertificate.Box.deltaQ, AtlasQuadratic.edgeQ, Pi.sub_apply]
  push_cast
  simp only [vI_cast, T_cast,
    edgeShell_outerIndex]
  ring

/-! ## Assembly -/

theorem le_foldr_max {α : Type} (f : α → ℤ) (init : ℤ) :
    ∀ (l : List α) (a : α), a ∈ l → f a ≤ l.foldr (fun k acc => max (f k) acc) init
  | [], _, h => by simp at h
  | b :: l, a, h => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (le_foldr_max f init l a h).trans (le_max_right _ _)

theorem foldr_add_cast {n : ℕ} (f : Fin n → ℤ) :
    (((List.finRange n).foldr (fun i acc => f i + acc) 0 : ℤ) : ℚ) = ∑ i, (f i : ℚ) := by
  rw [Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, Int.cast_add, ih, List.map_cons, List.sum_cons]

theorem rootSign_num_cast (root : Fin 8) (c : Fin 3) :
    ((rootSign root c).num : ℚ) = rootSign root c := by
  fin_cases root <;> fin_cases c <;> rfl

theorem supportMaxI_cast (box : Box) (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    (supportMaxI box i k : ℚ) = 1600 * triL box * max3 fun j => box.supportAt j i k := by
  have hL : (0 : ℚ) ≤ 1600 * triL box := by positivity
  simp only [supportMaxI, max3I, max3, Int.cast_max, supportI_cast]
  rw [mul_max_of_nonneg _ _ hL, mul_max_of_nonneg _ _ hL]

theorem defect_le (box : Box) (hL : 0 < triL box) (i : Fin (box.edgePred + 1)) :
    box.defect i ≤ (defectI box i : ℚ) / (1600 * triL box) + AtlasEdgeCertificate.supportError := by
  have hLq : (0 : ℚ) < 1600 * triL box := by positivity
  unfold Box.defect
  apply Finset.max'_le
  intro y hy
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
  unfold Box.supportUpper
  have hk := le_foldr_max (supportMaxI box i) (supportMaxI box i 0) (List.finRange 8) k
    (List.mem_finRange k)
  have hkq : (supportMaxI box i k : ℚ) ≤ defectI box i := by exact_mod_cast hk
  rw [supportMaxI_cast] at hkq
  have : (max3 fun j => box.supportAt j i k) ≤ (defectI box i : ℚ) / (1600 * triL box) := by
    rw [le_div_iff₀ hLq]; linarith
  linarith

theorem dBound_eq (box : Box) :
    box.edgeShell.dBound = (dBoundNum box : ℚ) / (boxE box : ℚ) ^ 2 := by
  have hE : (boxE box : ℚ) ≠ 0 := by
    have := lcmList_pos ((List.finRange 3).flatMap fun c =>
      [box.interval.min.get ⟨c.val + 2, by omega⟩, box.interval.max.get ⟨c.val + 2, by omega⟩])
    exact_mod_cast this.ne'
  have hEp : (0 : ℚ) < boxE box := lt_of_le_of_ne (by positivity) hE.symm
  have e : ∀ c : Fin 3, (max |(lo box c : ℚ)| |(hi box c : ℚ)|) =
      boxE box * AtlasEdgeCertificate.endpointAbsBound
        (box.interval.min.get ⟨c.val + 2, by omega⟩) (box.interval.max.get ⟨c.val + 2, by omega⟩) := by
    intro c
    rw [lo_cast, hi_cast, AtlasEdgeCertificate.endpointAbsBound, abs_mul, abs_mul,
      abs_of_pos hEp, mul_max_of_nonneg _ _ hEp.le]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp only [dBoundNum, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr]
  simp only [AtlasEdgeCertificate.Box.dBound, edgeShell_interval]
  push_cast
  simp only [] at e0 e1 e2
  rw [e0, e1, e2]
  field_simp
  simp only [AtlasPose.get] at *
  simp only [AtlasPose.equivPi, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add,
    Fin.reduceFinMk, Equiv.coe_fn_mk, Matrix.cons_val, Nat.one_mod, Nat.reduceAdd, Nat.mod_succ,
    add_zero]
  ring

theorem foldr_min_le {α : Type} (f : α → ℤ) (init : ℤ) :
    ∀ (l : List α) (a : α), a ∈ l → foldMin f init l ≤ f a
  | [], _, h => by simp at h
  | b :: l, a, h => by
      simp only [foldMin, List.foldr_cons] at *
      rcases List.mem_cons.mp h with rfl | h
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (foldr_min_le f init l a h)

theorem bernMinI_le (box : Box) (q : IQ) (i j k : Fin 3) :
    bernMinI box q ≤ bernI box q i.val j.val k.val := by
  have hm : (i.val, j.val, k.val) ∈ triples27 := by
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    obtain ⟨k, hk⟩ := k
    simp only [triples27]
    interval_cases i <;> interval_cases j <;> interval_cases k <;> decide
  have h2 := foldr_min_le (fun t => bernI box q t.1 t.2.1 t.2.2) (bernI box q 0 0 0) triples27 _ hm
  exact h2

theorem le_lower (vars : Fin 3 → RatBall) (q : RatQuadratic3) (c : ℚ)
    (h : ∀ i j k, c ≤ QuadraticBernstein.coefficient vars q i j k) :
    c ≤ QuadraticBernstein.lower vars q := by
  simp only [QuadraticBernstein.lower, QuadraticBernstein.min3, le_min_iff]
  and_intros <;> exact h _ _ _

/-- The signed-triangle condition from the integer triangle rows. -/
theorem signedTriangle_of_T (box : Box) (hL : 0 < (triL box : ℤ))
    (htri : ∀ i : Fin 3, (∀ c : Fin 3, 0 ≤ (rootSign box.root c).num * T box i c) ∧
      (rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = triL box) :
    SignedTriangleValid box.root box.triangle := by
  have hLq : (0 : ℚ) < triL box := by exact_mod_cast hL
  intro i
  obtain ⟨hnn, hsum⟩ := htri i
  have hsumq : ((rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
      (rootSign box.root 2).num * T box i 2 : ℚ) = triL box := by exact_mod_cast hsum
  simp only [rootSign_num_cast, T_cast] at hsumq
  refine ⟨fun c => ?_, ?_⟩
  · have := hnn c
    have hq : (0 : ℚ) ≤ (rootSign box.root c).num * T box i c := by exact_mod_cast this
    rw [rootSign_num_cast, T_cast] at hq
    have : (0 : ℚ) ≤ (triL box : ℚ) * (rootSign box.root c * box.triangle i c) := by
      have e : rootSign box.root c * ((triL box : ℚ) * box.triangle i c) =
          (triL box : ℚ) * (rootSign box.root c * box.triangle i c) := by ring
      rw [← e]; exact hq
    exact (mul_nonneg_iff_of_pos_left hLq).mp this
  · rw [Fin.sum_univ_three]
    have : (triL box : ℚ) * (rootSign box.root 0 * box.triangle i 0 +
        rootSign box.root 1 * box.triangle i 1 + rootSign box.root 2 * box.triangle i 2) =
        triL box * 1 := by linear_combination hsumq
    exact mul_left_cancel₀ hLq.ne' this

/-- `box.Valid` from integer facts: any upper bound `TD` on the integer total
defect and per-coefficient Bernstein bounds. -/
theorem valid_of_facts (box : Box) (TD : ℤ) (hL : 0 < (triL box : ℤ)) (hE : 0 < boxE box)
    (htri : ∀ i : Fin 3, (∀ c : Fin 3, 0 ≤ (rootSign box.root c).num * T box i c) ∧
      (rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = triL box)
    (hμ : ∀ j : Fin 3, 0 ≤ (box.ballMultiplier j).num)
    (hdir : ∀ i : Fin (box.edgePred + 1),
      supportMaxI box i (box.nonzeroWitness i) * 10 ^ 10 + 16000 * triL box < 0)
    (hTDge : totalDefectI box ≤ TD)
    (hbern : ∀ j a b c : Fin 3, dBoundNum box * (TD * 10 ^ 10 + 32000 * (box.edgePred + 1) *
      triL box) * 4 * (box.ballMultiplier j).den ≤
        bernI box (adjI box j) a.val b.val c.val * 10 ^ 10) : box.Valid := by
  have hLq : (0 : ℚ) < triL box := by exact_mod_cast hL
  have hEq : (0 : ℚ) < boxE box := by exact_mod_cast hE
  have hP : (0 : ℚ) < 10 ^ 10 := by norm_num
  have sE : AtlasEdgeCertificate.supportError = 10 / 10 ^ 10 := by
    simp [AtlasEdgeCertificate.supportError, RationalApprox.κℚ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact signedTriangle_of_T box hL htri
  · -- direction witnesses
    intro i
    have hi := hdir i
    have hq : (supportMaxI box i (box.nonzeroWitness i) : ℚ) * 10 ^ 10 + 16000 * triL box < 0 := by
      exact_mod_cast hi
    rw [supportMaxI_cast] at hq
    unfold Box.supportUpper
    rw [sE]
    have e : ((max3 fun j => box.supportAt j i (box.nonzeroWitness i)) + 10 / 10 ^ 10) *
        (1600 * triL box * 10 ^ 10) =
        1600 * (triL box : ℚ) * (max3 fun j => box.supportAt j i (box.nonzeroWitness i)) *
          10 ^ 10 + 16000 * triL box := by ring
    have hneg : ((max3 fun j => box.supportAt j i (box.nonzeroWitness i)) + 10 / 10 ^ 10) *
        (1600 * triL box * 10 ^ 10) < 0 := by rw [e]; exact hq
    exact neg_of_mul_neg_left hneg (by positivity)
  · intro j
    have := hμ j
    exact Rat.num_nonneg.mp this
  · -- displacement
    set L : ℚ := (triL box : ℚ) with hLdef
    set E : ℚ := (boxE box : ℚ) with hEdef
    set n : ℚ := (box.edgePred : ℚ) + 1 with hndef
    have hn : (0 : ℚ) < n := by positivity
    have hLn : 0 < triL box := by exact_mod_cast hL
    have hκ : RationalApprox.κℚ = 1 / 10 ^ 10 := by simp [RationalApprox.κℚ]
    -- the defect
    have hTDq : (totalDefectI box : ℚ) ≤ TD := by exact_mod_cast hTDge
    have hTD' : box.totalDefect ≤ (totalDefectI box : ℚ) / (1600 * L) + n * (10 / 10 ^ 10) := by
      unfold Box.totalDefect
      have hsum : ((totalDefectI box : ℤ) : ℚ) = ∑ i, (defectI box i : ℚ) := by
        unfold totalDefectI; exact foldr_add_cast _
      calc ∑ i, box.defect i ≤ ∑ i, ((defectI box i : ℚ) / (1600 * L) + 10 / 10 ^ 10) :=
            Finset.sum_le_sum fun i _ => by rw [← sE]; exact defect_le box hLn i
        _ = (totalDefectI box : ℚ) / (1600 * L) + n * (10 / 10 ^ 10) := by
            rw [Finset.sum_add_distrib, hsum, Finset.sum_div, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
    have hTD : box.totalDefect ≤ (TD : ℚ) / (1600 * L) + n * (10 / 10 ^ 10) := by
      have : (totalDefectI box : ℚ) / (1600 * L) ≤ (TD : ℚ) / (1600 * L) :=
        div_le_div_of_nonneg_right hTDq (by positivity)
      linarith
    have hdB := dBound_eq box
    set DN : ℚ := (dBoundNum box : ℚ) with hDN
    have hDNnn : 0 ≤ DN := by
      have : 0 ≤ dBoundNum box := by
        unfold dBoundNum
        have : 0 ≤ (List.finRange 3).foldr (fun c a => max |lo box c| |hi box c| ^ 2 + a) (0 : ℤ) := by
          induction (List.finRange 3) with
          | nil => simp
          | cons a l ih => simp only [List.foldr_cons]; positivity
        positivity
      rw [hDN]; exact_mod_cast this
    have hdB0 : 0 ≤ box.edgeShell.dBound := by rw [hdB]; positivity
    -- reduce to each corner
    unfold Box.adjustedDisplacementLower min3
    have corner : ∀ j : Fin 3, box.edgeShell.dBound * box.totalDefect +
        box.edgeShell.displacementError ≤ box.adjustedDisplacementCornerLower j := by
      intro j
      set μd : ℚ := ((box.ballMultiplier j).den : ℚ) with hμd
      have hμd0 : 0 < μd := by positivity
      set S : ℚ := 1600 * L * μd with hS
      have hS0 : 0 < S := by positivity
      set BM : ℚ := ((dBoundNum box * (TD * 10 ^ 10 + 32000 * (box.edgePred + 1) * triL box) * 4 *
        (box.ballMultiplier j).den : ℤ) : ℚ) / 10 ^ 10 with hBM
      -- Bernstein: BM / (4 E² S) ≤ lower
      have hlow : BM / (4 * E ^ 2 * S) ≤
          QuadraticBernstein.lower box.edgeShell.variableBalls (box.adjustedQuadratic j) := by
        apply le_lower
        intro a b c
        have h1 := hbern j a b c
        have h2 := bernI_cast box (adjI box j) a b c
        rw [adjI_toQ, QuadraticBernstein.coefficient_scale] at h2
        have h1q : BM ≤ (bernI box (adjI box j) a.val b.val c.val : ℚ) := by
          rw [hBM, div_le_iff₀ (by norm_num)]
          exact_mod_cast h1
        rw [h2] at h1q
        rw [div_le_iff₀ (by positivity)]
        have : 4 * E ^ 2 * (1600 * L * μd * QuadraticBernstein.coefficient
            box.edgeShell.variableBalls (box.adjustedQuadratic j) a b c) =
            QuadraticBernstein.coefficient box.edgeShell.variableBalls (box.adjustedQuadratic j)
              a b c * (4 * E ^ 2 * S) := by rw [hS]; ring
        linarith
      have hcl : QuadraticBernstein.lower box.edgeShell.variableBalls (box.adjustedQuadratic j) ≤
          box.adjustedDisplacementCornerLower j := le_max_right _ _
      -- the integer inequality
      have hintq : DN * ((TD : ℚ) * 10 ^ 10 + 32000 * n * L) * 4 * μd ≤
          BM * 10 ^ 10 := by
        rw [hBM, div_mul_cancel₀ _ (by norm_num), hDN, hμd, hndef, hLdef]
        push_cast
        rfl
      have hErr : box.edgeShell.displacementError = n * 10 * box.edgeShell.dBound * (1 / 10 ^ 10) := by
        rw [hndef]
        simp only [AtlasEdgeCertificate.Box.displacementError, hκ]
        rfl
      refine le_trans ?_ (hlow.trans hcl)
      rw [hErr]
      calc box.edgeShell.dBound * box.totalDefect + n * 10 * box.edgeShell.dBound * (1 / 10 ^ 10)
          ≤ box.edgeShell.dBound * ((TD : ℚ) / (1600 * L) + n * (10 / 10 ^ 10)) +
              n * 10 * box.edgeShell.dBound * (1 / 10 ^ 10) := by
            have := mul_le_mul_of_nonneg_left hTD hdB0
            linarith
        _ = DN * ((TD : ℚ) * 10 ^ 10 + 32000 * n * L) * 4 * μd /
              (4 * E ^ 2 * S * 10 ^ 10) := by
            rw [hdB, hS]; field_simp; ring
        _ ≤ BM * 10 ^ 10 / (4 * E ^ 2 * S * 10 ^ 10) :=
            div_le_div_of_nonneg_right hintq (by positivity)
        _ = BM / (4 * E ^ 2 * S) := by field_simp
    exact le_min (corner 0) (le_min (corner 1) (corner 2))

theorem validEdgeN_sound (box : Box) (h : validEdgeN box = true) : box.Valid := by
  simp only [validEdgeN, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨⟨hL, hE⟩, htri⟩, hμ⟩, hdir⟩, hdisp⟩ := h
  exact valid_of_facts box (totalDefectI box) hL hE htri hμ hdir le_rfl fun j a b c =>
    (hdisp j).trans (Int.mul_le_mul_of_nonneg_right (bernMinI_le box (adjI box j) a b c)
      (by norm_num))

end Noperts.Stellated.ChartKernel

/-! ## The packed Bernstein vectors -/

namespace Noperts.Stellated.ChartKernel
open PackedSlots

/-- Entry `i` of a triple. -/
def sel3 (f : ℕ × ℕ × ℕ) (i : ℕ) : ℕ := if i = 0 then f.1 else if i = 1 then f.2.1 else f.2.2

theorem vec27_eq (w : ℕ) (f g h : ℕ × ℕ × ℕ) :
    vec27 (2 ^ w) f g h =
      packW w (fun t => sel3 f (t / 9) * sel3 g (t / 3 % 3) * sel3 h (t % 3)) 27 := by
  rw [packW_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, vec27, tri3, sel3]
  norm_num
  ring

end Noperts.Stellated.ChartKernel

namespace Noperts.Stellated.ChartKernel
open PackedSlots AtlasProjectiveEdgeCertificate

/-- The basis pattern `p` at slot `t`. -/
def betaK (p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) (t : ℕ) : ℤ :=
  if t < 27 then (sel3 p.1 (t / 9) * sel3 p.2.1 (t / 3 % 3) * sel3 p.2.2 (t % 3) : ℕ) else 0

theorem basis_rep (p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) (hp : p ∈ basisTriples) :
    PRep KW 27 (vec27 (2 ^ KW) p.1 p.2.1 p.2.2, 0) (betaK p) 4 := by
  rw [vec27_eq]
  refine (PRep.ofNat KW 27 _ 4 ?_).congr fun t => rfl
  simp only [basisTriples, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The slot values of `bernPairK`. -/
def bernSlot (l : List (ℤ × ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)))) (t : ℕ) : ℤ :=
  l.foldr (fun p a => p.1 * betaK p.2 t + a) 0

theorem bernPair_rep : ∀ l : List (ℤ × ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ))),
    (∀ p ∈ l, p.2 ∈ basisTriples) →
    PRep KW 27 (l.foldr (fun p acc =>
      pairAdd (pairSmul p.1 (vec27 (2 ^ KW) p.2.1 p.2.2.1 p.2.2.2, 0)) acc) (0, 0))
      (bernSlot l) (l.foldr (fun p a => p.1.natAbs * 4 + a) 0)
  | [], _ => (PRep.zero KW 27).congr fun t => rfl
  | p :: l, h => by
      have ih := bernPair_rep l fun q hq => h q (List.mem_cons_of_mem _ hq)
      have hb := (basis_rep p.2 (h p List.mem_cons_self)).smul p.1
      exact (hb.add ih).congr fun t => rfl

theorem boundK_zip (cs : List ℤ) :
    (cs.zip basisTriples).foldr (fun p a => p.1.natAbs * 4 + a) 0 ≤ boundK cs := by
  unfold boundK
  generalize basisTriples = bs
  induction cs generalizing bs with
  | nil => simp
  | cons c cs ih =>
      cases bs with
      | nil => simp
      | cons b bs => simp only [List.zip_cons_cons, List.foldr_cons]; have := ih bs; omega

theorem bernPairK_eq (cs : List ℤ) : bernPairK cs = (cs.zip basisTriples).foldr (fun p acc =>
      pairAdd (pairSmul p.1 (vec27 (2 ^ KW) p.2.1 p.2.2.1 p.2.2.2, 0)) acc) (0, 0) := by
  simp only [bernPairK, basisVecsL_eq, basisVecs, List.zip_map_right, List.foldr_map, Prod.map]
  rfl

theorem bernPairK_rep (cs : List ℤ) :
    PRep KW 27 (bernPairK cs) (bernSlot (cs.zip basisTriples)) (boundK cs) :=
  bernPairK_eq cs ▸ (bernPair_rep _ fun _ hp => (List.of_mem_zip hp).2).mono (boundK_zip cs)

set_option maxHeartbeats 4000000 in
theorem bernSlot_eq (box : Box) (q : IQ) (i j k : Fin 3) :
    bernSlot ((bernWeights box q).zip basisTriples) (9 * i.val + 3 * j.val + k.val) =
      bernI box q i.val j.val k.val := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [bernSlot, bernWeights, basisTriples, betaK, sel3, bernI] <;> ring

end Noperts.Stellated.ChartKernel

namespace Noperts.Stellated.ChartKernel
open PackedSlots AtlasProjectiveEdgeCertificate

theorem kron_3_8 (w : ℕ) (a b : ℕ → ℕ) :
    packW (w * 8) a 3 * packW w b 8 = packW w (fun t => a (t / 8) * b (t % 8)) 24 := by
  simp only [packW_eq_sum, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

end Noperts.Stellated.ChartKernel

namespace Noperts.Stellated.ChartKernel
open PackedSlots AtlasProjectiveEdgeCertificate

theorem testGe_sound {n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep KW n U d M)
    {th : ℤ} (hb : 4 * (M + th.natAbs) < 2 ^ (KW - 1)) {p : ℕ → Bool}
    (h : testGe U n p th = true) : ∀ t < n, p t = true → th ≤ d t := by
  simp only [testGe, testGeM, onesL_eq, onesK, maskK, beq_iff_eq] at h
  exact hU.ge_of_testP (by decide) th hb p h

theorem testGeM_sound {n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep KW n U d M)
    {th : ℤ} (hb : 4 * (M + th.natAbs) < 2 ^ (KW - 1)) {p : ℕ → Bool}
    (h : testGeM U n (maskK p n) th = true) : ∀ t < n, p t = true → th ≤ d t :=
  testGe_sound hU hb h

/-- The packed product of a stride-8 3-vector and an 8-vector. -/
theorem pairMul_rep {A B : ℕ × ℕ} {f g : ℕ → ℤ} {Ma Mb : ℕ} (hA : PRep (KW * 8) 3 A f Ma)
    (hB : PRep KW 8 B g Mb) :
    PRep KW 24 (pairMul A B) (fun t => f (t / 8) * g (t % 8)) (2 * Ma * Mb) := by
  obtain ⟨a, b, rfl, hf, hMa⟩ := hA
  obtain ⟨a', b', rfl, hg, hMb⟩ := hB
  refine ⟨fun t => a (t / 8) * a' (t % 8) + b (t / 8) * b' (t % 8),
    fun t => a (t / 8) * b' (t % 8) + b (t / 8) * a' (t % 8), ?_, fun t => ?_, fun t => ?_⟩
  · simp only [pairMul, kron_3_8, ← packW_add]
  · push_cast
    rw [← hf, ← hg]; ring
  · have h1 := hMa (t / 8)
    have h2 := hMb (t % 8)
    have e1 := Nat.mul_le_mul h1.1 h2.1
    have e2 := Nat.mul_le_mul h1.2 h2.2
    have e3 := Nat.mul_le_mul h1.1 h2.2
    have e4 := Nat.mul_le_mul h1.2 h2.1
    have e : 2 * Ma * Mb = Ma * Mb + Ma * Mb := by ring
    rw [e]
    exact ⟨Nat.add_le_add e1 e2, Nat.add_le_add e3 e4⟩

/-- A sign-split packed vector. -/
theorem pmPack_rep (w n : ℕ) (f : ℕ → ℤ) (M : ℕ) (hf : ∀ t, (f t).natAbs ≤ M) :
    PRep w n (pmPack w n f) f M :=
  ⟨fun t => (f t).toNat, fun t => (-f t).toNat, rfl, fun t => by simp only; omega,
    fun t => ⟨by simp only; have := hf t; omega, by simp only; have := hf t; omega⟩⟩

theorem getD_ofFn {α : Type} {n : ℕ} (g : Fin n → α) (k : Fin n) (d : α) :
    (List.ofFn g).getD k.val d = g k := by
  simp [List.getD_eq_getElem?_getD]

theorem deltaT_eq (s : VertexIndex) (d : Fin 3) : deltaT s d = pmPack KW 8 (δN s d) := by
  simp only [deltaT, deltaTabL_eq, deltaTab, getD_ofFn]

theorem edgeT_eq (s f : VertexIndex) (d : Fin 3) : edgeT s f d = vI s d - vI f d := by
  simp only [edgeT, edgeTab, getD_ofFn]

theorem maskT_eq (w : VertexIndex) : maskT w = maskK (fun t => t % 8 == w.val) 24 := by
  simp only [maskT, maskTabL_eq, maskTab, getD_ofFn]

theorem contactT_eq (ch : CayleyAtlas.ChartIndex) (s f u : VertexIndex) (c : Fin 3) :
    contactT ch s f u c = contactFast ch s f u c := by
  simp only [contactT, contactTab, getD_ofFn]

theorem totalT_eq (box : Box) (c : Fin 3) : totalT box c = totalI box c := by
  simp only [totalT, totalI, contactT_eq]

theorem δN_le (s : VertexIndex) (d : Fin 3) (k : ℕ) : (δN s d k).natAbs ≤ 40 := by
  unfold δN
  split_ifs with hk
  · revert hk k; revert s d; decide
  · simp

theorem edge_le (s f : VertexIndex) (d : Fin 3) : (vI s d - vI f d).natAbs ≤ 40 := by
  revert s f d; decide

theorem le_sum9 (f : Fin 3 → Fin 3 → ℕ) (j c : Fin 3) :
    f j c ≤ f 0 0 + f 0 1 + f 0 2 + f 1 0 + f 1 1 + f 1 2 + f 2 0 + f 2 1 + f 2 2 := by
  fin_cases j <;> fin_cases c <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

theorem T_le_tBound (box : Box) (j c : Fin 3) : (T box j c).natAbs ≤ tBound box :=
  le_sum9 (fun j c => (T box j c).natAbs) j c

theorem tN_le (box : Box) (c : Fin 3) (j : ℕ) : (tN box c j).natAbs ≤ tBound box := by
  unfold tN
  split_ifs with hj
  · exact T_le_tBound box ⟨j, hj⟩ c
  · simp

theorem mPackT_rep (box : Box) (i : Fin (box.edgePred + 1)) (d : Fin 3) :
    PRep (KW * 8) 3 (mPackT box i d)
      (fun j => edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 2) *
          tN box (d + 1) j +
        -edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 1) *
          tN box (d + 2) j) (80 * tBound box) := by
  have r := ((pmPack_rep (KW * 8) 3 (tN box (d + 1)) _ (tN_le box _)).smul
    (edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 2))).add
    ((pmPack_rep (KW * 8) 3 (tN box (d + 2)) _ (tN_le box _)).smul
    (-edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 1)))
  refine r.mono ?_
  rw [edgeT_eq, edgeT_eq, Int.natAbs_neg]
  have h1 := edge_le (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 2)
  have h2 := edge_le (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 1)
  have := Nat.mul_le_mul_right (tBound box) h1
  have := Nat.mul_le_mul_right (tBound box) h2
  omega

/-- The slot values of `supportPackK`. -/
def supSlot (box : Box) (i : Fin (box.edgePred + 1)) (t : ℕ) : ℤ :=
  ∑ d : Fin 3,
    (edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 2) *
        tN box (d + 1) (t / 8) +
      -edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 1) *
        tN box (d + 2) (t / 8)) * δN (box.outerIndex i) d (t % 8)

theorem supportPackK_rep (box : Box) (i : Fin (box.edgePred + 1)) :
    PRep KW 24 (supportPackK box i) (supSlot box i) (19200 * tBound box) := by
  have hd : ∀ d : Fin 3, PRep KW 8 (deltaT (box.outerIndex i) d) (δN (box.outerIndex i) d) 40 :=
    fun d => by rw [deltaT_eq]; exact pmPack_rep KW 8 _ 40 (δN_le _ d)
  have r : ∀ d : Fin 3, PRep KW 24 (pairMul (mPackT box i d) (deltaT (box.outerIndex i) d))
      (fun t => (edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 2) *
          tN box (d + 1) (t / 8) +
        -edgeT (box.outerIndex i) (box.outerIndex (box.edgeShell.next i)) (d + 1) *
          tN box (d + 2) (t / 8)) * δN (box.outerIndex i) d (t % 8))
      (2 * (80 * tBound box) * 40) := fun d => pairMul_rep (mPackT_rep box i d) (hd d)
  refine (((r 0).add ((r 1).add (r 2))).congr fun t => ?_).mono (by omega)
  simp only [supSlot, Fin.sum_univ_three]
  ring

theorem supportSlot (box : Box) (i : Fin (box.edgePred + 1)) (j : Fin 3) (k : Fin 8) :
    supSlot box i (8 * j.val + k.val) = supportI box i j k := by
  have h1 : (8 * j.val + k.val) / 8 = j.val := by omega
  have h2 : (8 * j.val + k.val) % 8 = k.val := by omega
  simp only [supSlot, h1, h2, Fin.sum_univ_three, edgeT_eq, tN, δN, j.isLt, k.isLt,
    ↓reduceDIte, supportI, mI, Fin.isValue, Fin.reduceAdd]
  ring

theorem foldr_max_le {α : Type} (f : α → ℤ) (h init : ℤ) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ h) → init ≤ h → l.foldr (fun x a => max (f x) a) init ≤ h
  | [], _, hi => hi
  | x :: l, hl, hi => max_le (hl x List.mem_cons_self)
      (foldr_max_le f h init l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hi)

theorem foldr_sum_le {α : Type} (f g : α → ℤ) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ g x) →
      l.foldr (fun x a => f x + a) 0 ≤ l.foldr (fun x a => g x + a) 0
  | [], _ => le_rfl
  | x :: l, hl => add_le_add (hl x List.mem_cons_self)
      (foldr_sum_le f g l fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem supportMaxI_le (box : Box) (i : Fin (box.edgePred + 1)) (k : VertexIndex) (h : ℤ)
    (hs : ∀ j : Fin 3, supportI box i j k ≤ h) : supportMaxI box i k ≤ h :=
  max_le (hs 0) (max_le (hs 1) (hs 2))

theorem bernI_add (box : Box) (p q : IQ) (i j k : ℕ) :
    bernI box (IQ.add p q) i j k = bernI box p i j k + bernI box q i j k := by
  simp only [bernI, IQ.add]
  split_ifs <;> ring

theorem bernI_smul (box : Box) (c : ℤ) (q : IQ) (i j k : ℕ) :
    bernI box (IQ.smul c q) i j k = c * bernI box q i j k := by
  simp only [bernI, IQ.smul]
  split_ifs <;> ring

theorem le_ceilDiv_mul (a : ℤ) (b : ℕ) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have := Int.ediv_mul_le (-a) (show (b : ℤ) ≠ 0 by omega)
  linarith

theorem validEdgeK_sound (box : Box) (hints : List ℤ) (h : validEdgeK box hints = true) :
    box.Valid := by
  simp only [validEdgeK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const, totalT_eq, maskT_eq, maskAll_eq] at h
  obtain ⟨⟨⟨⟨⟨hL, hE⟩, htri⟩, hμ⟩, hsupp⟩, hbern⟩ := h
  refine valid_of_facts box (hintSum box hints) hL hE htri hμ (fun i => ?_) ?_ (fun j a b c => ?_)
  · obtain ⟨⟨⟨_, hb⟩, _⟩, hw⟩ := hsupp i
    set wv := box.nonzeroWitness i
    have hb' : 4 * (19200 * tBound box + (-((-16000 * (triL box : ℤ) - 1) / 10 ^ 10)).natAbs) <
        2 ^ (KW - 1) := by rwa [Int.natAbs_neg]
    have hr := testGeM_sound (supportPackK_rep box i).neg hb' hw
    have hmax : supportMaxI box i wv ≤ (-16000 * triL box - 1) / 10 ^ 10 := by
      refine supportMaxI_le box i wv _ fun j => ?_
      have := hr (8 * j.val + wv.val) (by omega) (by simp)
      rw [supportSlot] at this
      linarith
    have := Int.ediv_mul_le (-16000 * (triL box : ℤ) - 1) (show (10 : ℤ) ^ 10 ≠ 0 by norm_num)
    have := mul_le_mul_of_nonneg_right hmax (show (0 : ℤ) ≤ 10 ^ 10 by norm_num)
    linarith
  · unfold totalDefectI hintSum
    refine foldr_sum_le _ _ _ fun i _ => ?_
    obtain ⟨⟨⟨ha, _⟩, hf⟩, _⟩ := hsupp i
    have hr := testGe_sound (supportPackK_rep box i).neg (by rwa [Int.natAbs_neg]) hf
    have hall : ∀ k : VertexIndex, supportMaxI box i k ≤ hints.getD i.val 0 := by
      intro k
      refine supportMaxI_le box i _ _ fun j => ?_
      have := hr (8 * j.val + k.val) (by omega) rfl
      rw [supportSlot] at this
      linarith
    exact foldr_max_le _ _ _ _ (fun k _ => hall k) (hall 0)
  · obtain ⟨hb, ht⟩ := hbern j
    set μ := box.ballMultiplier j
    have rW := fun c => bernPairK_rep (bernWeights box (totalI box c))
    have rC := bernPairK_rep (bernWeights box ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩)
    have rU := ((((rW 0).smul (T box j 0)).add (((rW 1).smul (T box j 1)).add
      ((rW 2).smul (T box j 2)))).smul (μ.den : ℤ)).add (rC.smul (μ.num * 1600 * triL box))
    rw [Int.natAbs_natCast] at rU
    have hr := testGe_sound rU hb ht (9 * a.val + 3 * b.val + c.val) (by omega) rfl
    simp only [bernSlot_eq] at hr
    have hadj : bernI box (adjI box j) a.val b.val c.val =
        μ.den * (T box j 0 * bernI box (totalI box 0) a.val b.val c.val +
          (T box j 1 * bernI box (totalI box 1) a.val b.val c.val +
            T box j 2 * bernI box (totalI box 2) a.val b.val c.val)) +
          μ.num * 1600 * triL box * bernI box ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩ a.val b.val c.val := by
      simp only [adjI, bernI_add, bernI_smul]
      ring
    have hc := le_ceilDiv_mul (dBoundNum box * (hintSum box hints * 10 ^ 10 +
      32000 * ((box.edgePred : ℤ) + 1) * triL box) * 4 * μ.den) (10 ^ 10) (by norm_num)
    have := mul_le_mul_of_nonneg_right (hadj ▸ hr) (show (0 : ℤ) ≤ ((10 ^ 10 : ℕ) : ℤ) by positivity)
    push_cast at hc this ⊢
    linarith

end Noperts.Stellated.ChartKernel
