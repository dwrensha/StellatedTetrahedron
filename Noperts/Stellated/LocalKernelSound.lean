module

public import Noperts.Stellated.LocalKernel

@[expose] public section

/-!
# Soundness of the integer local view check

Scaling identities relating the integer quantities of `LocalKernel` to the
rational ones of `AtlasProjectiveLocalCertificate`: vertices are `40 · v`,
edges `40000 · edgeQ`, triangle rows `L · t`.
-/

namespace Noperts.Stellated.LocalKernel

open AtlasProjectiveLocalCertificate
open AtlasProjectiveEdgeCertificate (dotQ SignedTriangleValid)

theorem int_add_eq (a b : ℤ) : Int.add a b = a + b := rfl
theorem int_sub_eq (a b : ℤ) : Int.sub a b = a - b := rfl
theorem int_mul_eq (a b : ℤ) : Int.mul a b = a * b := rfl

/-- A `V3` as a rational vector. -/
def V3.toQ (a : V3) : Fin 3 → ℚ := ![(a.x : ℚ), (a.y : ℚ), (a.z : ℚ)]

@[simp] theorem V3.toQ_zero (a : V3) : a.toQ 0 = a.x := rfl
@[simp] theorem V3.toQ_one (a : V3) : a.toQ 1 = a.y := rfl
@[simp] theorem V3.toQ_two (a : V3) : a.toQ 2 = a.z := rfl

theorem V3.dot_cast (a b : V3) : ((V3.dot a b : ℤ) : ℚ) = dotQ a.toQ b.toQ := by
  simp [V3.dot, dotQ]

theorem V3.cross_toQ (a b : V3) :
    (V3.cross a b).toQ = LocalCertificate.crossQ a.toQ b.toQ := by
  funext c
  fin_cases c <;> simp [V3.cross, V3.toQ, LocalCertificate.crossQ, int_sub_eq]

theorem V3.sub_toQ (a b : V3) : (V3.sub a b).toQ = a.toQ - b.toQ := by
  funext c
  fin_cases c <;> simp [V3.sub, V3.toQ, int_sub_eq]

theorem V3.add_toQ (a b : V3) : (V3.add a b).toQ = a.toQ + b.toQ := by
  funext c
  fin_cases c <;> simp [V3.add, V3.toQ]

theorem V3.smul_toQ (k : ℤ) (a : V3) : (V3.smul k a).toQ = (k : ℚ) • a.toQ := by
  funext c
  fin_cases c <;> simp [V3.smul, V3.toQ]

theorem vtx_toQ (k : VertexIndex) : (vtx k).toQ = (40 : ℚ) • rationalVertex k := by
  funext c
  fin_cases k <;> fin_cases c <;> norm_num [vtx, V3.toQ, rationalVertex]

theorem edgeN_toQ (cert : AxisCertificate) (i : Fin 3) :
    (edgeN cert i).toQ = (40000 : ℚ) • cert.edgeQ i := by
  have hm : ((cert.mix i).val : ℚ) ≤ 1000 := by exact_mod_cast Nat.le_of_lt_succ (cert.mix i).isLt
  simp only [edgeN, V3.add_toQ, V3.smul_toQ, V3.sub_toQ, vtx_toQ, AxisCertificate.edgeQ,
    AxisCertificate.mixQ]
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  ring

theorem scaleQ_cast (L : ℕ) (q : ℚ) (h : q.den ∣ L) : (scaleQ L q : ℚ) = L * q := by
  obtain ⟨m, rfl⟩ := h
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  simp only [scaleQ, Nat.mul_div_cancel_left m q.den_pos]
  push_cast
  have := Rat.mul_den_eq_num q
  rw [← this]
  ring

theorem den_dvd_lcm9 (t : AtlasProjectiveView.Triangle ℚ) (c k : Fin 3) :
    (t c k).den ∣ lcm9 t := by
  unfold lcm9
  fin_cases c <;> fin_cases k
  · exact (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  · exact (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  · exact (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _))
  · exact (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _))
  · exact (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _))
  · exact (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _))
  · exact (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))
  · exact (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_right _ _).trans
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)))
  · exact (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_right _ _).trans
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)))

theorem lcm9_pos (t : AtlasProjectiveView.Triangle ℚ) : 0 < lcm9 t := by
  unfold lcm9
  apply Nat.lcm_pos <;> apply Nat.lcm_pos <;> (try apply Nat.lcm_pos) <;>
    (try apply Nat.lcm_pos) <;> exact Rat.den_pos _

theorem triRow_toQ (t : AtlasProjectiveView.Triangle ℚ) (c : Fin 3) :
    (triRow (lcm9 t) t c).toQ = ((lcm9 t : ℕ) : ℚ) • t c := by
  funext k
  fin_cases k <;> simp [triRow, V3.toQ, scaleQ_cast _ _ (den_dvd_lcm9 t c _)]

/-! ## Bilinearity -/

theorem dotQ_smul_left (a : ℚ) (u v : Fin 3 → ℚ) : dotQ (a • u) v = a * dotQ u v := by
  simp only [dotQ, Pi.smul_apply, smul_eq_mul]; ring

theorem dotQ_smul_right (a : ℚ) (u v : Fin 3 → ℚ) : dotQ u (a • v) = a * dotQ u v := by
  simp only [dotQ, Pi.smul_apply, smul_eq_mul]; ring

theorem crossQ_smul (a b : ℚ) (u v : Fin 3 → ℚ) :
    LocalCertificate.crossQ (a • u) (b • v) = (a * b) • LocalCertificate.crossQ u v := by
  funext c
  fin_cases c <;> simp [LocalCertificate.crossQ] <;> ring

theorem supportError_eq : supportError = 0 := by
  simp [supportError, tightVertexErrorQ]

/-! ## Weights -/

theorem wcN_toQ (cert : AxisCertificate) (i : Fin 3) :
    (wcN cert i).toQ = (40000 * 40000 : ℚ) • cert.weightCoefficient i := by
  fin_cases i <;>
    simp [wcN, V3.cross_toQ, edgeN_toQ, crossQ_smul, AxisCertificate.weightCoefficient]

theorem weight_cast (box : Box) (L : ℕ) (j : Fin 4) (c i : Fin 3) (t : V3)
    (ht : t.toQ = (L : ℚ) • box.triangle c) :
    ((V3.dot t (wcN (box.certificate j) i) : ℤ) : ℚ) =
      (L * (40000 * 40000) : ℚ) * box.weightAt j c i := by
  rw [V3.dot_cast, ht, wcN_toQ, dotQ_smul_left, dotQ_smul_right, Box.weightAt]
  ring

/-! ## Supports -/

theorem triple_algebra (a b t e : Fin 3 → ℚ) (L : ℚ) :
    dotQ ((40 : ℚ) • a) (LocalCertificate.crossQ (L • t) ((40000 : ℚ) • e)) -
      dotQ ((40 : ℚ) • b) (LocalCertificate.crossQ (L • t) ((40000 : ℚ) • e)) =
    (L * (40000 * 40) : ℚ) * dotQ t (LocalCertificate.crossQ e (a - b)) := by
  simp only [dotQ, LocalCertificate.crossQ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem support_cast (box : Box) (L : ℕ) (j : Fin 4) (c i : Fin 3) (k : VertexIndex)
    (t : V3) (ht : t.toQ = (L : ℚ) • box.triangle c) :
    (((V3.dot (vtx k) (V3.cross t (edgeN (box.certificate j) i)) -
        V3.dot (vtx ((box.certificate j).supportIndex box i))
          (V3.cross t (edgeN (box.certificate j) i)) : ℤ)) : ℚ) =
      (L * (40000 * 40)  : ℚ) * box.supportAt j c i k := by
  push_cast
  rw [V3.dot_cast, V3.dot_cast, V3.cross_toQ, vtx_toQ, vtx_toQ, ht, edgeN_toQ,
    triple_algebra]
  rfl

theorem tie_iff (box : Box) (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    (k == (box.certificate j).supportIndex box i ||
      ((box.certificate j).mix i).val == 1000 &&
        (box.certificate j).supportIndex box i == (box.certificate j).edgeFinish i &&
        k == (box.certificate j).edgeStart i ||
      ((box.certificate j).mix i).val == 0 &&
        (box.certificate j).supportIndex box i == (box.certificate j).edgeStart₂ i &&
        k == (box.certificate j).edgeFinish₂ i) = true ↔ box.exactSupportTie j i k := by
  simp only [Box.exactSupportTie, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Fin.ext_iff]
  simp only [Fin.val_zero]
  constructor <;> intro h <;> tauto

theorem max3_int_le (a b c : ℤ) (h : max3 a b c ≤ 0) : a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0 := by
  simp only [max3, max_le_iff] at h; omega

theorem max3_int_lt (a b c : ℤ) (h : max3 a b c < 0) : a < 0 ∧ b < 0 ∧ c < 0 := by
  simp only [max3, max_lt_iff] at h; omega

theorem supportUpper_le_of (box : Box) (j : Fin 4) (i : Fin 3) (k : VertexIndex)
    (S : ℚ) (hS : 0 < S) (v0 v1 v2 : ℤ) (tieB : Bool)
    (hv0 : (v0 : ℚ) = S * box.supportAt j 0 i k) (hv1 : (v1 : ℚ) = S * box.supportAt j 1 i k)
    (hv2 : (v2 : ℚ) = S * box.supportAt j 2 i k)
    (htie : tieB = true ↔ box.exactSupportTie j i k)
    (h : (tieB || decide (max3 v0 v1 v2 ≤ 0)) = true) : box.supportUpper j i k ≤ 0 := by
  rcases Bool.or_eq_true _ _ |>.mp h with ht | hm
  · simp [Box.supportUpper, htie.mp ht]
  · have hm' := max3_int_le _ _ _ (of_decide_eq_true hm)
    have c0 : box.supportAt j 0 i k ≤ 0 := by
      have : (v0 : ℚ) ≤ 0 := by exact_mod_cast hm'.1
      rw [hv0] at this; exact nonpos_of_mul_nonpos_right this hS |>.trans_eq' rfl
    have c1 : box.supportAt j 1 i k ≤ 0 := by
      have : (v1 : ℚ) ≤ 0 := by exact_mod_cast hm'.2.1
      rw [hv1] at this; exact nonpos_of_mul_nonpos_right this hS |>.trans_eq' rfl
    have c2 : box.supportAt j 2 i k ≤ 0 := by
      have : (v2 : ℚ) ≤ 0 := by exact_mod_cast hm'.2.2
      rw [hv2] at this; exact nonpos_of_mul_nonpos_right this hS |>.trans_eq' rfl
    unfold Box.supportUpper
    split_ifs
    · exact le_rfl
    · simp only [AtlasProjectiveEdgeCertificate.max3, supportError_eq, add_zero, max_le_iff]
      exact ⟨c0, c1, c2⟩

theorem supportUpper_lt_of (box : Box) (j : Fin 4) (i : Fin 3) (k : VertexIndex)
    (S : ℚ) (hS : 0 < S) (v0 v1 v2 : ℤ) (tieB : Bool)
    (hv0 : (v0 : ℚ) = S * box.supportAt j 0 i k) (hv1 : (v1 : ℚ) = S * box.supportAt j 1 i k)
    (hv2 : (v2 : ℚ) = S * box.supportAt j 2 i k)
    (htie : tieB = true ↔ box.exactSupportTie j i k)
    (h : (!tieB && decide (max3 v0 v1 v2 < 0)) = true) : box.supportUpper j i k < 0 := by
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  have hnt : ¬ box.exactSupportTie j i k := fun ht => by simp [htie.mpr ht] at h
  have hm' := max3_int_lt _ _ _ (of_decide_eq_true h.2)
  have c0 : box.supportAt j 0 i k < 0 := by
    have : (v0 : ℚ) < 0 := by exact_mod_cast hm'.1
    rw [hv0] at this; exact neg_of_mul_neg_right this hS.le
  have c1 : box.supportAt j 1 i k < 0 := by
    have : (v1 : ℚ) < 0 := by exact_mod_cast hm'.2.1
    rw [hv1] at this; exact neg_of_mul_neg_right this hS.le
  have c2 : box.supportAt j 2 i k < 0 := by
    have : (v2 : ℚ) < 0 := by exact_mod_cast hm'.2.2
    rw [hv2] at this; exact neg_of_mul_neg_right this hS.le
  unfold Box.supportUpper
  rw [ite_eq_right hnt]
  simp only [AtlasProjectiveEdgeCertificate.max3, supportError_eq, add_zero, max_lt_iff]
  exact ⟨c0, c1, c2⟩

theorem supportN_sound (box : Box) (L : ℕ) (hL : 0 < L) (j : Fin 4) (i : Fin 3)
    (t0 t1 t2 : V3) (ht0 : t0.toQ = (L : ℚ) • box.triangle 0)
    (ht1 : t1.toQ = (L : ℚ) • box.triangle 1) (ht2 : t2.toQ = (L : ℚ) • box.triangle 2)
    (h : supportN t0 t1 t2 (edgeN (box.certificate j) i)
      ((box.certificate j).supportIndex box i) ((box.certificate j).mix i).val
      ((box.certificate j).edgeStart i) ((box.certificate j).edgeFinish i)
      ((box.certificate j).edgeStart₂ i) ((box.certificate j).edgeFinish₂ i)
      ((box.certificate j).nonzeroWitness i) = true) :
    (∀ k, box.supportUpper j i k ≤ 0) ∧
      box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0 := by
  have hS : (0 : ℚ) < L * (40000 * 40) := by positivity
  have hv := fun k => And.intro (support_cast box L j 0 i k t0 ht0)
    (And.intro (support_cast box L j 1 i k t1 ht1) (support_cast box L j 2 i k t2 ht2))
  have htie := tie_iff box j i
  unfold supportN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hw⟩ := h
  refine ⟨fun k => ?_, ?_⟩
  · fin_cases k
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h0
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h1
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h2
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h3
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h4
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h5
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h6
    · exact supportUpper_le_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _) h7
  · exact supportUpper_lt_of box j i _ _ hS _ _ _ _ (hv _).1 (hv _).2.1 (hv _).2.2 (htie _)
      (by rw [Bool.and_eq_true]; exact hw)

/-! ## Variation balls -/

open Noperts.Checker in
theorem rp_add {n : ℕ} (p q : RatPolynomial n) : p + q = .add p q := rfl
open Noperts.Checker in
theorem rp_sub {n : ℕ} (p q : RatPolynomial n) : p - q = .add p (.neg q) := rfl
open Noperts.Checker in
theorem rp_mul {n : ℕ} (p q : RatPolynomial n) : p * q = .mul p q := rfl

open Noperts.Checker in
/-- Closed form of the ball enclosure of a quadratic around the balls' centers. -/
theorem evalBall_closed (q : RatQuadratic3) (v : Fin 3 → RatBall) :
    RatQuadratic3.evalBall v q =
      ⟨q.evalQ (v 0).center (v 1).center (v 2).center,
        |q.cx + 2 * q.cxx * (v 0).center + q.cxy * (v 1).center + q.cxz * (v 2).center| *
            (v 0).radius +
          |q.cy + q.cxy * (v 0).center + 2 * q.cyy * (v 1).center + q.cyz * (v 2).center| *
            (v 1).radius +
          |q.cz + q.cxz * (v 0).center + q.cyz * (v 1).center + 2 * q.czz * (v 2).center| *
            (v 2).radius +
          |q.cxx| * ((v 0).radius * (v 0).radius) + |q.cxy| * ((v 0).radius * (v 1).radius) +
          |q.cxz| * ((v 0).radius * (v 2).radius) + |q.cyy| * ((v 1).radius * (v 1).radius) +
          |q.cyz| * ((v 1).radius * (v 2).radius) + |q.czz| * ((v 2).radius * (v 2).radius)⟩ := by
  simp only [RatQuadratic3.evalBall, RatQuadratic3.centeredPolynomial, RatPolynomial.scale,
    rp_add, rp_sub, rp_mul, RatPolynomial.evalBall, RatBall.add, RatBall.mul, RatBall.neg,
    RatBall.const]
  congr 1
  · simp only [RatQuadratic3.evalQ]; ring
  · simp only [add_neg_cancel, abs_zero, zero_mul, mul_zero, add_zero, zero_add]

/-- The spec's `crossLiftCoefficient` for a given vertex and edge vector. -/
def crossLiftQ (sv ev : Fin 3 → ℚ) (coordinate : Fin 3) : Fin 3 → ℚ :=
  let l0 : Fin 3 → ℚ := ![0, ev 2, -ev 1]
  let l1 : Fin 3 → ℚ := ![-ev 2, 0, ev 0]
  let l2 : Fin 3 → ℚ := ![ev 1, -ev 0, 0]
  match coordinate with
  | 0 => sv 1 • l2 - sv 2 • l1
  | 1 => sv 2 • l0 - sv 0 • l2
  | 2 => sv 0 • l1 - sv 1 • l0

theorem crossLiftCoefficient_eq (box : Box) (cert : AxisCertificate) (i c : Fin 3) :
    cert.crossLiftCoefficient box i c =
      crossLiftQ (rationalVertex (cert.supportIndex box i)) (cert.edgeQ i) c := by
  fin_cases c <;> rfl

theorem crossLiftN_toQ (sv ev : V3) (c : Fin 3) :
    (crossLiftN sv ev c).toQ = crossLiftQ sv.toQ ev.toQ c := by
  funext d
  fin_cases c <;> fin_cases d <;>
    simp [crossLiftN, crossLiftQ, V3.sub, V3.smul, V3.toQ, int_sub_eq]

theorem crossLiftQ_smul (a b : ℚ) (sv ev : Fin 3 → ℚ) (c : Fin 3) :
    crossLiftQ (a • sv) (b • ev) c = (a * b) • crossLiftQ sv ev c := by
  funext d
  fin_cases c <;> fin_cases d <;> simp [crossLiftQ] <;> ring

open Noperts.Checker in
/-- `Q = K · q` on the quadratic coefficients, and `q` has no constant or linear part. -/
def Q6.Rel (Q : Q6) (K : ℚ) (q : RatQuadratic3) : Prop :=
  q.c0 = 0 ∧ q.cx = 0 ∧ q.cy = 0 ∧ q.cz = 0 ∧
    (Q.xx : ℚ) = K * q.cxx ∧ (Q.xy : ℚ) = K * q.cxy ∧ (Q.xz : ℚ) = K * q.cxz ∧
    (Q.yy : ℚ) = K * q.cyy ∧ (Q.yz : ℚ) = K * q.cyz ∧ (Q.zz : ℚ) = K * q.czz

open Noperts.Checker in
theorem Q6.Rel.add {Q Q' : Q6} {K : ℚ} {q q' : RatQuadratic3} (h : Q.Rel K q)
    (h' : Q'.Rel K q') : (Q6.add Q Q').Rel K (q + q') := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Q6.add, RatQuadratic3.add_c0, RatQuadratic3.add_cx, RatQuadratic3.add_cy,
      RatQuadratic3.add_cz, RatQuadratic3.add_cxx, RatQuadratic3.add_cxy,
      RatQuadratic3.add_cxz, RatQuadratic3.add_cyy, RatQuadratic3.add_cyz,
      RatQuadratic3.add_czz, Int.cast_add] <;> simp_all <;> ring

theorem mulLinearN_rel (a b : V3) (α β : ℚ) (u v : Fin 3 → ℚ) (ha : a.toQ = α • u)
    (hb : b.toQ = β • v) :
    (mulLinearN a b).Rel (α * β) (Noperts.ProjectiveLocalCertificate.mulLinear u v) := by
  have a0 := congrFun ha 0
  have a1 := congrFun ha 1
  have a2 := congrFun ha 2
  have b0 := congrFun hb 0
  have b1 := congrFun hb 1
  have b2 := congrFun hb 2
  simp only [V3.toQ_zero, V3.toQ_one, V3.toQ_two, Pi.smul_apply, smul_eq_mul] at a0 a1 a2 b0 b1 b2
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [mulLinearN, Noperts.ProjectiveLocalCertificate.mulLinear,
      Int.cast_add, Int.cast_mul, a0, a1, a2, b0, b1, b2] <;> ring

open Noperts.Checker in
theorem ballN_rel (Q : Q6) (K : ℚ) (hK : 0 < K) (q : RatQuadratic3) (hq : Q.Rel K q)
    (bn : BoxN) (L : ℚ) (hL : 0 < L) (v : Fin 3 → RatBall)
    (hmx : (bn.mx : ℚ) = 2 * L * (v 0).center) (hmy : (bn.my : ℚ) = 2 * L * (v 1).center)
    (hmz : (bn.mz : ℚ) = 2 * L * (v 2).center) (hrx : (bn.rx : ℚ) = 2 * L * (v 0).radius)
    (hry : (bn.ry : ℚ) = 2 * L * (v 1).radius) (hrz : (bn.rz : ℚ) = 2 * L * (v 2).radius) :
    ((ballN Q bn).1 : ℚ) = 4 * L ^ 2 * K * (RatQuadratic3.evalBall v q).center ∧
      ((ballN Q bn).2 : ℚ) = 4 * L ^ 2 * K * (RatQuadratic3.evalBall v q).radius := by
  obtain ⟨h0, hx, hy, hz, hxx, hxy, hxz, hyy, hyz, hzz⟩ := hq
  have hS : 0 < 2 * L * K := by positivity
  have gx : ((2 * Q.xx * bn.mx + Q.xy * bn.my + Q.xz * bn.mz : ℤ) : ℚ) =
      2 * L * K * (q.cx + 2 * q.cxx * (v 0).center + q.cxy * (v 1).center +
        q.cxz * (v 2).center) := by
    push_cast; rw [hxx, hxy, hxz, hmx, hmy, hmz, hx]; ring
  have gy : ((Q.xy * bn.mx + 2 * Q.yy * bn.my + Q.yz * bn.mz : ℤ) : ℚ) =
      2 * L * K * (q.cy + q.cxy * (v 0).center + 2 * q.cyy * (v 1).center +
        q.cyz * (v 2).center) := by
    push_cast; rw [hxy, hyy, hyz, hmx, hmy, hmz, hy]; ring
  have gz : ((Q.xz * bn.mx + Q.yz * bn.my + 2 * Q.zz * bn.mz : ℤ) : ℚ) =
      2 * L * K * (q.cz + q.cxz * (v 0).center + q.cyz * (v 1).center +
        2 * q.czz * (v 2).center) := by
    push_cast; rw [hxz, hyz, hzz, hmx, hmy, hmz, hz]; ring
  rw [evalBall_closed]
  refine ⟨?_, ?_⟩
  · simp only [ballN]
    push_cast
    rw [hxx, hxy, hxz, hyy, hyz, hzz, hmx, hmy, hmz]
    simp only [RatQuadratic3.evalQ, h0, hx, hy, hz]
    ring
  · simp only [ballN]
    push_cast
    have ax : |((2 * Q.xx * bn.mx + Q.xy * bn.my + Q.xz * bn.mz : ℤ) : ℚ)| =
        2 * L * K * |q.cx + 2 * q.cxx * (v 0).center + q.cxy * (v 1).center +
          q.cxz * (v 2).center| := by
      rw [gx, abs_mul, abs_of_pos hS]
    have ay : |((Q.xy * bn.mx + 2 * Q.yy * bn.my + Q.yz * bn.mz : ℤ) : ℚ)| =
        2 * L * K * |q.cy + q.cxy * (v 0).center + 2 * q.cyy * (v 1).center +
          q.cyz * (v 2).center| := by
      rw [gy, abs_mul, abs_of_pos hS]
    have az : |((Q.xz * bn.mx + Q.yz * bn.my + 2 * Q.zz * bn.mz : ℤ) : ℚ)| =
        2 * L * K * |q.cz + q.cxz * (v 0).center + q.cyz * (v 1).center +
          2 * q.czz * (v 2).center| := by
      rw [gz, abs_mul, abs_of_pos hS]
    push_cast at ax ay az
    rw [ax, ay, az, hxx, hxy, hxz, hyy, hyz, hzz, hrx, hry, hrz, abs_mul, abs_mul, abs_mul,
      abs_mul, abs_mul, abs_mul, abs_of_pos hK]
    ring

theorem min3_cast (a b c : ℤ) (L : ℚ) (hL : 0 ≤ L) (f : Fin 3 → ℚ)
    (ha : (a : ℚ) = L * f 0) (hb : (b : ℚ) = L * f 1) (hc : (c : ℚ) = L * f 2) :
    ((min3 a b c : ℤ) : ℚ) = L * AtlasProjectiveEdgeCertificate.min3 f := by
  simp only [min3, AtlasProjectiveEdgeCertificate.min3, Int.cast_min, ha, hb, hc,
    mul_min_of_nonneg _ _ hL]

theorem max3_cast (a b c : ℤ) (L : ℚ) (hL : 0 ≤ L) (f : Fin 3 → ℚ)
    (ha : (a : ℚ) = L * f 0) (hb : (b : ℚ) = L * f 1) (hc : (c : ℚ) = L * f 2) :
    ((max3 a b c : ℤ) : ℚ) = L * AtlasProjectiveEdgeCertificate.max3 f := by
  simp only [max3, AtlasProjectiveEdgeCertificate.max3, Int.cast_max, ha, hb, hc,
    mul_max_of_nonneg _ _ hL]

theorem toQ_comp (t : V3) (L : ℚ) (row : Fin 3 → ℚ) (ht : t.toQ = L • row) :
    (t.x : ℚ) = L * row 0 ∧ (t.y : ℚ) = L * row 1 ∧ (t.z : ℚ) = L * row 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrFun ht 0
  · simpa using congrFun ht 1
  · simpa using congrFun ht 2

theorem boxNOf_rel (box : Box) (L : ℕ) (t0 t1 t2 : V3)
    (ht0 : t0.toQ = (L : ℚ) • box.triangle 0) (ht1 : t1.toQ = (L : ℚ) • box.triangle 1)
    (ht2 : t2.toQ = (L : ℚ) • box.triangle 2) :
    let bn := boxNOf t0 t1 t2
    let v := box.triangleBalls
    (bn.mx : ℚ) = 2 * L * (v 0).center ∧ (bn.my : ℚ) = 2 * L * (v 1).center ∧
      (bn.mz : ℚ) = 2 * L * (v 2).center ∧ (bn.rx : ℚ) = 2 * L * (v 0).radius ∧
      (bn.ry : ℚ) = 2 * L * (v 1).radius ∧ (bn.rz : ℚ) = 2 * L * (v 2).radius := by
  intro bn v
  obtain ⟨a0, a1, a2⟩ := toQ_comp _ _ _ ht0
  obtain ⟨b0, b1, b2⟩ := toQ_comp _ _ _ ht1
  obtain ⟨c0, c1, c2⟩ := toQ_comp _ _ _ ht2
  have hL : (0 : ℚ) ≤ L := by positivity
  have mn := fun (k : Fin 3) (x y z : ℤ) (hx : (x : ℚ) = L * box.triangle 0 k)
      (hy : (y : ℚ) = L * box.triangle 1 k) (hz : (z : ℚ) = L * box.triangle 2 k) =>
    And.intro (min3_cast x y z L hL (fun j => box.triangle j k) hx hy hz)
      (max3_cast x y z L hL (fun j => box.triangle j k) hx hy hz)
  have m0 := mn 0 _ _ _ a0 b0 c0
  have m1 := mn 1 _ _ _ a1 b1 c1
  have m2 := mn 2 _ _ _ a2 b2 c2
  simp only [bn, v, boxNOf, Box.triangleBalls, Noperts.Checker.RatBall.ofEndpoints]
  push_cast
  rw [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem crossLiftN_spec (box : Box) (cert : AxisCertificate) (i c : Fin 3) :
    (crossLiftN (vtx (cert.supportIndex box i)) (edgeN cert i) c).toQ =
      ((40 : ℚ) * 40000) • cert.crossLiftCoefficient box i c := by
  rw [crossLiftN_toQ, vtx_toQ, edgeN_toQ, crossLiftQ_smul, crossLiftCoefficient_eq]

/-- The integer variation quadratic of axis `j`, coordinate `c`, as built by `axisN`. -/
def qN (box : Box) (j : Fin 4) (c : Fin 3) : Q6 :=
  let cert := box.certificate j
  Q6.add (Q6.add (mulLinearN (wcN cert 0) (crossLiftN (vtx (cert.supportIndex box 0))
      (edgeN cert 0) c))
    (mulLinearN (wcN cert 1) (crossLiftN (vtx (cert.supportIndex box 1)) (edgeN cert 1) c)))
    (mulLinearN (wcN cert 2) (crossLiftN (vtx (cert.supportIndex box 2)) (edgeN cert 2) c))

theorem qN_rel (box : Box) (j : Fin 4) (c : Fin 3) :
    (qN box j c).Rel ((40000 * 40000) * (40 * 40000))
      ((box.certificate j).variationPolynomial box c) := by
  unfold qN AxisCertificate.variationPolynomial
  exact ((mulLinearN_rel _ _ _ _ _ _ (wcN_toQ _ 0) (crossLiftN_spec box _ 0 c)).add
    (mulLinearN_rel _ _ _ _ _ _ (wcN_toQ _ 1) (crossLiftN_spec box _ 1 c))).add
    (mulLinearN_rel _ _ _ _ _ _ (wcN_toQ _ 2) (crossLiftN_spec box _ 2 c))

theorem weightLower_rel (box : Box) (L : ℕ) (j : Fin 4) (i : Fin 3) (t0 t1 t2 : V3)
    (ht0 : t0.toQ = (L : ℚ) • box.triangle 0) (ht1 : t1.toQ = (L : ℚ) • box.triangle 1)
    (ht2 : t2.toQ = (L : ℚ) • box.triangle 2) :
    ((min3 (V3.dot t0 (wcN (box.certificate j) i)) (V3.dot t1 (wcN (box.certificate j) i))
        (V3.dot t2 (wcN (box.certificate j) i)) : ℤ) : ℚ) =
      (L * (40000 * 40000) : ℚ) * box.weightLower j i := by
  rw [min3_cast _ _ _ _ (by positivity) (fun c => box.weightAt j c i)
    (weight_cast box L j 0 i t0 ht0) (weight_cast box L j 1 i t1 ht1)
    (weight_cast box L j 2 i t2 ht2)]
  simp [Box.weightLower, supportError_eq]

theorem weightUpper_rel (box : Box) (L : ℕ) (j : Fin 4) (i : Fin 3) (t0 t1 t2 : V3)
    (ht0 : t0.toQ = (L : ℚ) • box.triangle 0) (ht1 : t1.toQ = (L : ℚ) • box.triangle 1)
    (ht2 : t2.toQ = (L : ℚ) • box.triangle 2) :
    ((max3 (V3.dot t0 (wcN (box.certificate j) i)) (V3.dot t1 (wcN (box.certificate j) i))
        (V3.dot t2 (wcN (box.certificate j) i)) : ℤ) : ℚ) =
      (L * (40000 * 40000) : ℚ) * box.weightUpper j i := by
  rw [max3_cast _ _ _ _ (by positivity) (fun c => box.weightAt j c i)
    (weight_cast box L j 0 i t0 ht0) (weight_cast box L j 1 i t1 ht1)
    (weight_cast box L j 2 i t2 ht2)]
  simp [Box.weightUpper, supportError_eq]

theorem variationError_eq : 3 * variationError = 9 / 200000000 := by
  simp [variationError, RationalApprox.κℚ]; norm_num

theorem nonneg_of_cast {x : ℤ} {S y : ℚ} (hS : 0 < S) (h : (x : ℚ) = S * y) (hx : 0 ≤ x) :
    0 ≤ y := by
  have : (0 : ℚ) ≤ x := by exact_mod_cast hx
  rw [h] at this
  exact (mul_nonneg_iff_of_pos_left hS).mp this

theorem pos_of_cast {x : ℤ} {S y : ℚ} (hS : 0 < S) (h : (x : ℚ) = S * y) (hx : 0 < x) :
    0 < y := by
  have : (0 : ℚ) < x := by exact_mod_cast hx
  rw [h] at this
  exact (mul_pos_iff_of_pos_left hS).mp this

/-! ## The `Nat` fast path of the support test -/

theorem vtxN_cast (k : VertexIndex) :
    ((vtxN k).x : ℤ) = (vtx k).x + 20 ∧ ((vtxN k).y : ℤ) = (vtx k).y + 20 ∧
      ((vtxN k).z : ℤ) = (vtx k).z + 20 := by
  fin_cases k <;> simp [vtxN, vtx]

/-- The `Nat` vertex test computes the sign of the integer support value. -/
theorem vertex_value (t e : V3) (htx : 0 ≤ t.x) (hty : 0 ≤ t.y) (htz : 0 ≤ t.z)
    (k s : VertexIndex) :
    V3.dot (vtx k) (V3.cross t e) - V3.dot (vtx s) (V3.cross t e) =
      ((Nat.add (dotN (vtxN k) (crossP (toN3 t) (posPart e) (negPart e)))
          (dotN (vtxN s) (crossN (toN3 t) (posPart e) (negPart e))) : ℕ) : ℤ) -
        ((Nat.add (dotN (vtxN k) (crossN (toN3 t) (posPart e) (negPart e)))
          (dotN (vtxN s) (crossP (toN3 t) (posPart e) (negPart e))) : ℕ) : ℤ) := by
  obtain ⟨kx, ky, kz⟩ := vtxN_cast k
  obtain ⟨sx, sy, sz⟩ := vtxN_cast s
  have ex := Int.toNat_sub_toNat_neg e.x
  have ey := Int.toNat_sub_toNat_neg e.y
  have ez := Int.toNat_sub_toNat_neg e.z
  simp only [dotN, crossP, crossN, toN3, posPart, negPart, Nat.add_eq, Nat.mul_eq,
    Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg htx, Int.toNat_of_nonneg hty,
    Int.toNat_of_nonneg htz, kx, ky, kz, sx, sy, sz]
  simp only [V3.dot, V3.cross, int_add_eq, int_sub_eq, int_mul_eq]
  set A := (e.x.toNat : ℤ)
  set B := ((-e.x).toNat : ℤ)
  set C := (e.y.toNat : ℤ)
  set D := ((-e.y).toNat : ℤ)
  set E := (e.z.toNat : ℤ)
  set F := ((-e.z).toNat : ℤ)
  rw [← ex, ← ey, ← ez]
  ring

theorem vertexTestN_le (t e : V3) (htx : 0 ≤ t.x) (hty : 0 ≤ t.y) (htz : 0 ≤ t.z)
    (k s : VertexIndex)
    (h : vertexTestN false (crossP (toN3 t) (posPart e) (negPart e))
      (crossN (toN3 t) (posPart e) (negPart e)) k s = true) :
    V3.dot (vtx k) (V3.cross t e) - V3.dot (vtx s) (V3.cross t e) ≤ 0 := by
  rw [vertex_value t e htx hty htz]
  simp only [vertexTestN, Bool.false_eq_true, ↓reduceIte, Nat.ble_eq] at h
  omega

theorem vertexTestN_lt (t e : V3) (htx : 0 ≤ t.x) (hty : 0 ≤ t.y) (htz : 0 ≤ t.z)
    (k s : VertexIndex)
    (h : vertexTestN true (crossP (toN3 t) (posPart e) (negPart e))
      (crossN (toN3 t) (posPart e) (negPart e)) k s = true) :
    V3.dot (vtx k) (V3.cross t e) - V3.dot (vtx s) (V3.cross t e) < 0 := by
  rw [vertex_value t e htx hty htz]
  simp only [vertexTestN, ↓reduceIte, Nat.blt_eq] at h
  omega

theorem okK_of (tk b0 b1 b2 : Bool) (v0 v1 v2 : ℤ) (h0 : b0 = true → v0 ≤ 0)
    (h1 : b1 = true → v1 ≤ 0) (h2 : b2 = true → v2 ≤ 0) (k0 : (tk || b0) = true)
    (k1 : (tk || b1) = true) (k2 : (tk || b2) = true) :
    (tk || decide (max3 v0 v1 v2 ≤ 0)) = true := by
  cases tk
  · simp only [Bool.false_or] at k0 k1 k2 ⊢
    have := h0 k0; have := h1 k1; have := h2 k2
    simp only [max3, decide_eq_true_eq, max_le_iff]
    omega
  · rfl

theorem strict_of (b0 b1 b2 : Bool) (v0 v1 v2 : ℤ) (h0 : b0 = true → v0 < 0)
    (h1 : b1 = true → v1 < 0) (h2 : b2 = true → v2 < 0) (k0 : b0 = true) (k1 : b1 = true)
    (k2 : b2 = true) : decide (max3 v0 v1 v2 < 0) = true := by
  have := h0 k0; have := h1 k1; have := h2 k2
  simp only [max3, decide_eq_true_eq, max_lt_iff]
  omega

theorem supportFast_imp (t0 t1 t2 e : V3) (s : VertexIndex) (mix : ℕ)
    (es ef es₂ ef₂ w : VertexIndex)
    (h : supportFast t0 t1 t2 e s mix es ef es₂ ef₂ w = true) :
    supportN t0 t1 t2 e s mix es ef es₂ ef₂ w = true := by
  unfold supportFast at h
  split_ifs at h with hnn
  · simp only [nonnegV3, Bool.and_eq_true, decide_eq_true_eq] at hnn
    obtain ⟨⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩, ⟨c0, c1, c2⟩⟩ := hnn
    simp only [cornerN, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hw, ⟨⟨⟨⟨⟨⟨⟨⟨p0, p1⟩, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩, pw⟩⟩,
      ⟨⟨⟨⟨⟨⟨⟨⟨q0, q1⟩, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩, q7⟩, qw⟩⟩,
      ⟨⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩, rw⟩⟩ := h
    unfold supportN
    simp only [Bool.and_eq_true]
    have L0 := fun k => vertexTestN_le t0 e a0 a1 a2 k s
    have L1 := fun k => vertexTestN_le t1 e b0 b1 b2 k s
    have L2 := fun k => vertexTestN_le t2 e c0 c1 c2 k s
    refine ⟨⟨⟨⟨⟨⟨⟨⟨okK_of _ _ _ _ _ _ _ (L0 0) (L1 0) (L2 0) p0 q0 r0,
      okK_of _ _ _ _ _ _ _ (L0 1) (L1 1) (L2 1) p1 q1 r1⟩,
      okK_of _ _ _ _ _ _ _ (L0 2) (L1 2) (L2 2) p2 q2 r2⟩,
      okK_of _ _ _ _ _ _ _ (L0 3) (L1 3) (L2 3) p3 q3 r3⟩,
      okK_of _ _ _ _ _ _ _ (L0 4) (L1 4) (L2 4) p4 q4 r4⟩,
      okK_of _ _ _ _ _ _ _ (L0 5) (L1 5) (L2 5) p5 q5 r5⟩,
      okK_of _ _ _ _ _ _ _ (L0 6) (L1 6) (L2 6) p6 q6 r6⟩,
      okK_of _ _ _ _ _ _ _ (L0 7) (L1 7) (L2 7) p7 q7 r7⟩, hw,
      strict_of _ _ _ _ _ _ (vertexTestN_lt t0 e a0 a1 a2 w s) (vertexTestN_lt t1 e b0 b1 b2 w s)
        (vertexTestN_lt t2 e c0 c1 c2 w s) pw qw rw⟩
  · exact h

/-- Everything `ViewValid` asks of one axis. -/
def AxisFacts (box : Box) (j : Fin 4) : Prop :=
  0 < (box.certificate j).B ∧ (∀ i, 0 ≤ box.weightLower j i) ∧
    (∃ i, 0 < box.weightLower j i) ∧ (∀ i k, box.supportUpper j i k ≤ 0) ∧
    (∀ i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0) ∧
    box.weightBudget j ≤ (box.certificate j).B ∧
    box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ

/-- Everything `ViewValid` asks of one axis, from an accepted `axisN`. -/
theorem axisN_sound (box : Box) (L : ℕ) (hL : 0 < L) (t0 t1 t2 : V3)
    (ht0 : t0.toQ = (L : ℚ) • box.triangle 0) (ht1 : t1.toQ = (L : ℚ) • box.triangle 1)
    (ht2 : t2.toQ = (L : ℚ) • box.triangle 2) (j : Fin 4)
    (h : (axisN box (L : ℤ) t0 t1 t2 (boxNOf t0 t1 t2) j).ok = true) :
    0 < (box.certificate j).B ∧ (∀ i, 0 ≤ box.weightLower j i) ∧
      (∃ i, 0 < box.weightLower j i) ∧ (∀ i k, box.supportUpper j i k ≤ 0) ∧
      (∀ i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0) ∧
      box.weightBudget j ≤ (box.certificate j).B ∧
      box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ := by
  have hS : (0 : ℚ) < L * (40000 * 40000) := by positivity
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  simp only [axisN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hB, hw⟩, hbud⟩, ⟨⟨hs0, hs1⟩, hs2⟩⟩, hvar⟩ := h
  have wl := fun i => weightLower_rel box L j i t0 t1 t2 ht0 ht1 ht2
  have wu := fun i => weightUpper_rel box L j i t0 t1 t2 ht0 ht1 ht2
  obtain ⟨hw0, hw1, hw2, hwp⟩ := hw
  have sup0 := supportN_sound box L hL j 0 t0 t1 t2 ht0 ht1 ht2 (supportFast_imp _ _ _ _ _ _ _ _ _ _ _ hs0)
  have sup1 := supportN_sound box L hL j 1 t0 t1 t2 ht0 ht1 ht2 (supportFast_imp _ _ _ _ _ _ _ _ _ _ _ hs1)
  have sup2 := supportN_sound box L hL j 2 t0 t1 t2 ht0 ht1 ht2 (supportFast_imp _ _ _ _ _ _ _ _ _ _ _ hs2)
  refine ⟨hB, fun i => ?_, ?_, fun i k => ?_, fun i => ?_, ?_, ?_⟩
  · fin_cases i
    · exact nonneg_of_cast hS (wl 0) hw0
    · exact nonneg_of_cast hS (wl 1) hw1
    · exact nonneg_of_cast hS (wl 2) hw2
  · rcases hwp with h0 | h1 | h2
    · exact ⟨0, pos_of_cast hS (wl 0) h0⟩
    · exact ⟨1, pos_of_cast hS (wl 1) h1⟩
    · exact ⟨2, pos_of_cast hS (wl 2) h2⟩
  · fin_cases i
    · exact sup0.1 k
    · exact sup1.1 k
    · exact sup2.1 k
  · fin_cases i
    · exact sup0.2
    · exact sup1.2
    · exact sup2.2
  · -- budget
    have hc : ((2 * (box.certificate j).B.den * (max3 (V3.dot t0 (wcN (box.certificate j) 0))
          (V3.dot t1 (wcN (box.certificate j) 0)) (V3.dot t2 (wcN (box.certificate j) 0)) +
        max3 (V3.dot t0 (wcN (box.certificate j) 1)) (V3.dot t1 (wcN (box.certificate j) 1))
          (V3.dot t2 (wcN (box.certificate j) 1)) +
        max3 (V3.dot t0 (wcN (box.certificate j) 2)) (V3.dot t1 (wcN (box.certificate j) 2))
          (V3.dot t2 (wcN (box.certificate j) 2))) : ℤ) : ℚ) ≤
        (((box.certificate j).B.num * (L : ℤ) * 1600000000 : ℤ) : ℚ) := by
      exact_mod_cast hbud
    push_cast at hc
    rw [wu 0, wu 1, wu 2] at hc
    have hd : (0 : ℚ) < (box.certificate j).B.den := by exact_mod_cast (box.certificate j).B.den_pos
    have key : 2 * ((box.certificate j).B.den : ℚ) * (box.weightUpper j 0 + box.weightUpper j 1 +
        box.weightUpper j 2) ≤ (box.certificate j).B.num := by
      have h2 : (2 * ((box.certificate j).B.den : ℚ) * (box.weightUpper j 0 +
          box.weightUpper j 1 + box.weightUpper j 2)) * (L * (40000 * 40000)) ≤
          ((box.certificate j).B.num : ℚ) * (L * (40000 * 40000)) := by
        linarith
      exact le_of_mul_le_mul_right h2 hS
    rw [Box.weightBudget, Fin.sum_univ_three, ← Rat.num_div_den (box.certificate j).B,
      le_div_iff₀ hd]
    linarith
  · -- variation
    have hK : (0 : ℚ) < (40000 * 40000) * (40 * 40000) := by norm_num
    have bn := boxNOf_rel box L t0 t1 t2 ht0 ht1 ht2
    obtain ⟨hmx, hmy, hmz, hrx, hry, hrz⟩ := bn
    have br := fun c => (ballN_rel (qN box j c) _ hK _ (qN_rel box j c) (boxNOf t0 t1 t2)
      (L : ℚ) hLq box.triangleBalls hmx hmy hmz hrx hry hrz).2
    have hv : ((((ballN (qN box j 0) (boxNOf t0 t1 t2)).2 +
          (ballN (qN box j 1) (boxNOf t0 t1 t2)).2 + (ballN (qN box j 2) (boxNOf t0 t1 t2)).2) *
          200000000 * (box.certificate j).B.den * box.δ.den +
        9 * (4 * (L : ℤ) * L * 2560000000000000) * (box.certificate j).B.den * box.δ.den : ℤ)
        : ℚ) ≤ (((box.certificate j).B.num * box.δ.num * (4 * (L : ℤ) * L * 2560000000000000) *
          200000000 : ℤ) : ℚ) := by
      exact_mod_cast hvar
    push_cast at hv
    rw [br 0, br 1, br 2] at hv
    rw [Box.variationRadiusSum, Fin.sum_univ_three, variationError_eq]
    simp only [Box.variationBall]
    have hd : (0 : ℚ) < (box.certificate j).B.den := by exact_mod_cast (box.certificate j).B.den_pos
    have hdδ : (0 : ℚ) < box.δ.den := by exact_mod_cast box.δ.den_pos
    have hA : (0 : ℚ) < 4 * (L : ℚ) ^ 2 * ((40000 * 40000) * (40 * 40000)) := by positivity
    set R := (Noperts.Checker.RatQuadratic3.evalBall box.triangleBalls
        ((box.certificate j).variationPolynomial box 0)).radius +
      (Noperts.Checker.RatQuadratic3.evalBall box.triangleBalls
        ((box.certificate j).variationPolynomial box 1)).radius +
      (Noperts.Checker.RatQuadratic3.evalBall box.triangleBalls
        ((box.certificate j).variationPolynomial box 2)).radius with hR
    have key : (R * 200000000 * (box.certificate j).B.den * box.δ.den +
        9 * (box.certificate j).B.den * box.δ.den) * (4 * (L : ℚ) ^ 2 *
          ((40000 * 40000) * (40 * 40000))) ≤
        ((box.certificate j).B.num * box.δ.num * 200000000) *
          (4 * (L : ℚ) ^ 2 * ((40000 * 40000) * (40 * 40000))) := by
      rw [hR]; linarith [hv]
    have key2 := le_of_mul_le_mul_right key hA
    rw [← Rat.num_div_den (box.certificate j).B, ← Rat.num_div_den box.δ, div_mul_div_comm,
      le_div_iff₀ (by positivity)]
    linarith

/-! ## Barycentric test -/

open LocalCertificate (sub3Q det3Q) in
theorem det3_cast (a b c : V3) : ((det3 a b c : ℤ) : ℚ) = det3Q a.toQ b.toQ c.toQ := by
  rw [det3, V3.dot_cast, V3.cross_toQ]
  simp only [dotQ, det3Q, LocalCertificate.crossQ, V3.toQ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

open LocalCertificate (sub3Q det3Q) in
theorem det3Q_smul (l : ℚ) (u v w : Fin 3 → ℚ) :
    det3Q (l • u) (l • v) (l • w) = l ^ 3 * det3Q u v w := by
  simp only [det3Q, Pi.smul_apply, smul_eq_mul]; ring

open LocalCertificate (sub3Q det3Q) in
theorem sub_toQ_smul (a b : V3) (l : ℚ) (u v : Fin 3 → ℚ) (ha : a.toQ = l • u)
    (hb : b.toQ = l • v) : (V3.sub a b).toQ = l • sub3Q u v := by
  rw [V3.sub_toQ, ha, hb]; funext c; simp [sub3Q, mul_sub]

/-- One target test of `barycentricN`, transferred to the rational points. -/
theorem bary_target {D d0 d1 d2 : ℤ} {Dq e0 e1 e2 l : ℚ} (hl : 0 < l)
    (hD : (D : ℚ) = l ^ 3 * Dq) (h0 : (d0 : ℚ) = l ^ 3 * e0) (h1 : (d1 : ℚ) = l ^ 3 * e1)
    (h2 : (d2 : ℚ) = l ^ 3 * e2)
    (h : 0 ≤ d0 * D ∧ 0 ≤ d1 * D ∧ 0 ≤ d2 * D ∧ 0 ≤ (D - d0 - d1 - d2) * D) :
    0 ≤ e0 * Dq ∧ 0 ≤ e1 * Dq ∧ 0 ≤ e2 * Dq ∧ 0 ≤ (Dq - e0 - e1 - e2) * Dq := by
  have hl6 : (0 : ℚ) < l ^ 6 := by positivity
  have cast_nonneg : ∀ x : ℤ, 0 ≤ x → (0 : ℚ) ≤ x := fun x hx => by exact_mod_cast hx
  obtain ⟨a, b, c, d⟩ := h
  have a' := cast_nonneg _ a
  have b' := cast_nonneg _ b
  have c' := cast_nonneg _ c
  have d' := cast_nonneg _ d
  push_cast at a' b' c' d'
  rw [hD, h0] at a'
  rw [hD, h1] at b'
  rw [hD, h2] at c'
  rw [hD, h0, h1, h2] at d'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : l ^ 6 * (e0 * Dq) = l ^ 3 * e0 * (l ^ 3 * Dq) := by ring
    exact (mul_nonneg_iff_of_pos_left hl6).mp (this ▸ a')
  · have : l ^ 6 * (e1 * Dq) = l ^ 3 * e1 * (l ^ 3 * Dq) := by ring
    exact (mul_nonneg_iff_of_pos_left hl6).mp (this ▸ b')
  · have : l ^ 6 * (e2 * Dq) = l ^ 3 * e2 * (l ^ 3 * Dq) := by ring
    exact (mul_nonneg_iff_of_pos_left hl6).mp (this ▸ c')
  · have : l ^ 6 * ((Dq - e0 - e1 - e2) * Dq) =
        (l ^ 3 * Dq - l ^ 3 * e0 - l ^ 3 * e1 - l ^ 3 * e2) * (l ^ 3 * Dq) := by ring
    exact (mul_nonneg_iff_of_pos_left hl6).mp (this ▸ d')

open LocalCertificate (sub3Q det3Q) in
/-- One target of `barycentricN`, as a statement about the rational points. -/
theorem bary_one (P0 P1 P2 P3 tv : V3) (p : Fin 4 → Fin 3 → ℚ) (l s : ℚ) (hl : 0 < l)
    (h0 : P0.toQ = l • p 0) (h1 : P1.toQ = l • p 1) (h2 : P2.toQ = l • p 2)
    (h3 : P3.toQ = l • p 3) (k : Fin 6)
    (htv : tv.toQ = l • (s • LocalCertificate.octahedronAxis k))
    (h : 0 ≤ det3 (V3.sub tv P3) (V3.sub P1 P3) (V3.sub P2 P3) *
          det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub P2 P3) ∧
        0 ≤ det3 (V3.sub P0 P3) (V3.sub tv P3) (V3.sub P2 P3) *
          det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub P2 P3) ∧
        0 ≤ det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub tv P3) *
          det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub P2 P3) ∧
        0 ≤ (det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub P2 P3) -
            det3 (V3.sub tv P3) (V3.sub P1 P3) (V3.sub P2 P3) -
            det3 (V3.sub P0 P3) (V3.sub tv P3) (V3.sub P2 P3) -
            det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub tv P3)) *
          det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub P2 P3)) :
    let A := sub3Q (p 0) (p 3)
    let B := sub3Q (p 1) (p 3)
    let C := sub3Q (p 2) (p 3)
    let y := sub3Q (s • LocalCertificate.octahedronAxis k) (p 3)
    let D := det3Q A B C
    0 ≤ det3Q y B C * D ∧ 0 ≤ det3Q A y C * D ∧ 0 ≤ det3Q A B y * D ∧
      0 ≤ (D - det3Q y B C - det3Q A y C - det3Q A B y) * D := by
  intro A B C y D
  have ha := sub_toQ_smul _ _ _ _ _ h0 h3
  have hb := sub_toQ_smul _ _ _ _ _ h1 h3
  have hc := sub_toQ_smul _ _ _ _ _ h2 h3
  have hy := sub_toQ_smul _ _ _ _ _ htv h3
  apply bary_target hl (Dq := D)
    (by rw [det3_cast, ha, hb, hc, det3Q_smul]) (by rw [det3_cast, hy, hb, hc, det3Q_smul])
    (by rw [det3_cast, ha, hy, hc, det3Q_smul]) (by rw [det3_cast, ha, hb, hy, det3Q_smul]) h

open LocalCertificate (sub3Q det3Q) in
theorem barycentricN_sound (P0 P1 P2 P3 : V3) (target : ℤ) (p : Fin 4 → Fin 3 → ℚ)
    (l s : ℚ) (hl : 0 < l) (h0 : P0.toQ = l • p 0) (h1 : P1.toQ = l • p 1)
    (h2 : P2.toQ = l • p 2) (h3 : P3.toQ = l • p 3) (ht : (target : ℚ) = l * s)
    (h : barycentricN P0 P1 P2 P3 target = true) :
    baryProp (sub3Q (p 0) (p 3)) (sub3Q (p 1) (p 3)) (sub3Q (p 2) (p 3)) (p 3) s
      (det3Q (sub3Q (p 0) (p 3)) (sub3Q (p 1) (p 3)) (sub3Q (p 2) (p 3))) := by
  simp only [barycentricN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, k0⟩, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩ := h
  have ha := sub_toQ_smul _ _ _ _ _ h0 h3
  have hb := sub_toQ_smul _ _ _ _ _ h1 h3
  have hc := sub_toQ_smul _ _ _ _ _ h2 h3
  refine ⟨?_, fun k => ?_⟩
  · intro hz
    apply hD
    have : ((det3 (V3.sub P0 P3) (V3.sub P1 P3) (V3.sub P2 P3) : ℤ) : ℚ) = 0 := by
      rw [det3_cast, ha, hb, hc, det3Q_smul, hz, mul_zero]
    exact_mod_cast this
  · have tv : ∀ (x y z : ℤ) (u : Fin 3 → ℚ), (x : ℚ) = l * (s * u 0) → (y : ℚ) = l * (s * u 1) →
        (z : ℚ) = l * (s * u 2) → (⟨x, y, z⟩ : V3).toQ = l • (s • u) := by
      intro x y z u hx hy hz
      funext c; fin_cases c <;> simp [V3.toQ, hx, hy, hz]
    fin_cases k
    · exact bary_one _ _ _ _ _ p l s hl h0 h1 h2 h3 0
        (tv _ _ _ _ (by simp [ht]) (by simp) (by simp)) k0
    · exact bary_one _ _ _ _ _ p l s hl h0 h1 h2 h3 1
        (tv _ _ _ _ (by simp [ht]) (by simp) (by simp)) k1
    · exact bary_one _ _ _ _ _ p l s hl h0 h1 h2 h3 2
        (tv _ _ _ _ (by simp) (by simp [ht]) (by simp)) k2
    · exact bary_one _ _ _ _ _ p l s hl h0 h1 h2 h3 3
        (tv _ _ _ _ (by simp) (by simp [ht]) (by simp)) k3
    · exact bary_one _ _ _ _ _ p l s hl h0 h1 h2 h3 4
        (tv _ _ _ _ (by simp) (by simp) (by simp [ht])) k4
    · exact bary_one _ _ _ _ _ p l s hl h0 h1 h2 h3 5
        (tv _ _ _ _ (by simp) (by simp) (by simp [ht])) k5

/-! ### The fast barycentric test -/

theorem mul_nonneg_of_sameSign (x D : ℤ) (h : sameSign x D = true) : 0 ≤ x * D := by
  simp only [sameSign, decide_eq_true_eq] at h
  rcases lt_trichotomy D 0 with hD | hD | hD
  · exact mul_nonneg_of_nonpos_of_nonpos (h.2 hD) hD.le
  · simp [hD]
  · exact mul_nonneg (h.1 hD) hD.le

/-- One target of `barycentricN`, from the sign tests of `barycentricN2` on the
target's gradient components `g = (bc_m, ca_m, ab_m)`. -/
theorem ok_of_test (P0 P1 P2 P3 tv : V3) (g0 g1 g2 : ℤ)
    (hg0 : tv.x * (V3.cross (V3.sub P1 P3) (V3.sub P2 P3)).x +
        tv.y * (V3.cross (V3.sub P1 P3) (V3.sub P2 P3)).y +
        tv.z * (V3.cross (V3.sub P1 P3) (V3.sub P2 P3)).z = g0)
    (hg1 : tv.x * (V3.cross (V3.sub P2 P3) (V3.sub P0 P3)).x +
        tv.y * (V3.cross (V3.sub P2 P3) (V3.sub P0 P3)).y +
        tv.z * (V3.cross (V3.sub P2 P3) (V3.sub P0 P3)).z = g1)
    (hg2 : tv.x * (V3.cross (V3.sub P0 P3) (V3.sub P1 P3)).x +
        tv.y * (V3.cross (V3.sub P0 P3) (V3.sub P1 P3)).y +
        tv.z * (V3.cross (V3.sub P0 P3) (V3.sub P1 P3)).z = g2)
    (h : let D := V3.dot (V3.sub P0 P3) (V3.cross (V3.sub P1 P3) (V3.sub P2 P3))
      let x0 := g0 - V3.dot P3 (V3.cross (V3.sub P1 P3) (V3.sub P2 P3))
      let x1 := g1 - V3.dot P3 (V3.cross (V3.sub P2 P3) (V3.sub P0 P3))
      let x2 := g2 - V3.dot P3 (V3.cross (V3.sub P0 P3) (V3.sub P1 P3))
      ((sameSign x0 D = true ∧ sameSign x1 D = true) ∧ sameSign x2 D = true) ∧
        sameSign (D - x0 - x1 - x2) D = true) :
    let a := V3.sub P0 P3
    let b := V3.sub P1 P3
    let c := V3.sub P2 P3
    decide (0 ≤ det3 (V3.sub tv P3) b c * det3 a b c ∧
      0 ≤ det3 a (V3.sub tv P3) c * det3 a b c ∧ 0 ≤ det3 a b (V3.sub tv P3) * det3 a b c ∧
      0 ≤ (det3 a b c - det3 (V3.sub tv P3) b c - det3 a (V3.sub tv P3) c -
        det3 a b (V3.sub tv P3)) * det3 a b c) = true := by
  intro a b c
  have e0 : det3 (V3.sub tv P3) b c = g0 - V3.dot P3 (V3.cross b c) := by
    rw [← hg0]; simp only [b, c, det3, V3.dot, V3.cross, V3.sub, int_add_eq, int_sub_eq,
      int_mul_eq]; ring
  have e1 : det3 a (V3.sub tv P3) c = g1 - V3.dot P3 (V3.cross c a) := by
    rw [← hg1]; simp only [a, c, det3, V3.dot, V3.cross, V3.sub, int_add_eq, int_sub_eq,
      int_mul_eq]; ring
  have e2 : det3 a b (V3.sub tv P3) = g2 - V3.dot P3 (V3.cross a b) := by
    rw [← hg2]; simp only [a, b, det3, V3.dot, V3.cross, V3.sub, int_add_eq, int_sub_eq,
      int_mul_eq]; ring
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  rw [e0, e1, e2, decide_eq_true_eq]
  exact ⟨mul_nonneg_of_sameSign _ _ h0, mul_nonneg_of_sameSign _ _ h1,
    mul_nonneg_of_sameSign _ _ h2, mul_nonneg_of_sameSign _ _ h3⟩

theorem barycentricN2_imp (P0 P1 P2 P3 : V3) (T : ℤ)
    (h : barycentricN2 P0 P1 P2 P3 T = true) : barycentricN P0 P1 P2 P3 T = true := by
  simp only [barycentricN2, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hz, ⟨tx, tx'⟩⟩, ⟨ty, ty'⟩⟩, ⟨tz, tz'⟩⟩ := h
  unfold barycentricN
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hz, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ok_of_test P0 P1 P2 P3 _ _ _ _ (by simp) (by simp) (by simp) tx
  · exact ok_of_test P0 P1 P2 P3 _ _ _ _ (by simp) (by simp) (by simp) tx'
  · exact ok_of_test P0 P1 P2 P3 _ _ _ _ (by simp) (by simp) (by simp) ty
  · exact ok_of_test P0 P1 P2 P3 _ _ _ _ (by simp) (by simp) (by simp) ty'
  · exact ok_of_test P0 P1 P2 P3 _ _ _ _ (by simp) (by simp) (by simp) tz
  · exact ok_of_test P0 P1 P2 P3 _ _ _ _ (by simp) (by simp) (by simp) tz'

theorem gcdV3_dvd (a : V3) (g : ℕ) :
    gcdV3 a g ∣ g ∧ (gcdV3 a g : ℤ) ∣ a.x ∧ (gcdV3 a g : ℤ) ∣ a.y ∧ (gcdV3 a g : ℤ) ∣ a.z := by
  unfold gcdV3
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Nat.gcd_dvd_left _ _).trans ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  · exact Int.natAbs_dvd_natAbs.mp (by
      simpa using (Nat.gcd_dvd_left _ _).trans ((Nat.gcd_dvd_left _ _).trans
        (Nat.gcd_dvd_right _ _)))
  · exact Int.natAbs_dvd_natAbs.mp (by
      simpa using (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  · exact Int.natAbs_dvd_natAbs.mp (by simpa using Nat.gcd_dvd_right _ _)

theorem divV3_toQ (a : V3) (g : ℤ) (hg : g ≠ 0) (hx : g ∣ a.x) (hy : g ∣ a.y) (hz : g ∣ a.z)
    (l : ℚ) (u : Fin 3 → ℚ) (ha : a.toQ = l • u) : (divV3 a g).toQ = (l / g) • u := by
  have hx' := congrFun ha 0
  have hy' := congrFun ha 1
  have hz' := congrFun ha 2
  simp only [V3.toQ_zero, V3.toQ_one, V3.toQ_two, Pi.smul_apply, smul_eq_mul] at hx' hy' hz'
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  funext c
  fin_cases c <;>
    simp [divV3, V3.toQ, Int.cast_div hx hgq, Int.cast_div hy hgq, Int.cast_div hz hgq, hx',
      hy', hz'] <;> field_simp

open LocalCertificate (sub3Q det3Q) in
theorem barycentricN3_sound (P0 P1 P2 P3 : V3) (target : ℤ) (p : Fin 4 → Fin 3 → ℚ)
    (l s : ℚ) (hl : 0 < l) (h0 : P0.toQ = l • p 0) (h1 : P1.toQ = l • p 1)
    (h2 : P2.toQ = l • p 2) (h3 : P3.toQ = l • p 3) (ht : (target : ℚ) = l * s)
    (h : barycentricN3 P0 P1 P2 P3 target = true) :
    baryProp (sub3Q (p 0) (p 3)) (sub3Q (p 1) (p 3)) (sub3Q (p 2) (p 3)) (p 3) s
      (det3Q (sub3Q (p 0) (p 3)) (sub3Q (p 1) (p 3)) (sub3Q (p 2) (p 3))) := by
  simp only [barycentricN3] at h
  split_ifs at h with hg
  · exact barycentricN_sound _ _ _ _ _ p l s hl h0 h1 h2 h3 ht (barycentricN2_imp _ _ _ _ _ h)
  · set g := gcdV3 P3 (gcdV3 P2 (gcdV3 P1 (gcdV3 P0 target.natAbs))) with hgdef
    obtain ⟨d3, x3, y3, z3⟩ := gcdV3_dvd P3 (gcdV3 P2 (gcdV3 P1 (gcdV3 P0 target.natAbs)))
    obtain ⟨d2, x2, y2, z2⟩ := gcdV3_dvd P2 (gcdV3 P1 (gcdV3 P0 target.natAbs))
    obtain ⟨d1, x1, y1, z1⟩ := gcdV3_dvd P1 (gcdV3 P0 target.natAbs)
    obtain ⟨d0, x0, y0, z0⟩ := gcdV3_dvd P0 target.natAbs
    have c2 : (g : ℤ) ∣ ((gcdV3 P2 (gcdV3 P1 (gcdV3 P0 target.natAbs)) : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr d3
    have c1 : (g : ℤ) ∣ ((gcdV3 P1 (gcdV3 P0 target.natAbs) : ℕ) : ℤ) :=
      c2.trans (Int.natCast_dvd_natCast.mpr d2)
    have c0 : (g : ℤ) ∣ ((gcdV3 P0 target.natAbs : ℕ) : ℤ) :=
      c1.trans (Int.natCast_dvd_natCast.mpr d1)
    have cT : (g : ℤ) ∣ target := by
      have : (g : ℤ) ∣ ((target.natAbs : ℕ) : ℤ) := c0.trans (Int.natCast_dvd_natCast.mpr d0)
      exact Int.dvd_natAbs.mp (by simpa using this)
    have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg
    have hgpos : (0 : ℚ) < (g : ℤ) := by positivity
    have hl' : 0 < l / ((g : ℤ) : ℚ) := div_pos hl hgpos
    refine barycentricN_sound _ _ _ _ _ p (l / ((g : ℤ) : ℚ)) s hl'
      (divV3_toQ _ _ hgz (c0.trans x0) (c0.trans y0) (c0.trans z0) _ _ h0)
      (divV3_toQ _ _ hgz (c1.trans x1) (c1.trans y1) (c1.trans z1) _ _ h1)
      (divV3_toQ _ _ hgz (c2.trans x2) (c2.trans y2) (c2.trans z2) _ _ h2)
      (divV3_toQ _ _ hgz x3 y3 z3 _ _ h3) ?_ (barycentricN2_imp _ _ _ _ _ h)
    rw [Int.cast_div cT (by exact_mod_cast hgz), ht]
    ring

/-! ## The whole check -/

theorem rootSign_num_cast (root : Fin 8) (c : Fin 3) :
    (((AtlasProjectiveView.rootSign root c : ℚ).num : ℤ) : ℚ) =
      AtlasProjectiveView.rootSign root c := by
  fin_cases root <;> fin_cases c <;> rfl

theorem triOkN_sound (root : Fin 8) (L : ℕ) (hL : 0 < L) (p : V3) (t : Fin 3 → ℚ)
    (hp : p.toQ = (L : ℚ) • t) (h : triOkN root L p = true) :
    (∀ c, 0 ≤ AtlasProjectiveView.rootSign root c * t c) ∧
      (∑ c, AtlasProjectiveView.rootSign root c * t c) = 1 := by
  obtain ⟨hx, hy, hz⟩ := toQ_comp _ _ _ hp
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  simp only [triOkN, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2, hs⟩ := h
  have c0 : (0 : ℚ) ≤ ((AtlasProjectiveView.rootSign root 0 : ℚ).num : ℚ) * p.x := by
    exact_mod_cast h0
  have c1 : (0 : ℚ) ≤ ((AtlasProjectiveView.rootSign root 1 : ℚ).num : ℚ) * p.y := by
    exact_mod_cast h1
  have c2 : (0 : ℚ) ≤ ((AtlasProjectiveView.rootSign root 2 : ℚ).num : ℚ) * p.z := by
    exact_mod_cast h2
  have cs : (((AtlasProjectiveView.rootSign root 0 : ℚ).num : ℚ) * p.x +
      ((AtlasProjectiveView.rootSign root 1 : ℚ).num : ℚ) * p.y +
      ((AtlasProjectiveView.rootSign root 2 : ℚ).num : ℚ) * p.z) = (L : ℚ) := by
    exact_mod_cast hs
  rw [rootSign_num_cast, hx] at c0
  rw [rootSign_num_cast, hy] at c1
  rw [rootSign_num_cast, hz] at c2
  rw [rootSign_num_cast, rootSign_num_cast, rootSign_num_cast, hx, hy, hz] at cs
  refine ⟨fun c => ?_, ?_⟩
  · match c with
    | 0 => exact (mul_nonneg_iff_of_pos_left hLq).mp (by linarith)
    | 1 => exact (mul_nonneg_iff_of_pos_left hLq).mp (by linarith)
    | 2 => exact (mul_nonneg_iff_of_pos_left hLq).mp (by linarith)
  · rw [Fin.sum_univ_three]
    have : (L : ℚ) * (AtlasProjectiveView.rootSign root 0 * t 0 +
        AtlasProjectiveView.rootSign root 1 * t 1 + AtlasProjectiveView.rootSign root 2 * t 2) =
        L * 1 := by linarith
    exact mul_left_cancel₀ hLq.ne' this

theorem axis_center_rel (box : Box) (L : ℕ) (hL : 0 < L) (t0 t1 t2 : V3)
    (ht0 : t0.toQ = (L : ℚ) • box.triangle 0) (ht1 : t1.toQ = (L : ℚ) • box.triangle 1)
    (ht2 : t2.toQ = (L : ℚ) • box.triangle 2) (j : Fin 4) :
    (axisN box (L : ℤ) t0 t1 t2 (boxNOf t0 t1 t2) j).center.toQ =
      (4 * (L : ℚ) ^ 2 * ((40000 * 40000) * (40 * 40000))) •
        fun c => (box.variationBall j c).center := by
  have hK : (0 : ℚ) < (40000 * 40000) * (40 * 40000) := by norm_num
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  obtain ⟨hmx, hmy, hmz, hrx, hry, hrz⟩ := boxNOf_rel box L t0 t1 t2 ht0 ht1 ht2
  have br := fun c => (ballN_rel (qN box j c) _ hK _ (qN_rel box j c) (boxNOf t0 t1 t2)
    (L : ℚ) hLq box.triangleBalls hmx hmy hmz hrx hry hrz).1
  have hc : (axisN box (L : ℤ) t0 t1 t2 (boxNOf t0 t1 t2) j).center =
      ⟨(ballN (qN box j 0) (boxNOf t0 t1 t2)).1, (ballN (qN box j 1) (boxNOf t0 t1 t2)).1,
        (ballN (qN box j 2) (boxNOf t0 t1 t2)).1⟩ := rfl
  rw [hc]
  funext c
  fin_cases c <;> simp [V3.toQ, br, Box.variationBall]

/-- The integer local view check implies the specification. -/
theorem viewValidN_sound (box : Box) (h : viewValidN box = true) : box.ViewValid := by
  have hL := lcm9_pos box.triangle
  have ht0 := triRow_toQ box.triangle 0
  have ht1 := triRow_toQ box.triangle 1
  have ht2 := triRow_toQ box.triangle 2
  unfold viewValidN viewValidCore at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hT0⟩, hT1⟩, hT2⟩, ⟨hc, hδ, hr⟩⟩, ho0⟩, ho1⟩, ho2⟩, ho3⟩, hbary⟩,
    hang⟩ := h
  have ax : ∀ j : Fin 4, AxisFacts box j := by
    intro j
    fin_cases j
    · exact axisN_sound box _ hL _ _ _ ht0 ht1 ht2 0 ho0
    · exact axisN_sound box _ hL _ _ _ ht0 ht1 ht2 1 ho1
    · exact axisN_sound box _ hL _ _ _ ht0 ht1 ht2 2 ho2
    · exact axisN_sound box _ hL _ _ _ ht0 ht1 ht2 3 ho3
  refine ⟨?_, hc, hδ, hr, fun j => (ax j).1, fun j => (ax j).2.1, fun j => (ax j).2.2.1,
    fun j => (ax j).2.2.2.1, fun j => (ax j).2.2.2.2.1, fun j => (ax j).2.2.2.2.2.1,
    fun j => (ax j).2.2.2.2.2.2, ?_, hang⟩
  · intro i
    match i with
    | 0 => exact triOkN_sound _ _ hL _ _ ht0 hT0
    | 1 => exact triOkN_sound _ _ hL _ _ ht1 hT1
    | 2 => exact triOkN_sound _ _ hL _ _ ht2 hT2
  · -- barycentric
    have hBn : ∀ j : Fin 4, (0 : ℚ) < ((box.certificate j).B.num : ℚ) := fun j => by
      exact_mod_cast Rat.num_pos.mpr (ax j).1
    have hBd : ∀ j : Fin 4, (0 : ℚ) < ((box.certificate j).B.den : ℚ) := fun j => by
      exact_mod_cast (box.certificate j).B.den_pos
    have hsd : (0 : ℚ) < ((7 / 4 * (box.c + box.δ) : ℚ).den : ℚ) := by
      exact_mod_cast (7 / 4 * (box.c + box.δ) : ℚ).den_pos
    set A : ℚ := 4 * ((lcm9 box.triangle : ℕ) : ℚ) ^ 2 * ((40000 * 40000) * (40 * 40000)) with hA
    have hApos : 0 < A := by rw [hA]; positivity
    set l : ℚ := A * ((box.certificate 0).B.num * (box.certificate 1).B.num *
      (box.certificate 2).B.num * (box.certificate 3).B.num) *
      ((7 / 4 * (box.c + box.δ) : ℚ).den : ℚ) with hl
    have hlpos : 0 < l := by
      rw [hl]; have := hBn 0; have := hBn 1; have := hBn 2; have := hBn 3; positivity
    have hcen := fun j => axis_center_rel box _ hL _ _ _ ht0 ht1 ht2 j
    have hpt : ∀ (j : Fin 4) (k : ℤ),
        (k : ℚ) * A = l / (box.certificate j).B →
        (V3.smul k (axisN box ((lcm9 box.triangle : ℕ) : ℤ) (triRow (lcm9 box.triangle)
          box.triangle 0) (triRow (lcm9 box.triangle) box.triangle 1)
          (triRow (lcm9 box.triangle) box.triangle 2) (boxNOf (triRow (lcm9 box.triangle)
          box.triangle 0) (triRow (lcm9 box.triangle) box.triangle 1)
          (triRow (lcm9 box.triangle) box.triangle 2)) j).center).toQ =
          l • box.approxNormalizedCenter j := by
      intro j k hk
      rw [V3.smul_toQ, hcen j]
      funext c
      have hB : (box.certificate j).B ≠ 0 := (ax j).1.ne'
      simp only [Pi.smul_apply, smul_eq_mul, Box.approxNormalizedCenter]
      rw [← mul_assoc, hk]
      field_simp
    have hB : ∀ j : Fin 4, (box.certificate j).B =
        ((box.certificate j).B.num : ℚ) / ((box.certificate j).B.den : ℚ) := fun j =>
      (Rat.num_div_den _).symm
    have hdiv : ∀ j : Fin 4, l / (box.certificate j).B =
        l * ((box.certificate j).B.den : ℚ) / ((box.certificate j).B.num : ℚ) := by
      intro j
      conv_lhs => rw [← Rat.num_div_den (box.certificate j).B]
      rw [div_div_eq_mul_div]
    apply (Box.barycentricWith_iff_bary box _).mpr
    refine barycentricN3_sound _ _ _ _ _ _ l _ hlpos ?_ ?_ ?_ ?_ ?_ hbary
    · apply hpt 0
      rw [hdiv 0, eq_div_iff (hBn 0).ne', hl]
      push_cast
      ring
    · apply hpt 1
      rw [hdiv 1, eq_div_iff (hBn 1).ne', hl]
      push_cast
      ring
    · apply hpt 2
      rw [hdiv 2, eq_div_iff (hBn 2).ne', hl]
      push_cast
      ring
    · apply hpt 3
      rw [hdiv 3, eq_div_iff (hBn 3).ne', hl]
      push_cast
      ring
    · have hsn := Rat.mul_den_eq_num (7 / 4 * (box.c + box.δ) : ℚ)
      rw [hl, show A * ((box.certificate 0).B.num * (box.certificate 1).B.num *
          (box.certificate 2).B.num * (box.certificate 3).B.num) *
          ((7 / 4 * (box.c + box.δ) : ℚ).den : ℚ) * (7 / 4 * (box.c + box.δ)) =
        A * ((box.certificate 0).B.num * (box.certificate 1).B.num *
          (box.certificate 2).B.num * (box.certificate 3).B.num) *
          ((7 / 4 * (box.c + box.δ)) * ((7 / 4 * (box.c + box.δ) : ℚ).den : ℚ)) by ring, hsn, hA]
      push_cast
      ring

end Noperts.Stellated.LocalKernel
