module

public import Noperts.Stellated.AtlasPose
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# From reduced matrix poses to reduced atlas poses

A reduced pose (`MatrixPose.StellatedReduced`) is rotated in the screen so
that its outer rotation has Euler form `rotRM θ φ 0`.  The tetrahedral part of
its Dirichlet condition puts the relative rotation in Cayley chart zero, inside
the octahedron `|x| + |y| + |z| ≤ 1`.
-/

namespace Noperts.Stellated

open scoped Matrix
open CayleyAtlas

private theorem le_one_of_factored {v : ℝ} (h : (v - 1) * (v + 3) ≤ 0) :
    v ≤ 1 := by
  by_contra hc
  push Not at hc
  have := mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < v + 3)
  linarith

/-- The tetrahedral Dirichlet inequalities in chart zero give the
octahedron `|x| + |y| + |z| ≤ 1`. -/
theorem octahedron_of_dirichlet {x y z : ℝ}
    (h : ∀ b : SymIndex, isFlip b = false →
      Matrix.trace (cayleyMatrix x y z * symReal b) ≤
        Matrix.trace (cayleyMatrix x y z)) :
    |x| + |y| + |z| ≤ 1 := by
  have hd := cayleyDenom_pos x y z
  have key : ∀ b : SymIndex, isFlip b = false →
      (cayleyDenom x y z) * Matrix.trace (cayleyMatrix x y z * symReal b) ≤
        (cayleyDenom x y z) * Matrix.trace (cayleyMatrix x y z) :=
    fun b hb => mul_le_mul_of_nonneg_left (h b hb) hd.le
  have k4 := key 4 rfl
  have k5 := key 5 rfl
  have k6 := key 6 rfl
  have k7 := key 7 rfl
  have k8 := key 8 rfl
  have k9 := key 9 rfl
  have k10 := key 10 rfl
  have k11 := key 11 rfl
  simp only [symReal, symMatrix_4, symMatrix_5, symMatrix_6, symMatrix_7,
    symMatrix_8, symMatrix_9, symMatrix_10, symMatrix_11, cayleyMatrix,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.map_apply] at k4 k5 k6 k7 k8 k9 k10 k11
  simp at k4 k5 k6 k7 k8 k9 k10 k11
  field_simp at k4 k5 k6 k7 k8 k9 k10 k11
  have l4 : x + y + z ≤ 1 :=
    le_one_of_factored (by linear_combination k4)
  have l5 : -x - y + z ≤ 1 :=
    le_one_of_factored (by linear_combination k5)
  have l6 : x - y - z ≤ 1 :=
    le_one_of_factored (by linear_combination k6)
  have l7 : -x + y - z ≤ 1 :=
    le_one_of_factored (by linear_combination k7)
  have l8 : -x - y - z ≤ 1 :=
    le_one_of_factored (by linear_combination k8)
  have l9 : x - y + z ≤ 1 :=
    le_one_of_factored (by linear_combination k9)
  have l10 : x + y - z ≤ 1 :=
    le_one_of_factored (by linear_combination k10)
  have l11 : -x + y + z ≤ 1 :=
    le_one_of_factored (by linear_combination k11)
  rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩ <;>
    rcases abs_cases y with ⟨hy, -⟩ | ⟨hy, -⟩ <;>
    rcases abs_cases z with ⟨hz, -⟩ | ⟨hz, -⟩ <;>
    linarith

/-- The tetrahedral Dirichlet inequalities against the three chart
half-turns force a nonnegative trace, i.e. chart zero. -/
theorem trace_nonneg_of_dirichlet {R : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ b : SymIndex, isFlip b = false →
      Matrix.trace (R * symReal b) ≤ Matrix.trace R) :
    0 ≤ Matrix.trace R := by
  have h1 := h 1 rfl
  have h2 := h 2 rfl
  have h3 := h 3 rfl
  simp only [symReal, symMatrix_1, symMatrix_2, symMatrix_3, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.map_apply] at h1 h2 h3
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  simp at h1 h2 h3
  linarith

private theorem Rz_mul_rotRM_mat (δ θ φ α : ℝ) :
    Rz_mat δ * rotRM_mat θ φ α = rotRM_mat θ φ (δ + α) := by
  simp only [rotRM_mat, ← Matrix.mul_assoc, Bounding.Rz_mat_mul_Rz_mat]
  congr 3
  ring

private theorem Rz_transpose_mul_self (δ : ℝ) : (Rz_mat δ)ᵀ * Rz_mat δ = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp (MatrixPose.Rz_mat_mem_SO3 δ)).1

private theorem Rz_conj_screenHalfTurn (δ : ℝ) :
    (Rz_mat δ)ᵀ * symReal screenHalfTurn * Rz_mat δ = symReal screenHalfTurn := by
  rw [symReal_screenHalfTurn]
  have h := Real.sin_sq_add_cos_sq δ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz_mat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination h
      | linear_combination -h

private theorem chartMatrix_zero : chartMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartMatrix]

/-- A reduced Rupert matrix pose yields a reduced Rupert atlas pose in
chart zero. -/
theorem exists_reduced_atlas_pose (p : MatrixPose)
    (hred : p.StellatedReduced) (hp : RupertPose p exactPolyhedron.hull) :
    ∃ q ∈ AtlasPose.rootInterval ℝ, q.Reduced ∧ ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  obtain ⟨hview, hdir⟩ := hred
  obtain ⟨θ, φ, α, hθ, hφ, -, hO⟩ :=
    Noperts.SO3_to_bounded_rotRM_params
      p.outerRot.val p.outerRot.property
  set rel := p.relativeRotation with hrel
  have hT : ∀ b : SymIndex, isFlip b = false →
      Matrix.trace (rel * symReal b) ≤ Matrix.trace rel := by
    intro b hb
    simpa [relAct, hb] using hdir b
  obtain ⟨x, y, z, -, hxyz⟩ := exists_cayleyMatrix_of_trace_nonneg rel
    (Noperts.MatrixPose.relativeRotation_mem_SO3 p) (trace_nonneg_of_dirichlet hT)
  have hoct : |x| + |y| + |z| ≤ 1 :=
    octahedron_of_dirichlet (fun b hb => by rw [← hxyz]; exact hT b hb)
  let q : AtlasPose ℝ := { θ := θ, φ := φ, x := x, y := y, z := z }
  have hqview : q.view = poseView p := by
    funext c
    simp only [q, AtlasPose.view, poseView, hO, rotRM_mat_row_two]
  have hHalf : q.viewHalfTurn = poseViewHalfTurn p := by
    have h0 : rotRM_mat θ φ 0 = Rz_mat (-α) * rotRM_mat θ φ α := by
      rw [Rz_mul_rotRM_mat]; congr 1; ring
    simp only [q, AtlasPose.viewHalfTurn, poseViewHalfTurn, hO, h0,
      Matrix.transpose_mul]
    calc (rotRM_mat θ φ α)ᵀ * (Rz_mat (-α))ᵀ * symReal screenHalfTurn *
          (Rz_mat (-α) * rotRM_mat θ φ α) =
        (rotRM_mat θ φ α)ᵀ * ((Rz_mat (-α))ᵀ * symReal screenHalfTurn *
          Rz_mat (-α)) * rotRM_mat θ φ α := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Rz_conj_screenHalfTurn]
  have hchamber : InChamber (poseView p) := hview
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (8 / 5) := by
    have hc := hchamber
    rw [← hqview] at hc
    obtain ⟨h10, h21, h2⟩ := hc
    simp only [q, AtlasPose.view, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h10 h21 h2
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2
    have hsinφpos : 0 < Real.sin φ := by
      rcases hsinφ.eq_or_lt with h0 | h0
      · have hcos := Real.sin_sq_add_cos_sq φ
        rw [← h0] at hcos h21
        nlinarith
      · exact h0
    have hsinθ : 0 ≤ Real.sin θ := by
      by_contra hneg
      push Not at hneg
      nlinarith [mul_neg_of_neg_of_pos hneg hsinφpos]
    have hcosθ : 0 ≤ Real.cos θ := by
      by_contra hneg
      push Not at hneg
      have : Real.cos θ * Real.sin φ < 0 := mul_neg_of_neg_of_pos hneg hsinφpos
      nlinarith [mul_nonneg hsinθ hsinφ]
    constructor
    · by_contra hneg
      push Not at hneg
      exact absurd hsinθ (not_le.2
        (Real.sin_neg_of_neg_of_neg_pi_lt hneg hθ.1))
    · by_contra hbig
      push Not at hbig
      have hpi := Real.pi_lt_d2
      have : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
        (by linarith) (by linarith [hθ.2])
      linarith
  have habs : ∀ t : ℝ, |t| ≤ 1 → -1 ≤ t ∧ t ≤ 1 := fun t ht => abs_le.mp ht
  have hx := habs x (by linarith [abs_nonneg y, abs_nonneg z])
  have hy := habs y (by linarith [abs_nonneg x, abs_nonneg z])
  have hz := habs z (by linarith [abs_nonneg x, abs_nonneg y])
  refine ⟨q, ?_, ⟨?_, hoct, ?_⟩, rotR (-α) p.innerOffset, ?_⟩
  · rw [NonemptyInterval.mem_def, AtlasPose.le_iff, AtlasPose.le_iff]
    dsimp only [q, AtlasPose.rootInterval]
    have hpi4 := Real.pi_le_four
    exact ⟨⟨hθ'.1, hφ.1, hx.1, hy.1, hz.1⟩,
      ⟨hθ'.2, hφ.2.trans hpi4, hx.2, hy.2, hz.2⟩⟩
  · change InChamber q.view
    rw [hqview]; exact hchamber
  · intro b _
    rw [hHalf, ← hxyz]
    exact hdir b
  · have hrot := (MatrixPose.RupertPose_rotateBy_iff p (-α) _).mpr hp
    convert hrot using 1
    have hO0 : rotRM_mat θ φ 0 = Rz_mat (-α) * p.outerRot.val := by
      rw [hO, Rz_mul_rotRM_mat]; congr 1; ring
    apply matrixPose_ext_val
    · change rotRM_mat θ φ 0 * chartMatrix 0 * cayleyMatrix x y z =
        Rz_mat (-α) * p.innerRot.val
      rw [chartMatrix_zero, Matrix.mul_one, ← hxyz, hrel, hO0,
        MatrixPose.relativeRotation, Matrix.mul_assoc,
        ← Matrix.mul_assoc p.outerRot.val, orthogonal_of_SO3, Matrix.one_mul]
    · exact hO0
    · rfl

end Noperts.Stellated

end
