module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Noperts.Basic
public import Noperts.Bounding.OpNorm

@[expose] public section


/-!

Material for [SY25] Lemma 10 and Lemma 12.

-/

namespace Bounding
open Real

/-- The diagonal matrix of the projection onto the coordinate plane perpendicular to axis `d`. -/
noncomputable def projPerp_mat (d : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun i => if i = d then 0 else 1

/-- The orthogonal projection of `ℝ³` onto the coordinate plane perpendicular to axis `d`. -/
noncomputable def projPerpL (d : Fin 3) : ℝ³ →L[ℝ] ℝ³ :=
  (projPerp_mat d).toEuclideanLin.toContinuousLinearMap

lemma projPerpL_apply (d : Fin 3) (v : ℝ³) (i : Fin 3) :
    projPerpL d v i = if i = d then 0 else v i := by
  simp [projPerpL, projPerp_mat, Matrix.mulVec_diagonal, ite_mul]

lemma projPerpL_norm_one (d : Fin 3) : ‖projPerpL d‖ = 1 := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun v => ?_) (fun N _ h => ?_)
  · rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [projPerpL_apply]
    split
    · simpa using sq_nonneg _
    · exact le_rfl
  · obtain ⟨j, hj⟩ := exists_ne d
    have h2 : projPerpL d (EuclideanSpace.single j 1) = EuclideanSpace.single j 1 := by
      ext i
      rw [projPerpL_apply]
      rcases eq_or_ne i d with rfl | hi
      · simp [hj.symm]
      · simp [hi]
    have h1 := h (EuclideanSpace.single j 1)
    rw [h2] at h1
    simpa using h1

/-- The difference of two rotation matrices about axis `d` is a scalar multiple of a rotation
matrix times the projection onto the plane of rotation. -/
lemma rot3_mat_sub_rot3_mat (d : Fin 3) (α α' : ℝ) :
    rot3_mat d α - rot3_mat d α' =
      (2 * sin ((α - α') / 2)) • (rot3_mat d ((α + α') / 2 + π / 2) * projPerp_mat d) := by
  fin_cases d
  all_goals (
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rot3_mat, Rx_mat, Fin.zero_eta, Fin.isValue, Matrix.sub_apply, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, sub_self,
        cos_add_pi_div_two, sin_add_pi_div_two, projPerp_mat, Matrix.cons_mul,
        Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.empty_mul, Equiv.symm_apply_apply,
        Matrix.smul_apply, Matrix.vecMul_diagonal, ↓reduceIte, mul_zero, smul_eq_mul,
        Fin.mk_one, Matrix.cons_val_one, one_ne_zero, mul_one, Fin.reduceFinMk,
        Matrix.cons_val, Fin.reduceEq, mul_neg, sub_neg_eq_add, Ry_mat, zero_ne_one,
        Rz_mat])
  · linear_combination cos_sub_cos α α'
  · linear_combination -sin_sub_sin α α'
  · linear_combination sin_sub_sin α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination -sin_sub_sin α α'
  · linear_combination sin_sub_sin α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination cos_sub_cos α α'
  · linear_combination -sin_sub_sin α α'
  · linear_combination sin_sub_sin α α'
  · linear_combination cos_sub_cos α α'

/-- The difference of two rotations about axis `d` is a scalar multiple of a rotation
composed with the projection onto the plane of rotation. -/
lemma rot3_sub_rot3 (d : Fin 3) (α α' : ℝ) :
    (rot3 d α : ℝ³ →L[ℝ] ℝ³) - rot3 d α' =
      (2 * sin ((α - α') / 2)) • ((rot3 d ((α + α') / 2 + π / 2) : ℝ³ →L[ℝ] ℝ³) ∘L projPerpL d) := by
  have hmul : ((rot3_mat d ((α + α') / 2 + π / 2) * projPerp_mat d).toEuclideanLin).toContinuousLinearMap
      = ((rot3_mat d ((α + α') / 2 + π / 2)).toEuclideanLin).toContinuousLinearMap ∘L projPerpL d := by
    ext v
    simp [projPerpL]
  have e : ∀ θ : ℝ, (rot3 d θ : ℝ³ →L[ℝ] ℝ³) = (rot3_mat d θ).toEuclideanLin.toContinuousLinearMap := by
    intro θ
    fin_cases d <;> rfl
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.toEuclideanLin.toContinuousLinearMap)
    (rot3_mat_sub_rot3_mat d α α')
  simp only [map_sub, map_smul, hmul] at h
  rw [e, e, e]
  exact h

theorem dist_rot3 {d : Fin 3} {α α' : ℝ} :
  ‖rot3 d α - rot3 d α'‖ = 2 * |sin ((α - α') / 2)| := by
    rw [rot3_sub_rot3, norm_smul, rot3_preserves_op_norm, projPerpL_norm_one, mul_one,
      Real.norm_eq_abs, abs_mul, abs_two]

end Bounding

end
