module

public import Noperts.Stellated.Symmetry
public import Noperts.PoseClasses
public import Noperts.MatrixPose

@[expose] public section

/-!
# Rupert-preserving symmetry moves

Right multiplication of either rotation by an element `g ∈ T` does not change
the corresponding shadow.  An element `g ∈ O \ T` negates the solid, so it
negates the shadow; composing on the left with the screen half-turn
`diag(-1,-1,1)` (which negates every projection) restores it.  Hence for
every `g ∈ O` the move `R ↦ H^[g ∉ T] * R * g` preserves the shadow exactly,
where `H` is the screen half-turn.
-/

namespace Noperts.Stellated

open scoped Matrix Pointwise

noncomputable def symReal (g : SymIndex) : Matrix (Fin 3) (Fin 3) ℝ :=
  (symMatrix g).map (Rat.castHom ℝ)

theorem symReal_mul (g h : SymIndex) :
    symReal g * symReal h = symReal (symMul g h) := by
  rw [symReal, symReal, ← Matrix.map_mul, symMatrix_mul]
  rfl

theorem symReal_mem_SO3 (g : SymIndex) :
    symReal g ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · rw [symReal, ← Matrix.transpose_map, ← Matrix.map_mul,
      symMatrix_mul_transpose, Matrix.map_one _ (map_zero _) (map_one _)]
  · change ((Rat.castHom ℝ).mapMatrix (symMatrix g)).det = 1
    rw [← RingHom.map_det, symMatrix_det, map_one]

noncomputable def symSO3 (g : SymIndex) : SO3 :=
  ⟨symReal g, symReal_mem_SO3 g⟩

theorem symReal_apply_exactVertex (g : SymIndex) (i : VertexIndex) :
    (symReal g).toEuclideanLin (exactVertex i) =
      ((symSign g : ℚ) : ℝ) • exactVertex (symAction g i) := by
  have h := congrArg (fun v : Fin 3 → ℚ => toR3 v)
    (symMatrix_mulVec_rationalVertex g i)
  ext c
  have hc := congrArg (fun v : ℝ³ => v c) h
  simp only [toR3] at hc
  simp only [exactVertex, toR3, Matrix.toLpLin_apply, symReal,
    PiLp.smul_apply, smul_eq_mul]
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum,
    Rat.cast_mul] using hc

theorem symAction_bijective (g : SymIndex) :
    Function.Bijective (symAction g) := by
  rw [← Finite.injective_iff_bijective]
  revert g
  decide

/-- The screen half-turn `Rz(π) = diag(-1,-1,1)`, which is `symMatrix 3`. -/
abbrev screenHalfTurn : SymIndex := 3

theorem symReal_screenHalfTurn :
    symReal screenHalfTurn = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  have h : symMatrix screenHalfTurn = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symReal, h]

theorem proj_screenHalfTurn (v : ℝ³) :
    proj_xyL ((symReal screenHalfTurn).toEuclideanLin v) = -proj_xyL v := by
  rw [symReal_screenHalfTurn]
  ext c
  fin_cases c <;>
    simp [proj_xyL, proj_xy_mat, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_three]

theorem symReal_image_hull (g : SymIndex) :
    (symReal g).toEuclideanLin '' exactPolyhedron.hull =
      ((symSign g : ℚ) : ℝ) • exactPolyhedron.hull := by
  rw [Polyhedron.hull, LinearMap.image_convexHull, ← convexHull_smul]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨exactPolyhedron.v (symAction g i), ⟨_, rfl⟩,
      (symReal_apply_exactVertex g i).symm⟩
  · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (symAction_bijective g).2 j
    exact ⟨exactPolyhedron.v i, ⟨i, rfl⟩, symReal_apply_exactVertex g i⟩

/-- The shadow-preserving move attached to `g ∈ O`. -/
noncomputable def moveMatrix (g : SymIndex) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (if isFlip g then symReal screenHalfTurn else 1) * R * symReal g

theorem moveMatrix_mem_SO3 (g : SymIndex) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    moveMatrix g R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  unfold moveMatrix
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ hR) (symReal_mem_SO3 g)
  split_ifs
  · exact symReal_mem_SO3 _
  · exact Submonoid.one_mem _

theorem proj_image_moveMatrix (g : SymIndex) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    (fun v => proj_xyL ((moveMatrix g R).toEuclideanLin v)) ''
        exactPolyhedron.hull =
      (fun v => proj_xyL (R.toEuclideanLin v)) '' exactPolyhedron.hull := by
  have hsplit : ∀ v, (moveMatrix g R).toEuclideanLin v =
      (if isFlip g then symReal screenHalfTurn else 1).toEuclideanLin
        (R.toEuclideanLin ((symReal g).toEuclideanLin v)) := by
    intro v
    simp [moveMatrix, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  simp_rw [hsplit]
  rw [show (fun v => proj_xyL ((if isFlip g then symReal screenHalfTurn else 1).toEuclideanLin
        (R.toEuclideanLin ((symReal g).toEuclideanLin v)))) =
      (fun w => proj_xyL ((if isFlip g then symReal screenHalfTurn else 1).toEuclideanLin
        (R.toEuclideanLin w))) ∘ (symReal g).toEuclideanLin from rfl,
    Set.image_comp, symReal_image_hull]
  unfold symSign
  split_ifs with hflip
  · ext x
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨w, hw, ?_⟩
      simp [proj_screenHalfTurn]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨-w, ⟨w, hw, by simp⟩, ?_⟩
      simp [proj_screenHalfTurn]
  · simp

/-- Apply the move `a` to the outer rotation and `b` to the inner rotation. -/
noncomputable def _root_.MatrixPose.stellatedMove (p : MatrixPose)
    (a b : SymIndex) : MatrixPose where
  outerRot := ⟨moveMatrix a p.outerRot.val,
    moveMatrix_mem_SO3 a p.outerRot.property⟩
  innerRot := ⟨moveMatrix b p.innerRot.val,
    moveMatrix_mem_SO3 b p.innerRot.property⟩
  innerOffset := p.innerOffset

theorem innerShadow_stellatedMove (p : MatrixPose) (a b : SymIndex) :
    innerShadow (p.stellatedMove a b) exactPolyhedron.hull =
      innerShadow p exactPolyhedron.hull := by
  have key := proj_image_moveMatrix b p.innerRot.val
  rw [MatrixPose.inner_shadow_lemma, MatrixPose.inner_shadow_lemma]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hmem : proj_xyL ((moveMatrix b p.innerRot.val).toEuclideanLin v) ∈
        (fun v => proj_xyL (p.innerRot.val.toEuclideanLin v)) ''
          exactPolyhedron.hull := key ▸ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hmem
    exact ⟨w, hw, by simp [MatrixPose.stellatedMove, hwv]⟩
  · rintro ⟨v, hv, rfl⟩
    have hmem : proj_xyL (p.innerRot.val.toEuclideanLin v) ∈
        (fun v => proj_xyL ((moveMatrix b p.innerRot.val).toEuclideanLin v)) ''
          exactPolyhedron.hull := key.symm ▸ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hmem
    exact ⟨w, hw, by simp [MatrixPose.stellatedMove, hwv]⟩

theorem outerShadow_stellatedMove (p : MatrixPose) (a b : SymIndex) :
    outerShadow (p.stellatedMove a b) exactPolyhedron.hull =
      outerShadow p exactPolyhedron.hull := by
  have key := proj_image_moveMatrix a p.outerRot.val
  change (fun v => proj_xyL ((moveMatrix a p.outerRot.val).toEuclideanLin v)) ''
      exactPolyhedron.hull =
    (fun v => proj_xyL (p.outerRot.val.toEuclideanLin v)) '' exactPolyhedron.hull
  exact key

theorem RupertPose_stellatedMove_iff (p : MatrixPose) (a b : SymIndex) :
    RupertPose (p.stellatedMove a b) exactPolyhedron.hull ↔
      RupertPose p exactPolyhedron.hull := by
  simp only [RupertPose, innerShadow_stellatedMove, outerShadow_stellatedMove]

end Noperts.Stellated

end
