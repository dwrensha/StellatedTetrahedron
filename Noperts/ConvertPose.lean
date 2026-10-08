module

public import Noperts.MatrixPose
public import Noperts.Pose
public import Noperts.Bounding.OrthEquivRotz

@[expose] public section


open Bounding Real
open scoped Matrix

/-- Matrix version of rotRM. -/
noncomputable
def rotRM_mat (θ φ α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Rz_mat (-(π / 2)) * Rz_mat α * Ry_mat φ * Rz_mat (-θ)

/--
The matrix `rotRM_mat θ φ α` is in SO3 because it's a product of SO3 matrices.
-/
lemma rotRM_mat_mem_SO3 (θ φ α : ℝ) : rotRM_mat θ φ α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
    (Bounding.rot3_mat_mem_SO3 2 _) (Bounding.rot3_mat_mem_SO3 2 _))
    (Bounding.rot3_mat_mem_SO3 1 _)) (Bounding.rot3_mat_mem_SO3 2 _)

/--
`rotRM θ φ α` equals the continuous linear map induced by `rotRM_mat θ φ α`.
-/
lemma rotRM_eq_rotRM_mat (θ φ α : ℝ) :
    rotRM θ φ α = (rotRM_mat θ φ α).toEuclideanLin.toContinuousLinearMap := by
  ext v
  simp only [rotRM, rotRM_mat, RzL, RyL, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_toContinuousLinearMap']
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- inject_xy 0 = 0. -/
@[simp]
lemma inject_xy_zero : inject_xy (0 : ℝ²) = (0 : ℝ³) := by
  ext i; fin_cases i <;> simp [inject_xy]

/-- Convert a Pose to a MatrixPose. -/
noncomputable def Pose.matrixPoseOfPose (p : Pose ℝ) : MatrixPose where
  innerRot := ⟨rotRM_mat p.θ₁ p.φ₁ p.α, rotRM_mat_mem_SO3 _ _ _⟩
  outerRot := ⟨rotRM_mat p.θ₂ p.φ₂ 0, rotRM_mat_mem_SO3 _ _ _⟩
  innerOffset := 0

end
