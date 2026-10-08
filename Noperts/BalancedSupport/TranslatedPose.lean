module

public import Noperts.BalancedSupport.Rupert
public import Noperts.ConvertPose

@[expose] public section


/-!
# Euler parameters with an uncancelled translation

Balanced supports cancel translation in the proof, not in the geometry.  This
file shows that the existing five Euler rotation parameters, together with an
arbitrary planar offset, still represent every full `MatrixPose` up to a
common rotation of both shadows.
-/

namespace Noperts.BalancedSupport

open scoped RealInnerProductSpace

/-- Attach an arbitrary planar translation to the inner copy of an Euler
pose. -/
noncomputable def _root_.Pose.matrixPoseWithOffset (p : Pose ℝ) (offset : ℝ²) : MatrixPose :=
  {p.matrixPoseOfPose with innerOffset := offset}

@[simp] theorem _root_.Pose.matrixPoseWithOffset_zero (p : Pose ℝ) :
    p.matrixPoseWithOffset 0 = p.matrixPoseOfPose := by
  rfl

theorem matrixPoseWithOffset_inner_rotation_project
    (p : Pose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin v) = p.inner v := by
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose]
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f v)
    (rotRM_eq_rotRM_mat p.θ₁ p.φ₁ p.α)
  have hrot' : (rotRM p.θ₁ p.φ₁ p.α) v =
      (rotRM_mat p.θ₁ p.φ₁ p.α).toEuclideanLin v := by simpa using hrot
  rw [← hrot']
  simpa [PoseLike.inner] using
    congrArg (fun f : ℝ³ → ℝ² => f v) (Pose.poselike_inner_eq_proj_inner p)

theorem matrixPoseWithOffset_outer_rotation_project
    (p : Pose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin v) = p.outer v := by
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose]
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f v)
    (rotRM_eq_rotRM_mat p.θ₂ p.φ₂ 0)
  have hrot' : (rotRM p.θ₂ p.φ₂ 0) v =
      (rotRM_mat p.θ₂ p.φ₂ 0).toEuclideanLin v := by simpa using hrot
  rw [← hrot']
  simpa [PoseLike.outer] using
    congrArg (fun f : ℝ³ → ℝ² => f v) (Pose.poselike_outer_eq_proj_outer p)

theorem matrixPoseWithOffset_outer_project
    (p : Pose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL (PoseLike.outer (p.matrixPoseWithOffset offset) v) = p.outer v := by
  simpa only [PoseLike.outer, LinearMap.coe_toAffineMap] using
    matrixPoseWithOffset_outer_rotation_project p offset v

/-- Pose-coordinate transition form with support defects. -/
theorem not_translatedPose_of_balanced_support_with_defect
    {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty κ]
    (poly : Polyhedron ι ℝ³) (p : Pose ℝ) (offset : ℝ²)
    (Pi Qi : κ → ι) (μ : κ → ℝ) (u : κ → ℝ²) (defect : κ → ℝ)
    (hu : ∀ i, u i ≠ 0)
    (hμ : ∀ i, 0 ≤ μ i) (hμpos : ∃ i, 0 < μ i)
    (hbalance : ∑ i, μ i • u i = 0)
    (hsupport : ∀ i j,
      ⟪u i, p.outer (poly.v j)⟫ ≤
        ⟪u i, p.outer (poly.v (Qi i))⟫ + defect i)
    (hdisplacement : ∑ i, μ i * defect i ≤ ∑ i, μ i *
      ⟪u i, p.inner (poly.v (Pi i)) - p.outer (poly.v (Qi i))⟫) :
    ¬ RupertPose (p.matrixPoseWithOffset offset) poly.hull := by
  refine not_rupertPose_of_balanced_support_with_defect poly
    (p.matrixPoseWithOffset offset) Pi Qi μ u defect hu hμ hμpos hbalance ?_ ?_
  · intro i y hy
    obtain ⟨v, ⟨j, rfl⟩, rfl⟩ := hy
    simpa [outerProj, matrixPoseWithOffset_outer_project,
      matrixPoseWithOffset_outer_rotation_project] using hsupport i j
  · simpa [matrixPoseWithOffset_inner_rotation_project,
      matrixPoseWithOffset_outer_rotation_project] using hdisplacement

end Noperts.BalancedSupport

end
