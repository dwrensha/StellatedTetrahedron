module

public import Noperts.PoseClasses
public import Noperts.MatrixPose
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# A shadow never fits strictly inside a translate of itself

If the inner and outer rotations of a pose agree, the inner shadow is a
translate of the outer shadow, and a nonempty bounded planar set cannot have
the closure of a translate inside its own interior.  This handles the exact
diagonal poses (relative rotation `I`) that the blow-up certificates reach only
in the limit.
-/

namespace Noperts.Stellated

open scoped RealInnerProductSpace

/-- No nonempty bounded set in the plane has the closure of a translate in
its interior. -/
theorem not_closure_translate_subset_interior {K : Set ℝ²}
    (hK : Bornology.IsBounded K) (hne : K.Nonempty) (t : ℝ²) :
    ¬ closure ((fun x => t + x) '' K) ⊆ interior K := by
  intro hsub
  -- a direction in which the translate does not move backwards
  obtain ⟨d, hd, hdt⟩ : ∃ d : ℝ², d ≠ 0 ∧ 0 ≤ ⟪d, t⟫ := by
    by_cases ht : t = 0
    · refine ⟨EuclideanSpace.single 0 1, ?_, by simp [ht]⟩
      simp
    · exact ⟨t, ht, real_inner_self_nonneg⟩
  have hcompact : IsCompact (closure K) := hK.isCompact_closure
  obtain ⟨y, hy, hmax⟩ := hcompact.exists_isMaxOn (hne.mono subset_closure)
    (continuous_const.inner continuous_id).continuousOn
      (f := fun x => ⟪d, x⟫)
  -- `t + y` lies in the closure of the translate, hence in `interior K`
  have hty : t + y ∈ closure ((fun x => t + x) '' K) := by
    have hcont : Continuous (fun x : ℝ² => t + x) := continuous_const.add continuous_id
    exact (image_closure_subset_closure_image hcont) ⟨y, hy, rfl⟩
  have hint := hsub hty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (t + y) hint
  -- step a little further in direction `d`
  let z := t + y + (r / 2 / ‖d‖) • d
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hz : z ∈ interior K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [z, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    field_simp
    linarith
  have hzK : z ∈ closure K := subset_closure (interior_subset hz)
  have hle := hmax hzK
  simp only [Set.mem_ofPred_eq] at hle
  have : ⟪d, z⟫ = ⟪d, y⟫ + ⟪d, t⟫ + r / 2 * ‖d‖ := by
    simp only [z, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hpos : 0 < r / 2 * ‖d‖ := by positivity
  linarith

/-- Poses whose inner and outer rotations agree are never Rupert. -/
theorem not_rupertPose_of_innerRot_eq_outerRot (p : MatrixPose) {S : Set ℝ³}
    (hS : Bornology.IsBounded S) (hne : S.Nonempty)
    (h : p.innerRot = p.outerRot) : ¬ RupertPose p S := by
  intro hrupert
  have hinner : innerShadow p S =
      (fun x => p.innerOffset + x) '' outerShadow p S := by
    rw [MatrixPose.inner_shadow_lemma]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, outerShadow, h]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
  have hbounded : Bornology.IsBounded (outerShadow p S) := by
    let L : ℝ³ →L[ℝ] ℝ² := proj_xyL.comp
      (LinearMap.toContinuousLinearMap p.outerRot.val.toEuclideanLin)
    have hL : outerShadow p S = L '' S := by
      ext x
      simp [outerShadow, L, PoseLike.outer]
    rw [hL]
    exact L.lipschitzWith.isBounded_image hS
  have hne' : (outerShadow p S).Nonempty := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨_, v, hv, rfl⟩
  exact not_closure_translate_subset_interior hbounded hne' p.innerOffset
    (hinner ▸ hrupert)

end Noperts.Stellated

end
