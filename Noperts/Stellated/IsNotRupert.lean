module

public import Noperts.Stellated.AtlasProjectiveSolutionTree
public import Noperts.Rupert.Equivalences.RupertEquivRupertSet

@[expose] public section

/-!
# The public non-Rupert conclusion for the stellated tetrahedron

This file contains the small, certificate-independent bridge from a valid
chart-zero table to the usual vertex-set formulation of the Rupert property.
-/

open scoped Matrix

namespace Noperts.Stellated

open CayleyAtlas
open AtlasProjectiveSolutionTree

private lemma rupert_set_implies_matrix_pose {S : Set ℝ³}
    (h : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, innerSO3, offset, outer, outerSO3, hshadow⟩ := h
  let p : MatrixPose :=
    MatrixPose.mk ⟨inner, innerSO3⟩ ⟨outer, outerSO3⟩ offset
  refine ⟨p, ?_⟩
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  rw [p.inner_shadow_lemma, outerShadow]
  repeat rw [← proj_xy_eq_proj_xyL]
  exact hshadow

/-- A valid chart-zero exclusion table proves that the stellated tetrahedron
`P_{11/20}` is not Rupert. -/
theorem not_rupert_of_valid_table
    (table : AtlasProjectiveSolutionTree.Table)
    (hchart : table.chart = 0) (hvalid : table.Valid)
    (hcorner : AtlasProjectiveSolutionTree.CornerCovered) :
    ¬ IsRupert exactVerts := by
  intro hrupert
  have hset : IsRupertSet (convexHull ℝ exactVerts) :=
    (rupert_iff_rupert_set exactVerts).mp hrupert
  rw [← exactPolyhedron_hull] at hset
  exact no_matrixPose_of_valid_table table hchart hvalid hcorner
    (rupert_set_implies_matrix_pose hset)

/-- Exclusion on the chart-zero root box proves that `P_{11/20}` is not Rupert. -/
theorem not_rupert_of_root
    (h : AtlasProjectiveSolutionTree.NoRupert 0 (AtlasPose.rootInterval ℚ) .sphere) :
    ¬ IsRupert exactVerts := by
  intro hrupert
  have hset : IsRupertSet (convexHull ℝ exactVerts) :=
    (rupert_iff_rupert_set exactVerts).mp hrupert
  rw [← exactPolyhedron_hull] at hset
  exact AtlasProjectiveSolutionTree.no_matrixPose_of_root h
    (rupert_set_implies_matrix_pose hset)

end Noperts.Stellated

end
