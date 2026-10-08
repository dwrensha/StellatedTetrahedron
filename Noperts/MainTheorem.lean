module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
This file defines the Rupert property, in which our main theorem is stated, using only
Mathlib imports.
-/

@[expose] public section

/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def proj_xy {k : Type} (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  !₂[v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as a finite set of vertices. -/
def IsRupert (vertices : Finset (EuclideanSpace ℝ (Fin 3))) : Prop :=
   ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
   ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   let hull := convexHull ℝ vertices
   let inner_shadow := { inner_offset + proj_xy (inner_rotation.toEuclideanLin p) | p ∈ hull }
   let outer_shadow := { proj_xy (outer_rotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow

end
