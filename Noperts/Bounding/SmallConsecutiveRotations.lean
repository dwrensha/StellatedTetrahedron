module

public import Mathlib.LinearAlgebra.Trace
public import Noperts.Basic
public import Noperts.Bounding.OpNorm
public import Noperts.Bounding.BoundingUtil
public import Noperts.Bounding.OrthEquivRotz

@[expose] public section


/-!

Material for [SY25] Lemma 12.

-/

namespace Bounding
open Real

noncomputable abbrev tr := LinearMap.trace ℝ ℝ³
noncomputable abbrev tr' := LinearMap.trace ℝ (Fin 3 → ℝ)

lemma tr_RzL {α : ℝ} : tr (RzL α) = 1 + 2 * Real.cos α :=
  calc tr (RzL α)
  _ = tr' ((Rz_mat α).toLin') := by simp [RzL, Matrix.toLpLin_eq_toLin]
  _ = Matrix.trace (Rz_mat α) := by rw [Matrix.trace_toLin'_eq]
  _ = 1 + 2 * cos α := by
    simp [Matrix.trace, Fin.sum_univ_three]
    ring_nf

section AristotleLemmas

/-
The squared norm of the difference between the composition of two rotations and the identity is related to the trace of the composition.
-/
end AristotleLemmas

end Bounding

end
