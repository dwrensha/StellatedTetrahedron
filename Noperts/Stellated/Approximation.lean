module

public import Noperts.Stellated.Vertices
public import Noperts.RationalApprox.Basic

@[expose] public section

/-!
# The checker model is the exact solid

For Nopert #76 the checker reads published decimals that only approximate the
exact solid, and certificate files budget for that error through
`exactApproximation` and `vertex_close_tight`.  The stellated tetrahedron has
exact rational vertices, so both statements hold with zero error.  We keep the
same interface, including the `tightVertexErrorQ` constant that the
certificate checkers (and their Python mirror) reserve, so the ported
certificate files need no changes.
-/

namespace Noperts.Stellated

theorem exactVertex_sub_rational (i : VertexIndex) :
    exactVertex i - toR3 (rationalVertex i) = 0 :=
  sub_self _

noncomputable def exactApproximation :
    RationalApprox.κApproxPoly exactPolyhedron rationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx i := by
    simp [rationalPolyhedron, exactVertex_sub_rational,
      RationalApprox.κ]

/-- The vertex error reserved by the certificate checkers.  It is inherited
from Nopert #76; the vertices here are exact, so it is zero. -/
def tightVertexErrorQ : ℚ := 0

theorem vertex_close_tight (i : VertexIndex) :
    ‖exactVertex i - toR3 (rationalVertex i)‖ ≤
      (tightVertexErrorQ : ℝ) := by
  rw [exactVertex_sub_rational, norm_zero]
  norm_num [tightVertexErrorQ]

end Noperts.Stellated

end
