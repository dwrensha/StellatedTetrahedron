module

public import Noperts.Basic

@[expose] public section

/-!
# Vertices of the stellated tetrahedron `P_{11/20}`

Zeng (arXiv:2604.26531) conjectures that the stellated tetrahedron with
vertices

* `pᵢ = (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)`, and
* `qᵢ = -a pᵢ` with `a = 11/20`

is not Rupert.  We work with the similar copy scaled by `1/2`, so that every
vertex lies strictly inside the unit ball; the Rupert property is invariant
under this similarity.  All coordinates are rational, so the checker model
and the exact solid coincide.
-/

namespace Noperts.Stellated

abbrev VertexIndex := Fin 8

/-- The parameter `a` of the stellation. -/
def stellation : ℚ := 11 / 20

/-- The four vertices of the underlying regular tetrahedron, before scaling. -/
def tetrahedronVertex : Fin 4 → Fin 3 → ℚ := ![
  ![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- Vertices `0..3` are `pᵢ / 2`; vertices `4..7` are `qᵢ / 2 = -a pᵢ / 2`. -/
def rationalVertex : VertexIndex → Fin 3 → ℚ := ![
  ![1 / 2, 1 / 2, 1 / 2], ![1 / 2, -1 / 2, -1 / 2],
  ![-1 / 2, 1 / 2, -1 / 2], ![-1 / 2, -1 / 2, 1 / 2],
  ![-11 / 40, -11 / 40, -11 / 40], ![-11 / 40, 11 / 40, 11 / 40],
  ![11 / 40, -11 / 40, 11 / 40], ![11 / 40, 11 / 40, -11 / 40]]

theorem rationalVertex_spec (i : Fin 4) :
    rationalVertex (Fin.castAdd 4 i) = (1 / 2 : ℚ) • tetrahedronVertex i ∧
      rationalVertex (Fin.natAdd 4 i) =
        (-stellation / 2 : ℚ) • tetrahedronVertex i := by
  constructor <;> funext c <;> fin_cases i <;> fin_cases c <;>
    simp [rationalVertex, tetrahedronVertex, stellation] <;> norm_num

def rationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) :=
  ⟨rationalVertex⟩

noncomputable def exactVertex (i : VertexIndex) : ℝ³ :=
  toR3 (rationalVertex i)

noncomputable def exactPolyhedron : Polyhedron VertexIndex ℝ³ :=
  ⟨exactVertex⟩

noncomputable def exactVerts : Finset ℝ³ :=
  Finset.image exactVertex Finset.univ

theorem exactPolyhedron_hull :
    exactPolyhedron.hull = convexHull ℝ exactVerts := by
  simp only [Polyhedron.hull, exactPolyhedron, exactVerts, Finset.coe_image,
    Finset.coe_univ, Set.image_univ]
  congr 1

@[simp] theorem exactPolyhedron_vertex (i : VertexIndex) :
    exactPolyhedron.v i = exactVertex i := rfl

theorem exactVertex_norm_pos (i : VertexIndex) : 0 < ‖exactVertex i‖ := by
  rw [norm_pos_iff]
  intro h
  have hc := congrFun (congrArg WithLp.ofLp h) (0 : Fin 3)
  fin_cases i <;> simp [exactVertex, rationalVertex, toR3] at hc

theorem exactVertex_norm_le_one (i : VertexIndex) : ‖exactVertex i‖ ≤ 1 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [exactVertex, toR3, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs, one_pow]
  fin_cases i <;> simp [rationalVertex] <;> norm_num

noncomputable def exactGoodPoly : GoodPoly VertexIndex where
  vertices := exactPolyhedron
  nontriv := exactVertex_norm_pos
  vertex_radius_le_one := exactVertex_norm_le_one

end Noperts.Stellated

end
