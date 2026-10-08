module

public import Noperts.Stellated.AtlasEdgeCertificate
public import Noperts.ProjectiveView

@[expose] public section

/-!
# A signed projective atlas for the stellated tetrahedron viewing directions

The stellated tetrahedron does not have enough symmetry to move
every outer view into one positive chamber.  Eight signed coordinate
triangles cover the whole sphere.  Dividing a unit view by its signed
coordinate sum puts it in the appropriate rational triangle, and that sum
is at least one.
-/

namespace Noperts.Stellated.AtlasProjectiveView

open scoped RealInnerProductSpace
open AtlasEdgeCertificate
open Noperts.ProjectiveView

abbrev Vector (R : Type) := Fin 3 → R
abbrev Triangle (R : Type) := Fin 3 → Vector R

/-- The eight coordinate sign patterns, in binary order. -/
def rootSign (root : Fin 8) : Vector ℚ := ![
  ![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1],
  ![-1, 1, 1], ![-1, 1, -1], ![-1, -1, 1], ![-1, -1, -1]] root

@[simp] theorem rootSign_sq (root : Fin 8) (c : Fin 3) :
    rootSign root c ^ 2 = 1 := by
  fin_cases root <;> fin_cases c <;> norm_num [rootSign]

def signedBasis (root : Fin 8) (c : Fin 3) : Vector ℚ :=
  fun d => if c = d then rootSign root c else 0

/-- One signed coordinate face of the projective octahedron. -/
def rootTriangle (root : Fin 8) : Triangle ℚ :=
  fun c => signedBasis root c

/-- The rational projective triangle of the view chamber `x ≥ y ≥ z ≥ 0`. -/
def chamberTriangle : Triangle ℚ :=
  ![![1, 0, 0], ![1 / 2, 1 / 2, 0], ![1 / 3, 1 / 3, 1 / 3]]

noncomputable def viewScale (root : Fin 8) (p : AtlasPose ℝ) : ℝ :=
  ∑ c, (rootSign root c : ℝ) * viewVector p c

noncomputable def normalizedView (root : Fin 8)
    (p : AtlasPose ℝ) : Vector ℝ :=
  fun c => viewVector p c / viewScale root p

theorem one_le_viewScale_of_sign {root : Fin 8} {p : AtlasPose ℝ}
    (hsign : ∀ c, 0 ≤ (rootSign root c : ℝ) * viewVector p c) :
    1 ≤ viewScale root p := by
  have hnorm := viewVector_norm p
  have hnormsq := congrArg (fun x : ℝ => x ^ 2) hnorm
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_three] at hnormsq
  have h0 := hsign 0
  have h1 := hsign 1
  have h2 := hsign 2
  have hs0 : ((rootSign root 0 : ℚ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast rootSign_sq root 0
  have hs1 : ((rootSign root 1 : ℚ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast rootSign_sq root 1
  have hs2 : ((rootSign root 2 : ℚ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast rootSign_sq root 2
  unfold viewScale
  simp only [Fin.sum_univ_three]
  nlinarith

theorem normalizedView_mem_root_of_sign {root : Fin 8}
    {p : AtlasPose ℝ}
    (hsign : ∀ c, 0 ≤ (rootSign root c : ℝ) * viewVector p c) :
    InTriangle (toReal (rootTriangle root)) (normalizedView root p) := by
  have hscale := one_le_viewScale_of_sign hsign
  have hscale0 : 0 < viewScale root p := lt_of_lt_of_le (by norm_num) hscale
  let weight : Vector ℝ := fun c =>
    (rootSign root c : ℝ) * viewVector p c / viewScale root p
  refine ⟨weight, ?_, ?_, ?_⟩
  · intro c
    exact div_nonneg (hsign c) hscale0.le
  · simp only [weight]
    rw [← Finset.sum_div]
    exact div_self hscale0.ne'
  · funext c
    fin_cases c
    · simp [normalizedView, affinePoint, rootTriangle, signedBasis,
        toReal, weight, Fin.sum_univ_three]
      field_simp [hscale0.ne']
      rw [show ((rootSign root 0 : ℚ) : ℝ) ^ 2 = 1 by
        exact_mod_cast rootSign_sq root 0]
      ring
    · simp [normalizedView, affinePoint, rootTriangle, signedBasis,
        toReal, weight, Fin.sum_univ_three]
      field_simp [hscale0.ne']
      rw [show ((rootSign root 1 : ℚ) : ℝ) ^ 2 = 1 by
        exact_mod_cast rootSign_sq root 1]
      ring
    · simp [normalizedView, affinePoint, rootTriangle, signedBasis,
        toReal, weight, Fin.sum_univ_three]
      field_simp [hscale0.ne']
      rw [show ((rootSign root 2 : ℚ) : ℝ) ^ 2 = 1 by
        exact_mod_cast rootSign_sq root 2]
      ring

theorem viewVector_eq_view (p : AtlasPose ℝ) (c : Fin 3) :
    viewVector p c = p.view c := by
  fin_cases c <;> rfl

/-- Chamber views lie in the rational chamber triangle of the `+++` root. -/
theorem chamber_mem_triangle (p : AtlasPose ℝ) (hp : p.InChamber) :
    1 ≤ viewScale 0 p ∧
      InTriangle (toReal chamberTriangle) (normalizedView 0 p) := by
  obtain ⟨h10, h21, h2⟩ := hp
  simp only [← viewVector_eq_view] at h10 h21 h2
  have hsign : ∀ c, 0 ≤ (rootSign 0 c : ℝ) * viewVector p c := by
    intro c
    fin_cases c <;> simp [rootSign] <;> linarith
  have hscale := one_le_viewScale_of_sign hsign
  have hscale0 : 0 < viewScale 0 p := lt_of_lt_of_le (by norm_num) hscale
  let u := normalizedView 0 p
  have hu : ∀ c, u c = viewVector p c / viewScale 0 p := fun c => rfl
  have hscaleEq : viewScale 0 p =
      viewVector p 0 + viewVector p 1 + viewVector p 2 := by
    simp [viewScale, rootSign, Fin.sum_univ_three]
  have husum : u 0 + u 1 + u 2 = 1 := by
    rw [hu, hu, hu, ← add_div, ← add_div, ← hscaleEq, div_self hscale0.ne']
  have h10' : u 1 ≤ u 0 := by
    rw [hu, hu]; exact div_le_div_of_nonneg_right h10 hscale0.le
  have h21' : u 2 ≤ u 1 := by
    rw [hu, hu]; exact div_le_div_of_nonneg_right h21 hscale0.le
  have h2' : 0 ≤ u 2 := by rw [hu]; exact div_nonneg h2 hscale0.le
  refine ⟨hscale, ![u 0 - u 1, 2 * (u 1 - u 2), 3 * u 2], ?_, ?_, ?_⟩
  · intro c
    fin_cases c <;> simp <;> linarith
  · simp only [Fin.sum_univ_three]
    simp
    linarith
  · funext c
    fin_cases c <;>
      simp [u, chamberTriangle, affinePoint, toReal, Fin.sum_univ_three] <;>
      ring

/-- Every outer view belongs to one of the eight signed projective roots,
with a positive scaling factor at least one. -/
theorem exists_root (p : AtlasPose ℝ) :
    ∃ root : Fin 8, 1 ≤ viewScale root p ∧
      InTriangle (toReal (rootTriangle root)) (normalizedView root p) := by
  by_cases h0 : 0 ≤ viewVector p 0
  · by_cases h1 : 0 ≤ viewVector p 1
    · by_cases h2 : 0 ≤ viewVector p 2
      · have hs : ∀ c, 0 ≤ (rootSign 0 c : ℝ) * viewVector p c := by
          intro c
          fin_cases c <;> simp [rootSign, h0, h1, h2]
        exact ⟨0, one_le_viewScale_of_sign hs,
          normalizedView_mem_root_of_sign hs⟩
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨1, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0, h1, h2']
    · have h1' : viewVector p 1 ≤ 0 := le_of_not_ge h1
      by_cases h2 : 0 ≤ viewVector p 2
      · refine ⟨2, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0, h1', h2]
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨3, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0, h1', h2']
  · have h0' : viewVector p 0 ≤ 0 := le_of_not_ge h0
    by_cases h1 : 0 ≤ viewVector p 1
    · by_cases h2 : 0 ≤ viewVector p 2
      · refine ⟨4, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1, h2]
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨5, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1, h2']
    · have h1' : viewVector p 1 ≤ 0 := le_of_not_ge h1
      by_cases h2 : 0 ≤ viewVector p 2
      · refine ⟨6, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1', h2]
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨7, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1', h2']

end Noperts.Stellated.AtlasProjectiveView

end
