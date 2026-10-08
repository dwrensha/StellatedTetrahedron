module

public import Noperts.PoseClasses
public import Noperts.Basic

@[expose] public section


structure Pose (R : Type) : Type where
  θ₁ : R
  θ₂ : R
  φ₁ : R
  φ₂ : R
  α : R
deriving DecidableEq, Repr

instance {R : Type} [ToString R] : ToString (Pose R) where
  toString p := s!"\{θ₁ := {p.θ₁}, θ₂ := {p.θ₂}, φ₁ := {p.φ₁}, φ₂ := {p.φ₂}, α := {p.α}}"

noncomputable
instance : PoseLike (Pose ℝ) where
  inner vp := (rotRM vp.θ₁ vp.φ₁ vp.α).toAffineMap
  outer vp := (rotRM vp.θ₂ vp.φ₂ 0).toAffineMap

namespace Pose

/-- Bijection between `Pose` and `Fin 5 → ℝ`, used to transfer
the (sup-norm) `MetricSpace` instance from the Pi type. -/
def equivPi {R : Type} : Pose R ≃ (Fin 5 → R) where
  toFun p := ![p.θ₁, p.θ₂, p.φ₁, p.φ₂, p.α]
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4⟩
  left_inv p := by cases p; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

/-- Sup-norm transferred from `Fin 5 → R`. -/
instance {R} [MetricSpace R] : MetricSpace (Pose R) :=
  MetricSpace.induced equivPi equivPi.injective inferInstance

instance {R} [PartialOrder R] : PartialOrder (Pose R) := PartialOrder.lift equivPi equivPi.injective

lemma le_iff {R} [PartialOrder R] (p q : Pose R) :
    p ≤ q ↔ p.θ₁ ≤ q.θ₁ ∧ p.θ₂ ≤ q.θ₂ ∧ p.φ₁ ≤ q.φ₁ ∧ p.φ₂ ≤ q.φ₂ ∧ p.α ≤ q.α := by
  show equivPi p ≤ equivPi q ↔ _
  rw [Pi.le_def]
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩, ?_⟩
  rintro ⟨h1, h2, h3, h4, h5⟩ i
  fin_cases i <;> assumption

instance {R} [PartialOrder R] [DecidableLE R] : DecidableLE (Pose R) :=
  fun p q => decidable_of_iff _ (le_iff p q).symm

end Pose

namespace Pose

-- Some convenience functions for doing rotations with dot notation
-- Maybe the rotations in basic could be inlined here? It depends on whether
-- we actually use them not in the context of a Pose.

noncomputable
def rotM₁ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₁) (p.φ₁)
noncomputable
def rotM₂ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₂) (p.φ₂)
noncomputable
def rotR (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.rotR (p.α)
noncomputable
def rotM₁θ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₁φ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂φ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₂) (p.φ₂)
noncomputable
def rotR' (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.rotR' (p.α)

noncomputable
def rotM₁θθ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₁θφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₁φφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θθ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₂θφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθφ (p.θ₂) (p.φ₂)
noncomputable
def rotM₂φφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφφ (p.θ₂) (p.φ₂)

noncomputable
def inner (p : Pose ℝ) : ℝ³ →ᵃ[ℝ] ℝ² := innerProj p
noncomputable
def outer (p : Pose ℝ) : ℝ³ →ᵃ[ℝ] ℝ² := outerProj p


def innerParams (p : Pose ℝ) : ℝ³ := !₂[p.α, p.θ₁, p.φ₁]

def outerParams (p : Pose ℝ) : ℝ² := !₂[p.θ₂, p.φ₂]

lemma proj_rm_eq_m (θ φ : ℝ) (v : ℝ³) :
    proj_xyL (rotRM θ φ 0 v) = rotM θ φ v := by
  change (proj_xyL ∘ rotRM θ φ 0) v = rotM θ φ v
  rw [projxy_rotRM_eq_rotprojRM]
  change ((_root_.rotR 0) ∘L rotM θ φ) v = rotM θ φ v
  rw [AddChar.map_zero_eq_one]
  rfl

lemma inner_eq_RM (p : Pose ℝ)  :
    p.inner = (p.rotR ∘ p.rotM₁) := by
  ext1 v
  change (proj_xyL ∘ rotRM p.θ₁ p.φ₁ p.α) v = p.rotR (p.rotM₁ v)
  rw [projxy_rotRM_eq_rotprojRM]
  rfl

lemma outer_eq_M (p : Pose ℝ) : p.outer = ⇑p.rotM₂ := by
  ext1 v
  exact proj_rm_eq_m p.θ₂ p.φ₂ v

lemma poselike_inner_eq_proj_inner (p : Pose ℝ) :
    proj_xyL ∘ PoseLike.inner p = p.inner := by
  ext v
  simp only [PoseLike.inner, Pose.inner, innerProj, AffineMap.coe_comp,
    LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]

lemma poselike_outer_eq_proj_outer (p : Pose ℝ) :
    proj_xyL ∘ PoseLike.outer p = p.outer := by
  ext v
  simp only [PoseLike.outer, Pose.outer, outerProj, AffineMap.coe_comp,
    LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]

end Pose

end
