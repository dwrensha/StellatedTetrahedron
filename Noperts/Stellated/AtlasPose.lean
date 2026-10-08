module

public import Noperts.Stellated.CayleyAtlas

@[expose] public section

/-!
# the stellated tetrahedron poses in the bounded Cayley atlas

An atlas pose retains only the two outer viewing angles.  Its relative
rotation is represented in one of the four rational Cayley charts.  Thus the
certificate domain is four copies of a five-dimensional rational box, with
no Euler singularities.
-/

namespace Noperts.Stellated

open scoped Matrix
open CayleyAtlas

/-- Two outer viewing angles and three relative Cayley coordinates. -/
structure AtlasPose (R : Type) where
  θ : R
  φ : R
  x : R
  y : R
  z : R
deriving DecidableEq, Repr

namespace AtlasPose

def equivPi {R : Type} : AtlasPose R ≃ (Fin 5 → R) where
  toFun p := ![p.θ, p.φ, p.x, p.y, p.z]
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4⟩
  left_inv p := by cases p; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

instance {R : Type} [PartialOrder R] : PartialOrder (AtlasPose R) :=
  PartialOrder.lift equivPi equivPi.injective

theorem le_iff {R : Type} [PartialOrder R] (p q : AtlasPose R) :
    p ≤ q ↔ p.θ ≤ q.θ ∧ p.φ ≤ q.φ ∧ p.x ≤ q.x ∧
      p.y ≤ q.y ∧ p.z ≤ q.z := by
  show equivPi p ≤ equivPi q ↔ _
  rw [Pi.le_def]
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩, ?_⟩
  rintro ⟨hθ, hφ, hx, hy, hz⟩ i
  fin_cases i <;> assumption

instance {R : Type} [PartialOrder R] [DecidableLE R] :
    DecidableLE (AtlasPose R) :=
  fun p q => decidable_of_iff _ (le_iff p q).symm

/-- The rational root common to the four maximum-trace charts. -/
def rootInterval (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    NonemptyInterval (AtlasPose R) :=
  NonemptyInterval.mk
    ⟨{ θ := 0, φ := 0, x := -1, y := -1, z := -1 },
      { θ := 8 / 5, φ := 4, x := 1, y := 1, z := 1 }⟩
    (by rw [le_iff]; norm_num)

/-- Componentwise rational-to-real conversion. -/
def toReal (p : AtlasPose ℚ) : AtlasPose ℝ where
  θ := p.θ
  φ := p.φ
  x := p.x
  y := p.y
  z := p.z

@[simp] theorem toReal_θ (p : AtlasPose ℚ) : p.toReal.θ = (p.θ : ℝ) := rfl
@[simp] theorem toReal_φ (p : AtlasPose ℚ) : p.toReal.φ = (p.φ : ℝ) := rfl
@[simp] theorem toReal_x (p : AtlasPose ℚ) : p.toReal.x = (p.x : ℝ) := rfl
@[simp] theorem toReal_y (p : AtlasPose ℚ) : p.toReal.y = (p.y : ℝ) := rfl
@[simp] theorem toReal_z (p : AtlasPose ℚ) : p.toReal.z = (p.z : ℝ) := rfl

/-- The outer viewing rotation bundled as an element of `SO(3)`. -/
noncomputable def outerSO3 (p : AtlasPose ℝ) : SO3 :=
  ⟨rotRM_mat p.θ p.φ 0, rotRM_mat_mem_SO3 _ _ _⟩

/-- Interpret an atlas pose and chart as a full matrix pose. -/
noncomputable def matrixPoseWithOffset (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) : MatrixPose where
  outerRot := p.outerSO3
  innerRot := p.outerSO3 * chartSO3 chart * cayleySO3 p.x p.y p.z
  innerOffset := offset

@[simp] theorem matrixPoseWithOffset_outerRot_val (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).outerRot.val =
      rotRM_mat p.θ p.φ 0 := rfl

@[simp] theorem matrixPoseWithOffset_innerRot_val (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).innerRot.val =
      (rotRM_mat p.θ p.φ 0 * chartMatrix chart) *
        cayleyMatrix p.x p.y p.z := rfl

@[simp] theorem matrixPoseWithOffset_relativeRotation (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).relativeRotation =
      chartMatrix chart * cayleyMatrix p.x p.y p.z := by
  have horth := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (rotRM_mat_mem_SO3 p.θ p.φ 0).1
  simp only [MatrixPose.relativeRotation,
    matrixPoseWithOffset_outerRot_val, matrixPoseWithOffset_innerRot_val]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (rotRM_mat p.θ p.φ 0)ᵀ, horth, Matrix.one_mul]

theorem matrixPoseWithOffset_inner_rotation_project (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset chart offset).innerRot.val.toEuclideanLin v) =
      rotM p.θ p.φ
        ((chartMatrix chart * cayleyMatrix p.x p.y p.z).toEuclideanLin v) := by
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ =>
      f ((chartMatrix chart * cayleyMatrix p.x p.y p.z).toEuclideanLin v))
    (rotRM_eq_rotRM_mat p.θ p.φ 0)
  rw [← Pose.proj_rm_eq_m]
  apply congrArg proj_xyL
  simpa [matrixPoseWithOffset_innerRot_val, Matrix.toLpLin_apply,
    Matrix.mulVec_mulVec, Matrix.mul_assoc] using hrot.symm

theorem matrixPoseWithOffset_outer_rotation_project (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset chart offset).outerRot.val.toEuclideanLin v) =
      rotM p.θ p.φ v := by
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f v)
    (rotRM_eq_rotRM_mat p.θ p.φ 0)
  rw [← Pose.proj_rm_eq_m]
  apply congrArg proj_xyL
  simpa [matrixPoseWithOffset_outerRot_val] using hrot.symm

end AtlasPose

theorem matrixPose_ext_val {p q : MatrixPose}
    (hinner : p.innerRot.val = q.innerRot.val)
    (houter : p.outerRot.val = q.outerRot.val)
    (hoffset : p.innerOffset = q.innerOffset) : p = q := by
  cases p with
  | mk pinner pouter poffset =>
    cases q with
    | mk qinner qouter qoffset =>
      have hi : pinner = qinner := Subtype.ext hinner
      have ho : pouter = qouter := Subtype.ext houter
      subst hi
      subst ho
      subst hoffset
      rfl

def AtlasPose.CayleyBounded (p : AtlasPose ℝ) : Prop :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ 3

/-- The outer viewing direction `(cos θ sin φ, sin θ sin φ, cos φ)`. -/
noncomputable def AtlasPose.view (p : AtlasPose ℝ) : Fin 3 → ℝ :=
  ![Real.cos p.θ * Real.sin p.φ, Real.sin p.θ * Real.sin p.φ, Real.cos p.φ]

/-- The outer view lies in the chamber `x ≥ y ≥ z ≥ 0`. -/
def AtlasPose.InChamber (p : AtlasPose ℝ) : Prop :=
  Noperts.Stellated.InChamber p.view

/-- The tetrahedral part of the relative Dirichlet cell, in chart zero. -/
def AtlasPose.InOctahedron (p : AtlasPose ℝ) : Prop :=
  |p.x| + |p.y| + |p.z| ≤ 1

/-- The half-turn about the outer viewing direction. -/
noncomputable def AtlasPose.viewHalfTurn (p : AtlasPose ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (rotRM_mat p.θ p.φ 0)ᵀ * symReal screenHalfTurn * rotRM_mat p.θ p.φ 0

/-- The view-dependent part of the relative Dirichlet cell, in chart zero. -/
def AtlasPose.FlipReduced (p : AtlasPose ℝ) : Prop :=
  ∀ b : SymIndex, isFlip b →
    Matrix.trace (relAct p.viewHalfTurn (cayleyMatrix p.x p.y p.z) b) ≤
      Matrix.trace (cayleyMatrix p.x p.y p.z)

/-- The symmetry-reduced part of the chart-zero root. -/
def AtlasPose.Reduced (p : AtlasPose ℝ) : Prop :=
  p.InChamber ∧ p.InOctahedron ∧ p.FlipReduced

theorem rotRM_mat_row_two (θ φ α : ℝ) (c : Fin 3) :
    rotRM_mat θ φ α 2 c =
      ![Real.cos θ * Real.sin φ, Real.sin θ * Real.sin φ, Real.cos φ] c := by
  fin_cases c <;>
    simp [rotRM_mat, Rz_mat, Ry_mat, Matrix.mul_apply, Fin.sum_univ_three,
      mul_comm]

end Noperts.Stellated

end
