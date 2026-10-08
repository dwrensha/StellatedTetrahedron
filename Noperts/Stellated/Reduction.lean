module

public import Noperts.Stellated.Moves
public import Mathlib.Data.Finset.Max
public import Noperts.BalancedSupport.ViewAntipode
public import Noperts.RelativeRotation

@[expose] public section

/-!
# Symmetry reduction of Rupert poses

Outer views are reduced by the moves of `Moves.lean` together with the view
antipode to the chamber `x ≥ y ≥ z ≥ 0`.  Each step is a Dirichlet argument:
maximize a score over a finite group orbit, then compare the maximizer with a
few explicit neighbours.
-/

namespace Noperts.Stellated

open scoped Matrix

/-- The (unnormalized) chamber of outer viewing directions. -/
def InChamber (w : Fin 3 → ℝ) : Prop :=
  w 1 ≤ w 0 ∧ w 2 ≤ w 1 ∧ 0 ≤ w 2

/-- The signed transposed action on views: `w ↦ σ • gᵀ w`. -/
noncomputable def viewAct (g : SymIndex) (s : Bool) (w : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  (if s then -1 else 1 : ℝ) • ((symReal g)ᵀ *ᵥ w)

theorem viewAct_symMul (g k : SymIndex) (s t : Bool) (w : Fin 3 → ℝ) :
    viewAct (symMul g k) (s ^^ t) w = viewAct k t (viewAct g s w) := by
  simp only [viewAct, ← symReal_mul, Matrix.transpose_mul,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul]
  congr 1
  cases s <;> cases t <;> norm_num

private def chamberScore (w : Fin 3 → ℝ) : ℝ := 3 * w 0 + 2 * w 1 + w 2

private theorem symReal_19 :
    symReal 19 = !![0, -1, 0; -1, 0, 0; 0, 0, -1] := by
  have h : symMatrix 19 = !![0, -1, 0; -1, 0, 0; 0, 0, -1] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symReal, h]

private theorem symReal_15 :
    symReal 15 = !![-1, 0, 0; 0, 0, -1; 0, -1, 0] := by
  have h : symMatrix 15 = !![-1, 0, 0; 0, 0, -1; 0, -1, 0] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symReal, h]

theorem exists_viewAct_inChamber (w : Fin 3 → ℝ) :
    ∃ g : SymIndex, ∃ s : Bool, InChamber (viewAct g s w) := by
  obtain ⟨⟨g, s⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun gs : SymIndex × Bool => chamberScore (viewAct gs.1 gs.2 w))
    Finset.univ_nonempty
  refine ⟨g, s, ?_⟩
  set u := viewAct g s w
  have hcmp : ∀ k : SymIndex, chamberScore (viewAct k true u) ≤
      chamberScore u := by
    intro k
    rw [← viewAct_symMul]
    exact hmax (symMul g k, s ^^ true) (Finset.mem_univ _)
  have h19 := hcmp 19
  have h15 := hcmp 15
  have h3 := hcmp screenHalfTurn
  simp only [viewAct, symReal_19, symReal_15, symReal_screenHalfTurn,
    chamberScore, ite_true] at h19 h15 h3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.transpose_apply] at h19 h15 h3
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The action of `O` on relative rotations at a fixed view: `b ∈ T` acts by
right multiplication, `b ∈ O \ T` additionally by left multiplication with
the half-turn `H` about the view axis. -/
noncomputable def relAct (H rel : Matrix (Fin 3) (Fin 3) ℝ) (b : SymIndex) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (if isFlip b then H else 1) * rel * symReal b

theorem relAct_relAct {H : Matrix (Fin 3) (Fin 3) ℝ} (hH : H * H = 1)
    (rel : Matrix (Fin 3) (Fin 3) ℝ) (b b' : SymIndex) :
    relAct H (relAct H rel b) b' = relAct H rel (symMul b b') := by
  have hpow : (if isFlip b' then H else 1) * (if isFlip b then H else 1) =
      (if isFlip (symMul b b') then H else 1) := by
    rw [isFlip_symMul]
    cases isFlip b <;> cases isFlip b' <;> simp [hH]
  simp only [relAct, ← symReal_mul, ← hpow, Matrix.mul_assoc]

/-- Every relative rotation has a max-trace representative in its orbit. -/
theorem exists_relAct_dirichlet {H : Matrix (Fin 3) (Fin 3) ℝ}
    (hH : H * H = 1) (rel : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ b : SymIndex, ∀ b' : SymIndex,
      Matrix.trace (relAct H (relAct H rel b) b') ≤
        Matrix.trace (relAct H rel b) := by
  obtain ⟨b, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun b : SymIndex => Matrix.trace (relAct H rel b)) Finset.univ_nonempty
  refine ⟨b, fun b' => ?_⟩
  rw [relAct_relAct hH]
  exact hmax _ (Finset.mem_univ _)

/-! ## Pose-level reduction -/

/-- The outer viewing direction `outerᵀ e_z` (third row of the outer rotation). -/
noncomputable def poseView (p : MatrixPose) : Fin 3 → ℝ :=
  fun c => p.outerRot.val 2 c

/-- The half-turn about the viewing direction, `outerᵀ H outer`. -/
noncomputable def poseViewHalfTurn (p : MatrixPose) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  p.outerRot.valᵀ * symReal screenHalfTurn * p.outerRot.val

/-- The reduced poses: chamber view and max-trace relative rotation. -/
def _root_.MatrixPose.StellatedReduced (p : MatrixPose) : Prop :=
  InChamber (poseView p) ∧
    ∀ b : SymIndex,
      Matrix.trace (relAct (poseViewHalfTurn p) p.relativeRotation b) ≤
        Matrix.trace p.relativeRotation

theorem symReal_zero : symReal 0 = 1 := by
  have h : symMatrix 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [symReal, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem moveMatrix_zero (R : Matrix (Fin 3) (Fin 3) ℝ) : moveMatrix 0 R = R := by
  simp [moveMatrix, isFlip, symReal_zero]

theorem orthogonal_of_SO3 (R : SO3) : R.val * R.valᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1

theorem orthogonal_of_SO3' (R : SO3) : R.valᵀ * R.val = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1

theorem screenHalfTurn_mul_self :
    symReal screenHalfTurn * symReal screenHalfTurn = 1 := by
  rw [symReal_screenHalfTurn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem poseViewHalfTurn_mul_self (p : MatrixPose) :
    poseViewHalfTurn p * poseViewHalfTurn p = 1 := by
  have h := orthogonal_of_SO3 p.outerRot
  calc poseViewHalfTurn p * poseViewHalfTurn p =
        p.outerRot.valᵀ * symReal screenHalfTurn *
          (p.outerRot.val * p.outerRot.valᵀ) * symReal screenHalfTurn *
          p.outerRot.val := by
          simp only [poseViewHalfTurn, Matrix.mul_assoc]
    _ = 1 := by
      rw [h, Matrix.mul_one, Matrix.mul_assoc (p.outerRot.valᵀ),
        screenHalfTurn_mul_self, Matrix.mul_one, orthogonal_of_SO3']

private theorem row_two_screenHalfTurn_mul (R : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3) : (symReal screenHalfTurn * R) 2 c = R 2 c := by
  rw [symReal_screenHalfTurn]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem poseView_stellatedMove (p : MatrixPose) (a b : SymIndex) :
    poseView (p.stellatedMove a b) = (symReal a)ᵀ *ᵥ poseView p := by
  funext c
  have hrow : (moveMatrix a p.outerRot.val) 2 c =
      (p.outerRot.val * symReal a) 2 c := by
    unfold moveMatrix
    split_ifs
    · rw [Matrix.mul_assoc, row_two_screenHalfTurn_mul]
    · rw [Matrix.one_mul]
  simp only [poseView, MatrixPose.stellatedMove, hrow]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    poseView, mul_comm]

theorem poseView_viewAntipode (p : MatrixPose) :
    poseView p.viewAntipode = -poseView p := by
  funext c
  simp [poseView, MatrixPose.viewAntipode, MatrixPose.viewAntipodeRotation,
    Rx_mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem poseViewHalfTurn_viewAntipode (p : MatrixPose) :
    poseViewHalfTurn p.viewAntipode = poseViewHalfTurn p := by
  have hcomm : (Rx_mat Real.pi)ᵀ * symReal screenHalfTurn * Rx_mat Real.pi =
      symReal screenHalfTurn := by
    rw [symReal_screenHalfTurn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rx_mat, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [poseViewHalfTurn, MatrixPose.viewAntipode,
    MatrixPose.viewAntipodeRotation, Submonoid.coe_mul, Matrix.transpose_mul]
  rw [show p.outerRot.valᵀ * (Rx_mat Real.pi)ᵀ * symReal screenHalfTurn *
      (Rx_mat Real.pi * p.outerRot.val) =
    p.outerRot.valᵀ * ((Rx_mat Real.pi)ᵀ * symReal screenHalfTurn *
      Rx_mat Real.pi) * p.outerRot.val by simp only [Matrix.mul_assoc],
    hcomm]

theorem poseViewHalfTurn_stellatedMove_inner (p : MatrixPose) (b : SymIndex) :
    poseViewHalfTurn (p.stellatedMove 0 b) = poseViewHalfTurn p := by
  simp [poseViewHalfTurn, MatrixPose.stellatedMove, moveMatrix_zero]

theorem relativeRotation_stellatedMove_inner (p : MatrixPose) (b : SymIndex) :
    (p.stellatedMove 0 b).relativeRotation =
      relAct (poseViewHalfTurn p) p.relativeRotation b := by
  have h := orthogonal_of_SO3 p.outerRot
  have houter : (p.stellatedMove 0 b).outerRot.val = p.outerRot.val :=
    moveMatrix_zero _
  have hinner : (p.stellatedMove 0 b).innerRot.val =
      moveMatrix b p.innerRot.val := rfl
  simp only [MatrixPose.relativeRotation, houter, hinner, relAct,
    poseViewHalfTurn, moveMatrix]
  split_ifs
  · calc p.outerRot.valᵀ * (symReal screenHalfTurn * p.innerRot.val * symReal b) =
          p.outerRot.valᵀ * symReal screenHalfTurn *
            (p.outerRot.val * p.outerRot.valᵀ) * p.innerRot.val * symReal b := by
          rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · simp only [Matrix.one_mul, Matrix.mul_assoc]

/-- Every Rupert pose has a reduced Rupert representative. -/
theorem exists_reduced_rupert (p : MatrixPose)
    (hp : RupertPose p exactPolyhedron.hull) :
    ∃ q : MatrixPose, q.StellatedReduced ∧
      RupertPose q exactPolyhedron.hull := by
  obtain ⟨g, s, hg⟩ := exists_viewAct_inChamber (poseView p)
  let p0 := if s then p.viewAntipode else p
  have hp0 : RupertPose p0 exactPolyhedron.hull := by
    by_cases hs : s
    · simpa [p0, hs, MatrixPose.RupertPose_viewAntipode_iff] using hp
    · simpa [p0, hs] using hp
  have hview0 : poseView p0 = (if s then -1 else 1 : ℝ) • poseView p := by
    by_cases hs : s
    · simp [p0, hs, poseView_viewAntipode]
    · simp [p0, hs]
  let p1 := p0.stellatedMove g 0
  have hp1 : RupertPose p1 exactPolyhedron.hull :=
    (RupertPose_stellatedMove_iff p0 g 0).mpr hp0
  have hview1 : InChamber (poseView p1) := by
    have : poseView p1 = viewAct g s (poseView p) := by
      simp only [p1, poseView_stellatedMove, hview0, viewAct,
        Matrix.mulVec_smul]
    rw [this]
    exact hg
  obtain ⟨b, hb⟩ := exists_relAct_dirichlet (poseViewHalfTurn_mul_self p1)
    p1.relativeRotation
  let p2 := p1.stellatedMove 0 b
  refine ⟨p2, ⟨?_, ?_⟩, (RupertPose_stellatedMove_iff p1 0 b).mpr hp1⟩
  · have : poseView p2 = poseView p1 := by
      simp [p2, poseView_stellatedMove, symReal_zero]
    rw [this]
    exact hview1
  · intro b'
    rw [poseViewHalfTurn_stellatedMove_inner,
      relativeRotation_stellatedMove_inner]
    exact hb b'

end Noperts.Stellated

end
