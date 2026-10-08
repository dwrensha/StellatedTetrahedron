module

public import Noperts.Stellated.AtlasProjectiveView

@[expose] public section

/-!
# View-dependent flip pruning

For each `b ∈ O \ T` there is an integer bilinear form `ℓ_b(X, v)` in the
Cayley vector `X = (x,y,z)` and the unit view `v` with

    d · trace (H_v · C(X) · b) = 2 ℓ_b(X,v)² - d,     d · trace C(X) = 4 - d,

where `d = 1 + |X|²` and `H_v = 2vvᵀ - 1`.  Hence the flip part of the
Dirichlet cell is `ℓ_b(X,v)² ≤ 2`.  Since `ℓ_b` is linear in `v`, and the
view is a multiple `σ ≥ 1` of a point of the rational view triangle, a box is
pruned once `s · ℓ_b(X, tᵢ) ≥ L` at the three triangle corners `tᵢ`, for a
sign `s` and a rational `L` with `L > 0` and `L² > 2`.
-/

namespace Noperts.Stellated.FlipPrune

open scoped Matrix
open AtlasProjectiveView Noperts.ProjectiveView

-- BEGIN GENERATED (gen_flip_prune.py)

/-- Coefficients of `ℓ_k`: row `c` holds the coefficients of `v c` in the
basis `1, x, y, z`. -/
def flipCoeff : Fin 12 → Fin 3 → Fin 4 → ℚ := ![
  !![-1, 1, 0, 0; 0, 0, 1, -1; 0, 0, 1, 1],
  !![1, 1, 0, 0; 0, 0, 1, 1; 0, 0, -1, 1],
  !![0, 0, -1, 1; -1, 1, 0, 0; -1, -1, 0, 0],
  !![0, 0, -1, -1; 1, 1, 0, 0; -1, 1, 0, 0],
  !![1, 0, 0, -1; 1, 0, 0, 1; 0, 1, -1, 0],
  !![0, 1, -1, 0; 0, 1, 1, 0; -1, 0, 0, 1],
  !![0, 1, 1, 0; 0, -1, 1, 0; 1, 0, 0, 1],
  !![-1, 0, 0, -1; 1, 0, 0, -1; 0, 1, 1, 0],
  !![0, 1, 0, -1; 1, 0, 1, 0; 0, 1, 0, 1],
  !![-1, 0, -1, 0; 0, 1, 0, -1; -1, 0, 1, 0],
  !![0, 1, 0, 1; -1, 0, 1, 0; 0, -1, 0, 1],
  !![1, 0, -1, 0; 0, 1, 0, 1; -1, 0, -1, 0]]

theorem flipCoeff_0 : flipCoeff 0 = !![-1, 1, 0, 0; 0, 0, 1, -1; 0, 0, 1, 1] := rfl

theorem flipCoeff_1 : flipCoeff 1 = !![1, 1, 0, 0; 0, 0, 1, 1; 0, 0, -1, 1] := rfl

theorem flipCoeff_2 : flipCoeff 2 = !![0, 0, -1, 1; -1, 1, 0, 0; -1, -1, 0, 0] := rfl

theorem flipCoeff_3 : flipCoeff 3 = !![0, 0, -1, -1; 1, 1, 0, 0; -1, 1, 0, 0] := rfl

theorem flipCoeff_4 : flipCoeff 4 = !![1, 0, 0, -1; 1, 0, 0, 1; 0, 1, -1, 0] := rfl

theorem flipCoeff_5 : flipCoeff 5 = !![0, 1, -1, 0; 0, 1, 1, 0; -1, 0, 0, 1] := rfl

theorem flipCoeff_6 : flipCoeff 6 = !![0, 1, 1, 0; 0, -1, 1, 0; 1, 0, 0, 1] := rfl

theorem flipCoeff_7 : flipCoeff 7 = !![-1, 0, 0, -1; 1, 0, 0, -1; 0, 1, 1, 0] := rfl

theorem flipCoeff_8 : flipCoeff 8 = !![0, 1, 0, -1; 1, 0, 1, 0; 0, 1, 0, 1] := rfl

theorem flipCoeff_9 : flipCoeff 9 = !![-1, 0, -1, 0; 0, 1, 0, -1; -1, 0, 1, 0] := rfl

theorem flipCoeff_10 : flipCoeff 10 = !![0, 1, 0, 1; -1, 0, 1, 0; 0, -1, 0, 1] := rfl

theorem flipCoeff_11 : flipCoeff 11 = !![1, 0, -1, 0; 0, 1, 0, 1; -1, 0, -1, 0] := rfl

/-- The bilinear form `ℓ_k(X, v)`. -/
noncomputable def flipForm (k : Fin 12) (x y z : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ c, v c * ((flipCoeff k c 0 : ℝ) + flipCoeff k c 1 * x +
    flipCoeff k c 2 * y + flipCoeff k c 3 * z)

/-- The half-turn `2vvᵀ - 1` about a unit vector. -/
noncomputable def halfTurnOf (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2 * v 0 * v 0 - 1, 2 * v 0 * v 1, 2 * v 0 * v 2;
     2 * v 1 * v 0, 2 * v 1 * v 1 - 1, 2 * v 1 * v 2;
     2 * v 2 * v 0, 2 * v 2 * v 1, 2 * v 2 * v 2 - 1]

private theorem trace_flip_0 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 12) =
      2 * flipForm 0 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_12,
    flipForm, flipCoeff_0, cayleyDenom, Fin.sum_univ_three]
  linear_combination (4*x - 2*y^2 - 2*z^2) * hv

private theorem trace_flip_1 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 13) =
      2 * flipForm 1 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_13,
    flipForm, flipCoeff_1, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-4*x - 2*y^2 - 2*z^2) * hv

private theorem trace_flip_2 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 14) =
      2 * flipForm 2 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_14,
    flipForm, flipCoeff_2, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-2*x^2 + 4*y*z - 2) * hv

private theorem trace_flip_3 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 15) =
      2 * flipForm 3 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_15,
    flipForm, flipCoeff_3, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-2*x^2 - 4*y*z - 2) * hv

private theorem trace_flip_4 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 16) =
      2 * flipForm 4 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_16,
    flipForm, flipCoeff_4, cayleyDenom, Fin.sum_univ_three]
  linear_combination (4*x*y - 2*z^2 - 2) * hv

private theorem trace_flip_5 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 17) =
      2 * flipForm 5 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_17,
    flipForm, flipCoeff_5, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-2*x^2 - 2*y^2 + 4*z) * hv

private theorem trace_flip_6 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 18) =
      2 * flipForm 6 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_18,
    flipForm, flipCoeff_6, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-2*x^2 - 2*y^2 - 4*z) * hv

private theorem trace_flip_7 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 19) =
      2 * flipForm 7 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_19,
    flipForm, flipCoeff_7, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-4*x*y - 2*z^2 - 2) * hv

private theorem trace_flip_8 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 20) =
      2 * flipForm 8 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_20,
    flipForm, flipCoeff_8, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-2*x^2 - 4*y - 2*z^2) * hv

private theorem trace_flip_9 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 21) =
      2 * flipForm 9 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_21,
    flipForm, flipCoeff_9, cayleyDenom, Fin.sum_univ_three]
  linear_combination (4*x*z - 2*y^2 - 2) * hv

private theorem trace_flip_10 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 22) =
      2 * flipForm 10 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_22,
    flipForm, flipCoeff_10, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-2*x^2 + 4*y - 2*z^2) * hv

private theorem trace_flip_11 (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z * symReal 23) =
      2 * flipForm 11 x y z v ^ 2 - cayleyDenom x y z := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.mul_apply]
  simp [halfTurnOf, cayleyNumeratorMatrix, symReal, symMatrix_23,
    flipForm, flipCoeff_11, cayleyDenom, Fin.sum_univ_three]
  linear_combination (-4*x*z - 2*y^2 - 2) * hv

-- END GENERATED

/-! ## The general identity -/

/-- The flip symmetry attached to a form index. -/
def flipSym (k : Fin 12) : SymIndex := ⟨k.val + 12, by omega⟩

theorem isFlip_flipSym (k : Fin 12) : isFlip (flipSym k) = true := by
  simp [isFlip, flipSym]

theorem trace_flip (k : Fin 12) (x y z : ℝ) (v : Fin 3 → ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    Matrix.trace (halfTurnOf v * cayleyNumeratorMatrix x y z *
        symReal (flipSym k)) =
      2 * flipForm k x y z v ^ 2 - cayleyDenom x y z := by
  fin_cases k
  · exact trace_flip_0 x y z v hv
  · exact trace_flip_1 x y z v hv
  · exact trace_flip_2 x y z v hv
  · exact trace_flip_3 x y z v hv
  · exact trace_flip_4 x y z v hv
  · exact trace_flip_5 x y z v hv
  · exact trace_flip_6 x y z v hv
  · exact trace_flip_7 x y z v hv
  · exact trace_flip_8 x y z v hv
  · exact trace_flip_9 x y z v hv
  · exact trace_flip_10 x y z v hv
  · exact trace_flip_11 x y z v hv

theorem trace_cayleyNumerator (x y z : ℝ) :
    Matrix.trace (cayleyNumeratorMatrix x y z) = 4 - cayleyDenom x y z := by
  simp [Matrix.trace, cayleyNumeratorMatrix, cayleyDenom, Fin.sum_univ_three]
  ring

/-- For an orthogonal `O`, conjugating the screen half-turn gives the
half-turn about the third row of `O`. -/
theorem conj_screenHalfTurn {O : Matrix (Fin 3) (Fin 3) ℝ}
    (hO : Oᵀ * O = 1) :
    Oᵀ * symReal screenHalfTurn * O = halfTurnOf (fun c => O 2 c) := by
  rw [symReal_screenHalfTurn]
  ext i j
  have h := congrFun (congrFun hO i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    Matrix.one_apply] at h
  fin_cases i <;> fin_cases j <;>
    simp [halfTurnOf, Matrix.mul_apply, Fin.sum_univ_three] at h ⊢ <;>
    linear_combination -h

theorem viewHalfTurn_eq (p : AtlasPose ℝ) :
    p.viewHalfTurn = halfTurnOf p.view := by
  have hO : (rotRM_mat p.θ p.φ 0)ᵀ * rotRM_mat p.θ p.φ 0 = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp (rotRM_mat_mem_SO3 _ _ _)).1
  rw [AtlasPose.viewHalfTurn, conj_screenHalfTurn hO]
  congr 1
  funext c
  rw [rotRM_mat_row_two]
  rfl

theorem view_norm_sq (p : AtlasPose ℝ) :
    p.view 0 ^ 2 + p.view 1 ^ 2 + p.view 2 ^ 2 = 1 := by
  simp only [AtlasPose.view, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hθ := Real.sin_sq_add_cos_sq p.θ
  have hφ := Real.sin_sq_add_cos_sq p.φ
  linear_combination (Real.sin p.φ ^ 2) * hθ + hφ

theorem denom_mul_trace (M B : Matrix (Fin 3) (Fin 3) ℝ) (x y z : ℝ) :
    cayleyDenom x y z * Matrix.trace (M * cayleyMatrix x y z * B) =
      Matrix.trace (M * cayleyNumeratorMatrix x y z * B) := by
  rw [cayleyNumeratorMatrix_eq_denom_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]

theorem denom_mul_trace_cayley (x y z : ℝ) :
    cayleyDenom x y z * Matrix.trace (cayleyMatrix x y z) =
      Matrix.trace (cayleyNumeratorMatrix x y z) := by
  rw [cayleyNumeratorMatrix_eq_denom_smul, Matrix.trace_smul, smul_eq_mul]

/-- The flip half of the Dirichlet cell, as a bound on `ℓ`. -/
theorem flipForm_sq_le_of_flipReduced {p : AtlasPose ℝ}
    (h : p.FlipReduced) (k : Fin 12) :
    flipForm k p.x p.y p.z p.view ^ 2 ≤ 2 := by
  have hk := h (flipSym k) (isFlip_flipSym k)
  have hd := cayleyDenom_pos p.x p.y p.z
  have hmul := mul_le_mul_of_nonneg_left hk hd.le
  rw [relAct, isFlip_flipSym, ite_eq_left rfl, viewHalfTurn_eq] at hmul
  rw [denom_mul_trace, denom_mul_trace_cayley,
    trace_flip k _ _ _ _ (view_norm_sq p), trace_cayleyNumerator] at hmul
  linarith

/-! ## Rational checker -/

/-- Affine coefficients of `ℓ_k(X, t)` for a fixed rational corner `t`. -/
def cornerCoeff (k : Fin 12) (t : Fin 3 → ℚ) (j : Fin 4) : ℚ :=
  ∑ c, t c * flipCoeff k c j

theorem flipForm_corner (k : Fin 12) (x y z : ℝ) (t : Fin 3 → ℚ) :
    flipForm k x y z (fun c => (t c : ℝ)) =
      (cornerCoeff k t 0 : ℝ) + cornerCoeff k t 1 * x +
        cornerCoeff k t 2 * y + cornerCoeff k t 3 * z := by
  simp only [flipForm, cornerCoeff, Fin.sum_univ_three]
  push_cast
  ring

structure Box where
  interval : AtlasInterval ℚ
  triangle : AtlasProjectiveView.Triangle ℚ
  form : Fin 12
  negate : Bool
deriving DecidableEq

def Box.sign (box : Box) : ℚ := if box.negate then -1 else 1

/-- Center and radius of the Cayley coordinate `j ∈ {1,2,3}` (`x,y,z`). -/
def Box.center (box : Box) (j : Fin 3) : ℚ :=
  (box.interval.min.get (j.succ.succ.castLT (by omega)) +
    box.interval.max.get (j.succ.succ.castLT (by omega))) / 2

def Box.radius (box : Box) (j : Fin 3) : ℚ :=
  (box.interval.max.get (j.succ.succ.castLT (by omega)) -
    box.interval.min.get (j.succ.succ.castLT (by omega))) / 2

/-- Lower bound of `sign · ℓ(X, tᵢ)` over the Cayley box. -/
def Box.cornerLower (box : Box) (i : Fin 3) : ℚ :=
  let a := fun j => box.sign * cornerCoeff box.form (box.triangle i) j
  a 0 + a 1 * box.center 0 + a 2 * box.center 1 + a 3 * box.center 2 -
    (|a 1| * box.radius 0 + |a 2| * box.radius 1 + |a 3| * box.radius 2)

def Box.lower (box : Box) : ℚ :=
  min (box.cornerLower 0) (min (box.cornerLower 1) (box.cornerLower 2))

/-- Upper bound for `|w|²` over the view triangle (attained at a corner). -/
def Box.maxNormSq (box : Box) : ℚ :=
  let n := fun i => ∑ c, box.triangle i c ^ 2
  max (n 0) (max (n 1) (n 2))

/-- The view is `w / |w|` for `w` in the triangle, so `ℓ(v)² = ℓ(w)² / |w|²`;
it suffices that `L² > 2 · max |tᵢ|²`. -/
def Box.Valid (box : Box) : Prop :=
  0 < box.lower ∧ 2 * box.maxNormSq < box.lower ^ 2

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

private theorem sq_weighted_le (w a : Fin 3 → ℝ) (h0 : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) :
    (∑ i, w i * a i) ^ 2 ≤ ∑ i, w i * a i ^ 2 := by
  simp only [Fin.sum_univ_three] at h1 ⊢
  have e01 := mul_nonneg (mul_nonneg (h0 0) (h0 1)) (sq_nonneg (a 0 - a 1))
  have e02 := mul_nonneg (mul_nonneg (h0 0) (h0 2)) (sq_nonneg (a 0 - a 2))
  have e12 := mul_nonneg (mul_nonneg (h0 1) (h0 2)) (sq_nonneg (a 1 - a 2))
  have hsum : w 0 * a 0 ^ 2 + w 1 * a 1 ^ 2 + w 2 * a 2 ^ 2 -
      (w 0 * a 0 + w 1 * a 1 + w 2 * a 2) ^ 2 =
      w 0 * w 1 * (a 0 - a 1) ^ 2 + w 0 * w 2 * (a 0 - a 2) ^ 2 +
        w 1 * w 2 * (a 1 - a 2) ^ 2 := by
    linear_combination
      (-(w 0 * a 0 ^ 2 + w 1 * a 1 ^ 2 + w 2 * a 2 ^ 2)) * h1
  linarith

private theorem affine_lower {a t c r : ℝ} (ht : |t - c| ≤ r) :
    a * c - |a| * r ≤ a * t := by
  have h1 : -(|a| * |t - c|) ≤ a * (t - c) := by
    rw [← abs_mul]; exact neg_abs_le _
  have h2 : |a| * |t - c| ≤ |a| * r := mul_le_mul_of_nonneg_left ht (abs_nonneg a)
  nlinarith

theorem Box.cornerLower_le (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (i : Fin 3) :
    (box.cornerLower i : ℝ) ≤
      box.sign * flipForm box.form p.x p.y p.z
        (fun c => (box.triangle i c : ℝ)) := by
  have hmem := AtlasInterval.mem_toReal_iff.mp hp
  have hx := hmem 2
  have hy := hmem 3
  have hz := hmem 4
  simp [AtlasPose.get, AtlasPose.equivPi] at hx hy hz
  have habs : ∀ {t lo hi : ℝ}, lo ≤ t → t ≤ hi →
      |t - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
    intro t lo hi hlo hhi
    rw [abs_le]; constructor <;> linarith
  rw [flipForm_corner]
  simp only [Box.cornerLower, Box.center, Box.radius]
  push_cast
  have e1 := affine_lower (a := (box.sign * cornerCoeff box.form (box.triangle i) 1 : ℚ))
    (habs hx.1 hx.2)
  have e2 := affine_lower (a := (box.sign * cornerCoeff box.form (box.triangle i) 2 : ℚ))
    (habs hy.1 hy.2)
  have e3 := affine_lower (a := (box.sign * cornerCoeff box.form (box.triangle i) 3 : ℚ))
    (habs hz.1 hz.2)
  push_cast at e1 e2 e3
  simp [AtlasPose.get, AtlasPose.equivPi] at e1 e2 e3 ⊢
  nlinarith [e1, e2, e3]

theorem Box.valid_not_flipReduced (box : Box) (hvalid : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hscale : 1 ≤ viewScale 0 p)
    (hmem : InTriangle (toReal box.triangle) (normalizedView 0 p)) :
    ¬ p.FlipReduced := by
  intro hflip
  have hsq := flipForm_sq_le_of_flipReduced hflip box.form
  obtain ⟨weight, hw0, hw1, hpoint⟩ := hmem
  have hscale0 : 0 < viewScale 0 p := lt_of_lt_of_le one_pos hscale
  have hL0 : (0 : ℝ) < (box.lower : ℝ) := by exact_mod_cast hvalid.1
  -- the view is `σ` times the affine point
  have hview : p.view = fun c =>
      viewScale 0 p * ∑ i, weight i * (box.triangle i c : ℝ) := by
    funext c
    have := congrFun hpoint c
    simp only [AtlasProjectiveView.normalizedView, affinePoint, toReal] at this
    rw [← this, ← viewVector_eq_view]
    field_simp
  -- linearity of `ℓ` in the view
  have hlin : box.sign * flipForm box.form p.x p.y p.z p.view =
      viewScale 0 p * ∑ i, weight i *
        (box.sign * flipForm box.form p.x p.y p.z
          (fun c => (box.triangle i c : ℝ))) := by
    rw [hview]
    simp only [flipForm, Fin.sum_univ_three]
    ring
  have hlower : (box.lower : ℝ) ≤ ∑ i, weight i *
      (box.sign * flipForm box.form p.x p.y p.z
        (fun c => (box.triangle i c : ℝ))) := by
    have hle : ∀ i, (box.lower : ℝ) ≤ box.sign * flipForm box.form p.x p.y p.z
        (fun c => (box.triangle i c : ℝ)) := by
      intro i
      refine le_trans ?_ (box.cornerLower_le hp i)
      have : box.lower ≤ box.cornerLower i := by
        fin_cases i <;> simp [Box.lower]
      exact_mod_cast this
    calc (box.lower : ℝ) = ∑ i, weight i * (box.lower : ℝ) := by rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hle i) (hw0 i)
  have hsign : (box.sign : ℝ) ^ 2 = 1 := by
    unfold Box.sign; split_ifs <;> norm_num
  set σ := viewScale 0 p
  set S := ∑ i, weight i * (box.sign * flipForm box.form p.x p.y p.z
    (fun c => (box.triangle i c : ℝ)))
  -- `σ² |w|² = 1`, and `|w|² ≤ M`
  have hunit : σ ^ 2 * ∑ c, (∑ i, weight i * (box.triangle i c : ℝ)) ^ 2 = 1 := by
    have hn := view_norm_sq p
    rw [hview] at hn
    simp only [Fin.sum_univ_three] at hn ⊢
    linear_combination hn
  have hM : ∑ c, (∑ i, weight i * (box.triangle i c : ℝ)) ^ 2 ≤
      (box.maxNormSq : ℝ) := by
    calc ∑ c, (∑ i, weight i * (box.triangle i c : ℝ)) ^ 2
        ≤ ∑ c, ∑ i, weight i * (box.triangle i c : ℝ) ^ 2 :=
          Finset.sum_le_sum fun c _ =>
            sq_weighted_le weight (fun i => (box.triangle i c : ℝ)) hw0 hw1
      _ = ∑ i, weight i * ∑ c, (box.triangle i c : ℝ) ^ 2 := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ ∑ i, weight i * (box.maxNormSq : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hw0 i)
          have : ∑ c, box.triangle i c ^ 2 ≤ box.maxNormSq := by
            fin_cases i <;> simp [Box.maxNormSq]
          exact_mod_cast this
      _ = box.maxNormSq := by rw [← Finset.sum_mul, hw1, one_mul]
  have hS : (box.lower : ℝ) ≤ S := hlower
  have hS2 : (box.lower : ℝ) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hL0.le hS 2
  have hvalid2 : 2 * (box.maxNormSq : ℝ) < (box.lower : ℝ) ^ 2 := by
    exact_mod_cast hvalid.2
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hℓ : flipForm box.form p.x p.y p.z p.view ^ 2 = σ ^ 2 * S ^ 2 := by
    have := congrArg (· ^ 2) hlin
    simp only [mul_pow, hsign, one_mul] at this
    exact this
  -- `ℓ² = σ² S² ≥ σ² L² > σ² · 2M ≥ 2 σ² |w|² = 2`
  have hσpos : 0 < σ ^ 2 := by positivity
  have : 2 < flipForm box.form p.x p.y p.z p.view ^ 2 := by
    rw [hℓ]
    nlinarith [mul_le_mul_of_nonneg_left hS2 hσ2,
      mul_lt_mul_of_pos_left hvalid2 hσpos, mul_le_mul_of_nonneg_left hM hσ2]
  linarith

end Noperts.Stellated.FlipPrune

end
