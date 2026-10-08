module

public import Noperts.Basic
public import Noperts.Pose
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


namespace RationalApprox

noncomputable section

/- The below definitions are [SY25] Definition 37 -/

open scoped Nat -- for ! notation
/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯$ up to and including the degree $2n-1$ term.
-/
def sin_psum {k : Type} [Field k] (n : ℕ) (x : k) : k :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯$ up to and including the degree $2n-2$ degree term.
-/
def cos_psum {k : Type} [Field k] (n : ℕ) (x : k) : k :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / (2 * i)!)

/--
Round down to a multiple of `10⁻¹³`. Applied to the trig partial sums so that
the checker's rational arithmetic runs on small denominators (the raw partial
sums have denominators around `10²¹²`, making every downstream `ℚ` operation
a large-integer gcd). The rounding error is absorbed into the `κ/7` trig
budget of `sinℚ_approx'`/`cosℚ_approx'`. Defined via `Int.floor` so that it
commutes with the cast `ℚ → ℝ` (`Rat.floor_cast`). -/
def round13 {k : Type} [Field k] [LinearOrder k] [FloorRing k] (x : k) : k :=
  ⌊x * 10 ^ 13⌋ / 10 ^ 13

lemma abs_round13_sub_le {k : Type} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [FloorRing k] (x : k) : |round13 x - x| ≤ 1 / 10 ^ 13 := by
  have h10 : (0 : k) < 10 ^ 13 := by positivity
  have h1 : ((⌊x * 10 ^ 13⌋ : ℤ) : k) ≤ x * 10 ^ 13 := Int.floor_le _
  have h2 : x * 10 ^ 13 < ((⌊x * 10 ^ 13⌋ : ℤ) : k) + 1 := Int.lt_floor_add_one _
  have hrw : round13 x - x = (((⌊x * 10 ^ 13⌋ : ℤ) : k) - x * 10 ^ 13) / 10 ^ 13 := by
    unfold round13; field_simp
  rw [hrw, abs_div, abs_of_pos h10]
  gcongr
  rw [abs_le]
  constructor <;> linarith

/-- Componentwise `round13`: round each coordinate of a vector down to a
multiple of `10⁻¹³`. Applied to the per-pose hoisted vectors of the global
and local checkers so that the per-vertex dot products run on small
denominators; the rounding error is absorbed into the `κ` budgets.

NOTE: like every `Fin n → k` value, this is a closure, so each access
re-rounds. The checkers' hot loops must read each component once into a
scalar `let` or structure field (see `HScalars` in RationalGlobal.lean). -/
def round13v {k : Type} [Field k] [LinearOrder k] [FloorRing k] {n : ℕ}
    (v : Fin n → k) : Fin n → k :=
  fun i => round13 (v i)

/-- Rounding the left vector of a dot product perturbs it by at most
`(∑ i, |P i|) / 10¹³`. -/
lemma abs_round13v_dot_sub_le {k : Type} [Field k] [LinearOrder k]
    [IsStrictOrderedRing k] [FloorRing k] {n : ℕ} (v P : Fin n → k) :
    |round13v v ⬝ᵥ P - v ⬝ᵥ P| ≤ (∑ i, |P i|) / 10 ^ 13 := by
  have h : round13v v ⬝ᵥ P - v ⬝ᵥ P = ∑ i, (round13 (v i) - v i) * P i := by
    simp only [dotProduct, round13v, ← Finset.sum_sub_distrib, sub_mul]
  rw [h, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |round13 (v i) - v i| * |P i|
      ≤ (1 / 10 ^ 13) * |P i| :=
        mul_le_mul_of_nonneg_right (abs_round13_sub_le _) (abs_nonneg _)
    _ = |P i| / 10 ^ 13 := by ring

/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯ + x^{25}/25!$, rounded down to a
multiple of `10⁻¹³` (see `round13`).
-/
def sinℚ {k : Type} [Field k] [LinearOrder k] [FloorRing k] (x : k) : k :=
  round13 (sin_psum 13 x)

lemma sinℚ_match (x : ℚ) : sinℚ (k := ℚ) x = sinℚ (k := ℝ) x := by
  have h : ((sin_psum 13 x : ℚ) : ℝ) = sin_psum 13 (x : ℝ) := by
    unfold sin_psum; push_cast; rfl
  unfold sinℚ round13
  rw [← h]
  norm_cast

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯ + x^{24}/24!$, rounded down to a
multiple of `10⁻¹³` (see `round13`).
-/
def cosℚ {k : Type} [Field k] [LinearOrder k] [FloorRing k] (x : k) : k :=
  round13 (cos_psum 13 x)

lemma cosℚ_match (x : ℚ) : cosℚ (k := ℚ) x = cosℚ (k := ℝ) x := by
  have h : ((cos_psum 13 x : ℚ) : ℝ) = cos_psum 13 (x : ℝ) := by
    unfold cos_psum; push_cast; rfl
  unfold cosℚ round13
  rw [← h]
  norm_cast

/--
Frequently used constant for controlling the degree of approximation
of rational versions to real counterparts.
-/
def κℚ : ℚ := 1 / 10^10
def κ : ℝ := 1 / 10^10

/--
  A real polyhedron A and a rational polyhedron B that is a κ-approximation of A.
-/
structure κApproxPoly {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Polyhedron ι₁ ℝ³) (B : Polyhedron ι₂ (Fin 3 → ℚ)) where
  bijection : ι₁ ≃ ι₂
  approx : ∀ a : ι₁, ‖(A.v a : ℝ³) - toR3 (B.v (bijection a))‖ ≤ κ

end

def rotMℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-sinℚ θ, cosℚ θ, 0; -cosℚ θ * cosℚ φ, -sinℚ θ * cosℚ φ, sinℚ φ]

def rotMθℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-cosℚ θ, -sinℚ θ, 0; sinℚ θ * cosℚ φ, -cosℚ θ * cosℚ φ, 0]

def rotMφℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ]

def rotMθθℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![sinℚ θ, -cosℚ θ, 0; cosℚ θ * cosℚ φ, sinℚ θ * cosℚ φ, 0]

def rotMθφℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; -sinℚ θ * sinℚ φ, cosℚ θ * sinℚ φ, 0]

def rotMφφℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; cosℚ θ * cosℚ φ, sinℚ θ * cosℚ φ, -sinℚ φ]

def rotRℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![cosℚ α, -sinℚ α;
     sinℚ α,  cosℚ α]

def rotR'ℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![-sinℚ α, -cosℚ α;
     cosℚ α,  -sinℚ α]

def rotMℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMℚ_mat θ φ |>.toLin'

def rotMθℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMθℚ_mat θ φ |>.toLin'

def rotMφℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMφℚ_mat θ φ |>.toLin'

def rotMθθℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMθθℚ_mat θ φ |>.toLin'

def rotMθφℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMθφℚ_mat θ φ |>.toLin'

def rotMφφℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMφφℚ_mat θ φ |>.toLin'

def rotRℚ (α : ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotRℚ_mat α |>.toLin'

def rotR'ℚ (α : ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotR'ℚ_mat α |>.toLin'

def _root_.Pose.rotRℚ (p : Pose ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := _root_.RationalApprox.rotRℚ p.α

def _root_.Pose.rotR'ℚ (p : Pose ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := _root_.RationalApprox.rotR'ℚ p.α

def _root_.Pose.rotM₁ℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂ℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁θℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂θℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁φℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂φℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁θθℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθθℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂θθℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθθℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁θφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθφℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂θφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθφℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁φφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφφℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂φφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφφℚ p.θ₂ p.φ₂

def _root_.Pose.innerℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := p.rotRℚ ∘ₗ p.rotM₁ℚ
noncomputable
def rotMℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMφℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθθℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθθℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθφℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMφφℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMφφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotRℚℝ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotRℚ_mat α |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotR'ℚℝ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotR'ℚ_mat α |>.toEuclideanLin.toContinuousLinearMap

noncomputable section
end

structure UpperSqrt where
  f : ℚ → ℚ
  bound : ∀ (x : ℚ), 0 ≤ x → √x ≤ f x

end RationalApprox

end
