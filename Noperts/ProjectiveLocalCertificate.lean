module

public import Noperts.Checker.RatQuadratic3
public import Noperts.Checker.SqrtFixed
public import Noperts.RationalRotation
public import Noperts.ProjectiveView

@[expose] public section


/-!
# Rational helpers for projective local certificates

Rational vectors, coordinate bounds over projective triangles (`min3`/`max3`), products
of linear forms, and the coordinate-sum bound on the Euclidean norm.
-/

namespace Noperts.ProjectiveLocalCertificate

open scoped RealInnerProductSpace
open Noperts.Checker
open Noperts.BalancedSupport
open CayleyEdgeCertificate ProjectiveView

def max3 (f : Fin 3 → ℚ) : ℚ := max (f 0) (max (f 1) (f 2))
def min3 (f : Fin 3 → ℚ) : ℚ := min (f 0) (min (f 1) (f 2))

theorem le_max3 (f : Fin 3 → ℚ) (i : Fin 3) : f i ≤ max3 f := by
  fin_cases i <;> simp [max3]

theorem min3_le (f : Fin 3 → ℚ) (i : Fin 3) : min3 f ≤ f i := by
  fin_cases i <;> simp [min3]

abbrev VectorQ := Fin 3 → ℚ

/-- Product of two homogeneous linear forms. -/
def mulLinear (a b : VectorQ) : RatQuadratic3 :=
  { c0 := 0, cx := 0, cy := 0, cz := 0,
    cxx := a 0 * b 0,
    cxy := a 0 * b 1 + a 1 * b 0,
    cxz := a 0 * b 2 + a 2 * b 0,
    cyy := a 1 * b 1,
    cyz := a 1 * b 2 + a 2 * b 1,
    czz := a 2 * b 2 }

theorem evalReal_mulLinear (a b : VectorQ) (n : Fin 3 → ℝ) :
    (mulLinear a b).evalReal (n 0) (n 1) (n 2) =
      linearValue n (fun c => (a c : ℝ)) *
        linearValue n (fun c => (b c : ℝ)) := by
  simp [mulLinear, RatQuadratic3.evalReal, linearValue]
  ring

def unitCoordinate (coordinate : Fin 3) : Fin 3 → ℝ :=
  fun c => if c = coordinate then 1 else 0

@[simp] theorem linearValue_unitCoordinate (n : Fin 3 → ℝ)
    (coordinate : Fin 3) :
    linearValue n (unitCoordinate coordinate) = n coordinate := by
  fin_cases coordinate <;> simp [linearValue, unitCoordinate]

theorem coordinate_mem_triangleBounds {triangle : Triangle ℚ}
    {n : Fin 3 → ℝ} (hmem : InTriangle (toReal triangle) n)
    (coordinate : Fin 3) :
    n coordinate ∈ Set.Icc
      ((min3 (fun j => triangle j coordinate) : ℚ) : ℝ)
      ((max3 (fun j => triangle j coordinate) : ℚ) : ℝ) := by
  constructor
  · rw [← linearValue_unitCoordinate n coordinate]
    apply le_linearValue_of_mem hmem
    intro j
    have hmin := min3_le (fun j => triangle j coordinate) j
    rw [linearValue_unitCoordinate]
    change ((min3 (fun j => triangle j coordinate) : ℚ) : ℝ) ≤
      (triangle j coordinate : ℝ)
    exact_mod_cast hmin
  · rw [← linearValue_unitCoordinate n coordinate]
    apply linearValue_le_of_mem hmem
    intro j
    have hmax := le_max3 (fun j => triangle j coordinate) j
    rw [linearValue_unitCoordinate]
    change (triangle j coordinate : ℝ) ≤
      ((max3 (fun j => triangle j coordinate) : ℚ) : ℝ)
    exact_mod_cast hmax

theorem norm_le_sum_abs_coordinates (v : ℝ³) :
    ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2),
      sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]

theorem norm_quarterTurn (u : ℝ²) : ‖quarterTurn u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [quarterTurn, Fin.sum_univ_two, sq_abs]
  ring

end Noperts.ProjectiveLocalCertificate

end
