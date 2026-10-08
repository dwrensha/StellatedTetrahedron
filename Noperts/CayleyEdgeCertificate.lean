module

public import Noperts.BalancedSupport.Cycle
public import Noperts.Checker.RatQuadratic3
public import Noperts.Checker.RatTrigBall
public import Noperts.Cayley

@[expose] public section


/-!
# Normalized Cayley quadratics

The entries of `cayleyDenom x y z • cayleyMatrix x y z` are quadratics in the Cayley
coordinates.  This file names their ten monomial basis polynomials (`qOne`, `qx`, …,
`qzz`) and proves the evaluation identities for the numerator and denominator.
-/

namespace Noperts.CayleyEdgeCertificate

open scoped RealInnerProductSpace Matrix
open Noperts.Checker
open Noperts.BalancedSupport
open RationalApprox


def qOne : RatQuadratic3 := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def qx : RatQuadratic3 := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩
def qy : RatQuadratic3 := ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩
def qz : RatQuadratic3 := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩
def qxx : RatQuadratic3 := ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩
def qxy : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩
def qxz : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩
def qyy : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩
def qyz : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩
def qzz : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩

def denomQuadratic : RatQuadratic3 := qOne + qxx + qyy + qzz

def numeratorQuadratic : Matrix (Fin 3) (Fin 3) RatQuadratic3 :=
  !![qOne + qxx - qyy - qzz,
      RatQuadratic3.scale 2 (qxy - qz),
      RatQuadratic3.scale 2 (qxz + qy);
     RatQuadratic3.scale 2 (qxy + qz),
      qOne - qxx + qyy - qzz,
      RatQuadratic3.scale 2 (qyz - qx);
     RatQuadratic3.scale 2 (qxz - qy),
      RatQuadratic3.scale 2 (qyz + qx),
     qOne - qxx - qyy + qzz]

theorem eval_denomQuadratic (x y z : ℝ) :
    denomQuadratic.evalReal x y z = cayleyDenom x y z := by
  simp only [denomQuadratic, RatQuadratic3.evalReal_add]
  simp [qOne, qxx, qyy, qzz, RatQuadratic3.evalReal, cayleyDenom]
  ring

theorem eval_numeratorQuadratic (c j : Fin 3) (x y z : ℝ) :
    (numeratorQuadratic c j).evalReal x y z =
      cayleyNumeratorMatrix x y z c j := by
  fin_cases c <;> fin_cases j <;>
    simp only [numeratorQuadratic] <;>
    simp [qOne, qx, qy, qz, qxx, qxy, qxz, qyy, qyz, qzz,
      RatQuadratic3.evalReal, cayleyNumeratorMatrix] <;> ring

end Noperts.CayleyEdgeCertificate

end
