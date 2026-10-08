module

public import Noperts.Stellated.ChartKernelGlobal
public import Noperts.Stellated.AtlasProjectiveMixedGlobalCertificate

@[expose] public section

/-!
# A packed integer checker for mixed global certificates

The four components are checked by `ChartKernelG.globalCore` (admissibility and
hinted weighted defects, three hints per component), and the mixture's Bernstein
controls are the integer combination `Σ_k f_k · ctlPair_k` of the components'
packed control vectors, `f_k = a_k ∏_{l ≠ k} μ_l.den` with `w_k = a_k / D`.
-/

namespace Noperts.Stellated.ChartKernelM

open ChartKernel ChartKernelG PackedSlots
open AtlasProjectiveMixedGlobalCertificate

/-- The common denominator of the mixture weights. -/
def wDen (mb : Box) : ℕ := lcmList [mb.weight 0, mb.weight 1, mb.weight 2, mb.weight 3]

/-- The integer mixture weights `a_k = D w_k`. -/
def aW (mb : Box) (k : Fin 4) : ℤ := qScale (wDen mb) (mb.weight k)

def μd (mb : Box) (k : Fin 4) : ℤ := ((mb.componentBox k).ballMultiplier.den : ℤ)

/-- `∏_{l ≠ k} μ_l.den`. -/
def μOther (mb : Box) : Fin 4 → ℤ
  | 0 => μd mb 1 * μd mb 2 * μd mb 3
  | 1 => μd mb 0 * μd mb 2 * μd mb 3
  | 2 => μd mb 0 * μd mb 1 * μd mb 3
  | 3 => μd mb 0 * μd mb 1 * μd mb 2

def μAll (mb : Box) : ℤ := μd mb 0 * μd mb 1 * μd mb 2 * μd mb 3

/-- The hint sum of component `k`. -/
def hintK (hints : List ℤ) (k : Fin 4) : ℤ :=
  hints.getD (3 * k.val) 0 + (hints.getD (3 * k.val + 1) 0 + hints.getD (3 * k.val + 2) 0)

def mixPair (mb : Box) (i j : Fin 3) : (ℕ × ℕ) × ℕ :=
  let c := fun k => ctlPair (mb.componentBox k) i j
  let f := fun k => aW mb k * μOther mb k
  (pairAdd (pairSmul (f 0) (c 0).1) (pairAdd (pairSmul (f 1) (c 1).1)
      (pairAdd (pairSmul (f 2) (c 2).1) (pairSmul (f 3) (c 3).1))),
    (f 0).natAbs * (c 0).2 + ((f 1).natAbs * (c 1).2 +
      ((f 2).natAbs * (c 2).2 + (f 3).natAbs * (c 3).2)))

def validMixedK (mb : Box) (hints : List ℤ) : Bool :=
  let c0 := mb.componentBox 0
  let sh := shell c0
  let D : ℤ := wDen mb
  let HA : ℤ := aW mb 0 * hintK hints 0 + (aW mb 1 * hintK hints 1 +
    (aW mb 2 * hintK hints 2 + aW mb 3 * hintK hints 3))
  let th := ceilDiv (4 * μAll mb * dBoundNum sh * HA * 10 ^ 10 +
    2400 * μAll mb * D * σ0 c0 * dBoundNum sh) (10 ^ 10)
  (List.finRange 4).all (fun k =>
    decide (0 ≤ aW mb k) && globalCore (mb.componentBox k) (hints.drop (3 * k.val))) &&
  decide (aW mb 0 + aW mb 1 + aW mb 2 + aW mb 3 = D) &&
  ctlIndices.all fun p => ctlOk (mixPair mb p.1 p.2).1 (mixPair mb p.1 p.2).2 th

/-- Native hint generation: the global hints of each component. -/
def mixedHints (mb : Box) : List ℤ :=
  (List.finRange 4).flatMap fun k => globalHints (mb.componentBox k)

end Noperts.Stellated.ChartKernelM
