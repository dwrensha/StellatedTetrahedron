module

public import Noperts.Stellated.ChartKernelEdge
public import Noperts.Stellated.LocalKernel
public import Noperts.Stellated.AtlasProjectiveGlobalCertificate

@[expose] public section

/-!
# A packed integer checker for global projective certificates

`validGlobalK box hints` decides a sufficient condition for
`AtlasProjectiveGlobalCertificate.Box.Valid` in the style of
`ChartKernel.validEdgeK`: the triangle is scaled by the common denominator
`L` of its entries, edges by `40000`, vertices by `40`, so weights carry the
scale `L·40000²`, supports `L·40000·40`, and the contact quadratics `40000·40`.
The displacement test uses only the Bernstein bound (it certifies every
sampled row), evaluated as packed 27-slot vectors; the weighted support
defect of contact `i` is bounded by a generator-supplied hint `hints[i]`,
checked slot-wise on the packed 72-slot vector of symmetric controls.
-/

namespace Noperts.Stellated.ChartKernelG

open ChartKernel PackedSlots AtlasProjectiveGlobalCertificate AtlasProjectiveView
open LocalKernel (V3 edgeN wcN)

/-- An edge-certificate shell carrying the global box's interval and view, so
that the edge checker's integer Bernstein machinery applies verbatim. -/
def shell (b : Box) : AtlasProjectiveEdgeCertificate.Box where
  interval := b.interval
  root := b.root
  triangle := b.triangle
  chart := b.chart
  edgePred := 0
  outerIndex := fun _ => 0
  innerIndex := fun _ => 0
  nonzeroWitness := fun _ => 0
  ballMultiplier := fun _ => b.ballMultiplier

/-- Row `j` of the scaled triangle. -/
def trow (b : Box) (j : Fin 3) : V3 := ⟨T (shell b) j 0, T (shell b) j 1, T (shell b) j 2⟩

/-- `L² · 40000² · 40000 · 40`. -/
def σ0 (b : Box) : ℤ := (triL (shell b) : ℤ) ^ 2 * 2560000000000000

/-- Closed table of `dispI`. -/
def dispTab : List (List (List (List IQ))) :=
  List.ofFn fun ch : CayleyAtlas.ChartIndex => List.ofFn fun u : VertexIndex =>
    List.ofFn fun o : VertexIndex => List.ofFn fun c : Fin 3 => dispI ch u o c

def dispT (ch : CayleyAtlas.ChartIndex) (u o : VertexIndex) (c : Fin 3) : IQ :=
  (((dispTab.getD ch.val []).getD u.val []).getD o.val []).getD c.val IQ.zero

/-- `40000 · 40 ·` the contact quadratic `(i, c)`. -/
def cqG (b : Box) (i c : Fin 3) : IQ :=
  let e := edgeN b.certificate i
  let d := dispT b.chart (b.innerIndex i) (b.certificate.index i)
  match c with
  | 0 => IQ.sub (IQ.smul e.y (d 2)) (IQ.smul e.z (d 1))
  | 1 => IQ.sub (IQ.smul e.z (d 0)) (IQ.smul e.x (d 2))
  | 2 => IQ.sub (IQ.smul e.x (d 1)) (IQ.smul e.y (d 0))

def cayI : IQ := ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩

/-- The packed Bernstein vector of an integer quadratic on the box. -/
def bvec (b : Box) (q : IQ) : ℕ × ℕ := bernPairK (bernWeights (shell b) q)

def bbound (b : Box) (q : IQ) : ℕ := boundK (bernWeights (shell b) q)

/-- `σ ·` the adjusted view quadratic at the view `t` (`t = L n`), as a packed
Bernstein vector; `s = 1` at corners, `s = 4` at doubled midpoints. -/
def viewVec (b : Box) (B : Fin 3 → Fin 3 → ℕ × ℕ) (Bc : ℕ × ℕ) (t : V3) (s : ℤ) : ℕ × ℕ :=
  let μ := b.ballMultiplier
  let α := fun i c => (μ.den : ℤ) * V3.dot t (wcN b.certificate i) * V3.get t c
  let row := fun i => pairAdd (pairSmul (α i 0) (B i 0))
    (pairAdd (pairSmul (α i 1) (B i 1)) (pairSmul (α i 2) (B i 2)))
  pairAdd (pairAdd (row 0) (pairAdd (row 1) (row 2))) (pairSmul (μ.num * s * σ0 b) Bc)

def viewBound (b : Box) (MB : Fin 3 → Fin 3 → ℕ) (Mc : ℕ) (t : V3) (s : ℤ) : ℕ :=
  let μ := b.ballMultiplier
  let α := fun i c => (μ.den : ℤ) * V3.dot t (wcN b.certificate i) * V3.get t c
  let row := fun i => (α i 0).natAbs * MB i 0 + ((α i 1).natAbs * MB i 1 +
    (α i 2).natAbs * MB i 2)
  (row 0 + (row 1 + row 2)) + (μ.num * s * σ0 b).natAbs * Mc

/-! ### Weighted support defects -/

/-- Coordinate `d` of `trow b × edgeN i`, over `b` (zero for `b ≥ 3`). -/
def mG (bx : Box) (i : Fin 3) (d : Fin 3) (j : ℕ) : ℤ :=
  if h : j < 3 then V3.get (V3.cross (trow bx ⟨j, h⟩) (edgeN bx.certificate i)) d else 0

/-- The weight `trow a · wcN i` (zero for `a ≥ 3`). -/
def wG (bx : Box) (i : Fin 3) (a : ℕ) : ℤ :=
  if h : a < 3 then V3.dot (trow bx ⟨a, h⟩) (wcN bx.certificate i) else 0

def mBoundG (bx : Box) (i : Fin 3) : ℕ :=
  (mG bx i 0 0).natAbs + (mG bx i 0 1).natAbs + (mG bx i 0 2).natAbs +
  (mG bx i 1 0).natAbs + (mG bx i 1 1).natAbs + (mG bx i 1 2).natAbs +
  (mG bx i 2 0).natAbs + (mG bx i 2 1).natAbs + (mG bx i 2 2).natAbs

def wBoundG (bx : Box) (i : Fin 3) : ℕ :=
  (wG bx i 0).natAbs + (wG bx i 1).natAbs + (wG bx i 2).natAbs

/-- Slot `24 a + 8 b + k`: `w_a s_{b,k} + w_b s_{a,k}`. -/
def controlPack (bx : Box) (i : Fin 3) : ℕ × ℕ :=
  let s := bx.certificate.index i
  let S := pairAdd (pairMul (pmPack (KW * 8) 3 (mG bx i 0)) (deltaT s 0))
    (pairAdd (pairMul (pmPack (KW * 8) 3 (mG bx i 1)) (deltaT s 1))
      (pairMul (pmPack (KW * 8) 3 (mG bx i 2)) (deltaT s 2)))
  let W8 := pmPack (KW * 8) 3 (wG bx i)
  let W24 := pmPack (KW * 24) 3 (wG bx i)
  let P1 := pairMul W24 S
  let P2 := pairAdd (pairMul (pmPack (KW * 24) 3 (mG bx i 0)) (pairMul W8 (deltaT s 0)))
    (pairAdd (pairMul (pmPack (KW * 24) 3 (mG bx i 1)) (pairMul W8 (deltaT s 1)))
      (pairMul (pmPack (KW * 24) 3 (mG bx i 2)) (pairMul W8 (deltaT s 2))))
  pairAdd P1 P2

/-- Closed table of the defect masks: every slot except `k = idx`. -/
def defectMaskTab : List ℕ :=
  List.ofFn fun idx : VertexIndex => maskK (fun t => t % 8 != idx.val) 72

theorem defectMaskTabL_eq : defectMaskTabL = defectMaskTab := by decide +kernel

def defectMaskT (idx : VertexIndex) : ℕ := defectMaskTabL.getD idx.val 0

/-! ### The checker -/

/-- The packed Bernstein vector of `2σ ·` the control quadratic `(i, j)`, with
its slot bound (`viewControlQuadratic` is symmetric, so `i ≤ j` suffices). -/
def ctlPair (bx : Box) (i j : Fin 3) : (ℕ × ℕ) × ℕ :=
  let B := fun i c => bvec bx (cqG bx i c)
  let MB := fun i c => bbound bx (cqG bx i c)
  let Bc := bvec bx cayI
  let Mc := bbound bx cayI
  let t := trow bx
  if i = j then
    (pairSmul 2 (viewVec bx B Bc (t i) 1), 2 * viewBound bx MB Mc (t i) 1)
  else
    (pairAdd (viewVec bx B Bc (V3.add (t i) (t j)) 4)
        (pairNeg (pairAdd (viewVec bx B Bc (t i) 1) (viewVec bx B Bc (t j) 1))),
      viewBound bx MB Mc (V3.add (t i) (t j)) 4 +
        (viewBound bx MB Mc (t i) 1 + viewBound bx MB Mc (t j) 1))

/-- Admissibility and the hinted weighted-defect checks of one global box. -/
def globalCore (bx : Box) (hints : List ℤ) : Bool :=
  let sh := shell bx
  let L : ℤ := triL sh
  let K : ℕ := 2 ^ (KW - 1)
  let t := trow bx
  decide (0 < L) && decide (0 < boxE sh) && decide (0 ≤ bx.ballMultiplier.num) &&
    (List.finRange 3).all (fun i =>
      (List.finRange 3).all (fun c => decide (0 ≤ (rootSign bx.root c).num * T sh i c)) &&
      decide ((rootSign bx.root 0).num * T sh i 0 + (rootSign bx.root 1).num * T sh i 1 +
        (rootSign bx.root 2).num * T sh i 2 = L)) &&
    -- weights: all nonnegative, some contact strictly positive
    (List.finRange 3).all (fun i => (List.finRange 3).all fun a =>
      decide (0 ≤ V3.dot (t a) (wcN bx.certificate i))) &&
    (List.finRange 3).any (fun i => (List.finRange 3).all fun a =>
      decide (0 < V3.dot (t a) (wcN bx.certificate i))) &&
    -- direction witnesses
    (List.finRange 3).all (fun i =>
      let w := bx.certificate.nonzeroWitness i
      !decide (bx.localShell.exactSupportTie 0 i w) &&
      (List.finRange 3).all fun a =>
        decide (V3.dot (V3.sub (LocalKernel.vtx w) (LocalKernel.vtx (bx.certificate.index i)))
          (V3.cross (t a) (edgeN bx.certificate i)) < 0)) &&
    -- weighted support defects
    (List.finRange 3).all (fun i =>
      let h := hints.getD i.val 0
      let M := 1920 * wBoundG bx i * mBoundG bx i
      decide (0 ≤ h) && decide (4 * (M + h.natAbs) < K) &&
        testGeM (pairNeg (controlPack bx i)) 72 (defectMaskT (bx.certificate.index i)) (-h))

/-- The packed lower-bound test of one control vector. -/
def ctlOk (U : ℕ × ℕ) (M : ℕ) (th : ℤ) : Bool :=
  decide (4 * (M + th.natAbs) < 2 ^ (KW - 1)) && testGeM U 27 (maskAll 27) th

/-- The six control index pairs `i ≤ j`. -/
def ctlIndices : List (Fin 3 × Fin 3) := [(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2)]

def validGlobalK (bx : Box) (hints : List ℤ) : Bool :=
  let sh := shell bx
  let μ := bx.ballMultiplier
  let H : ℤ := hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0)
  let th := ceilDiv (4 * μ.den * dBoundNum sh * H * 10 ^ 10 +
    2400 * μ.den * σ0 bx * dBoundNum sh) (10 ^ 10)
  globalCore bx hints &&
    ctlIndices.all fun p => ctlOk (ctlPair bx p.1 p.2).1 (ctlPair bx p.1 p.2).2 th

/-! ### Hint generation (native) -/

/-- The exact maxima of the symmetric controls, clamped at `0`. -/
def globalHints (bx : Box) : List ℤ :=
  (List.finRange 3).map fun i =>
    let s := bx.certificate.index i
    let w := fun a : Fin 3 => V3.dot (trow bx a) (wcN bx.certificate i)
    let sup := fun (a : Fin 3) (k : VertexIndex) =>
      V3.dot (V3.sub (LocalKernel.vtx k) (LocalKernel.vtx s))
        (V3.cross (trow bx a) (edgeN bx.certificate i))
    (List.finRange 8).foldl (fun m k => if k = s then m else
      (List.finRange 3).foldl (fun m a => (List.finRange 3).foldl (fun m b =>
        max m (w a * sup b k + w b * sup a k)) m) m) 0

end Noperts.Stellated.ChartKernelG
