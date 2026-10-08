module

public import Noperts.Stellated.AtlasProjectiveEdgeCertificate
public import Noperts.Stellated.PackedSlots
public import Noperts.Stellated.ChartKernelLits

@[expose] public section

/-!
# An integer checker for projective edge-cycle certificates

`validEdgeN box` decides, in integer arithmetic, a sufficient condition for
`box.Valid` (`AtlasProjectiveEdgeCertificate`): vertices are scaled by `40`,
the view triangle by the common denominator `L` of its entries, and the
Cayley box by the common denominator `E` of its `x, y, z` endpoints.  The
displacement test uses only the Bernstein lower bound (the specification takes
the maximum of it and an interval bound), compared after clearing all
denominators.
-/

namespace Noperts.Stellated.ChartKernel

open AtlasProjectiveEdgeCertificate AtlasProjectiveView

/-- An integer quadratic in `x, y, z` (fields as in `RatQuadratic3`). -/
structure IQ where
  c0 : ℤ
  cx : ℤ
  cy : ℤ
  cz : ℤ
  cxx : ℤ
  cxy : ℤ
  cxz : ℤ
  cyy : ℤ
  cyz : ℤ
  czz : ℤ

namespace IQ

def zero : IQ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def add (a b : IQ) : IQ :=
  ⟨a.c0 + b.c0, a.cx + b.cx, a.cy + b.cy, a.cz + b.cz, a.cxx + b.cxx, a.cxy + b.cxy,
    a.cxz + b.cxz, a.cyy + b.cyy, a.cyz + b.cyz, a.czz + b.czz⟩

def smul (k : ℤ) (a : IQ) : IQ :=
  ⟨k * a.c0, k * a.cx, k * a.cy, k * a.cz, k * a.cxx, k * a.cxy, k * a.cxz, k * a.cyy,
    k * a.cyz, k * a.czz⟩

def sub (a b : IQ) : IQ := add a (smul (-1) b)

end IQ

/-- Vertices scaled by `40`. -/
def vI : VertexIndex → Fin 3 → ℤ := ![
  ![20, 20, 20], ![20, -20, -20], ![-20, 20, -20], ![-20, -20, 20],
  ![-11, -11, -11], ![-11, 11, 11], ![11, -11, 11], ![11, 11, -11]]

def denomI : IQ := ⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩

/-- `CayleyEdgeCertificate.numeratorQuadratic` with integer coefficients. -/
def numI : Fin 3 → Fin 3 → IQ := ![
  ![⟨1, 0, 0, 0, 1, 0, 0, -1, 0, -1⟩, ⟨0, 0, 0, -2, 0, 2, 0, 0, 0, 0⟩,
    ⟨0, 0, 2, 0, 0, 0, 2, 0, 0, 0⟩],
  ![⟨0, 0, 0, 2, 0, 2, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, -1, 0, 0, 1, 0, -1⟩,
    ⟨0, -2, 0, 0, 0, 0, 0, 0, 2, 0⟩],
  ![⟨0, 0, -2, 0, 0, 0, 2, 0, 0, 0⟩, ⟨0, 2, 0, 0, 0, 0, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, -1, 0, 0, -1, 0, 1⟩]]

def chartSignI (chart : CayleyAtlas.ChartIndex) (c : Fin 3) : ℤ :=
  if chart.val = 0 ∨ chart.val = c.val + 1 then 1 else -1

/-- `40 ·` the denominator-cleared displacement quadratic. -/
def dispI (chart : CayleyAtlas.ChartIndex) (inner outer : VertexIndex) (c : Fin 3) : IQ :=
  IQ.sub (IQ.add (IQ.add (IQ.smul (vI inner 0 * chartSignI chart c) (numI c 0))
    (IQ.smul (vI inner 1 * chartSignI chart c) (numI c 1)))
    (IQ.smul (vI inner 2 * chartSignI chart c) (numI c 2)))
    (IQ.smul (vI outer c) denomI)

/-- `1600 ·` the contact quadratic of an edge. -/
def contactI (chart : CayleyAtlas.ChartIndex) (start finish inner : VertexIndex) (c : Fin 3) :
    IQ :=
  let e := fun d => vI start d - vI finish d
  let d := dispI chart inner start
  match c with
  | 0 => IQ.sub (IQ.smul (e 1) (d 2)) (IQ.smul (e 2) (d 1))
  | 1 => IQ.sub (IQ.smul (e 2) (d 0)) (IQ.smul (e 0) (d 2))
  | 2 => IQ.sub (IQ.smul (e 0) (d 1)) (IQ.smul (e 1) (d 0))

/-- `1600 ·` the contact quadratic, in closed form. -/
def contactFast (chart : CayleyAtlas.ChartIndex) (start finish inner : VertexIndex) : Fin 3 → IQ :=
  let s0 := vI start 0; let s1 := vI start 1; let s2 := vI start 2
  let u0 := vI inner 0; let u1 := vI inner 1; let u2 := vI inner 2
  let e0 := s0 - vI finish 0; let e1 := s1 - vI finish 1; let e2 := s2 - vI finish 2
  let g0 := chartSignI chart 0; let g1 := chartSignI chart 1; let g2 := chartSignI chart 2
  let d0c0 : ℤ := g0 * (u0) + -s0
  let d0cx : ℤ := 0
  let d0cy : ℤ := g0 * (2 * u2)
  let d0cz : ℤ := g0 * (-2 * u1)
  let d0cxx : ℤ := g0 * (u0) + -s0
  let d0cxy : ℤ := g0 * (2 * u1)
  let d0cxz : ℤ := g0 * (2 * u2)
  let d0cyy : ℤ := g0 * (-u0) + -s0
  let d0cyz : ℤ := 0
  let d0czz : ℤ := g0 * (-u0) + -s0
  let d1c0 : ℤ := g1 * (u1) + -s1
  let d1cx : ℤ := g1 * (-2 * u2)
  let d1cy : ℤ := 0
  let d1cz : ℤ := g1 * (2 * u0)
  let d1cxx : ℤ := g1 * (-u1) + -s1
  let d1cxy : ℤ := g1 * (2 * u0)
  let d1cxz : ℤ := 0
  let d1cyy : ℤ := g1 * (u1) + -s1
  let d1cyz : ℤ := g1 * (2 * u2)
  let d1czz : ℤ := g1 * (-u1) + -s1
  let d2c0 : ℤ := g2 * (u2) + -s2
  let d2cx : ℤ := g2 * (2 * u1)
  let d2cy : ℤ := g2 * (-2 * u0)
  let d2cz : ℤ := 0
  let d2cxx : ℤ := g2 * (-u2) + -s2
  let d2cxy : ℤ := 0
  let d2cxz : ℤ := g2 * (2 * u0)
  let d2cyy : ℤ := g2 * (-u2) + -s2
  let d2cyz : ℤ := g2 * (2 * u1)
  let d2czz : ℤ := g2 * (u2) + -s2
  fun c => match c with
    | 0 => ⟨e1 * d2c0 - e2 * d1c0, e1 * d2cx - e2 * d1cx, e1 * d2cy - e2 * d1cy, e1 * d2cz - e2 * d1cz, e1 * d2cxx - e2 * d1cxx, e1 * d2cxy - e2 * d1cxy, e1 * d2cxz - e2 * d1cxz, e1 * d2cyy - e2 * d1cyy, e1 * d2cyz - e2 * d1cyz, e1 * d2czz - e2 * d1czz⟩
    | 1 => ⟨e2 * d0c0 - e0 * d2c0, e2 * d0cx - e0 * d2cx, e2 * d0cy - e0 * d2cy, e2 * d0cz - e0 * d2cz, e2 * d0cxx - e0 * d2cxx, e2 * d0cxy - e0 * d2cxy, e2 * d0cxz - e0 * d2cxz, e2 * d0cyy - e0 * d2cyy, e2 * d0cyz - e0 * d2cyz, e2 * d0czz - e0 * d2czz⟩
    | 2 => ⟨e0 * d1c0 - e1 * d0c0, e0 * d1cx - e1 * d0cx, e0 * d1cy - e1 * d0cy, e0 * d1cz - e1 * d0cz, e0 * d1cxx - e1 * d0cxx, e0 * d1cxy - e1 * d0cxy, e0 * d1cxz - e1 * d0cxz, e0 * d1cyy - e1 * d0cyy, e0 * d1cyz - e1 * d0cyz, e0 * d1czz - e1 * d0czz⟩

/-- `L · q` as an integer, for `q.den ∣ L`. -/
def qScale (L : ℕ) (q : ℚ) : ℤ := q.num * ((L / q.den : ℕ) : ℤ)

def lcmList (qs : List ℚ) : ℕ := qs.foldr (fun q a => Nat.lcm q.den a) 1

section
variable (box : Box)

def triL : ℕ := lcmList ((List.finRange 3).flatMap fun j => (List.finRange 3).map (box.triangle j))

def T (j c : Fin 3) : ℤ := qScale (triL box) (box.triangle j c)

def boxE : ℕ :=
  lcmList ((List.finRange 3).flatMap fun c =>
    [box.interval.min.get ⟨c.val + 2, by omega⟩, box.interval.max.get ⟨c.val + 2, by omega⟩])

def lo (c : Fin 3) : ℤ := qScale (boxE box) (box.interval.min.get ⟨c.val + 2, by omega⟩)

def hi (c : Fin 3) : ℤ := qScale (boxE box) (box.interval.max.get ⟨c.val + 2, by omega⟩)

def totalI (c : Fin 3) : IQ :=
  (List.finRange (box.edgePred + 1)).foldr (fun i acc =>
    IQ.add (contactFast box.chart (box.outerIndex i) (box.outerIndex (box.edgeShell.next i))
      (box.innerIndex i) c) acc) IQ.zero

/-- `T_j × e_i`, shared by the supports of all vertices. -/
def mI (i : Fin (box.edgePred + 1)) (j : Fin 3) : ℤ × ℤ × ℤ :=
  let s := box.outerIndex i
  let f := box.outerIndex (box.edgeShell.next i)
  let e0 := vI s 0 - vI f 0
  let e1 := vI s 1 - vI f 1
  let e2 := vI s 2 - vI f 2
  let t0 := T box j 0
  let t1 := T box j 1
  let t2 := T box j 2
  (t1 * e2 - t2 * e1, t2 * e0 - t0 * e2, t0 * e1 - t1 * e0)

/-- `1600 L ·` the support of vertex `k` against edge `i` at triangle corner `j`:
`T_j · (e_i × (v_k - v_s)) = (v_k - v_s) · (T_j × e_i)`. -/
def supportI (i : Fin (box.edgePred + 1)) (j : Fin 3) (k : VertexIndex) : ℤ :=
  let s := box.outerIndex i
  let m := mI box i j
  (vI k 0 - vI s 0) * m.1 + (vI k 1 - vI s 1) * m.2.1 + (vI k 2 - vI s 2) * m.2.2

def max3I (f : Fin 3 → ℤ) : ℤ := max (f 0) (max (f 1) (f 2))

def supportMaxI (i : Fin (box.edgePred + 1)) (k : VertexIndex) : ℤ :=
  max3I fun j => supportI box i j k

def defectI (i : Fin (box.edgePred + 1)) : ℤ :=
  (List.finRange 8).foldr (fun k acc => max (supportMaxI box i k) acc) (supportMaxI box i 0)

def totalDefectI : ℤ := (List.finRange (box.edgePred + 1)).foldr (fun i acc => defectI box i + acc) 0

/-- `1600 L μden ·` the adjusted quadratic at corner `j`. -/
def adjI (j : Fin 3) : IQ :=
  let μ := box.ballMultiplier j
  IQ.add (IQ.smul (μ.den : ℤ) (IQ.add (IQ.add (IQ.smul (T box j 0) (totalI box 0))
    (IQ.smul (T box j 1) (totalI box 1))) (IQ.smul (T box j 2) (totalI box 2))))
    (IQ.smul (μ.num * 1600 * (triL box : ℤ)) ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩)

/-- `4 E² ·` the Bernstein control coefficient `(i, j, k)` of `q` on the box. -/
def bernI (q : IQ) (i j k : ℕ) : ℤ :=
  let E : ℤ := boxE box
  let lx := lo box 0
  let ly := lo box 1
  let lz := lo box 2
  let wx := hi box 0 - lx
  let wy := hi box 1 - ly
  let wz := hi box 2 - lz
  let A0 := q.c0 * E * E + E * (q.cx * lx + q.cy * ly + q.cz * lz) + q.cxx * lx * lx +
    q.cxy * lx * ly + q.cxz * lx * lz + q.cyy * ly * ly + q.cyz * ly * lz + q.czz * lz * lz
  let AX := wx * (q.cx * E + 2 * q.cxx * lx + q.cxy * ly + q.cxz * lz)
  let AY := wy * (q.cy * E + q.cxy * lx + 2 * q.cyy * ly + q.cyz * lz)
  let AZ := wz * (q.cz * E + q.cxz * lx + q.cyz * ly + 2 * q.czz * lz)
  4 * A0 + 2 * (i : ℤ) * AX + 2 * (j : ℤ) * AY + 2 * (k : ℤ) * AZ +
    (if i = 2 then 4 * q.cxx * wx * wx else 0) +
    (if j = 2 then 4 * q.cyy * wy * wy else 0) +
    (if k = 2 then 4 * q.czz * wz * wz else 0) +
    (i : ℤ) * j * q.cxy * wx * wy + (i : ℤ) * k * q.cxz * wx * wz + (j : ℤ) * k * q.cyz * wy * wz

def foldMin {α : Type} (f : α → ℤ) (init : ℤ) (l : List α) : ℤ :=
  l.foldr (fun t a => min (f t) a) init

def triples27 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 2, 0), (0, 2, 1), (0, 2, 2), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 2, 0), (1, 2, 1), (1, 2, 2), (2, 0, 0), (2, 0, 1), (2, 0, 2), (2, 1, 0), (2, 1, 1), (2, 1, 2), (2, 2, 0), (2, 2, 1), (2, 2, 2)]

def bernMinI (q : IQ) : ℤ :=
  foldMin (fun t => bernI box q t.1 t.2.1 t.2.2) (bernI box q 0 0 0) triples27

def dBoundNum : ℤ :=
  (boxE box : ℤ) ^ 2 + (List.finRange 3).foldr (fun c a => max |lo box c| |hi box c| ^ 2 + a) 0

def validEdgeN : Bool :=
  let L : ℤ := triL box
  let n : ℤ := box.edgePred + 1
  let P : ℤ := 10 ^ 10
  decide (0 < L) && decide (0 < boxE box) &&
    -- the triangle lies on its signed face
    (List.finRange 3).all (fun i =>
      (List.finRange 3).all (fun c => decide (0 ≤ (rootSign box.root c).num * T box i c)) &&
      decide ((rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = L)) &&
    (List.finRange 3).all (fun j => decide (0 ≤ (box.ballMultiplier j).num)) &&
    (List.finRange (box.edgePred + 1)).all (fun i =>
      decide (supportMaxI box i (box.nonzeroWitness i) * P + 16000 * L < 0)) &&
    (List.finRange 3).all (fun j =>
      decide (dBoundNum box * (totalDefectI box * P + 32000 * n * L) * 4 *
        (box.ballMultiplier j).den ≤ bernMinI box (adjI box j) * P))

end

end Noperts.Stellated.ChartKernel

namespace Noperts.Stellated.ChartKernel
open AtlasProjectiveEdgeCertificate

/-- Profiling helpers. -/
def probeTotals (box : Box) : ℤ :=
  (totalI box 0).c0 + (totalI box 1).cxy + (totalI box 2).czz + (totalI box 0).cxx

def probeAdj (box : Box) : ℤ := (adjI box 0).c0 + (adjI box 1).cx + (adjI box 2).czz

def probeSupports (box : Box) : ℤ := totalDefectI box

def probeBern (box : Box) : ℤ := bernMinI box (adjI box 0) + bernMinI box (adjI box 1) +
  bernMinI box (adjI box 2)

end Noperts.Stellated.ChartKernel

/-! ## Packed Bernstein test -/

namespace Noperts.Stellated.ChartKernel
open AtlasProjectiveEdgeCertificate AtlasProjectiveView

/-- `a₀ + a₁ y + a₂ y²` for `y = x ^ e`. -/
def tri3 (x e a0 a1 a2 : ℕ) : ℕ := a0 + a1 * x ^ e + a2 * x ^ (2 * e)

/-- The 27-slot vector `Σ f(i) g(j) h(k) x^(9i+3j+k)`. -/
def vec27 (x : ℕ) (f g h : ℕ × ℕ × ℕ) : ℕ :=
  tri3 x 9 f.1 f.2.1 f.2.2 * tri3 x 3 g.1 g.2.1 g.2.2 * tri3 x 1 h.1 h.2.1 h.2.2

/-- The ten Bernstein basis patterns, as separable `(f, g, h)`:
`1, i, j, k, [i=2], [j=2], [k=2], ij, ik, jk`. -/
def basis27 (x : ℕ) : List ℕ :=
  let one := (1, 1, 1)
  let idx := (0, 1, 2)
  let top := (0, 0, 1)
  [vec27 x one one one, vec27 x idx one one, vec27 x one idx one, vec27 x one one idx,
   vec27 x top one one, vec27 x one top one, vec27 x one one top,
   vec27 x idx idx one, vec27 x idx one idx, vec27 x one idx idx]

/-- The ten integer weights of the patterns for quadratic `q` (so that the
Bernstein coefficient `(i,j,k)` is `Σ c_m β_m(i,j,k)`). -/
def bernWeights (box : Box) (q : IQ) : List ℤ :=
  let E : ℤ := boxE box
  let lx := lo box 0
  let ly := lo box 1
  let lz := lo box 2
  let wx := hi box 0 - lx
  let wy := hi box 1 - ly
  let wz := hi box 2 - lz
  let A0 := q.c0 * E * E + E * (q.cx * lx + q.cy * ly + q.cz * lz) + q.cxx * lx * lx +
    q.cxy * lx * ly + q.cxz * lx * lz + q.cyy * ly * ly + q.cyz * ly * lz + q.czz * lz * lz
  let AX := wx * (q.cx * E + 2 * q.cxx * lx + q.cxy * ly + q.cxz * lz)
  let AY := wy * (q.cy * E + q.cxy * lx + 2 * q.cyy * ly + q.cyz * lz)
  let AZ := wz * (q.cz * E + q.cxz * lx + q.cyz * ly + 2 * q.czz * lz)
  [4 * A0, 2 * AX, 2 * AY, 2 * AZ, 4 * q.cxx * wx * wx, 4 * q.cyy * wy * wy, 4 * q.czz * wz * wz,
   q.cxy * wx * wy, q.cxz * wx * wz, q.cyz * wy * wz]

def dotPos (cs : List ℤ) (vs : List ℕ) : ℕ :=
  (List.zip cs vs).foldr (fun p a => (if 0 ≤ p.1 then p.1.toNat * p.2 else 0) + a) 0

def dotNeg (cs : List ℤ) (vs : List ℕ) : ℕ :=
  (List.zip cs vs).foldr (fun p a => (if p.1 < 0 then (-p.1).toNat * p.2 else 0) + a) 0

/-- Every Bernstein coefficient of `q` is at least `th`: a packed test on
`w`-bit slots (`x = 2^w`). -/
def bernAllGe (box : Box) (q : IQ) (th : ℤ) (w : ℕ) : Bool :=
  let cs := bernWeights box q
  let M : ℕ := 4 * (cs.foldr (fun c a => c.natAbs + a) 0) + th.natAbs
  let x : ℕ := 2 ^ w
  let K : ℕ := 2 ^ (w - 1)
  let vs := basis27 x
  let ones := vec27 x (1, 1, 1) (1, 1, 1) (1, 1, 1)
  let A := dotPos cs vs + K * ones + (if th < 0 then th.natAbs * ones else 0)
  let B := dotNeg cs vs + (if 0 ≤ th then th.natAbs * ones else 0)
  Nat.blt 1 w && Nat.blt (4 * M) K && Nat.land (A - B) (K * ones) == K * ones

/-- A slot width for the packed test. -/
def bernWidth (box : Box) (q : IQ) (th : ℤ) : ℕ :=
  Nat.log2 (4 * (4 * ((bernWeights box q).foldr (fun c a => c.natAbs + a) 0) + th.natAbs)) + 3

def ceilDiv (a : ℤ) (b : ℕ) : ℤ := -((-a) / (b : ℤ))

/-- `validEdgeN` with the packed Bernstein test. -/
def validEdgeP (box : Box) : Bool :=
  let L : ℤ := triL box
  let n : ℤ := box.edgePred + 1
  let P : ℤ := 10 ^ 10
  decide (0 < L) && decide (0 < boxE box) &&
    (List.finRange 3).all (fun i =>
      (List.finRange 3).all (fun c => decide (0 ≤ (rootSign box.root c).num * T box i c)) &&
      decide ((rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = L)) &&
    (List.finRange 3).all (fun j => decide (0 ≤ (box.ballMultiplier j).num)) &&
    (List.finRange (box.edgePred + 1)).all (fun i =>
      decide (supportMaxI box i (box.nonzeroWitness i) * P + 16000 * L < 0)) &&
    (List.finRange 3).all (fun j =>
      let th := ceilDiv (dBoundNum box * (totalDefectI box * P + 32000 * n * L) * 4 *
        (box.ballMultiplier j).den) (10 ^ 10)
      let q := adjI box j
      bernAllGe box q th (bernWidth box q th))

end Noperts.Stellated.ChartKernel

/-! ## Packed sign-split quadratics

A quadratic's ten integer fields are packed into two Nats (positive and
negative parts), field `f` in bits `[W f, W f + W)`, `W = 256`.  Additions and
nonnegative scalings act on all fields at once; the sign of a scalar is
decided once, outside the packed arithmetic. -/

namespace Noperts.Stellated.ChartKernel

def PW : ℕ := 256

/-- A packed sign-split quadratic: value of field `f` = slot `f` of `p` minus slot `f` of `n`. -/
structure PQ where
  p : ℕ
  n : ℕ

def PQ.add (a b : PQ) : PQ := ⟨a.p + b.p, a.n + b.n⟩

def PQ.neg (a : PQ) : PQ := ⟨a.n, a.p⟩

/-- Multiply by a signed integer: the sign is handled once. -/
def PQ.smul (k : ℤ) (a : PQ) : PQ :=
  if 0 ≤ k then ⟨k.toNat * a.p, k.toNat * a.n⟩ else ⟨k.natAbs * a.n, k.natAbs * a.p⟩

def packField (f : ℕ) (v : ℤ) : PQ :=
  if 0 ≤ v then ⟨v.toNat <<< (PW * f), 0⟩ else ⟨0, v.natAbs <<< (PW * f)⟩

def IQ.pack (q : IQ) : PQ :=
  [q.c0, q.cx, q.cy, q.cz, q.cxx, q.cxy, q.cxz, q.cyy, q.cyz, q.czz].zipIdx.foldr
    (fun (v, f) acc => PQ.add (packField f v) acc) ⟨0, 0⟩

def slotOf (x f : ℕ) : ℕ := (x >>> (PW * f)) % 2 ^ PW

def PQ.field (a : PQ) (f : ℕ) : ℤ := (slotOf a.p f : ℤ) - slotOf a.n f

def PQ.unpack (a : PQ) : IQ :=
  ⟨a.field 0, a.field 1, a.field 2, a.field 3, a.field 4, a.field 5, a.field 6, a.field 7,
    a.field 8, a.field 9⟩

/-- Packed Cayley numerator and denominator quadratics. -/
def numP (c j : Fin 3) : PQ := (numI c j).pack
def denomP : PQ := denomI.pack

/-- `contactFast`, packed. -/
def contactP (chart : CayleyAtlas.ChartIndex) (start finish inner : VertexIndex) : Fin 3 → PQ :=
  let e := fun d => vI start d - vI finish d
  let d := fun (b : Fin 3) =>
    PQ.add (PQ.smul (chartSignI chart b) (PQ.add (PQ.add (PQ.smul (vI inner 0) (numP b 0))
      (PQ.smul (vI inner 1) (numP b 1))) (PQ.smul (vI inner 2) (numP b 2))))
      (PQ.smul (-vI start b) denomP)
  fun c => match c with
    | 0 => PQ.add (PQ.smul (e 1) (d 2)) (PQ.smul (-e 2) (d 1))
    | 1 => PQ.add (PQ.smul (e 2) (d 0)) (PQ.smul (-e 0) (d 2))
    | 2 => PQ.add (PQ.smul (e 0) (d 1)) (PQ.smul (-e 1) (d 0))

def totalP (box : AtlasProjectiveEdgeCertificate.Box) (c : Fin 3) : PQ :=
  (List.finRange (box.edgePred + 1)).foldr (fun i acc =>
    PQ.add (contactP box.chart (box.outerIndex i) (box.outerIndex (box.edgeShell.next i))
      (box.innerIndex i) c) acc) ⟨0, 0⟩

def probeTotalsP (box : AtlasProjectiveEdgeCertificate.Box) : ℤ :=
  (totalP box 0).unpack.c0 + (totalP box 1).unpack.cxy + (totalP box 2).unpack.czz +
    (totalP box 0).unpack.cxx

end Noperts.Stellated.ChartKernel

namespace Noperts.Stellated.ChartKernel
open AtlasProjectiveEdgeCertificate

def probeWeights (box : Box) : ℤ :=
  ((bernWeights box (adjI box 0)).foldr (· + ·) 0) + ((bernWeights box (adjI box 1)).foldr (· + ·) 0)
    + ((bernWeights box (adjI box 2)).foldr (· + ·) 0)

def probeBernP (box : Box) : Bool :=
  bernAllGe box (adjI box 0) 0 (bernWidth box (adjI box 0) 0) ||
  bernAllGe box (adjI box 1) 0 (bernWidth box (adjI box 1) 0) ||
  bernAllGe box (adjI box 2) 0 (bernWidth box (adjI box 2) 0) || true

def probeDBound (box : Box) : ℤ := dBoundNum box + triL box

end Noperts.Stellated.ChartKernel

namespace Noperts.Stellated.ChartKernel
open AtlasProjectiveEdgeCertificate AtlasProjectiveView

/-- Packed Bernstein coefficient vector `(Σ⁺ c_m V_m, Σ⁻ |c_m| V_m)` of quadratic `q`. -/
def bernVec (box : Box) (vs : List ℕ) (q : IQ) : ℕ × ℕ :=
  let cs := bernWeights box q
  (dotPos cs vs, dotNeg cs vs)

def pairSmul (k : ℤ) (a : ℕ × ℕ) : ℕ × ℕ :=
  if 0 ≤ k then (k.toNat * a.1, k.toNat * a.2) else (k.natAbs * a.2, k.natAbs * a.1)

def pairAdd (a b : ℕ × ℕ) : ℕ × ℕ := (a.1 + b.1, a.2 + b.2)

/-- The packed test with a precomputed coefficient vector. -/
def packedAllGe (U : ℕ × ℕ) (ones : ℕ) (th : ℤ) (w : ℕ) : Bool :=
  let K : ℕ := 2 ^ (w - 1)
  let A := U.1 + K * ones + (if th < 0 then th.natAbs * ones else 0)
  let B := U.2 + (if 0 ≤ th then th.natAbs * ones else 0)
  Nat.land (A - B) (K * ones) == K * ones

def validEdgeQ (box : Box) : Bool :=
  let L : ℤ := triL box
  let n : ℤ := box.edgePred + 1
  let P : ℤ := 10 ^ 10
  let w : ℕ := 600
  let x : ℕ := 2 ^ w
  let vs := basis27 x
  let ones := vec27 x (1, 1, 1) (1, 1, 1) (1, 1, 1)
  let U0 := bernVec box vs (totalI box 0)
  let U1 := bernVec box vs (totalI box 1)
  let U2 := bernVec box vs (totalI box 2)
  let Uc := bernVec box vs ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩
  decide (0 < L) && decide (0 < boxE box) &&
    (List.finRange 3).all (fun i =>
      (List.finRange 3).all (fun c => decide (0 ≤ (rootSign box.root c).num * T box i c)) &&
      decide ((rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = L)) &&
    (List.finRange 3).all (fun j => decide (0 ≤ (box.ballMultiplier j).num)) &&
    (List.finRange (box.edgePred + 1)).all (fun i =>
      decide (supportMaxI box i (box.nonzeroWitness i) * P + 16000 * L < 0)) &&
    (List.finRange 3).all (fun j =>
      let μ := box.ballMultiplier j
      let th := ceilDiv (dBoundNum box * (totalDefectI box * P + 32000 * n * L) * 4 * μ.den) (10 ^ 10)
      let U := pairAdd (pairSmul (μ.den : ℤ) (pairAdd (pairAdd (pairSmul (T box j 0) U0)
        (pairSmul (T box j 1) U1)) (pairSmul (T box j 2) U2))) (pairSmul (μ.num * 1600 * L) Uc)
      packedAllGe U ones th w)

end Noperts.Stellated.ChartKernel

namespace Noperts.Stellated.ChartKernel
open AtlasProjectiveEdgeCertificate AtlasProjectiveView

def pairSub (a b : ℕ × ℕ) : ℕ × ℕ := (a.1 + b.2, a.2 + b.1)

def pairMul (a b : ℕ × ℕ) : ℕ × ℕ := (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- `Σ_k v_k[d] x^k` as a pair (vertex coordinates are ±20, ±11). -/
def vertPack (x : ℕ) (d : Fin 3) : ℕ × ℕ :=
  (List.finRange 8).foldr (fun k acc => pairAdd (pairSmul (vI k d) (x ^ k.val, 0)) acc) (0, 0)

def ones8 (x : ℕ) : ℕ := (List.range 8).foldr (fun k a => x ^ k + a) 0

/-- Packed supports of edge `i`: slot `8 j + k` holds `supportI box i j k`. -/
def supportPack (x : ℕ) (VP : Fin 3 → ℕ × ℕ) (box : Box) (i : Fin (box.edgePred + 1)) : ℕ × ℕ :=
  let s := box.outerIndex i
  let o8 := ones8 x
  let M := fun d : Fin 3 =>
    pairAdd (pairAdd (pairSmul (mI box i 0 |> fun m => [m.1, m.2.1, m.2.2].getD d 0) (1, 0))
      (pairSmul (mI box i 1 |> fun m => [m.1, m.2.1, m.2.2].getD d 0) (x ^ 8, 0)))
      (pairSmul (mI box i 2 |> fun m => [m.1, m.2.1, m.2.2].getD d 0) (x ^ 16, 0))
  let Δ := fun d : Fin 3 => pairSub (VP d) (pairSmul (vI s d) (o8, 0))
  pairAdd (pairAdd (pairMul (M 0) (Δ 0)) (pairMul (M 1) (Δ 1))) (pairMul (M 2) (Δ 2))

/-- All slots of `S` (where `mask` is set) are at most `th`. -/
def packedAllLe (S : ℕ × ℕ) (ones mask : ℕ) (th : ℤ) (w : ℕ) : Bool :=
  let K : ℕ := 2 ^ (w - 1)
  -- slot value  th - S + K  must be ≥ K
  let A := S.2 + K * ones + (if 0 ≤ th then th.natAbs * ones else 0)
  let B := S.1 + (if th < 0 then th.natAbs * ones else 0)
  Nat.land (A - B) mask == mask

def validEdgeH (box : Box) (hints : List ℤ) : Bool :=
  let L : ℤ := triL box
  let n : ℤ := box.edgePred + 1
  let P : ℤ := 10 ^ 10
  let w : ℕ := 600
  let x : ℕ := 2 ^ w
  let K : ℕ := 2 ^ (w - 1)
  let vs := basis27 x
  let ones := vec27 x (1, 1, 1) (1, 1, 1) (1, 1, 1)
  let ones24 := (List.range 24).foldr (fun t a => x ^ t + a) 0
  let VP := fun d => vertPack x d
  let U0 := bernVec box vs (totalI box 0)
  let U1 := bernVec box vs (totalI box 1)
  let U2 := bernVec box vs (totalI box 2)
  let Uc := bernVec box vs ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩
  let thw : ℤ := (-16000 * L - 1) / P
  let TD : ℤ := hints.foldr (· + ·) 0
  decide (0 < L) && decide (0 < boxE box) && decide (hints.length = box.edgePred + 1) &&
    (List.finRange 3).all (fun i =>
      (List.finRange 3).all (fun c => decide (0 ≤ (rootSign box.root c).num * T box i c)) &&
      decide ((rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = L)) &&
    (List.finRange 3).all (fun j => decide (0 ≤ (box.ballMultiplier j).num)) &&
    (List.finRange (box.edgePred + 1)).all (fun i =>
      let S := supportPack x VP box i
      let wv := (box.nonzeroWitness i).val
      let maskW := K * (x ^ wv + x ^ (8 + wv) + x ^ (16 + wv))
      packedAllLe S ones24 (K * ones24) (hints.getD i.val 0) w &&
        packedAllLe S ones24 maskW thw w) &&
    (List.finRange 3).all (fun j =>
      let μ := box.ballMultiplier j
      let th := ceilDiv (dBoundNum box * (TD * P + 32000 * n * L) * 4 * μ.den) (10 ^ 10)
      let U := pairAdd (pairSmul (μ.den : ℤ) (pairAdd (pairAdd (pairSmul (T box j 0) U0)
        (pairSmul (T box j 1) U1)) (pairSmul (T box j 2) U2))) (pairSmul (μ.num * 1600 * L) Uc)
      packedAllGe U ones th w)

/-- The exact per-edge defects (what a generator supplies as hints). -/
def defectHints (box : Box) : List ℤ := (List.finRange (box.edgePred + 1)).map (defectI box)

end Noperts.Stellated.ChartKernel

/-! ## The kernel edge checker (proof-friendly packed form) -/

namespace Noperts.Stellated.ChartKernel
open AtlasProjectiveEdgeCertificate AtlasProjectiveView PackedSlots

def KW : ℕ := 600

/-- The ten Bernstein basis patterns as `(f, g, h)` triples. -/
def basisTriples : List ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  let one := (1, 1, 1)
  let idx := (0, 1, 2)
  let top := (0, 0, 1)
  [(one, one, one), (idx, one, one), (one, idx, one), (one, one, idx), (top, one, one),
   (one, top, one), (one, one, top), (idx, idx, one), (idx, one, idx), (one, idx, idx)]

/-- The packed basis vectors (a closed table: the kernel evaluates it once). -/
def basisVecs : List ℕ := basisTriples.map fun p => vec27 (2 ^ KW) p.1 p.2.1 p.2.2

theorem basisVecsL_eq : basisVecsL = basisVecs := by decide +kernel

/-- `(Σ⁺ c_m V_m, Σ⁻ |c_m| V_m)` over the basis vectors. -/
def bernPairK (cs : List ℤ) : ℕ × ℕ :=
  (cs.zip basisVecsL).foldr (fun p acc => pairAdd (pairSmul p.1 (p.2, 0)) acc) (0, 0)

def boundK (cs : List ℤ) : ℕ := cs.foldr (fun c a => c.natAbs * 4 + a) 0

def pairNeg (a : ℕ × ℕ) : ℕ × ℕ := (a.2, a.1)

def onesK (n : ℕ) : ℕ := packW KW (fun _ => 1) n

def maskK (p : ℕ → Bool) (n : ℕ) : ℕ := packW KW (fun t => if p t then 2 ^ (KW - 1) else 0) n

/-- `onesK n`, read from a literal for the sizes in use. -/
def onesL (n : ℕ) : ℕ :=
  if n = 24 then ones24L else if n = 27 then ones27L else if n = 72 then ones72L else onesK n

theorem onesL_eq (n : ℕ) : onesL n = onesK n := by
  unfold onesL
  split_ifs with h1 h2 h3
  · subst h1; decide +kernel
  · subst h2; decide +kernel
  · subst h3; decide +kernel
  · rfl

/-- `maskK (fun _ => true) n`, read from a literal for the sizes in use. -/
def maskAll (n : ℕ) : ℕ :=
  if n = 24 then mask24L else if n = 27 then mask27L else if n = 72 then mask72L
  else maskK (fun _ => true) n

theorem maskAll_eq (n : ℕ) : maskAll n = maskK (fun _ => true) n := by
  unfold maskAll
  split_ifs with h1 h2 h3
  · subst h1; decide +kernel
  · subst h2; decide +kernel
  · subst h3; decide +kernel
  · rfl

/-- A packed test: every slot of `U` selected by `mask` is at least `th`. -/
def testGeM (U : ℕ × ℕ) (n : ℕ) (mask : ℕ) (th : ℤ) : Bool :=
  Nat.land (U.1 + 2 ^ (KW - 1) * onesL n + (if th < 0 then th.natAbs * onesL n else 0) -
    (U.2 + (if 0 ≤ th then th.natAbs * onesL n else 0))) mask == mask

/-- A packed test: every slot of `U` selected by `p` is at least `th`. -/
def testGe (U : ℕ × ℕ) (n : ℕ) (p : ℕ → Bool) (th : ℤ) : Bool := testGeM U n (maskK p n) th

/-- `v_k[d] - v_s[d]` (zero for `k ≥ 8`). -/
def δN (s : VertexIndex) (d : Fin 3) (k : ℕ) : ℤ :=
  if h : k < 8 then vI ⟨k, h⟩ d - vI s d else 0

def pmPack (w n : ℕ) (f : ℕ → ℤ) : ℕ × ℕ :=
  (packW w (fun t => (f t).toNat) n, packW w (fun t => (-f t).toNat) n)

/-- Closed table of `pmPack KW 8 (δN s d)`. -/
def deltaTab : List (List (ℕ × ℕ)) :=
  List.ofFn fun s : VertexIndex => List.ofFn fun d : Fin 3 => pmPack KW 8 (δN s d)

theorem deltaTabL_eq : deltaTabL = deltaTab := by decide +kernel

def deltaT (s : VertexIndex) (d : Fin 3) : ℕ × ℕ := (deltaTabL.getD s.val []).getD d.val (0, 0)

/-- Closed table of the witness masks. -/
def maskTab : List ℕ := List.ofFn fun w : VertexIndex => maskK (fun t => t % 8 == w.val) 24

theorem maskTabL_eq : maskTabL = maskTab := by decide +kernel

def maskT (w : VertexIndex) : ℕ := maskTabL.getD w.val 0

/-- Closed table of the contact quadratics. -/
def contactTab : List (List (List (List (List IQ)))) :=
  List.ofFn fun ch : CayleyAtlas.ChartIndex => List.ofFn fun s : VertexIndex =>
    List.ofFn fun f : VertexIndex => List.ofFn fun u : VertexIndex =>
      List.ofFn fun c : Fin 3 => contactFast ch s f u c

def contactT (ch : CayleyAtlas.ChartIndex) (s f u : VertexIndex) (c : Fin 3) : IQ :=
  ((((contactTab.getD ch.val []).getD s.val []).getD f.val []).getD u.val []).getD c.val IQ.zero

def totalT (box : Box) (c : Fin 3) : IQ :=
  (List.finRange (box.edgePred + 1)).foldr (fun i acc =>
    IQ.add (contactT box.chart (box.outerIndex i) (box.outerIndex (box.edgeShell.next i))
      (box.innerIndex i) c) acc) IQ.zero

/-- `T box j c` (zero for `j ≥ 3`). -/
def tN (box : Box) (c : Fin 3) (j : ℕ) : ℤ := if h : j < 3 then T box ⟨j, h⟩ c else 0

/-- Column `c` of the scaled triangle, packed at stride `8`. -/
def tPack (box : Box) (c : Fin 3) : ℕ × ℕ := pmPack (KW * 8) 3 (tN box c)

def tBound (box : Box) : ℕ :=
  (T box 0 0).natAbs + (T box 0 1).natAbs + (T box 0 2).natAbs + (T box 1 0).natAbs +
    (T box 1 1).natAbs + (T box 1 2).natAbs + (T box 2 0).natAbs + (T box 2 1).natAbs +
    (T box 2 2).natAbs

/-- Closed table of edge vectors `v_s - v_f`. -/
def edgeTab : List (List (List ℤ)) :=
  List.ofFn fun s : VertexIndex => List.ofFn fun f : VertexIndex =>
    List.ofFn fun d : Fin 3 => vI s d - vI f d

def edgeT (s f : VertexIndex) (d : Fin 3) : ℤ := ((edgeTab.getD s.val []).getD f.val []).getD d.val 0

/-- Coordinate `d` of the normals `m_j = T_j × e` of edge `i`, packed over `j`. -/
def mPackT (box : Box) (i : Fin (box.edgePred + 1)) (d : Fin 3) : ℕ × ℕ :=
  let s := box.outerIndex i
  let f := box.outerIndex (box.edgeShell.next i)
  pairAdd (pairSmul (edgeT s f (d + 2)) (tPack box (d + 1)))
    (pairSmul (-edgeT s f (d + 1)) (tPack box (d + 2)))

/-- Slot `8 j + k` holds `supportI box i j k`. -/
def supportPackK (box : Box) (i : Fin (box.edgePred + 1)) : ℕ × ℕ :=
  let s := box.outerIndex i
  pairAdd (pairMul (mPackT box i 0) (deltaT s 0))
    (pairAdd (pairMul (mPackT box i 1) (deltaT s 1)) (pairMul (mPackT box i 2) (deltaT s 2)))

def hintSum (box : Box) (hints : List ℤ) : ℤ :=
  (List.finRange (box.edgePred + 1)).foldr (fun i acc => hints.getD i.val 0 + acc) 0

def validEdgeK (box : Box) (hints : List ℤ) : Bool :=
  let L : ℤ := triL box
  let n : ℤ := box.edgePred + 1
  let P : ℤ := 10 ^ 10
  let K : ℕ := 2 ^ (KW - 1)
  let W := fun c => bernWeights box (totalT box c)
  let Wc := bernWeights box ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩
  let thw : ℤ := (-16000 * L - 1) / P
  let TD : ℤ := hintSum box hints
  decide (0 < L) && decide (0 < boxE box) &&
    (List.finRange 3).all (fun i =>
      (List.finRange 3).all (fun c => decide (0 ≤ (rootSign box.root c).num * T box i c)) &&
      decide ((rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = L)) &&
    (List.finRange 3).all (fun j => decide (0 ≤ (box.ballMultiplier j).num)) &&
    (List.finRange (box.edgePred + 1)).all (fun i =>
      let S := supportPackK box i
      let MS := 19200 * tBound box
      let h := hints.getD i.val 0
      decide (4 * (MS + h.natAbs) < K) && decide (4 * (MS + thw.natAbs) < K) &&
        testGeM (pairNeg S) 24 (maskAll 24) (-h) &&
        testGeM (pairNeg S) 24 (maskT (box.nonzeroWitness i)) (-thw)) &&
    (List.finRange 3).all (fun j =>
      let μ := box.ballMultiplier j
      let th := ceilDiv (dBoundNum box * (TD * P + 32000 * n * L) * 4 * μ.den) (10 ^ 10)
      let U := pairAdd (pairSmul (μ.den : ℤ) (pairAdd (pairSmul (T box j 0) (bernPairK (W 0)))
        (pairAdd (pairSmul (T box j 1) (bernPairK (W 1))) (pairSmul (T box j 2) (bernPairK (W 2))))))
        (pairSmul (μ.num * 1600 * L) (bernPairK Wc))
      let M := μ.den * ((T box j 0).natAbs * boundK (W 0) + ((T box j 1).natAbs * boundK (W 1) +
        (T box j 2).natAbs * boundK (W 2))) + (μ.num * 1600 * L).natAbs * boundK Wc
      decide (4 * (M + th.natAbs) < K) && testGeM U 27 (maskAll 27) th)

end Noperts.Stellated.ChartKernel
