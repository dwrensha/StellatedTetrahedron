module

public import Noperts.Stellated.AtlasProjectiveLocalCertificate

@[expose] public section

/-!
# Integer rendering of the local view check (kernel prototype)

`AtlasProjectiveLocalCertificate.Box.ViewValid` evaluated in exact integer
arithmetic: the triangle is scaled by the common denominator `L` of its
coordinates, vertices by 40, edges by 40000.  Every rational comparison of the
specification becomes an integer comparison after clearing positive
denominators.  Intended for `decide +kernel`, where rational arithmetic costs
about a millisecond per operation and small integer arithmetic microseconds.
-/

namespace Noperts.Stellated.LocalKernel

open AtlasProjectiveLocalCertificate

structure V3 where
  x : Int
  y : Int
  z : Int

namespace V3

def dot (a b : V3) : Int :=
  Int.add (Int.add (Int.mul a.x b.x) (Int.mul a.y b.y)) (Int.mul a.z b.z)

def cross (a b : V3) : V3 :=
  ⟨Int.sub (Int.mul a.y b.z) (Int.mul a.z b.y), Int.sub (Int.mul a.z b.x) (Int.mul a.x b.z),
    Int.sub (Int.mul a.x b.y) (Int.mul a.y b.x)⟩

def sub (a b : V3) : V3 := ⟨Int.sub a.x b.x, Int.sub a.y b.y, Int.sub a.z b.z⟩

def add (a b : V3) : V3 := ⟨Int.add a.x b.x, Int.add a.y b.y, Int.add a.z b.z⟩

def smul (c : Int) (a : V3) : V3 := ⟨Int.mul c a.x, Int.mul c a.y, Int.mul c a.z⟩

def get (a : V3) (c : Fin 3) : Int :=
  match c with
  | 0 => a.x
  | 1 => a.y
  | 2 => a.z

end V3

/-- `40 · rationalVertex`. -/
def vtx : VertexIndex → V3
  | 0 => ⟨20, 20, 20⟩
  | 1 => ⟨20, -20, -20⟩
  | 2 => ⟨-20, 20, -20⟩
  | 3 => ⟨-20, -20, 20⟩
  | 4 => ⟨-11, -11, -11⟩
  | 5 => ⟨-11, 11, 11⟩
  | 6 => ⟨11, -11, 11⟩
  | 7 => ⟨11, 11, -11⟩

def min3 (a b c : Int) : Int := min a (min b c)
def max3 (a b c : Int) : Int := max a (max b c)

/-- `40000 · edgeQ`. -/
def edgeN (cert : AxisCertificate) (i : Fin 3) : V3 :=
  let m : Int := (cert.mix i).val
  V3.add (V3.smul m (V3.sub (vtx (cert.edgeStart i)) (vtx (cert.edgeFinish i))))
    (V3.smul (1000 - m) (V3.sub (vtx (cert.edgeStart₂ i)) (vtx (cert.edgeFinish₂ i))))

/-- `40 · 40000 · crossLiftCoefficient i coordinate` for support vertex `s`. -/
def crossLiftN (s : V3) (e : V3) (coordinate : Fin 3) : V3 :=
  -- liftCoefficient columns: l0 = (0, e2, -e1), l1 = (-e2, 0, e0), l2 = (e1, -e0, 0)
  let l0 : V3 := ⟨0, e.z, -e.y⟩
  let l1 : V3 := ⟨-e.z, 0, e.x⟩
  let l2 : V3 := ⟨e.y, -e.x, 0⟩
  match coordinate with
  | 0 => V3.sub (V3.smul s.y l2) (V3.smul s.z l1)
  | 1 => V3.sub (V3.smul s.z l0) (V3.smul s.x l2)
  | 2 => V3.sub (V3.smul s.x l1) (V3.smul s.y l0)

/-- Six quadratic coefficients `xx xy xz yy yz zz`. -/
structure Q6 where
  xx : Int
  xy : Int
  xz : Int
  yy : Int
  yz : Int
  zz : Int

def mulLinearN (a b : V3) : Q6 :=
  ⟨a.x * b.x, a.x * b.y + a.y * b.x, a.x * b.z + a.z * b.x,
    a.y * b.y, a.y * b.z + a.z * b.y, a.z * b.z⟩

def Q6.add (p q : Q6) : Q6 :=
  ⟨p.xx + q.xx, p.xy + q.xy, p.xz + q.xz, p.yy + q.yy, p.yz + q.yz, p.zz + q.zz⟩

/-- Ball data of the triangle box in `T` units: `M = lo + hi`, `R = hi - lo`. -/
structure BoxN where
  mx : Int
  my : Int
  mz : Int
  rx : Int
  ry : Int
  rz : Int

/-- `4 L² · 2.56e15 · center` and `· radius` of the variation ball. -/
def ballN (q : Q6) (b : BoxN) : Int × Int :=
  let center := q.xx * b.mx * b.mx + q.xy * b.mx * b.my + q.xz * b.mx * b.mz +
    q.yy * b.my * b.my + q.yz * b.my * b.mz + q.zz * b.mz * b.mz
  let gx := 2 * q.xx * b.mx + q.xy * b.my + q.xz * b.mz
  let gy := q.xy * b.mx + 2 * q.yy * b.my + q.yz * b.mz
  let gz := q.xz * b.mx + q.yz * b.my + 2 * q.zz * b.mz
  let radius := |gx| * b.rx + |gy| * b.ry + |gz| * b.rz +
    |q.xx| * b.rx * b.rx + |q.xy| * b.rx * b.ry + |q.xz| * b.rx * b.rz +
    |q.yy| * b.ry * b.ry + |q.yz| * b.ry * b.rz + |q.zz| * b.rz * b.rz
  (center, radius)

def det3 (a b c : V3) : Int := V3.dot a (V3.cross b c)

/-- Support test for one edge: for every vertex `k`, either `k` is an exact tie
or all three corner values `dot(vtx k - vtx s, cross(t, e))` are `≤ 0`; and the
nonzero witness is not a tie with all three values `< 0`. -/
def supportN (t0 t1 t2 e : V3) (s : VertexIndex) (mix : Nat)
    (es ef es₂ ef₂ w : VertexIndex) : Bool :=
  let vs := vtx s
  let u0 := V3.cross t0 e
  let u1 := V3.cross t1 e
  let u2 := V3.cross t2 e
  let a0 := V3.dot vs u0
  let a1 := V3.dot vs u1
  let a2 := V3.dot vs u2
  let tie : VertexIndex → Bool := fun k =>
    k == s || (mix == 1000 && s == ef && k == es) || (mix == 0 && s == es₂ && k == ef₂)
  let val : VertexIndex → Int := fun k =>
    let vk := vtx k
    max3 (V3.dot vk u0 - a0) (V3.dot vk u1 - a1) (V3.dot vk u2 - a2)
  let okK : VertexIndex → Bool := fun k => tie k || decide (val k ≤ 0)
  okK 0 && okK 1 && okK 2 && okK 3 && okK 4 && okK 5 && okK 6 && okK 7 &&
    (!tie w && decide (val w < 0))

/-- The weight-coefficient cross product of an axis certificate for contact `i`. -/
def wcN (cert : AxisCertificate) (i : Fin 3) : V3 :=
  match i with
  | 0 => V3.cross (edgeN cert 1) (edgeN cert 2)
  | 1 => V3.cross (edgeN cert 2) (edgeN cert 0)
  | 2 => V3.cross (edgeN cert 0) (edgeN cert 1)

/-! ### `Nat` fast path of the support test

For a nonnegative triangle the support test runs on `Nat` only (GMP-backed in
the kernel).  With `e = e⁺ - e⁻`, `cross(t, e) = P - N` for
`P, N` below, and with the offset vertices `v̂ = 40·v + 20 ∈ [0, 40]` the value
`dot(v_k - v_s, P - N)` is `≤ 0` iff `A_k + B_s ≤ B_k + A_s`, where
`A = dot(v̂, P)`, `B = dot(v̂, N)`. -/

structure N3' where
  x : Nat
  y : Nat
  z : Nat

/-- `40 · rationalVertex + 20`. -/
def vtxN : VertexIndex → N3'
  | 0 => ⟨40, 40, 40⟩
  | 1 => ⟨40, 0, 0⟩
  | 2 => ⟨0, 40, 0⟩
  | 3 => ⟨0, 0, 40⟩
  | 4 => ⟨9, 9, 9⟩
  | 5 => ⟨9, 31, 31⟩
  | 6 => ⟨31, 9, 31⟩
  | 7 => ⟨31, 31, 9⟩

def dotN (a b : N3') : Nat := Nat.add (Nat.add (Nat.mul a.x b.x) (Nat.mul a.y b.y)) (Nat.mul a.z b.z)

/-- `dot(v_k - v_s, P - N) ≤ 0` (`< 0` if `strict`). -/
def vertexTestN (strict : Bool) (P N : N3') (k s : VertexIndex) : Bool :=
  let vk := vtxN k
  let vs := vtxN s
  let lhs := Nat.add (dotN vk P) (dotN vs N)
  let rhs := Nat.add (dotN vk N) (dotN vs P)
  if strict then Nat.blt lhs rhs else Nat.ble lhs rhs

/-- One corner's support tests from the parts of `cross(t, e)`. -/
def cornerN (P N : N3') (s : VertexIndex) (tie : VertexIndex → Bool) (w : VertexIndex) : Bool :=
  let ok := fun k => tie k || vertexTestN false P N k s
  ok 0 && ok 1 && ok 2 && ok 3 && ok 4 && ok 5 && ok 6 && ok 7 &&
    vertexTestN true P N w s

/-- `cross(t, e⁺ - e⁻) = P - N`. -/
def crossP (t ep en : N3') : N3' :=
  ⟨Nat.add (Nat.mul t.y ep.z) (Nat.mul t.z en.y), Nat.add (Nat.mul t.z ep.x) (Nat.mul t.x en.z),
    Nat.add (Nat.mul t.x ep.y) (Nat.mul t.y en.x)⟩
def crossN (t ep en : N3') : N3' :=
  ⟨Nat.add (Nat.mul t.y en.z) (Nat.mul t.z ep.y), Nat.add (Nat.mul t.z en.x) (Nat.mul t.x ep.z),
    Nat.add (Nat.mul t.x en.y) (Nat.mul t.y ep.x)⟩

def toN3 (a : V3) : N3' := ⟨a.x.toNat, a.y.toNat, a.z.toNat⟩
def posPart (a : V3) : N3' := ⟨a.x.toNat, a.y.toNat, a.z.toNat⟩
def negPart (a : V3) : N3' := ⟨(-a.x).toNat, (-a.y).toNat, (-a.z).toNat⟩

def nonnegV3 (a : V3) : Bool := decide (0 ≤ a.x ∧ 0 ≤ a.y ∧ 0 ≤ a.z)

/-- The support test of `supportN`, on `Nat` when the corners are nonnegative. -/
def supportFast (t0 t1 t2 e : V3) (s : VertexIndex) (mix : Nat)
    (es ef es₂ ef₂ w : VertexIndex) : Bool :=
  if nonnegV3 t0 && nonnegV3 t1 && nonnegV3 t2 then
    let tie : VertexIndex → Bool := fun k =>
      k == s || (mix == 1000 && s == ef && k == es) || (mix == 0 && s == es₂ && k == ef₂)
    let ep := posPart e
    let en := negPart e
    let n0 := toN3 t0
    let n1 := toN3 t1
    let n2 := toN3 t2
    !tie w && cornerN (crossP n0 ep en) (crossN n0 ep en) s tie w &&
      cornerN (crossP n1 ep en) (crossN n1 ep en) s tie w &&
      cornerN (crossP n2 ep en) (crossN n2 ep en) s tie w
  else supportN t0 t1 t2 e s mix es ef es₂ ef₂ w

/-- Per-axis integer data and checks. -/
structure AxisOut where
  ok : Bool
  /-- `4 L² · 2.56e15 · variationBall.center` for the three coordinates. -/
  center : V3

def axisN (box : Box) (L : Int) (t0 t1 t2 : V3) (bn : BoxN) (j : Fin 4) : AxisOut :=
  let cert := box.certificate j
  let e0 := edgeN cert 0
  let e1 := edgeN cert 1
  let e2 := edgeN cert 2
  let wc0 := wcN cert 0
  let wc1 := wcN cert 1
  let wc2 := wcN cert 2
  -- weights (scaled by L · 1.6e9)
  let w0 := (V3.dot t0 wc0, V3.dot t1 wc0, V3.dot t2 wc0)
  let w1 := (V3.dot t0 wc1, V3.dot t1 wc1, V3.dot t2 wc1)
  let w2 := (V3.dot t0 wc2, V3.dot t1 wc2, V3.dot t2 wc2)
  let lo0 := min3 w0.1 w0.2.1 w0.2.2
  let lo1 := min3 w1.1 w1.2.1 w1.2.2
  let lo2 := min3 w2.1 w2.2.1 w2.2.2
  let hi0 := max3 w0.1 w0.2.1 w0.2.2
  let hi1 := max3 w1.1 w1.2.1 w1.2.2
  let hi2 := max3 w2.1 w2.2.1 w2.2.2
  let B := cert.B
  let weightsOk := decide (0 ≤ lo0 ∧ 0 ≤ lo1 ∧ 0 ≤ lo2 ∧ (0 < lo0 ∨ 0 < lo1 ∨ 0 < lo2))
  let budgetOk := decide (2 * B.den * (hi0 + hi1 + hi2) ≤ B.num * L * 1600000000)
  -- supports: dot(t, cross(e, vtx k - vtx s)) = dot(vtx k - vtx s, cross(t, e))
  let s0 := cert.supportIndex box 0
  let s1 := cert.supportIndex box 1
  let s2 := cert.supportIndex box 2
  let supportsOk := supportFast t0 t1 t2 e0 s0 (cert.mix 0).val (cert.edgeStart 0)
      (cert.edgeFinish 0) (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0) (cert.nonzeroWitness 0) &&
    supportFast t0 t1 t2 e1 s1 (cert.mix 1).val (cert.edgeStart 1)
      (cert.edgeFinish 1) (cert.edgeStart₂ 1) (cert.edgeFinish₂ 1) (cert.nonzeroWitness 1) &&
    supportFast t0 t1 t2 e2 s2 (cert.mix 2).val (cert.edgeStart 2)
      (cert.edgeFinish 2) (cert.edgeStart₂ 2) (cert.edgeFinish₂ 2) (cert.nonzeroWitness 2)
  let s : Fin 3 → VertexIndex := fun i => match i with | 0 => s0 | 1 => s1 | 2 => s2
  -- variation balls
  let q : Fin 3 → Q6 := fun coordinate =>
    Q6.add (Q6.add (mulLinearN wc0 (crossLiftN (vtx (s 0)) e0 coordinate))
      (mulLinearN wc1 (crossLiftN (vtx (s 1)) e1 coordinate)))
      (mulLinearN wc2 (crossLiftN (vtx (s 2)) e2 coordinate))
  let b0 := ballN (q 0) bn
  let b1 := ballN (q 1) bn
  let b2 := ballN (q 2) bn
  let δ := box.δ
  -- Σ radius / (4L²·2.56e15) + 9/(2·10⁸) ≤ B·δ
  let scale : Int := 4 * L * L * 2560000000000000
  let variationOk := decide ((b0.2 + b1.2 + b2.2) * 200000000 * B.den * δ.den +
      9 * scale * B.den * δ.den ≤ B.num * δ.num * scale * 200000000)
  { ok := decide (0 < B) && weightsOk && budgetOk && supportsOk && variationOk
    center := ⟨b0.1, b1.1, b2.1⟩ }

/-- The barycentric test on integer centers `P j = scale_j · center_j`, all
points (and targets) scaled by one common positive factor. -/
def barycentricN (P0 P1 P2 P3 : V3) (target : Int) : Bool :=
  let a := V3.sub P0 P3
  let b := V3.sub P1 P3
  let c := V3.sub P2 P3
  let D := det3 a b c
  let ok : V3 → Bool := fun t =>
    let y := V3.sub t P3
    let d0 := det3 y b c
    let d1 := det3 a y c
    let d2 := det3 a b y
    decide (0 ≤ d0 * D ∧ 0 ≤ d1 * D ∧ 0 ≤ d2 * D ∧ 0 ≤ (D - d0 - d1 - d2) * D)
  decide (D ≠ 0) &&
    ok ⟨target, 0, 0⟩ && ok ⟨-target, 0, 0⟩ && ok ⟨0, target, 0⟩ &&
    ok ⟨0, -target, 0⟩ && ok ⟨0, 0, target⟩ && ok ⟨0, 0, -target⟩

/-- `0 ≤ x * D` without forming the product. -/
def sameSign (x D : Int) : Bool := decide ((0 < D → 0 ≤ x) ∧ (D < 0 → x ≤ 0))

/-- `barycentricN` with shared cross products: for the target `y = σ T e_m`,
`det(y - P₃, b, c) = σ T (b × c)_m - P₃ · (b × c)`, and likewise with
`c × a`, `a × b`; sign tests replace the products `d · D`. -/
def barycentricN2 (P0 P1 P2 P3 : V3) (target : Int) : Bool :=
  let a := V3.sub P0 P3
  let b := V3.sub P1 P3
  let c := V3.sub P2 P3
  let bc := V3.cross b c
  let ca := V3.cross c a
  let ab := V3.cross a b
  let D := V3.dot a bc
  let e0 := V3.dot P3 bc
  let e1 := V3.dot P3 ca
  let e2 := V3.dot P3 ab
  let test := fun (u0 u1 u2 : Int) =>
    sameSign u0 D && sameSign u1 D && sameSign u2 D && sameSign (D - u0 - u1 - u2) D
  let ax := fun (g0 g1 g2 : Int) =>
    test (target * g0 - e0) (target * g1 - e1) (target * g2 - e2) &&
      test (-target * g0 - e0) (-target * g1 - e1) (-target * g2 - e2)
  decide (D ≠ 0) && ax bc.x ca.x ab.x && ax bc.y ca.y ab.y && ax bc.z ca.z ab.z

/-- The gcd of a vector's coordinates with `g`. -/
def gcdV3 (a : V3) (g : Nat) : Nat := Nat.gcd (Nat.gcd (Nat.gcd g a.x.natAbs) a.y.natAbs) a.z.natAbs

def divV3 (a : V3) (g : Int) : V3 := ⟨a.x / g, a.y / g, a.z / g⟩

/-- `barycentricN2` after dividing all points and the target by their common
gcd (barycentric coordinates are invariant under uniform positive scaling). -/
def barycentricN3 (P0 P1 P2 P3 : V3) (target : Int) : Bool :=
  let g := gcdV3 P3 (gcdV3 P2 (gcdV3 P1 (gcdV3 P0 target.natAbs)))
  if g = 0 then barycentricN2 P0 P1 P2 P3 target
  else
    let gi : Int := g
    barycentricN2 (divV3 P0 gi) (divV3 P1 gi) (divV3 P2 gi) (divV3 P3 gi) (target / gi)


/-- The common denominator of a triangle's nine coordinates. -/
def lcm9 (t : AtlasProjectiveView.Triangle ℚ) : Nat :=
  Nat.lcm (Nat.lcm (Nat.lcm (t 0 0).den (t 0 1).den) (Nat.lcm (t 0 2).den
    (t 1 0).den)) (Nat.lcm (Nat.lcm (t 1 1).den (t 1 2).den) (Nat.lcm (t 2 0).den
    (Nat.lcm (t 2 1).den (t 2 2).den)))

/-- `L · q` as an integer, for `q.den ∣ L`. -/
def scaleQ (L : Nat) (q : ℚ) : Int := q.num * ((L / q.den : Nat) : Int)

def triRow (L : Nat) (t : AtlasProjectiveView.Triangle ℚ) (c : Fin 3) : V3 :=
  ⟨scaleQ L (t c 0), scaleQ L (t c 1), scaleQ L (t c 2)⟩

/-- `M = lo + hi`, `R = hi - lo` of the triangle's coordinate box, in `T` units. -/
def boxNOf (t0 t1 t2 : V3) : BoxN :=
  ⟨min3 t0.x t1.x t2.x + max3 t0.x t1.x t2.x, min3 t0.y t1.y t2.y + max3 t0.y t1.y t2.y,
    min3 t0.z t1.z t2.z + max3 t0.z t1.z t2.z,
    max3 t0.x t1.x t2.x - min3 t0.x t1.x t2.x, max3 t0.y t1.y t2.y - min3 t0.y t1.y t2.y,
    max3 t0.z t1.z t2.z - min3 t0.z t1.z t2.z⟩

/-- `SignedTriangleValid` for one scaled corner `p = L · t c`. -/
def triOkN (root : Fin 8) (L : Int) (p : V3) : Bool :=
  let sgn : Fin 3 → Int := fun c => (AtlasProjectiveView.rootSign root c : ℚ).num
  decide (0 ≤ sgn 0 * p.x ∧ 0 ≤ sgn 1 * p.y ∧ 0 ≤ sgn 2 * p.z ∧
    sgn 0 * p.x + sgn 1 * p.y + sgn 2 * p.z = L)

/-- The barycentric test from the four scaled variation-ball centers
`ctr j = 4L²·2.56e15 · center_j`: all points scaled by `4L²·2.56e15 · ∏ Bn · sd`. -/
def baryN (box : Box) (L : Int) (c0 c1 c2 c3 : V3) : Bool :=
  let B0 := (box.certificate 0).B
  let B1 := (box.certificate 1).B
  let B2 := (box.certificate 2).B
  let B3 := (box.certificate 3).B
  let sQ : ℚ := 7 / 4 * (box.c + box.δ)
  let scale : Int := 4 * L * L * 2560000000000000
  barycentricN3 (V3.smul (B0.den * B1.num * B2.num * B3.num * sQ.den) c0)
    (V3.smul (B1.den * B0.num * B2.num * B3.num * sQ.den) c1)
    (V3.smul (B2.den * B0.num * B1.num * B3.num * sQ.den) c2)
    (V3.smul (B3.den * B0.num * B1.num * B2.num * sQ.den) c3)
    (sQ.num * scale * B0.num * B1.num * B2.num * B3.num)

def viewValidCore (box : Box) (L : Nat) (t0 t1 t2 : V3) : Bool :=
  let Li : Int := L
  let bn := boxNOf t0 t1 t2
  let o0 := axisN box Li t0 t1 t2 bn 0
  let o1 := axisN box Li t0 t1 t2 bn 1
  let o2 := axisN box Li t0 t1 t2 bn 2
  let o3 := axisN box Li t0 t1 t2 bn 3
  decide (0 < L) && triOkN box.root Li t0 && triOkN box.root Li t1 && triOkN box.root Li t2 &&
    decide (0 ≤ box.c ∧ 0 ≤ box.δ ∧ 0 ≤ box.r) &&
    o0.ok && o1.ok && o2.ok && o3.ok &&
    baryN box Li o0.center o1.center o2.center o3.center &&
    decide (box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2)

def viewValidN (box : Box) : Bool :=
  let L := lcm9 box.triangle
  viewValidCore box L (triRow L box.triangle 0) (triRow L box.triangle 1)
    (triRow L box.triangle 2)

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

/-- Profiling helpers (prototype). -/
def viewValidL (box : Box) : Nat := lcm9 box.triangle

def axisOnly (box : Box) (j : Fin 4) : Bool :=
  let t := box.triangle
  let L := viewValidL box
  let sc : ℚ → Int := fun x => x.num * ((L / x.den : Nat) : Int)
  let row : Fin 3 → V3 := fun c => ⟨sc (t c 0), sc (t c 1), sc (t c 2)⟩
  let t0 := row 0
  let t1 := row 1
  let t2 := row 2
  let bn : BoxN := ⟨0, 0, 0, 0, 0, 0⟩
  (axisN box L t0 t1 t2 bn j).ok || true

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

def triRows (box : Box) : V3 × V3 × V3 :=
  let t := box.triangle
  let L := viewValidL box
  let sc : ℚ → Int := fun x => x.num * ((L / x.den : Nat) : Int)
  (⟨sc (t 0 0), sc (t 0 1), sc (t 0 2)⟩, ⟨sc (t 1 0), sc (t 1 1), sc (t 1 2)⟩,
    ⟨sc (t 2 0), sc (t 2 1), sc (t 2 2)⟩)

def partEdges (box : Box) (j : Fin 4) : Bool :=
  let cert := box.certificate j
  decide ((edgeN cert 0).x + (edgeN cert 1).y + (edgeN cert 2).z ≠ 12345)

def partTri (box : Box) : Bool :=
  let r := triRows box
  decide (r.1.x + r.2.1.y + r.2.2.z ≠ 12345)

def partSupport (box : Box) (j : Fin 4) : Bool :=
  let cert := box.certificate j
  let r := triRows box
  supportN r.1 r.2.1 r.2.2 (edgeN cert 0) (cert.supportIndex box 0) (cert.mix 0).val
    (cert.edgeStart 0) (cert.edgeFinish 0) (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
    (cert.nonzeroWitness 0) || true

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

/-! ### Nat-only support test (prototype)

Signed values are carried as `x⁺ - x⁻` with both parts in `Nat`, so the kernel
only ever runs GMP-backed `Nat` primitives. Vertices are offset by 20
(`v̂ = 40·v + 20 ∈ [0, 40]`); the triangle (root 0) is nonnegative. -/

structure N3 where
  x : Nat
  y : Nat
  z : Nat

/-- `40 · rationalVertex + 20`. -/
def vtxO : VertexIndex → N3
  | 0 => ⟨40, 40, 40⟩
  | 1 => ⟨40, 0, 0⟩
  | 2 => ⟨0, 40, 0⟩
  | 3 => ⟨0, 0, 40⟩
  | 4 => ⟨9, 9, 9⟩
  | 5 => ⟨9, 31, 31⟩
  | 6 => ⟨31, 9, 31⟩
  | 7 => ⟨31, 31, 9⟩

/-- `1000 · 40 · edge` as positive and negative parts (offsets cancel). -/
def edgeParts (m : Nat) (a b c d : VertexIndex) : N3 × N3 :=
  let va := vtxO a
  let vb := vtxO b
  let vc := vtxO c
  let vd := vtxO d
  let m' := Nat.sub 1000 m
  let px := Nat.add (Nat.mul m va.x) (Nat.mul m' vc.x)
  let py := Nat.add (Nat.mul m va.y) (Nat.mul m' vc.y)
  let pz := Nat.add (Nat.mul m va.z) (Nat.mul m' vc.z)
  let nx := Nat.add (Nat.mul m vb.x) (Nat.mul m' vd.x)
  let ny := Nat.add (Nat.mul m vb.y) (Nat.mul m' vd.y)
  let nz := Nat.add (Nat.mul m vb.z) (Nat.mul m' vd.z)
  (⟨Nat.sub px nx, Nat.sub py ny, Nat.sub pz nz⟩, ⟨Nat.sub nx px, Nat.sub ny py, Nat.sub nz pz⟩)

/-- One corner: is `dot(vtx k - vtx s, cross(t, e)) ≤ 0` (`strict`: `< 0`)? -/
def cornerTest (strict : Bool) (t ep en : N3) (k s : VertexIndex) : Bool :=
  -- cross(t, e) = P - N
  let Px := Nat.add (Nat.mul t.y ep.z) (Nat.mul t.z en.y)
  let Nx := Nat.add (Nat.mul t.y en.z) (Nat.mul t.z ep.y)
  let Py := Nat.add (Nat.mul t.z ep.x) (Nat.mul t.x en.z)
  let Ny := Nat.add (Nat.mul t.z en.x) (Nat.mul t.x ep.z)
  let Pz := Nat.add (Nat.mul t.x ep.y) (Nat.mul t.y en.x)
  let Nz := Nat.add (Nat.mul t.x en.y) (Nat.mul t.y ep.x)
  let vk := vtxO k
  let vs := vtxO s
  let dpx := Nat.sub vk.x vs.x
  let dnx := Nat.sub vs.x vk.x
  let dpy := Nat.sub vk.y vs.y
  let dny := Nat.sub vs.y vk.y
  let dpz := Nat.sub vk.z vs.z
  let dnz := Nat.sub vs.z vk.z
  let A := Nat.add (Nat.add (Nat.add (Nat.mul dpx Px) (Nat.mul dnx Nx))
    (Nat.add (Nat.mul dpy Py) (Nat.mul dny Ny))) (Nat.add (Nat.mul dpz Pz) (Nat.mul dnz Nz))
  let B := Nat.add (Nat.add (Nat.add (Nat.mul dpx Nx) (Nat.mul dnx Px))
    (Nat.add (Nat.mul dpy Ny) (Nat.mul dny Py))) (Nat.add (Nat.mul dpz Nz) (Nat.mul dnz Pz))
  if strict then Nat.blt A B else Nat.ble A B

def supportNat (t0 t1 t2 : N3) (ep en : N3) (s : VertexIndex) (mix : Nat)
    (es ef es₂ ef₂ w : VertexIndex) : Bool :=
  let tie : VertexIndex → Bool := fun k =>
    k == s || (mix == 1000 && s == ef && k == es) || (mix == 0 && s == es₂ && k == ef₂)
  let okK : VertexIndex → Bool := fun k =>
    tie k || (cornerTest false t0 ep en k s && cornerTest false t1 ep en k s &&
      cornerTest false t2 ep en k s)
  okK 0 && okK 1 && okK 2 && okK 3 && okK 4 && okK 5 && okK 6 && okK 7 &&
    (!tie w && cornerTest true t0 ep en w s && cornerTest true t1 ep en w s &&
      cornerTest true t2 ep en w s)

def triRowsN (box : Box) : N3 × N3 × N3 :=
  let r := triRows box
  (⟨r.1.x.toNat, r.1.y.toNat, r.1.z.toNat⟩, ⟨r.2.1.x.toNat, r.2.1.y.toNat, r.2.1.z.toNat⟩,
    ⟨r.2.2.x.toNat, r.2.2.y.toNat, r.2.2.z.toNat⟩)

def partSupportNat (box : Box) (j : Fin 4) : Bool :=
  let cert := box.certificate j
  let r := triRowsN box
  let e := edgeParts (cert.mix 0).val (cert.edgeStart 0) (cert.edgeFinish 0)
    (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
  supportNat r.1 r.2.1 r.2.2 e.1 e.2 (cert.supportIndex box 0) (cert.mix 0).val
    (cert.edgeStart 0) (cert.edgeFinish 0) (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
    (cert.nonzeroWitness 0) || true

def partSupportNatOnly (box : Box) (j : Fin 4) : Bool :=
  let cert := box.certificate j
  let r := triRowsN box
  let e := edgeParts (cert.mix 0).val (cert.edgeStart 0) (cert.edgeFinish 0)
    (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
  supportNat r.1 r.2.1 r.2.2 e.1 e.2 (cert.supportIndex box 0) (cert.mix 0).val
    (cert.edgeStart 0) (cert.edgeFinish 0) (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
    (cert.nonzeroWitness 0)

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

/-- `dot(vk - vs, P - N) ≤ 0` (or `< 0`) for precomputed parts of `cross(t, e)`. -/
def kTest (strict : Bool) (Px Nx Py Ny Pz Nz : Nat) (vk vs : N3) : Bool :=
  let dpx := Nat.sub vk.x vs.x
  let dnx := Nat.sub vs.x vk.x
  let dpy := Nat.sub vk.y vs.y
  let dny := Nat.sub vs.y vk.y
  let dpz := Nat.sub vk.z vs.z
  let dnz := Nat.sub vs.z vk.z
  let A := Nat.add (Nat.add (Nat.add (Nat.mul dpx Px) (Nat.mul dnx Nx))
    (Nat.add (Nat.mul dpy Py) (Nat.mul dny Ny))) (Nat.add (Nat.mul dpz Pz) (Nat.mul dnz Nz))
  let B := Nat.add (Nat.add (Nat.add (Nat.mul dpx Nx) (Nat.mul dnx Px))
    (Nat.add (Nat.mul dpy Ny) (Nat.mul dny Py))) (Nat.add (Nat.mul dpz Nz) (Nat.mul dnz Pz))
  if strict then Nat.blt A B else Nat.ble A B

/-- All eight vertices (ties excused via `tieMask` bits) plus the strict witness,
for one corner with precomputed cross parts. -/
def cornerAll (Px Nx Py Ny Pz Nz : Nat) (vs : N3) (tie : VertexIndex → Bool)
    (w : VertexIndex) : Bool :=
  let t := fun k => tie k || kTest false Px Nx Py Ny Pz Nz (vtxO k) vs
  t 0 && t 1 && t 2 && t 3 && t 4 && t 5 && t 6 && t 7 &&
    kTest true Px Nx Py Ny Pz Nz (vtxO w) vs

def cornerOf (t ep en : N3) (vs : N3) (tie : VertexIndex → Bool) (w : VertexIndex) : Bool :=
  cornerAll (Nat.add (Nat.mul t.y ep.z) (Nat.mul t.z en.y))
    (Nat.add (Nat.mul t.y en.z) (Nat.mul t.z ep.y))
    (Nat.add (Nat.mul t.z ep.x) (Nat.mul t.x en.z))
    (Nat.add (Nat.mul t.z en.x) (Nat.mul t.x ep.z))
    (Nat.add (Nat.mul t.x ep.y) (Nat.mul t.y en.x))
    (Nat.add (Nat.mul t.x en.y) (Nat.mul t.y ep.x)) vs tie w

def supportNat2 (t0 t1 t2 : N3) (ep en : N3) (s : VertexIndex) (mix : Nat)
    (es ef es₂ ef₂ w : VertexIndex) : Bool :=
  let tie : VertexIndex → Bool := fun k =>
    k == s || (mix == 1000 && s == ef && k == es) || (mix == 0 && s == es₂ && k == ef₂)
  let vs := vtxO s
  !tie w && cornerOf t0 ep en vs tie w && cornerOf t1 ep en vs tie w &&
    cornerOf t2 ep en vs tie w

def partSupportNat2 (box : Box) (j : Fin 4) : Bool :=
  let cert := box.certificate j
  let r := triRowsN box
  let e := edgeParts (cert.mix 0).val (cert.edgeStart 0) (cert.edgeFinish 0)
    (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
  supportNat2 r.1 r.2.1 r.2.2 e.1 e.2 (cert.supportIndex box 0) (cert.mix 0).val
    (cert.edgeStart 0) (cert.edgeFinish 0) (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
    (cert.nonzeroWitness 0)

def partTriN (box : Box) : Bool :=
  let r := triRowsN box
  Nat.ble 1 (r.1.x + r.2.1.y + r.2.2.z)

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

/-! ### Packed (SWAR) support test (prototype)

Eight 64-bit fields, one per vertex `k`, hold `w_k + O` for the support
functional `w_k = cross(e, v_k - v_s)` (offset `O = 2^24 ≥ |w_k|`).  A corner's
eight values `t · w_k + O·Σt` come from three big multiplications; adding
`2^63 - 1 - O·Σt` to every field sets bit 63 exactly where `t · w_k > 0`. -/

/-- `Σ_k 2^(64k)` for `k < 8`. -/
def ONES : Nat := 1 + 2^64 + 2^128 + 2^192 + 2^256 + 2^320 + 2^384 + 2^448

/-- Bit 63 of every field. -/
def HIGH : Nat := ONES * 2^63

/-- Packed offset vertex coordinates `v̂_k = 40·v_k + 20` (fields `k = 0..7`). -/
def VX : Nat := 40 + 40 * 2^64 + 0 * 2^128 + 0 * 2^192 + 9 * 2^256 + 9 * 2^320 + 31 * 2^384 + 31 * 2^448
def VY : Nat := 40 + 0 * 2^64 + 40 * 2^128 + 0 * 2^192 + 9 * 2^256 + 31 * 2^320 + 9 * 2^384 + 31 * 2^448
def VZ : Nat := 40 + 0 * 2^64 + 0 * 2^128 + 40 * 2^192 + 9 * 2^256 + 31 * 2^320 + 31 * 2^384 + 9 * 2^448

def OFF : Nat := 2^24

/-- Packed `w_k + O` component: `a·B + c·C + d - (a'·B + c'·C + d')` style, with
`P`/`N` collecting the positive and negative contributions. -/
def packComp (pB nB pC nC : Nat) (VB VC : Nat) (pS nS : Nat) : Nat :=
  Nat.sub (Nat.add (Nat.add (Nat.mul OFF ONES) (Nat.add (Nat.mul pB VB) (Nat.mul pC VC)))
      (Nat.mul pS ONES))
    (Nat.add (Nat.add (Nat.mul nB VB) (Nat.mul nC VC)) (Nat.mul nS ONES))

/-- Packed `cross(e, v_k - v_s) + O` for all `k`, as three packed components. -/
def packW (ep en vs : N3) : Nat × Nat × Nat :=
  -- w.x = e.y (vk.z - vs.z) - e.z (vk.y - vs.y)
  let wx := packComp ep.y en.y en.z ep.z VZ VY
    (Nat.add (Nat.mul en.y vs.z) (Nat.mul ep.z vs.y)) (Nat.add (Nat.mul ep.y vs.z) (Nat.mul en.z vs.y))
  -- w.y = e.z (vk.x - vs.x) - e.x (vk.z - vs.z)
  let wy := packComp ep.z en.z en.x ep.x VX VZ
    (Nat.add (Nat.mul en.z vs.x) (Nat.mul ep.x vs.z)) (Nat.add (Nat.mul ep.z vs.x) (Nat.mul en.x vs.z))
  -- w.z = e.x (vk.y - vs.y) - e.y (vk.x - vs.x)
  let wz := packComp ep.x en.x en.y ep.y VY VX
    (Nat.add (Nat.mul en.x vs.y) (Nat.mul ep.y vs.x)) (Nat.add (Nat.mul ep.x vs.y) (Nat.mul en.y vs.x))
  (wx, wy, wz)

/-- All non-excused fields have `t · w_k ≤ 0` (`excuse` has bit 63 set on tie fields). -/
def cornerPacked (t : N3) (W : Nat × Nat × Nat) (excuse : Nat) : Bool :=
  let S := Nat.add (Nat.add (Nat.mul t.x W.1) (Nat.mul t.y W.2.1)) (Nat.mul t.z W.2.2)
  let θ := Nat.mul OFF (Nat.add (Nat.add t.x t.y) t.z)
  let C := Nat.mul (Nat.sub (2^63 - 1) θ) ONES
  Nat.beq (Nat.land (Nat.land (Nat.add S C) HIGH) (Nat.sub HIGH excuse)) 0

/-- Field `k` of a packed value. -/
def field (x : Nat) (k : Nat) : Nat := Nat.land (Nat.shiftRight x (64 * k)) (2^64 - 1)

/-- Strict test for the witness field: `t · w_k < 0`. -/
def cornerStrict (t : N3) (W : Nat × Nat × Nat) (k : Nat) : Bool :=
  let S := Nat.add (Nat.add (Nat.mul t.x W.1) (Nat.mul t.y W.2.1)) (Nat.mul t.z W.2.2)
  Nat.blt (field S k) (Nat.mul OFF (Nat.add (Nat.add t.x t.y) t.z))

def supportPacked (t0 t1 t2 : N3) (ep en : N3) (s : VertexIndex) (mix : Nat)
    (es ef es₂ ef₂ w : VertexIndex) : Bool :=
  let tie : VertexIndex → Bool := fun k =>
    k == s || (mix == 1000 && s == ef && k == es) || (mix == 0 && s == es₂ && k == ef₂)
  let bit : VertexIndex → Nat := fun k => if tie k then Nat.shiftLeft (2^63) (64 * k.val) else 0
  let excuse := bit 0 + bit 1 + bit 2 + bit 3 + bit 4 + bit 5 + bit 6 + bit 7
  let W := packW ep en (vtxO s)
  !tie w && cornerPacked t0 W excuse && cornerPacked t1 W excuse && cornerPacked t2 W excuse &&
    cornerStrict t0 W w.val && cornerStrict t1 W w.val && cornerStrict t2 W w.val

def partSupportPacked (box : Box) (j : Fin 4) : Bool :=
  let cert := box.certificate j
  let r := triRowsN box
  let e := edgeParts (cert.mix 0).val (cert.edgeStart 0) (cert.edgeFinish 0)
    (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
  supportPacked r.1 r.2.1 r.2.2 e.1 e.2 (cert.supportIndex box 0) (cert.mix 0).val
    (cert.edgeStart 0) (cert.edgeFinish 0) (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0)
    (cert.nonzeroWitness 0)

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

/-! Profiling helpers (probes only). -/

def probeRows (box : Box) : V3 × V3 × V3 :=
  let L := lcm9 box.triangle
  (triRow L box.triangle 0, triRow L box.triangle 1, triRow L box.triangle 2)

def probeAxes (box : Box) : Bool :=
  let L := lcm9 box.triangle
  let r := probeRows box
  let bn := boxNOf r.1 r.2.1 r.2.2
  (axisN box L r.1 r.2.1 r.2.2 bn 0).ok && (axisN box L r.1 r.2.1 r.2.2 bn 1).ok &&
    (axisN box L r.1 r.2.1 r.2.2 bn 2).ok && (axisN box L r.1 r.2.1 r.2.2 bn 3).ok

def probeLcm (box : Box) : Bool := decide (0 < lcm9 box.triangle)

def probeRowsOnly (box : Box) : Bool :=
  let r := probeRows box
  decide (r.1.x + r.2.1.y + r.2.2.z ≠ 7)

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

def probeCenters (box : Box) : Bool :=
  let L := lcm9 box.triangle
  let r := probeRows box
  let bn := boxNOf r.1 r.2.1 r.2.2
  let c := fun j => (axisN box L r.1 r.2.1 r.2.2 bn j).center
  decide ((c 0).x + (c 1).y + (c 2).z + (c 3).x ≠ 7)

def probeBary (box : Box) : Bool :=
  let L := lcm9 box.triangle
  let r := probeRows box
  let bn := boxNOf r.1 r.2.1 r.2.2
  let c := fun j => (axisN box L r.1 r.2.1 r.2.2 bn j).center
  baryN box L (c 0) (c 1) (c 2) (c 3)

end Noperts.Stellated.LocalKernel

namespace Noperts.Stellated.LocalKernel
open AtlasProjectiveLocalCertificate

def probeSupports (box : Box) : Bool :=
  let r := probeRows box
  (List.finRange 4).all fun j =>
    let cert := box.certificate j
    (List.finRange 3).all fun i =>
      supportFast r.1 r.2.1 r.2.2 (edgeN cert i) (cert.supportIndex box i) (cert.mix i).val
        (cert.edgeStart i) (cert.edgeFinish i) (cert.edgeStart₂ i) (cert.edgeFinish₂ i)
        (cert.nonzeroWitness i)

def probeVariation (box : Box) : Bool :=
  let r := probeRows box
  let bn := boxNOf r.1 r.2.1 r.2.2
  (List.finRange 4).all fun j =>
    let cert := box.certificate j
    (List.finRange 3).all fun c =>
      let q := Q6.add (Q6.add (mulLinearN (wcN cert 0)
          (crossLiftN (vtx (cert.supportIndex box 0)) (edgeN cert 0) c))
        (mulLinearN (wcN cert 1) (crossLiftN (vtx (cert.supportIndex box 1)) (edgeN cert 1) c)))
        (mulLinearN (wcN cert 2) (crossLiftN (vtx (cert.supportIndex box 2)) (edgeN cert 2) c))
      decide ((ballN q bn).2 ≠ -1)

def probeWeights (box : Box) : Bool :=
  let r := probeRows box
  (List.finRange 4).all fun j =>
    let cert := box.certificate j
    (List.finRange 3).all fun i =>
      decide (min3 (V3.dot r.1 (wcN cert i)) (V3.dot r.2.1 (wcN cert i))
        (V3.dot r.2.2 (wcN cert i)) ≠ -12345)

end Noperts.Stellated.LocalKernel
