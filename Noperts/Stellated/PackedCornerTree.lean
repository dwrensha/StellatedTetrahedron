module

public import Noperts.Stellated.CornerCoverage
public import Noperts.Stellated.PackedLocalViewTree

@[expose] public section

/-!
# Packed corner blow-up tables

A comma-separated stream of naturals (rationals as zig-zag numerator and
denominator, see `PackedLocalViewTree`).  The 43 tables come in the order:
for segment A then B, the seven plain faces, the six tube faces, the wedge,
the four wedge-tube faces; then the skew root of segment B; then the six
exact-corner-view (`λ = 0`) faces; then the sixteen cone roots at the tie (index
`43 + k`, bit `i` of `k` set when coordinate `i` is negative); then the nine
pocket roots (index `59 + 3 k + m`); then the three skew pocket roots (`68 + m`); then the six plain pocket roots
(`71 + 3 k + m`).  Each table is a
row count followed by rows:

* frame: `seg kind n center₀ … center_{n-1} radius₀ … radius_{n-1} m aff`,
  `aff` = `m` rows of five rationals;
* `0 id frame v m lower upper`: split of variable `v` at `m`;
* `1 id frame T split`: certificate row, `T` = nine edge coordinates, three
  inner and three outer vertices; `split` = count, then `var sign` pairs;
* `2 id frame k`: flip prune with form `k`;
* `3 id frame h`: hand-off (`0` tube, `1` wedge, `2` wedge tube, `3` skew,
  `4` cone, `5` pocket, `6` skew pocket, `7` plain pocket);
* `4 id frame T split shift`: certificate row with a translation, `shift` =
  count, then rationals;
* `5 id frame i j α β lower upper`: stellar split.
-/

namespace Noperts.Stellated.PackedCornerTree

open PackedLocalViewTree CornerPoly CornerCertificate CornerTree CornerCoverage

instance : Inhabited Node :=
  ⟨.leaf 0 ⟨false, .plain, [], [], []⟩ (.flip 0)⟩

instance : Inhabited Table := ⟨{ get := fun _ => default, size := 0 }⟩

def readList {α : Type} (read : Decoder α) : Nat → List α → Decoder (List α)
  | 0, acc => pure acc.reverse
  | n + 1, acc => do
      let a ← read
      readList read n (a :: acc)

def kindOf (n : Nat) : ChartKind :=
  match n with
  | 0 => .plain
  | 1 => .tube
  | 2 => .wedge
  | 3 => .wtube
  | 4 => .skew
  | 5 => .atube
  | 6 => .btube false
  | 7 => .btube true
  | 8 => .askew
  | 9 => .bskew false
  | 10 => .bskew true
  | 11 => .aplain
  | 12 => .bplain false
  | _ => .bplain true

def readFrame : Decoder Frame := do
  let seg ← readNat
  let kind ← readNat
  let n ← readNat
  let center ← readList readRat n []
  let radius ← readList readRat n []
  let m ← readNat
  let aff ← readList (readList readRat 5 []) m []
  pure ⟨seg = 1, kindOf kind, center, radius, aff⟩

def readTriple : Decoder Triple := do
  let e ← readList readRat 9 []
  let inner ← readVertices
  let outer ← readVertices
  pure ⟨fun i j => e.getD (3 * i.val + j.val) 0, inner, outer⟩

def readSplit : Decoder (List (ℕ × Bool)) := do
  let n ← readNat
  readList (do
    let v ← readNat
    let s ← readNat
    pure (v, s = 1)) n []

def handoffOf (n : Nat) : Handoff :=
  match n with
  | 0 => .tube
  | 1 => .wedge
  | 2 => .wtube
  | 3 => .skew
  | 4 => .cone
  | 5 => .pocket
  | 6 => .spocket
  | 7 => .ppocket
  | _ => .cpocket

def readNode : Decoder Node := do
  let tag ← readNat
  let id ← readNat
  let frame ← readFrame
  if tag = 0 then
    let v ← readNat
    let m ← readRat
    let lower ← readNat
    let upper ← readNat
    pure (.split id frame v m lower upper)
  else if tag = 1 then
    let triple ← readTriple
    let split ← readSplit
    pure (.leaf id frame (.cert ⟨frame.seg, frame.kind, frame.center, frame.radius,
      triple, split, [], frame.aff⟩))
  else if tag = 4 then
    let triple ← readTriple
    let split ← readSplit
    let n ← readNat
    let shift ← readList readRat n []
    pure (.leaf id frame (.cert ⟨frame.seg, frame.kind, frame.center, frame.radius,
      triple, split, shift, frame.aff⟩))
  else if tag = 5 then
    let i ← readNat
    let j ← readNat
    let α ← readRat
    let β ← readRat
    let lower ← readNat
    let upper ← readNat
    pure (.stellar id frame i j α β lower upper)
  else if tag = 2 then
    let k ← readNat
    pure (.leaf id frame (.flip (fin12 k)))
  else
    let h ← readNat
    pure (.leaf id frame (.handoff (handoffOf h)))

def readTable : Decoder Table := do
  let count ← readNat
  let rows ← readList readNode count []
  let arr := rows.toArray
  pure { get := fun i => arr[i]!, size := count }

def decodeTables (packed : String) : Array Table :=
  (readList readTable 86 [] { data := packed.toUTF8 }).1.toArray

/-! ## Format v2: shared fact rows

Each table starts with its fact rows (`factCount`, then per fact a frame and a
triple), followed by `count` nodes.  Node tag `6 id frame fact split shift` is a
`Leaf.shared` certificate whose triple is the fact's. -/

def dummyTriple : Triple := ⟨fun _ _ => 0, ![0, 0, 0], ![0, 0, 0]⟩

def readFact : Decoder Row := do
  let frame ← readFrame
  let triple ← readTriple
  pure ⟨frame.seg, frame.kind, frame.center, frame.radius, triple, [], [], frame.aff⟩

def readNodeV2 (facts : Array Row) : Decoder Node := do
  let tag ← readNat
  if tag = 6 then
    let id ← readNat
    let frame ← readFrame
    let k ← readNat
    let split ← readSplit
    let n ← readNat
    let shift ← readList readRat n []
    let triple := match facts[k]? with
      | some f => f.triple
      | none => dummyTriple
    pure (.leaf id frame (.shared ⟨frame.seg, frame.kind, frame.center, frame.radius,
      triple, split, shift, frame.aff⟩ k))
  else
    -- reuse the v1 decoder for the other tags: rewind over the tag
    fun cursor => readNode { cursor with pos := cursor.pos - tagWidth tag }
where
  /-- Bytes taken by the decimal tag and its separator. -/
  tagWidth (tag : Nat) : Nat := (toString tag).length + 1

def readTableV2 : Decoder Table := do
  let factCount ← readNat
  let facts ← readList readFact factCount []
  let factArr := facts.toArray
  let count ← readNat
  let rows ← readList (readNodeV2 factArr) count []
  let arr := rows.toArray
  pure { get := fun i => arr[i]!, size := count, facts := factArr }

def decodeTablesV2 (packed : String) : Array Table :=
  (readList readTableV2 86 [] { data := packed.toUTF8 }).1.toArray

/-! ## Format v3: fact polynomials and kernel-friendly shared leaves

After the fact rows, each table lists one `CornerKernel.FactPoly` per fact:
`termCount`, then per term `len e₀ … e_{len-1} |c| neg`; then the monomial
`m` (`len e…`) and `K`.  Node tag `7 id frame fact split shift` is a
`Leaf.sharedP` leaf. -/

def readMono : Decoder (List ℕ) := do
  let n ← readNat
  readList readNat n []

def readFactPoly : Decoder CornerKernel.FactPoly := do
  let n ← readNat
  let S ← readList (do
    let m ← readMono
    let c ← readNat
    let neg ← readNat
    pure (m, c, neg == 1)) n []
  let m ← readMono
  let K ← readNat
  pure ⟨S, m, K⟩

def readNodeV3 (facts : Array Row) : Decoder Node := do
  let tag ← readNat
  if tag = 7 then
    let id ← readNat
    let frame ← readFrame
    let k ← readNat
    let split ← readSplit
    let n ← readNat
    let shift ← readList readRat n []
    let triple := match facts[k]? with
      | some f => f.triple
      | none => dummyTriple
    pure (.leaf id frame (.sharedP ⟨frame.seg, frame.kind, frame.center, frame.radius,
      triple, split, shift, frame.aff⟩ k))
  else
    fun cursor => readNodeV2 facts { cursor with pos := cursor.pos - tagWidth tag }
where
  tagWidth (tag : Nat) : Nat := (toString tag).length + 1

def readTableV3 : Decoder Table := do
  let factCount ← readNat
  let facts ← readList readFact factCount []
  let factArr := facts.toArray
  let fps ← readList readFactPoly factCount []
  let count ← readNat
  let rows ← readList (readNodeV3 factArr) count []
  let arr := rows.toArray
  pure { get := fun i => arr[i]!, size := count, facts := factArr, fpolys := fps.toArray }

def decodeTablesV3 (packed : String) : Array Table :=
  (readList readTableV3 86 [] { data := packed.toUTF8 }).1.toArray

def tablesOf (arr : Array Table) : Tables where
  plain seg face := arr[(if seg then 18 else 0) + face.val]!
  tube seg face := arr[(if seg then 18 else 0) + 7 + face.val]!
  wedge seg := arr[(if seg then 18 else 0) + 13]!
  wtube seg face := arr[(if seg then 18 else 0) + 14 + face.val]!
  skew := arr[36]!
  zero face := arr[37 + face.val]!
  cone neg := arr[43 + (if neg 0 then 1 else 0) + (if neg 1 then 2 else 0) +
    (if neg 2 then 4 else 0) + (if neg 3 then 8 else 0)]!
  pocket k m := arr[59 + 3 * k.val + m.val]!
  spocket m := arr[68 + m.val]!
  ppocket k m := arr[(if k.val < 2 then 71 + 3 * k.val else 83) + m.val]!
  tpocket face m := arr[77 + 3 * face.val + m.val]!

end Noperts.Stellated.PackedCornerTree

end
