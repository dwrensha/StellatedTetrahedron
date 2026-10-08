module

public import Noperts.Stellated.AtlasProjectiveLocalViewTree

@[expose] public section

/-!
# Packed native certificates for the Nopert #214 local view tree

Large generated local certificates contain very little repeated axis data.
Representing every integer in that data as a separate Lean declaration makes
elaboration and code generation dominate the actual certificate check.  This
module provides a deliberately small total decoder for comma-separated natural
numbers.  Generated native-only modules can therefore contain one string
literal; `native_decide` still checks the fully decoded exact rational table.

A triangle is a path from the table's base triangle: steps `0..3` are
midpoint children and step `4 + k` (followed by three rational weights) is
child `k` of a cut.  Row tag `0` is a midpoint split, `1` a certificate and
`2` a cut (three children, then the three weights).

Signed rational numerators use zig-zag coding: `z >= 0` is encoded as `2*z`,
and `z < 0` as `-2*z-1`.
-/

namespace Noperts.Stellated.PackedLocalViewTree

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open AtlasProjectiveLocalViewTree
open Noperts.ProjectiveView

structure Cursor where
  data : ByteArray
  pos : Nat := 0

def readNatAux (data : ByteArray) (pos acc fuel : Nat) : Nat × Nat :=
  match fuel with
  | 0 => (acc, pos)
  | fuel + 1 =>
      if h : pos < data.size then
        let value := (data[pos]).toNat
        if 48 ≤ value ∧ value ≤ 57 then
          readNatAux data (pos + 1) (10 * acc + value - 48) fuel
        else
          (acc, pos + 1)
      else
        (acc, pos)

def Cursor.readNat (cursor : Cursor) : Nat × Cursor :=
  let result := readNatAux cursor.data cursor.pos 0
    (cursor.data.size - cursor.pos)
  (result.1, { cursor with pos := result.2 })

abbrev Decoder := StateM Cursor

def readNat : Decoder Nat := fun cursor => cursor.readNat

def fin3 (n : Nat) : Fin 3 := ⟨n % 3, by omega⟩
def fin4 (n : Nat) : Fin 4 := ⟨n % 4, by omega⟩
def fin5 (n : Nat) : Fin 5 := ⟨n % 5, by omega⟩
def fin8 (n : Nat) : Fin 8 := ⟨n % 8, by omega⟩
def fin8v (n : Nat) : Fin 8 := ⟨n % 8, by omega⟩
def fin12 (n : Nat) : Fin 12 := ⟨n % 12, by omega⟩
def fin64 (n : Nat) : Fin 64 := ⟨n % 64, by omega⟩
def fin1001 (n : Nat) : Fin 1001 := ⟨n % 1001, by omega⟩

def zigzagInt (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

def readRat : Decoder Rat := do
  let numerator ← readNat
  let denominator ← readNat
  pure ((((zigzagInt numerator : Int) : Rat) / (denominator : Rat)) : Rat)

def readVertices : Decoder (Fin 3 → VertexIndex) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![fin8v a, fin8v b, fin8v c]

def readMix : Decoder (Fin 3 → Fin 1001) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![fin1001 a, fin1001 b, fin1001 c]

def readAxis : Decoder AxisCertificate := do
  let edgeStart ← readVertices
  let edgeFinish ← readVertices
  let edgeStart₂ ← readVertices
  let edgeFinish₂ ← readVertices
  let mix ← readMix
  let index ← readVertices
  let nonzeroWitness ← readVertices
  let B ← readRat
  pure {
    edgeStart := edgeStart
    edgeFinish := edgeFinish
    edgeStart₂ := edgeStart₂
    edgeFinish₂ := edgeFinish₂
    mix := mix
    index := index
    nonzeroWitness := nonzeroWitness
    B := B }

def readCertificate : Decoder (Fin 4 → AxisCertificate) := do
  let a ← readAxis
  let b ← readAxis
  let c ← readAxis
  let d ← readAxis
  pure ![a, b, c, d]

/-! Triangles are decoded as arrays of their nine coordinates (`3 i + c`),
applying the same midpoint / cut formulas as `split` and `cutTriangle`; only
the finished triangle is wrapped as a function.  Building them as chains of
closures made each coordinate access re-evaluate the whole path (about `2^d`
work at depth `d`, ~13 s per depth-16 row in the native check), and the
compiler floats cached `let`s back into such closures.  The checker verifies
every decoded triangle against its parent, so this changes performance only. -/

@[noinline] def triangleArray (t : AtlasProjectiveView.Triangle Rat) : Array Rat :=
  #[t 0 0, t 0 1, t 0 2, t 1 0, t 1 1, t 1 2, t 2 0, t 2 1, t 2 2]

@[noinline] def triangleOfArray (arr : Array Rat) : AtlasProjectiveView.Triangle Rat :=
  fun i j => arr.getD (3 * i.val + j.val) 0

def mid (t : Array Rat) (i j c : Nat) : Rat :=
  (t.getD (3 * i + c) 0 + t.getD (3 * j + c) 0) / 2

/-- `split` on coordinate arrays. -/
def splitArray (t : Array Rat) (child : Nat) : Array Rat :=
  let g := fun i c => t.getD (3 * i + c) 0
  let m01 := #[mid t 0 1 0, mid t 0 1 1, mid t 0 1 2]
  let m02 := #[mid t 0 2 0, mid t 0 2 1, mid t 0 2 2]
  let m12 := #[mid t 1 2 0, mid t 1 2 1, mid t 1 2 2]
  let m20 := #[mid t 2 0 0, mid t 2 0 1, mid t 2 0 2]
  let v0 := #[g 0 0, g 0 1, g 0 2]
  let v1 := #[g 1 0, g 1 1, g 1 2]
  let v2 := #[g 2 0, g 2 1, g 2 2]
  match child with
  | 0 => v0 ++ m01 ++ m02
  | 1 => m01 ++ v1 ++ m12
  | 2 => m02 ++ m12 ++ v2
  | _ => m01 ++ m12 ++ m20

/-- `cutTriangle` on coordinate arrays. -/
def cutArray (t : Array Rat) (w0 w1 w2 : Rat) (k : Nat) : Array Rat :=
  let g := fun i c => t.getD (3 * i + c) 0
  let p := #[w0 * g 0 0 + w1 * g 1 0 + w2 * g 2 0, w0 * g 0 1 + w1 * g 1 1 + w2 * g 2 1,
    w0 * g 0 2 + w1 * g 1 2 + w2 * g 2 2]
  let row := fun i => if i = k then p else #[g i 0, g i 1, g i 2]
  row 0 ++ row 1 ++ row 2

def readTrianglePath : Nat → Array Rat → Decoder (Array Rat)
  | 0, triangle => pure triangle
  | length + 1, triangle => do
      let child ← readNat
      if child < 4 then
        readTrianglePath length (splitArray triangle child)
      else
        let a ← readRat
        let b ← readRat
        let c ← readRat
        readTrianglePath length (cutArray triangle a b c ((child - 4) % 3))

def readTriangle (base : Array Rat) : Decoder (AtlasProjectiveView.Triangle Rat) := do
  let length ← readNat
  let arr ← readTrianglePath length base
  pure (triangleOfArray arr)

def readRow (base : Array Rat) : Decoder Row := do
  let tag ← readNat
  let id ← readNat
  let root ← readNat
  let triangle ← readTriangle base
  if tag = 0 then
    let a ← readNat
    let b ← readNat
    let c ← readNat
    let d ← readNat
    pure (.split id ![a, b, c, d] (fin8 root) triangle)
  else if tag = 2 then
    let a ← readNat
    let b ← readNat
    let c ← readNat
    let wa ← readRat
    let wb ← readRat
    let wc ← readRat
    pure (.cut id ![a, b, c] (fin8 root) triangle ![wa, wb, wc])
  else
    let symmetryIndex ← readNat
    let certificate ← readCertificate
    let c ← readRat
    let δ ← readRat
    let r ← readRat
    pure (.certificate id {
      interval := AtlasPose.rootInterval Rat
      root := fin8 root
      triangle
      chart := 0
      symmetryIndex := fin12 symmetryIndex
      certificate
      c
      δ
      r })

def readRows (base : Array Rat) :
    Nat → Array Row → Decoder (Array Row)
  | 0, rows => pure rows
  | count + 1, rows => do
      let row ← readRow base
      readRows base count (rows.push row)

def decodeRows (base : AtlasProjectiveView.Triangle Rat)
    (count : Nat) (packed : String) : Array Row :=
  (readRows (triangleArray base) count #[] { data := packed.toUTF8 }).1

/-- The depth-3 chamber subtriangle with index `16 a + 4 b + c`. -/
def depth3Triangle (index : Nat) : AtlasProjectiveView.Triangle Rat :=
  split (split (split chamberTriangle (fin4 (index / 16)))
    (fin4 (index / 4 % 4))) (fin4 (index % 4))

def decodeTable (tableIndex symmetryIndex : Nat) (r : Rat)
    (count : Nat) (packed : String) : Table :=
  let base := depth3Triangle tableIndex
  let rows := decodeRows base count packed
  {
    symmetryIndex := fin12 symmetryIndex
    r
    root := 0
    triangle := base
    get := fun i => rows[i]!
    size := count
  }

structure Decoded where
  symmetryIndex : Nat
  r : Rat
  count : Nat
  rows : Array Row

def readDecoded (base : AtlasProjectiveView.Triangle Rat) :
    Decoder Decoded := do
  let count ← readNat
  let symmetryIndex ← readNat
  let r ← readRat
  let rows ← readRows (triangleArray base) count #[]
  pure { symmetryIndex, r, count, rows }

/-- Decode a self-describing packed local-table artifact.  Its root triangle is
the depth-3 chamber subtriangle given by its table index. -/
def decodePackedTable (tableIndex : Nat) (packed : String) : Table :=
  let base := depth3Triangle tableIndex
  let decoded :=
    (readDecoded base { data := packed.toUTF8 }).1
  {
    symmetryIndex := fin12 decoded.symmetryIndex
    r := decoded.r
    root := 0
    triangle := base
    get := fun i => decoded.rows[i]!
    size := decoded.count
  }

end Noperts.Stellated.PackedLocalViewTree

end
