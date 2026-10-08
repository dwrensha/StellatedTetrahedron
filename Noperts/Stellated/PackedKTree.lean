module

public import Noperts.Stellated.CornerKernelTree
public import Noperts.Stellated.PackedCornerTree

@[expose] public section

/-!
# Packed integer-frame corner trees

A comma-separated stream of naturals (integers zig-zag encoded).  A chunk file
holds `count` chunks, each `id frame tree`:

* frame: `seg kind n D X₀ … X_{n-1} H₀ … H_{n-1}`;
* tree, in prefix order:
  `0 v M s lo hi` split; `1 n k₁ … kₙ t` anchor; `2 k` kernel shared leaf;
  `3 k` flip; `4 h` hand-off; `5 k split shift triple` shared leaf; `8 k` cheap-bound flip;
  `6 split shift triple` certificate; `7` hole (at the current frame).

Leaves that carry a `Row` take its box from the current frame (`IFrame.toFrame`).
-/

namespace Noperts.Stellated.PackedKTree

open PackedLocalViewTree PackedCornerTree CornerCertificate CornerTree CornerKernel

instance : Inhabited KTree := ⟨.leafP 0⟩

def unzig (n : ℕ) : ℤ := if n % 2 = 0 then (n / 2 : ℕ) else -(((n + 1) / 2 : ℕ) : ℤ)

def readInt : Decoder ℤ := do return unzig (← readNat)

def readIFrame : Decoder IFrame := do
  let seg ← readNat
  let kind ← readNat
  let n ← readNat
  let D ← readNat
  let X ← readList readInt n []
  let H ← readList readInt n []
  pure ⟨seg = 1, kindOf kind, D, X, H⟩

def readShift : Decoder (List ℚ) := do
  let n ← readNat
  readList readRat n []

def frameRow (f : IFrame) (triple : Triple) (split : List (ℕ × Bool)) (shift : List ℚ) : Row :=
  let F := f.toFrame
  ⟨F.seg, F.kind, F.center, F.radius, triple, split, shift, []⟩

partial def readKTree (f : IFrame) : Decoder KTree := do
  let tag ← readNat
  if tag = 0 then
    let v ← readNat
    let M ← readInt
    let s ← readNat
    let lo ← readKTree (f.child v M s false).reduce
    let hi ← readKTree (f.child v M s true).reduce
    pure (.split v M s lo hi)
  else if tag = 1 then
    let n ← readNat
    let ks ← readList readNat n []
    let t ← readKTree f
    pure (.anchor ks t)
  else if tag = 2 then
    pure (.leafP (← readNat))
  else if tag = 3 then
    pure (.leaf (.flip (fin12 (← readNat))))
  else if tag = 4 then
    pure (.leaf (.handoff (handoffOf (← readNat))))
  else if tag = 5 then
    let k ← readNat
    let split ← readSplit
    let shift ← readShift
    let triple ← readTriple
    pure (.leaf (.shared (frameRow f triple split shift) k))
  else if tag = 8 then
    pure (.flipP (fin12 (← readNat)))
  else if tag = 6 then
    let split ← readSplit
    let shift ← readShift
    let triple ← readTriple
    pure (.leaf (.cert (frameRow f triple split shift)))
  else
    pure (.hole f)

def readChunk : Decoder (ℕ × IFrame × KTree) := do
  let id ← readNat
  let f ← readIFrame
  let t ← readKTree f
  pure (id, f, t)

def decodeChunks (packed : String) : Array (ℕ × IFrame × KTree) :=
  (do let n ← readNat; readList readChunk n [] : Decoder _) { data := packed.toUTF8 } |>.1.toArray

end Noperts.Stellated.PackedKTree
