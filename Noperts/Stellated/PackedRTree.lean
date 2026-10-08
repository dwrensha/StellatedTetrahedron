module

public import Noperts.Stellated.CornerAffTree
public import Noperts.Stellated.PackedCornerTree

@[expose] public section

/-! Decoder for packed reparametrized corner trees (format: `KernelLoadAff`). -/

namespace Noperts.Stellated.PackedRTree

open PackedLocalViewTree PackedCornerTree CornerTree CornerCertificate CornerAff

instance : Inhabited RTree := ⟨.leaf (.flip 0)⟩

def readShiftR : Decoder (List ℚ) := do
  let n ← readNat
  readList readRat n []

partial def readRTree : Decoder RTree := do
  let tag ← readNat
  match tag with
  | 0 =>
      let v ← readNat
      let m ← readRat
      let lo ← readRTree
      let hi ← readRTree
      pure (.split v m lo hi)
  | 1 =>
      let i ← readNat
      let j ← readNat
      let α ← readRat
      let β ← readRat
      let lo ← readRTree
      let hi ← readRTree
      pure (.stellar i j α β lo hi)
  | 2 => pure (.leaf (.flip (fin12 (← readNat))))
  | 3 => pure (.leaf (.handoff (handoffOf (← readNat))))
  | 4 =>
      let triple ← readTriple
      let split ← readSplit
      let shift ← readShiftR
      pure (.leaf (.cert ⟨false, .plain, [], [], triple, split, shift, []⟩))
  | 5 =>
      let triple ← readTriple
      let split ← readSplit
      let shift ← readShiftR
      let k ← readNat
      pure (.sharedPA triple split shift k)
  | _ => pure (.hole (← readFrame))

/-- Certificate leaves carry their frame implicitly; fill it in. -/
partial def fillCert : Frame → RTree → RTree
  | f, .split v m lo hi => .split v m (fillCert (f.lower v m) lo) (fillCert (f.upper v m) hi)
  | f, .stellar i j α β lo hi =>
      .stellar i j α β (fillCert (f.stellar i j α β) lo) (fillCert (f.stellar j i β α) hi)
  | f, .leaf (.cert r) =>
      .leaf (.cert ⟨f.seg, f.kind, f.center, f.radius, r.triple, r.split, r.shift, f.aff⟩)
  | _, t => t

def readChunk : Decoder (ℕ × Frame × RTree) := do
  let id ← readNat
  let f ← readFrame
  let t ← readRTree
  pure (id, f, fillCert f t)

def decodeChunks (packed : String) : Array (ℕ × Frame × RTree) :=
  (do let n ← readNat; readList readChunk n [] : Decoder _) { data := packed.toUTF8 } |>.1.toArray

end Noperts.Stellated.PackedRTree
