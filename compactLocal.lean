import Noperts.Stellated.NativeExecutable

/-!
Compact a packed local-view table: walking the tree bottom-up, a split or cut
node whose children are all certificate leaves is replaced by a single leaf
when one of the children's certificates, with `B` and `δ` re-tuned (and rounded
up to short decimals), certifies the parent triangle.  Every decision uses the
exact `Box.ViewValid` checker, and the rewritten table is re-validated with
`localTableValidParB` before it is written.

`compactLocal IN.pack OUT.pack TABLE`
-/

open Noperts.Stellated
open Noperts.Stellated.AtlasProjectiveLocalViewTree
open Noperts.Stellated.AtlasProjectiveLocalCertificate
open Noperts.Stellated.PackedLocalViewTree

/-- Round `q > 0` up to about ten significant decimal digits. -/
def roundUp (q : ℚ) : ℚ :=
  if q ≤ 0 then q else
  -- find k with 10^9 ≤ q · 10^k < 10^10
  let rec go (k : Int) (fuel : Nat) : Int :=
    match fuel with
    | 0 => k
    | fuel + 1 =>
      let s := q * (10 : ℚ) ^ k
      if s < 1000000000 then go (k + 1) fuel
      else if s ≥ 10000000000 then go (k - 1) fuel
      else k
  let k := go 0 200
  let s := q * (10 : ℚ) ^ k
  (⌈s⌉ : ℚ) / (10 : ℚ) ^ k

/-- The child's certificate retuned for a parent triangle. -/
def retune (b0 : Box) (tri : AtlasProjectiveView.Triangle ℚ) : Box :=
  let b : Box := { b0 with triangle := tri }
  let Bs : Fin 4 → ℚ := fun j => roundUp (max (b.certificate j).B (b.weightBudget j))
  let certs : Array AxisCertificate :=
    #[{ b.certificate 0 with B := Bs 0 }, { b.certificate 1 with B := Bs 1 },
      { b.certificate 2 with B := Bs 2 }, { b.certificate 3 with B := Bs 3 }]
  let b : Box := { b with certificate := fun j => certs.getD j.val (b.certificate j) }
  let δ := (List.finRange 4).foldl (fun acc j =>
    max acc ((b.variationRadiusSum j + 3 * variationError) / (b.certificate j).B)) (0 : ℚ)
  { b with δ := roundUp δ }

/-! ## Pack writer (inverse of `PackedLocalViewTree.readRow`) -/

def zig (z : Int) : Nat := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

def ratToks (q : ℚ) : Array Nat := #[zig q.num, q.den]

def vertsToks (f : Fin 3 → VertexIndex) : Array Nat := #[(f 0).val, (f 1).val, (f 2).val]

def axisToks (a : AxisCertificate) : Array Nat :=
  vertsToks a.edgeStart ++ vertsToks a.edgeFinish ++ vertsToks a.edgeStart₂ ++
    vertsToks a.edgeFinish₂ ++ #[(a.mix 0).val, (a.mix 1).val, (a.mix 2).val] ++
    vertsToks a.index ++ vertsToks a.nonzeroWitness ++ ratToks a.B

/-- A path step from a parent: midpoint child `c`, or cut child `k` with weights. -/
inductive Step where
  | split (c : Nat)
  | cut (k : Nat) (w : Array ℚ)

def stepToks : Step → Array Nat
  | .split c => #[c]
  | .cut k w => #[4 + k] ++ ratToks w[0]! ++ ratToks w[1]! ++ ratToks w[2]!

structure Out where
  toks : Array Nat := #[]
  count : Nat := 0

def main (args : List String) : IO Unit := do
  let (inPath, outPath, index) ← match args with
    | [i, o, t] => pure (i, o, t.toNat!)
    | _ => throw (IO.userError "expects IN.pack OUT.pack TABLE")
  let data ← IO.FS.readFile inPath
  let table := decodePackedTable index data
  let n := table.size
  let rows : Array Row := (List.range n).toArray.map table.get
  -- bottom-up: children have larger ids
  let mut leaf : Array (Option Box) := Array.replicate n none
  let mut merged := 0
  for i' in List.range n do
    let i := n - 1 - i'
    match rows[i]! with
    | .certificate _ b => leaf := leaf.set! i (some b)
    | .split _ children _ tri =>
        let kids := (List.finRange 4).map fun c => leaf[children c]!
        if kids.all Option.isSome then
          let cands := kids.filterMap id
          match cands.find? (fun b => (retune b tri).viewFastB) with
          | some b => leaf := leaf.set! i (some (retune b tri)); merged := merged + 1
          | none => pure ()
    | .cut _ children _ tri weights =>
        let live := (List.finRange 3).filter fun k => 0 < weights k
        let kids := live.map fun k => leaf[children k]!
        if kids.all Option.isSome then
          let cands := kids.filterMap id
          match cands.find? (fun b => (retune b tri).viewFastB) with
          | some b => leaf := leaf.set! i (some (retune b tri)); merged := merged + 1
          | none => pure ()
  IO.println s!"table {index}: {n} rows, {merged} nodes became leaves"
  -- re-emit in BFS order from the root, stopping at leaves
  let sym := table.symmetryIndex.val
  let mut order : Array (Nat × Array Step) := #[(0, #[])]   -- (old id, path)
  let mut qi := 0
  let mut newId : Array Nat := Array.replicate n 0
  while qi < order.size do
    let (i, path) := order[qi]!
    newId := newId.set! i qi
    qi := qi + 1
    if leaf[i]!.isNone then
      match rows[i]! with
      | .split _ children _ _ =>
          for c in List.finRange 4 do
            order := order.push (children c, path.push (.split c.val))
      | .cut _ children _ _ weights =>
          for k in List.finRange 3 do
            if 0 < weights k then
              order := order.push (children k,
                path.push (.cut k.val #[weights 0, weights 1, weights 2]))
      | .certificate .. => pure ()
  let mut out : Array Nat := #[order.size, sym] ++ ratToks table.r
  for (i, path) in order do
    let pathToks := path.foldl (fun acc s => acc ++ stepToks s) #[path.size]
    match leaf[i]! with
    | some b =>
        out := out ++ #[1, newId[i]!, b.root.val] ++ pathToks ++ #[b.symmetryIndex.val] ++
          axisToks (b.certificate 0) ++ axisToks (b.certificate 1) ++
          axisToks (b.certificate 2) ++ axisToks (b.certificate 3) ++
          ratToks b.c ++ ratToks b.δ ++ ratToks b.r
    | none =>
        match rows[i]! with
        | .split _ children root _ =>
            out := out ++ #[0, newId[i]!, root.val] ++ pathToks ++
              ((List.finRange 4).map fun c => newId[children c]!).toArray
        | .cut _ children root _ weights =>
            out := out ++ #[2, newId[i]!, root.val] ++ pathToks ++
              ((List.finRange 3).map fun k =>
                if 0 < weights k then newId[children k]! else 0).toArray ++
              ratToks (weights 0) ++ ratToks (weights 1) ++ ratToks (weights 2)
        | .certificate .. => pure ()
  let text := ",".intercalate (out.toList.map toString) ++ ","
  -- validate the rewritten table before writing it
  let newTable := decodePackedTable index text
  IO.println s!"new table: {newTable.size} rows ({n - newTable.size} fewer)"
  unless NativeExecutable.localTableValidParB newTable 16 do
    throw (IO.userError "rewritten table is NOT valid; not writing")
  IO.FS.writeFile outPath text
  IO.println s!"valid; wrote {outPath}"
