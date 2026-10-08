import Noperts.Stellated.NativeExecutable
import Noperts.Stellated.PackedCornerTree

/-!
Rewrite `corner.pack` (format v1) into format v2 with shared fact rows: in
each table whose root frame has no affine reparametrization, the distinct
triples of its certificate rows become fact rows checked once on the root
frame (`Row.KeyFacts`), and each certificate row that passes
`Row.SharedValid` against its fact is re-emitted as a `Leaf.shared` node, which
checks only the radius and displacement conditions on its own box.  The
result is validated with the same `Tables.ValidPar` check the proof uses
before it is written.

`shareCorner IN.pack OUT.pack`
-/

open Noperts.Stellated
open Noperts.Stellated.CornerTree CornerCertificate CornerPoly PackedCornerTree

def zig (z : Int) : Nat := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

def ratT (q : ℚ) : Array Nat := #[zig q.num, q.den]

def kindCode : ChartKind → Nat
  | .plain => 0 | .tube => 1 | .wedge => 2 | .wtube => 3 | .skew => 4 | .atube => 5
  | .btube false => 6 | .btube true => 7 | .askew => 8 | .bskew false => 9
  | .bskew true => 10 | .aplain => 11 | .bplain false => 12 | .bplain true => 13

def handoffCode : Handoff → Nat
  | .tube => 0 | .wedge => 1 | .wtube => 2 | .skew => 3 | .cone => 4 | .pocket => 5
  | .spocket => 6 | .ppocket => 7 | .cpocket => 8

def frameT (f : Frame) : Array Nat :=
  #[if f.seg then 1 else 0, kindCode f.kind, f.center.length] ++
    (f.center.foldl (fun a q => a ++ ratT q) #[]) ++
    (f.radius.foldl (fun a q => a ++ ratT q) #[]) ++ #[f.aff.length] ++
    (f.aff.foldl (fun a row => row.foldl (fun b q => b ++ ratT q) a) #[])

def tripleT (t : Triple) : Array Nat :=
  ((List.range 9).foldl (fun a n =>
      a ++ ratT (t.edge ⟨n / 3 % 3, by omega⟩ ⟨n % 3, by omega⟩)) #[]) ++
    #[(t.inner 0).val, (t.inner 1).val, (t.inner 2).val,
      (t.outer 0).val, (t.outer 1).val, (t.outer 2).val]

def splitT (sp : List (ℕ × Bool)) : Array Nat :=
  sp.foldl (fun a p => a ++ #[p.1, if p.2 then 1 else 0]) #[sp.length]

def shiftT (sh : List ℚ) : Array Nat := sh.foldl (fun a q => a ++ ratT q) #[sh.length]

def nodeT (facts : Std.HashMap (Bool × Nat × Array Nat) Nat) (factRows : Array Row)
    (n : Node) : Array Nat × Bool :=
  match n with
  | .split id f v m lo hi => (#[0, id] ++ frameT f ++ #[v] ++ ratT m ++ #[lo, hi], false)
  | .stellar id f i j α β lo hi =>
      (#[5, id] ++ frameT f ++ #[i, j] ++ ratT α ++ ratT β ++ #[lo, hi], false)
  | .leaf id f (.flip k) => (#[2, id] ++ frameT f ++ #[k.val], false)
  | .leaf id f (.handoff h) => (#[3, id] ++ frameT f ++ #[handoffCode h], false)
  | .leaf id f (.shared r k) =>
      (#[6, id] ++ frameT f ++ #[k] ++ splitT r.split ++ shiftT r.shift, true)
  | .leaf id f (.sharedP r k) =>
      (#[7, id] ++ frameT f ++ #[k] ++ splitT r.split ++ shiftT r.shift, true)
  | .leaf id f (.cert r) =>
      let plain := if r.shift.isEmpty then
          #[1, id] ++ frameT f ++ tripleT r.triple ++ splitT r.split
        else #[4, id] ++ frameT f ++ tripleT r.triple ++ splitT r.split ++ shiftT r.shift
      if r.aff.isEmpty then
        match facts.get? (r.seg, kindCode r.kind, tripleT r.triple) with
        | some k =>
            if (factRows[k]?.map fun fr => decide (r.SharedValid fr)).getD false then
              (#[6, id] ++ frameT f ++ #[k] ++ splitT r.split ++ shiftT r.shift, true)
            else (plain, false)
        | none => (plain, false)
      else (plain, false)

/-- Write nodes `[lo, hi)` of table `index` of a v2 pack, with that table's facts,
as a one-table v2 file (node ids unchanged). -/
def slice (inPath outPath : String) (index lo hi : Nat) : IO Unit := do
  let tables := decodeTablesV2 (← IO.FS.readFile inPath)
  let t := tables[index]!
  let mut out : Array Nat := #[t.facts.size]
  for f in t.facts do
    out := out ++ frameT ⟨f.seg, f.kind, f.center, f.radius, f.aff⟩ ++ tripleT f.triple
  out := out.push (hi - lo)
  for k in List.range (hi - lo) do
    out := out ++ (nodeT {} #[] (t.get (lo + k))).1
  IO.FS.writeFile outPath (",".intercalate (out.toList.map toString) ++ ",")
  IO.println s!"wrote {hi - lo} nodes and {t.facts.size} facts of table {index}"

def main (args : List String) : IO Unit := do
  if let ["slice", i, o, t, lo, hi] := args then
    slice i o t.toNat! lo.toNat! hi.toNat!
    return
  let (inPath, outPath) ← match args with
    | [i, o] => pure (i, o)
    | _ => throw (IO.userError "expects IN.pack OUT.pack")
  let data ← IO.FS.readFile inPath
  let tables := decodeTables data
  let mut out : Array Nat := #[]
  let mut totShared := 0
  let mut totFacts := 0
  for index in List.range 86 do
    let t := tables[index]!
    let root := (t.get 0).frame
    -- candidate facts: distinct triples of aff-free certificate rows
    let mut facts : Std.HashMap (Bool × Nat × Array Nat) Nat := {}
    let mut factRows : Array Row := #[]
    if root.aff.isEmpty then
      let mut seen : Std.HashSet (Bool × Nat × Array Nat) := {}
      for k in List.range t.size do
        if let .leaf _ _ (.cert r) := t.get k then
          let key := (r.seg, kindCode r.kind, tripleT r.triple)
          if r.aff.isEmpty && r.seg == root.seg && r.kind == root.kind && !seen.contains key then
            seen := seen.insert key
            let fact : Row := ⟨root.seg, root.kind, root.center, root.radius, r.triple, [], [], []⟩
            if decide fact.KeyFacts then
              facts := facts.insert key factRows.size
              factRows := factRows.push fact
    out := out.push factRows.size
    for f in factRows do
      out := out ++ frameT ⟨f.seg, f.kind, f.center, f.radius, f.aff⟩ ++ tripleT f.triple
    out := out.push t.size
    let mut shared := 0
    for k in List.range t.size do
      let (toks, sh) := nodeT facts factRows (t.get k)
      out := out ++ toks
      if sh then shared := shared + 1
    totShared := totShared + shared
    totFacts := totFacts + factRows.size
    if t.size > 10000 then
      IO.println s!"table {index}: {t.size} rows, {factRows.size} facts, {shared} shared leaves"
      (← IO.getStdout).flush
  IO.println s!"total: {totFacts} facts, {totShared} shared leaves"
  let text := ",".intercalate (out.toList.map toString) ++ ","
  let newTables := decodeTablesV2 text
  let start ← IO.monoNanosNow
  unless decide ((tablesOf newTables).ValidPar AtlasProjectiveSolutionTree.cornerEps 16) do
    throw (IO.userError "rewritten corner tables are NOT valid; not writing")
  let finish ← IO.monoNanosNow
  IO.println s!"valid (check {(finish - start) / 1000000} ms); writing {outPath}"
  IO.FS.writeFile outPath text
