import Noperts.Stellated.PackedCornerTree

/-!
Profiling aid (not part of the proof): times each conjunct of
`CornerCertificate.Row.Valid` on certificate rows of one corner table, plus
whole-row checks of every node kind.  `benchCornerRow corner.pack TABLE NROWS`.
-/

open Noperts.Stellated
open Noperts.Stellated.CornerTree CornerCertificate CornerPoly PackedCornerTree
open SparsePoly

def timeIt (label : String) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let ok ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / 1000000} ms ({ok})"
  (← IO.getStdout).flush

def sweep (path : String) (nrows : Nat) : IO Unit := do
  let data ← IO.FS.readFile path
  let tables := decodeTables data
  let mut totalMs : Float := 0
  for index in List.range 86 do
    let t := tables[index]!
    let mut certs : Array Row := #[]
    for k in List.range t.size do
      match t.get k with
      | .leaf _ _ (.cert r) => certs := certs.push r
      | _ => pure ()
    let stride := max 1 (certs.size / max 1 nrows)
    let sample : List Row := (List.range (min nrows certs.size)).filterMap fun j => certs[j * stride]?
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => sample.all fun r => decide r.Valid
    let t1 ← IO.monoNanosNow
    let per : Float := (t1 - t0).toFloat / 1e6 / (max 1 sample.length).toFloat
    let est := per * certs.size.toFloat
    totalMs := totalMs + est
    IO.println s!"table {index}: {certs.size} certs, {per} ms/row, est {est / 1000} s ({ok})"
    (← IO.getStdout).flush
  IO.println s!"estimated corner cert total: {totalMs / 3.6e6} CPU-hours"

/-- Over-split probe: split/stellar nodes whose two children are certificate
leaves, and whether a child's certificate already certifies the parent frame. -/
def overprobe (path : String) : IO Unit := do
  let data ← IO.FS.readFile path
  let tables := decodeTables data
  let mut totLeafSplits := 0
  let mut totMerge := 0
  for index in List.range 86 do
    let t := tables[index]!
    let mut leafSplits := 0
    let mut merge := 0
    let mut certs := 0
    for k in List.range t.size do
      let kids : Option (ℕ × ℕ × Frame) := match t.get k with
        | .split _ f _ _ lo hi => some (lo, hi, f)
        | .stellar _ f _ _ _ _ lo hi => some (lo, hi, f)
        | .leaf _ _ (.cert _) => none
        | _ => none
      if let .leaf _ _ (.cert _) := t.get k then certs := certs + 1
      if let some (lo, hi, f) := kids then
        if leafSplits ≥ 3000 then continue
        match t.get lo, t.get hi with
        | .leaf _ _ (.cert r1), .leaf _ _ (.cert r2) =>
            leafSplits := leafSplits + 1
            let try_ := fun (r : Row) =>
              decide ({ r with center := f.center, radius := f.radius, aff := f.aff } : Row).Valid
            if try_ r1 || try_ r2 then merge := merge + 1
        | _, _ => pure ()
    totLeafSplits := totLeafSplits + leafSplits
    totMerge := totMerge + merge
    if certs > 1000 then
      IO.println s!"table {index}: {t.size} rows, {certs} certs, all-leaf splits {leafSplits}, mergeable {merge}"
      (← IO.getStdout).flush
  IO.println s!"TOTAL all-leaf splits {totLeafSplits}, mergeable {totMerge}"

/-- How many per-row gap/weight checks already hold on the table's root frame? -/
def rootprobe (path : String) (index cap : Nat) : IO Unit := do
  let data ← IO.FS.readFile path
  let tables := decodeTables data
  let t := tables[index]!
  let root := (t.get 0).frame
  let mut rows := 0
  let mut gapsRoot := 0
  let mut weightsRoot := 0
  let mut seen := 0
  for k in List.range t.size do
    if let .leaf _ _ (.cert r) := t.get k then
      seen := seen + 1
      if seen % 37 == 0 && rows < cap then
        rows := rows + 1
        let R : Row := { r with center := root.center, radius := root.radius, aff := root.aff }
        for i in List.finRange 3 do
          for kk in List.finRange 8 do
            if decide (NonnegOk R.nonnegVars R.box (scale (-1) (cmp R.aff (gapPoly R.seg R.triple i kk)))) then
              gapsRoot := gapsRoot + 1
          if decide (NonnegOk R.nonnegVars R.box (cmp R.aff (weightPoly R.seg R.triple i))) then
            weightsRoot := weightsRoot + 1
  IO.println s!"table {index}: {rows} sampled rows; gap checks true on root frame {gapsRoot}/{rows * 24}; weight checks {weightsRoot}/{rows * 3}"

/-- Print the displacement parts of a few certificate rows. -/
def showParts (path : String) (index cap : Nat) : IO Unit := do
  let data ← IO.FS.readFile path
  let tables := decodeTables data
  let t := tables[index]!
  let mut shown := 0
  let mut seen := 0
  for k in List.range t.size do
    if let .leaf _ _ (.cert r) := t.get k then
      seen := seen + 1
      if seen % 50000 == 1 && shown < cap then
        shown := shown + 1
        let ps := splitParts (r.split.map Prod.fst) r.G
        IO.println s!"row {k}: kind {repr r.kind} split {r.split} shift {r.shift} box center {r.center} radius {r.radius}"
        IO.println s!"  D: {r.D.length} terms; parts {(ps.2 :: ps.1).map List.length}"
        for q in ps.2 :: ps.1 do
          let mons := (normalize q).map (·.1)
          let maxdeg := (List.range 7).map fun v => (mons.map fun m => m.getD v 0).foldl max 0
          IO.println s!"  part: {q.length} terms, max degree per var (ε λ u a b c ρ) {maxdeg}"

/-! Cheap first-order + absolute-majorant bounds (experiment). -/

def evalQ (x : ℕ → ℚ) (p : Poly) : ℚ :=
  p.foldl (fun acc t => acc + t.2 * ((List.range t.1.length).foldl
    (fun m i => m * x i ^ t.1.getD i 0) 1)) 0

def derivQ (i : ℕ) (p : Poly) : Poly :=
  p.filterMap fun t =>
    let e : ℕ := t.1.getD i 0
    if e = 0 then none else some (t.1.set i (e - 1), t.2 * (e : ℚ))

def absPoly (p : Poly) : Poly := p.map fun t => (t.1, |t.2|)

def nvars (p : Poly) : ℕ := (p.map fun t => t.1.length).foldl max 0

/-- `q ≥ 0` on `[c - r, c + r]` via value and gradient at an anchor `a` with
displacement range `h ∈ [lo_h, hi_h]` (centered: `[-r, r]`; corner: `[0, 2r]`). -/
def cheapBound (q : Poly) (a : ℕ → ℚ) (hlo hhi : ℕ → ℚ) : ℚ :=
  let n := nvars q
  let pa := absPoly q
  let absA : ℕ → ℚ := fun i => |a i|
  let hmax : ℕ → ℚ := fun i => max |hlo i| |hhi i|
  let lin := (List.range n).foldl (fun acc i =>
    let g := evalQ a (derivQ i q)
    acc + min (g * hlo i) (g * hhi i)) 0
  let up : ℕ → ℚ := fun i => absA i + hmax i
  let rem := evalQ up pa - evalQ absA pa -
    (List.range n).foldl (fun acc i => acc + evalQ absA (derivQ i pa) * hmax i) 0
  evalQ a q + lin - rem

def cheapOk (box : Box) (allowed : ℕ → Bool) (q0 : Poly) : Bool :=
  let q := stripped allowed q0
  let c := box.center
  let r := box.radius
  decide (0 ≤ cheapBound q c (fun i => -r i) r) ||
    decide (0 ≤ cheapBound q (fun i => c i - r i) (fun _ => 0) (fun i => 2 * r i))

/-- The crude majorant bound `q(a) + |q|(|a|) - |q|(|a| + hm)`. -/
def crudeBound (q : Poly) (a hm : ℕ → ℚ) : ℚ :=
  let pa := absPoly q
  let absA : ℕ → ℚ := fun i => |a i|
  evalQ a q + evalQ absA pa - evalQ (fun i => absA i + hm i) pa

def crudeOk (box : Box) (allowed : ℕ → Bool) (q0 : Poly) : Bool :=
  let q := stripped allowed q0
  let c := box.center
  let r := box.radius
  decide (0 ≤ crudeBound q c r) || decide (0 ≤ crudeBound q (fun i => c i - r i) (fun i => 2 * r i))

def crudeCenterOk (box : Box) (allowed : ℕ → Bool) (q0 : Poly) : Bool :=
  decide (0 ≤ crudeBound (stripped allowed q0) box.center box.radius)

def cheapprobe (path : String) (index cap : Nat) : IO Unit := do
  let data ← IO.FS.readFile path
  let tables := decodeTables data
  let t := tables[index]!
  let mut rows := 0
  let mut rowsOk := 0
  let mut crude := 0
  let mut crudeC := 0
  let mut seen := 0
  for k in List.range t.size do
    if let .leaf _ _ (.cert r) := t.get k then
      seen := seen + 1
      if seen % 37 == 0 && rows < cap then
        rows := rows + 1
        let ps := splitParts (r.split.map Prod.fst) r.G
        let scaled := (ps.1.zip r.split).map (fun q => scale (signQ q.2.2) q.1)
        let all := ps.2 :: scaled
        if all.all (cheapOk r.sbox r.sbox.nonnegVars) then rowsOk := rowsOk + 1
        if all.all (crudeOk r.sbox r.sbox.nonnegVars) then crude := crude + 1
        if all.all (crudeCenterOk r.sbox r.sbox.nonnegVars) then crudeC := crudeC + 1
  IO.println s!"table {index}: {rows} sampled rows, cheap bound certifies {rowsOk}, crude {crude}, crude-centered {crudeC}"

def main (args : List String) : IO Unit := do
  if let [path, "cheap", t, n] := args then
    cheapprobe path t.toNat! n.toNat!
    return
  if let [path, "parts", t, n] := args then
    showParts path t.toNat! n.toNat!
    return
  if let [path, "rootprobe", t, n] := args then
    rootprobe path t.toNat! n.toNat!
    return
  if let [path, "overprobe"] := args then
    overprobe path
    return
  if let [path, "all", n] := args then
    sweep path n.toNat!
    return
  let (path, index, nrows) ← match args with
    | [p, i, n] => pure (p, i.toNat!, n.toNat!)
    | _ => throw (IO.userError "expects corner.pack TABLE NROWS")
  let data ← IO.FS.readFile path
  let tables := decodeTables data
  let t := tables[index]!
  let mut certCount := 0
  for k in List.range t.size do
    match t.get k with
    | .leaf _ _ (.cert _) => certCount := certCount + 1
    | _ => pure ()
  let stride := max 1 (certCount / max 1 nrows)
  let mut seen := 0
  let mut rows : Array Row := #[]
  let mut kinds : Array Nat := #[0, 0, 0, 0, 0]
  for k in List.range t.size do
    match t.get k with
    | .leaf _ _ (.cert r) =>
        kinds := kinds.modify 0 (· + 1)
        if seen % stride == 0 && rows.size < nrows then rows := rows.push r
        seen := seen + 1
    | .leaf _ _ (.flip _) => kinds := kinds.modify 1 (· + 1)
    | .leaf _ _ (.handoff _) => kinds := kinds.modify 2 (· + 1)
    | .leaf _ _ (.shared ..) => kinds := kinds.modify 0 (· + 1)
    | .leaf _ _ (.sharedP ..) => kinds := kinds.modify 0 (· + 1)
    | .split .. => kinds := kinds.modify 3 (· + 1)
    | .stellar .. => kinds := kinds.modify 4 (· + 1)
  IO.println s!"table {index}: {t.size} rows; cert/flip/handoff/split/stellar {kinds}; timing {rows.size} cert rows"
  if let some r := rows[0]? then
    let dp := dispPoly r.seg r.kind r.triple
    IO.println s!"dispPoly raw {dp.length}, normalized {(normalize dp).length}, termPoly0 raw {(termPoly r.seg r.kind r.triple 0).length}, weightPoly0 {(weightPoly r.seg r.triple 0).length}"
    IO.println s!"split vars {r.split.length}, shift {r.shift.length}, aff {r.aff.length}, D terms {r.D.length}, G terms {r.G.length}"
  (← IO.getStdout).flush
  let each (p : Row → Bool) : Unit → Bool := fun _ => rows.all p
  timeIt "whole Valid" (each fun r => decide r.Valid)
  timeIt "radius" (each fun r => decide (∀ x ∈ r.radius, 0 ≤ x))
  timeIt "weights" (each fun r => decide (∀ i, NonnegOk r.nonnegVars r.box
    (cmp r.aff (weightPoly r.seg r.triple i))))
  timeIt "weightsPos" (each fun r => decide (∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧
    PosOk r.positiveVars r.box (cmp r.aff (weightPoly r.seg r.triple j))))
  timeIt "gaps" (each fun r => decide (∀ i k, NonnegOk r.nonnegVars r.box
    (scale (-1) (cmp r.aff (gapPoly r.seg r.triple i k)))))
  timeIt "disp" (each fun r => decide r.DispOk)
  timeIt "D only" (each fun r => r.D.length > 0)
  timeIt "weightPoly normalize x3" (each fun r => (List.finRange 3).all fun i =>
    (normalize (weightPoly r.seg r.triple i)).length > 0)
  timeIt "termPoly x3" (each fun r => (List.finRange 3).all fun i =>
    (termPoly r.seg r.kind r.triple i).length > 0)
  timeIt "normalize dispPoly" (each fun r => (normalize (dispPoly r.seg r.kind r.triple)).length > 0)
  timeIt "cmp of normalized dispPoly" (each fun r =>
    (normalize (cmp r.aff (normalize (dispPoly r.seg r.kind r.triple)))).length > 0)
  let partsOf (r : Row) : List Poly :=
    let ps := splitParts (r.split.map Prod.fst) r.G
    ps.2 :: ps.1
  let stripOf (r : Row) (q : Poly) : Poly := stripped r.sbox.nonnegVars q
  timeIt "parts only" (each fun r => (partsOf r).length > 0)
  timeIt "stripped parts" (each fun r => ((partsOf r).map (stripOf r)).length > 0)
  timeIt "centeredLower of parts" (each fun r =>
    ((partsOf r).map fun q => centeredLower r.sbox (stripOf r q)).length > 0 && true)
  timeIt "cornerLower of parts" (each fun r =>
    ((partsOf r).map fun q => cornerLower r.sbox (stripOf r q)).length > 0)
  timeIt "subst raw (centered) of parts" (each fun r =>
    ((partsOf r).map fun q => (subst r.sbox.center r.sbox.radius (stripOf r q)).length).sum > 0)
  if let some r := rows[0]? then
    let qs := partsOf r
    IO.println s!"part sizes {qs.map List.length}; subst sizes {qs.map fun q => (subst r.sbox.center r.sbox.radius (stripOf r q)).length}"
    IO.println s!"centered ok {qs.map fun q => decide (0 ≤ centeredLower r.sbox (stripOf r q))} corner ok {qs.map fun q => decide (0 ≤ cornerLower r.sbox (stripOf r q))} cornerHi ok {qs.map fun q => decide (0 ≤ cornerLowerHi r.sbox (stripOf r q))}"
    IO.println s!"max degree {qs.map fun q => (q.map fun t => t.1.foldl (· + ·) 0).foldl max 0}"
  timeIt "G only" (each fun r => r.G.length > 0)
  let H := fun (_ : Handoff) (_ : Frame) => true
  let _ := H
  timeIt "all rows rowB (handoffs as stage none)" fun _ =>
    (List.range t.size).all fun k => match t.get k with
      | .leaf _ _ (.cert _) => true
      | n => decide (n.id = k) && true
