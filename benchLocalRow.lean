import Noperts.Stellated.NativeExecutable
import Noperts.Stellated.PackedSolutionTree
import Noperts.Stellated.LocalKernel

/-!
Profiling aid (not part of the proof): times each conjunct of
`AtlasProjectiveLocalCertificate.Box.ViewValid` on certificate rows of one
packed local table.  `benchLocalRow DIR TABLE NROWS`.
-/

open Noperts.Stellated
open Noperts.Stellated.AtlasProjectiveLocalViewTree
open Noperts.Stellated.AtlasProjectiveLocalCertificate
open Noperts.Stellated.AtlasProjectiveEdgeCertificate (SignedTriangleValid)

private def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

def timeIt (label : String) (n : Nat) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut ok := 0
  for _ in List.range n do
    if f () then ok := ok + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / 1000000} ms ({ok} true)"
  (← IO.getStdout).flush

def agree (directory : String) (index : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/local-{pad2 index}.pack"
  let table := PackedLocalViewTree.decodePackedTable index data
  let mut n := 0
  let mut bad := 0
  let mut acceptN := 0
  for i in List.range table.size do
    match table.get i with
    | .certificate _ box =>
        n := n + 1
        let a := box.viewFastB
        let b := LocalKernel.viewValidN box
        if b then acceptN := acceptN + 1
        if a != b then
          bad := bad + 1
          if bad ≤ 5 then IO.println s!"row {i}: spec {a} integer {b}"
    | _ => pure ()
  IO.println s!"table {index}: {n} certificate rows, integer accepts {acceptN}, disagreements {bad}"

def ratSrc (q : ℚ) : String := s!"({q.num} / {q.den} : ℚ)"

def vec3Src {α : Type} (f : Fin 3 → α) (show_ : α → String) : String :=
  s!"![{show_ (f 0)}, {show_ (f 1)}, {show_ (f 2)}]"

def axisSrc (a : AxisCertificate) : String :=
  let v := fun (f : Fin 3 → VertexIndex) => vec3Src f (fun x => toString x.val)
  "{ edgeStart := " ++ v a.edgeStart ++ ", edgeFinish := " ++ v a.edgeFinish ++
  ", edgeStart₂ := " ++ v a.edgeStart₂ ++ ", edgeFinish₂ := " ++ v a.edgeFinish₂ ++
  ", mix := " ++ vec3Src a.mix (fun x => toString x.val) ++
  ", index := " ++ v a.index ++ ", nonzeroWitness := " ++ v a.nonzeroWitness ++
  ", B := " ++ ratSrc a.B ++ " }"

def boxSrc (b : Box) : String :=
  let tri := vec3Src b.triangle (fun r => vec3Src r ratSrc)
  "{ interval := AtlasPose.rootInterval ℚ, root := " ++ toString b.root.val ++
  ", triangle := " ++ tri ++ ", chart := 0, symmetryIndex := " ++ toString b.symmetryIndex.val ++
  ", certificate := ![" ++ axisSrc (b.certificate 0) ++ ", " ++ axisSrc (b.certificate 1) ++
  ", " ++ axisSrc (b.certificate 2) ++ ", " ++ axisSrc (b.certificate 3) ++ "]" ++
  ", c := " ++ ratSrc b.c ++ ", δ := " ++ ratSrc b.δ ++ ", r := " ++ ratSrc b.r ++ " }"

def emit (directory : String) (index nth : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/local-{pad2 index}.pack"
  let table := PackedLocalViewTree.decodePackedTable index data
  let mut seen := 0
  for i in List.range table.size do
    match table.get i with
    | .certificate _ box =>
        if seen == nth then
          IO.println (boxSrc box)
          return
        seen := seen + 1
    | _ => pure ()

def emitMany (directory : String) (index count stride : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/local-{pad2 index}.pack"
  let table := PackedLocalViewTree.decodePackedTable index data
  let mut seen := 0
  let mut out := 0
  for i in List.range table.size do
    if out ≥ count then break
    match table.get i with
    | .certificate _ box =>
        if seen % stride == 0 then
          IO.println (boxSrc box)
          out := out + 1
        seen := seen + 1
    | _ => pure ()

/-- Over-split probe: split nodes whose four children are certificate leaves,
and whether some child's certificate already certifies the parent triangle. -/
def overprobe (directory : String) (index : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/local-{pad2 index}.pack"
  let table := PackedLocalViewTree.decodePackedTable index data
  let mut splits := 0
  let mut leafSplits := 0
  let mut mergeable := 0
  let mut cuts := 0
  let mut certs := 0
  for i in List.range table.size do
    match table.get i with
    | .certificate .. => certs := certs + 1
    | .cut .. => cuts := cuts + 1
    | .split _ children _ tri =>
        splits := splits + 1
        let kids := (List.finRange 4).map fun c => table.get (children c)
        let boxes := kids.filterMap fun r => match r with
          | .certificate _ b => some b
          | _ => none
        if boxes.length == 4 then
          leafSplits := leafSplits + 1
          if boxes.any (fun b => ({ b with triangle := tri } : Box).viewFastB) then
            mergeable := mergeable + 1
  IO.println s!"table {index}: {table.size} rows: {certs} certs, {splits} splits, {cuts} cuts; all-leaf splits {leafSplits}, mergeable by a child certificate {mergeable}"

/-- Which ViewValid conjunct fails when a child's certificate is tried on its
parent triangle (δ re-tuned to the smallest value the variation test allows). -/
def failprobe (directory : String) (index : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/local-{pad2 index}.pack"
  let table := PackedLocalViewTree.decodePackedTable index data
  let mut tried := 0
  let mut counts : Array Nat := Array.replicate 6 0
  for i in List.range table.size do
    match table.get i with
    | .split _ children _ tri =>
        let boxes := ((List.finRange 4).map fun c => table.get (children c)).filterMap fun r =>
          match r with
          | .certificate _ b => some b
          | _ => none
        if boxes.length == 4 then
          -- first failing conjunct, best (latest) over the four children
          let mut best := 0
          for b0 in boxes do
            let b : Box := { b0 with triangle := tri }
            let b : Box := { b with certificate := fun j =>
              let cj := b.certificate j
              { cj with B := max cj.B (b.weightBudget j) } }
            let δ := (List.finRange 4).foldl (fun acc j =>
              max acc ((b.variationRadiusSum j + 3 * variationError) / (b.certificate j).B)) (0 : ℚ)
            let b : Box := { b with δ := δ }
            let stage :=
              if !(decide (∀ j i, 0 ≤ b.weightLower j i) && decide (∀ j, ∃ i, 0 < b.weightLower j i)) then 0
              else if !(decide (∀ j i k, b.supportUpper j i k ≤ 0)) then 1
              else if !(decide (∀ j, b.weightBudget j ≤ (b.certificate j).B)) then 2
              else if !(decide b.barycentricValid) then 3
              else if !(decide (b.r ^ 2 * (1 + b.c ^ 2) ≤ 4 * b.c ^ 2)) then 4
              else 5
            best := max best stage
          tried := tried + 1
          counts := counts.modify best (· + 1)
    | _ => pure ()
  IO.println s!"table {index}: {tried} all-leaf parents; furthest stage reached: weights-fail {counts[0]!}, support-fail {counts[1]!}, budget-fail {counts[2]!}, barycentric-fail {counts[3]!}, angle-fail {counts[4]!}, PASS-with-retuned-δ {counts[5]!}"

def main (args : List String) : IO Unit := do
  if let [d, "failprobe", t] := args then
    failprobe d t.toNat!
    return
  if let [d, "overprobe", t] := args then
    overprobe d t.toNat!
    return
  if let [d, "emitmany", t, n, st] := args then
    emitMany d t.toNat! n.toNat! st.toNat!
    return
  if let [d, "emit", t, n] := args then
    emit d t.toNat! n.toNat!
    return
  if let [d, "agree", t] := args then
    agree d t.toNat!
    return
  let (directory, index, nrows) ← match args with
    | [d, i, n] => pure (d, i.toNat!, n.toNat!)
    | _ => throw (IO.userError "expects DIR TABLE NROWS")
  let tStart ← IO.monoNanosNow
  let data ← IO.FS.readFile s!"{directory}/local-{pad2 index}.pack"
  let tRead ← IO.monoNanosNow
  IO.println s!"read pack: {(tRead - tStart) / 1000000} ms"
  (← IO.getStdout).flush
  let table := PackedLocalViewTree.decodePackedTable index data
  let mut boxes : Array Box := #[]
  for i in List.range table.size do
    if boxes.size < nrows then
      match table.get i with
      | .certificate _ box => boxes := boxes.push box
      | _ => pure ()
  let tDec ← IO.monoNanosNow
  IO.println s!"table {index}: {table.size} rows, timing {boxes.size} certificate rows (decode {(tDec - tRead) / 1000000} ms)"
  (← IO.getStdout).flush
  let digits (q : ℚ) : String := s!"{(toString q.num).length}/{(toString q.den).length}"
  if let some b := boxes[0]? then
    let tt0 ← IO.monoNanosNow
    let x := b.triangle 1 2
    let tt1 ← IO.monoNanosNow
    IO.println s!"triangle coord {x} read in {(tt1 - tt0) / 1000} us"
    (← IO.getStdout).flush
    let tc0 ← IO.monoNanosNow
    let y := b.approxNormalizedCenter 0 0
    let tc1 ← IO.monoNanosNow
    IO.println s!"one center coord in {(tc1 - tc0) / 1000000} ms (digits {(toString y.num).length})"
    (← IO.getStdout).flush
    let c := b.approxNormalizedCenter
    IO.println s!"center digits (num/den): {digits (c 0 0)} {digits (c 1 1)} {digits (c 2 2)} {digits (c 3 0)}"
    IO.println s!"c, delta, B digits: {digits b.c} {digits b.δ} {digits (b.certificate 0).B}"
    (← IO.getStdout).flush
    let t0 ← IO.monoNanosNow
    let d := LocalCertificate.tetraDetQ (centersOfArray b.centerArray)
    let t1 ← IO.monoNanosNow
    IO.println s!"tetraDet digits {digits d} in {(t1 - t0) / 1000000} ms"
    (← IO.getStdout).flush
  let each (p : Box → Bool) : Unit → Bool := fun _ => boxes.all p
  timeIt "whole ViewValid" 1 (each fun b => decide b.ViewValid)
  let tb := fun (b : Box) => ball3Of b.tbArr
  timeIt "new: eArr x4" 1 (each fun b => (List.finRange 4).all fun j => (b.eArr j).size = 9)
  timeIt "new: + wcArrOf" 1 (each fun b => (List.finRange 4).all fun j =>
    (wcArrOf (vec9Of (b.eArr j))).size = 9)
  timeIt "new: + wArrOf" 1 (each fun b => (List.finRange 4).all fun j =>
    (b.wArrOf (vec9Of (wcArrOf (vec9Of (b.eArr j))))).size = 9)
  timeIt "new: eArr + sArrOf" 1 (each fun b => (List.finRange 4).all fun j =>
    (b.sArrOf j (vec9Of (b.eArr j))).size = 72)
  timeIt "new: tbArr" 1 (each fun b => b.tbArr.size = 3)
  timeIt "new: + vbArrOf" 1 (each fun b => (List.finRange 4).all fun j =>
    (b.vbArrOf j (tb b) (vec9Of (b.eArr j)) (vec9Of (wcArrOf (vec9Of (b.eArr j))))).size = 3)
  timeIt "new: axisFromE x4" 1 (each fun b => (List.finRange 4).all fun j =>
    (b.axisFromE (tb b) j (b.eArr j)).1)
  timeIt "new: barycentric (vbAll precomputed)" 1 (fun _ =>
    let cs := boxes.map fun b => b.centerArrayOf b.vbAll
    (boxes.zip cs).all fun (b, c) => b.barycentricB c)
  timeIt "new: viewFastB" 1 (each fun b => b.viewFastB)
  timeIt "triangle_valid" 1 (each fun b => decide (SignedTriangleValid b.root b.triangle))
  timeIt "B_pos" 1 (each fun b => decide (∀ j, 0 < (b.certificate j).B))
  timeIt "weight_nonneg" 1 (each fun b => decide (∀ j i, 0 ≤ b.weightLower j i))
  timeIt "support" 1 (each fun b => decide (∀ j i k, b.supportUpper j i k ≤ 0))
  timeIt "budget" 1 (each fun b => decide (∀ j, b.weightBudget j ≤ (b.certificate j).B))
  timeIt "variation" 1 (each fun b => decide (∀ j,
    b.variationRadiusSum j + 3 * variationError ≤ (b.certificate j).B * b.δ))
  timeIt "barycentric" 1 (each fun b => decide b.barycentricValid)
  timeIt "angle_bound" 1 (each fun b => decide (b.r ^ 2 * (1 + b.c ^ 2) ≤ 4 * b.c ^ 2))
