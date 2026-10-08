import Noperts.Stellated.PackedSolutionTree
import Noperts.Stellated.ChartKernelEdge
import Noperts.Stellated.ChartKernelGlobal
import Noperts.Stellated.ChartKernelMixed

/-!
Profiling aid (not part of the proof): estimates the chart-0 check cost per
row kind from evenly sampled rows.  Local tables are not loaded, so tube rows
time `tube.Valid` and then fail the (cheap) shared-table match.
`benchChartRow DIR NSAMPLE`.
-/

open Noperts.Stellated
open Noperts.Stellated.AtlasProjectiveSolutionTree

def kindOf : Row → Nat
  | .cayleySplit .. => 0 | .viewRoot .. => 1 | .viewSplit .. => 2
  | .projective .. => 3 | .projectiveGlobal .. => 4 | .projectiveMixedGlobal .. => 5
  | .symmetryLocal .. => 6 | .projectiveLocal .. => 7 | .symmetryTube .. => 8
  | .octahedronPrune .. => 9 | .flipPrune .. => 10 | .corner .. => 11 | .viewCut .. => 12

def kindNames : Array String := #["cayleySplit", "viewRoot", "viewSplit", "projective",
  "projectiveGlobal", "projectiveMixedGlobal", "symmetryLocal", "projectiveLocal",
  "symmetryTube", "octahedronPrune", "flipPrune", "corner", "viewCut"]

def timeIt (label : String) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let ok ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / 1000000} ms ({ok})"
  (← IO.getStdout).flush

open AtlasProjectiveEdgeCertificate in
def projBench (directory : String) (n : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut boxes : Array Box := #[]
  let mut seen := 0
  for i in List.range table.size do
    match table.get i with
    | .projective _ box =>
        if seen % 10000 == 0 && boxes.size < n then boxes := boxes.push box
        seen := seen + 1
    | _ => pure ()
  IO.println s!"{boxes.size} projective boxes; edges {boxes.map (·.edgePred + 1)}"
  let each (p : Box → Bool) : Unit → Bool := fun _ => boxes.all p
  timeIt "whole Valid" (each fun b => decide b.Valid)
  timeIt "triangle_valid" (each fun b => decide (SignedTriangleValid b.root b.triangle))
  timeIt "direction_nonzero" (each fun b => decide (∀ i, b.supportUpper i (b.nonzeroWitness i) < 0))
  timeIt "totalDefect" (each fun b => decide (b.totalDefect ≤ 1000000))
  timeIt "adjustedDisplacementLower" (each fun b => decide (b.adjustedDisplacementLower ≤ 1000000))
  timeIt "totalQuadratic x3" (each fun b => decide ((b.edgeShell.totalQuadratic 0).c0 +
    (b.edgeShell.totalQuadratic 1).c0 + (b.edgeShell.totalQuadratic 2).c0 ≤ 1000000))
  timeIt "contactQuadratic all (c0 only)" (each fun b => decide ((List.finRange (b.edgePred + 1)).all
    fun i => (List.finRange 3).all fun c => (b.edgeShell.contactQuadratic i c).c0 ≤ 1000000))
  timeIt "dBound only" (each fun b => decide (b.edgeShell.dBound ≤ 1000000))
  timeIt "κℚ only" (each fun _ => decide (RationalApprox.κℚ ≤ 1000000))
  timeIt "fastLower only" (each fun b => decide (b.fastLower ≤ 1000000))
  timeIt "error only" (each fun b => decide (b.edgeShell.displacementError ≤ 1000000))
  timeIt "cast edges" (each fun b => decide (((b.edgePred + 1 : ℕ) : ℚ) * 10 ≤ 1000000))
  timeIt "dBound*κ" (each fun b => decide (b.edgeShell.dBound * RationalApprox.κℚ ≤ 1000000))
  timeIt "dBound+error" (each fun b => decide (b.edgeShell.displacementError ≤ 1000000))

open AtlasProjectiveGlobalCertificate in
def globalBench (directory : String) (n : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut boxes : Array Box := #[]
  let mut seen := 0
  for i in List.range table.size do
    match table.get i with
    | .projectiveGlobal _ box =>
        if seen % 10000 == 0 && boxes.size < n then boxes := boxes.push box
        seen := seen + 1
    | _ => pure ()
  IO.println s!"{boxes.size} global boxes"
  let each (p : Box → Bool) : Unit → Bool := fun _ => boxes.all p
  let big : ℚ := 1000000
  timeIt "whole Valid" (each fun b => decide b.Valid)
  timeIt "Admissible" (each fun b => decide b.Admissible)
  timeIt "certifiedFast" (each fun b => decide (b.certifiedFast ≤ big))
  timeIt "weightedFast" (each fun b => decide (b.weightedFast ≤ big))
  timeIt "coefficient balls" (each fun b => decide ((coefficientBallArray (AtlasProjectiveEdgeCertificate.fnOf3 b.tbArray ⟨0, 0⟩)
    (cqOf b.cqArray) (vecOf9 b.wcArray)).size = 10))
  timeIt "bernstein fast" (each fun b => decide (bernsteinOf (AtlasProjectiveEdgeCertificate.fnOf3 b.rbArray ⟨0, 0⟩)
    (AtlasProjectiveEdgeCertificate.fnOf3 (b.aArray (cqOf b.cqArray) (vecOf9 b.wcArray)) 0)
    (cqOf (b.mArray (cqOf b.cqArray) (vecOf9 b.wcArray))) ≤ big))
  timeIt "weightedDefectUpper" (each fun b => decide (b.weightedDefectUpper ≤ big))
  timeIt "certifiedDisplacementLower" (each fun b => decide (b.certifiedDisplacementLower ≤ big))
  timeIt "adjustedDisplacementBall center" (each fun b => decide (b.adjustedDisplacementBall.center ≤ big))
  timeIt "bernsteinDisplacementLower" (each fun b => decide (b.bernsteinDisplacementLower ≤ big))
  timeIt "contactQuadratic all c0" (each fun b => (List.finRange 3).all fun i =>
    (List.finRange 3).all fun c => decide ((b.contactQuadratic i c).c0 ≤ big))
  timeIt "dBound/error" (each fun b => decide (b.displacementError ≤ big))

open AtlasProjectiveGlobalCertificate in
def globalWhich (directory : String) (stride : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut n := 0
  let mut ball := 0
  let mut bern := 0
  let mut bonly := 0
  let mut unsymOk := 0
  let mut seen := 0
  for i in List.range table.size do
    match table.get i with
    | .projectiveGlobal _ b =>
        seen := seen + 1
        if seen % stride != 0 then continue
        n := n + 1
        let rhs := b.dBound * b.weightedFast + b.displacementError
        let bl := b.adjustedDisplacementBall.center - b.adjustedDisplacementBall.radius
        if rhs ≤ bl then ball := ball + 1
        if rhs ≤ b.certifiedFast then bern := bern + 1
        if rhs ≤ b.bernsteinDisplacementLower then bonly := bonly + 1
        let w := b.wArray (vecOf9 b.wcArray)
        let sa := b.sArray
        let unsym : ℚ := (List.finRange 3).foldl (fun acc i =>
          acc + max 0 ((List.finRange 8).foldl (fun m k =>
            if k = b.certificate.index i then m else
            (List.finRange 3).foldl (fun m a => (List.finRange 3).foldl (fun m bb =>
              max m (w.getD (3 * a.val + i.val) 0 * sa.getD (9 * k.val + 3 * i.val + bb.val) 0)) m) m) 0)) 0
        if b.dBound * unsym + b.displacementError ≤ b.bernsteinDisplacementLower then unsymOk := unsymOk + 1
    | _ => pure ()
  IO.println s!"global sampled {n}: ball-only {ball}, bernstein-only {bonly}, certified(max) {bern}, unsym+bern {unsymOk}"

/-- Is this chart leaf's certificate still valid on a bigger region? -/
def leafOn (r : Row) (iv : Interval) (tri : Option (Fin 8 × Triangle)) : Bool :=
  match r with
  | .projective _ b =>
      let b := { b with interval := iv }
      let b := match tri with | some (root, t) => { b with root, triangle := t } | none => b
      decide b.Valid
  | .projectiveGlobal _ b =>
      let b := { b with interval := iv }
      let b := match tri with | some (root, t) => { b with root, triangle := t } | none => b
      decide b.Valid
  | _ => false

def isCertLeaf : Row → Bool
  | .projective .. | .projectiveGlobal .. => true
  | _ => false

/-- Over-split probe for chart 0 (sampled). -/
def overprobe (directory : String) (cap : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut cs := 0
  let mut csM := 0
  let mut vs := 0
  let mut vsM := 0
  let mut seen := 0
  for i in List.range table.size do
    match table.get i with
    | .cayleySplit _ lo hi _ iv region =>
        let a := table.get lo
        let b := table.get hi
        if isCertLeaf a && isCertLeaf b then
          seen := seen + 1
          if seen % 50 == 0 && cs < cap then
            cs := cs + 1
            let tri := match region with | .triangle root t => some (root, t) | .sphere => none
            if leafOn a iv tri || leafOn b iv tri then csM := csM + 1
    | .viewSplit _ children iv root t =>
        let kids := (List.finRange 4).map fun c => table.get (children c)
        if kids.all isCertLeaf && vs < cap then
          vs := vs + 1
          if kids.any (fun k => leafOn k iv (some (root, t))) then vsM := vsM + 1
    | _ => pure ()
  IO.println s!"cayley splits with two cert leaves: sampled {cs}, mergeable {csM}; view splits with four cert leaves: sampled {vs}, mergeable {vsM}"

def qf (q : ℚ) : Float := (if q.num < 0 then -1 else 1) * q.num.natAbs.toFloat / q.den.toFloat

open AtlasProjectiveEdgeCertificate in
/-- Why does a projective leaf's certificate fail on its parent's box?  Ratio
`need / have` with `need = dBound·totalDefect + displacementError` and
`have = adjustedDisplacementLower`, for the leaf box and the parent box. -/
def whyfail (directory : String) (cap : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut n := 0
  let mut seen := 0
  let mut negHave := 0
  let mut gridNeg := 0
  let mut defectDom := 0
  let mut otherFail := 0
  let mut hist : Array ℕ := Array.replicate 8 0   -- parent need/have in [1,1.25),[1.25,1.5),[1.5,2),[2,3),[3,5),[5,10),[10,∞), else
  for i in List.range table.size do
    if n < cap then
      if let .cayleySplit _ lo _ _ iv _ := table.get i then
        if let .projective _ b := table.get lo then
          seen := seen + 1
          if seen % 20 == 0 then
            n := n + 1
            let pb := { b with interval := iv }
            let hv := pb.adjustedDisplacementLower
            let d := pb.edgeShell.dBound * pb.totalDefect
            let e := pb.edgeShell.displacementError
            if hv ≤ 0 then
              negHave := negHave + 1
              -- grid minimum of the adjusted quadratic at each corner (exact quadratic)
              let vb := pb.edgeShell.variableBalls
              let gridMin := fun (q : Noperts.Checker.RatQuadratic3) => Id.run do
                let mut m : Float := 1e300
                for a in List.range 9 do
                  for b' in List.range 9 do
                    for c in List.range 9 do
                      let t := fun (k : ℕ) (r : Noperts.Checker.RatBall) =>
                        qf r.center + qf r.radius * ((k.toFloat / 4) - 1)
                      let x := t a (vb 0)
                      let y := t b' (vb 1)
                      let z := t c (vb 2)
                      let v := qf q.c0 + qf q.cx * x + qf q.cy * y + qf q.cz * z + qf q.cxx * x * x +
                        qf q.cxy * x * y + qf q.cxz * x * z + qf q.cyy * y * y + qf q.cyz * y * z +
                        qf q.czz * z * z
                      m := min m v
                return m
              let gm := min (gridMin (pb.adjustedQuadratic 0))
                (min (gridMin (pb.adjustedQuadratic 1)) (gridMin (pb.adjustedQuadratic 2)))
              if gm ≤ 0 then gridNeg := gridNeg + 1
            else
              let r := qf ((d + e) / hv)
              let k := if r < 1 then 7 else if r < 1.25 then 0 else if r < 1.5 then 1 else if r < 2 then 2
                else if r < 3 then 3 else if r < 5 then 4 else if r < 10 then 5 else 6
              hist := hist.modify k (· + 1)
              if qf d > qf e then defectDom := defectDom + 1
              if r < 1 then otherFail := otherFail + 1
  IO.println s!"{n} projective-leaf parents: displacement lower ≤ 0 on parent: {negHave}; grid-true negative {gridNeg}"
  IO.println s!"need/have histogram [1,1.25) [1.25,1.5) [1.5,2) [2,3) [3,5) [5,10) [10,∞) <1(other part fails): {hist}"
  IO.println s!"support-defect term dominates the error: {defectDom}"

def edgeAgree (directory : String) (stride : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut n := 0
  let mut both := 0
  let mut onlySpec := 0
  let mut bad := 0
  let mut seen := 0
  for i in List.range table.size do
    if let .projective _ b := table.get i then
      seen := seen + 1
      if seen % stride == 0 then
        n := n + 1
        let a := ChartKernel.validEdgeN b
        if ChartKernel.validEdgeP b != a then IO.println s!"P/N disagree at row {i}"
        if ChartKernel.validEdgeQ b != a then IO.println s!"Q/N disagree at row {i}"
        if ChartKernel.validEdgeK b (ChartKernel.defectHints b) != a then
          IO.println s!"K/N disagree at row {i}"
        if ChartKernel.validEdgeH b (ChartKernel.defectHints b) != a then
          IO.println s!"H/N disagree at row {i}"
        let v := decide b.Valid
        if a && v then both := both + 1
        if !a && v then onlySpec := onlySpec + 1
        if a && !v then bad := bad + 1
  IO.println s!"projective rows sampled {n}: integer+spec {both}, spec only {onlySpec}, UNSOUND {bad}"

def qS (q : ℚ) : String := s!"({q.num} / {q.den} : ℚ)"

def poseS (p : AtlasPose ℚ) : String := s!"⟨{qS p.θ}, {qS p.φ}, {qS p.x}, {qS p.y}, {qS p.z}⟩"

open AtlasProjectiveEdgeCertificate in
def edgeBoxS (b : Box) : String :=
  let n := b.edgePred + 1
  let vec := fun (f : Fin n → VertexIndex) =>
    "![" ++ ", ".intercalate ((List.finRange n).map fun i => toString (f i).val) ++ "]"
  let tri := "![" ++ ", ".intercalate ((List.finRange 3).map fun j =>
    "![" ++ ", ".intercalate ((List.finRange 3).map fun c => qS (b.triangle j c)) ++ "]") ++ "]"
  s!"⟨AtlasInterval.mk {poseS b.interval.min} {poseS b.interval.max} (by decide +kernel), {b.root.val}, {tri}, {b.chart.val}, {b.edgePred}, {vec b.outerIndex}, {vec b.innerIndex}, {vec b.nonzeroWitness}, ![{qS (b.ballMultiplier 0)}, {qS (b.ballMultiplier 1)}, {qS (b.ballMultiplier 2)}]⟩"

def emitEdge (directory : String) (stride count : Nat) (out : String) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut rows : Array String := #[]
  let mut seen := 0
  for i in List.range table.size do
    if rows.size < count then
      if let .projective _ b := table.get i then
        seen := seen + 1
        if seen % stride == 0 then
          rows := rows.push s!"({edgeBoxS b}, {ChartKernel.defectHints b})"
  IO.FS.writeFile out s!"import Noperts.Stellated.ChartKernelEdge
open Noperts.Stellated Noperts.Stellated.AtlasProjectiveEdgeCertificate

set_option maxHeartbeats 0
def rows : List (Box × List Int) := [
{",\n".intercalate rows.toList}]

set_option maxRecDepth 100000
theorem rows_ok : rows.all (fun r => ChartKernel.validEdgeK r.1 r.2) = true := by decide +kernel
"


def globalAgree (directory : String) (stride : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut n := 0
  let mut both := 0
  let mut onlySpec := 0
  let mut bad := 0
  let mut seen := 0
  for i in List.range table.size do
    if let .projectiveGlobal _ b := table.get i then
      seen := seen + 1
      if seen % stride == 0 then
        n := n + 1
        let a := ChartKernelG.validGlobalK b (ChartKernelG.globalHints b)
        let v := decide b.Valid
        if a && v then both := both + 1
        if !a && v then
          onlySpec := onlySpec + 1
          if onlySpec ≤ 5 then IO.println s!"spec-only row {i}"
        if a && !v then bad := bad + 1
  IO.println s!"global rows sampled {n}: integer+spec {both}, spec only {onlySpec}, UNSOUND {bad}"

def certS (c : AtlasProjectiveLocalCertificate.AxisCertificate) : String :=
  let v := fun (f : Fin 3 → VertexIndex) =>
    "![" ++ ", ".intercalate ((List.finRange 3).map fun i => toString (f i).val) ++ "]"
  let m := "![" ++ ", ".intercalate ((List.finRange 3).map fun i => toString (c.mix i).val) ++ "]"
  s!"⟨{v c.edgeStart}, {v c.edgeFinish}, {v c.edgeStart₂}, {v c.edgeFinish₂}, {m}, {v c.index}, {v c.nonzeroWitness}, {qS c.B}⟩"

open AtlasProjectiveGlobalCertificate in
def globalBoxS (b : Box) : String :=
  let vec := fun (f : Fin 3 → VertexIndex) =>
    "![" ++ ", ".intercalate ((List.finRange 3).map fun i => toString (f i).val) ++ "]"
  let tri := "![" ++ ", ".intercalate ((List.finRange 3).map fun j =>
    "![" ++ ", ".intercalate ((List.finRange 3).map fun c => qS (b.triangle j c)) ++ "]") ++ "]"
  s!"⟨AtlasInterval.mk {poseS b.interval.min} {poseS b.interval.max} (by decide +kernel), {b.root.val}, {tri}, {b.chart.val}, {certS b.certificate}, {vec b.innerIndex}, {qS b.ballMultiplier}⟩"

def emitGlobal (directory : String) (stride count : Nat) (out : String) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut rows : Array String := #[]
  let mut seen := 0
  for i in List.range table.size do
    if rows.size < count then
      if let .projectiveGlobal _ b := table.get i then
        seen := seen + 1
        if seen % stride == 0 then
          rows := rows.push s!"({globalBoxS b}, {ChartKernelG.globalHints b})"
  IO.FS.writeFile out s!"import Noperts.Stellated.ChartKernelGlobal
open Noperts.Stellated Noperts.Stellated.AtlasProjectiveGlobalCertificate

set_option maxHeartbeats 0
def rows : List (Box × List Int) := [
{",\n".intercalate rows.toList}]

set_option maxRecDepth 100000
theorem rows_ok : rows.all (fun r => ChartKernelG.validGlobalK r.1 r.2) = true := by decide +kernel
"

def mixedAgree (directory : String) (stride : Nat) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut n := 0
  let mut both := 0
  let mut onlySpec := 0
  let mut bad := 0
  let mut seen := 0
  for i in List.range table.size do
    if let .projectiveMixedGlobal _ b := table.get i then
      seen := seen + 1
      if seen % stride == 0 then
        n := n + 1
        let a := ChartKernelM.validMixedK b (ChartKernelM.mixedHints b)
        let v := decide b.Valid
        if a && v then both := both + 1
        if !a && v then
          onlySpec := onlySpec + 1
          if onlySpec ≤ 5 then IO.println s!"spec-only row {i}"
        if a && !v then bad := bad + 1
  IO.println s!"mixed rows sampled {n}: integer+spec {both}, spec only {onlySpec}, UNSOUND {bad}"

open AtlasProjectiveMixedGlobalCertificate in
def mixedBoxS (b : Box) : String :=
  let tri := "![" ++ ", ".intercalate ((List.finRange 3).map fun j =>
    "![" ++ ", ".intercalate ((List.finRange 3).map fun c => qS (b.triangle j c)) ++ "]") ++ "]"
  let vec := fun (f : Fin 3 → VertexIndex) =>
    "![" ++ ", ".intercalate ((List.finRange 3).map fun i => toString (f i).val) ++ "]"
  let comp := fun (c : Component) => s!"⟨{certS c.certificate}, {vec c.innerIndex}, {qS c.ballMultiplier}⟩"
  s!"⟨AtlasInterval.mk {poseS b.interval.min} {poseS b.interval.max} (by decide +kernel), {b.root.val}, {tri}, {b.chart.val}, ![{comp (b.component 0)}, {comp (b.component 1)}, {comp (b.component 2)}, {comp (b.component 3)}], ![{qS (b.weight 0)}, {qS (b.weight 1)}, {qS (b.weight 2)}, {qS (b.weight 3)}]⟩"

def emitMixed (directory : String) (stride count : Nat) (out : String) : IO Unit := do
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut rows : Array String := #[]
  let mut seen := 0
  for i in List.range table.size do
    if rows.size < count then
      if let .projectiveMixedGlobal _ b := table.get i then
        seen := seen + 1
        if seen % stride == 0 then
          rows := rows.push s!"({mixedBoxS b}, {ChartKernelM.mixedHints b})"
  IO.FS.writeFile out s!"import Noperts.Stellated.ChartKernelMixed
open Noperts.Stellated Noperts.Stellated.AtlasProjectiveMixedGlobalCertificate
open Noperts.Stellated.AtlasProjectiveLocalCertificate

set_option maxHeartbeats 0
def rows : List (AtlasProjectiveMixedGlobalCertificate.Box × List Int) := [
{",\n".intercalate rows.toList}]

set_option maxRecDepth 100000
theorem rows_ok : rows.all (fun r => ChartKernelM.validMixedK r.1 r.2) = true := by decide +kernel
"

def main (args : List String) : IO Unit := do
  if let [d, "emitedge", st, c, o] := args then
    emitEdge d st.toNat! c.toNat! o
    return
  if let [d, "edgeagree", n] := args then
    edgeAgree d n.toNat!
    return
  if let [d, "whyfail", n] := args then
    whyfail d n.toNat!
    return
  if let [d, "overprobe", n] := args then
    overprobe d n.toNat!
    return
  if let [d, "mixedagree", n] := args then
    mixedAgree d n.toNat!; return
  if let [d, "emitmixed", st, c, o] := args then
    emitMixed d st.toNat! c.toNat! o; return
  if let [d, "globalagree", n] := args then
    globalAgree d n.toNat!; return
  if let [d, "emitglobal", st, c, o] := args then
    emitGlobal d st.toNat! c.toNat! o; return
  if let [d, "globalwhich", n] := args then
    globalWhich d n.toNat!; return
  if let [d, "global", n] := args then
    globalBench d n.toNat!
    return
  if let [d, "proj", n] := args then
    projBench d n.toNat!
    return
  let (directory, nsample) ← match args with
    | [d, n] => pure (d, n.toNat!)
    | _ => throw (IO.userError "expects DIR NSAMPLE")
  let data ← IO.FS.readFile s!"{directory}/chart0.pack"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut counts : Array Nat := Array.replicate 13 0
  for i in List.range table.size do
    counts := counts.modify (kindOf (table.get i)) (· + 1)
  IO.println s!"chart 0: {table.size} rows"
  let mut total : Float := 0
  for kind in List.range 13 do
    if counts[kind]! == 0 then continue
    let stride := max 1 (counts[kind]! / nsample)
    let mut sample : Array Nat := #[]
    let mut seen := 0
    for i in List.range table.size do
      if kindOf (table.get i) == kind then
        if seen % stride == 0 && sample.size < nsample then sample := sample.push i
        seen := seen + 1
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => sample.foldl (fun n i =>
      if validIxAtB table.chart table.get table.size table.sharedLocal i then n + 1 else n) 0
    let t1 ← IO.monoNanosNow
    let per : Float := (t1 - t0).toFloat / 1e6 / sample.size.toFloat
    let est := per * (counts[kind]!).toFloat / 1000
    total := total + est
    IO.println s!"{kindNames[kind]!}: {counts[kind]!} rows, {per} ms/row, est {est} s ({ok}/{sample.size} pass)"
    (← IO.getStdout).flush
  IO.println s!"estimated chart total: {total / 3600} CPU-hours"
