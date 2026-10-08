import Noperts.Stellated.PackedSolutionTree

/-!
Test harness: decode a packed chart-0 table and check every leaf row that
does not depend on other rows or shared tables, reporting counts per kind.
Not part of the proof.
-/

open Noperts.Stellated
open Noperts.Stellated.AtlasProjectiveSolutionTree

def kindName : Row → String
  | .cayleySplit .. => "relative_split"
  | .viewRoot .. => "view_root"
  | .viewSplit .. => "view_split"
  | .projective .. => "edge"
  | .projectiveGlobal .. => "global"
  | .projectiveMixedGlobal .. => "mixed_global"
  | .symmetryLocal .. => "symmetry_local"
  | .projectiveLocal .. => "local"
  | .symmetryTube .. => "tube"
  | .octahedronPrune .. => "octahedron"
  | .flipPrune .. => "flip"
  | .corner .. => "corner"
  | .viewCut .. => "view_cut"

def isLeaf : Row → Bool
  | .cayleySplit .. | .viewRoot .. | .viewSplit .. | .symmetryTube ..
  | .viewCut .. => false
  | _ => true

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [p] => pure p
    | _ => throw (IO.userError "expects one pack file")
  let data ← IO.FS.readFile path
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) data
  let mut pass : Std.HashMap String Nat := {}
  let mut fail : Std.HashMap String Nat := {}
  let mut firstFail : Std.HashMap String Nat := {}
  for i in List.range table.size do
    let row := table.get i
    if isLeaf row then
      let k := kindName row
      if decide (row.ValidAt 0 table.get table.size table.sharedLocal) then
        pass := pass.insert k (pass.getD k 0 + 1)
      else
        fail := fail.insert k (fail.getD k 0 + 1)
        unless firstFail.contains k do firstFail := firstFail.insert k i
  IO.println s!"rows {table.size}"
  for (k, n) in pass.toList do IO.println s!"pass {k}: {n}"
  for (k, n) in fail.toList do IO.println s!"FAIL {k}: {n} (first row {firstFail.getD k 0})"
