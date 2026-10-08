import Noperts.Stellated.PackedCornerTree
import Noperts.Stellated.AtlasProjectiveSolutionTree

/-!
Check a `corner.pack` table by table, reporting the first invalid row.
-/

open Noperts.Stellated
open Noperts.Stellated.CornerTree CornerCoverage CornerHandoff PackedCornerTree

def coneNeg (k : Nat) : Fin 4 → Bool := fun b => (k >>> b.val) % 2 = 1

def rootOf (e0 : ℚ) (i : Nat) : Frame :=
  if 83 ≤ i then ppocketRoot e0 2 ⟨(i - 83) % 3, Nat.mod_lt _ (by decide)⟩ else
  if 77 ≤ i then tpocketRoot e0 ⟨((i - 77) / 3) % 2, Nat.mod_lt _ (by decide)⟩
    ⟨(i - 77) % 3, Nat.mod_lt _ (by decide)⟩ else
  if 71 ≤ i then ppocketRoot e0 ⟨((i - 71) / 3) % 3, Nat.mod_lt _ (by decide)⟩
    ⟨(i - 71) % 3, Nat.mod_lt _ (by decide)⟩ else
  if 68 ≤ i then spocketRoot e0 ⟨(i - 68) % 3, Nat.mod_lt _ (by decide)⟩ else
  if 59 ≤ i then pocketRoot e0 ⟨((i - 59) / 3) % 3, Nat.mod_lt _ (by decide)⟩
    ⟨(i - 59) % 3, Nat.mod_lt _ (by decide)⟩ else
  if 43 ≤ i then coneRoot e0 (coneNeg (i - 43)) else
  if i = 36 then skewRoot e0 else
  if 37 ≤ i then zeroRoot e0 ⟨(i - 37) % 6, Nat.mod_lt _ (by decide)⟩ else
  let seg := 18 ≤ i
  let j := i % 18
  if j < 7 then plainRoot e0 seg ⟨j % 7, Nat.mod_lt _ (by decide)⟩
  else if j < 13 then tubeRoot e0 seg ⟨(j - 7) % 6, Nat.mod_lt _ (by decide)⟩
  else if j = 13 then wedgeRoot e0 seg
  else wtubeRoot e0 seg ⟨(j - 14) % 4, Nat.mod_lt _ (by decide)⟩

def stageOf (i : Nat) : Handoff → Bool :=
  if i = 36 then skewStage else
  if 43 ≤ i ∧ i < 59 then cpocketStage else
  if 36 ≤ i then noHandoff else
  let j := i % 18
  if j < 7 then plainStage else if j = 13 then wedgeStage
  else if j < 13 then coneStage else noHandoff

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [p] => pure p
    | _ => throw (IO.userError "expects corner.pack")
  let data ← IO.FS.readFile path
  let tables := decodeTables data
  let e0 := AtlasProjectiveSolutionTree.cornerEps
  let mut ok := true
  for i in List.range 86 do
    let t := tables[i]!
    let H := stage e0 (stageOf i)
    let rootOk := decide (0 < t.size ∧ (t.get 0).frame = rootOf e0 i)
    let mut bad : Option Nat := none
    for k in List.range t.size do
      if bad.isNone then
        unless decide ((t.get k).id = k ∧ (t.get k).ValidAt H t.facts t.fpolys t.get t.size) do
          bad := some k
    if rootOk && bad.isNone then
      IO.println s!"table {i}: valid ({t.size} rows)"
    else
      ok := false
      IO.println s!"table {i}: INVALID root={rootOk} first bad row={bad}"
  IO.println (if ok then "all corner tables valid" else "corner tables INVALID")
