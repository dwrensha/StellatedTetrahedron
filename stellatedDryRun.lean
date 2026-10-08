import Noperts.Stellated.NativeExecutable
import Noperts.Stellated.PackedSolutionTree

/-!
Resource dry run for `constructStellated`: decodes and checks the local packs
present in a directory and the chart-0 table, reporting per-part times, without
the corner tables and without failing on chart rows whose local tables are not
yet packed.  Not part of the proof.
-/

open Noperts.Stellated
open Noperts.Stellated.AtlasProjectiveSolutionTree
open Noperts.Stellated.NativeExecutable

private def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

def main (args : List String) : IO Unit := do
  let (directory, localTasks, globalTasks, only) ← match args with
    | [d] => pure (d, 16, 256, none)
    | [d, l, g] => pure (d, l.toNat!, g.toNat!, none)
    | [d, l, g, o] => pure (d, l.toNat!, g.toNat!, some o.toNat!)
    | _ => throw (IO.userError "expects a directory [localTasks globalTasks [onlyLocal]]")
  let start ← IO.monoNanosNow
  let mut localData : Array (Option String) := #[]
  for index in List.range 64 do
    let path := s!"{directory}/local-{pad2 index}.pack"
    if only.isSome && only != some index then
      localData := localData.push none
    else if ← System.FilePath.pathExists path then
      localData := localData.push (some (← IO.FS.readFile path))
    else
      localData := localData.push none
  let chartData ← IO.FS.readFile s!"{directory}/chart0.pack"
  let data := localData
  let shared : SharedLocalTables := fun index =>
    (data[index.val]!).map (PackedLocalViewTree.decodePackedTable index.val)
  let mut localRows := 0
  for index in List.finRange 64 do
    match shared index with
    | none => pure ()
    | some table =>
        let valid := localTableValidParB table localTasks
        localRows := localRows + table.size
        let now ← IO.monoNanosNow
        log s!"local {index}: {table.size} rows, valid {valid} ({(now - start) / 1000000} ms)"
  if only.isSome then
    let finish ← IO.monoNanosNow
    log s!"locals only: {localRows} rows, {(finish - start) / 1000000} ms"
    return
  let table := PackedSolutionTree.decodeTable 0 shared chartData
  log s!"chart 0: {table.size} rows; checking in {globalTasks} tasks"
  let tasks := tableCoreTasks table globalTasks
  let mut bad := 0
  for task in tasks do
    unless task.get do bad := bad + 1
  let finish ← IO.monoNanosNow
  log s!"done: {localRows} local rows, chart {table.size} rows, {bad}/{tasks.length} chart chunks invalid, total {(finish - start) / 1000000} ms"
