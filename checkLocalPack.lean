import Noperts.Stellated.NativeExecutable

/-!
Check one packed local-view table: `checkLocalPack NN file.pack`.
-/

open Noperts.Stellated
open Noperts.Stellated.NativeExecutable

def main (args : List String) : IO Unit := do
  let (index, path) ← match args with
    | [i, p] => pure (i.toNat!, p)
    | _ => throw (IO.userError "expects a table index and a pack file")
  let data ← IO.FS.readFile path
  let table := PackedLocalViewTree.decodePackedTable index data
  let start ← IO.monoMsNow
  let ok := localTableValidParB table 16
  let finish ← IO.monoMsNow
  IO.println s!"table {index}: {table.size} rows, r = {table.r}, valid = {ok} ({finish - start} ms)"
