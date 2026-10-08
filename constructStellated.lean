import Noperts.Stellated.NativeExecutable
import Noperts.Stellated.PackedSolutionTree
import Noperts.Stellated.PackedCornerTree

/-!
Native executable that reads and checks exact certificate data, then constructs
a proof that the stellated tetrahedron `P_{11/20}` is not Rupert.

The directory must contain `chart0.pack`, `corner.pack` (the 36 corner
blow-up tables) and `local-NN.pack` for each depth-3
chamber subtriangle `NN` (two digits) that has a shared local table; missing
local packs are treated as absent tables.
-/

open Noperts.Stellated
open Noperts.Stellated.AtlasProjectiveSolutionTree
open Noperts.Stellated.NativeExecutable

private def localTaskCount : Nat := 16
private def globalTaskCount : Nat := 256

private def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

def main (args : List String) : IO Unit := do
  let directory ← match args with
    | [directory] => pure directory
    | _ => throw (IO.userError
        "expects one directory containing chart0.pack and local-NN.pack files")
  let mut localData : Array (Option String) := #[]
  for index in List.range 64 do
    let path := s!"{directory}/local-{pad2 index}.pack"
    if ← System.FilePath.pathExists path then
      localData := localData.push (some (← IO.FS.readFile path))
    else
      localData := localData.push none
  let chartData ← IO.FS.readFile s!"{directory}/chart0.pack"
  -- Corner tables: format v2 (`corner-v2.pack`, shared fact rows) if present,
  -- else the original v1 `corner.pack`.
  let v2 := s!"{directory}/corner-v2.pack"
  let corner ← if ← System.FilePath.pathExists v2 then
      pure (PackedCornerTree.tablesOf (PackedCornerTree.decodeTablesV2 (← IO.FS.readFile v2)))
    else
      pure (PackedCornerTree.tablesOf
        (PackedCornerTree.decodeTables (← IO.FS.readFile s!"{directory}/corner.pack")))
  -- Decode every local table exactly once: chart rows look up `shared index`
  -- per row, so a decoding closure would re-decode a whole table each time.
  let mut decoded : Array (Option AtlasProjectiveLocalViewTree.Table) := #[]
  for index in List.range 64 do
    match localData[index]! with
    | none => decoded := decoded.push none
    | some packed =>
        let table := PackedLocalViewTree.decodePackedTable index packed
        -- force the rows now so decoding is timed and not repeated
        log s!"decoded local table {index}: {table.size} rows"
        decoded := decoded.push (some table)
  let tables := decoded
  let shared : SharedLocalTables := fun index => tables[index.val]!
  let globalTable : SharedLocalTables → AtlasProjectiveSolutionTree.Table :=
    fun s => PackedSolutionTree.decodeTable 0 s chartData
  let checked ← constructProof localTaskCount globalTaskCount corner shared
    globalTable (fun _ => rfl) (fun _ => rfl)
  let _proof : ¬ IsRupert exactVerts := checked.down
