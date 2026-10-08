import Noperts.Stellated.PackedLocalViewTree

/-!
Generator for the kernel local tables (not part of the proof).

`localKernelGen DIR OUT ROWS PART` writes, for each `DIR/local-NN.pack`:
* `OUT/LNN/Data.lean`, loading the literal table;
* `OUT/LNN/P<k>.lean`, proving `PART` slices of `ROWS` rows each
  (`decide +kernel` with the integer `ViewValid` instance), so the slices of a big
  table check in parallel;
* `OUT/LNN.lean`, chaining the slices into `Table.Valid` and the header's `LocalCovered`;
and `OUT/Assembly.lean` proving `HeadersCovered headers`.
-/

open Noperts.Stellated

def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

def main (args : List String) : IO Unit := do
  let (dir, out, rows, part) ← match args with
    | [d, o, r, p] => pure (d, o, r.toNat!, p.toNat!)
    | _ => throw (IO.userError "expects DIR OUT ROWS PART")
  IO.FS.createDirAll out
  let absDir ← IO.FS.realPath dir
  let mut present : Array Nat := #[]
  for idx in List.range 64 do
    let path := s!"{dir}/local-{pad2 idx}.pack"
    unless ← System.FilePath.pathExists path do continue
    present := present.push idx
    let packed ← IO.FS.readFile path
    let table := PackedLocalViewTree.decodePackedTable idx packed
    let n := table.size
    let t := s!"t{pad2 idx}"
    let mut starts : Array (Nat × Nat) := #[]
    let mut s := 0
    while s < n do
      let c := min rows (n - s)
      starts := starts.push (s, c)
      s := s + c
    let L := s!"L{pad2 idx}"
    IO.FS.createDirAll s!"{out}/{L}"
    IO.FS.writeFile s!"{out}/{L}/Data.lean" s!"import Noperts.Stellated.KernelLoad

open Noperts.Stellated Noperts.Stellated.AtlasProjectiveLocalViewTree

set_option Elab.async false

namespace Noperts.Stellated.LocalK

stellated_local_tree \"{absDir}/local-{pad2 idx}.pack\" {idx} {t}
-- data hash {hash packed} (the loaded file is not tracked by Lake)

noncomputable def {t}.get (i : ℕ) : Row := LocalKernel.Tree8.get {t}.depth {t}.tree i

end Noperts.Stellated.LocalK
"
    let parts := (List.range ((starts.size + part - 1) / part)).map fun k =>
      (starts.toList.drop (k * part)).take part
    for (k, ps) in (List.range parts.length).zip parts do
      let body := String.join (ps.map fun (st, c) =>
        s!"theorem {t}.r{st} : RowsValidRangeAt {t}.sym {t}.r {t}.get {t}.size {st} {c} := by\n  decide +kernel\n\n")
      IO.FS.writeFile s!"{out}/{L}/P{k}.lean" s!"import StellatedKernel.Local.{L}.Data

open Noperts.Stellated Noperts.Stellated.AtlasProjectiveLocalViewTree

set_option Elab.async false

namespace Noperts.Stellated.LocalK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

{body}end Noperts.Stellated.LocalK
"
    let partImports := "\n".intercalate ((List.range parts.length).map fun k =>
      s!"import StellatedKernel.Local.{L}.P{k}")
    -- chain the slices
    let mut chain := s!"{t}.r0"
    for (st, _) in starts.toList.drop 1 do
      chain := s!"(rowsValidRange_append {chain} {t}.r{st})"
    let tri := s!"PackedLocalViewTree.depth3Triangle {idx}"
    IO.FS.writeFile s!"{out}/L{pad2 idx}.lean" s!"{partImports}
import StellatedKernel.Chart.Headers

open Noperts.Stellated Noperts.Stellated.AtlasProjectiveLocalViewTree
open Noperts.Stellated.ChartKernelTree

set_option Elab.async false

namespace Noperts.Stellated.LocalK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem {t}.rows : RowsValidAt {t}.sym {t}.r {t}.get {t}.size :=
  rowsValidAt_of_range {chain}

noncomputable def {t}.table : Table where
  symmetryIndex := {t}.sym
  r := {t}.r
  root := 0
  triangle := {tri}
  get := {t}.get
  size := {t}.size

theorem {t}.valid : {t}.table.Valid :=
  ⟨by decide +kernel, {t}.rows, by decide +kernel, by decide +kernel⟩

theorem {t}.covered (h : Header) (hh : ChartK.headers ⟨{idx}, by decide⟩ = some h) :
    LocalCovered h := by
  have e1 : (ChartK.headers ⟨{idx}, by decide⟩).map Header.symmetryIndex = some {t}.sym := by
    decide +kernel
  have e2 : (ChartK.headers ⟨{idx}, by decide⟩).map Header.r = some {t}.r := by decide +kernel
  have e3 : (ChartK.headers ⟨{idx}, by decide⟩).map Header.root = some 0 := by decide +kernel
  have e4 : (ChartK.headers ⟨{idx}, by decide⟩).map Header.triangle = some ({tri}) := by
    decide +kernel
  rw [hh] at e1 e2 e3 e4
  obtain ⟨s, r, root, tri⟩ := h
  simp only [Option.map_some, Option.some.injEq] at e1 e2 e3 e4
  subst e1 e2 e3 e4
  exact localCovered_of_table {t}.table {t}.valid

end Noperts.Stellated.LocalK
"
    IO.println s!"table {idx}: {n} rows, {starts.size} slices, {parts.length} parts"
  let imports := present.toList.map fun idx => s!"import StellatedKernel.Local.L{pad2 idx}"
  let cases := (List.range 64).map fun idx =>
    if present.contains idx then s!"  · exact t{pad2 idx}.covered h hh"
    else "  · simp [ChartK.headers, ChartK.headerList] at hh"
  IO.FS.writeFile s!"{out}/Assembly.lean" s!"{"\n".intercalate imports}

open Noperts.Stellated Noperts.Stellated.ChartKernelTree

namespace Noperts.Stellated.LocalK

theorem headers_covered : HeadersCovered ChartK.headers := by
  intro idx h hh
  fin_cases idx
{"\n".intercalate cases}

end Noperts.Stellated.LocalK
"
  IO.println s!"{present.size} tables"
