module

public import Noperts.Stellated.IsNotRupert
public import Noperts.Stellated.PackedSolutionTree

@[expose] public section

/-!
# Native executable proof construction for the stellated tetrahedron

A release-mode program checks the data-only local and global tables with
native worker tasks and keeps the kernel-proved validity witnesses in `PLift`.
The result of a successful run is a value of the public proposition
`¬ IsRupert exactVerts`.  As with `native_decide`, the trust base includes the
Lean compiler.
-/

namespace Noperts.Stellated.NativeExecutable

open AtlasProjectiveLocalViewTree

def log (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

/-! ## Parallel local-table checker -/

def localIxB (table : AtlasProjectiveLocalViewTree.Table) (i : ℕ) : Bool :=
  if i < table.size then
    decide ((table.get i).id = i ∧
      (table.get i).ValidAt table.symmetryIndex table.r table.get table.size)
  else true

def localTableValidParB (table : AtlasProjectiveLocalViewTree.Table)
    (taskCount : ℕ) : Bool :=
  decide (0 < table.size ∧ (table.get 0).root = table.root ∧
      (table.get 0).triangle = table.triangle) &&
    Noperts.ParallelBool.allParB (localIxB table) table.size taskCount

theorem localTable_valid_of_parB {table : AtlasProjectiveLocalViewTree.Table}
    {taskCount : ℕ} (h : localTableValidParB table taskCount = true) :
    table.Valid := by
  unfold localTableValidParB at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨⟨hsize, hroot, htriangle⟩, hrows⟩ := h
  refine ⟨hsize, ?_, hroot, htriangle⟩
  intro i
  have hi := Noperts.ParallelBool.all_of_parB hrows i.val i.isLt
  unfold localIxB at hi
  rw [ite_eq_left i.isLt, decide_eq_true_iff] at hi
  exact hi

def optionalLocalB (taskCount : ℕ) :
    Option AtlasProjectiveLocalViewTree.Table → Bool
  | none => true
  | some table => localTableValidParB table taskCount

theorem optionalLocal_of_B {taskCount : ℕ}
    {table : Option AtlasProjectiveLocalViewTree.Table}
    (h : optionalLocalB taskCount table = true) :
    AtlasProjectiveSolutionTree.OptionalLocalValid table := by
  cases table with
  | none => trivial
  | some table => exact localTable_valid_of_parB h

def sharedLocalB (taskCount : ℕ)
    (shared : AtlasProjectiveSolutionTree.SharedLocalTables) : Bool :=
  (List.finRange 64).all fun index => optionalLocalB taskCount (shared index)

theorem sharedLocal_of_B {taskCount : ℕ}
    {shared : AtlasProjectiveSolutionTree.SharedLocalTables}
    (h : sharedLocalB taskCount shared = true) :
    AtlasProjectiveSolutionTree.SharedLocalValid shared := by
  intro index
  unfold sharedLocalB at h
  rw [List.all_eq_true] at h
  exact optionalLocal_of_B (h index (List.mem_finRange index))

/-- Check the listed shared local tables one at a time, logging each, and
return the validity proof for exactly the tables checked. -/
def checkSharedList (taskCount : ℕ)
    (shared : AtlasProjectiveSolutionTree.SharedLocalTables) :
    (l : List (Fin 64)) →
      IO (PLift (∀ i ∈ l, AtlasProjectiveSolutionTree.OptionalLocalValid (shared i)))
  | [] => pure ⟨by simp⟩
  | index :: rest => do
      let start ← IO.monoNanosNow
      if h : optionalLocalB taskCount (shared index) = true then
        let finish ← IO.monoNanosNow
        match shared index with
        | none => pure ()
        | some table =>
            log s!"valid local table {index}: {table.size} rows ({(finish - start) / 1000000} ms)"
        let ⟨hrest⟩ ← checkSharedList taskCount shared rest
        pure ⟨by
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact optionalLocal_of_B h
          · exact hrest j hj⟩
      else
        throw (IO.userError s!"local table {index} is not valid")

/-- Check all shared local tables, reporting per-table results. -/
def checkShared (taskCount : ℕ)
    (shared : AtlasProjectiveSolutionTree.SharedLocalTables) :
    IO (PLift (AtlasProjectiveSolutionTree.SharedLocalValid shared)) := do
  let start ← IO.monoNanosNow
  let ⟨h⟩ ← checkSharedList taskCount shared (List.finRange 64)
  let finish ← IO.monoNanosNow
  log s!"valid shared local tables: {(finish - start) / 1000000} ms"
  pure ⟨fun index => h index (List.mem_finRange index)⟩

/-- Check the chart-0 table after attaching the checked shared tables. -/
def checkGlobal (taskCount : ℕ) (table : AtlasProjectiveSolutionTree.Table)
    (hshared : AtlasProjectiveSolutionTree.SharedLocalValid table.sharedLocal) :
    IO (PLift table.Valid) := do
  let start ← IO.monoNanosNow
  log s!"checking chart 0: {table.size} rows in {taskCount} native tasks"
  let chunkSize := table.size / taskCount + 1
  let tasks := AtlasProjectiveSolutionTree.tableCoreTasks table taskCount
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    unless valid do
      let first := index * chunkSize
      throw (IO.userError (s!"chart 0 is invalid in rows " ++
        s!"[{first}, {min table.size (first + chunkSize)})"))
    completed := completed + 1
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log s!"chart 0: {completed}/{total} tasks ({(now - start) / 1000000} ms)"
  if h : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
      table taskCount tasks = true then
    have h' : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
        table taskCount
        (AtlasProjectiveSolutionTree.tableCoreTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨AtlasProjectiveSolutionTree.Table.Valid.of_withTasksB hshared h'⟩
  else
    throw (IO.userError "chart 0 table is not valid")

/-- Check the corner blow-up tables. -/
def checkCorner (taskCount : ℕ) (tables : CornerCoverage.Tables) :
    IO (PLift AtlasProjectiveSolutionTree.CornerCovered) := do
  let start ← IO.monoNanosNow
  if h : tables.ValidPar AtlasProjectiveSolutionTree.cornerEps taskCount then
    let finish ← IO.monoNanosNow
    log s!"valid corner tables: {(finish - start) / 1000000} ms"
    pure ⟨CornerCoverage.Tables.covered _ tables (CornerCoverage.Tables.Valid.of_par h)⟩
  else
    throw (IO.userError "corner tables are not valid")

/-- Check all certificate data and construct the final non-Rupert proof. -/
def constructProof (localTaskCount globalTaskCount : ℕ)
    (corner : CornerCoverage.Tables)
    (shared : AtlasProjectiveSolutionTree.SharedLocalTables)
    (globalTable : AtlasProjectiveSolutionTree.SharedLocalTables →
      AtlasProjectiveSolutionTree.Table)
    (hchart : ∀ s, (globalTable s).chart = 0)
    (hshared : ∀ s, (globalTable s).sharedLocal = s) :
    IO (PLift (¬ IsRupert exactVerts)) := do
  let cornerValid ← checkCorner localTaskCount corner
  let sharedValid ← checkShared localTaskCount shared
  let table := globalTable shared
  have hsharedTable : AtlasProjectiveSolutionTree.SharedLocalValid
      table.sharedLocal := by
    rw [hshared shared]
    exact sharedValid.down
  let valid ← checkGlobal globalTaskCount table hsharedTable
  log "constructed proof: the stellated tetrahedron P_{11/20} is not Rupert"
  pure ⟨not_rupert_of_valid_table table (hchart shared) valid.down cornerValid.down⟩

end Noperts.Stellated.NativeExecutable

end
