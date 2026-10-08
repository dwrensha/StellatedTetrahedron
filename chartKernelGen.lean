import Noperts.Stellated.PackedSolutionTree
import Noperts.Stellated.PackedLocalViewTree
import Noperts.Stellated.PackedCTree
import Noperts.Stellated.ChartKernelMixed
import Std.Data.HashMap

/-!
Generator for the kernel chart tree (not part of the proof).

`chartKernelGen DIR OUT BUDGET_MS MODULE_MS` reads `DIR/chart0.pack` and the
`DIR/local-NN.pack` headers, converts the chart table into a recursive
`ChartKernelTree.CTree` (with generator hints for the integer leaf checkers),
validates it natively, cuts it into chunks of estimated kernel cost about
`BUDGET_MS`, groups chunks into modules of about `MODULE_MS`, and writes
`OUT/data/M<k>.ct`, `OUT/M<k>.lean`, `OUT/Headers.lean` and `OUT/Assembly.lean`.
-/

open Noperts.Stellated
open Noperts.Stellated.AtlasProjectiveSolutionTree
open Noperts.Stellated.ChartKernelTree

instance : Inhabited CTree := ⟨.corner⟩

partial def build (get : ℕ → Row) (i : ℕ) : CTree :=
  match get i with
  | .cayleySplit _ lo hi c _ _ => .cayleySplit c (build get lo) (build get hi)
  | .viewRoot _ child _ => .viewRoot (build get child)
  | .viewSplit _ ch _ _ _ =>
      .viewSplit (build get (ch 0)) (build get (ch 1)) (build get (ch 2)) (build get (ch 3))
  | .viewCut _ ch _ _ _ w =>
      let sub := fun k => if 0 < w k then build get (ch k) else .octahedron
      .viewCut w (sub 0) (sub 1) (sub 2)
  | .projective _ b =>
      .projective ⟨b.edgePred, b.outerIndex, b.innerIndex, b.nonzeroWitness, b.ballMultiplier⟩
        (ChartKernel.defectHints b)
  | .projectiveGlobal _ b =>
      .global ⟨b.certificate, b.innerIndex, b.ballMultiplier⟩ (ChartKernelG.globalHints b)
  | .projectiveMixedGlobal _ b =>
      .mixed ⟨b.component, b.weight⟩ (ChartKernelM.mixedHints b)
  | .projectiveLocal _ b => .projectiveLocal ⟨b.symmetryIndex, b.certificate, b.c, b.δ, b.r⟩
  | .symmetryTube _ tube idx _ within => .tube tube.symmetryIndex tube.r idx within
  | .octahedronPrune .. => .octahedron
  | .flipPrune _ b => .flip b.form b.negate
  | .corner .. => .corner
  | .symmetryLocal .. => .hole []  -- unsupported (absent from the table): fails the check

/-- Row ids at depth `d` below row `i` (fewer if leaves come first). -/
partial def rowFrontier (get : ℕ → Row) (i d : ℕ) (acc : Array ℕ) : Array ℕ :=
  if d = 0 then acc.push i else
  match get i with
  | .cayleySplit _ lo hi _ _ _ => rowFrontier get hi (d - 1) (rowFrontier get lo (d - 1) acc)
  | .viewRoot _ child _ => rowFrontier get child (d - 1) acc
  | .viewSplit _ ch _ _ _ =>
      rowFrontier get (ch 3) (d - 1) (rowFrontier get (ch 2) (d - 1)
        (rowFrontier get (ch 1) (d - 1) (rowFrontier get (ch 0) (d - 1) acc)))
  | _ => acc.push i

/-- `build` with the subtrees at depth `d` taken from `done`. -/
partial def buildTop (get : ℕ → Row) (done : Std.HashMap ℕ CTree) (i d : ℕ) : CTree :=
  if d = 0 then done.getD i .corner else
  match get i with
  | .cayleySplit _ lo hi c _ _ => .cayleySplit c (buildTop get done lo (d - 1))
      (buildTop get done hi (d - 1))
  | .viewRoot _ child _ => .viewRoot (buildTop get done child (d - 1))
  | .viewSplit _ ch _ _ _ =>
      .viewSplit (buildTop get done (ch 0) (d - 1)) (buildTop get done (ch 1) (d - 1))
        (buildTop get done (ch 2) (d - 1)) (buildTop get done (ch 3) (d - 1))
  | _ => done.getD i .corner

/-- Estimated kernel cost (ms) of a node itself. -/
def nodeCost : CTree → ℕ
  | .cayleySplit .. => 3
  | .viewRoot _ => 1
  | .viewSplit .. => 15
  | .viewCut .. => 15
  | .projective .. => 65
  | .global .. => 135
  | .mixed .. => 550
  | .projectiveLocal _ => 300
  | .tube .. => 500
  | .octahedron => 5
  | .flip .. => 60
  | .corner => 30
  | .hole _ => 5

@[noinline] def matTri (t : Triangle) : Triangle :=
  PackedLocalViewTree.triangleOfArray (PackedLocalViewTree.triangleArray t)

def matReg : Region → Region
  | .triangle r t => .triangle r (matTri t)
  | .sphere => .sphere

@[noinline] def matIv (iv : Interval) : Interval :=
  ⟨⟨⟨iv.min.θ, iv.min.φ, iv.min.x, iv.min.y, iv.min.z⟩,
    ⟨iv.max.θ, iv.max.φ, iv.max.x, iv.max.y, iv.max.z⟩⟩, iv.2⟩

/-- `CTree.check` with materialized frames (native validation only). -/
partial def checkN (hdr : Fin 64 → Option Header) (iv : Interval) (reg : Region) : CTree → Bool
  | .cayleySplit c lo hi =>
      checkN hdr (matIv (iv.lowerHalf c)) reg lo && checkN hdr (matIv (iv.upperHalf c)) reg hi
  | .viewRoot child => checkN hdr iv (.triangle 0 AtlasProjectiveView.chamberTriangle) child
  | .viewSplit a b c d =>
      match reg with
      | .triangle root tri =>
          let sub := fun k x => checkN hdr iv (.triangle root (matTri (Noperts.ProjectiveView.split tri k))) x
          sub 0 a && sub 1 b && sub 2 c && sub 3 d
      | .sphere => false
  | .viewCut w a b c =>
      match reg with
      | .triangle root tri =>
          let sub := fun k x => !decide (0 < w k) ||
            checkN hdr iv (.triangle root (matTri (AtlasProjectiveLocalViewTree.cutTriangle tri w k))) x
          decide ((∀ j, 0 ≤ w j) ∧ w 0 + w 1 + w 2 = 1) && sub 0 a && sub 1 b && sub 2 c
      | .sphere => false
  | .octahedron => decide iv.outsideOctahedron
  | .hole _ => false
  | t =>
      match reg with
      | .triangle root tri => leafOk hdr 0 iv root tri t
      | .sphere => false

/-- Validate in parallel: spawn tasks for the subtrees at the given depth. -/
partial def collect (iv : Interval) (reg : Region) (t : CTree) (d : ℕ)
    (acc : Array (Interval × Region × CTree)) : Array (Interval × Region × CTree) :=
  if d = 0 then acc.push (iv, reg, t) else
  match t, reg with
  | .cayleySplit c lo hi, _ =>
      collect (matIv (iv.upperHalf c)) reg hi (d - 1)
        (collect (matIv (iv.lowerHalf c)) reg lo (d - 1) acc)
  | .viewRoot child, _ => collect iv (.triangle 0 AtlasProjectiveView.chamberTriangle) child d acc
  | .viewSplit a b c e, .triangle root tri =>
      let f := fun k => Region.triangle root (matTri (Noperts.ProjectiveView.split tri k))
      collect iv (f 3) e (d - 1) (collect iv (f 2) c (d - 1)
        (collect iv (f 1) b (d - 1) (collect iv (f 0) a (d - 1) acc)))
  | _, _ => acc.push (iv, reg, t)

/-! ## Chunking -/

structure Chunk where
  id : ℕ
  path : List Step
  tree : CTree
  cost : ℕ

/-- Returns the tree with large subtrees replaced by holes, its residual cost,
and appends the cut chunks (post-order) to the state. -/
partial def chunkify (budget : ℕ) (path : List Step) (reg : Region) (t : CTree) :
    StateM (Array Chunk) (CTree × ℕ) := do
  let sub := fun (st : Step) (r : Region) (x : CTree) => do
    let (x', c) ← chunkify budget (path ++ [st]) r x
    if c ≥ budget then
      let id := (← get).size
      modify (·.push ⟨id, path ++ [st], x', c⟩)
      pure (CTree.hole (path ++ [st]), 5)
    else pure (x', c)
  match t, reg with
  | .cayleySplit c lo hi, _ =>
      let (lo', a) ← sub (.half c false) reg lo
      let (hi', b) ← sub (.half c true) reg hi
      pure (.cayleySplit c lo' hi', a + b + nodeCost t)
  | .viewRoot child, _ =>
      let (c', a) ← sub .root (.triangle 0 AtlasProjectiveView.chamberTriangle) child
      pure (.viewRoot c', a + nodeCost t)
  | .viewSplit x0 x1 x2 x3, .triangle root tri =>
      let f := fun k => Region.triangle root (matTri (Noperts.ProjectiveView.split tri k))
      let (y0, a0) ← sub (.view 0) (f 0) x0
      let (y1, a1) ← sub (.view 1) (f 1) x1
      let (y2, a2) ← sub (.view 2) (f 2) x2
      let (y3, a3) ← sub (.view 3) (f 3) x3
      pure (.viewSplit y0 y1 y2 y3, a0 + a1 + a2 + a3 + nodeCost t)
  | .viewCut w x0 x1 x2, .triangle root tri =>
      let f := fun k => Region.triangle root
        (matTri (AtlasProjectiveLocalViewTree.cutTriangle tri w k))
      let (y0, a0) ← if 0 < w 0 then sub (.cut w 0) (f 0) x0 else pure (x0, 0)
      let (y1, a1) ← if 0 < w 1 then sub (.cut w 1) (f 1) x1 else pure (x1, 0)
      let (y2, a2) ← if 0 < w 2 then sub (.cut w 2) (f 2) x2 else pure (x2, 0)
      pure (.viewCut w y0 y1 y2, a0 + a1 + a2 + nodeCost t)
  | _, _ => pure (t, nodeCost t)

/-! ## Emission -/

def qS (q : ℚ) : String := s!"({q.num} / {q.den} : ℚ)"

def headerS : Option Header → String
  | none => "none"
  | some h =>
      let tri := "![" ++ ", ".intercalate ((List.finRange 3).map fun j =>
        "![" ++ ", ".intercalate ((List.finRange 3).map fun c => qS (h.triangle j c)) ++ "]") ++ "]"
      s!"some ⟨{h.symmetryIndex.val}, {qS h.r}, {h.root.val}, {tri}⟩"

def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

def stepsKey (l : List Step) : String :=
  (do for s in l do PackedCTree.putStep s : PackedCTree.EncM Unit).run {} |>.2.out.toList.toString

/-- Proof of `∀ x ∈ holeList, NoRupert …` from the children's assembly theorems, as a
right-nested chain of `holes_cons` ending in `holes_nil`; linear in the number of holes. -/
def holesProof (ids : List ℕ) : String :=
  ids.foldr (fun i acc => s!"(holes_cons (a{i} hhdr hcorner) {acc})") "holes_nil"

def main (args : List String) : IO Unit := do
  let (dir, out, budget, moduleBudget, validate) ← match args with
    | [d, o, b, m] => pure (d, o, b.toNat!, m.toNat!, true)
    | [d, o, b, m, "novalidate"] => pure (d, o, b.toNat!, m.toNat!, false)
    | _ => throw (IO.userError "expects DIR OUT BUDGET_MS MODULE_MS [novalidate]")
  -- local table headers
  let mut headers : Array (Option Header) := #[]
  for index in List.range 64 do
    let path := s!"{dir}/local-{pad2 index}.pack"
    if ← System.FilePath.pathExists path then
      let table := PackedLocalViewTree.decodePackedTable index (← IO.FS.readFile path)
      headers := headers.push (some ⟨table.symmetryIndex, table.r, table.root, table.triangle⟩)
    else headers := headers.push none
  let hdr : Fin 64 → Option Header := fun i => headers[i.val]!
  let log := fun (m : String) => do IO.eprintln m; (← IO.getStderr).flush
  log "headers done"
  let table := PackedSolutionTree.decodeTable 0 (fun _ => none) (← IO.FS.readFile s!"{dir}/chart0.pack")
  log s!"decoded {table.size} rows"
  let ids := rowFrontier table.get 0 12 #[]
  log s!"building {ids.size} subtrees in parallel"
  let tasks := ids.map fun i => Task.spawn (prio := .dedicated) fun _ => (i, build table.get i)
  let mut done : Std.HashMap ℕ CTree := {}
  let mut nd := 0
  for tk in tasks do
    let (i, x) := tk.get
    done := done.insert i x
    nd := nd + 1
    if nd % 500 == 0 then log s!"built {nd}/{ids.size}"
  let t := buildTop table.get done 0 12
  log s!"built tree from {table.size} rows"
  -- native validation
  let root := AtlasPose.rootInterval ℚ
  let parts := if validate then collect root .sphere t 14 #[] else #[]
  log s!"validating {parts.size} subtrees"
  let tasks := parts.map fun (iv, reg, x) =>
    Task.spawn fun _ => checkN hdr iv reg x
  let mut bad := 0
  for tk in tasks do
    unless tk.get do bad := bad + 1
  IO.println s!"native validation: {parts.size - bad}/{parts.size} subtrees pass"
  if bad > 0 then throw (IO.userError "validation failed")
  -- chunking
  let ((top, topCost), chunks) := (chunkify budget [] .sphere t).run #[]
  let chunks := chunks.push ⟨chunks.size, [], top, topCost⟩
  IO.println s!"{chunks.size} chunks"
  -- modules
  IO.FS.createDirAll s!"{out}/data"
  let mut modules : Array (Array Chunk) := #[]
  let mut cur : Array Chunk := #[]
  let mut curCost := 0
  for c in chunks do
    cur := cur.push c
    curCost := curCost + c.cost
    if curCost ≥ moduleBudget then
      modules := modules.push cur; cur := #[]; curCost := 0
  if cur.size > 0 then modules := modules.push cur
  IO.println s!"{modules.size} modules"
  let mut moduleOf : Array ℕ := Array.replicate chunks.size 0
  for k in List.range modules.size do
    let ms := modules[k]!
    for c in ms do moduleOf := moduleOf.set! c.id k
    let dataS := PackedCTree.encodeChunks (ms.toList.map fun c => (c.id, c.path, c.tree))
    IO.FS.writeFile s!"{out}/data/M{k}.ct" dataS
    let thms := ms.toList.map fun c =>
      s!"theorem m{k}.c{c.id}.ok (hhdr : HeadersCovered headers) (hcorner : CornerCovered)
    (hh : ∀ x ∈ m{k}.c{c.id}.holeList, NoRupert 0 (framePath x).1 (framePath x).2) :
    NoRupert 0 (framePath m{k}.c{c.id}.steps).1 (framePath m{k}.c{c.id}.steps).2 :=
  chunk_sound headers hhdr hcorner _ m{k}.c{c.id}.tree (by decide +kernel)
    (holes_of m{k}.c{c.id}.holes_eq hh)
"
    IO.FS.writeFile s!"{out}/M{k}.lean" s!"import Noperts.Stellated.KernelLoadChart
import StellatedKernel.Chart.Headers

open Noperts.Stellated Noperts.Stellated.ChartKernelTree
open Noperts.Stellated.AtlasProjectiveSolutionTree

-- synchronous elaboration frees each chunk's kernel state before the next (20 → 13 GB peak)
set_option Elab.async false

namespace Noperts.Stellated.ChartK

stellated_ctree_chunks \"{out}/data/M{k}.ct\" m{k}
-- data hash {hash dataS} (the loaded file is not tracked by Lake)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

{"\n".intercalate thms}
end Noperts.Stellated.ChartK
"
  -- headers
  IO.FS.writeFile s!"{out}/Headers.lean" s!"import Noperts.Stellated.ChartKernelTree

open Noperts.Stellated Noperts.Stellated.ChartKernelTree

namespace Noperts.Stellated.ChartK

def headerList : List (Option Header) := [
  {",\n  ".intercalate (headers.toList.map headerS)}]

def headers (i : Fin 64) : Option Header := headerList.getD i.val none

end Noperts.Stellated.ChartK
"
  -- assembly: post-order, children before parents
  let mut idOf : Std.HashMap String ℕ := {}
  for c in chunks do idOf := idOf.insert (stepsKey c.path) c.id
  let thms := chunks.toList.map fun c =>
    let k := moduleOf[c.id]!
    let ids := c.tree.holes.map fun p => idOf.getD (stepsKey p) 0
    s!"theorem a{c.id} (hhdr : HeadersCovered headers) (hcorner : CornerCovered) :
    NoRupert 0 (framePath m{k}.c{c.id}.steps).1 (framePath m{k}.c{c.id}.steps).2 :=
  m{k}.c{c.id}.ok hhdr hcorner {holesProof ids}
"
  let imports := (List.range modules.size).map fun k => s!"import StellatedKernel.Chart.M{k}"
  IO.FS.writeFile s!"{out}/Assembly.lean" s!"{"\n".intercalate imports}

open Noperts.Stellated Noperts.Stellated.ChartKernelTree
open Noperts.Stellated.AtlasProjectiveSolutionTree

set_option Elab.async false

namespace Noperts.Stellated.ChartK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! One theorem per chunk, children first, so each step elaborates in a small context. -/

theorem holes_nil : ∀ x ∈ ([] : List (List Step)), NoRupert 0 (framePath x).1 (framePath x).2 :=
  fun _ h => nomatch h

theorem holes_cons \{a : List Step} \{l : List (List Step)}
    (ha : NoRupert 0 (framePath a).1 (framePath a).2)
    (hl : ∀ x ∈ l, NoRupert 0 (framePath x).1 (framePath x).2) :
    ∀ x ∈ a :: l, NoRupert 0 (framePath x).1 (framePath x).2 := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact hl x hx

{"\n".intercalate thms}
theorem chart_root (hhdr : HeadersCovered headers) (hcorner : CornerCovered) :
    NoRupert 0 (AtlasPose.rootInterval ℚ) .sphere :=
  a{chunks.size - 1} hhdr hcorner

end Noperts.Stellated.ChartK
"
  IO.println "done"
