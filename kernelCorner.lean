import Noperts.Stellated.NativeExecutable
import Noperts.Stellated.PackedCornerTree
import Noperts.Stellated.CornerKernelTree
import Noperts.Stellated.PackedKTree
import Noperts.Stellated.FlipPolysBase

/-!
Convert corner tables for the kernel: give each shared fact its polynomial
data (`CornerKernel.FactPoly`), turn shared leaves that pass the packed cheap
bound into `Leaf.sharedP`, and refine the others by splitting.

`kernelCorner stats IN.pack DEPTH [TABLES...]`
-/

open Noperts.Stellated
open Noperts.Stellated.CornerTree CornerCertificate CornerPoly PackedCornerTree SparsePoly
open Noperts.Stellated.CornerKernel

instance : Inhabited Row := ⟨⟨false, .plain, [], [], ⟨fun _ _ => 0, fun _ => 0, fun _ => 0⟩, [], [], []⟩⟩
instance : Inhabited FactPoly := ⟨⟨[], [], 1⟩⟩
instance : Inhabited IFrame := ⟨⟨false, .plain, 1, [], []⟩⟩

def factPoly (fact : Row) : FactPoly :=
  let F := normalize (divByMono fact.D [1])
  let m := gcdMono fact.nonnegVars F
  let S := divByMono F m
  let K := S.foldl (fun acc t => Nat.lcm acc t.2.den) 1
  ⟨S.map fun t => let c := (t.2 * (K : ℚ)).num; (t.1, c.natAbs, decide (c < 0)), m, K⟩

def frameRow (f : Frame) (r : Row) : Row := { r with center := f.center, radius := f.radius }

/-- Refine a row by splitting until every piece passes, up to `depth` levels:
returns the split plan as a tree of frames, or `none`. -/
inductive Plan where
  | leaf
  | split (v : ℕ) (m : ℚ) (lo hi : Plan)

partial def refine (fact : Row) (fp : FactPoly) (f : Frame) (r : Row) (depth : ℕ) :
    Option Plan :=
  if decide (SharedPValid (frameRow f r) fact fp) then some .leaf
  else if depth = 0 then none
  else
    let vars := ((List.range f.radius.length).filter fun v => f.radius.getD v 0 > 0)
    let ranked := vars.mergeSort fun a b => f.radius.getD a 0 ≥ f.radius.getD b 0
    let tries := if depth ≥ 2 then ranked.take 2 else ranked
    tries.findSome? fun v =>
      let m := f.center.getD v 0
      match refine fact fp (f.lower v m) r (depth - 1) with
      | none => none
      | some pl => (refine fact fp (f.upper v m) r (depth - 1)).map (.split v m pl)

def Plan.leaves : Plan → ℕ
  | .leaf => 1
  | .split _ _ a b => a.leaves + b.leaves

def kindCode : ChartKind → Nat
  | .plain => 0 | .tube => 1 | .wedge => 2 | .wtube => 3 | .skew => 4 | .atube => 5
  | .btube false => 6 | .btube true => 7 | .askew => 8 | .bskew false => 9
  | .bskew true => 10 | .aplain => 11 | .bplain false => 12 | .bplain true => 13

def stats (tables : Array Table) (depth : ℕ) (index : ℕ) : IO Unit := do
  let t := tables[index]!
  let fps := t.facts.map factPoly
  let mut okFacts := 0
  for k in List.range fps.size do
    if decide (fps[k]!.Ok t.facts[k]!) then okFacts := okFacts + 1
  let mut direct := 0
  let mut refined := 0
  let mut extraLeaves := 0
  let mut failed := 0
  for j in List.range t.size do
    if let .leaf _ f (.shared r k) := t.get j then
      match refine t.facts[k]! fps[k]! f r depth with
      | some .leaf => direct := direct + 1
      | some pl => refined := refined + 1; extraLeaves := extraLeaves + pl.leaves - 1
      | none =>
          failed := failed + 1
          IO.println s!"FAIL t{index} split {r.split.length} shift {(r.shift.filter (· != 0)).length} rhoface {r.isTube && decide (r.lo 6 ≤ 0)} kind {kindCode r.kind}"
  IO.println s!"table {index}: facts {fps.size} (poly ok {okFacts}); shared leaves: direct {direct}, refined {refined} (+{extraLeaves} leaves), failed {failed}"
  (← IO.getStdout).flush

def shiftPairs (tables : Array Table) : IO Unit := do
  let mut pairs : Std.HashSet String := {}
  let mut n := 0
  for index in List.range tables.size do
    let t := tables[index]!
    for j in List.range t.size do
      if let .leaf _ _ (.shared r k) := t.get j then
        if r.shift.any (· != 0) then
          n := n + 1
          pairs := pairs.insert s!"{index}/{k}/{r.shift}"
  IO.println s!"{n} shifted shared leaves, {pairs.size} distinct (table, fact, shift)"

/-! ## Writing format v3 -/

def zig (z : Int) : Nat := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

def ratT (q : ℚ) : Array Nat := #[zig q.num, q.den]

def handoffCode : Handoff → Nat
  | .tube => 0 | .wedge => 1 | .wtube => 2 | .skew => 3 | .cone => 4 | .pocket => 5
  | .spocket => 6 | .ppocket => 7 | .cpocket => 8

def frameT (f : Frame) : Array Nat :=
  #[if f.seg then 1 else 0, kindCode f.kind, f.center.length] ++
    (f.center.foldl (fun a q => a ++ ratT q) #[]) ++
    (f.radius.foldl (fun a q => a ++ ratT q) #[]) ++ #[f.aff.length] ++
    (f.aff.foldl (fun a row => row.foldl (fun b q => b ++ ratT q) a) #[])

def tripleT (t : Triple) : Array Nat :=
  ((List.range 9).foldl (fun a n =>
      a ++ ratT (t.edge ⟨n / 3 % 3, by omega⟩ ⟨n % 3, by omega⟩)) #[]) ++
    #[(t.inner 0).val, (t.inner 1).val, (t.inner 2).val,
      (t.outer 0).val, (t.outer 1).val, (t.outer 2).val]

def splitT (sp : List (ℕ × Bool)) : Array Nat :=
  sp.foldl (fun a p => a ++ #[p.1, if p.2 then 1 else 0]) #[sp.length]

def shiftT (sh : List ℚ) : Array Nat := sh.foldl (fun a q => a ++ ratT q) #[sh.length]

def monoT (m : List ℕ) : Array Nat := #[m.length] ++ m.toArray

def factPolyT (fp : FactPoly) : Array Nat :=
  fp.S.foldl (fun a t => a ++ monoT t.1 ++ #[t.2.1, if t.2.2 then 1 else 0]) #[fp.S.length] ++
    monoT fp.m ++ #[fp.K]

def nodeT (n : Node) : Array Nat :=
  match n with
  | .split id f v m lo hi => #[0, id] ++ frameT f ++ #[v] ++ ratT m ++ #[lo, hi]
  | .stellar id f i j α β lo hi =>
      #[5, id] ++ frameT f ++ #[i, j] ++ ratT α ++ ratT β ++ #[lo, hi]
  | .leaf id f (.flip k) => #[2, id] ++ frameT f ++ #[k.val]
  | .leaf id f (.handoff h) => #[3, id] ++ frameT f ++ #[handoffCode h]
  | .leaf id f (.shared r k) => #[6, id] ++ frameT f ++ #[k] ++ splitT r.split ++ shiftT r.shift
  | .leaf id f (.sharedP r k) => #[7, id] ++ frameT f ++ #[k] ++ splitT r.split ++ shiftT r.shift
  | .leaf id f (.cert r) =>
      if r.shift.isEmpty then #[1, id] ++ frameT f ++ tripleT r.triple ++ splitT r.split
      else #[4, id] ++ frameT f ++ tripleT r.triple ++ splitT r.split ++ shiftT r.shift

/-- Emit the leaves of a refinement plan for frame `f` at node `id`, appending
new nodes to `nodes`. -/
partial def emitPlan (r : Row) (k : ℕ) (nodes : Array Node) (id : ℕ) (f : Frame) :
    Plan → Array Node
  | .leaf => nodes.set! id (.leaf id f (.sharedP (frameRow f r) k))
  | .split v m lo hi =>
      let li := nodes.size
      let ui := nodes.size + 1
      let nodes := nodes.set! id (.split id f v m li ui)
      let nodes := nodes.push default |>.push default
      let nodes := emitPlan r k nodes li (f.lower v m) lo
      emitPlan r k nodes ui (f.upper v m) hi

structure ConvStats where
  direct : ℕ := 0
  refined : ℕ := 0
  failed : ℕ := 0

def convertTable (t : Table) (depth : ℕ) : Table × ConvStats := Id.run do
  let fps := t.facts.map factPoly
  let mut nodes : Array Node := (List.range t.size).toArray.map t.get
  let mut st : ConvStats := {}
  for j in List.range t.size do
    if let .leaf _ f (.shared r k) := t.get j then
      match refine t.facts[k]! fps[k]! f r depth with
      | some .leaf =>
          st := { st with direct := st.direct + 1 }
          nodes := nodes.set! j (.leaf j f (.sharedP (frameRow f r) k))
      | some pl =>
          st := { st with refined := st.refined + 1 }
          nodes := emitPlan r k nodes j f pl
      | none => st := { st with failed := st.failed + 1 }
  let arr := nodes
  return ({ get := fun i => arr[i]!, size := arr.size, facts := t.facts, fpolys := fps }, st)

def tableT (t : Table) : Array Nat := Id.run do
  let mut out : Array Nat := #[t.facts.size]
  for f in t.facts do
    out := out ++ frameT ⟨f.seg, f.kind, f.center, f.radius, f.aff⟩ ++ tripleT f.triple
  for fp in t.fpolys do
    out := out ++ factPolyT fp
  out := out.push t.size
  for k in List.range t.size do
    out := out ++ nodeT (t.get k)
  return out

def convert (inPath outPath : String) (depth : ℕ) : IO Unit := do
  let tables := decodeTablesV2 (← IO.FS.readFile inPath)
  let tasks ← (List.range tables.size).mapM fun i =>
    IO.asTask (pure (convertTable tables[i]! depth))
  let mut out : Array Nat := #[]
  let mut newTables : Array Table := #[]
  let mut tot : ConvStats := {}
  for (task, i) in tasks.zip (List.range tables.size) do
    let (t, st) ← IO.ofExcept (← IO.wait task)
    newTables := newTables.push t
    out := out ++ tableT t
    tot := ⟨tot.direct + st.direct, tot.refined + st.refined, tot.failed + st.failed⟩
    if st.refined + st.failed > 0 then
      IO.println s!"table {i}: {t.size} nodes; direct {st.direct} refined {st.refined} failed {st.failed}"
      (← IO.getStdout).flush
  IO.println s!"total: direct {tot.direct} refined {tot.refined} failed {tot.failed}"
  let text := ",".intercalate (out.toList.map toString) ++ ","
  let decoded := decodeTablesV3 text
  let start ← IO.monoNanosNow
  unless decide ((tablesOf decoded).ValidPar AtlasProjectiveSolutionTree.cornerEps 16) do
    throw (IO.userError "converted corner tables are NOT valid; not writing")
  let finish ← IO.monoNanosNow
  IO.println s!"valid (check {(finish - start) / 1000000} ms); writing {outPath}"
  IO.FS.writeFile outPath text

/-- Nodes `[lo, hi)` of table `index` of a v3 pack (ids unchanged), with the
table's facts and fact polynomials, as a one-table v3 file. -/
def slice (inPath outPath : String) (index lo hi : Nat) : IO Unit := do
  let t := (decodeTablesV3 (← IO.FS.readFile inPath))[index]!
  let mut out : Array Nat := #[t.facts.size]
  for f in t.facts do
    out := out ++ frameT ⟨f.seg, f.kind, f.center, f.radius, f.aff⟩ ++ tripleT f.triple
  for fp in t.fpolys do
    out := out ++ factPolyT fp
  out := out.push (hi - lo)
  for k in List.range (hi - lo) do
    out := out ++ nodeT (t.get (lo + k))
  IO.FS.writeFile outPath (",".intercalate (out.toList.map toString) ++ ",")
  let nP := (List.range (hi - lo)).countP fun k => match t.get (lo + k) with
    | .leaf _ _ (.sharedP ..) => true | _ => false
  let nS := (List.range (hi - lo)).countP fun k => match t.get (lo + k) with
    | .split _ _ _ _ _ u => decide (u < hi) | _ => false
  IO.println s!"wrote {hi - lo} of {t.size} nodes ({nP} sharedP leaves, {nS} in-range splits), {t.facts.size} facts of table {index}"

def kindsV3 (tables : Array Table) : IO Unit := do
  for i in List.range tables.size do
    let t := tables[i]!
    let mut c : Array Nat := Array.replicate 7 0
    for j in List.range t.size do
      let k := match t.get j with
        | .split .. => 0 | .stellar .. => 1 | .leaf _ _ (.sharedP ..) => 2
        | .leaf _ _ (.shared ..) => 3 | .leaf _ _ (.cert ..) => 4
        | .leaf _ _ (.flip ..) => 5 | .leaf _ _ (.handoff ..) => 6
      c := c.modify k (· + 1)
    IO.println s!"table {i} aff {(t.get 0).frame.aff.length}: split/stellar/sharedP/shared/cert/flip/handoff {c}"

/-- For aff-free cert leaves: the highest ancestor frame on which the leaf's
triple has `KeyFacts` and the leaf is `SharedValid`; count distinct facts. -/
def ancestorFacts (tables : Array Table) (index : ℕ) : IO Unit := do
  let t := tables[index]!
  let mut parent : Array ℕ := Array.replicate t.size t.size
  for j in List.range t.size do
    match t.get j with
    | .split _ _ _ _ lo hi => parent := (parent.set! lo j).set! hi j
    | .stellar _ _ _ _ _ _ lo hi => parent := (parent.set! lo j).set! hi j
    | _ => pure ()
  let mut facts : Std.HashSet (ℕ × String) := {}
  let mut ok := 0
  let mut bad := 0
  let mut certs := 0
  for j in List.range t.size do
    if let .leaf _ f (.cert r) := t.get j then
      if r.aff.isEmpty then
        certs := certs + 1
        -- climb while the ancestor's frame still supports the facts
        let mut best : Option ℕ := none
        let mut a := j
        let mut fuel := 64
        while fuel > 0 do
          fuel := fuel - 1
          let fr := (t.get a).frame
          let fact : Row := ⟨fr.seg, fr.kind, fr.center, fr.radius, r.triple, [], [], []⟩
          if fr.aff.isEmpty && decide fact.KeyFacts && decide (r.SharedValid fact) then
            best := some a
            if parent[a]! < t.size then a := parent[a]! else fuel := 0
          else fuel := 0
        match best with
        | some anc => ok := ok + 1; facts := facts.insert (anc, s!"{repr r.triple.inner}{repr r.triple.outer}{(List.range 9).map fun n => r.triple.edge ⟨n / 3 % 3, by omega⟩ ⟨n % 3, by omega⟩}")
        | none => bad := bad + 1
  if certs > 0 then
    IO.println s!"table {index}: {certs} aff-free cert leaves; {ok} shareable via {facts.size} ancestor facts; {bad} not"
    (← IO.getStdout).flush

def splitStats (tables : Array Table) : IO Unit := do
  let mut center := 0
  let mut other := 0
  for t in tables do
    for j in List.range t.size do
      if let .split _ f v m _ _ := t.get j then
        if m == f.center.getD v 0 then center := center + 1 else other := other + 1
  IO.println s!"splits at center {center}, elsewhere {other}"

/-! ## Integer-frame trees -/

def ratLcm (qs : List ℚ) : ℕ := qs.foldl (fun a q => Nat.lcm a q.den) 1

def toIFrame (f : Frame) : IFrame :=
  let n := f.center.length
  let qs := (List.range n).map (f.center.getD · 0) ++ (List.range n).map (f.radius.getD · 0)
  let D := ratLcm qs
  ⟨f.seg, f.kind, D, (List.range n).map fun i => (f.center.getD i 0 * D).num,
    (List.range n).map fun i => (f.radius.getD i 0 * D).num⟩

/-- Lean source of the subtree at node `j`, as a `KTree`; `budget` nodes, then holes. -/
partial def ktreeSrc (t : Table) (f : IFrame) (j : ℕ) (budget : IO.Ref ℕ) : IO String := do
  let b ← budget.get
  if b = 0 then return s!"(.hole {reprFrame f})"
  budget.set (b - 1)
  match t.get j with
  | .split _ _ v m lo hi =>
      let g := Nat.gcd f.D m.den
      let sc := m.den / g
      let M := (m * (f.D * sc : ℕ)).num
      let a ← ktreeSrc t (f.child v M sc false) lo budget
      let c ← ktreeSrc t (f.child v M sc true) hi budget
      return s!"(.split {v} ({M}) {sc} {a} {c})"
  | .leaf _ _ (.sharedP _ k) => return s!"(.leafP {k})"
  | _ => return s!"(.hole {reprFrame f})"
where
  reprFrame (f : IFrame) : String :=
    s!"⟨{f.seg}, .{kindName f.kind}, {f.D}, {f.X.map fun x => s!"({x})"}, {f.H.map fun x => s!"({x})"}⟩"
  kindName : ChartKind → String
    | .plain => "plain" | .tube => "tube" | .wedge => "wedge" | .wtube => "wtube"
    | .skew => "skew" | .atube => "atube" | .btube b => s!"btube {b}" | .askew => "askew"
    | .bskew b => s!"bskew {b}" | .aplain => "aplain" | .bplain b => s!"bplain {b}"

def emitKTree (inPath : String) (index node budget : ℕ) (slicePath out : String) : IO Unit := do
  let t := (decodeTablesV3 (← IO.FS.readFile inPath))[index]!
  -- frame of `node`: walk down from the root
  let mut parent : Array ℕ := Array.replicate t.size t.size
  for j in List.range t.size do
    if let .split _ _ _ _ lo hi := t.get j then parent := (parent.set! lo j).set! hi j
  -- subtree sizes; `node = 0` means: first node whose subtree has ~`budget` nodes
  let mut size : Array ℕ := Array.replicate t.size 1
  for j' in List.range t.size do
    let j := t.size - 1 - j'
    if let .split _ _ _ _ lo hi := t.get j then size := size.set! j (1 + size[lo]! + size[hi]!)
  let node := if node ≠ 0 then node else
    ((List.range t.size).find? fun j => size[j]! ≥ budget / 2 && size[j]! ≤ budget).getD 0
  IO.println s!"node {node}: subtree size {size[node]!}"
  let f := toIFrame (t.get node).frame
  let ref ← IO.mkRef budget
  let src ← ktreeSrc t f node ref
  let ks := (List.range t.facts.size).toArray.toList
  IO.FS.writeFile out s!"import Noperts.Stellated.KernelLoad
import Noperts.Stellated.CornerKernelTree

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

stellated_corner_chunk \"{slicePath}\" 0 0 1 chunk
def H0 : Handoffs := \{ Valid := fun _ _ => False, dec := fun _ _ => isFalse id }
def fr : IFrame := {ktreeSrc.reprFrame f}
def tr : KTree := .anchor {ks} {src}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem tr_ok : KTree.check H0 chunk.facts.toArray chunk.fpolys.toArray fr [] tr = true := by
  decide +kernel
"
  IO.println s!"emitted subtree at node {node}, budget left {← ref.get}"

def handoffStats (tables : Array Table) : IO Unit := do
  let mut c : Array ℕ := Array.replicate 9 0
  for t in tables do
    for j in List.range t.size do
      if let .leaf _ _ (.handoff h) := t.get j then c := c.modify (handoffCode h) (· + 1)
  IO.println s!"handoffs tube/wedge/wtube/skew/cone/pocket/spocket/ppocket/cpocket: {c}"

/-! ## Chunked integer-frame trees for the kernel -/

def iframeT (f : IFrame) : Array Nat :=
  #[if f.seg then 1 else 0, kindCode f.kind, f.X.length, f.D] ++
    (f.X.map zig).toArray ++ (f.H.map zig).toArray

structure ChunkOut where
  id : ℕ
  frame : IFrame
  body : Array Nat
  facts : Std.HashSet ℕ
  children : Array ℕ   -- chunk ids, in hole order
  heavy : Bool := false
  /-- A flip leaf that only the specification path proves (~9 GB of kernel heap). -/
  slow : Bool := false

/-- Serialize the subtree at node `j` (frame `f`) into the current chunk, up to
`budget` nodes; holes queue new chunks. -/
def frameKey (f : Frame) : String := s!"{f.seg}{f.center}{f.radius}"

def isSpecLeaf : Node → Bool
  | .leaf _ _ (.shared ..) | .leaf _ _ (.cert _) => true
  | _ => false

/-- The kernel's cheap integer bound for flip `k` on `f` (the `flipP` leaf check). -/
def flipFast (k : Fin 12) (f : IFrame) : Bool :=
  match flipFP f.seg f.kind k with
  | some fp => cheapI7 (scaleSub fp (f.D ^ 10)) f
  | none => false

/-- An encoded subtree proving flip `k` on `f` by cheap integer bounds alone: a `flipP`
leaf, or a bisection (at the centre of the widest variable) whose halves are proved the
same way, at most `depth` levels deep. -/
partial def flipSplit (k : Fin 12) (f : IFrame) : ℕ → Option (Array Nat)
  | depth =>
    if flipFast k f then some #[8, k.val]
    else if depth = 0 then none
    else
      let vs := (List.range f.X.length).filter (fun v => 0 < f.H.getD v 0)
      match vs.foldl (fun best v => match best with
          | some b => if f.H.getD b 0 < f.H.getD v 0 then some v else best
          | none => some v) none with
      | none => none
      | some v =>
        let M := f.X.getD v 0
        match flipSplit k (f.child v M 1 false).reduce (depth - 1),
            flipSplit k (f.child v M 1 true).reduce (depth - 1) with
        | some a, some b => some (#[0, v, zig M, 1] ++ a ++ b)
        | _, _ => none

/-- Bisection depth allowed when replacing a slow flip leaf by cheap integer checks. -/
def flipDepth : ℕ := 16

/-- Flip leaves that cheap integer bounds cannot prove, even after bisection, stay on
the specification path. -/
def isSlowFlip (f : IFrame) : Node → Bool
  | .leaf _ _ (.flip k) => (flipSplit k f flipDepth).isNone
  | _ => false

partial def emitNode (t : Table) (homes : Std.HashMap String (List ℕ)) (anchored : IO.Ref (Std.HashSet ℕ))
    (size : Array ℕ) (B parentSize : ℕ) (isRoot : Bool) (f : IFrame)
    (j : ℕ)
    (budget : IO.Ref ℕ)
    (body : IO.Ref (Array Nat)) (facts : IO.Ref (Std.HashSet ℕ)) (children : IO.Ref (Array ℕ))
    (queue : IO.Ref (Array (ℕ × IFrame × ℕ))) (nextId : IO.Ref ℕ) : IO Unit := do
  let b ← budget.get
  -- cut at maximal subtrees of size ≤ B, when the budget runs out, and at every
  -- specification-checked leaf (expensive: each gets its own chunk)
  if !isRoot && ((parentSize > B && size[j]! ≤ B) || b = 0 || isSpecLeaf (t.get j) ||
      isSlowFlip f (t.get j)) then
    let id ← nextId.get
    nextId.set (id + 1)
    queue.modify (·.push (id, f, j))
    children.modify (·.push id)
    body.modify (·.push 7)
    return
  budget.set (b - 1)
  -- facts living on this node's frame are anchored here
  if let some ks := homes.get? (frameKey (t.get j).frame) then
    body.modify (· ++ #[1, ks.length] ++ ks.toArray)
    anchored.modify fun a => ks.foldl (·.insert ·) a
  match t.get j with
  | .split _ _ v m lo hi =>
      let sc := m.den / Nat.gcd f.D m.den
      let M := (m * (f.D * sc : ℕ)).num
      body.modify (· ++ #[0, v, zig M, sc])
      emitNode t homes anchored size B size[j]! false (f.child v M sc false).reduce lo budget body facts children queue nextId
      emitNode t homes anchored size B size[j]! false (f.child v M sc true).reduce hi budget body facts children queue nextId
  | .leaf _ _ (.sharedP _ k) =>
      facts.modify (·.insert k)
      body.modify (· ++ #[2, k])
  | .leaf _ _ (.flip k) =>
      body.modify (· ++ (flipSplit k f flipDepth).getD #[3, k.val])
  | .leaf _ _ (.handoff h) => body.modify (· ++ #[4, handoffCode h])
  | .leaf _ _ (.shared r k) =>
      body.modify (· ++ #[5, k] ++ splitT r.split ++ shiftT r.shift ++ tripleT r.triple)
  | .leaf _ _ (.cert r) =>
      body.modify (· ++ #[6] ++ splitT r.split ++ shiftT r.shift ++ tripleT r.triple)
  | .stellar .. => throw (IO.userError s!"stellar split at node {j} not supported")

def ktreeGen (inPath : String) (index budget groupSize : ℕ) (rootE stageE outDir dataDir : String) :
    IO Unit := do
  let tables := decodeTablesV3 (← IO.FS.readFile inPath)
  let t := tables[index]!
  let tn := s!"T{index}"
  IO.FS.createDirAll s!"{outDir}/{tn}"
  IO.FS.createDirAll dataDir
  -- facts slice
  let factsPath := s!"{dataDir}/{tn}.facts.slice3"
  let mut fout : Array Nat := #[t.facts.size]
  for fr in t.facts do
    fout := fout ++ frameT ⟨fr.seg, fr.kind, fr.center, fr.radius, fr.aff⟩ ++ tripleT fr.triple
  for fp in t.fpolys do
    fout := fout ++ factPolyT fp
  fout := fout ++ #[1] ++ nodeT (t.get 0)
  let factsS := ",".intercalate (fout.toList.map toString) ++ ","
  IO.FS.writeFile factsPath factsS
  -- fact homes (frames)
  let mut homes : Std.HashMap String (List ℕ) := {}
  for k in List.range t.facts.size do
    let fr := t.facts[k]!
    let key := frameKey ⟨fr.seg, fr.kind, fr.center, fr.radius, fr.aff⟩
    homes := homes.insert key (homes.getD key [] ++ [k])
  -- subtree sizes
  let mut size : Array ℕ := Array.replicate t.size 1
  for j' in List.range t.size do
    let j := t.size - 1 - j'
    if let .split _ _ _ _ lo hi := t.get j then size := size.set! j (1 + size[lo]! + size[hi]!)
  -- chunks
  let root := toIFrame (t.get 0).frame
  let queue ← IO.mkRef (#[(0, root, 0)] : Array (ℕ × IFrame × ℕ))
  let nextId ← IO.mkRef 1
  let mut chunks : Array ChunkOut := #[]
  let mut qi := 0
  while qi < (← queue.get).size do
    let (id, f, j) := (← queue.get)[qi]!
    qi := qi + 1
    let bud ← IO.mkRef budget
    let body ← IO.mkRef (#[] : Array Nat)
    let facts ← IO.mkRef ({} : Std.HashSet ℕ)
    let children ← IO.mkRef (#[] : Array ℕ)
    let anchored ← IO.mkRef ({} : Std.HashSet ℕ)
    emitNode t homes anchored size budget 0 true f j bud body facts children queue nextId
    let used ← facts.get
    let anch ← anchored.get
    -- facts whose home is above this chunk are anchored at its root
    let outer := used.toList.filter (!anch.contains ·)
    chunks := chunks.push ⟨id, f, ← body.get, Std.HashSet.ofList outer, ← children.get,
      isSpecLeaf (t.get j) || isSlowFlip f (t.get j), isSlowFlip f (t.get j)⟩
  IO.println s!"table {index}: {chunks.size} chunks"
  -- groups
  -- light chunks in groups of `groupSize`; specification-checked leaves in groups of 3
  let light := chunks.filter (!·.heavy)
  let heavyC := chunks.filter (·.heavy)
  let chop := fun (xs : Array ChunkOut) (n : ℕ) => Id.run do
    let mut out : Array (List ChunkOut) := #[]
    let mut i := 0
    while i < xs.size do
      out := out.push (xs.toList.drop i |>.take n)
      i := i + n
    return out
  -- specification-checked chunks in modules of 3, all slow flips of the table in one
  -- module (the kernel cache resets per theorem, so heap stays near one leaf's), spread evenly
  -- through the import order: Lake starts ready modules roughly in import order, so
  -- spreading keeps heavy modules from running all at once
  -- spread `b` evenly through `a`
  let spread := fun (a b : Array (List ChunkOut)) => Id.run do
    let mut out := #[]
    let mut bi := 0
    for ai in List.range a.size do
      out := out.push a[ai]!
      while bi < b.size && bi * a.size ≤ ai * b.size do
        out := out.push b[bi]!; bi := bi + 1
    while bi < b.size do
      out := out.push b[bi]!; bi := bi + 1
    return out
  let groupL := spread (chop light groupSize)
    (spread (chop (heavyC.filter (!·.slow)) 3) (chop (heavyC.filter (·.slow)) (max 1 (heavyC.filter (·.slow)).size)))
  let groups := groupL.size
  let groupOf : Array ℕ := Id.run do
    let mut g : Array ℕ := Array.replicate chunks.size 0
    for gi in List.range groups do
      for c in groupL[gi]! do g := g.set! c.id gi
    return g
  IO.FS.writeFile s!"{outDir}/{tn}/heavy.txt"
    ("\n".intercalate ((List.range groups).filter (fun g => groupL[g]!.any (·.heavy)) |>.map fun g =>
      s!"StellatedKernel.{tn}.G{g}"))
  let pre := s!"Noperts.Stellated.KernelCorner.{tn}"
  -- Facts module
  IO.FS.writeFile s!"{outDir}/{tn}/Facts.lean" s!"import Noperts.Stellated.KernelLoad
import Noperts.Stellated.AtlasProjectiveSolutionTree
import Noperts.Stellated.CornerCoverage

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

stellated_corner_chunk \"{factsPath}\" 0 0 1 src
-- data hash {hash factsS} (the loaded file is not tracked by Lake)
noncomputable abbrev facts : Array CornerCertificate.Row := src.facts.toArray
noncomputable abbrev fps : Array FactPoly := src.fpolys.toArray
abbrev H : Handoffs := CornerCoverage.stage AtlasProjectiveSolutionTree.cornerEps {stageE}

end {pre}
"
  for g in List.range groups do
    let members := groupL[g]!
    let mut dout : Array Nat := #[members.length]
    for c in members do
      let ks := c.facts.toList.mergeSort (· ≤ ·)
      dout := dout ++ #[c.id] ++ iframeT c.frame ++ #[1, ks.length] ++ ks.toArray ++ c.body
    let dataPath := s!"{dataDir}/{tn}.g{g}.kt"
    let dataS := ",".intercalate (dout.toList.map toString) ++ ","
    IO.FS.writeFile dataPath dataS
    let mut src := s!"import {"StellatedKernel"}.{tn}.Facts

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

stellated_ktree_chunks \"{dataPath}\" g{g}
-- data hash {hash dataS} (the loaded file is not tracked by Lake)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
"
    for c in members do
      src := src ++ s!"
theorem g{g}.ok{c.id} (hH : ∀ h f, H.Valid h f → Covered f)
    (hf : ∀ fact ∈ facts, fact.KeyFacts) (hp : FactPolysOk facts fps)
    (hh : ∀ x ∈ g{g}.c{c.id}.tree.holes, ICovered x) : ICovered g{g}.c{c.id}.frame :=
  check_sound H facts fps hH hf hp _ _ [] (IFrame.good_of_wf _ (by decide +kernel))
    (activeInv_nil _ _) (by decide +kernel) hh
"
    src := src ++ s!"\nend {pre}\n"
    IO.FS.writeFile s!"{outDir}/{tn}/G{g}.lean" src
  -- Assembly: bottom-up (reverse BFS order)
  let mut asm := s!"import StellatedKernel.{tn}.Facts\n"
  for g in List.range groups do
    asm := asm ++ s!"import StellatedKernel.{tn}.G{g}\n"
  asm := asm ++ s!"
open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

set_option maxRecDepth 100000
set_option maxHeartbeats 0

section
variable (hH : ∀ h f, H.Valid h f → Covered f) (hf : ∀ fact ∈ facts, fact.KeyFacts)
  (hp : FactPolysOk facts fps)
include hH hf hp
"
  for c in chunks.reverse do
    let g := groupOf[c.id]!
    let holes := ", ".intercalate (c.children.toList.map fun k => s!"g{groupOf[k]!}.c{k}.frame")
    let proofs := c.children.toList.foldr (fun k acc =>
      s!"List.forall_mem_cons.2 ⟨cov{k} hH hf hp, {acc}⟩") "List.forall_mem_nil _"
    asm := asm ++ s!"
theorem cov{c.id} : ICovered g{g}.c{c.id}.frame :=
  g{g}.ok{c.id} hH hf hp (holes_of_eq (by decide +kernel : g{g}.c{c.id}.tree.holes = [{holes}])
    ({proofs}))
"
  asm := asm ++ s!"
theorem covered : Covered {rootE} :=
  covered_of_toFrame _ (by decide +kernel) _ (by decide +kernel) (cov0 hH hf hp)

end

end {pre}
"
  IO.FS.writeFile s!"{outDir}/{tn}/Assembly.lean" asm
  -- per-fact theorems, in modules of 10 facts
  let nf := t.facts.size
  let fgroups := (nf + 9) / 10
  for fg in List.range fgroups do
    let mut src := s!"import StellatedKernel.{tn}.Facts

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

set_option maxRecDepth 100000
set_option maxHeartbeats 0
"
    for i in List.range nf do
      if i / 10 = fg then
        src := src ++ s!"
theorem fact{i} : ∀ h : {i} < facts.size, (facts[{i}]'h).KeyFacts := by decide +kernel

theorem fpoly{i} : ∀ h : {i} < fps.size, FactPolyAt facts fps ⟨{i}, h⟩ := by decide +kernel
"
    src := src ++ s!"\nend {pre}\n"
    IO.FS.writeFile s!"{outDir}/{tn}/F{fg}.lean" src
  let mut fok := s!"import StellatedKernel.{tn}.Facts\n"
  for fg in List.range fgroups do
    fok := fok ++ s!"import StellatedKernel.{tn}.F{fg}\n"
  let factCases := String.join ((List.range nf).map fun i => s!"\n    | {i}, h => fact{i} h")
  let fpCases := String.join ((List.range nf).map fun i => s!"\n    | {i}, h => fpoly{i} h")
  fok := fok ++ s!"
open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

set_option maxRecDepth 100000

theorem facts_ok : ∀ fact ∈ facts, fact.KeyFacts := by
  have hsize : facts.size = {nf} := by decide +kernel
  have key : ∀ i (h : i < facts.size), (facts[i]'h).KeyFacts := fun i h => match i, h with{factCases}
    | _ + {nf}, h => absurd h (by omega)
  intro fact hm
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hm
  exact key i hi

theorem fps_ok : FactPolysOk facts fps := by
  have hsize : fps.size = {nf} := by decide +kernel
  have key : ∀ i (h : i < fps.size), FactPolyAt facts fps ⟨i, h⟩ := fun i h => match i, h with{fpCases}
    | _ + {nf}, h => absurd h (by omega)
  intro k
  exact key k.val k.isLt

end {pre}
"
  IO.FS.writeFile s!"{outDir}/{tn}/FactsOk.lean" fok
  IO.FS.writeFile s!"{outDir}/{tn}/Table.lean" s!"import StellatedKernel.{tn}.Assembly
import StellatedKernel.{tn}.FactsOk

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

set_option maxRecDepth 100000

theorem table_covered (hH : ∀ h f, H.Valid h f → Covered f) : Covered {rootE} :=
  covered hH facts_ok fps_ok

end {pre}
"
  IO.println s!"wrote {groups} groups to {outDir}/{tn}"

/-- Natively evaluate the generated chunks of a group file against the table. -/
partial def explain (H : Handoffs) (facts : Array Row) (fps : Array FactPoly) (f : IFrame)
    (act : List (ℕ × Bool)) : KTree → IO Unit
  | .split v M s lo hi => do
      unless v < f.X.length && 0 < s do IO.println s!"bad split header v={v} len={f.X.length}"
      explain H facts fps (f.child v M s false).reduce act lo
      explain H facts fps (f.child v M s true).reduce act hi
  | .anchor ks t => do
      for k in ks do
        unless anchorOk facts f k do IO.println s!"anchor {k} fails at {repr f.X} D={f.D}"
      explain H facts fps f (ks.map (fun k => (k, anchorFlag facts k)) ++ act) t
  | .leafP k => do
      unless leafPOk fps f act k do
        IO.println s!"leafP {k} fails: lookup {act.lookup k} cheap {(fps[k]?.map fun fp => cheapI7 fp f)}"
  | t => do
      unless KTree.check H facts fps f act t do IO.println s!"other leaf fails"

def checkGroup (pack group : String) (index : ℕ) (stage : Handoff → Bool) : IO Unit := do
  let t := (decodeTablesV3 (← IO.FS.readFile pack))[index]!
  let chunks := PackedKTree.decodeChunks (← IO.FS.readFile group)
  let H := CornerCoverage.stage AtlasProjectiveSolutionTree.cornerEps stage
  for (id, f, tr) in chunks.toList.take 2 do
    IO.println s!"chunk {id}: wf {f.WF} check {KTree.check H t.facts t.fpolys f [] tr}"
    explain H t.facts t.fpolys f [] tr

def directCheap (pack : String) (index : ℕ) : IO Unit := do
  let t := (decodeTablesV3 (← IO.FS.readFile pack))[index]!
  let mut ok := 0
  let mut bad := 0
  for j in List.range (min t.size 3000) do
    if let .leaf _ f (.sharedP r k) := t.get j then
      let g := toIFrame f
      if cheapI7 t.fpolys[k]! g then ok := ok + 1 else
        bad := bad + 1
        if bad ≤ 2 then
          IO.println s!"node {j}: frame c {f.center} r {f.radius}; I D {g.D} X {g.X} H {g.H}; cheapRow {cheapRow t.fpolys[k]!.S r}"
  IO.println s!"direct: ok {ok} bad {bad}"

partial def anchorStats (t : Table) (f : IFrame) (j : ℕ) (acc : IO.Ref (ℕ × ℕ × ℕ)) : IO Unit := do
  match t.get j with
  | .split _ _ v m lo hi =>
      let sc := m.den / Nat.gcd f.D m.den
      let M := (m * (f.D * sc : ℕ)).num
      anchorStats t (f.child v M sc false).reduce lo acc
      anchorStats t (f.child v M sc true).reduce hi acc
  | .leaf _ _ (.sharedP _ k) =>
      let fp := t.fpolys[k]!
      let Hn := f.H.map Int.toNat
      let c := cheapP fp.S f.D (f.X.map Int.natAbs) (f.X.map fun x => decide (x < 0)) Hn true
      acc.modify fun (a, b, n) => if c then (a + 1, b, n + fp.S.length) else (a, b + 1, n + fp.S.length)
  | _ => pure ()

/-! ## Second-order merge probe (Float) -/

def qfl (q : ℚ) : Float := (if q.num < 0 then -1 else 1) * q.num.natAbs.toFloat / q.den.toFloat

/-- Lower bounds (first, second order) of `S` on the box `a ± hm`. -/
def bounds12 (S : List (Mono × ℕ × Bool)) (a hm : Array Float) : Float × Float := Id.run do
  let n := 7
  let mut v := 0.0
  let mut g : Array Float := Array.replicate n 0
  let mut H : Array Float := Array.replicate (n * n) 0
  let mut V := 0.0
  let mut G : Array Float := Array.replicate n 0
  let mut Hm : Array Float := Array.replicate (n * n) 0
  let mut T := 0.0
  let aa := a.map Float.abs
  for t in S do
    let c := (if t.2.2 then -1.0 else 1.0) * t.2.1.toFloat
    let ac := Float.abs c
    let e : Array ℕ := (t.1.toArray ++ Array.replicate n 0).extract 0 n
    let mono := fun (x : Array Float) (d : Array ℕ) => Id.run do
      let mut r := 1.0
      for i in [0:n] do
        if e[i]! < d[i]! then return 0.0
        r := r * x[i]! ^ (e[i]! - d[i]!).toFloat
      return r
    let z : Array ℕ := Array.replicate n 0
    v := v + c * mono a z
    V := V + ac * mono aa z
    T := T + ac * mono ((aa.zip hm).map fun (x, y) => x + y) z
    for i in [0:n] do
      if e[i]! > 0 then
        let di := z.set! i 1
        g := g.modify i (· + c * e[i]!.toFloat * mono a di)
        G := G.modify i (· + ac * e[i]!.toFloat * mono aa di)
        for j in [0:n] do
          if j == i then
            if e[i]! ≥ 2 then
              let dd := z.set! i 2
              let k := (e[i]! * (e[i]! - 1)).toFloat
              H := H.modify (i * n + i) (· + c * k * mono a dd)
              Hm := Hm.modify (i * n + i) (· + ac * k * mono aa dd)
          else if e[j]! > 0 then
            let dd := (z.set! i 1).set! j 1
            let k := (e[i]! * e[j]!).toFloat
            H := H.modify (i * n + j) (· + c * k * mono a dd)
            Hm := Hm.modify (i * n + j) (· + ac * k * mono aa dd)
  -- first order
  let mut lin1 := 0.0
  let mut L := 0.0
  for i in [0:n] do
    lin1 := lin1 - Float.abs g[i]! * hm[i]!
    L := L + G[i]! * hm[i]!
  let b1 := v + lin1 - (T - V - L)
  -- second order
  let mut quad := 0.0
  let mut Q2 := 0.0
  for i in [0:n] do
    let r := hm[i]!
    let gi := g[i]!
    let hi := H[i * n + i]!
    let f := fun (x : Float) => gi * x + 0.5 * hi * x * x
    let mut m := min (f (-r)) (f r)
    if hi > 0 then
      let x := -gi / hi
      if x > -r && x < r then m := min m (f x)
    quad := quad + m
    for j in [0:n] do
      Q2 := Q2 + 0.5 * Hm[i * n + j]! * r * hm[j]!
      if j > i then quad := quad - Float.abs H[i * n + j]! * r * hm[j]!
  let b2 := v + quad - (T - V - L - Q2)
  return (b1, b2)

def iframeF (f : IFrame) : Array Float × Array Float :=
  let D := f.D.toFloat
  ((List.range 7).toArray.map fun i =>
      (if f.X.getD i 0 < 0 then -1.0 else 1.0) * (f.X.getD i 0).natAbs.toFloat / D,
   (List.range 7).toArray.map fun i => (f.H.getD i 0).natAbs.toFloat / D)

/-- Bottom-up merge with the second-order bound: returns (leaves after merging, facts usable). -/
partial def mergeProbe (t : Table) (f : IFrame) (j : ℕ) (order2 : Bool) : ℕ × Option (List ℕ) :=
  match t.get j with
  | .split _ _ v m lo hi =>
      let sc := m.den / Nat.gcd f.D m.den
      let M := (m * (f.D * sc : ℕ)).num
      let (n1, a) := mergeProbe t (f.child v M sc false).reduce lo order2
      let (n2, b) := mergeProbe t (f.child v M sc true).reduce hi order2
      match a, b with
      | some ka, some kb =>
          let cands := (ka ++ kb).eraseDups
          let (ax, hm) := iframeF f
          let ok := cands.filter fun k =>
            let (b1, b2) := bounds12 t.fpolys[k]!.S ax hm
            if order2 then b2 ≥ 0 else b1 ≥ 0
          if ok.isEmpty then (n1 + n2, none) else (1, some ok)
      | _, _ => (n1 + n2, none)
  | .leaf _ _ (.sharedP _ k) => (1, some [k])
  | .leaf .. => (1, none)
  | .stellar .. => (1, none)

/-! ## Exact bottom-up merging with the cheap bound -/

/-- Merge decisions: `some k` when the subtree at `j` becomes one sharedP leaf
with fact `k`. -/
partial def mergeExact (t : Table) (f : IFrame) (j : ℕ) (out : IO.Ref (Std.HashMap ℕ ℕ)) :
    IO (Option (List ℕ)) := do
  match t.get j with
  | .split _ _ v m lo hi =>
      let sc := m.den / Nat.gcd f.D m.den
      let M := (m * (f.D * sc : ℕ)).num
      let a ← mergeExact t (f.child v M sc false).reduce lo out
      let b ← mergeExact t (f.child v M sc true).reduce hi out
      match a, b with
      | some ka, some kb =>
          let cands := (ka ++ kb).eraseDups
          match cands.find? fun k => cheapI7 t.fpolys[k]! f with
          | some k => out.modify (·.insert j k); return some [k]
          | none => return none
      | _, _ => return none
  | .leaf _ _ (.sharedP _ k) => return some [k]
  | _ => return none

/-- Re-emit the reachable nodes in preorder with fresh ids, cutting merged
subtrees into sharedP leaves. -/
partial def reemit (t : Table) (merged : Std.HashMap ℕ ℕ) (j : ℕ) (acc : IO.Ref (Array Node)) :
    IO ℕ := do
  let id ← acc.modifyGet fun a => (a.size, a.push default)
  let n := t.get j
  match merged.get? j with
  | some k =>
      let f := n.frame
      acc.modify (·.set! id (.leaf id f (.sharedP (frameRow f t.facts[k]!) k)))
  | none =>
      match n with
      | .split _ f v m lo hi =>
          let a ← reemit t merged lo acc
          let b ← reemit t merged hi acc
          acc.modify (·.set! id (.split id f v m a b))
      | .stellar _ f i j' α β lo hi =>
          let a ← reemit t merged lo acc
          let b ← reemit t merged hi acc
          acc.modify (·.set! id (.stellar id f i j' α β a b))
      | .leaf _ f l => acc.modify (·.set! id (.leaf id f l))
  return id

def compactTable (t : Table) : IO Table := do
  if (t.get 0).frame.aff.length > 0 then return t
  let merged ← IO.mkRef ({} : Std.HashMap ℕ ℕ)
  let _ ← mergeExact t (toIFrame (t.get 0).frame) 0 merged
  let acc ← IO.mkRef (#[] : Array Node)
  let _ ← reemit t (← merged.get) 0 acc
  let arr ← acc.get
  return { get := fun i => arr[i]!, size := arr.size, facts := t.facts, fpolys := t.fpolys }

def compactAll (inPath outPath : String) : IO Unit := do
  let tables := decodeTablesV3 (← IO.FS.readFile inPath)
  let tasks ← (List.range tables.size).mapM fun i => IO.asTask (compactTable tables[i]!)
  let mut out : Array Nat := #[]
  let mut newTables : Array Table := #[]
  let mut before := 0
  let mut after := 0
  for (task, i) in tasks.zip (List.range tables.size) do
    let t ← IO.ofExcept (← IO.wait task)
    let t0 := tables[i]!
    before := before + t0.size
    after := after + t.size
    if t.size < t0.size then
      IO.println s!"table {i}: {t0.size} → {t.size} nodes"
      (← IO.getStdout).flush
    newTables := newTables.push t
    out := out ++ tableT t
  IO.println s!"total nodes {before} → {after}"
  let text := ",".intercalate (out.toList.map toString) ++ ","
  let decoded := decodeTablesV3 text
  unless decide ((tablesOf decoded).ValidPar AtlasProjectiveSolutionTree.cornerEps 16) do
    throw (IO.userError "compacted corner tables are NOT valid; not writing")
  IO.println s!"valid; writing {outPath}"
  IO.FS.writeFile outPath text

/-! ## Split-part probe for fallback leaves -/

def termsWith (v : ℕ) (S : List (Mono × ℕ × Bool)) : List (Mono × ℕ × Bool) :=
  S.filter fun t => 0 < t.1.getD v 0

def termsWithout (v : ℕ) (S : List (Mono × ℕ × Bool)) : List (Mono × ℕ × Bool) :=
  S.filter fun t => t.1.getD v 0 = 0

def divVar (v : ℕ) (S : List (Mono × ℕ × Bool)) : List (Mono × ℕ × Bool) :=
  S.map fun t => (t.1.set v (t.1.getD v 0 - 1), t.2)

def negPoly (S : List (Mono × ℕ × Bool)) : List (Mono × ℕ × Bool) :=
  S.map fun t => (t.1, t.2.1, !t.2.2)

/-- Split parts of `S`: `[(sign, part)]` and the rest. -/
def splitPartsN : List (ℕ × Bool) → List (Mono × ℕ × Bool) →
    List (List (Mono × ℕ × Bool)) × List (Mono × ℕ × Bool)
  | [], S => ([], S)
  | (v, pos) :: vs, S =>
      let (ps, rest) := splitPartsN vs (termsWithout v S)
      let part := divVar v (termsWith v S)
      ((if pos then part else negPoly part) :: ps, rest)

def splitProbe (pack : String) : IO Unit := do
  let tables := decodeTablesV3 (← IO.FS.readFile pack)
  let mut total := 0
  let mut okN := 0
  let mut shifted := 0
  for t in tables do
    for j in List.range t.size do
      if let .leaf _ f (.shared r k) := t.get j then
        total := total + 1
        if r.shift.any (· != 0) then shifted := shifted + 1 else
          let g := toIFrame f
          let (ps, rest) := splitPartsN r.split t.fpolys[k]!.S
          if (rest :: ps).all fun q => q.isEmpty || cheapI7 ⟨q, [], 1⟩ g then okN := okN + 1
  IO.println s!"fallback leaves {total}: shifted {shifted}; unshifted certified by split parts {okN}"

/-! ## Cert leaves → shared facts on ancestor frames -/

def tripleKey (t : Triple) : String :=
  s!"{(List.range 9).map fun n => t.edge ⟨n / 3 % 3, by omega⟩ ⟨n % 3, by omega⟩}{repr t.inner}{repr t.outer}"

def ancestorizeTable (t : Table) (depth : ℕ) : IO (Table × ℕ × ℕ × ℕ) := do
  if (t.get 0).frame.aff.length > 0 then return (t, 0, 0, 0)
  let mut parent : Array ℕ := Array.replicate t.size t.size
  for j in List.range t.size do
    match t.get j with
    | .split _ _ _ _ lo hi => parent := (parent.set! lo j).set! hi j
    | _ => pure ()
  let mut memo : Std.HashMap (ℕ × String) Bool := {}
  let mut factIx : Std.HashMap (ℕ × String) ℕ := {}
  let mut facts := t.facts
  let mut fps := t.fpolys
  let mut nodes : Array Node := (List.range t.size).toArray.map t.get
  let mut converted := 0
  let mut failed := 0
  let mut newFacts := 0
  for j in List.range t.size do
    if let .leaf _ f (.cert r) := t.get j then
      if !r.aff.isEmpty then failed := failed + 1; continue
      let key := tripleKey r.triple
      -- climb while KeyFacts holds on the ancestor frame
      let mut best : Option ℕ := none
      let mut a := j
      let mut go := true
      while go do
        let ok ← match memo.get? (a, key) with
          | some b => pure b
          | none => do
              let fr := (t.get a).frame
              let fact : Row := ⟨fr.seg, fr.kind, fr.center, fr.radius, r.triple, [], [], []⟩
              let b := fr.aff.isEmpty && decide fact.KeyFacts && decide ((factPoly fact).Ok fact)
              memo := memo.insert (a, key) b
              pure b
        if ok then
          best := some a
          if parent[a]! < t.size then a := parent[a]! else go := false
        else go := false
      match best with
      | none => failed := failed + 1
      | some anc =>
          let k ← match factIx.get? (anc, key) with
            | some k => pure k
            | none => do
                let fr := (t.get anc).frame
                let fact : Row := ⟨fr.seg, fr.kind, fr.center, fr.radius, r.triple, [], [], []⟩
                let k := facts.size
                facts := facts.push fact
                fps := fps.push (factPoly fact)
                factIx := factIx.insert (anc, key) k
                newFacts := newFacts + 1
                pure k
          let fact := facts[k]!
          let fp := fps[k]!
          match refine fact fp f r depth with
          | some .leaf =>
              nodes := nodes.set! j (.leaf j f (.sharedP (frameRow f r) k))
              converted := converted + 1
          | some pl =>
              nodes := emitPlan r k nodes j f pl
              converted := converted + 1
          | none => failed := failed + 1
  let arr := nodes
  return ({ get := fun i => arr[i]!, size := arr.size, facts := facts, fpolys := fps },
    converted, failed, newFacts)

def ancestorizeAll (inPath outPath : String) (depth : ℕ) : IO Unit := do
  let tables := decodeTablesV3 (← IO.FS.readFile inPath)
  let tasks ← (List.range tables.size).mapM fun i =>
    IO.asTask (ancestorizeTable tables[i]! depth) (prio := .dedicated)
  let mut out : Array Nat := #[]
  for (task, i) in tasks.zip (List.range tables.size) do
    let (t, c, fl, nf) ← IO.ofExcept (← IO.wait task)
    if c + fl > 0 then
      IO.println s!"table {i}: certs converted {c}, failed {fl}, new facts {nf}"
      (← IO.getStdout).flush
    out := out ++ tableT t
  let text := ",".intercalate (out.toList.map toString) ++ ","
  let decoded := decodeTablesV3 text
  unless decide ((tablesOf decoded).ValidPar AtlasProjectiveSolutionTree.cornerEps 16) do
    throw (IO.userError "ancestorized corner tables are NOT valid; not writing")
  IO.println s!"valid; writing {outPath}"
  IO.FS.writeFile outPath text

def kindSrc : ChartKind → String
  | .plain => ".plain" | .tube => ".tube" | .wedge => ".wedge" | .wtube => ".wtube"
  | .skew => ".skew" | .atube => ".atube" | .btube b => s!"(.btube {b})" | .askew => ".askew"
  | .bskew b => s!"(.bskew {b})" | .aplain => ".aplain" | .bplain b => s!"(.bplain {b})"

def flipFactPoly (seg : Bool) (kind : ChartKind) (k : Fin 12) : FactPoly :=
  let q := normalize (flipPoly seg kind k)
  let e := (gcdMono (· == 0) q).getD 0 0
  let m : Mono := if e = 0 then [] else [e]
  let S := divByMono q m
  let K := S.foldl (fun acc t => Nat.lcm acc t.2.den) 1
  ⟨S.map fun t => let c := (t.2 * (K : ℚ)).num; (t.1, c.natAbs, decide (c < 0)), m, K⟩

def flipPolys (inPath outPath : String) : IO Unit := do
  let tables := decodeTablesV3 (← IO.FS.readFile inPath)
  let mut keys : Std.HashMap String (Bool × ChartKind × Fin 12) := {}
  for t in tables do
    for j in List.range t.size do
      if let .leaf _ f (.flip k) := t.get j then
        keys := keys.insert s!"{f.seg}{repr f.kind}{k}" (f.seg, f.kind, k)
  let mut defs := ""
  let mut chain := "none"
  let mut cases := ""
  let mut i := 0
  for (_, (seg, kind, k)) in keys.toList do
    let fp := flipFactPoly seg kind k
    let terms := ", ".intercalate (fp.S.map fun t => s!"({t.1}, {t.2.1}, {t.2.2})")
    defs := defs ++ s!"def flipFP{i} : FactPoly := ⟨[{terms}], {fp.m}, {fp.K}⟩\n\ntheorem flipFP{i}_ok : FlipOk flipFP{i} {seg} {kindSrc kind} {k.val} := by\n  refine ⟨by decide, by decide, fun y => ?_⟩\n  simp only [flipFP{i}, toIPoly, IPoly.toPoly, List.map, eval_cons, eval_nil, sgnI]\n  simp only [flipPoly, flipLin, xPolyK, eval_add, eval_mul, eval_scale, eval_const, eval_wPoly, wVal]\n  simp [flipCoeff, B0, F1, F2, sVal, tVal, monoEval, monoEvalFrom, eval_var, xPoly, eval_add,\n    eval_mul, eval_scale, eval_const, sPoly, tPoly, M1, M2, M3, scalePoly, eval_scalePoly, scaleVal,\n    skewK, atubeA, plainX, skewX, tubeX]\n  ring\n\n"
    chain := s!"if seg = {seg} ∧ kind = {kindSrc kind} ∧ k = {k.val} then some flipFP{i} else\n    " ++ chain
    i := i + 1
  let alts := " | ".intercalate ((List.range i).map fun j => s!"exact flipFP{j}_ok")
  cases := s!"\n  all_goals (obtain ⟨rfl, rfl, rfl⟩ := ‹_›; first | {alts})"
  IO.FS.writeFile outPath s!"module

public import Noperts.Stellated.FlipPolysBase

@[expose] public section

/-! Flip polynomial data for the flip leaves of the corner tables (generated by
`kernelCorner flippolys`). -/

namespace Noperts.Stellated.CornerKernel

open CornerPoly CornerTree SparsePoly FlipPrune

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

{defs}def flipFP (seg : Bool) (kind : ChartKind) (k : Fin 12) : Option FactPoly :=
  {chain}

theorem flipFP_ok \{seg : Bool} \{kind : ChartKind} \{k : Fin 12} \{fp : FactPoly}
    (h : flipFP seg kind k = some fp) : FlipOk fp seg kind k := by
  unfold flipFP at h
  split_ifs at h <;> (try simp at h) <;> subst h{cases}

end Noperts.Stellated.CornerKernel
"
  IO.println s!"{i} flip polynomials"

def main (args : List String) : IO Unit := do
  if let ["ancestorize", i, o, d] := args then
    ancestorizeAll i o d.toNat!
    return
  if let ["splitprobe", i] := args then
    splitProbe i
    return
  if let ["compact", i, o] := args then
    compactAll i o
    return
  if let ["mergeprobe", i, t] := args then
    let tab := (decodeTablesV3 (← IO.FS.readFile i))[t.toNat!]!
    let root := toIFrame (tab.get 0).frame
    let leaves := (List.range tab.size).countP fun j => match tab.get j with | .leaf .. => true | _ => false
    let (n1, _) := mergeProbe tab root 0 false
    let (n2, _) := mergeProbe tab root 0 true
    IO.println s!"table {t}: leaves {leaves}; after merging: first-order {n1}, second-order {n2}"
    return
  if let ["anchors", i, t] := args then
    let tab := (decodeTablesV3 (← IO.FS.readFile i))[t.toNat!]!
    let acc ← IO.mkRef (0, 0, 0)
    anchorStats tab (toIFrame (tab.get 0).frame) 0 acc
    let (a, b, n) ← acc.get
    IO.println s!"centered passes {a}, needs corner {b}, avg terms {n / max 1 (a + b)}"
    return
  if let ["direct", p, t] := args then
    directCheap p t.toNat!
    return
  if let ["checkgroup", p, g, t] := args then
    checkGroup p g t.toNat! CornerCoverage.noHandoff
    return
  if let ["flippolys", i, o] := args then
    flipPolys i o
    return
  if let ["ktreegen", i, t, b, gs, rootE, stageE, outDir, dataDir] := args then
    ktreeGen i t.toNat! b.toNat! gs.toNat! rootE stageE outDir dataDir
    return
  if let ["handoffs", i] := args then
    handoffStats (decodeTablesV3 (← IO.FS.readFile i))
    return
  if let ["ktree", i, t, n, b, sl, o] := args then
    emitKTree i t.toNat! n.toNat! b.toNat! sl o
    return
  if let ["splitstats", i] := args then
    splitStats (decodeTablesV3 (← IO.FS.readFile i))
    return
  if let ["ancestors", i] := args then
    let tables := decodeTablesV3 (← IO.FS.readFile i)
    let tasks ← (List.range tables.size).mapM fun t => IO.asTask (ancestorFacts tables t)
    for task in tasks do
      let _ ← IO.wait task
    return
  if let ["kinds", i] := args then
    kindsV3 (decodeTablesV3 (← IO.FS.readFile i))
    return
  if let ["slice", i, o, t, lo, hi] := args then
    slice i o t.toNat! lo.toNat! hi.toNat!
    return
  if let ["convert", i, o, d] := args then
    convert i o d.toNat!
    return
  if let ["shifts", i] := args then
    shiftPairs (decodeTablesV2 (← IO.FS.readFile i))
    return
  if let "stats" :: i :: d :: ts := args then
    let tables := decodeTablesV2 (← IO.FS.readFile i)
    let ts := if ts == [] then List.range tables.size else ts.map String.toNat!
    let tasks ← ts.mapM fun t => IO.asTask (stats tables d.toNat! t)
    for task in tasks do
      let _ ← IO.wait task
