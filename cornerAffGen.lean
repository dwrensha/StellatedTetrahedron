import Noperts.Stellated.NativeExecutable
import Noperts.Stellated.PackedCornerTree
import Noperts.Stellated.CornerAffTree
import Std.Data.HashMap

/-!
Generator for kernel trees of reparametrized (cone) corner tables (not part of
the proof): converts certificate leaves into shared leaves citing an ancestor
fact with the same reparametrization (`CornerAff.SharedPValidA`), refining by
splits where the cheap bound fails.

`cornerAffGen stats PACK TABLE DEPTH`
-/

open Noperts.Stellated
open Noperts.Stellated.CornerTree CornerCertificate CornerPoly PackedCornerTree SparsePoly
open Noperts.Stellated.CornerKernel CornerAff

instance : Inhabited Row := ⟨⟨false, .plain, [], [], ⟨fun _ _ => 0, fun _ => 0, fun _ => 0⟩, [], [], []⟩⟩
instance : Inhabited FactPoly := ⟨⟨[], [], 1⟩⟩
instance : Inhabited RTree := ⟨.hole ⟨false, .plain, [], [], []⟩⟩

def factPoly (fact : Row) : FactPoly :=
  let F := normalize (divByMono fact.D [1])
  let m := gcdMono fact.nonnegVars F
  let S := divByMono F m
  let K := S.foldl (fun acc t => Nat.lcm acc t.2.den) 1
  ⟨S.map fun t => let c := (t.2 * (K : ℚ)).num; (t.1, c.natAbs, decide (c < 0)), m, K⟩

/-- Refine by splitting until every piece passes the shared check. -/
partial def refine (fact : Row) (fp : FactPoly) (f : Frame) (r : Row) (depth : ℕ) :
    Option RTree :=
  let row := frameRow f r.triple r.split r.shift
  if decide (SharedPValidA row fact fp) then some (.sharedPA r.triple r.split r.shift 0)
  else if depth = 0 then none
  else
    let vars := ((List.range f.radius.length).filter fun v => f.radius.getD v 0 > 0)
    let ranked := vars.mergeSort fun a b => f.radius.getD a 0 ≥ f.radius.getD b 0
    let tries := if depth ≥ 2 then ranked.take 2 else ranked
    tries.findSome? fun v =>
      let m := f.center.getD v 0
      match refine fact fp (f.lower v m) r (depth - 1) with
      | none => none
      | some lo => (refine fact fp (f.upper v m) r (depth - 1)).map (.split v m lo)

/-- Set the fact index of every shared leaf. -/
def setFact (k : ℕ) : RTree → RTree
  | .split v m lo hi => .split v m (setFact k lo) (setFact k hi)
  | .sharedPA t s sh _ => .sharedPA t s sh k
  | x => x

def tripleKey (t : Triple) : String :=
  toString ((List.range 9).map fun n => t.edge ⟨n / 3 % 3, by omega⟩ ⟨n % 3, by omega⟩) ++
    toString [(t.inner 0).val, (t.inner 1).val, (t.inner 2).val,
      (t.outer 0).val, (t.outer 1).val, (t.outer 2).val]

def frameKey (f : Frame) : String :=
  s!"{f.seg}{repr f.kind}{f.center}{f.radius}{f.aff}"

structure St where
  facts : Array Row := #[]
  fps : Array FactPoly := #[]
  factIx : Std.HashMap String ℕ := {}
  memo : Std.HashMap String Bool := {}
  converted : ℕ := 0
  failed : ℕ := 0
  nodes : ℕ := 0

/-- Convert node `j`; `anc` lists the frames above it since the last stellar
split (nearest last). -/
partial def conv (t : Table) (depth : ℕ) (anc : Array Frame) (j : ℕ) : StateM St RTree := do
  modify fun s => { s with nodes := s.nodes + 1 }
  match t.get j with
  | .split _ f v m lo hi =>
      let a := anc.push f
      return .split v m (← conv t depth a lo) (← conv t depth a hi)
  | .stellar _ _ i k α β lo hi =>
      return .stellar i k α β (← conv t depth #[] lo) (← conv t depth #[] hi)
  | .leaf _ f (.cert r) =>
      let key := tripleKey r.triple
      -- climb from the leaf while the fact's key facts hold
      let chain := (anc.push f).reverse
      let mut best : Option Frame := none
      for fr in chain do
        let mk := frameKey fr ++ key
        let ok ← match (← get).memo.get? mk with
          | some b => pure b
          | none => do
              let fact : Row := ⟨fr.seg, fr.kind, fr.center, fr.radius, r.triple, [], [], fr.aff⟩
              let b := decide fact.KeyFacts && decide ((factPoly fact).Ok fact)
              modify fun s => { s with memo := s.memo.insert mk b }
              pure b
        if ok then best := some fr else break
      match best with
      | none =>
          modify fun s => { s with failed := s.failed + 1 }
          return .leaf (.cert r)
      | some fr =>
          let mk := frameKey fr ++ key
          let k ← match (← get).factIx.get? mk with
            | some k => pure k
            | none => do
                let fact : Row := ⟨fr.seg, fr.kind, fr.center, fr.radius, r.triple, [], [], fr.aff⟩
                let k := (← get).facts.size
                modify fun s =>
                  { s with facts := s.facts.push fact, fps := s.fps.push (factPoly fact),
                           factIx := s.factIx.insert mk k }
                pure k
          let s ← get
          match refine s.facts[k]! s.fps[k]! f r depth with
          | some pl =>
              modify fun s => { s with converted := s.converted + 1 }
              return setFact k pl
          | none =>
              modify fun s => { s with failed := s.failed + 1 }
              return .leaf (.cert r)
  | .leaf _ _ l => return .leaf l


/-! ## Encoding -/

def zig (z : Int) : Nat := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1
def ratT (q : ℚ) : Array Nat := #[zig q.num, q.den]
def kindCode : ChartKind → Nat
  | .plain => 0 | .tube => 1 | .wedge => 2 | .wtube => 3 | .skew => 4 | .atube => 5
  | .btube false => 6 | .btube true => 7 | .askew => 8 | .bskew false => 9
  | .bskew true => 10 | .aplain => 11 | .bplain false => 12 | .bplain true => 13
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

partial def treeT : RTree → Array Nat
  | .split v m lo hi => #[0, v] ++ ratT m ++ treeT lo ++ treeT hi
  | .stellar i j α β lo hi => #[1, i, j] ++ ratT α ++ ratT β ++ treeT lo ++ treeT hi
  | .leaf (.flip k) => #[2, k.val]
  | .leaf (.handoff h) => #[3, handoffCode h]
  | .leaf (.cert r) => #[4] ++ tripleT r.triple ++ splitT r.split ++ shiftT r.shift
  | .sharedPA t sp sh k => #[5] ++ tripleT t ++ splitT sp ++ shiftT sh ++ #[k]
  | .hole f => #[6] ++ frameT f
  | .leaf _ => panic! "unexpected shared leaf"

def cost : RTree → ℕ
  | .split .. => 3 | .stellar .. => 10 | .sharedPA .. => 40 | .leaf (.cert _) => 9000
  | .leaf _ => 50 | .hole _ => 5

structure Chunk where
  id : ℕ
  frame : Frame
  tree : RTree
  cost : ℕ

partial def chunkify (budget : ℕ) (f : Frame) (t : RTree) : StateM (Array Chunk) (RTree × ℕ) := do
  let sub := fun (g : Frame) (x : RTree) => do
    let (x', c) ← chunkify budget g x
    if c ≥ budget then
      let id := (← get).size
      modify (·.push ⟨id, g, x', c⟩)
      pure (RTree.hole g, 5)
    else pure (x', c)
  match t with
  | .split v m lo hi =>
      let (a, ca) ← sub (f.lower v m) lo
      let (b, cb) ← sub (f.upper v m) hi
      pure (.split v m a b, ca + cb + cost t)
  | .stellar i j α β lo hi =>
      let (a, ca) ← sub (f.stellar i j α β) lo
      let (b, cb) ← sub (f.stellar j i β α) hi
      pure (.stellar i j α β a b, ca + cb + cost t)
  | _ => pure (t, cost t)

def main (args : List String) : IO Unit := do
  match args with
  | ["stats", pack, ti, d] =>
      let tables := decodeTablesV3 (← IO.FS.readFile pack)
      let t := tables[ti.toNat!]!
      let (tree, st) := (conv t d.toNat! #[] 0).run {}
      IO.println s!"table {ti}: {st.nodes} nodes, certs converted {st.converted}, failed {st.failed}, facts {st.facts.size}"
      let _ := tree

  | ["emit", pack, ti, d, root, stage, budget, group, outDir, dataDir] =>
      let tables := decodeTablesV3 (← IO.FS.readFile pack)
      let tix := ti.toNat!
      let t := tables[tix]!
      let (tree, st) := (conv t d.toNat! #[] 0).run {}
      IO.println s!"table {ti}: certs converted {st.converted}, failed {st.failed}, facts {st.facts.size}"
      let rootF := (t.get 0).frame
      let H : Handoffs := CornerCoverage.stage AtlasProjectiveSolutionTree.cornerEps
        (if stage == "cpocket" then CornerCoverage.cpocketStage else CornerCoverage.noHandoff)
      unless tree.check H st.facts st.fps rootF do throw (IO.userError "native check FAILED")
      IO.println "native check ok"
      let ((top, topCost), chunks) := (chunkify budget.toNat! rootF tree).run #[]
      let chunks := chunks.push ⟨chunks.size, rootF, top, topCost⟩
      IO.println s!"{chunks.size} chunks"
      let tn := s!"T{ti}"
      let pre := s!"Noperts.Stellated.KernelCorner.{tn}"
      IO.FS.createDirAll s!"{outDir}/{tn}"
      IO.FS.createDirAll dataDir
      -- facts slice: facts, fact polynomials, and the root node
      let mut fout : Array Nat := #[st.facts.size]
      for fr in st.facts do
        fout := fout ++ frameT ⟨fr.seg, fr.kind, fr.center, fr.radius, fr.aff⟩ ++ tripleT fr.triple
      for fp in st.fps do fout := fout ++ factPolyT fp
      fout := fout ++ #[1, 2, 0, 1] ++ frameT rootF ++ #[0]
      let factsS := ",".intercalate (fout.toList.map toString) ++ ","
      IO.FS.writeFile s!"{dataDir}/{tn}.facts.slice3" factsS
      IO.FS.writeFile s!"{outDir}/{tn}/Facts.lean" s!"import Noperts.Stellated.KernelLoadAff
import Noperts.Stellated.AtlasProjectiveSolutionTree
import Noperts.Stellated.CornerCoverage

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

stellated_corner_chunk \"{dataDir}/{tn}.facts.slice3\" 0 0 1 src
-- data hash {hash factsS} (the loaded file is not tracked by Lake)
noncomputable abbrev facts : Array CornerCertificate.Row := src.facts.toArray
noncomputable abbrev fps : Array FactPoly := src.fpolys.toArray
abbrev H : Handoffs := CornerCoverage.stage AtlasProjectiveSolutionTree.cornerEps {if stage == "cpocket" then "CornerCoverage.cpocketStage" else "CornerCoverage.noHandoff"}

end {pre}
"
      -- per-fact modules
      let nf := st.facts.size
      let fgroups := (nf + 9) / 10
      for fg in List.range fgroups do
        let mut src := s!"import StellatedKernel.{tn}.Facts\n\nopen Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel\n\nnamespace {pre}\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        for k in List.range (min 10 (nf - 10 * fg)) do
          let i := 10 * fg + k
          src := src ++ s!"\ntheorem fact{i} : ∀ h : {i} < facts.size, (facts[{i}]'h).KeyFacts := by decide +kernel\n\ntheorem fpoly{i} : ∀ h : {i} < fps.size, FactPolyAt facts fps ⟨{i}, h⟩ := by decide +kernel\n"
        src := src ++ s!"\nend {pre}\n"
        IO.FS.writeFile s!"{outDir}/{tn}/F{fg}.lean" src
      let fimports := "\n".intercalate ((List.range fgroups).map fun g => s!"import StellatedKernel.{tn}.F{g}")
      let cases := fun (nm : String) => "\n".intercalate ((List.range nf).map fun i => s!"    | {i}, h => {nm}{i} h")
      IO.FS.writeFile s!"{outDir}/{tn}/FactsOk.lean" s!"import StellatedKernel.{tn}.Facts
{fimports}

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

set_option maxRecDepth 100000

theorem facts_ok : ∀ fact ∈ facts, fact.KeyFacts := by
  have hsize : facts.size = {nf} := by decide +kernel
  have key : ∀ i (h : i < facts.size), (facts[i]'h).KeyFacts := fun i h => match i, h with
{cases "fact"}
    | _ + {nf}, h => absurd h (by omega)
  intro fact hm
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hm
  exact key i hi

theorem fps_ok : FactPolysOk facts fps := by
  have hsize : fps.size = {nf} := by decide +kernel
  have key : ∀ i (h : i < fps.size), FactPolyAt facts fps ⟨i, h⟩ := fun i h => match i, h with
{cases "fpoly"}
    | _ + {nf}, h => absurd h (by omega)
  intro k
  exact key k.val k.isLt

end {pre}
"
      -- modules: cheap chunks packed by cost (`group` = module cost budget)
      let modBudget := group.toNat!
      let isCert := fun (c : Chunk) => match c.tree with | .leaf (.cert _) => true | _ => false
      let mut mods : Array (String × Array Chunk) := #[]
      let mut cur : Array Chunk := #[]
      let mut curCost := 0
      let mut nG := 0
      for c in chunks do
        if !isCert c then
          cur := cur.push c; curCost := curCost + c.cost
          if curCost ≥ modBudget then
            mods := mods.push (s!"G{nG}", cur); nG := nG + 1; cur := #[]; curCost := 0
      if cur.size > 0 then mods := mods.push (s!"G{nG}", cur)
      -- cert chunks (~7 GB of kernel heap each): a few modules of many; the kernel cache
      -- resets per theorem, so a module peaks at one chunk's heap, and few such modules
      -- can run at once
      let certs := chunks.filter isCert
      let nC := min certs.size 5
      let per := (certs.size + nC - 1) / max nC 1
      for k in List.range nC do
        mods := mods.push (s!"C{k}", (certs.toList.drop (k * per)).take per |>.toArray)
      let mut idOf : Std.HashMap String ℕ := {}
      for c in chunks do idOf := idOf.insert (frameKey c.frame) c.id
      let mut modOf : Std.HashMap ℕ String := {}
      for (m, cs) in mods do
        for c in cs do modOf := modOf.insert c.id m
      for (m, members) in mods do
        let tag := m.toLower
        let mut dout : Array Nat := #[members.size]
        for c in members do dout := dout ++ #[c.id] ++ frameT c.frame ++ treeT c.tree
        let dataS := ",".intercalate (dout.toList.map toString) ++ ","
        IO.FS.writeFile s!"{dataDir}/{tn}.{tag}.rt" dataS
        let thms := members.toList.map fun c => s!"
theorem {tag}.ok{c.id} (hH : ∀ h f, H.Valid h f → Covered f)
    (hf : ∀ fact ∈ facts, fact.KeyFacts) (hp : FactPolysOk facts fps)
    (hh : ∀ x ∈ {tag}.c{c.id}.holeList, Covered x) : Covered {tag}.c{c.id}.frame :=
  CornerAff.RTree.check_sound H hH facts fps hf hp _ _ (by decide +kernel)
    (CornerAff.holes_of {tag}.c{c.id}.holes_eq hh)
"
        IO.FS.writeFile s!"{outDir}/{tn}/{m}.lean" s!"import StellatedKernel.{tn}.Facts

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

stellated_rtree_chunks \"{dataDir}/{tn}.{tag}.rt\" {tag}
-- data hash {hash dataS} (the loaded file is not tracked by Lake)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
{"".intercalate thms}
end {pre}
"
      -- assembly: one theorem per chunk, children first (chunks are in post-order)
      let gimports := "\n".intercalate (mods.toList.map fun (m, _) => s!"import StellatedKernel.{tn}.{m}")
      let mut asm := ""
      for c in chunks do
        let tag := (modOf.getD c.id "").toLower
        let kids := c.tree.holes.map fun h => idOf.getD (frameKey h) 0
        let hp := kids.foldr (fun k acc => s!"(covered_cons (cov{k} hH) {acc})") "covered_nil"
        asm := asm ++ s!"theorem cov{c.id} (hH : ∀ h f, H.Valid h f → Covered f) :
    Covered {tag}.c{c.id}.frame :=
  {tag}.ok{c.id} hH facts_ok fps_ok {hp}

"
      let last := chunks.size - 1
      let lastTag := (modOf.getD last "").toLower
      IO.FS.writeFile s!"{outDir}/{tn}/Table.lean" s!"import StellatedKernel.{tn}.FactsOk
{gimports}

open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel

set_option Elab.async false

namespace {pre}

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem covered_nil : ∀ x ∈ ([] : List Frame), Covered x := fun _ h => nomatch h

theorem covered_cons \{a : Frame} \{l : List Frame} (ha : Covered a)
    (hl : ∀ x ∈ l, Covered x) : ∀ x ∈ a :: l, Covered x := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact hl x hx

{asm}theorem table_covered (hH : ∀ h f, H.Valid h f → Covered f) : Covered {root} := by
  have e : {lastTag}.c{last}.frame = {root} := by decide +kernel
  rw [← e]
  exact cov{last} hH

end {pre}
"
      IO.println "written"
  | _ => throw (IO.userError "usage: cornerAffGen stats|emit ...")
