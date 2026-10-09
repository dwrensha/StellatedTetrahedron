module

public import Lean
public import Noperts.Stellated.PackedLocalViewTree
public import Noperts.Stellated.PackedCornerTree
public import Noperts.Stellated.PackedKTree
public import Noperts.Stellated.LocalKernelInstance
public meta import Lean
public meta import Noperts.Stellated.PackedLocalViewTree
public meta import Noperts.Stellated.PackedCornerTree
public meta import Noperts.Stellated.PackedKTree
public meta import Noperts.Stellated.LocalKernelInstance

public section

/-!
# Literal row loading for kernel checking

Elaboration-time commands that decode packed certificate tables natively and add
their rows as literal constants (`Expr`s built directly, no parsing), so that
`decide +kernel` never decodes data.  Rationals are `mkRat num den` (the kernel
normalizes each with one GMP gcd, memoized within a declaration); finite indices
are `Fin.mk` with `decide` proofs; `Fin n → α` fields are `![…]` vectors.
-/

open Lean Elab Command Term Meta

namespace Noperts.Stellated.KernelLoad

open AtlasProjectiveLocalViewTree AtlasProjectiveLocalCertificate PackedLocalViewTree

meta section

def natE (n : ℕ) : Expr := mkRawNatLit n

def intE : ℤ → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (natE n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (natE n)

def reflTrueE : Expr :=
  mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)

def decideProofE (prop inst : Expr) : Expr :=
  mkApp3 (Lean.mkConst ``of_decide_eq_true) prop inst reflTrueE

/-- A rational literal as `Rat.mk'` with decided side conditions, so `num` and
`den` are projections (a `mkRat` literal is renormalized on every use). -/
def ratE (q : ℚ) : Expr :=
  let nE := intE q.num
  let dE := natE q.den
  let natTy := Lean.mkConst ``Nat
  let neProp := mkApp3 (Lean.mkConst ``Ne [Level.one]) natTy dE (natE 0)
  let neInst := mkApp2 (Lean.mkConst ``instDecidableNot) (mkApp3 (Lean.mkConst ``Eq [Level.one])
    natTy dE (natE 0)) (mkApp2 (Lean.mkConst ``instDecidableEqNat) dE (natE 0))
  let gE := mkApp2 (Lean.mkConst ``Nat.gcd) (mkApp (Lean.mkConst ``Int.natAbs) nE) dE
  let copProp := mkApp3 (Lean.mkConst ``Eq [Level.one]) natTy gE (natE 1)
  let copInst := mkApp2 (Lean.mkConst ``instDecidableEqNat) gE (natE 1)
  mkApp4 (Lean.mkConst ``Rat.mk') nE dE (decideProofE neProp neInst)
    (decideProofE copProp copInst)

def finE (n v : ℕ) : Expr :=
  let nE := natE n
  let vE := natE v
  let prop := mkApp4 (Lean.mkConst ``LT.lt [Level.zero]) (Lean.mkConst ``Nat)
    (Lean.mkConst ``instLTNat) vE nE
  let inst := mkApp2 (Lean.mkConst ``Nat.decLt) vE nE
  mkApp3 (Lean.mkConst ``Fin.mk) nE vE (decideProofE prop inst)

/-- `![e₀, …, e_{k-1}] : Fin k → τ`. -/
def vecConsE (τ : Expr) (es : Array Expr) : Expr := Id.run do
  let mut acc := mkApp (Lean.mkConst ``Matrix.vecEmpty [Level.zero]) τ
  for idx in [0:es.size] do
    let i := es.size - 1 - idx
    acc := mkApp4 (Lean.mkConst ``Matrix.vecCons [Level.zero]) τ (natE idx) es[i]! acc
  acc

/-- The function `i ↦ eᵢ : Fin k → τ` (for `τ : Type`) as a balanced `Bool.rec` tree on
`Nat.blt i.val m`: the kernel selects an entry in `⌈log₂ k⌉` accelerated comparisons, where
an `![…]` literal unfolds `Fin.cons` and `Fin.induction` once per preceding entry. -/
def vecE (τ : Expr) (es : Array Expr) : Expr :=
  if es.size = 0 then vecConsE τ es else
  let n := es.size
  let v := mkApp2 (Lean.mkConst ``Fin.val) (natE n) (.bvar 0)
  let motive := mkLambda `_ .default (Lean.mkConst ``Bool) τ
  let rec go (fuel lo hi : ℕ) : Expr :=
    match fuel with
    | 0 => es[lo]!
    | fuel + 1 =>
      if hi ≤ lo + 1 then es[lo]! else
      let mid := (lo + hi) / 2
      mkApp4 (Lean.mkConst ``Bool.rec [Level.one]) motive (go fuel mid hi) (go fuel lo mid)
        (mkApp2 (Lean.mkConst ``Nat.blt) v (natE mid))
  mkLambda `i .default (mkApp (Lean.mkConst ``Fin) (natE n)) (go n 0 n)

def ratTy : Expr := Lean.mkConst ``Rat

def finTy (n : ℕ) : Expr := mkApp (Lean.mkConst ``Fin) (natE n)

def vec3RatE (f : Fin 3 → ℚ) : Expr := vecE ratTy #[ratE (f 0), ratE (f 1), ratE (f 2)]

def triangleE (t : AtlasProjectiveView.Triangle ℚ) : Expr :=
  vecE (mkForall `c .default (finTy 3) ratTy) #[vec3RatE (t 0), vec3RatE (t 1), vec3RatE (t 2)]

def vec3FinE (n : ℕ) (f : Fin 3 → Fin n) : Expr :=
  vecE (finTy n) #[finE n (f 0).val, finE n (f 1).val, finE n (f 2).val]

def axisE (a : AxisCertificate) : Expr :=
  mkAppN (Lean.mkConst ``AxisCertificate.mk) #[
    vec3FinE 8 a.edgeStart, vec3FinE 8 a.edgeFinish, vec3FinE 8 a.edgeStart₂,
    vec3FinE 8 a.edgeFinish₂, vec3FinE 1001 a.mix, vec3FinE 8 a.index,
    vec3FinE 8 a.nonzeroWitness, ratE a.B]

structure Ctx where
  rootInterval : Expr

def mkCtx : TermElabM Ctx := do
  let e ← Term.elabTerm (← `(AtlasPose.rootInterval ℚ)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  return { rootInterval := ← instantiateMVars e }

def boxE (ctx : Ctx) (b : Box) : Expr :=
  mkAppN (Lean.mkConst ``Box.mk) #[ctx.rootInterval, finE 8 b.root.val, triangleE b.triangle,
    finE 4 b.chart.val, finE 12 b.symmetryIndex.val,
    vecE (Lean.mkConst ``AxisCertificate) #[axisE (b.certificate 0), axisE (b.certificate 1),
      axisE (b.certificate 2), axisE (b.certificate 3)],
    ratE b.c, ratE b.δ, ratE b.r]

def localRowE (ctx : Ctx) : Row → Expr
  | .split id children root tri =>
      mkAppN (Lean.mkConst ``Row.split) #[natE id,
        vecE (Lean.mkConst ``Nat) #[natE (children 0), natE (children 1), natE (children 2),
          natE (children 3)], finE 8 root.val, triangleE tri]
  | .certificate id box => mkApp2 (Lean.mkConst ``Row.certificate) (natE id) (boxE ctx box)
  | .cut id children root tri w =>
      mkAppN (Lean.mkConst ``Row.cut) #[natE id,
        vecE (Lean.mkConst ``Nat) #[natE (children 0), natE (children 1), natE (children 2)],
        finE 8 root.val, triangleE tri, vec3RatE w]

/-- `stellated_local_chunk "pack" table lo hi name` defines
`name : List Row` holding rows `[lo, hi)` of the packed local table. -/
syntax (name := localChunkCmd)
  "stellated_local_chunk " str num num num ident : command

@[command_elab localChunkCmd] def elabLocalChunk : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let table := stx[2].isNatLit?.getD 0
  let lo := stx[3].isNatLit?.getD 0
  let hi := stx[4].isNatLit?.getD 0
  let name := stx[5].getId
  let data ← IO.FS.readFile path
  let t := decodePackedTable table data
  unless lo < hi ∧ hi ≤ t.size do throwError "bad range [{lo}, {hi}) of {t.size} rows"
  liftTermElabM do
    let ctx ← mkCtx
    let rowTy := Lean.mkConst ``Row
    let rows := (List.range (hi - lo)).map fun k => t.get (lo + k)
    let listE := rows.foldr
      (fun r acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) rowTy (localRowE ctx r) acc)
      (mkApp (Lean.mkConst ``List.nil [Level.zero]) rowTy)
    let declName := (← getCurrNamespace) ++ name
    withExporting <| addDecl <| .defnDecl {
      name := declName, levelParams := [],
      type := mkApp (Lean.mkConst ``List [Level.zero]) rowTy, value := listE,
      hints := .abbrev, safety := .safe }
    modifyEnv (addNoncomputable · declName)

/-- `Tree8 τ d` as an `Expr`. -/
def tree8TyE (τ : Expr) : ℕ → Expr
  | 0 => τ
  | d + 1 => mkForall `i .default (finTy 8) (tree8TyE τ d)

/-- A depth-`d` tree over `leaves` (padded with the last leaf). -/
partial def tree8E (τ : Expr) (leaves : Array Expr) (d : ℕ) (base : ℕ) : Expr :=
  if d = 0 then leaves[min base (leaves.size - 1)]!
  else
    let step := 8 ^ (d - 1)
    vecE (tree8TyE τ (d - 1)) ((Array.range 8).map fun k =>
      tree8E τ leaves (d - 1) (base + k * step))

/-- `stellated_local_tree "pack" table name` defines `name.depth : ℕ`,
`name.tree : Tree8 Row name.depth`, and `name.size`, `name.r`, `name.sym`. -/
syntax (name := localTreeCmd) "stellated_local_tree " str num ident : command

@[command_elab localTreeCmd] def elabLocalTree : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let table := stx[2].isNatLit?.getD 0
  let name := stx[3].getId
  let data ← IO.FS.readFile path
  let t := decodePackedTable table data
  liftTermElabM do
    let ctx ← mkCtx
    let ns := (← getCurrNamespace) ++ name
    let mut d := 0
    while 8 ^ d < t.size do d := d + 1
    let rowTy := Lean.mkConst ``Row
    let leaves := (Array.range t.size).map fun k => localRowE ctx (t.get k)
    let add := fun (n : Name) (ty v : Expr) => withExporting <| addDecl <| .defnDecl {
      name := ns ++ n, levelParams := [], type := ty, value := v, hints := .abbrev,
      safety := .safe }
    add `depth (Lean.mkConst ``Nat) (natE d)
    add `size (Lean.mkConst ``Nat) (natE t.size)
    add `r ratTy (ratE t.r)
    add `sym (finTy 12) (finE 12 t.symmetryIndex.val)
    add `tree (mkApp2 (Lean.mkConst ``LocalKernel.Tree8) rowTy (natE d))
      (tree8E rowTy leaves d 0)
    for n in [`depth, `size, `r, `sym, `tree] do modifyEnv (addNoncomputable · (ns ++ n))

/-! ## Corner tables -/

section Corner
open CornerTree CornerCertificate CornerPoly

def boolE (b : Bool) : Expr := Lean.mkConst (if b then ``Bool.true else ``Bool.false)

def kindE : ChartKind → Expr
  | .plain => Lean.mkConst ``ChartKind.plain
  | .tube => Lean.mkConst ``ChartKind.tube
  | .wedge => Lean.mkConst ``ChartKind.wedge
  | .wtube => Lean.mkConst ``ChartKind.wtube
  | .skew => Lean.mkConst ``ChartKind.skew
  | .atube => Lean.mkConst ``ChartKind.atube
  | .btube b => mkApp (Lean.mkConst ``ChartKind.btube) (boolE b)
  | .askew => Lean.mkConst ``ChartKind.askew
  | .bskew b => mkApp (Lean.mkConst ``ChartKind.bskew) (boolE b)
  | .aplain => Lean.mkConst ``ChartKind.aplain
  | .bplain b => mkApp (Lean.mkConst ``ChartKind.bplain) (boolE b)

def listE (τ : Expr) (es : List Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) τ e acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) τ)

def ratListE (qs : List ℚ) : Expr := listE ratTy (qs.map ratE)

def affE (aff : List (List ℚ)) : Expr :=
  listE (mkApp (Lean.mkConst ``List [Level.zero]) ratTy) (aff.map ratListE)

def frameE (f : Frame) : Expr :=
  mkAppN (Lean.mkConst ``Frame.mk) #[boolE f.seg, kindE f.kind, ratListE f.center,
    ratListE f.radius, affE f.aff]

def tripleE (t : Triple) : Expr :=
  mkApp3 (Lean.mkConst ``Triple.mk) (triangleE t.edge) (vec3FinE 8 t.inner)
    (vec3FinE 8 t.outer)

def splitListE (sp : List (ℕ × Bool)) : Expr :=
  let pTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (Lean.mkConst ``Nat)
    (Lean.mkConst ``Bool)
  listE pTy (sp.map fun p => mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
    (Lean.mkConst ``Nat) (Lean.mkConst ``Bool) (natE p.1) (boolE p.2))

def cornerRowE (r : CornerCertificate.Row) : Expr :=
  mkAppN (Lean.mkConst ``CornerCertificate.Row.mk) #[boolE r.seg, kindE r.kind,
    ratListE r.center, ratListE r.radius, tripleE r.triple, splitListE r.split,
    ratListE r.shift, affE r.aff]

def handoffE (h : Handoff) : Expr :=
  Lean.mkConst (match h with
    | .tube => ``Handoff.tube | .wedge => ``Handoff.wedge | .wtube => ``Handoff.wtube
    | .skew => ``Handoff.skew | .cone => ``Handoff.cone | .pocket => ``Handoff.pocket
    | .spocket => ``Handoff.spocket | .ppocket => ``Handoff.ppocket
    | .cpocket => ``Handoff.cpocket)

def leafE : Leaf → Expr
  | .cert r => mkApp (Lean.mkConst ``Leaf.cert) (cornerRowE r)
  | .flip k => mkApp (Lean.mkConst ``Leaf.flip) (finE 12 k.val)
  | .handoff h => mkApp (Lean.mkConst ``Leaf.handoff) (handoffE h)
  | .shared r k => mkApp2 (Lean.mkConst ``Leaf.shared) (cornerRowE r) (natE k)
  | .sharedP r k => mkApp2 (Lean.mkConst ``Leaf.sharedP) (cornerRowE r) (natE k)

def nodeE : Node → Expr
  | .split id f v m lo hi => mkAppN (Lean.mkConst ``Node.split)
      #[natE id, frameE f, natE v, ratE m, natE lo, natE hi]
  | .stellar id f i j α β lo hi => mkAppN (Lean.mkConst ``Node.stellar)
      #[natE id, frameE f, natE i, natE j, ratE α, ratE β, natE lo, natE hi]
  | .leaf id f l => mkApp3 (Lean.mkConst ``Node.leaf) (natE id) (frameE f) (leafE l)

def monoE (m : List ℕ) : Expr := listE (Lean.mkConst ``Nat) (m.map natE)

def factPolyE (fp : CornerKernel.FactPoly) : Expr :=
  let monoTy := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Nat)
  let nbTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (Lean.mkConst ``Nat)
    (Lean.mkConst ``Bool)
  let tTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) monoTy nbTy
  let termE := fun (t : List ℕ × ℕ × Bool) =>
    mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) monoTy nbTy (monoE t.1)
      (mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) (Lean.mkConst ``Nat)
        (Lean.mkConst ``Bool) (natE t.2.1) (boolE t.2.2))
  mkApp3 (Lean.mkConst ``CornerKernel.FactPoly.mk) (listE tTy (fp.S.map termE)) (monoE fp.m)
    (natE fp.K)

/-- `stellated_corner_chunk "corner-v2.pack" table lo hi name` defines
`name : List Node` (nodes `[lo, hi)` of that table) and `name.facts : List Row`. -/
syntax (name := cornerChunkCmd)
  "stellated_corner_chunk " str num num num ident : command

@[command_elab cornerChunkCmd] def elabCornerChunk : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let table := stx[2].isNatLit?.getD 0
  let lo := stx[3].isNatLit?.getD 0
  let hi := stx[4].isNatLit?.getD 0
  let name := stx[5].getId
  let data ← IO.FS.readFile path
  -- a one-table slice file (from `shareCorner slice`) when `table` is 0 and the
  -- path ends in `.slice`; otherwise a full v2 pack
  let t := if path.endsWith ".slice3" then
      (PackedCornerTree.readTableV3 { data := data.toUTF8 }).1
    else if path.endsWith ".slice" then
      (PackedCornerTree.readTableV2 { data := data.toUTF8 }).1
    else (PackedCornerTree.decodeTablesV2 data)[table]!
  unless lo < hi ∧ hi ≤ t.size do throwError "bad range [{lo}, {hi}) of {t.size} rows"
  liftTermElabM do
    let ns := (← getCurrNamespace) ++ name
    let nodeTy := Lean.mkConst ``Node
    let nodes := (List.range (hi - lo)).map fun k => nodeE (t.get (lo + k))
    withExporting <| addDecl <| .defnDecl {
      name := ns, levelParams := [], type := mkApp (Lean.mkConst ``List [Level.zero]) nodeTy,
      value := listE nodeTy nodes, hints := .abbrev, safety := .safe }
    modifyEnv (addNoncomputable · ns)
    let rowTy := Lean.mkConst ``CornerCertificate.Row
    withExporting <| addDecl <| .defnDecl {
      name := ns ++ `facts, levelParams := [],
      type := mkApp (Lean.mkConst ``List [Level.zero]) rowTy,
      value := listE rowTy (t.facts.toList.map cornerRowE), hints := .abbrev, safety := .safe }
    modifyEnv (addNoncomputable · (ns ++ `facts))
    let fpTy := Lean.mkConst ``CornerKernel.FactPoly
    withExporting <| addDecl <| .defnDecl {
      name := ns ++ `fpolys, levelParams := [],
      type := mkApp (Lean.mkConst ``List [Level.zero]) fpTy,
      value := listE fpTy (t.fpolys.toList.map factPolyE), hints := .abbrev, safety := .safe }
    modifyEnv (addNoncomputable · (ns ++ `fpolys))

def intListE (l : List ℤ) : Expr := listE (Lean.mkConst ``Int) (l.map intE)

def iframeE (f : CornerKernel.IFrame) : Expr :=
  mkAppN (Lean.mkConst ``CornerKernel.IFrame.mk) #[boolE f.seg, kindE f.kind, natE f.D,
    intListE f.X, intListE f.H]

partial def ktreeE : CornerKernel.KTree → Expr
  | .split v M s lo hi => mkAppN (Lean.mkConst ``CornerKernel.KTree.split)
      #[natE v, intE M, natE s, ktreeE lo, ktreeE hi]
  | .anchor ks t => mkApp2 (Lean.mkConst ``CornerKernel.KTree.anchor)
      (listE (Lean.mkConst ``Nat) (ks.map natE)) (ktreeE t)
  | .leafP k => mkApp (Lean.mkConst ``CornerKernel.KTree.leafP) (natE k)
  | .flipP k => mkApp (Lean.mkConst ``CornerKernel.KTree.flipP) (finE 12 k.val)
  | .leaf l => mkApp (Lean.mkConst ``CornerKernel.KTree.leaf) (leafE l)
  | .hole f => mkApp (Lean.mkConst ``CornerKernel.KTree.hole) (iframeE f)

/-- `stellated_ktree_chunks "file" pre` defines `pre.c<id>.frame : IFrame` and
`pre.c<id>.tree : KTree` for every chunk of a packed chunk file. -/
syntax (name := ktreeChunksCmd) "stellated_ktree_chunks " str ident : command

@[command_elab ktreeChunksCmd] def elabKTreeChunks : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let pre := stx[2].getId
  let chunks := PackedKTree.decodeChunks (← IO.FS.readFile path)
  liftTermElabM do
    let ns := (← getCurrNamespace) ++ pre
    for (id, f, t) in chunks do
      let base := ns ++ Name.mkSimple s!"c{id}"
      withExporting <| addDecl <| .defnDecl {
        name := base ++ `frame, levelParams := [], type := Lean.mkConst ``CornerKernel.IFrame,
        value := iframeE f, hints := .abbrev, safety := .safe }
      modifyEnv (addNoncomputable · (base ++ `frame))
      withExporting <| addDecl <| .defnDecl {
        name := base ++ `tree, levelParams := [], type := Lean.mkConst ``CornerKernel.KTree,
        value := ktreeE t, hints := .abbrev, safety := .safe }
      modifyEnv (addNoncomputable · (base ++ `tree))

end Corner

end

end Noperts.Stellated.KernelLoad

end
