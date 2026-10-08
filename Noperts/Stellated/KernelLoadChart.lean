module

public import Lean
public import Noperts.Stellated.KernelLoad
public import Noperts.Stellated.PackedCTree
public meta import Lean
public meta import Noperts.Stellated.KernelLoad
public meta import Noperts.Stellated.PackedCTree

public section

/-!
# Loading kernel chart-tree chunks

`stellated_ctree_chunks "file" pre` decodes a packed chunk file natively and
defines, for every chunk `id`, the literal constants `pre.c<id>.steps`,
`pre.c<id>.tree`, `pre.c<id>.holeList` and the proof
`pre.c<id>.holes_eq : pre.c<id>.tree.holes = pre.c<id>.holeList` (by `Eq.refl`,
checked by the kernel).
-/

open Lean Elab Command Term Meta

namespace Noperts.Stellated.KernelLoad

open ChartKernelTree AtlasProjectiveLocalCertificate

meta section

def stepTy : Expr := Lean.mkConst ``Step

def stepE : Step → Expr
  | .half c up => mkApp2 (Lean.mkConst ``Step.half) (finE 5 c.val) (boolE up)
  | .root => Lean.mkConst ``Step.root
  | .view k => mkApp (Lean.mkConst ``Step.view) (finE 4 k.val)
  | .cut w k => mkApp2 (Lean.mkConst ``Step.cut) (vec3RatE w) (finE 3 k.val)

def stepsE (l : List Step) : Expr := listE stepTy (l.map stepE)

def intsE (l : List ℤ) : Expr := listE (Lean.mkConst ``Int) (l.map intE)

def componentE (c : AtlasProjectiveMixedGlobalCertificate.Component) : Expr :=
  mkApp3 (Lean.mkConst ``AtlasProjectiveMixedGlobalCertificate.Component.mk) (axisE c.certificate)
    (vec3FinE 8 c.innerIndex) (ratE c.ballMultiplier)

def finVecE (n m : ℕ) (f : Fin n → Fin m) : Expr :=
  vecE (finTy m) ((List.finRange n).map fun i => finE m (f i).val).toArray

partial def ctreeE : CTree → Expr
  | .cayleySplit c lo hi => mkApp3 (Lean.mkConst ``CTree.cayleySplit) (finE 5 c.val)
      (ctreeE lo) (ctreeE hi)
  | .viewRoot t => mkApp (Lean.mkConst ``CTree.viewRoot) (ctreeE t)
  | .viewSplit a b c d => mkApp4 (Lean.mkConst ``CTree.viewSplit) (ctreeE a) (ctreeE b)
      (ctreeE c) (ctreeE d)
  | .viewCut w a b c => mkApp4 (Lean.mkConst ``CTree.viewCut) (vec3RatE w) (ctreeE a)
      (ctreeE b) (ctreeE c)
  | .projective e h => mkApp2 (Lean.mkConst ``CTree.projective)
      (mkAppN (Lean.mkConst ``EdgeRest.mk) #[natE e.edgePred,
        finVecE (e.edgePred + 1) 8 e.outerIndex, finVecE (e.edgePred + 1) 8 e.innerIndex,
        finVecE (e.edgePred + 1) 8 e.nonzeroWitness, vec3RatE e.ballMultiplier])
      (intsE h)
  | .global g h => mkApp2 (Lean.mkConst ``CTree.global)
      (mkApp3 (Lean.mkConst ``GlobalRest.mk) (axisE g.certificate) (vec3FinE 8 g.innerIndex)
        (ratE g.ballMultiplier))
      (intsE h)
  | .mixed m h => mkApp2 (Lean.mkConst ``CTree.mixed)
      (mkApp2 (Lean.mkConst ``MixedRest.mk)
        (vecE (Lean.mkConst ``AtlasProjectiveMixedGlobalCertificate.Component)
          ((List.finRange 4).map fun k => componentE (m.component k)).toArray)
        (vecE ratTy ((List.finRange 4).map fun k => ratE (m.weight k)).toArray))
      (intsE h)
  | .projectiveLocal l => mkApp (Lean.mkConst ``CTree.projectiveLocal)
      (mkAppN (Lean.mkConst ``LocalRest.mk) #[finE 12 l.symmetryIndex.val,
        vecE (Lean.mkConst ``AxisCertificate)
          ((List.finRange 4).map fun j => axisE (l.certificate j)).toArray,
        ratE l.c, ratE l.δ, ratE l.r])
  | .tube s r idx w => mkApp4 (Lean.mkConst ``CTree.tube) (finE 12 s.val) (ratE r)
      (finE 64 idx.val)
      (vecE (mkForall `c .default (finTy 3) ratTy)
        ((List.finRange 3).map fun i => vec3RatE (w i)).toArray)
  | .octahedron => Lean.mkConst ``CTree.octahedron
  | .flip form negate => mkApp2 (Lean.mkConst ``CTree.flip) (finE 12 form.val) (boolE negate)
  | .corner => Lean.mkConst ``CTree.corner
  | .hole steps => mkApp (Lean.mkConst ``CTree.hole) (stepsE steps)

syntax (name := ctreeChunksCmd) "stellated_ctree_chunks " str ident : command

@[command_elab ctreeChunksCmd] def elabCTreeChunks : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let pre := stx[2].getId
  let chunks := PackedCTree.decodeChunks (← IO.FS.readFile path)
  liftTermElabM do
    let ns := (← getCurrNamespace) ++ pre
    let stepsTy := mkApp (Lean.mkConst ``List [Level.zero]) stepTy
    for (id, steps, t) in chunks do
      let base := ns ++ Name.mkSimple s!"c{id}"
      let defn := fun (n : Name) (ty v : Expr) => do
        withExporting <| addDecl <| .defnDecl {
          name := base ++ n, levelParams := [], type := ty, value := v, hints := .abbrev,
          safety := .safe }
        modifyEnv (addNoncomputable · (base ++ n))
      defn `steps stepsTy (stepsE steps)
      defn `tree (Lean.mkConst ``CTree) (ctreeE t)
      let holeListTy := mkApp (Lean.mkConst ``List [Level.zero]) stepsTy
      defn `holeList holeListTy (listE stepsTy (t.holes.map stepsE))
      let lhs := mkApp (Lean.mkConst ``CTree.holes) (Lean.mkConst (base ++ `tree))
      let rhs := Lean.mkConst (base ++ `holeList)
      withExporting <| addDecl <| .thmDecl {
        name := base ++ `holes_eq, levelParams := [],
        type := mkApp3 (Lean.mkConst ``Eq [Level.one]) holeListTy lhs rhs,
        value := mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) holeListTy rhs }

end

end Noperts.Stellated.KernelLoad

end
