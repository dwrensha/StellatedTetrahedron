module

public import Lean
public import Noperts.Stellated.KernelLoad
public import Noperts.Stellated.PackedRTree
public meta import Lean
public meta import Noperts.Stellated.KernelLoad
public meta import Noperts.Stellated.PackedRTree

public section

/-!
# Packed reparametrized corner trees and their loader

A chunk file holds `count` chunks, each `id frame tree` (frames as in
`PackedCornerTree.readFrame`); tree, in prefix order: `0 v m lo hi` split,
`1 i j α β lo hi` stellar split, `2 k` flip, `3 h` hand-off,
`4 triple split shift` certificate, `5 triple split shift k` shared leaf,
`6 frame` hole.

`stellated_rtree_chunks "file" pre` defines `pre.c<id>.frame`, `pre.c<id>.tree`,
`pre.c<id>.holeList` and `pre.c<id>.holes_eq : pre.c<id>.tree.holes = pre.c<id>.holeList`.
-/



open Lean Elab Command Term Meta

namespace Noperts.Stellated.KernelLoad

open CornerTree CornerCertificate CornerAff

meta section

partial def rtreeE : RTree → Expr
  | .split v m lo hi => mkApp4 (Lean.mkConst ``RTree.split) (natE v) (ratE m) (rtreeE lo)
      (rtreeE hi)
  | .stellar i j α β lo hi => mkAppN (Lean.mkConst ``RTree.stellar)
      #[natE i, natE j, ratE α, ratE β, rtreeE lo, rtreeE hi]
  | .leaf l => mkApp (Lean.mkConst ``RTree.leaf) (leafE l)
  | .sharedPA t sp sh k => mkApp4 (Lean.mkConst ``RTree.sharedPA) (tripleE t) (splitListE sp)
      (ratListE sh) (natE k)
  | .hole f => mkApp (Lean.mkConst ``RTree.hole) (frameE f)

syntax (name := rtreeChunksCmd) "stellated_rtree_chunks " str ident : command

@[command_elab rtreeChunksCmd] def elabRTreeChunks : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let pre := stx[2].getId
  let chunks := PackedRTree.decodeChunks (← IO.FS.readFile path)
  liftTermElabM do
    let ns := (← getCurrNamespace) ++ pre
    let frameTy := Lean.mkConst ``Frame
    let listTy := mkApp (Lean.mkConst ``List [Level.zero]) frameTy
    for (id, f, t) in chunks do
      let base := ns ++ Name.mkSimple s!"c{id}"
      let defn := fun (n : Name) (ty v : Expr) => do
        withExporting <| addDecl <| .defnDecl {
          name := base ++ n, levelParams := [], type := ty, value := v, hints := .abbrev,
          safety := .safe }
        modifyEnv (addNoncomputable · (base ++ n))
      defn `frame frameTy (frameE f)
      defn `tree (Lean.mkConst ``RTree) (rtreeE t)
      defn `holeList listTy (listE frameTy (t.holes.map frameE))
      let lhs := mkApp (Lean.mkConst ``RTree.holes) (Lean.mkConst (base ++ `tree))
      let rhs := Lean.mkConst (base ++ `holeList)
      withExporting <| addDecl <| .thmDecl {
        name := base ++ `holes_eq, levelParams := [],
        type := mkApp3 (Lean.mkConst ``Eq [Level.one]) listTy lhs rhs,
        value := mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) listTy rhs }

end

end Noperts.Stellated.KernelLoad

end
