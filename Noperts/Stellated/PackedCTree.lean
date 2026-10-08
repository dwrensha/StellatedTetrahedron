module

public import Noperts.Stellated.ChartKernelTree
public import Noperts.Stellated.PackedLocalViewTree

@[expose] public section

/-!
# Packed kernel chart trees

A comma-separated stream of naturals (integers zig-zag encoded, rationals as
`num den`).  A chunk file holds `count` chunks, each `id path tree`:

* path: `n` steps, each `0 c up` (halve coordinate `c`), `1` (view root),
  `2 k` (view split child), `3 w₀ w₁ w₂ k` (view cut child);
* tree, in prefix order: `0 c lo hi` Cayley split; `1 t` view root;
  `2 t₀ t₁ t₂ t₃` view split; `3 w₀ w₁ w₂ t₀ t₁ t₂` view cut;
  `4 e o… i… w… b₀ b₁ b₂ n h…` projective edge leaf (`e + 1` indices each);
  `5 axis i₀ i₁ i₂ b n h…` global leaf; `6 (axis i₀ i₁ i₂ b)⁴ w⁴ n h…` mixed
  leaf; `7 s axis⁴ c δ r` projective local leaf; `8 s r idx w⁹` tube;
  `9` octahedron; `10 form negate` flip; `11` corner; `12 path` hole.
-/

namespace Noperts.Stellated.PackedCTree

open PackedLocalViewTree ChartKernelTree AtlasProjectiveLocalCertificate

/-! ## Encoding -/

def zig (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

structure Enc where
  out : Array String := #[]

abbrev EncM := StateM Enc

def putN (n : ℕ) : EncM Unit := modify fun e => { e with out := e.out.push (toString n) }
def putZ (z : ℤ) : EncM Unit := putN (zig z)
def putQ (q : ℚ) : EncM Unit := do putZ q.num; putN q.den

def putAxis (a : AxisCertificate) : EncM Unit := do
  for f in [a.edgeStart, a.edgeFinish, a.edgeStart₂, a.edgeFinish₂] do
    for i in List.finRange 3 do putN (f i).val
  for i in List.finRange 3 do putN (a.mix i).val
  for f in [a.index, a.nonzeroWitness] do
    for i in List.finRange 3 do putN (f i).val
  putQ a.B

def putStep : Step → EncM Unit
  | .half c up => do putN 0; putN c.val; putN (if up then 1 else 0)
  | .root => putN 1
  | .view k => do putN 2; putN k.val
  | .cut w k => do putN 3; putQ (w 0); putQ (w 1); putQ (w 2); putN k.val

def putHints (h : List ℤ) : EncM Unit := do
  putN h.length
  for x in h do putZ x

partial def putTree : CTree → EncM Unit
  | .cayleySplit c lo hi => do putN 0; putN c.val; putTree lo; putTree hi
  | .viewRoot t => do putN 1; putTree t
  | .viewSplit a b c d => do
      putN 2; putTree a; putTree b; putTree c; putTree d
  | .viewCut w a b c => do
      putN 3; putQ (w 0); putQ (w 1); putQ (w 2)
      putTree a; putTree b; putTree c
  | .projective e h => do
      putN 4; putN e.edgePred
      for f in [e.outerIndex, e.innerIndex, e.nonzeroWitness] do
        for i in List.finRange (e.edgePred + 1) do putN (f i).val
      for j in List.finRange 3 do putQ (e.ballMultiplier j)
      putHints h
  | .global g h => do
      putN 5; putAxis g.certificate
      for i in List.finRange 3 do putN (g.innerIndex i).val
      putQ g.ballMultiplier; putHints h
  | .mixed m h => do
      putN 6
      for k in List.finRange 4 do
        let c := m.component k
        putAxis c.certificate
        for i in List.finRange 3 do putN (c.innerIndex i).val
        putQ c.ballMultiplier
      for k in List.finRange 4 do putQ (m.weight k)
      putHints h
  | .projectiveLocal l => do
      putN 7; putN l.symmetryIndex.val
      for j in List.finRange 4 do putAxis (l.certificate j)
      putQ l.c; putQ l.δ; putQ l.r
  | .tube s r idx w => do
      putN 8; putN s.val; putQ r; putN idx.val
      for i in List.finRange 3 do
        for j in List.finRange 3 do putQ (w i j)
  | .octahedron => putN 9
  | .flip form negate => do putN 10; putN form.val; putN (if negate then 1 else 0)
  | .corner => putN 11
  | .hole steps => do
      putN 12; putN steps.length
      for st in steps do putStep st

def putChunk (id : ℕ) (path : List Step) (t : CTree) : EncM Unit := do
  putN id
  putN path.length
  for s in path do putStep s
  putTree t

def encodeChunks (chunks : List (ℕ × List Step × CTree)) : String :=
  let e : EncM Unit := do
    putN chunks.length
    for (id, path, t) in chunks do putChunk id path t
  ",".intercalate (e.run {}).2.out.toList

/-! ## Decoding -/

instance : Inhabited CTree := ⟨.corner⟩

def readQ : Decoder ℚ := do
  let n ← readNat
  let d ← readNat
  pure ((zigzagInt n : ℚ) / d)

def readZ : Decoder ℤ := do return zigzagInt (← readNat)

def readFins (m k : ℕ) (f : ℕ → Fin m) : Decoder (List (Fin m)) := do
  let mut acc := #[]
  for _ in [0:k] do acc := acc.push (f (← readNat))
  pure acc.toList

def vecOf {α : Type} [Inhabited α] (n : ℕ) (l : List α) : Fin n → α := fun i => l.getD i.val default

def readHints : Decoder (List ℤ) := do
  let n ← readNat
  let mut acc := #[]
  for _ in [0:n] do acc := acc.push (← readZ)
  pure acc.toList

def readStep : Decoder Step := do
  let tag ← readNat
  if tag = 0 then
    let c ← readNat
    let up ← readNat
    pure (.half (fin5 c) (up = 1))
  else if tag = 1 then pure .root
  else if tag = 2 then pure (.view (fin4 (← readNat)))
  else
    let w0 ← readQ
    let w1 ← readQ
    let w2 ← readQ
    pure (.cut ![w0, w1, w2] (fin3 (← readNat)))

def readComponent : Decoder AtlasProjectiveMixedGlobalCertificate.Component := do
  let a ← readAxis
  let i ← readVertices
  let b ← readQ
  pure ⟨a, i, b⟩

partial def readCTree : Decoder CTree := do
  let tag ← readNat
  match tag with
  | 0 =>
      let c ← readNat
      let lo ← readCTree
      let hi ← readCTree
      pure (.cayleySplit (fin5 c) lo hi)
  | 1 => pure (.viewRoot (← readCTree))
  | 2 =>
      let a ← readCTree
      let b ← readCTree
      let c ← readCTree
      let d ← readCTree
      pure (.viewSplit a b c d)
  | 3 =>
      let w0 ← readQ
      let w1 ← readQ
      let w2 ← readQ
      let a ← readCTree
      let b ← readCTree
      let c ← readCTree
      pure (.viewCut ![w0, w1, w2] a b c)
  | 4 =>
      let e ← readNat
      let o ← readFins 8 (e + 1) fin8
      let i ← readFins 8 (e + 1) fin8
      let w ← readFins 8 (e + 1) fin8
      let b0 ← readQ
      let b1 ← readQ
      let b2 ← readQ
      let h ← readHints
      pure ((.projective ⟨e, vecOf _ o, vecOf _ i, vecOf _ w, ![b0, b1, b2]⟩ h))
  | 5 =>
      let a ← readAxis
      let i ← readVertices
      let b ← readQ
      let h ← readHints
      pure ((.global ⟨a, i, b⟩ h))
  | 6 =>
      let c0 ← readComponent
      let c1 ← readComponent
      let c2 ← readComponent
      let c3 ← readComponent
      let w0 ← readQ
      let w1 ← readQ
      let w2 ← readQ
      let w3 ← readQ
      let h ← readHints
      pure ((.mixed ⟨![c0, c1, c2, c3], ![w0, w1, w2, w3]⟩ h))
  | 7 =>
      let s ← readNat
      let cert ← readCertificate
      let c ← readQ
      let δ ← readQ
      let r ← readQ
      pure ((.projectiveLocal ⟨fin12 s, cert, c, δ, r⟩))
  | 8 =>
      let s ← readNat
      let r ← readQ
      let idx ← readNat
      let mut w : Array ℚ := #[]
      for _ in [0:9] do w := w.push (← readQ)
      pure ((.tube (fin12 s) r (fin64 idx)
        ![![w[0]!, w[1]!, w[2]!], ![w[3]!, w[4]!, w[5]!], ![w[6]!, w[7]!, w[8]!]]))
  | 9 => pure .octahedron
  | 10 =>
      let f ← readNat
      let n ← readNat
      pure ((.flip (fin12 f) (n = 1)))
  | 11 => pure .corner
  | _ =>
      let n ← readNat
      let mut path := #[]
      for _ in [0:n] do path := path.push (← readStep)
      pure (.hole path.toList)

def readChunk : Decoder (ℕ × List Step × CTree) := do
  let id ← readNat
  let n ← readNat
  let mut path := #[]
  for _ in [0:n] do path := path.push (← readStep)
  let t ← readCTree
  pure (id, path.toList, t)

def decodeChunks (packed : String) : Array (ℕ × List Step × CTree) :=
  (do
    let n ← readNat
    let mut acc := #[]
    for _ in [0:n] do acc := acc.push (← readChunk)
    pure acc : Decoder _) { data := packed.toUTF8 } |>.1

end Noperts.Stellated.PackedCTree
