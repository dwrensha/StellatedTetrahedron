import Noperts.Stellated.NativeExecutable
import Noperts.Stellated.PackedCornerTree
import Noperts.Stellated.CornerKernel

/-!
Probe: how many corner split nodes whose two children are (after merging,
bottom-up) shared leaves can themselves become a shared leaf, by re-using one
child's fact, split and shift on the parent box?

`compactCorner probe IN.pack TABLE`
-/

open Noperts.Stellated
open Noperts.Stellated.CornerTree CornerCertificate CornerPoly PackedCornerTree SparsePoly

def qf (q : ℚ) : Float :=
  (if q.num < 0 then -1 else 1) * q.num.natAbs.toFloat / q.den.toFloat

/-- Try to certify frame `f` with a shared leaf built from `r` (fact `k`). -/
def tryShared (facts : Array Row) (f : Frame) (r : Row) (k : ℕ) : Option Leaf :=
  let cand : Row := { r with center := f.center, radius := f.radius }
  match facts[k]? with
  | some fr => if decide (cand.SharedValid fr) then some (.shared cand k) else none
  | none => none

def probe (tables : Array Table) (index : Nat) : IO Unit := do
  let t := tables[index]!
  let mut merged : Array (Option Leaf) := Array.replicate t.size none
  let mut leaves := 0
  let mut sharedLeaves := 0
  let mut merges := 0
  for k' in List.range t.size do
    let k := t.size - 1 - k'
    match t.get k with
    | .leaf _ _ l =>
        leaves := leaves + 1
        if let .shared _ _ := l then
          sharedLeaves := sharedLeaves + 1
          merged := merged.set! k (some l)
    | .split _ f _ _ lo hi =>
        match merged[lo]!, merged[hi]! with
        | some (.shared r1 k1), some (.shared r2 k2) =>
            let res := (tryShared t.facts f r1 k1).orElse fun _ =>
              if k2 == k1 && r2.split == r1.split && r2.shift == r1.shift then none
              else tryShared t.facts f r2 k2
            if let some l := res then
              merges := merges + 1
              merged := merged.set! k (some l)
        | _, _ => pure ()
    | _ => pure ()
  IO.println s!"table {index}: {t.size} nodes, {leaves} leaves ({sharedLeaves} shared), {merges} merges (−{2 * merges} nodes)"
  (← IO.getStdout).flush

def evalFl (x : Array Float) (p : Poly) : Float :=
  p.foldl (fun acc t =>
    let (_, m) := t.1.foldl (fun (i, m) e => (i + 1, m * (x[i]!) ^ e.toFloat)) (0, 1.0)
    acc + qf t.2 * m) 0

/-- Grid minimum of `F` (with the fact's triple) over a frame: `n` points per
non-degenerate variable among `ε λ u a b c ρ`. -/
def gridMin (F : Poly) (f : Frame) (n : Nat) : Float := Id.run do
  let c := (List.range 7).map fun i => (f.center.getD i 0)
  let r := (List.range 7).map fun i => (f.radius.getD i 0)
  let vars := (List.range 7).filter fun i => r[i]! != 0
  let total := n ^ vars.length
  let mut best : Float := 1e300
  for idx in List.range total do
    let mut x : Array Float := (c.map qf).toArray
    let mut k := idx
    for v in vars do
      let t := (k % n).toFloat / (n - 1).toFloat
      k := k / n
      x := x.set! v (qf (c[v]! - r[v]!) + t * qf (2 * r[v]!))
    if x[0]! > 0 then
      best := min best (evalFl x F)
  return best

/-- For split nodes with two shared-leaf children: does `F` of either child's
triple look nonnegative on the parent box (grid sampling)? -/
def truthProbe (tables : Array Table) (index n : Nat) (cap : Nat) : IO Unit := do
  let t := tables[index]!
  let mut tried := 0
  let mut plausible := 0
  for k in List.range t.size do
    if tried < cap then
      if let .split _ f _ _ lo hi := t.get k then
        if let (.leaf _ _ (.shared r1 _), .leaf _ _ (.shared r2 _)) := (t.get lo, t.get hi) then
          tried := tried + 1
          let F1 := r1.F
          let F2 := r2.F
          -- scale-free tolerance: relative to the coefficient size
          let scale1 := F1.foldl (fun a t => max a (Float.abs (qf t.2))) 0
          let scale2 := F2.foldl (fun a t => max a (Float.abs (qf t.2))) 0
          let m1 := gridMin F1 f n
          let m2 := gridMin F2 f n
          if m1 ≥ -1e-12 * scale1 || m2 ≥ -1e-12 * scale2 then plausible := plausible + 1
  IO.println s!"table {index}: {tried} leaf-pair parents, {plausible} with F ≥ 0 on a {n}-grid"
  (← IO.getStdout).flush

def shapeProbe (tables : Array Table) : IO Unit := do
  let mut hist : Std.HashMap (Nat × Nat × Bool) Nat := {}
  for t in tables do
    for k in List.range t.size do
      if let .leaf _ _ (.shared r _) := t.get k then
        let key := (r.split.length, (r.shift.filter (· != 0)).length,
          r.isTube && decide (r.lo 6 ≤ 0))
        hist := hist.insert key (hist.getD key 0 + 1)
  for (k, v) in hist.toList do
    IO.println s!"split {k.1} shift-nonzero {k.2.1} rho-face {k.2.2}: {v}"

open CornerKernel in
/-- The fact's stripped displacement `S` (integer coefficients) and its monomial. -/
def factS (fact : Row) : IPoly × Mono :=
  let F := normalize (divByMono fact.D [1])
  let m := gcdMono fact.nonnegVars F
  let S := divByMono F m
  let K := S.foldl (fun acc t => Nat.lcm acc t.2.den) 1
  (S.map fun t => (t.1, (t.2 * (K : ℚ)).num), m)

/-- Integer anchor data of a box: `(D, X, H)`. -/
def boxInts (r : Row) : ℕ × List ℤ × List ℤ :=
  let qs := (List.range 7).map r.box.center ++ (List.range 7).map r.box.radius
  let D := qs.foldl (fun acc q => Nat.lcm acc q.den) 1
  (D, (List.range 7).map fun i => (r.box.center i * D).num,
    (List.range 7).map fun i => (r.box.radius i * D).num)

open CornerKernel in
def leafCheap (S : IPoly) (b : ℕ × List ℤ × List ℤ) : Bool :=
  let (D, X, H) := b
  cheapI S D (fun i => X.getD i 0) (fun i => -(H.getD i 0)) (fun i => H.getD i 0) ||
    cheapI S D (fun i => X.getD i 0 - H.getD i 0) (fun _ => 0) (fun i => 2 * H.getD i 0)

def showI (S : CornerKernel.IPoly) : String :=
  "[" ++ ", ".intercalate (S.map fun t => s!"({t.1}, {t.2})") ++ "]"

/-- Emit a kernel probe: the first `n` plain shared leaves of fact `k` of a table. -/
def emitCheap (tables : Array Table) (index k n : Nat) (out : String) : IO Unit := do
  let t := tables[index]!
  let mut counts : Array Nat := Array.replicate t.facts.size 0
  for j in List.range t.size do
    if let .leaf _ _ (.shared _ k') := t.get j then counts := counts.modify k' (· + 1)
  let k := if k < t.facts.size then k else
    (List.range t.facts.size).foldl (fun b i => if counts[i]! > counts[b]! then i else b) 0
  let some fact := t.facts[k]? | throw (IO.userError "no such fact")
  let (S, m) := factS fact
  let mut boxes : Array (ℕ × List ℤ × List ℤ) := #[]
  let mut passN := 0
  for j in List.range t.size do
    if boxes.size < n then
      if let .leaf _ _ (.shared r k') := t.get j then
        if k' == k && r.split.isEmpty && r.shift.all (· == 0) then
          let b := boxInts r
          if leafCheap S b then
            passN := passN + 1
            boxes := boxes.push b
  IO.println s!"fact {k}: S {S.length} terms, m {m}, degree {CornerKernel.maxDeg S}; {boxes.size} leaves, native cheapI pass {passN}"
  let lines := boxes.toList.map fun (D, X, H) => s!"  ({D}, {X}, {H})"
  IO.FS.writeFile out s!"import Noperts.Stellated.CornerKernel
open Noperts.Stellated.CornerKernel

def S0 : IPoly := {showI S}
def boxes : List (Nat × List Int × List Int) := [
{",\n".intercalate lines}]

set_option maxRecDepth 100000
theorem leaves_ok : (boxes.all fun (D, X, H) =>
    cheapI S0 D (fun i => X.getD i 0) (fun i => -(H.getD i 0)) (fun i => H.getD i 0) ||
    cheapI S0 D (fun i => X.getD i 0 - H.getD i 0) (fun _ => 0) (fun i => 2 * H.getD i 0)) = true := by
  decide +kernel
"

/-- Stripped integer polynomial of `F` for a given allowed-variable set. -/
def stripI (allowed : ℕ → Bool) (F : Poly) : CornerKernel.IPoly × Mono :=
  let m := gcdMono allowed F
  let S := divByMono F m
  let K := S.foldl (fun acc t => Nat.lcm acc t.2.den) 1
  (S.map fun t => (t.1, (t.2 * (K : ℚ)).num), m)

def cheapStats (tables : Array Table) (index stride : Nat) : IO Unit := do
  let t := tables[index]!
  let Fs := t.facts.map fun f => normalize (divByMono f.D [1])
  let Ss := t.facts.map factS
  let mut n := 0
  let mut okFact := 0
  let mut okLeaf := 0
  let mut seen := 0
  for j in List.range t.size do
    if let .leaf _ _ (.shared r k) := t.get j then
      if r.split.isEmpty && r.shift.all (· == 0) then
        seen := seen + 1
        if seen % stride == 0 then
          n := n + 1
          let b := boxInts r
          if leafCheap Ss[k]!.1 b then okFact := okFact + 1
          if leafCheap (stripI r.nonnegVars Fs[k]!).1 b then okLeaf := okLeaf + 1
  IO.println s!"table {index}: {n} plain leaves sampled; fact-stripped pass {okFact}, leaf-stripped pass {okLeaf}"

def main (args : List String) : IO Unit := do
  if let ["cheapstats", i, stride, t] := args then
    cheapStats (decodeTablesV2 (← IO.FS.readFile i)) t.toNat! stride.toNat!
    return
  if let ["emitcheap", i, t, k, n, o] := args then
    emitCheap (decodeTablesV2 (← IO.FS.readFile i)) t.toNat! k.toNat! n.toNat! o
    return
  if let ["shape", i] := args then
    shapeProbe (decodeTablesV2 (← IO.FS.readFile i))
    return
  if let ["truth", i, n, cap, t] := args then
    let tables := decodeTablesV2 (← IO.FS.readFile i)
    truthProbe tables t.toNat! n.toNat! cap.toNat!
    return
  if let "probe" :: i :: ts := args then
    let tables := decodeTablesV2 (← IO.FS.readFile i)
    let ts := if ts == ["all"] then List.range tables.size else ts.map String.toNat!
    let tasks ← ts.mapM fun t => IO.asTask (probe tables t)
    for task in tasks do
      let _ ← IO.wait task
