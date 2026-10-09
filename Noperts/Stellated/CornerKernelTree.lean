module

public import Noperts.Stellated.CornerTree
public import Noperts.Stellated.FlipPolys

@[expose] public section

/-!
# Corner trees over integer frames, for the kernel

A frame without reparametrization is an integer box: center `X / D` and radius
`H / D` (seven coordinates).  `KTree.check` walks a tree top-down, computing
each child's frame with a few integer operations (no rational arithmetic and no
stored frames).  Shared facts are *anchored* at a node whose box lies in the
fact's box; leaves below cite them (`KTree.leafP`) and run the packed cheap
bound directly on the integer box.  Other leaves convert the frame to a
rational `Frame` once and use `Leaf.Valid`.  A `hole` defers a subtree to a
separate theorem about its frame, so large trees split into chunks.
-/

namespace Noperts.Stellated.CornerKernel

open scoped RealInnerProductSpace
open SparsePoly CornerCertificate CornerPoly CornerTree
open AtlasProjectiveLocalRigidity AtlasProjectiveView
open Noperts.ProjectiveView

structure IFrame where
  seg : Bool
  kind : ChartKind
  D : ℕ
  X : List ℤ
  H : List ℤ
deriving DecidableEq

def IFrame.Mem (f : IFrame) (y : ℕ → ℝ) : Prop :=
  ∀ i, |y i - (f.X.getD i 0 : ℝ) / f.D| ≤ (f.H.getD i 0 : ℝ) / f.D

def IFrame.hi1 (f : IFrame) : ℤ := f.X.getD 1 0 + f.H.getD 1 0

/-- The claim of an integer frame. -/
def ICovered (f : IFrame) : Prop :=
  ∀ (p : AtlasPose ℝ) (offset : ℝ²) (y : ℕ → ℝ), Coords f.seg f.kind p y →
    f.Mem y → 0 < y 0 → (f.kind.hasRho = true → 0 < y 6) → (0 < f.hi1 → 0 < y 1) →
    p.FlipReduced → 1 ≤ viewScale 0 p →
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull

/-- Well-formed: `D > 0`, at most seven coordinates, nonnegative radii. -/
def IFrame.WF (f : IFrame) : Bool :=
  Nat.blt 0 f.D && Nat.ble f.X.length 7 && Nat.ble f.H.length f.X.length && f.H.all (0 ≤ ·)

/-- `[g k x₀ h₀, g (k+1) x₁ h₁, …]` over `xs` (with `hs` padded by zeros), by `List.rec`. -/
def zipIdxR (g : ℕ → ℤ → ℤ → ℤ) (xs : List ℤ) : ℕ → List ℤ → List ℤ :=
  @List.rec ℤ (fun _ => ℕ → List ℤ → List ℤ) (fun _ _ => [])
    (fun x _ ih k hs => g k x (hs.headD 0) :: ih (Nat.succ k) hs.tail) xs

/-- `l.map g`, by `List.rec`. -/
def mapR (g : ℤ → ℤ) (l : List ℤ) : List ℤ :=
  @List.rec ℤ (fun _ => List ℤ) [] (fun x _ ih => g x :: ih) l

/-- The child frame of a split of variable `v` at `M / (D s)`: `[lo, M]`
(`upper = false`) or `[M, hi]`, with denominators `2 D s`. -/
def IFrame.child (f : IFrame) (v : ℕ) (M : ℤ) (s : ℕ) (upper : Bool) : IFrame :=
  let lo := (s : ℤ) * (f.X.getD v 0 - f.H.getD v 0)
  let hi := (s : ℤ) * (f.X.getD v 0 + f.H.getD v 0)
  let a := if upper then M else lo
  let b := if upper then hi else M
  let s2 : ℤ := Int.ofNat (Nat.mul 2 s)
  { f with D := Nat.mul (Nat.mul 2 f.D) s,
           X := zipIdxR (fun i x _ => if i = v then Int.add a b else Int.mul s2 x) f.X 0 [],
           H := zipIdxR (fun i _ h => if i = v then Int.sub b a else Int.mul s2 h) f.X 0 f.H }

/-- `l.foldr (fun x a => Nat.gcd x.natAbs a) acc`, by `List.rec`. -/
def gcdL (l : List ℤ) (acc : ℕ) : ℕ :=
  @List.rec ℤ (fun _ => ℕ) acc (fun x _ ih => Nat.gcd x.natAbs ih) l

/-- Divide `D`, `X`, `H` by their common divisor (keeps numbers small). -/
def IFrame.reduce (f : IFrame) : IFrame :=
  let g := gcdL f.X (gcdL f.H f.D)
  { f with D := Nat.div f.D g, X := mapR (· / (g : ℤ)) f.X, H := mapR (· / (g : ℤ)) f.H }

theorem int_add_eq' (a b : ℤ) : Int.add a b = a + b := rfl
theorem int_sub_eq' (a b : ℤ) : Int.sub a b = a - b := rfl
theorem int_mul_eq' (a b : ℤ) : Int.mul a b = a * b := rfl

theorem zipIdxR_cons (g : ℕ → ℤ → ℤ → ℤ) (x : ℤ) (xs : List ℤ) (k : ℕ) (hs : List ℤ) :
    zipIdxR g (x :: xs) k hs = g k x (hs.headD 0) :: zipIdxR g xs (Nat.succ k) hs.tail := rfl

theorem zipIdxR_length (g : ℕ → ℤ → ℤ → ℤ) (xs : List ℤ) :
    ∀ (k : ℕ) (hs : List ℤ), (zipIdxR g xs k hs).length = xs.length := by
  induction xs with
  | nil => intro _ _; rfl
  | cons x xs ih => intro k hs; rw [zipIdxR_cons, List.length_cons, ih]; rfl

theorem zipIdxR_getD (g : ℕ → ℤ → ℤ → ℤ) (xs : List ℤ) : ∀ (k : ℕ) (hs : List ℤ) (i : ℕ),
    (zipIdxR g xs k hs).getD i 0 = if i < xs.length then g (k + i) (xs.getD i 0) (hs.getD i 0) else 0 := by
  induction xs with
  | nil => intro _ _ _; rfl
  | cons x xs ih =>
      intro k hs i
      rw [zipIdxR_cons]
      cases i with
      | zero =>
          simp only [List.getD_cons_zero, List.length_cons, Nat.zero_lt_succ, ite_true, Nat.add_zero]
          cases hs <;> rfl
      | succ i =>
          rw [List.getD_cons_succ, ih]
          have e1 : Nat.succ k + i = k + (i + 1) := by omega
          rw [e1]
          simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getD_cons_succ]
          cases hs with
          | nil => simp
          | cons h t => rfl

theorem mapR_eq (g : ℤ → ℤ) : ∀ l : List ℤ, mapR g l = l.map g
  | [] => rfl
  | x :: l => by
      show g x :: mapR g l = _
      rw [mapR_eq g l]; rfl

theorem gcdL_cons (x : ℤ) (l : List ℤ) (acc : ℕ) : gcdL (x :: l) acc = Nat.gcd x.natAbs (gcdL l acc) :=
  rfl

/-- The frame as a rational `Frame` (no reparametrization). -/
def IFrame.toFrame (f : IFrame) : Frame :=
  ⟨f.seg, f.kind, (List.range f.X.length).map fun i => ((f.X.getD i 0 : ℚ) / f.D),
    (List.range f.X.length).map fun i => ((f.H.getD i 0 : ℚ) / f.D), []⟩

/-- The integer box lies in the rational box of `r`. -/
def IFrame.inBox (f : IFrame) (r : Row) : Bool :=
  Nat.ble r.center.length 7 && Nat.ble r.radius.length 7 &&
    (List.range 7).all fun i =>
      decide (|(f.X.getD i 0 : ℚ) / f.D - r.box.center i| + (f.H.getD i 0 : ℚ) / f.D ≤
        r.box.radius i)

inductive KTree where
  | split (v : ℕ) (M : ℤ) (s : ℕ) (lo hi : KTree)
  /-- Anchor facts `ks`: their boxes contain this frame. -/
  | anchor (ks : List ℕ) (t : KTree)
  /-- A kernel shared leaf citing anchored fact `k`. -/
  | leafP (k : ℕ)
  /-- A flip leaf checked by the cheap bound on its flip polynomial (`flipFP`). -/
  | flipP (k : Fin 12)
  /-- Any other leaf, on the rational frame. -/
  | leaf (l : Leaf)
  /-- A subtree proved separately, at frame `f`. -/
  | hole (f : IFrame)

section
variable (H : Handoffs) (facts : Array Row) (fps : Array FactPoly)

/-- The cheap bound for fact polynomial `fp` on the integer box. -/
def cheapI7 (fp : FactPoly) (f : IFrame) : Bool :=
  let Hn := f.H.map Int.toNat
  let Y := (List.range 7).map fun i => f.X.getD i 0 - f.H.getD i 0
  cheapP fp.S f.D (f.X.map Int.natAbs) (f.X.map fun x => decide (x < 0)) Hn true ||
    cheapP fp.S f.D (Y.map Int.natAbs) (Y.map fun x => decide (x < 0)) (Hn.map (2 * ·)) false

/-- A fact anchored with its `hi₁ > 0` flag. -/
def anchorOk (f : IFrame) (k : ℕ) : Bool :=
  match facts[k]? with
  | some r => decide (r.aff = [] ∧ r.seg = f.seg ∧ r.kind = f.kind) && f.inBox r
  | none => false

def anchorFlag (k : ℕ) : Bool :=
  match facts[k]? with
  | some r => decide (0 < r.hi 1)
  | none => true

def leafPOk (f : IFrame) (active : List (ℕ × Bool)) (k : ℕ) : Bool :=
  match active.lookup k, fps[k]? with
  | some flag, some fp =>
      (!flag || decide (0 < f.hi1)) &&
      (List.range fp.m.length).all (fun i =>
        decide (fp.m.getD i 0 = 0) || decide (f.H.getD i 0 ≤ f.X.getD i 0)) &&
      cheapI7 fp f
  | _, _ => false

def KTree.check : IFrame → List (ℕ × Bool) → KTree → Bool
  | f, act, .split v M s lo hi =>
      Nat.blt v f.X.length && Nat.blt 0 s &&
        decide ((s : ℤ) * (f.X.getD v 0 - f.H.getD v 0) ≤ M ∧
          M ≤ (s : ℤ) * (f.X.getD v 0 + f.H.getD v 0)) &&
        KTree.check (f.child v M s false).reduce act lo &&
        KTree.check (f.child v M s true).reduce act hi
  | f, act, .anchor ks t =>
      ks.all (anchorOk facts f) && KTree.check f (ks.map (fun k => (k, anchorFlag facts k)) ++ act) t
  | f, act, .leafP k => leafPOk fps f act k
  | f, _, .flipP k =>
      match flipFP f.seg f.kind k with
      | some fp => cheapI7 (scaleSub fp (f.D ^ 10)) f
      | none => false
  | f, _, .leaf l => decide (l.Valid H facts fps f.toFrame)
  | f, _, .hole g => decide (g = f)

/-- The holes of a tree. -/
def KTree.holes : KTree → List IFrame
  | .split _ _ _ lo hi => lo.holes ++ hi.holes
  | .anchor _ t => t.holes
  | .leafP _ => []
  | .flipP _ => []
  | .leaf _ => []
  | .hole g => [g]

end

/-! ## Soundness: frames -/

theorem getD_range_map (n : ℕ) (f : ℕ → ℤ) (i : ℕ) :
    ((List.range n).map f).getD i 0 = if i < n then f i else 0 := by
  by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]

theorem getD_of_length_le {n : ℕ} (l : List ℤ) (h : l.length ≤ n) (i : ℕ) (hi : ¬ i < n) :
    l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ i)]

structure IFrame.Good (f : IFrame) : Prop where
  D : 0 < f.D
  X : f.X.length ≤ 7
  H : f.H.length ≤ f.X.length
  Hnn : ∀ i, 0 ≤ f.H.getD i 0

theorem IFrame.good_of_wf (f : IFrame) (h : f.WF = true) : f.Good := by
  simp only [IFrame.WF, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hD, hX⟩, hH⟩, hnn⟩ := h
  refine ⟨hD, hX, hH, fun i => ?_⟩
  simp only [List.getD_eq_getElem?_getD]
  cases hget : f.H[i]? with
  | none => simp
  | some x => simpa using hnn x (List.mem_of_getElem? hget)

section child
variable (f : IFrame) (v : ℕ) (M : ℤ) (s : ℕ)

theorem IFrame.child_D (upper : Bool) : (f.child v M s upper).D = 2 * f.D * s := rfl

theorem IFrame.child_X_length (upper : Bool) : (f.child v M s upper).X.length = f.X.length := by
  simp only [IFrame.child]; exact zipIdxR_length _ _ _ _

theorem IFrame.child_H_length (upper : Bool) : (f.child v M s upper).H.length = f.X.length := by
  simp only [IFrame.child]; exact zipIdxR_length _ _ _ _

/-- The child's interval in coordinate `v` is `[a, b] / (D s)`. -/
def IFrame.childA (upper : Bool) : ℤ :=
  if upper then M else (s : ℤ) * (f.X.getD v 0 - f.H.getD v 0)

def IFrame.childB (upper : Bool) : ℤ :=
  if upper then (s : ℤ) * (f.X.getD v 0 + f.H.getD v 0) else M

theorem IFrame.child_X (upper : Bool) (i : ℕ) : (f.child v M s upper).X.getD i 0 =
    if i < f.X.length then (if i = v then f.childA v M s upper + f.childB v M s upper
      else 2 * s * f.X.getD i 0) else 0 := by
  simp only [IFrame.child, zipIdxR_getD, IFrame.childA, IFrame.childB, Nat.zero_add,
    int_add_eq', int_sub_eq', int_mul_eq']
  rfl

theorem IFrame.child_H (upper : Bool) (i : ℕ) : (f.child v M s upper).H.getD i 0 =
    if i < f.X.length then (if i = v then f.childB v M s upper - f.childA v M s upper
      else 2 * s * f.H.getD i 0) else 0 := by
  simp only [IFrame.child, zipIdxR_getD, IFrame.childA, IFrame.childB, Nat.zero_add,
    int_add_eq', int_sub_eq', int_mul_eq']
  rfl

theorem abs_sub_le_iff' (y c r : ℝ) : |y - c| ≤ r ↔ c - r ≤ y ∧ y ≤ c + r := by
  rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

variable (hv : v < f.X.length) (hs : 0 < s)
  (hlo : (s : ℤ) * (f.X.getD v 0 - f.H.getD v 0) ≤ M)
  (hhi : M ≤ (s : ℤ) * (f.X.getD v 0 + f.H.getD v 0))
include hv hs hlo hhi

omit hv hs in
theorem IFrame.childA_le_childB (upper : Bool) : f.childA v M s upper ≤ f.childB v M s upper := by
  cases upper <;> simp only [IFrame.childA, IFrame.childB, Bool.false_eq_true, ite_false, ite_true] <;> omega

omit hv in
theorem IFrame.child_good (hg : f.Good) (upper : Bool) : (f.child v M s upper).Good := by
  refine ⟨?_, by rw [IFrame.child_X_length]; exact hg.X,
    by rw [IFrame.child_H_length, IFrame.child_X_length], fun i => ?_⟩
  · rw [IFrame.child_D]; have := hg.D; positivity
  · rw [IFrame.child_H]
    have := f.childA_le_childB v M s hlo hhi upper
    have := hg.Hnn i
    split_ifs <;> first | omega | positivity

/-- Membership in a child, coordinatewise. -/
theorem IFrame.mem_child_iff (hg : f.Good) (upper : Bool) (y : ℕ → ℝ) :
    (f.child v M s upper).Mem y ↔
      (∀ i, i ≠ v → |y i - (f.X.getD i 0 : ℝ) / f.D| ≤ (f.H.getD i 0 : ℝ) / f.D) ∧
      (f.childA v M s upper : ℝ) / (f.D * s) ≤ y v ∧
      y v ≤ (f.childB v M s upper : ℝ) / (f.D * s) := by
  have hD : (0 : ℝ) < f.D := by exact_mod_cast hg.D
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hother : ∀ i, i ≠ v → (|y i - ((f.child v M s upper).X.getD i 0 : ℝ) /
      (f.child v M s upper).D| ≤ ((f.child v M s upper).H.getD i 0 : ℝ) /
      (f.child v M s upper).D ↔ |y i - (f.X.getD i 0 : ℝ) / f.D| ≤ (f.H.getD i 0 : ℝ) / f.D) := by
    intro i hi
    rw [IFrame.child_X, IFrame.child_H, IFrame.child_D]
    by_cases h7 : i < f.X.length
    · simp only [ite_eq_left h7, ite_eq_right hi]
      push_cast
      have e1 : (2 * (s : ℝ) * f.X.getD i 0) / (2 * f.D * s) = (f.X.getD i 0 : ℝ) / f.D := by
        field_simp
      have e2 : (2 * (s : ℝ) * f.H.getD i 0) / (2 * f.D * s) = (f.H.getD i 0 : ℝ) / f.D := by
        field_simp
      rw [e1, e2]
    · simp only [ite_eq_right h7, getD_of_length_le _ le_rfl i h7, getD_of_length_le _ hg.H i h7]
      simp
  have hvv : (|y v - ((f.child v M s upper).X.getD v 0 : ℝ) / (f.child v M s upper).D| ≤
      ((f.child v M s upper).H.getD v 0 : ℝ) / (f.child v M s upper).D) ↔
      (f.childA v M s upper : ℝ) / (f.D * s) ≤ y v ∧
        y v ≤ (f.childB v M s upper : ℝ) / (f.D * s) := by
    rw [IFrame.child_X, IFrame.child_H, IFrame.child_D, ite_eq_left hv, ite_eq_left hv, ite_eq_left rfl,
      ite_eq_left rfl, abs_sub_le_iff']
    push_cast
    have e1 : ((f.childA v M s upper : ℝ) + f.childB v M s upper) / (2 * f.D * s) -
        ((f.childB v M s upper : ℝ) - f.childA v M s upper) / (2 * f.D * s) =
        (f.childA v M s upper : ℝ) / (f.D * s) := by field_simp; ring
    have e2 : ((f.childA v M s upper : ℝ) + f.childB v M s upper) / (2 * f.D * s) +
        ((f.childB v M s upper : ℝ) - f.childA v M s upper) / (2 * f.D * s) =
        (f.childB v M s upper : ℝ) / (f.D * s) := by field_simp; ring
    rw [e1, e2]
  constructor
  · intro h
    exact ⟨fun i hi => (hother i hi).mp (h i), hvv.mp (h v)⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i = v
    · subst hi; exact hvv.mpr h2
    · exact (hother i hi).mpr (h1 i hi)

omit hv hlo hhi in
/-- The parent's coordinate `v` interval, over `D s`. -/
theorem IFrame.mem_v_iff (hg : f.Good) (y : ℕ → ℝ) :
    |y v - (f.X.getD v 0 : ℝ) / f.D| ≤ (f.H.getD v 0 : ℝ) / f.D ↔
      (((s : ℤ) * (f.X.getD v 0 - f.H.getD v 0) : ℤ) : ℝ) / (f.D * s) ≤ y v ∧
      y v ≤ (((s : ℤ) * (f.X.getD v 0 + f.H.getD v 0) : ℤ) : ℝ) / (f.D * s) := by
  have hD : (0 : ℝ) < f.D := by exact_mod_cast hg.D
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  rw [abs_sub_le_iff']
  push_cast
  have e1 : (s : ℝ) * ((f.X.getD v 0 : ℝ) - f.H.getD v 0) / (f.D * s) =
      (f.X.getD v 0 : ℝ) / f.D - (f.H.getD v 0 : ℝ) / f.D := by field_simp
  have e2 : (s : ℝ) * ((f.X.getD v 0 : ℝ) + f.H.getD v 0) / (f.D * s) =
      (f.X.getD v 0 : ℝ) / f.D + (f.H.getD v 0 : ℝ) / f.D := by field_simp
  rw [e1, e2]

/-- The two children cover the parent. -/
theorem IFrame.mem_child (hg : f.Good) {y : ℕ → ℝ} (hy : f.Mem y) :
    (f.child v M s false).Mem y ∨ (f.child v M s true).Mem y := by
  have hpar := (f.mem_v_iff v s hs hg y).mp (hy v)
  have hD : (0 : ℝ) < f.D := by exact_mod_cast hg.D
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  rcases le_total (y v) ((M : ℝ) / (f.D * s)) with hm | hm
  · left
    rw [f.mem_child_iff v M s hv hs hlo hhi hg]
    exact ⟨fun i _ => hy i, by simpa [IFrame.childA] using hpar.1,
      by simpa [IFrame.childB] using hm⟩
  · right
    rw [f.mem_child_iff v M s hv hs hlo hhi hg]
    exact ⟨fun i _ => hy i, by simpa [IFrame.childA] using hm,
      by simpa [IFrame.childB] using hpar.2⟩

/-- A child lies in its parent. -/
theorem IFrame.mem_of_child (hg : f.Good) (upper : Bool) {y : ℕ → ℝ}
    (hy : (f.child v M s upper).Mem y) : f.Mem y := by
  rw [f.mem_child_iff v M s hv hs hlo hhi hg] at hy
  obtain ⟨h1, h2, h3⟩ := hy
  have hD : (0 : ℝ) < f.D := by exact_mod_cast hg.D
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  intro i
  by_cases hi : i = v
  · subst hi
    rw [f.mem_v_iff i s hs hg]
    have hloR : ((((s : ℤ) * (f.X.getD i 0 - f.H.getD i 0) : ℤ) : ℝ)) ≤ f.childA i M s upper := by
      have : (s : ℤ) * (f.X.getD i 0 - f.H.getD i 0) ≤ f.childA i M s upper := by
        cases upper <;> simp only [IFrame.childA, Bool.false_eq_true, ite_false, ite_true] <;> omega
      exact_mod_cast this
    have hhiR : ((f.childB i M s upper : ℤ) : ℝ) ≤
        (((s : ℤ) * (f.X.getD i 0 + f.H.getD i 0) : ℤ) : ℝ) := by
      have : f.childB i M s upper ≤ (s : ℤ) * (f.X.getD i 0 + f.H.getD i 0) := by
        cases upper <;> simp only [IFrame.childB, Bool.false_eq_true, ite_false, ite_true] <;> omega
      exact_mod_cast this
    have hpos : (0 : ℝ) < f.D * s := by positivity
    exact ⟨le_trans (div_le_div_of_nonneg_right hloR hpos.le) h2,
      le_trans h3 (div_le_div_of_nonneg_right hhiR hpos.le)⟩
  · exact h1 i hi

theorem IFrame.child_hi1 (upper : Bool) (h : 0 < (f.child v M s upper).hi1) :
    0 < f.hi1 := by
  have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
  unfold IFrame.hi1 at h ⊢
  rw [IFrame.child_X, IFrame.child_H] at h
  by_cases h1len : 1 < f.X.length
  swap
  · simp only [ite_eq_right h1len] at h; exact absurd h (lt_irrefl 0)
  simp only [ite_eq_left h1len] at h
  have hB := f.childA_le_childB v M s hlo hhi upper
  split_ifs at h with h1
  · subst h1
    have : f.childB 1 M s upper ≤ (s : ℤ) * (f.X.getD 1 0 + f.H.getD 1 0) := by
      cases upper <;> simp only [IFrame.childB, Bool.false_eq_true, ite_false, ite_true] <;> omega
    by_contra hc
    have : (s : ℤ) * (f.X.getD 1 0 + f.H.getD 1 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsZ.le (by omega)
    omega
  · by_contra hc
    have : (2 * (s : ℤ)) * (f.X.getD 1 0 + f.H.getD 1 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    have e : 2 * (s : ℤ) * f.X.getD 1 0 + 2 * s * f.H.getD 1 0 =
        (2 * (s : ℤ)) * (f.X.getD 1 0 + f.H.getD 1 0) := by ring
    omega

end child

/-! ## Soundness: reduction -/

theorem gcdL_dvd : ∀ (l : List ℤ) (acc : ℕ),
    gcdL l acc ∣ acc ∧ ∀ x ∈ l, ((gcdL l acc : ℕ) : ℤ) ∣ x
  | [], acc => ⟨dvd_rfl, by simp⟩
  | x :: l, acc => by
      obtain ⟨h1, h2⟩ := gcdL_dvd l acc
      simp only [gcdL_cons] at h1 h2 ⊢
      refine ⟨(Nat.gcd_dvd_right _ _).trans h1, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
      · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 y hy)

theorem getD_map_div (l : List ℤ) (g : ℤ) (i : ℕ) :
    (mapR (· / g) l).getD i 0 = l.getD i 0 / g := by
  simp only [mapR_eq, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

section reduce
variable (f : IFrame) (hg : f.Good)

/-- The common divisor used by `reduce`. -/
def IFrame.rg (f : IFrame) : ℕ := gcdL f.X (gcdL f.H f.D)

theorem IFrame.reduce_D : f.reduce.D = f.D / f.rg := rfl

theorem IFrame.reduce_X (i : ℕ) : f.reduce.X.getD i 0 = f.X.getD i 0 / (f.rg : ℤ) :=
  getD_map_div _ _ _

theorem IFrame.reduce_H (i : ℕ) : f.reduce.H.getD i 0 = f.H.getD i 0 / (f.rg : ℤ) :=
  getD_map_div _ _ _

theorem IFrame.reduce_seg : f.reduce.seg = f.seg := rfl

theorem IFrame.reduce_kind : f.reduce.kind = f.kind := rfl

include hg

theorem IFrame.rg_spec : 0 < f.rg ∧ f.rg ∣ f.D ∧ (∀ i, (f.rg : ℤ) ∣ f.X.getD i 0) ∧
    (∀ i, (f.rg : ℤ) ∣ f.H.getD i 0) := by
  obtain ⟨hD1, hX⟩ := gcdL_dvd f.X (gcdL f.H f.D)
  obtain ⟨hD2, hH⟩ := gcdL_dvd f.H f.D
  have hgD : f.rg ∣ f.D := hD1.trans hD2
  refine ⟨Nat.pos_of_dvd_of_pos hgD hg.D, hgD, fun i => ?_, fun i => ?_⟩
  · simp only [List.getD_eq_getElem?_getD]
    cases h : f.X[i]? with
    | none => simp
    | some x => exact hX x (List.mem_of_getElem? h)
  · simp only [List.getD_eq_getElem?_getD]
    cases h : f.H[i]? with
    | none => simp
    | some x =>
        exact (Int.natCast_dvd_natCast.mpr hD1).trans (hH x (List.mem_of_getElem? h))

theorem IFrame.reduce_good : f.reduce.Good := by
  obtain ⟨hgpos, hgD, hX, hH⟩ := f.rg_spec hg
  refine ⟨?_, by simpa [IFrame.reduce, mapR_eq] using hg.X,
    by simpa [IFrame.reduce, mapR_eq] using hg.H,
    fun i => ?_⟩
  · rw [IFrame.reduce_D]; exact Nat.div_pos (Nat.le_of_dvd hg.D hgD) hgpos
  · rw [IFrame.reduce_H]; exact Int.ediv_nonneg (hg.Hnn i) (by positivity)

theorem IFrame.reduce_mem (y : ℕ → ℝ) : f.reduce.Mem y ↔ f.Mem y := by
  obtain ⟨hgpos, hgD, hX, hH⟩ := f.rg_spec hg
  have hgR : (f.rg : ℝ) ≠ 0 := by positivity
  have hgZ : ((f.rg : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hgR
  have hD : ((f.reduce.D : ℕ) : ℝ) = (f.D : ℝ) / f.rg := by
    rw [IFrame.reduce_D, Nat.cast_div hgD hgR]
  have e : ∀ x : ℤ, (f.rg : ℤ) ∣ x →
      ((x / (f.rg : ℤ) : ℤ) : ℝ) / ((f.D : ℝ) / f.rg) = (x : ℝ) / f.D := by
    intro x hx
    rw [Int.cast_div hx hgZ]
    push_cast
    field_simp
  unfold IFrame.Mem
  simp only [hD, IFrame.reduce_X, IFrame.reduce_H, e _ (hX _), e _ (hH _)]

theorem IFrame.reduce_hi1 : 0 < f.reduce.hi1 ↔ 0 < f.hi1 := by
  obtain ⟨hgpos, hgD, hX, hH⟩ := f.rg_spec hg
  obtain ⟨c, hc⟩ := dvd_add (hX 1) (hH 1)
  have hg0 : (0 : ℤ) < f.rg := by exact_mod_cast hgpos
  have e : f.reduce.hi1 = c := by
    unfold IFrame.hi1
    rw [IFrame.reduce_X, IFrame.reduce_H, ← Int.add_ediv_of_dvd_left (hX 1), hc,
      Int.mul_ediv_cancel_left _ hg0.ne']
  rw [e]
  unfold IFrame.hi1
  rw [hc]
  exact (mul_pos_iff_of_pos_left hg0).symm

end reduce

/-! ## Soundness: anchors, rational frames, leaves -/

theorem IFrame.getD_Xq (f : IFrame) (i : ℕ) :
    ((List.range f.X.length).map fun i => ((f.X.getD i 0 : ℚ) / f.D)).getD i 0 =
      (f.X.getD i 0 : ℚ) / f.D := by
  by_cases h7 : i < f.X.length
  · simp [List.getD_eq_getElem?_getD, h7]
  · rw [getD_of_length_le _ le_rfl i h7]; simp [List.getD_eq_getElem?_getD, h7]

theorem IFrame.getD_Hq (f : IFrame) (hg : f.Good) (i : ℕ) :
    ((List.range f.X.length).map fun i => ((f.H.getD i 0 : ℚ) / f.D)).getD i 0 =
      (f.H.getD i 0 : ℚ) / f.D := by
  by_cases h7 : i < f.X.length
  · simp [List.getD_eq_getElem?_getD, h7]
  · rw [getD_of_length_le _ hg.H i h7]; simp [List.getD_eq_getElem?_getD, h7]

theorem IFrame.toFrame_mem (f : IFrame) (hg : f.Good) (y : ℕ → ℝ) :
    f.toFrame.box.Mem y ↔ f.Mem y := by
  unfold Box.Mem IFrame.Mem
  simp only [Frame.box, Frame.toRow, Row.box, IFrame.toFrame, f.getD_Xq, f.getD_Hq hg]
  push_cast
  rfl

theorem IFrame.toFrame_hi1 (f : IFrame) (hg : f.Good) : 0 < f.toFrame.hi 1 ↔ 0 < f.hi1 := by
  have hD : (0 : ℚ) < f.D := by exact_mod_cast hg.D
  simp only [Frame.hi, Frame.toRow, Row.hi, Row.box, IFrame.toFrame, IFrame.hi1,
    f.getD_Xq, f.getD_Hq hg]
  rw [← add_div, div_pos_iff_of_pos_right hD]
  exact_mod_cast Iff.rfl

theorem IFrame.inBox_sound (f : IFrame) (r : Row) (hg : f.Good) (h : f.inBox r = true)
    (y : ℕ → ℝ) (hy : f.Mem y) : r.box.Mem y := by
  simp only [IFrame.inBox, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨hc, hr⟩, h⟩ := h
  intro i
  by_cases h7 : i < 7
  · have hi := h i h7
    have hiR : |((f.X.getD i 0 : ℚ) / f.D : ℝ) - (r.box.center i : ℝ)| +
        ((f.H.getD i 0 : ℚ) / f.D : ℝ) ≤ (r.box.radius i : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hi
      push_cast at this ⊢
      exact this
    push_cast at hiR
    have hyi := hy i
    calc |y i - r.box.center i|
        ≤ |y i - (f.X.getD i 0 : ℝ) / f.D| + |(f.X.getD i 0 : ℝ) / f.D - r.box.center i| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith
  · have hyi := hy i
    rw [getD_of_length_le _ hg.X i h7, getD_of_length_le _ (hg.H.trans hg.X) i h7] at hyi
    have e := box_beyond r hc hr i h7
    rw [e.1, e.2]
    simpa using hyi

theorem cheapI7_sound (fp : FactPoly) (f : IFrame) (hg : f.Good) (h : cheapI7 fp f = true)
    (y : ℕ → ℝ) (hy : f.Mem y) : 0 ≤ eval y (toIPoly fp.S).toPoly := by
  have hD : (0 : ℝ) < f.D := by exact_mod_cast hg.D
  have hHn : ∀ i, natI (f.H.map Int.toNat) i = f.H.getD i 0 := by
    intro i
    have := hg.Hnn i
    simp only [natI, List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
    cases hh : f.H[i]? with
    | none => simp
    | some x => simp only [hh, Option.getD_some, Option.map_some] at this ⊢; omega
  simp only [cheapI7, Bool.or_eq_true] at h
  rcases h with h | h
  · refine cheapI_sound _ _ _ _ _ (cheapP_imp _ _ _ _ _ _ h) y fun i => ?_
    rw [xI_map]
    have hm := (abs_sub_le_iff' _ _ _).mp (hy i)
    simp only [loI, ite_true, hHn]
    push_cast
    rw [neg_div]
    constructor <;> linarith [hm.1, hm.2]
  · refine cheapI_sound _ _ _ _ _ (cheapP_imp _ _ _ _ _ _ h) y fun i => ?_
    rw [xI_map]
    have hm := (abs_sub_le_iff' _ _ _).mp (hy i)
    have hY : ((List.range 7).map fun i => f.X.getD i 0 - f.H.getD i 0).getD i 0 =
        f.X.getD i 0 - f.H.getD i 0 := by
      rw [getD_range_map]
      split_ifs with h7
      · rfl
      · rw [getD_of_length_le _ hg.X i h7, getD_of_length_le _ (hg.H.trans hg.X) i h7]; rfl
    simp only [loI, Bool.false_eq_true, ite_false, natI_map_two, hHn, hY]
    push_cast
    rw [sub_div, zero_div, mul_div_assoc]
    constructor <;> linarith [hm.1, hm.2]

/-! ## Soundness: the tree -/

theorem mem_of_lookup {act : List (ℕ × Bool)} {k : ℕ} {b : Bool}
    (h : act.lookup k = some b) : (k, b) ∈ act := by
  induction act with
  | nil => simp at h
  | cons p act ih =>
      obtain ⟨k', b'⟩ := p
      simp only [List.lookup_cons] at h
      by_cases hk : k = k'
      · subst hk
        simp only [beq_self_eq_true, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · have : (k == k') = false := by simpa using hk
        rw [this] at h
        exact List.mem_cons_of_mem _ (ih h)

section
variable (H : Handoffs) (facts : Array Row) (fps : Array FactPoly)

/-- Each active fact is valid for the frame and contains it. -/
def ActiveInv (f : IFrame) (act : List (ℕ × Bool)) : Prop :=
  ∀ k b, (k, b) ∈ act → ∃ r, facts[k]? = some r ∧ r.aff = [] ∧ r.seg = f.seg ∧
    r.kind = f.kind ∧ (∀ y, f.Mem y → r.box.Mem y) ∧ (b = false → ¬ 0 < r.hi 1)

theorem fps_ok (hfps : FactPolysOk facts fps) {k : ℕ} {r : Row} {fp : FactPoly}
    (hr : facts[k]? = some r) (hp : fps[k]? = some fp) : fp.Ok r := by
  have hkl : k < fps.size := by
    by_contra h
    simp [Array.getElem?_eq_none (by omega : fps.size ≤ k)] at hp
  have hok := hfps ⟨k, hkl⟩
  simp only [FactPolyAt, hr, Fin.getElem_fin] at hok
  rw [Array.getElem?_eq_getElem hkl] at hp
  rwa [← Option.some.inj hp]

theorem check_sound (hH : ∀ h f, H.Valid h f → Covered f)
    (hfacts : ∀ fact ∈ facts, fact.KeyFacts) (hfps : FactPolysOk facts fps) :
    ∀ (t : KTree) (f : IFrame) (act : List (ℕ × Bool)), f.Good → ActiveInv facts f act →
      KTree.check H facts fps f act t = true → (∀ g ∈ t.holes, ICovered g) → ICovered f
  | .split v M s lo hi, f, act, hg, hinv, h, hholes => by
      simp only [KTree.check, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hv, hs⟩, hlo, hhi⟩, hL⟩, hU⟩ := h
      have cg := fun upper => f.child_good v M s hs hlo hhi hg upper
      have childInv : ∀ upper, ActiveInv facts (f.child v M s upper).reduce act := by
        intro upper k b hkb
        obtain ⟨r, hr, haff, hseg, hkind, hbox, hflag⟩ := hinv k b hkb
        refine ⟨r, hr, haff, by rw [IFrame.reduce_seg]; exact hseg,
          by rw [IFrame.reduce_kind]; exact hkind, fun y hy => hbox y ?_, hflag⟩
        exact f.mem_of_child v M s hv hs hlo hhi hg upper ((IFrame.reduce_mem _ (cg upper) y).mp hy)
      have covL := check_sound hH hfacts hfps lo _ act (IFrame.reduce_good _ (cg false))
        (childInv false) hL (fun g hg' => hholes g (by simp [KTree.holes, hg']))
      have covU := check_sound hH hfacts hfps hi _ act (IFrame.reduce_good _ (cg true))
        (childInv true) hU (fun g hg' => hholes g (by simp [KTree.holes, hg']))
      intro p offset y hc hmem hε hρ hlam hflip hscale
      rcases f.mem_child v M s hv hs hlo hhi hg hmem with hm | hm
      · refine covL p offset y (by rw [IFrame.reduce_seg, IFrame.reduce_kind]; exact hc)
          ((IFrame.reduce_mem _ (cg false) y).mpr hm) hε
          (by rw [IFrame.reduce_kind]; exact hρ)
          (fun h => hlam (f.child_hi1 v M s hv hs hlo hhi false
            ((IFrame.reduce_hi1 _ (cg false)).mp h))) hflip hscale
      · refine covU p offset y (by rw [IFrame.reduce_seg, IFrame.reduce_kind]; exact hc)
          ((IFrame.reduce_mem _ (cg true) y).mpr hm) hε
          (by rw [IFrame.reduce_kind]; exact hρ)
          (fun h => hlam (f.child_hi1 v M s hv hs hlo hhi true
            ((IFrame.reduce_hi1 _ (cg true)).mp h))) hflip hscale
  | .anchor ks t, f, act, hg, hinv, h, hholes => by
      simp only [KTree.check, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨hks, ht⟩ := h
      refine check_sound hH hfacts hfps t f _ hg ?_ ht (fun g hg' => hholes g hg')
      intro k b hkb
      rcases List.mem_append.mp hkb with hkb | hkb
      · obtain ⟨k', hk', he⟩ := List.mem_map.mp hkb
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hok := hks k' hk'
        unfold anchorOk at hok
        unfold anchorFlag
        cases hr : facts[k']? with
        | none => simp [hr] at hok
        | some r =>
            simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨⟨haff, hseg, hkind⟩, hbox⟩ := hok
            refine ⟨r, rfl, haff, hseg, hkind, f.inBox_sound r hg hbox, ?_⟩
            intro hb
            simpa using hb
      · exact hinv k b hkb
  | .leafP k, f, act, hg, hinv, h, _ => by
      simp only [KTree.check] at h
      unfold leafPOk at h
      cases hl : act.lookup k with
      | none => simp [hl] at h
      | some flag =>
          cases hp : fps[k]? with
          | none => simp [hl, hp] at h
          | some fp =>
              simp only [hl, hp, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
              obtain ⟨⟨hflag1, hm⟩, hcheap⟩ := h
              obtain ⟨r, hr, haff, hseg, hkind, hbox, hflag⟩ := hinv k flag (mem_of_lookup hl)
              have hfp := fps_ok facts fps hfps hr hp
              have hrk := hfacts r (Array.mem_of_getElem? hr)
              have hD : (0 : ℝ) < f.D := by exact_mod_cast hg.D
              intro p offset y hc hmem hε hρ hlam hflip hscale
              refine r.not_rupert_fact hrk haff p offset y (hseg ▸ hkind ▸ hc) (hbox y hmem) hε
                (fun ht => hρ (by simpa [Row.isTube, hkind] using ht)) ?_ hscale ?_
              · intro hpos
                cases flag
                · exact absurd hpos (hflag rfl)
                · rcases hflag1 with h1 | h1
                  · simp at h1
                  · exact hlam h1
              · rw [hfp.eval_D]
                have hK : (0 : ℝ) < fp.K := by exact_mod_cast hfp.1
                have hmono : 0 ≤ monoEval y fp.m := by
                  apply monoEval_nonneg_of
                  intro i hi
                  have hlen : i < fp.m.length := by
                    by_contra hc'
                    simp [List.getD_eq_getElem?_getD,
                      List.getElem?_eq_none (by omega : fp.m.length ≤ i)] at hi
                  rcases hm i hlen with h0 | h0
                  · omega
                  · have hyi := (abs_sub_le_iff' _ _ _).mp (hmem i)
                    have : (0 : ℝ) ≤ (f.X.getD i 0 : ℝ) / f.D - (f.H.getD i 0 : ℝ) / f.D := by
                      rw [← sub_div]
                      apply div_nonneg _ hD.le
                      have : (f.H.getD i 0 : ℝ) ≤ f.X.getD i 0 := by exact_mod_cast h0
                      linarith
                    linarith [hyi.1]
                have hS := cheapI7_sound fp f hg hcheap y hmem
                exact mul_nonneg hε.le (div_nonneg (mul_nonneg hmono hS) hK.le)
  | .flipP k, f, act, hg, _, h, _ => by
      simp only [KTree.check] at h
      cases hfp : flipFP f.seg f.kind k with
      | none => simp [hfp] at h
      | some fp =>
          simp only [hfp] at h
          intro p offset y hc hmem hε hρ hlam hflip hscale
          have hS := cheapI7_sound (scaleSub fp (f.D ^ 10)) f hg h y hmem
          rw [eval_scaleSub] at hS
          have hok := flipFP_ok hfp
          have hK : (0 : ℝ) < fp.K := by exact_mod_cast hok.1
          have hcpos : (0 : ℝ) < ((f.D ^ 10 : ℕ) : ℝ) := by
            have : 0 < f.D := hg.D
            positivity
          have hSpos : 0 < eval y (toIPoly fp.S).toPoly := by
            by_contra hn
            have := mul_nonpos_of_nonneg_of_nonpos hcpos.le (not_lt.mp hn)
            linarith
          have hpos : 0 < eval y (flipPoly f.seg f.kind k) := by
            rw [hok.eval_flip]
            exact div_pos (mul_pos (monoEval_pos_of_len y hε fp.m hok.2.1) hSpos) hK
          exact absurd hflip (not_flipReduced_of_flipPoly_pos hc k hscale hpos)
  | .leaf l, f, act, hg, _, h, _ => by
      simp only [KTree.check, decide_eq_true_eq] at h
      have cov := leaf_covered H hH facts hfacts fps hfps f.toFrame l h
      intro p offset y hc hmem hε hρ hlam hflip hscale
      exact cov p offset y (by simpa [IFrame.toFrame, affY_nil] using hc)
        ((f.toFrame_mem hg y).mpr hmem) hε hρ (fun h => hlam ((f.toFrame_hi1 hg).mp h))
        hflip hscale
  | .hole g, f, act, hg, _, h, hholes => by
      simp only [KTree.check, decide_eq_true_eq] at h
      subst h
      exact hholes g (by simp [KTree.holes])

end

/-! ## Glue for generated proofs -/

theorem holes_of_eq {t : KTree} {l : List IFrame} (h : t.holes = l)
    (hl : ∀ g ∈ l, ICovered g) : ∀ g ∈ t.holes, ICovered g := h ▸ hl

theorem activeInv_nil (facts : Array Row) (f : IFrame) : ActiveInv facts f [] :=
  fun _ _ h => absurd h List.not_mem_nil

/-- A table root given as an integer frame. -/
theorem covered_of_toFrame (g : IFrame) (hg : g.WF = true) (f : Frame) (h : g.toFrame = f)
    (hc : ICovered g) : Covered f := by
  subst h
  have hgood := g.good_of_wf hg
  intro p offset y hcoords hmem hε hρ hlam hflip hscale
  exact hc p offset y (by simpa [IFrame.toFrame, affY_nil] using hcoords)
    ((g.toFrame_mem hgood y).mp hmem) hε hρ (fun h => hlam ((g.toFrame_hi1 hgood).mpr h))
    hflip hscale

end Noperts.Stellated.CornerKernel
