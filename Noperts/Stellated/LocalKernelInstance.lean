module

public import Noperts.Stellated.LocalKernelSound
public import Noperts.Stellated.LocalKernelFast
public import Noperts.Stellated.AtlasProjectiveLocalViewTree

@[expose] public section

/-!
# Kernel-path decision instances for local view tables

Imported only by kernel-checked (`decide +kernel`) files: `Box.ViewValid` is
decided by the integer checker `LocalKernel.viewValidN` (sound by
`viewValidN_sound`), falling back to the rational specification otherwise, and
the row/range instances are re-derived so they pick it up.  The native path
keeps the instances of `AtlasProjectiveLocalCertificate`.
-/

namespace Noperts.Stellated.LocalKernel

open AtlasProjectiveLocalCertificate AtlasProjectiveLocalViewTree

/-- Equality of view triangles entry by entry (the generic decision procedure for
functions on `Fin 3 × Fin 3` enumerates `Finset.univ` in the kernel). -/
instance (priority := high) instTriangleDecEqKernel (s t : Fin 3 → Fin 3 → ℚ) : Decidable (s = t) :=
  decidable_of_iff (s 0 0 = t 0 0 ∧ s 0 1 = t 0 1 ∧ s 0 2 = t 0 2 ∧ s 1 0 = t 1 0 ∧
      s 1 1 = t 1 1 ∧ s 1 2 = t 1 2 ∧ s 2 0 = t 2 0 ∧ s 2 1 = t 2 1 ∧ s 2 2 = t 2 2) (by
    constructor
    · rintro ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩
      funext i j
      fin_cases i <;> fin_cases j <;> assumption
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)


/-- Entry-wise equality of view triangles. -/
def triEq9 (s t : AtlasProjectiveView.Triangle ℚ) : Bool :=
  decide (s 0 0 = t 0 0) && decide (s 0 1 = t 0 1) && decide (s 0 2 = t 0 2) &&
  decide (s 1 0 = t 1 0) && decide (s 1 1 = t 1 1) && decide (s 1 2 = t 1 2) &&
  decide (s 2 0 = t 2 0) && decide (s 2 1 = t 2 1) && decide (s 2 2 = t 2 2)

theorem triEq9_iff (s t : AtlasProjectiveView.Triangle ℚ) : triEq9 s t = true ↔ s = t := by
  simp only [triEq9, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h10⟩, h11⟩, h12⟩, h20⟩, h21⟩, h22⟩
    funext i j
    fin_cases i <;> fin_cases j <;> assumption
  · rintro rfl
    exact ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- The triangle with rows `a, b, c`. -/
def tri3 (a b c : AtlasProjectiveView.Vector ℚ) : AtlasProjectiveView.Triangle ℚ :=
  fun i => match i with | 0 => a | 1 => b | 2 => c

/-- The conditions of a split row, with the children's triangles from shared midpoints. -/
def splitRowOk (get : ℕ → Row) (size id : ℕ) (children : Fin 4 → ℕ) (root : Fin 8)
    (t : AtlasProjectiveView.Triangle ℚ) : Bool :=
  let m01 := Noperts.ProjectiveView.midpoint (t 0) (t 1)
  let m02 := Noperts.ProjectiveView.midpoint (t 0) (t 2)
  let m12 := Noperts.ProjectiveView.midpoint (t 1) (t 2)
  let m20 := Noperts.ProjectiveView.midpoint (t 2) (t 0)
  let one := fun (c : ℕ) (e : AtlasProjectiveView.Triangle ℚ) =>
    Nat.blt id c && Nat.blt c size && decide ((get c).root = root) && triEq9 (get c).triangle e
  one (children 0) (tri3 (t 0) m01 m02) && one (children 1) (tri3 m01 (t 1) m12) &&
    one (children 2) (tri3 m02 m12 (t 2)) && one (children 3) (tri3 m01 m12 m20)

theorem split_tri3 (t : AtlasProjectiveView.Triangle ℚ) (k : Fin 4) :
    Noperts.ProjectiveView.split t k = (match k with
      | 0 => tri3 (t 0) (Noperts.ProjectiveView.midpoint (t 0) (t 1))
          (Noperts.ProjectiveView.midpoint (t 0) (t 2))
      | 1 => tri3 (Noperts.ProjectiveView.midpoint (t 0) (t 1)) (t 1)
          (Noperts.ProjectiveView.midpoint (t 1) (t 2))
      | 2 => tri3 (Noperts.ProjectiveView.midpoint (t 0) (t 2))
          (Noperts.ProjectiveView.midpoint (t 1) (t 2)) (t 2)
      | 3 => tri3 (Noperts.ProjectiveView.midpoint (t 0) (t 1))
          (Noperts.ProjectiveView.midpoint (t 1) (t 2)) (Noperts.ProjectiveView.midpoint (t 2) (t 0))) := by
  funext i
  fin_cases k <;> fin_cases i <;> rfl

theorem splitRowOk_iff (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row) (size id : ℕ)
    (children : Fin 4 → ℕ) (root : Fin 8) (t : AtlasProjectiveView.Triangle ℚ) :
    splitRowOk get size id children root t = true ↔
      (Row.split id children root t).ValidAt symmetryIndex r get size := by
  simp only [splitRowOk, Row.ValidAt, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, triEq9_iff]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ k
    fin_cases k
    · exact ⟨h0.1.1.1, h0.1.1.2, h0.1.2, h0.2.trans (split_tri3 t 0).symm⟩
    · exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2.trans (split_tri3 t 1).symm⟩
    · exact ⟨h2.1.1.1, h2.1.1.2, h2.1.2, h2.2.trans (split_tri3 t 2).symm⟩
    · exact ⟨h3.1.1.1, h3.1.1.2, h3.1.2, h3.2.trans (split_tri3 t 3).symm⟩
  · intro h
    have e := fun k => (h k).2.2.2.trans (split_tri3 t k)
    exact ⟨⟨⟨⟨⟨⟨(h 0).1, (h 0).2.1⟩, (h 0).2.2.1⟩, e 0⟩, ⟨⟨⟨(h 1).1, (h 1).2.1⟩, (h 1).2.2.1⟩, e 1⟩⟩,
      ⟨⟨⟨(h 2).1, (h 2).2.1⟩, (h 2).2.2.1⟩, e 2⟩⟩, ⟨⟨⟨(h 3).1, (h 3).2.1⟩, (h 3).2.2.1⟩, e 3⟩⟩

instance (priority := high) instViewValidKernel (box : Box) : Decidable box.ViewValid :=
  if h : viewValidZ box = true then isTrue (viewValidZ_sound box h)
  else decidable_of_iff _ box.viewValid_iff_fastB.symm

instance (priority := high) instRowValidAtKernel (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidAt symmetryIndex r get size) := by
  cases row with
  | split id children root t =>
      exact decidable_of_iff _ (splitRowOk_iff symmetryIndex r get size id children root t)
  | certificate id box => simp only [Row.ValidAt]; infer_instance
  | cut id children root t w => simp only [Row.ValidAt]; infer_instance

instance (priority := high) instRowsValidRangeAtKernel (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size start count : ℕ) :
    Decidable (RowsValidRangeAt symmetryIndex r get size start count) := by
  unfold RowsValidRangeAt; infer_instance

/-- An 8-ary tree of depth `d` with leaves in `α` (`Fin 8 → … → α`). -/
def Tree8 (α : Type) : ℕ → Type
  | 0 => α
  | d + 1 => Fin 8 → Tree8 α d

/-- Leaf `i` of a depth-`d` tree: digit `d-1` of `i` (base 8) selects the top
branch, …, digit `0` the leaf.  `O(d)` `Fin.cons` walks of at most 8 cells. -/
def Tree8.get {α : Type} : (d : ℕ) → Tree8 α d → ℕ → α
  | 0, t, _ => t
  | d + 1, t, i => Tree8.get d (t ⟨i / 8 ^ d % 8, Nat.mod_lt _ (by decide)⟩) i

end Noperts.Stellated.LocalKernel
