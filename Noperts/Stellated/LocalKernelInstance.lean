module

public import Noperts.Stellated.LocalKernelSound
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

instance (priority := high) instViewValidKernel (box : Box) : Decidable box.ViewValid :=
  if h : viewValidN box = true then isTrue (viewValidN_sound box h)
  else decidable_of_iff _ box.viewValid_iff_fastB.symm

instance (priority := high) instRowValidAtKernel (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidAt symmetryIndex r get size) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

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
