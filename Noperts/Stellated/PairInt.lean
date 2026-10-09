module

public import Noperts.Stellated.PackedSlots

@[expose] public section

/-!
# Integers as pairs of naturals, for the kernel

The kernel evaluates `Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.ble`, … on literals by GMP in
one step, but an `Int` operation unfolds through several matches on the constructors.  A
pair `(p, n)` stands for `p - n`; its arithmetic uses only `Nat` primitives.  Pairs are not
normalized.
-/

namespace Noperts.Stellated.ZP

abbrev Z := ℕ × ℕ

/-- The integer `p - n`. -/
def toZ (a : Z) : ℤ := (a.1 : ℤ) - a.2

def ofI (z : ℤ) : Z := match z with | .ofNat n => (n, 0) | .negSucc n => (0, Nat.succ n)
def add (a b : Z) : Z := (Nat.add a.1 b.1, Nat.add a.2 b.2)
def sub (a b : Z) : Z := (Nat.add a.1 b.2, Nat.add a.2 b.1)
def mul (a b : Z) : Z :=
  (Nat.add (Nat.mul a.1 b.1) (Nat.mul a.2 b.2), Nat.add (Nat.mul a.1 b.2) (Nat.mul a.2 b.1))
def nmul (k : ℕ) (a : Z) : Z := (Nat.mul k a.1, Nat.mul k a.2)
def neg (a : Z) : Z := (a.2, a.1)
def nonneg (a : Z) : Bool := Nat.ble a.2 a.1
def pos (a : Z) : Bool := Nat.blt a.2 a.1
def isNeg (a : Z) : Bool := Nat.blt a.1 a.2
def eqZ (a b : Z) : Bool := Nat.beq (Nat.add a.1 b.2) (Nat.add a.2 b.1)
/-- A bound on `|toZ a|` (and on both parts' contributions). -/
def sz (a : Z) : ℕ := Nat.add a.1 a.2

@[simp] theorem toZ_mk0 (n : ℕ) : toZ (n, 0) = n := by simp [toZ]
@[simp] theorem toZ_ofI (z : ℤ) : toZ (ofI z) = z := by
  cases z <;> simp [toZ, ofI] <;> omega
@[simp] theorem toZ_add (a b : Z) : toZ (add a b) = toZ a + toZ b := by
  simp only [toZ, add, Nat.add_eq]; push_cast; ring
@[simp] theorem toZ_sub (a b : Z) : toZ (sub a b) = toZ a - toZ b := by
  simp only [toZ, sub, Nat.add_eq]; push_cast; ring
@[simp] theorem toZ_mul (a b : Z) : toZ (mul a b) = toZ a * toZ b := by
  simp only [toZ, mul, Nat.add_eq, Nat.mul_eq]; push_cast; ring
@[simp] theorem toZ_nmul (k : ℕ) (a : Z) : toZ (nmul k a) = k * toZ a := by
  simp only [toZ, nmul, Nat.mul_eq]; push_cast; ring
@[simp] theorem toZ_neg (a : Z) : toZ (neg a) = -toZ a := by simp [toZ, neg]
theorem nonneg_iff (a : Z) : nonneg a = true ↔ 0 ≤ toZ a := by
  simp [nonneg, toZ]
theorem pos_iff (a : Z) : pos a = true ↔ 0 < toZ a := by
  simp [pos, toZ]
theorem isNeg_iff (a : Z) : isNeg a = true ↔ toZ a < 0 := by
  simp [isNeg, toZ]
theorem eqZ_iff (a b : Z) : eqZ a b = true ↔ toZ a = toZ b := by
  simp only [eqZ, toZ, Nat.add_eq, Nat.beq_eq]; omega
theorem natAbs_le_sz (a : Z) : (toZ a).natAbs ≤ sz a := by
  have h := Int.natAbs_sub_le (a.1 : ℤ) a.2
  simp only [Int.natAbs_natCast] at h
  simpa [toZ, sz] using h

/-! ## Packed vectors scaled by pairs -/

open PackedSlots

/-- `U` scaled by the pair `k`. -/
def psm (k : Z) (U : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.add (Nat.mul k.1 U.1) (Nat.mul k.2 U.2), Nat.add (Nat.mul k.1 U.2) (Nat.mul k.2 U.1))

def padd (a b : ℕ × ℕ) : ℕ × ℕ := (Nat.add a.1 b.1, Nat.add a.2 b.2)

theorem _root_.Noperts.Stellated.PackedSlots.PRep.psm {w n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep w n U d M) (k : Z) :
    PRep w n (psm k U) (fun t => toZ k * d t) (sz k * M) := by
  obtain ⟨a, b, rfl, hd, hM⟩ := hU
  refine ⟨fun t => k.1 * a t + k.2 * b t, fun t => k.1 * b t + k.2 * a t, ?_, fun t => ?_,
    fun t => ?_⟩
  · simp only [ZP.psm, packW_add, packW_smul, Nat.add_eq, Nat.mul_eq]
  · simp only [toZ]; push_cast; rw [← hd t]; ring
  · obtain ⟨h1, h2⟩ := hM t
    have e1 := Nat.mul_le_mul_left k.1 h1
    have e2 := Nat.mul_le_mul_left k.2 h2
    have e3 := Nat.mul_le_mul_left k.1 h2
    have e4 := Nat.mul_le_mul_left k.2 h1
    have e : sz k * M = k.1 * M + k.2 * M := by simp only [sz, Nat.add_eq]; ring
    rw [e]
    show k.1 * a t + k.2 * b t ≤ _ ∧ k.1 * b t + k.2 * a t ≤ _
    exact ⟨by omega, by omega⟩

theorem _root_.Noperts.Stellated.PackedSlots.PRep.padd {w n : ℕ} {U V : ℕ × ℕ} {d e : ℕ → ℤ} {M N : ℕ} (hU : PRep w n U d M)
    (hV : PRep w n V e N) : PRep w n (padd U V) (fun t => d t + e t) (M + N) :=
  hU.add hV

/-- The product of packed vectors (a convolution of slots). -/
def pmul (A B : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.add (Nat.mul A.1 B.1) (Nat.mul A.2 B.2), Nat.add (Nat.mul A.1 B.2) (Nat.mul A.2 B.1))

/-- Three pairs packed at slot width `w`, given `P₁ = 2^w`, `P₂ = 2^(2w)`. -/
def pk3 (P₁ P₂ : ℕ) (a b c : Z) : ℕ × ℕ :=
  (Nat.add (Nat.add a.1 (Nat.mul P₁ b.1)) (Nat.mul P₂ c.1),
    Nat.add (Nat.add a.2 (Nat.mul P₁ b.2)) (Nat.mul P₂ c.2))

/-- The three-entry function `0 ↦ a, 1 ↦ b, 2 ↦ c` (zero beyond). -/
def sel3Z (a b c : ℤ) (j : ℕ) : ℤ := if j = 0 then a else if j = 1 then b else if j = 2 then c else 0

theorem pk3_rep (w : ℕ) (a b c : Z) (M : ℕ) (ha : sz a ≤ M) (hb : sz b ≤ M) (hc : sz c ≤ M) :
    PRep w 3 (pk3 (2 ^ w) (2 ^ (2 * w)) a b c) (sel3Z (toZ a) (toZ b) (toZ c)) M := by
  refine ⟨fun j => if j = 0 then a.1 else if j = 1 then b.1 else if j = 2 then c.1 else 0,
    fun j => if j = 0 then a.2 else if j = 1 then b.2 else if j = 2 then c.2 else 0, ?_,
    fun t => ?_, fun t => ?_⟩
  · simp only [pk3, packW, Nat.add_eq, Nat.mul_eq]
    simp only [show w * 2 = 2 * w by ring, mul_zero, pow_zero, mul_one, one_mul]
    norm_num
  · simp only [sel3Z, toZ]; split_ifs <;> simp
  · simp only [sz, Nat.add_eq] at ha hb hc
    dsimp only
    split_ifs <;> omega

end Noperts.Stellated.ZP
