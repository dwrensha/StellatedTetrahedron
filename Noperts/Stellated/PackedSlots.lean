module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Packed slots in a natural number

`packW w z n = Σ_{t < n} z t · 2^(w t)` packs `n` values into `w`-bit slots.
When every value fits (`z t < 2^w`), the bits of slot `t` are those of `z t`,
so a single `&&&` against the mask of slot top bits tests `2^(w-1) ≤ z t` for
all `t` at once (`ge_of_land_mask`).
-/

namespace Noperts.Stellated.PackedSlots

def packW (w : ℕ) (z : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packW w z n + 2 ^ (w * n) * z n

theorem packW_lt (w : ℕ) (z : ℕ → ℕ) (hz : ∀ t, z t < 2 ^ w) : ∀ n, packW w z n < 2 ^ (w * n)
  | 0 => by simp [packW]
  | n + 1 => by
      have ih := packW_lt w z hz n
      have h1 := hz n
      simp only [packW]
      calc packW w z n + 2 ^ (w * n) * z n < 2 ^ (w * n) + 2 ^ (w * n) * z n := by omega
        _ = 2 ^ (w * n) * (z n + 1) := by ring
        _ ≤ 2 ^ (w * n) * 2 ^ w := Nat.mul_le_mul_left _ h1
        _ = 2 ^ (w * (n + 1)) := by rw [← pow_add]; ring_nf

/-- The bits of slot `t` are those of `z t`. -/
theorem testBit_packW (w : ℕ) (z : ℕ → ℕ) (hz : ∀ t, z t < 2 ^ w) :
    ∀ n t b, t < n → b < w → (packW w z n).testBit (w * t + b) = (z t).testBit b
  | 0, _, _, h, _ => absurd h (by omega)
  | n + 1, t, b, ht, hb => by
      simp only [packW]
      rw [add_comm, Nat.testBit_two_pow_mul_add _ (packW_lt w z hz n)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · have : w * t + b < w * n := by
          calc w * t + b < w * t + w := by omega
            _ = w * (t + 1) := by ring
            _ ≤ w * n := Nat.mul_le_mul_left _ ht
        rw [ite_eq_left this]
        exact testBit_packW w z hz n t b ht hb
      · rw [ite_eq_right (by omega)]
        congr 1
        omega

theorem packW_add (w : ℕ) (a b : ℕ → ℕ) :
    ∀ n, packW w (fun t => a t + b t) n = packW w a n + packW w b n
  | 0 => rfl
  | n + 1 => by simp only [packW, packW_add w a b n]; ring

theorem packW_smul (w k : ℕ) (a : ℕ → ℕ) :
    ∀ n, packW w (fun t => k * a t) n = k * packW w a n
  | 0 => by simp [packW]
  | n + 1 => by simp only [packW, packW_smul w k a n]; ring

theorem packW_sub (w : ℕ) (a b : ℕ → ℕ) (h : ∀ t, b t ≤ a t) :
    ∀ n, packW w a n - packW w b n = packW w (fun t => a t - b t) n
  | 0 => rfl
  | n + 1 => by
      have ih := packW_sub w a b h n
      have hle : ∀ m, packW w b m ≤ packW w a m := by
        intro m
        induction m with
        | zero => simp [packW]
        | succ m ihm => simp only [packW]; exact Nat.add_le_add ihm (Nat.mul_le_mul_left _ (h m))
      simp only [packW]
      have := hle n
      have := h n
      rw [← ih, Nat.mul_sub]
      have h3 : 2 ^ (w * n) * b n ≤ 2 ^ (w * n) * a n := Nat.mul_le_mul_left _ (h n)
      omega

/-- The top-bit test. -/
theorem ge_of_land_mask (w n : ℕ) (hw : 0 < w) (z : ℕ → ℕ) (hz : ∀ t, z t < 2 ^ w)
    (h : Nat.land (packW w z n) (packW w (fun _ => 2 ^ (w - 1)) n) =
      packW w (fun _ => 2 ^ (w - 1)) n) :
    ∀ t < n, 2 ^ (w - 1) ≤ z t := by
  intro t ht
  have hK : ∀ s : ℕ, (fun _ : ℕ => 2 ^ (w - 1)) s < 2 ^ w := fun _ =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hb : w - 1 < w := by omega
  have hM : (packW w (fun _ => 2 ^ (w - 1)) n).testBit (w * t + (w - 1)) = true := by
    rw [testBit_packW w _ hK n t (w - 1) ht hb, Nat.testBit_two_pow_self]
  have hland := congrArg (fun m => m.testBit (w * t + (w - 1))) h
  simp only at hland
  have hZ : (packW w z n).testBit (w * t + (w - 1)) = true := by
    have : (Nat.land (packW w z n) (packW w (fun _ => 2 ^ (w - 1)) n)).testBit
        (w * t + (w - 1)) = true := by rw [hland]; exact hM
    rw [show Nat.land (packW w z n) (packW w (fun _ => 2 ^ (w - 1)) n) =
      packW w z n &&& packW w (fun _ => 2 ^ (w - 1)) n from rfl, Nat.testBit_land] at this
    simp only [Bool.and_eq_true] at this
    exact this.1
  rw [testBit_packW w z hz n t (w - 1) ht hb] at hZ
  exact Nat.ge_two_pow_of_testBit hZ

/-! ## Signed packed vectors -/

/-- `U` packs the signed slot values `d` (positive parts in `U.1`, negative in
`U.2`), every part at most `M`. -/
def PRep (w n : ℕ) (U : ℕ × ℕ) (d : ℕ → ℤ) (M : ℕ) : Prop :=
  ∃ a b : ℕ → ℕ, U = (packW w a n, packW w b n) ∧ (∀ t, (a t : ℤ) - b t = d t) ∧
    ∀ t, a t ≤ M ∧ b t ≤ M

theorem PRep.add {w n : ℕ} {U V : ℕ × ℕ} {d e : ℕ → ℤ} {M N : ℕ}
    (hU : PRep w n U d M) (hV : PRep w n V e N) :
    PRep w n (U.1 + V.1, U.2 + V.2) (fun t => d t + e t) (M + N) := by
  obtain ⟨a, b, rfl, hd, hM⟩ := hU
  obtain ⟨a', b', rfl, he, hN⟩ := hV
  refine ⟨fun t => a t + a' t, fun t => b t + b' t, ?_, fun t => ?_, fun t => ?_⟩
  · simp [packW_add]
  · push_cast; rw [← hd t, ← he t]; ring
  · exact ⟨Nat.add_le_add (hM t).1 (hN t).1, Nat.add_le_add (hM t).2 (hN t).2⟩

theorem PRep.smul {w n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep w n U d M) (k : ℤ) :
    PRep w n (if 0 ≤ k then (k.toNat * U.1, k.toNat * U.2) else (k.natAbs * U.2, k.natAbs * U.1))
      (fun t => k * d t) (k.natAbs * M) := by
  obtain ⟨a, b, rfl, hd, hM⟩ := hU
  split_ifs with hk
  · refine ⟨fun t => k.toNat * a t, fun t => k.toNat * b t, ?_, fun t => ?_, fun t => ?_⟩
    · simp [packW_smul]
    · push_cast; rw [Int.toNat_of_nonneg hk, ← hd t]; ring
    · have : k.toNat = k.natAbs := by omega
      rw [this]
      exact ⟨Nat.mul_le_mul_left _ (hM t).1, Nat.mul_le_mul_left _ (hM t).2⟩
  · refine ⟨fun t => k.natAbs * b t, fun t => k.natAbs * a t, ?_, fun t => ?_, fun t => ?_⟩
    · simp [packW_smul]
    · push_cast
      have : |k| = -k := abs_of_neg (by omega)
      rw [this, ← hd t]; ring
    · exact ⟨Nat.mul_le_mul_left _ (hM t).2, Nat.mul_le_mul_left _ (hM t).1⟩

theorem PRep.mono {w n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M N : ℕ} (hU : PRep w n U d M)
    (h : M ≤ N) : PRep w n U d N := by
  obtain ⟨a, b, hU, hd, hM⟩ := hU
  exact ⟨a, b, hU, hd, fun t => ⟨(hM t).1.trans h, (hM t).2.trans h⟩⟩

theorem packW_const_lt (w : ℕ) (c : ℕ) (hc : c < 2 ^ w) : ∀ t, (fun _ : ℕ => c) t < 2 ^ w :=
  fun _ => hc

/-- The packed lower-bound test: every slot value is at least `th`. -/
theorem PRep.ge_of_test {w n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep w n U d M)
    (hw : 1 < w) (th : ℤ) (hbound : 4 * (M + th.natAbs) < 2 ^ (w - 1))
    (h : Nat.land (U.1 + 2 ^ (w - 1) * packW w (fun _ => 1) n +
        (if th < 0 then th.natAbs * packW w (fun _ => 1) n else 0) -
        (U.2 + (if 0 ≤ th then th.natAbs * packW w (fun _ => 1) n else 0)))
        (2 ^ (w - 1) * packW w (fun _ => 1) n) = 2 ^ (w - 1) * packW w (fun _ => 1) n) :
    ∀ t < n, th ≤ d t := by
  obtain ⟨a, b, rfl, hd, hM⟩ := hU
  set K := 2 ^ (w - 1) with hK
  have hKw : 2 ^ w = 2 * K := by
    rw [hK, ← pow_succ']; congr 1; omega
  set tp := (if th < 0 then th.natAbs else 0) with htp
  set tn := (if 0 ≤ th then th.natAbs else 0) with htn
  have hzero : packW w (fun _ => 0) n = 0 := by
    have := packW_smul w 0 (fun _ => 1) n
    simpa using this
  have hconst : ∀ c : ℕ, c * packW w (fun _ => 1) n = packW w (fun _ => c) n := by
    intro c; rw [← packW_smul]; simp only [mul_one]
  have htp' : (if th < 0 then th.natAbs * packW w (fun _ => 1) n else 0) =
      packW w (fun _ => tp) n := by
    rw [htp]
    by_cases h0 : th < 0
    · simp only [h0, ↓reduceIte, hconst]
    · simp only [h0, ↓reduceIte, hzero]
  have htn' : (if 0 ≤ th then th.natAbs * packW w (fun _ => 1) n else 0) =
      packW w (fun _ => tn) n := by
    rw [htn]
    by_cases h0 : 0 ≤ th
    · simp only [h0, ↓reduceIte, hconst]
    · simp only [h0, ↓reduceIte, hzero]
  have hKo : K * packW w (fun _ => 1) n = packW w (fun _ => K) n := hconst K
  simp only at h
  rw [htp', htn', hKo, ← packW_add, ← packW_add, ← packW_add] at h
  have hle : ∀ t, b t + tn ≤ a t + K + tp := by
    intro t
    have := (hM t).2
    have : tn ≤ th.natAbs := by rw [htn]; split_ifs <;> omega
    omega
  rw [packW_sub w _ _ hle] at h
  have hz : ∀ t, a t + K + tp - (b t + tn) < 2 ^ w := by
    intro t
    have := (hM t).1
    have : tp ≤ th.natAbs := by rw [htp]; split_ifs <;> omega
    omega
  have hge := ge_of_land_mask w n (by omega) _ hz h
  intro t ht
  have := hge t ht
  have hdt := hd t
  have : (K : ℤ) ≤ a t + K + tp - (b t + tn) := by
    have h1 : b t + tn ≤ a t + K + tp := hle t
    have := this
    exact_mod_cast this
  rw [htp, htn] at this
  split_ifs at this with h1 h2 <;> omega

/-! ## Partial masks -/

/-- The top-bit test on the slots selected by `p`. -/
theorem ge_of_land_maskP (w n : ℕ) (hw : 0 < w) (z : ℕ → ℕ) (hz : ∀ t, z t < 2 ^ w)
    (p : ℕ → Bool)
    (h : Nat.land (packW w z n) (packW w (fun t => if p t then 2 ^ (w - 1) else 0) n) =
      packW w (fun t => if p t then 2 ^ (w - 1) else 0) n) :
    ∀ t < n, p t = true → 2 ^ (w - 1) ≤ z t := by
  intro t ht hp
  have hK : ∀ s : ℕ, (fun s : ℕ => if p s then 2 ^ (w - 1) else 0) s < 2 ^ w := by
    intro s
    simp only
    split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · positivity
  have hb : w - 1 < w := by omega
  have hM : (packW w (fun s => if p s then 2 ^ (w - 1) else 0) n).testBit (w * t + (w - 1)) =
      true := by
    rw [testBit_packW w _ hK n t (w - 1) ht hb]
    simp [hp, Nat.testBit_two_pow_self]
  have hland := congrArg (fun m => m.testBit (w * t + (w - 1))) h
  have hZ : (packW w z n).testBit (w * t + (w - 1)) = true := by
    have : (Nat.land (packW w z n) (packW w (fun s => if p s then 2 ^ (w - 1) else 0) n)).testBit
        (w * t + (w - 1)) = true := by rw [hland]; exact hM
    rw [show Nat.land (packW w z n) (packW w (fun s => if p s then 2 ^ (w - 1) else 0) n) =
      packW w z n &&& packW w (fun s => if p s then 2 ^ (w - 1) else 0) n from rfl,
      Nat.testBit_land] at this
    simp only [Bool.and_eq_true] at this
    exact this.1
  rw [testBit_packW w z hz n t (w - 1) ht hb] at hZ
  exact Nat.ge_two_pow_of_testBit hZ

/-- The packed lower-bound test on the slots selected by `p`. -/
theorem PRep.ge_of_testP {w n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep w n U d M)
    (hw : 1 < w) (th : ℤ) (hbound : 4 * (M + th.natAbs) < 2 ^ (w - 1)) (p : ℕ → Bool)
    (h : Nat.land (U.1 + 2 ^ (w - 1) * packW w (fun _ => 1) n +
        (if th < 0 then th.natAbs * packW w (fun _ => 1) n else 0) -
        (U.2 + (if 0 ≤ th then th.natAbs * packW w (fun _ => 1) n else 0)))
        (packW w (fun t => if p t then 2 ^ (w - 1) else 0) n) =
          packW w (fun t => if p t then 2 ^ (w - 1) else 0) n) :
    ∀ t < n, p t = true → th ≤ d t := by
  obtain ⟨a, b, rfl, hd, hM⟩ := hU
  set K := 2 ^ (w - 1) with hK
  have hKw : 2 ^ w = 2 * K := by
    rw [hK, ← pow_succ']; congr 1; omega
  set tp := (if th < 0 then th.natAbs else 0) with htp
  set tn := (if 0 ≤ th then th.natAbs else 0) with htn
  have hzero : packW w (fun _ => 0) n = 0 := by
    have := packW_smul w 0 (fun _ => 1) n
    simpa using this
  have hconst : ∀ c : ℕ, c * packW w (fun _ => 1) n = packW w (fun _ => c) n := by
    intro c; rw [← packW_smul]; simp only [mul_one]
  have htp' : (if th < 0 then th.natAbs * packW w (fun _ => 1) n else 0) =
      packW w (fun _ => tp) n := by
    rw [htp]
    by_cases h0 : th < 0
    · simp only [h0, ↓reduceIte, hconst]
    · simp only [h0, ↓reduceIte, hzero]
  have htn' : (if 0 ≤ th then th.natAbs * packW w (fun _ => 1) n else 0) =
      packW w (fun _ => tn) n := by
    rw [htn]
    by_cases h0 : 0 ≤ th
    · simp only [h0, ↓reduceIte, hconst]
    · simp only [h0, ↓reduceIte, hzero]
  have hKo : K * packW w (fun _ => 1) n = packW w (fun _ => K) n := hconst K
  simp only at h
  rw [htp', htn', hKo, ← packW_add, ← packW_add, ← packW_add] at h
  have hle : ∀ t, b t + tn ≤ a t + K + tp := by
    intro t
    have := (hM t).2
    have : tn ≤ th.natAbs := by rw [htn]; split_ifs <;> omega
    omega
  rw [packW_sub w _ _ hle] at h
  have hz : ∀ t, a t + K + tp - (b t + tn) < 2 ^ w := by
    intro t
    have := (hM t).1
    have : tp ≤ th.natAbs := by rw [htp]; split_ifs <;> omega
    omega
  have hge := ge_of_land_maskP w n (by omega) _ hz p h
  intro t ht hpt
  have := hge t ht hpt
  have hdt := hd t
  have : (K : ℤ) ≤ a t + K + tp - (b t + tn) := by
    have h1 : b t + tn ≤ a t + K + tp := hle t
    exact_mod_cast this
  rw [htp, htn] at this
  split_ifs at this with h1 h2 <;> omega

/-! ## Packed sums as polynomials in `x = 2^w` -/

theorem packW_eq_sum (w : ℕ) (z : ℕ → ℕ) :
    ∀ n, packW w z n = ∑ t ∈ Finset.range n, z t * (2 ^ w) ^ t
  | 0 => rfl
  | n + 1 => by
      rw [packW, packW_eq_sum w z n, Finset.sum_range_succ, ← pow_mul]; ring

theorem packW_congr (w : ℕ) (z z' : ℕ → ℕ) :
    ∀ n, (∀ t < n, z t = z' t) → packW w z n = packW w z' n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [packW]
      rw [packW_congr w z z' n (fun t ht => h t (by omega)), h n (by omega)]

theorem PRep.zero (w n : ℕ) : PRep w n (0, 0) (fun _ => 0) 0 :=
  ⟨fun _ => 0, fun _ => 0, by simp [packW_eq_sum], fun _ => by simp, fun _ => by simp⟩

/-- A nonnegative packed vector with bounded slots. -/
theorem PRep.ofNat (w n : ℕ) (z : ℕ → ℕ) (M : ℕ) (hz : ∀ t < n, z t ≤ M) :
    PRep w n (packW w z n, 0) (fun t => if t < n then (z t : ℤ) else 0) M := by
  refine ⟨fun t => if t < n then z t else 0, fun _ => 0, ?_, fun t => ?_, fun t => ?_⟩
  · simp only [Prod.mk.injEq]
    refine ⟨packW_congr w _ _ n fun t ht => by simp [ht], ?_⟩
    simp [packW_eq_sum]
  · simp only
    split_ifs <;> simp
  · simp only
    split_ifs with h
    · exact ⟨hz t h, Nat.zero_le _⟩
    · simp

theorem PRep.neg {w n : ℕ} {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep w n U d M) :
    PRep w n (U.2, U.1) (fun t => -d t) M := by
  obtain ⟨a, b, rfl, hd, hM⟩ := hU
  exact ⟨b, a, rfl, fun t => by simp only; rw [← hd t]; ring, fun t => ⟨(hM t).2, (hM t).1⟩⟩

theorem PRep.congr {w n : ℕ} {U : ℕ × ℕ} {d e : ℕ → ℤ} {M : ℕ} (hU : PRep w n U d M)
    (h : ∀ t, d t = e t) : PRep w n U e M := by
  obtain ⟨a, b, hU, hd, hM⟩ := hU
  exact ⟨a, b, hU, fun t => (hd t).trans (h t), hM⟩

end Noperts.Stellated.PackedSlots
