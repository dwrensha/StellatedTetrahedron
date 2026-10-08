module

public import Noperts.Stellated.CornerKernel

@[expose] public section

/-!
# A fast Nat form of the integer cheap bound

`cheapP` computes the quantities of `cheapCore` in one pass over the terms,
with sign–magnitude Nat arithmetic (GMP-backed in the kernel).  Per term, a
single product-rule walk yields the monomial's magnitude at `|x|` and at
`|x| + hm`, its sign parity, and the `H`-weighted partial derivatives of all
seven variables packed into one Nat (variable `j` in bits `[256 j, 256 j + 256)`),
split by the sign of the coordinate.  `cheapP_imp` shows it implies `cheapI`.
-/

namespace Noperts.Stellated.CornerKernel

open SparsePoly

/-! ## Per-term walks -/

/-- `∏ (a_i)^(e_i)` over lockstep lists (missing entries are `0`). -/
def monoNat (ax : List ℕ) : Mono → ℕ
  | [] => 1
  | e :: m => ax.headD 0 ^ e * monoNat ax.tail m

/-- Parity of the number of negative factors. -/
def parN (sg : List Bool) : Mono → Bool
  | [] => false
  | e :: m => (sg.headD false && e % 2 == 1) ^^ parN sg.tail m

/-- The product-rule derivative of `monoNat ax` in direction `w`. -/
def linNat (ax w : List ℕ) : Mono → ℕ
  | [] => 0
  | e :: m => ax.headD 0 ^ e * linNat ax.tail w.tail m +
      e * ax.headD 0 ^ (e - 1) * w.headD 0 * monoNat ax.tail m

theorem headD_drop (l : List ℕ) (k : ℕ) : (l.drop k).headD 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => cases k <;> simp

theorem headD_drop_bool (l : List Bool) (k : ℕ) :
    (l.drop k).headD false = l.getD k false := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => cases k <;> simp

theorem tail_drop {α : Type} (l : List α) (k : ℕ) : (l.drop k).tail = l.drop (k + 1) := by
  rw [List.tail_drop]

/-- Signed integer coordinates from magnitudes and signs. -/
def xI (ax : List ℕ) (sg : List Bool) (i : ℕ) : ℤ :=
  if sg.getD i false then -(ax.getD i 0 : ℤ) else ax.getD i 0

def natI (ax : List ℕ) (i : ℕ) : ℤ := ax.getD i 0

def sgnI (b : Bool) (v : ℤ) : ℤ := if b then -v else v

theorem monoI_natI (ax : List ℕ) :
    ∀ (k : ℕ) (m : Mono), monoI (natI ax) k m = monoNat (ax.drop k) m
  | _, [] => by simp [monoI, monoNat]
  | k, e :: m => by
      simp only [monoI, monoNat, monoI_natI ax (k + 1) m, headD_drop, tail_drop, natI]
      push_cast; rfl

theorem monoI_xI (ax : List ℕ) (sg : List Bool) :
    ∀ (k : ℕ) (m : Mono),
      monoI (xI ax sg) k m = sgnI (parN (sg.drop k) m) (monoNat (ax.drop k) m)
  | _, [] => by simp [monoI, monoNat, parN, sgnI]
  | k, e :: m => by
      simp only [monoI, monoNat, parN, monoI_xI ax sg (k + 1) m, headD_drop, headD_drop_bool,
        tail_drop, xI]
      rcases Nat.even_or_odd e with he | he
      · have h2 : e % 2 = 0 := Nat.even_iff.mp he
        cases sg.getD k false <;> cases parN (sg.drop (k + 1)) m <;>
          simp [sgnI, h2, he.neg_pow]
      · have h2 : e % 2 = 1 := Nat.odd_iff.mp he
        cases sg.getD k false <;> cases parN (sg.drop (k + 1)) m <;>
          simp [sgnI, h2, he.neg_pow]

theorem derivI_of_lt (x : ℕ → ℤ) (i : ℕ) :
    ∀ (k : ℕ) (m : Mono), i < k → derivI x i k m = 0
  | _, [], _ => rfl
  | k, e :: m, h => by
      simp only [derivI, ite_eq_right (by omega : k ≠ i), derivI_of_lt x i (k + 1) m (by omega),
        mul_zero]

theorem derivI_of_ge (x : ℕ → ℤ) (i : ℕ) :
    ∀ (k : ℕ) (m : Mono), k + m.length ≤ i → derivI x i k m = 0
  | _, [], _ => rfl
  | k, e :: m, h => by
      simp only [List.length_cons] at h
      simp only [derivI, ite_eq_right (by omega : k ≠ i),
        derivI_of_ge x i (k + 1) m (by omega), mul_zero]

theorem linNat_eq (ax w : List ℕ) (n : ℕ) :
    ∀ (k : ℕ) (m : Mono), k + m.length ≤ n →
      (linNat (ax.drop k) (w.drop k) m : ℤ) =
        ∑ j ∈ Finset.range n, (w.getD j 0 : ℤ) * derivI (natI ax) j k m
  | _, [], _ => by simp [linNat, derivI]
  | k, e :: m, h => by
      simp only [List.length_cons] at h
      have ih := linNat_eq ax w n (k + 1) m (by omega)
      have hk : k ∈ Finset.range n := Finset.mem_range.mpr (by omega)
      have hterm : ∀ j, (w.getD j 0 : ℤ) * derivI (natI ax) j k (e :: m) =
          (if j = k then (w.getD k 0 : ℤ) * ((e : ℤ) * natI ax k ^ (e - 1) *
            monoI (natI ax) (k + 1) m) else 0) +
          natI ax k ^ e * ((w.getD j 0 : ℤ) * derivI (natI ax) j (k + 1) m) := by
        intro j
        simp only [derivI]
        by_cases hj : j = k
        · subst hj
          simp [derivI_of_lt (natI ax) j (j + 1) m (by omega)]
        · simp [hj, Ne.symm hj]
          ring
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_ite_eq',
        ite_eq_left hk, ← Finset.mul_sum, ← ih]
      simp only [linNat, headD_drop, tail_drop, monoI_natI, natI]
      push_cast
      ring

theorem derivI_xI (ax : List ℕ) (sg : List Bool) (j : ℕ) :
    ∀ (k : ℕ) (m : Mono),
      derivI (xI ax sg) j k m =
        sgnI (parN (sg.drop k) m ^^ sg.getD j false) (derivI (natI ax) j k m)
  | _, [] => by simp [derivI, sgnI]
  | k, e :: m => by
      simp only [derivI, parN, headD_drop_bool, tail_drop]
      by_cases hkj : k = j
      · subst hkj
        simp only [monoI_xI, monoI_natI]
        rcases e with _ | e
        · simp [sgnI]
        · simp only [Nat.add_sub_cancel, xI, natI]
          rcases Nat.even_or_odd e with he | he
          · have h2 : (e + 1) % 2 = 1 := by rcases he with ⟨r, hr⟩; omega
            cases sg.getD k false <;> cases parN (sg.drop (k + 1)) m <;>
              simp [sgnI, h2, he.neg_pow]
          · have h2 : (e + 1) % 2 = 0 := by rcases he with ⟨r, hr⟩; omega
            cases sg.getD k false <;> cases parN (sg.drop (k + 1)) m <;>
              simp [sgnI, h2, he.neg_pow]
      · simp only [ite_eq_right hkj, derivI_xI ax sg j (k + 1) m, xI, natI]
        rcases Nat.even_or_odd e with he | he
        · have h2 : e % 2 = 0 := Nat.even_iff.mp he
          cases sg.getD k false <;> cases parN (sg.drop (k + 1)) m <;>
            cases sg.getD j false <;> simp [sgnI, h2, he.neg_pow]
        · have h2 : e % 2 = 1 := Nat.odd_iff.mp he
          cases sg.getD k false <;> cases parN (sg.drop (k + 1)) m <;>
            cases sg.getD j false <;> simp [sgnI, h2, he.neg_pow]

/-! ## The checker -/

/-- One product-rule walk: `(P, Q, parity, Zp, Zm)` = magnitudes at `ax` and
`up`, sign parity, and the derivatives in directions `wp`, `wm`. -/
def walk (ax up wp wm : List ℕ) (sgB : List Bool) : Mono → ℕ × ℕ × Bool × ℕ × ℕ
  | [] => (1, 1, false, 0, 0)
  | e :: m =>
      let r := walk ax.tail up.tail wp.tail wm.tail sgB.tail m
      if e = 0 then r else
        let ae := ax.headD 0 ^ e
        let de := e * ax.headD 0 ^ (e - 1) * r.1
        (ae * r.1, up.headD 0 ^ e * r.2.1, (sgB.headD false && e % 2 == 1) ^^ r.2.2.1,
          ae * r.2.2.2.1 + de * wp.headD 0, ae * r.2.2.2.2 + de * wm.headD 0)

theorem walk_eq (ax up wp wm : List ℕ) (sgB : List Bool) :
    ∀ m : Mono, walk ax up wp wm sgB m =
      (monoNat ax m, monoNat up m, parN sgB m, linNat ax wp m, linNat ax wm m)
  | [] => rfl
  | e :: m => by
      simp only [walk, walk_eq ax.tail up.tail wp.tail wm.tail sgB.tail m]
      split_ifs with he
      · subst he
        simp [monoNat, parN, linNat]
      · simp only [monoNat, parN, linNat, Prod.mk.injEq]
        refine ⟨trivial, trivial, trivial, by ring, by ring⟩

/-- Packing weights: `H_j · 2^(256 j)` on coordinates with the given sign. -/
def packW (sgB : List Bool) (H : List ℕ) (neg : Bool) : List ℕ :=
  (List.range 7).map fun j =>
    if sgB.getD j false == neg then H.getD j 0 * 2 ^ (256 * j) else 0

def slot (x j : ℕ) : ℕ := x / 2 ^ (256 * j) % 2 ^ 256

def addL7 (ax H : List ℕ) : List ℕ := (List.range 7).map fun i => ax.getD i 0 + H.getD i 0

/-- Accumulate over the terms; `vP vN V T gP gN` as in `cheapP`. -/
def accP (D N : ℕ) (ax up wp wm : List ℕ) (sgB : List Bool) :
    List (Mono × ℕ × Bool) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | [], vP, vN, V, T, gP, gN => (vP, vN, V, T, gP, gN)
  | t :: S, vP, vN, V, T, gP, gN =>
      let r := walk ax up wp wm sgB t.1
      let c := t.2.1 * D ^ (N - degM t.1)
      let cP := c * r.1
      if t.2.2 ^^ r.2.2.1 then
        accP D N ax up wp wm sgB S vP (vN + cP) (V + cP) (T + c * r.2.1)
          (gP + c * r.2.2.2.2) (gN + c * r.2.2.2.1)
      else
        accP D N ax up wp wm sgB S (vP + cP) vN (V + cP) (T + c * r.2.1)
          (gP + c * r.2.2.2.1) (gN + c * r.2.2.2.2)

/-- The (negated) linear-part bound of one coordinate: `|p - q|` (centered) or
`(q - p)⁺` (corner). -/
def linT (centered : Bool) (p q : ℕ) : ℕ :=
  if centered then (if p ≤ q then q - p else p - q) else q - p

/-- Linear and remainder sums from the packed gradients: `(lin, L)`. -/
def finishLin (centered : Bool) (gP gN : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | j + 1 =>
      let r := finishLin centered gP gN j
      let p := slot gP j
      let q := slot gN j
      (r.1 + linT centered p q, r.2 + p + q)

def maxDegN (S : List (Mono × ℕ × Bool)) : ℕ := (S.map fun t => degM t.1).foldr max 0

/-- The cheap bound for `S` (terms `(m, |c|, c < 0)`) at the anchor with
magnitudes `ax` and signs `sgB` (over `D`), displacement `h ∈ [-H, H] / D`
(`centered`) or `h ∈ [0, H] / D`. -/
def cheapP (S : List (Mono × ℕ × Bool)) (D : ℕ) (ax : List ℕ) (sgB : List Bool)
    (H : List ℕ) (centered : Bool) : Bool :=
  let N := maxDegN S
  let a := accP D N ax (addL7 ax H) (packW sgB H false) (packW sgB H true) sgB S 0 0 0 0 0 0
  let f := finishLin centered a.2.2.2.2.1 a.2.2.2.2.2 7
  Nat.blt 0 D && S.all (fun t => Nat.ble t.1.length 7) &&
    Nat.ble ax.length 7 && Nat.ble H.length 7 &&
    Nat.blt (N * a.2.2.2.1) (2 ^ 256) &&
    Nat.ble (a.2.1 + f.1 + a.2.2.2.1) (a.1 + a.2.2.1 + f.2)

/-! ## Soundness: accumulation -/

section
variable (D N : ℕ) (ax up wp wm : List ℕ) (sgB : List Bool)

def tc (t : Mono × ℕ × Bool) : ℕ := t.2.1 * D ^ (N - degM t.1)
def tneg (t : Mono × ℕ × Bool) : Bool := t.2.2 ^^ parN sgB t.1

theorem accP_eq : ∀ (S : List (Mono × ℕ × Bool)) (vP vN V T gP gN : ℕ),
    accP D N ax up wp wm sgB S vP vN V T gP gN =
      (vP + (S.map fun t => if tneg sgB t then 0 else tc D N t * monoNat ax t.1).sum,
       vN + (S.map fun t => if tneg sgB t then tc D N t * monoNat ax t.1 else 0).sum,
       V + (S.map fun t => tc D N t * monoNat ax t.1).sum,
       T + (S.map fun t => tc D N t * monoNat up t.1).sum,
       gP + (S.map fun t => tc D N t *
         (if tneg sgB t then linNat ax wm t.1 else linNat ax wp t.1)).sum,
       gN + (S.map fun t => tc D N t *
         (if tneg sgB t then linNat ax wp t.1 else linNat ax wm t.1)).sum)
  | [], vP, vN, V, T, gP, gN => by simp [accP]
  | t :: S, vP, vN, V, T, gP, gN => by
      simp only [accP, walk_eq]
      split_ifs with h
      · rw [accP_eq S]
        simp only [List.map_cons, List.sum_cons, tneg, h, ite_true, Prod.mk.injEq, tc]
        refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩
      · rw [accP_eq S]
        have h' : (t.2.2 ^^ parN sgB t.1) = false := by simpa using h
        simp only [List.map_cons, List.sum_cons, tneg, h', Prod.mk.injEq, tc]
        refine ⟨by simp; ring, by simp, by ring, by ring, by simp; ring, by simp; ring⟩

end

/-! ## Soundness: packed slots -/

def packSum (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packSum c n + c n * 2 ^ (256 * n)

theorem packSum_lt (c : ℕ → ℕ) (hc : ∀ j, c j < 2 ^ 256) :
    ∀ n, packSum c n < 2 ^ (256 * n)
  | 0 => by simp [packSum]
  | n + 1 => by
      have ih := packSum_lt c hc n
      have h1 := hc n
      simp only [packSum]
      calc packSum c n + c n * 2 ^ (256 * n)
          < 2 ^ (256 * n) + c n * 2 ^ (256 * n) := by omega
        _ = (c n + 1) * 2 ^ (256 * n) := by ring
        _ ≤ 2 ^ 256 * 2 ^ (256 * n) := Nat.mul_le_mul_right _ h1
        _ = 2 ^ (256 * (n + 1)) := by rw [← pow_add]; ring_nf

theorem slot_packSum (c : ℕ → ℕ) (hc : ∀ j, c j < 2 ^ 256) :
    ∀ n j, j < n → slot (packSum c n) j = c j
  | 0, j, h => absurd h (by omega)
  | n + 1, j, h => by
      simp only [slot, packSum]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with hj | hj
      · have hsplit : c n * 2 ^ (256 * n) =
            2 ^ 256 * (c n * 2 ^ (256 * (n - j - 1))) * 2 ^ (256 * j) := by
          rw [show 256 * n = 256 + 256 * (n - j - 1) + 256 * j by omega, pow_add, pow_add]
          ring
        rw [hsplit, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]
        exact slot_packSum c hc n j hj
      · subst hj
        rw [Nat.add_mul_div_right _ _ (by positivity),
          Nat.div_eq_of_lt (packSum_lt c hc j), zero_add, Nat.mod_eq_of_lt (hc j)]

/-! ## Soundness: Nat partials and their bound -/

/-- `derivI` on Nat coordinates. -/
def derivN (ax : List ℕ) (i : ℕ) : ℕ → Mono → ℕ
  | _, [] => 0
  | k, e :: m => if k = i then e * ax.getD k 0 ^ (e - 1) * monoNat (ax.drop (k + 1)) m
      else ax.getD k 0 ^ e * derivN ax i (k + 1) m

theorem derivN_cast (ax : List ℕ) (i : ℕ) :
    ∀ (k : ℕ) (m : Mono), (derivN ax i k m : ℤ) = derivI (natI ax) i k m
  | _, [] => rfl
  | k, e :: m => by
      simp only [derivN, derivI]
      split_ifs
      · rw [monoI_natI]; push_cast; rfl
      · rw [← derivN_cast ax i (k + 1) m]; push_cast; rfl

theorem monoNat_mono (ax up : List ℕ) (h : ∀ i, ax.getD i 0 ≤ up.getD i 0) :
    ∀ (k : ℕ) (m : Mono), monoNat (ax.drop k) m ≤ monoNat (up.drop k) m
  | _, [] => le_rfl
  | k, e :: m => by
      simp only [monoNat, headD_drop, tail_drop]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (h k) e) (monoNat_mono ax up h (k + 1) m)

theorem pow_pred_mul_le (a H u e : ℕ) (hu : a + H ≤ u) :
    e * a ^ (e - 1) * H ≤ e * u ^ e := by
  rcases e with _ | e
  · simp
  · rw [Nat.add_sub_cancel, mul_assoc]
    apply Nat.mul_le_mul_left
    calc a ^ e * H ≤ u ^ e * u :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) e) (by omega)
      _ = u ^ (e + 1) := (pow_succ u e).symm

theorem derivN_bound (ax up : List ℕ) (H : ℕ) (j : ℕ)
    (h : ∀ i, ax.getD i 0 ≤ up.getD i 0) (hj : ax.getD j 0 + H ≤ up.getD j 0) :
    ∀ (k : ℕ) (m : Mono), derivN ax j k m * H ≤ degM m * monoNat (up.drop k) m
  | _, [] => by simp [derivN]
  | k, e :: m => by
      simp only [derivN, degM_cons, monoNat, headD_drop, tail_drop]
      have hm := monoNat_mono ax up h (k + 1) m
      split_ifs with hk
      · subst hk
        have := pow_pred_mul_le (ax.getD k 0) H (up.getD k 0) e hj
        calc e * ax.getD k 0 ^ (e - 1) * monoNat (ax.drop (k + 1)) m * H
            = e * ax.getD k 0 ^ (e - 1) * H * monoNat (ax.drop (k + 1)) m := by ring
          _ ≤ e * up.getD k 0 ^ e * monoNat (up.drop (k + 1)) m := Nat.mul_le_mul this hm
          _ ≤ (e + degM m) * (up.getD k 0 ^ e * monoNat (up.drop (k + 1)) m) := by
            rw [← mul_assoc]
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      · have ih := derivN_bound ax up H j h hj (k + 1) m
        calc ax.getD k 0 ^ e * derivN ax j (k + 1) m * H
            = ax.getD k 0 ^ e * (derivN ax j (k + 1) m * H) := by ring
          _ ≤ up.getD k 0 ^ e * (degM m * monoNat (up.drop (k + 1)) m) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (h k) e) ih
          _ ≤ (e + degM m) * (up.getD k 0 ^ e * monoNat (up.drop (k + 1)) m) := by
            rw [mul_left_comm]
            exact Nat.mul_le_mul_right _ (by omega)

/-! ## Soundness: packing -/

theorem packSum_eq (c : ℕ → ℕ) :
    ∀ n, packSum c n = ∑ j ∈ Finset.range n, c j * 2 ^ (256 * j)
  | 0 => rfl
  | n + 1 => by rw [packSum, packSum_eq c n, Finset.sum_range_succ]

theorem packSum_add (c d : ℕ → ℕ) (n : ℕ) :
    packSum (fun j => c j + d j) n = packSum c n + packSum d n := by
  simp only [packSum_eq, add_mul, Finset.sum_add_distrib]

theorem packSum_mul (a : ℕ) (c : ℕ → ℕ) (n : ℕ) :
    a * packSum c n = packSum (fun j => a * c j) n := by
  simp only [packSum_eq, Finset.mul_sum, mul_assoc]

theorem packSum_zero (n : ℕ) : packSum (fun _ => 0) n = 0 := by
  simp [packSum_eq]

theorem packSum_list {α : Type} (S : List α) (f : α → ℕ → ℕ) (n : ℕ) :
    (S.map fun t => packSum (f t) n).sum = packSum (fun j => (S.map fun t => f t j).sum) n := by
  induction S with
  | nil => simp [packSum_zero]
  | cons t S ih => simp only [List.map_cons, List.sum_cons, ih, packSum_add]

theorem getD_packW (sgB : List Bool) (H : List ℕ) (neg : Bool) (j : ℕ) (hj : j < 7) :
    (packW sgB H neg).getD j 0 =
      if sgB.getD j false == neg then H.getD j 0 * 2 ^ (256 * j) else 0 := by
  simp [packW, List.getD_eq_getElem?_getD, hj]

theorem linNat_pack (ax : List ℕ) (sgB : List Bool) (H : List ℕ) (neg : Bool) (m : Mono)
    (hm : m.length ≤ 7) :
    linNat ax (packW sgB H neg) m = packSum (fun j =>
      if sgB.getD j false == neg then H.getD j 0 * derivN ax j 0 m else 0) 7 := by
  apply Nat.cast_injective (R := ℤ)
  have := linNat_eq ax (packW sgB H neg) 7 0 m (by omega)
  simp only [List.drop_zero] at this
  rw [this, packSum_eq]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [getD_packW sgB H neg j (Finset.mem_range.mp hj), ← derivN_cast]
  split_ifs <;> push_cast <;> ring

/-! ## Soundness: the integer quantities -/

/-- The signed integer polynomial of `S`. -/
def toIPoly (S : List (Mono × ℕ × Bool)) : IPoly :=
  S.map fun t => (t.1, sgnI t.2.2 (t.2.1 : ℤ))

def loI (H : List ℕ) (centered : Bool) (i : ℕ) : ℤ := if centered then -natI H i else 0

theorem sumI_nil (f : Mono × ℤ → ℤ) : sumI [] f = 0 := rfl

theorem sumI_cons (t : Mono × ℤ) (S : IPoly) (f : Mono × ℤ → ℤ) :
    sumI (t :: S) f = f t + sumI S f := rfl

theorem sum7_eq (f : ℕ → ℤ) : sum7 f = ∑ i ∈ Finset.range 7, f i := by
  simp [sum7, List.range_succ, Finset.sum_range_succ]
  ring

theorem maxDeg_toIPoly (S : List (Mono × ℕ × Bool)) : maxDeg (toIPoly S) = maxDegN S := by
  simp [maxDeg, maxDegN, toIPoly, Function.comp_def]

theorem degM_le_maxDegN (S : List (Mono × ℕ × Bool)) (t : Mono × ℕ × Bool) (ht : t ∈ S) :
    degM t.1 ≤ maxDegN S := by
  have := degM_le_maxDeg (toIPoly S) (t.1, sgnI t.2.2 (t.2.1 : ℤ))
    (List.mem_map.mpr ⟨t, ht, rfl⟩)
  rwa [maxDeg_toIPoly] at this

theorem abs_sgnI (b : Bool) (v : ℤ) : |sgnI b v| = |v| := by cases b <;> simp [sgnI]

theorem abs_xI (ax : List ℕ) (sgB : List Bool) : (fun i => |xI ax sgB i|) = natI ax := by
  funext i
  simp only [xI, natI]
  split_ifs <;> simp

section
variable (D N : ℕ) (ax : List ℕ) (sgB : List Bool)

theorem valSum_eq : ∀ S : List (Mono × ℕ × Bool),
    valSum (toIPoly S) D N (xI ax sgB) =
      ((S.map fun t => if tneg sgB t then 0 else tc D N t * monoNat ax t.1).sum : ℕ) -
      ((S.map fun t => if tneg sgB t then tc D N t * monoNat ax t.1 else 0).sum : ℕ)
  | [] => rfl
  | t :: S => by
      have ih := valSum_eq S
      simp only [valSum, toIPoly, List.map_cons, sumI_cons] at ih ⊢
      rw [ih, monoI_xI]
      simp only [List.drop_zero, List.sum_cons, tneg, tc]
      obtain ⟨m, c, b⟩ := t
      cases b <;> by_cases hp : parN sgB m = true <;> simp [hp, sgnI] <;> ring

theorem absSum_eq (up : List ℕ) : ∀ S : List (Mono × ℕ × Bool),
    absSum (toIPoly S) D N (natI up) =
      ((S.map fun t => tc D N t * monoNat up t.1).sum : ℕ)
  | [] => rfl
  | t :: S => by
      have ih := absSum_eq up S
      simp only [absSum, toIPoly, List.map_cons, sumI_cons] at ih ⊢
      rw [ih, monoI_natI, abs_sgnI]
      simp only [List.drop_zero, List.sum_cons, tc]
      push_cast
      rw [abs_of_nonneg (by positivity)]
      ring

def pSlot (H : List ℕ) (S : List (Mono × ℕ × Bool)) (same : Bool) (j : ℕ) : ℕ :=
  (S.map fun t => if (sgB.getD j false == tneg sgB t) == same then
    tc D N t * (H.getD j 0 * derivN ax j 0 t.1) else 0).sum

theorem gradSum_eq (H : List ℕ) (j : ℕ) : ∀ S : List (Mono × ℕ × Bool),
    gradSum (toIPoly S) D N (xI ax sgB) j * natI H j =
      (pSlot D N ax sgB H S true j : ℤ) - pSlot D N ax sgB H S false j
  | [] => by simp [gradSum, toIPoly, sumI_nil, pSlot]
  | t :: S => by
      have ih := gradSum_eq H j S
      simp only [gradSum, pSlot, toIPoly, List.map_cons, sumI_cons] at ih ⊢
      rw [add_mul, ih, derivI_xI, ← derivN_cast]
      simp only [List.drop_zero, List.sum_cons, tneg, tc, natI]
      obtain ⟨m, c, b⟩ := t
      generalize sgB.getD j false = sj
      cases b <;> by_cases hp : parN sgB m = true <;> cases sj <;>
        simp [hp, sgnI] <;> ring

theorem absGradSum_eq (H : List ℕ) (j : ℕ) : ∀ S : List (Mono × ℕ × Bool),
    natI H j * absGradSum (toIPoly S) D N (natI ax) j =
      (pSlot D N ax sgB H S true j : ℤ) + pSlot D N ax sgB H S false j
  | [] => by simp [absGradSum, toIPoly, sumI_nil, pSlot]
  | t :: S => by
      have ih := absGradSum_eq H j S
      simp only [absGradSum, pSlot, toIPoly, List.map_cons, sumI_cons] at ih ⊢
      rw [mul_add, ih, abs_sgnI, ← derivN_cast]
      simp only [List.sum_cons, tneg, tc, natI]
      push_cast
      rw [abs_of_nonneg (by positivity)]
      obtain ⟨m, c, b⟩ := t
      generalize sgB.getD j false = sj
      cases b <;> by_cases hp : parN sgB m = true <;> cases sj <;>
        simp [hp] <;> ring

end

theorem grad_pack (D N : ℕ) (ax : List ℕ) (sgB : List Bool) (H : List ℕ)
    (S : List (Mono × ℕ × Bool)) (hS : ∀ t ∈ S, t.1.length ≤ 7) (same : Bool) :
    (S.map fun t => tc D N t * (if tneg sgB t == same then linNat ax (packW sgB H true) t.1
      else linNat ax (packW sgB H false) t.1)).sum = packSum (pSlot D N ax sgB H S same) 7 := by
  unfold pSlot
  rw [← packSum_list]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rw [linNat_pack ax sgB H true t.1 (hS t ht), linNat_pack ax sgB H false t.1 (hS t ht)]
  have key : ∀ neg : Bool, (tneg sgB t == same) = neg →
      (fun j => tc D N t * if sgB.getD j false == neg then H.getD j 0 * derivN ax j 0 t.1
        else 0) = fun j => if (sgB.getD j false == tneg sgB t) == same then
          tc D N t * (H.getD j 0 * derivN ax j 0 t.1) else 0 := by
    intro neg hneg
    funext j
    cases hs : sgB.getD j false <;> cases ht' : tneg sgB t <;> cases same <;>
      simp_all
  split_ifs with h
  · rw [packSum_mul, key true (by simpa using h)]
  · rw [packSum_mul, key false (by simpa using h)]

theorem pSlot_le (D N : ℕ) (ax : List ℕ) (sgB : List Bool) (H : List ℕ)
    (S : List (Mono × ℕ × Bool)) (same : Bool) (j : ℕ)
    (hup : ∀ i, ax.getD i 0 ≤ (addL7 ax H).getD i 0)
    (hj : ax.getD j 0 + H.getD j 0 ≤ (addL7 ax H).getD j 0)
    (hN : ∀ t ∈ S, degM t.1 ≤ N) :
    pSlot D N ax sgB H S same j ≤ N * (S.map fun t => tc D N t * monoNat (addL7 ax H) t.1).sum := by
  unfold pSlot
  rw [← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro t ht
  split_ifs
  · have hb := derivN_bound ax (addL7 ax H) (H.getD j 0) j hup hj 0 t.1
    simp only [List.drop_zero] at hb
    calc tc D N t * (H.getD j 0 * derivN ax j 0 t.1)
        = tc D N t * (derivN ax j 0 t.1 * H.getD j 0) := by ring
      _ ≤ tc D N t * (degM t.1 * monoNat (addL7 ax H) t.1) := Nat.mul_le_mul_left _ hb
      _ ≤ tc D N t * (N * monoNat (addL7 ax H) t.1) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (hN t ht))
      _ = N * (tc D N t * monoNat (addL7 ax H) t.1) := by ring
  · exact Nat.zero_le _

/-! ## Soundness: the implication -/

theorem getD_addL7 (ax H : List ℕ) (hax : ax.length ≤ 7) (hH : H.length ≤ 7) (i : ℕ) :
    (addL7 ax H).getD i 0 = ax.getD i 0 + H.getD i 0 := by
  by_cases hi : i < 7
  · simp [addL7, List.getD_eq_getElem?_getD, hi]
  · simp [addL7, List.getD_eq_getElem?_getD, hi, List.getElem?_eq_none (by omega : ax.length ≤ i),
      List.getElem?_eq_none (by omega : H.length ≤ i)]

theorem finishLin_eq (centered : Bool) (gP gN : ℕ) : ∀ n,
    finishLin centered gP gN n =
      (∑ j ∈ Finset.range n, linT centered (slot gP j) (slot gN j),
        ∑ j ∈ Finset.range n, (slot gP j + slot gN j))
  | 0 => rfl
  | n + 1 => by
      simp only [finishLin, finishLin_eq centered gP gN n, Finset.sum_range_succ]
      ring_nf

theorem min_linT (centered : Bool) (p q : ℕ) :
    min ((if centered then -(1 : ℤ) else 0) * ((p : ℤ) - q)) ((p : ℤ) - q) =
      -((linT centered p q : ℕ) : ℤ) := by
  cases centered <;> simp only [linT, Bool.false_eq_true, ite_false, ite_true, min_def] <;>
    split_ifs <;> omega

theorem max_loI (H : List ℕ) (centered : Bool) (i : ℕ) :
    max |loI H centered i| |natI H i| = natI H i := by
  have h0 : (0 : ℤ) ≤ natI H i := by simp [natI]
  cases centered <;> simp [loI, abs_of_nonneg h0, h0]

theorem cheapP_imp (S : List (Mono × ℕ × Bool)) (D : ℕ) (ax : List ℕ) (sgB : List Bool)
    (H : List ℕ) (centered : Bool) (h : cheapP S D ax sgB H centered = true) :
    cheapI (toIPoly S) D (xI ax sgB) (loI H centered) (natI H) = true := by
  simp only [cheapP, accP_eq, finishLin_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    List.all_eq_true, zero_add] at h
  obtain ⟨⟨⟨⟨⟨hD, hS⟩, hax⟩, hH⟩, hbound⟩, hfin⟩ := h
  set N := maxDegN S with hNdef
  have hNdeg := degM_le_maxDegN S
  have hup := getD_addL7 ax H hax hH
  have hle : ∀ i, ax.getD i 0 ≤ (addL7 ax H).getD i 0 := fun i => by rw [hup]; omega
  have hgP : (S.map fun t => tc D N t * (if tneg sgB t then linNat ax (packW sgB H true) t.1
      else linNat ax (packW sgB H false) t.1)).sum = packSum (pSlot D N ax sgB H S true) 7 := by
    rw [← grad_pack D N ax sgB H S hS true]
    simp
  have hgN : (S.map fun t => tc D N t * (if tneg sgB t then linNat ax (packW sgB H false) t.1
      else linNat ax (packW sgB H true) t.1)).sum = packSum (pSlot D N ax sgB H S false) 7 := by
    rw [← grad_pack D N ax sgB H S hS false]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    cases tneg sgB t <;> simp
  rw [hgP, hgN] at hfin
  have hslot : ∀ same, ∀ j < 7, slot (packSum (pSlot D N ax sgB H S same) 7) j =
      pSlot D N ax sgB H S same j := fun same j hj =>
    slot_packSum _ (fun j' => lt_of_le_of_lt
      (pSlot_le D N ax sgB H S same j' hle (by rw [hup]) hNdeg) hbound) 7 j hj
  have e1 : ∑ j ∈ Finset.range 7, linT centered (slot (packSum (pSlot D N ax sgB H S true) 7) j)
      (slot (packSum (pSlot D N ax sgB H S false) 7) j) =
      ∑ j ∈ Finset.range 7, linT centered (pSlot D N ax sgB H S true j)
        (pSlot D N ax sgB H S false j) := Finset.sum_congr rfl fun j hj => by
    rw [hslot true j (Finset.mem_range.mp hj), hslot false j (Finset.mem_range.mp hj)]
  have e2 : ∑ j ∈ Finset.range 7, (slot (packSum (pSlot D N ax sgB H S true) 7) j +
      slot (packSum (pSlot D N ax sgB H S false) 7) j) =
      ∑ j ∈ Finset.range 7, (pSlot D N ax sgB H S true j + pSlot D N ax sgB H S false j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [hslot true j (Finset.mem_range.mp hj), hslot false j (Finset.mem_range.mp hj)]
  rw [e1, e2] at hfin
  -- the integer form
  simp only [cheapI, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, maxDeg_toIPoly]
  refine ⟨⟨hD, fun t ht => ?_⟩, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hS u hu
  simp only [cheapCore, decide_eq_true_eq, abs_xI, max_loI, sum7_eq]
  have hupF : (fun i => |xI ax sgB i| + natI H i) = natI (addL7 ax H) := by
    funext i
    have := congrFun (abs_xI ax sgB) i
    rw [this]
    simp only [natI, hup]
    push_cast
    rfl
  rw [hupF, valSum_eq, absSum_eq, absSum_eq]
  rw [Finset.sum_congr rfl fun i _ => by
      rw [show loI H centered i = (if centered then -(1 : ℤ) else 0) * natI H i by
          cases centered <;> simp [loI],
        show ∀ g : ℤ, g * ((if centered then -(1 : ℤ) else 0) * natI H i) =
          (if centered then -(1 : ℤ) else 0) * (g * natI H i) from fun g => by ring,
        gradSum_eq, min_linT]]
  rw [Finset.sum_congr rfl fun i _ => absGradSum_eq D N ax sgB H i S]
  have hZ := (Nat.cast_le (α := ℤ)).mpr hfin
  push_cast at hZ ⊢
  simp only [Finset.sum_neg_distrib]
  linarith

end Noperts.Stellated.CornerKernel
