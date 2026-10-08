module

public import Noperts.Stellated.CheapBound

@[expose] public section

/-!
# An integer cheap bound for the kernel

`cheapI S D x lo hi` checks, in integer arithmetic, the cheap bound
(`CheapBound.cheap_bound`) of an integer-coefficient polynomial `S` at the
anchor `x / D` over displacements `lo / D ≤ h ≤ hi / D`: value, gradient and
the absolute-majorant remainder, all scaled by `D ^ N` (`N` the degree).  No
substitution or expansion is involved, so it suits `decide +kernel`.
-/

namespace Noperts.Stellated.CornerKernel

open SparsePoly CheapBound

/-- A polynomial with integer coefficients. -/
abbrev IPoly := List (Mono × ℤ)

def IPoly.toPoly (S : IPoly) : Poly := S.map fun t => (t.1, (t.2 : ℚ))

def degM (m : Mono) : ℕ := m.foldr (· + ·) 0

/-- `∏ⱼ x (k + j) ^ mⱼ`. -/
def monoI (x : ℕ → ℤ) : ℕ → Mono → ℤ
  | _, [] => 1
  | k, e :: m => x k ^ e * monoI x (k + 1) m

/-- The partial derivative of `∏ⱼ x (k + j) ^ mⱼ` in variable `i`. -/
def derivI (x : ℕ → ℤ) (i : ℕ) : ℕ → Mono → ℤ
  | _, [] => 0
  | k, e :: m => if k = i then (e : ℤ) * x k ^ (e - 1) * monoI x (k + 1) m
      else x k ^ e * derivI x i (k + 1) m

def maxDeg (S : IPoly) : ℕ := (S.map fun t => degM t.1).foldr max 0

def sumI (S : IPoly) (f : Mono × ℤ → ℤ) : ℤ := (S.map f).foldr (· + ·) 0

/-- Sum over the seven chart variables. -/
def sum7 (f : ℕ → ℤ) : ℤ := (List.range 7).foldr (fun i acc => f i + acc) 0

section
variable (S : IPoly) (D N : ℕ)

/-- `Σ c · ∏ xᵐ`, homogenized to degree `N` by powers of `D`. -/
def valSum (x : ℕ → ℤ) : ℤ := sumI S fun t => t.2 * monoI x 0 t.1 * (D : ℤ) ^ (N - degM t.1)

def absSum (x : ℕ → ℤ) : ℤ := sumI S fun t => |t.2| * monoI x 0 t.1 * (D : ℤ) ^ (N - degM t.1)

def gradSum (x : ℕ → ℤ) (i : ℕ) : ℤ :=
  sumI S fun t => t.2 * derivI x i 0 t.1 * (D : ℤ) ^ (N - degM t.1)

def absGradSum (x : ℕ → ℤ) (i : ℕ) : ℤ :=
  sumI S fun t => |t.2| * derivI x i 0 t.1 * (D : ℤ) ^ (N - degM t.1)

def cheapCore (x lo hi : ℕ → ℤ) : Bool :=
  decide (0 ≤ valSum S D N x +
      sum7 (fun i => min (gradSum S D N x i * lo i) (gradSum S D N x i * hi i)) -
    (absSum S D N (fun i => |x i| + max |lo i| |hi i|) - absSum S D N (fun i => |x i|) -
      sum7 (fun i => max |lo i| |hi i| * absGradSum S D N (fun i => |x i|) i)))

end

/-- The cheap bound certifies `S ≥ 0` at every `y` with
`lo / D ≤ y - x / D ≤ hi / D`. -/
def cheapI (S : IPoly) (D : ℕ) (x lo hi : ℕ → ℤ) : Bool :=
  decide (0 < D) && S.all (fun t => decide (t.1.length ≤ 7)) &&
    cheapCore S D (maxDeg S) x lo hi

/-! ## Soundness -/

/-- The real partial derivative of a monomial, mirroring `derivI`. -/
noncomputable def derivR (a : ℕ → ℝ) (i : ℕ) : ℕ → Mono → ℝ
  | _, [] => 0
  | k, e :: m => if k = i then (e : ℝ) * a k ^ (e - 1) * monoEvalFrom a (k + 1) m
      else a k ^ e * derivR a i (k + 1) m

theorem powLin_one (a : ℝ) : ∀ e : ℕ, powLin a 1 e = (e : ℝ) * a ^ (e - 1)
  | 0 => by simp [powLin]
  | 1 => by simp [powLin]
  | e + 2 => by
      rw [powLin, powLin_one a (e + 1)]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

theorem derivR_of_lt (a : ℕ → ℝ) (i : ℕ) :
    ∀ (k : ℕ) (m : Mono), i < k → derivR a i k m = 0
  | _, [], _ => rfl
  | k, e :: m, h => by
      simp only [derivR, ite_eq_right (by omega : k ≠ i), derivR_of_lt a i (k + 1) m (by omega),
        mul_zero]

theorem monoLinFrom_unit (a : ℕ → ℝ) (i : ℕ) :
    ∀ (k : ℕ) (m : Mono), monoLinFrom a (unit i) k m = derivR a i k m
  | _, [] => rfl
  | k, e :: m => by
      simp only [monoLinFrom, derivR, monoLinFrom_unit a i (k + 1) m]
      split_ifs with hk
      · subst hk
        rw [derivR_of_lt a k (k + 1) m (by omega)]
        have hu : unit k k = 1 := by simp [unit]
        rw [hu, powLin_one]
        ring
      · rw [powLin_linear _ (unit i k)]
        simp [unit, hk]

theorem degM_cons (e : ℕ) (m : Mono) : degM (e :: m) = e + degM m := rfl

theorem monoI_cast (x : ℕ → ℤ) (D : ℝ) (hD : D ≠ 0) :
    ∀ (k : ℕ) (m : Mono),
      (monoI x k m : ℝ) = D ^ degM m * monoEvalFrom (fun i => (x i : ℝ) / D) k m
  | _, [] => by simp [monoI, monoEvalFrom, degM]
  | k, e :: m => by
      simp only [monoI, monoEvalFrom, degM_cons]
      push_cast
      rw [monoI_cast x D hD (k + 1) m, div_pow, pow_add]
      field_simp

theorem derivI_cast (x : ℕ → ℤ) (i : ℕ) (D : ℝ) (hD : D ≠ 0) :
    ∀ (k : ℕ) (m : Mono),
      (derivI x i k m : ℝ) * D = D ^ degM m * derivR (fun i => (x i : ℝ) / D) i k m
  | _, [] => by simp [derivI, derivR]
  | k, e :: m => by
      simp only [derivI, derivR, degM_cons]
      split_ifs with hk
      · push_cast
        rw [monoI_cast x D hD (k + 1) m]
        rcases e with _ | e
        · simp
        · simp only [Nat.add_sub_cancel, div_pow, pow_add, pow_succ]
          field_simp
      · push_cast
        rw [mul_assoc, derivI_cast x i D hD (k + 1) m, div_pow, pow_add]
        field_simp

theorem sumI_cast (S : IPoly) (f : Mono × ℤ → ℤ) :
    ((sumI S f : ℤ) : ℝ) = (S.map fun t => ((f t : ℤ) : ℝ)).sum := by
  induction S with
  | nil => simp [sumI]
  | cons t S ih => simp [sumI] at ih ⊢; rw [ih]

theorem sum7_cast (f : ℕ → ℤ) :
    ((sum7 f : ℤ) : ℝ) = ∑ i ∈ Finset.range 7, ((f i : ℤ) : ℝ) := by
  simp [sum7, List.range_succ, Finset.sum_range_succ]
  ring

theorem eval_toPoly (y : ℕ → ℝ) (S : IPoly) :
    eval y S.toPoly = (S.map fun t => (t.2 : ℝ) * monoEvalFrom y 0 t.1).sum := by
  induction S with
  | nil => simp [IPoly.toPoly]
  | cons t S ih =>
      simp only [IPoly.toPoly, List.map_cons, eval_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp [monoEval]

theorem absPoly_toPoly (S : IPoly) :
    absPoly S.toPoly = IPoly.toPoly (S.map fun t => (t.1, |t.2|)) := by
  simp [absPoly, IPoly.toPoly, Int.cast_abs]

theorem grad_toPoly (a : ℕ → ℝ) (S : IPoly) (i : ℕ) :
    grad a S.toPoly i = (S.map fun t => (t.2 : ℝ) * derivR a i 0 t.1).sum := by
  induction S with
  | nil => simp [grad, polyLin, IPoly.toPoly]
  | cons t S ih =>
      simp only [grad, polyLin, IPoly.toPoly, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, monoLinFrom_unit]
      simp

theorem degM_le_maxDeg (S : IPoly) (t : Mono × ℤ) (ht : t ∈ S) : degM t.1 ≤ maxDeg S := by
  induction S with
  | nil => simp at ht
  | cons u S ih =>
      simp only [maxDeg, List.map_cons, List.foldr_cons] at ih ⊢
      rcases List.mem_cons.mp ht with rfl | ht
      · exact le_max_left _ _
      · exact (ih ht).trans (le_max_right _ _)

/-- Scaling a monomial sum by `D ^ N`. -/
theorem scaled_sum (S : IPoly) (D : ℕ) (N : ℕ)
    (hN : ∀ t ∈ S, degM t.1 ≤ N) (c : Mono × ℤ → ℤ) (val : Mono → ℝ) (valI : Mono → ℤ)
    (hval : ∀ m, (valI m : ℝ) = (D : ℝ) ^ degM m * val m) :
    (D : ℝ) ^ N * (S.map fun t => ((c t : ℤ) : ℝ) * val t.1).sum =
      ((sumI S fun t => c t * valI t.1 * (D : ℤ) ^ (N - degM t.1) : ℤ) : ℝ) := by
  rw [sumI_cast]
  induction S with
  | nil => simp
  | cons t S ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih fun u hu => hN u (by simp [hu])]
      congr 1
      have hle := hN t (by simp)
      push_cast
      rw [hval, show N = degM t.1 + (N - degM t.1) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring

theorem sumI_mul_right (S : IPoly) (f : Mono × ℤ → ℤ) (d : ℤ) :
    sumI S (fun t => f t * d) = sumI S f * d := by
  induction S with
  | nil => simp [sumI]
  | cons t S ih =>
      simp only [sumI, List.map_cons, List.foldr_cons] at ih ⊢
      rw [ih]; ring

section
variable (S : IPoly) (D N : ℕ) (hD : (D : ℝ) ≠ 0) (hN : ∀ t ∈ S, degM t.1 ≤ N)
include hD hN

theorem valSum_cast (x : ℕ → ℤ) :
    (valSum S D N x : ℝ) = (D : ℝ) ^ N * eval (fun i => (x i : ℝ) / D) S.toPoly := by
  rw [eval_toPoly, scaled_sum S D N hN (fun t => t.2) _ (monoI x 0)
    (fun m => monoI_cast x D hD 0 m)]
  rfl

theorem absSum_cast (z : ℕ → ℤ) :
    (absSum S D N z : ℝ) =
      (D : ℝ) ^ N * eval (fun i => (z i : ℝ) / D) (absPoly S.toPoly) := by
  rw [absPoly_toPoly, eval_toPoly, List.map_map]
  rw [show ((fun t : Mono × ℤ => (t.2 : ℝ) * monoEvalFrom (fun i => (z i : ℝ) / D) 0 t.1) ∘
      fun t : Mono × ℤ => (t.1, |t.2|)) =
      fun t => ((|t.2| : ℤ) : ℝ) * monoEvalFrom (fun i => (z i : ℝ) / D) 0 t.1 from rfl]
  rw [scaled_sum S D N hN (fun t => |t.2|) _ (monoI z 0) (fun m => monoI_cast z D hD 0 m)]
  rfl

theorem gradSum_cast (x : ℕ → ℤ) (i : ℕ) :
    (gradSum S D N x i : ℝ) * D =
      (D : ℝ) ^ N * grad (fun i => (x i : ℝ) / D) S.toPoly i := by
  rw [grad_toPoly, scaled_sum S D N hN (fun t => t.2) _ (fun m => derivI x i 0 m * D)
    (fun m => by push_cast; exact derivI_cast x i D hD 0 m)]
  rw [show (fun t : Mono × ℤ => t.2 * (derivI x i 0 t.1 * (D : ℤ)) * (D : ℤ) ^ (N - degM t.1)) =
      fun t => t.2 * derivI x i 0 t.1 * (D : ℤ) ^ (N - degM t.1) * D from
    funext fun t => by ring, sumI_mul_right]
  push_cast
  rfl

theorem absGradSum_cast (z : ℕ → ℤ) (i : ℕ) :
    (absGradSum S D N z i : ℝ) * D =
      (D : ℝ) ^ N * grad (fun i => (z i : ℝ) / D) (absPoly S.toPoly) i := by
  rw [absPoly_toPoly, grad_toPoly, List.map_map]
  rw [show ((fun t : Mono × ℤ => (t.2 : ℝ) * derivR (fun i => (z i : ℝ) / D) i 0 t.1) ∘
      fun t : Mono × ℤ => (t.1, |t.2|)) =
      fun t => ((|t.2| : ℤ) : ℝ) * derivR (fun i => (z i : ℝ) / D) i 0 t.1 from rfl]
  rw [scaled_sum S D N hN (fun t => |t.2|) _ (fun m => derivI z i 0 m * D)
    (fun m => by push_cast; exact derivI_cast z i D hD 0 m)]
  rw [show (fun t : Mono × ℤ => |t.2| * (derivI z i 0 t.1 * (D : ℤ)) *
      (D : ℤ) ^ (N - degM t.1)) =
      fun t => |t.2| * derivI z i 0 t.1 * (D : ℤ) ^ (N - degM t.1) * D from
    funext fun t => by ring, sumI_mul_right]
  push_cast
  rfl

end

theorem length_toPoly (S : IPoly) (h : ∀ t ∈ S, t.1.length ≤ 7) :
    ∀ t ∈ S.toPoly, t.1.length ≤ 7 := by
  intro t ht
  simp only [IPoly.toPoly, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact h u hu

theorem length_absPoly (q : Poly) (h : ∀ t ∈ q, t.1.length ≤ 7) :
    ∀ t ∈ absPoly q, t.1.length ≤ 7 := by
  intro t ht
  simp only [absPoly, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact h u hu

theorem cheapI_sound (S : IPoly) (D : ℕ) (x lo hi : ℕ → ℤ) (h : cheapI S D x lo hi = true)
    (y : ℕ → ℝ)
    (hy : ∀ i, (lo i : ℝ) / D ≤ y i - x i / D ∧ y i - x i / D ≤ hi i / D) :
    0 ≤ eval y S.toPoly := by
  simp only [cheapI, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hD, hlen⟩, hcore⟩ := h
  have hN := degM_le_maxDeg S
  set N := maxDeg S
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hD0 : (D : ℝ) ≠ 0 := hDr.ne'
  have hDN : (0 : ℝ) < (D : ℝ) ^ N := pow_pos hDr N
  set q := S.toPoly
  set a : ℕ → ℝ := fun i => (x i : ℝ) / D with ha
  set hmR : ℕ → ℝ := fun i => ((max |lo i| |hi i| : ℤ) : ℝ) / D with hhm
  set hv : ℕ → ℝ := fun i => y i - a i with hhv
  have hh : ∀ i, |hv i| ≤ hmR i := by
    intro i
    obtain ⟨h1, h2⟩ := hy i
    have l1 : -((max |lo i| |hi i| : ℤ) : ℝ) ≤ lo i := by
      push_cast
      have := neg_abs_le (lo i : ℝ)
      have := le_max_left |(lo i : ℝ)| |(hi i : ℝ)|
      linarith
    have l2 : (hi i : ℝ) ≤ ((max |lo i| |hi i| : ℤ) : ℝ) := by
      push_cast
      have := le_abs_self (hi i : ℝ)
      have := le_max_right |(lo i : ℝ)| |(hi i : ℝ)|
      linarith
    have e1 := div_le_div_of_nonneg_right l1 hDr.le
    have e2 := div_le_div_of_nonneg_right l2 hDr.le
    rw [neg_div] at e1
    rw [abs_le]
    exact ⟨by simp only [hv, hmR, a]; linarith, by simp only [hv, hmR, a]; linarith⟩
  have cb := cheap_bound a hv hmR hh q
  have hy' : (fun i => a i + hv i) = y := funext fun i => by simp [hv]
  rw [hy'] at cb
  have hlenq := length_toPoly S hlen
  have hlin : ∑ i ∈ Finset.range 7,
      min (grad a q i * ((lo i : ℝ) / D)) (grad a q i * ((hi i : ℝ) / D)) ≤
        polyLin a hv q := by
    rw [polyLin_eq_grad_aux a hv 7 q hlenq]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h1, h2⟩ := hy i
    rcases le_total 0 (grad a q i) with hg | hg
    · refine (min_le_left _ _).trans ?_
      rw [mul_comm (hv i)]
      exact mul_le_mul_of_nonneg_left h1 hg
    · refine (min_le_right _ _).trans ?_
      rw [mul_comm (hv i)]
      exact mul_le_mul_of_nonpos_left h2 hg
  have hL : polyLin (fun i => |a i|) hmR (absPoly q) =
      ∑ i ∈ Finset.range 7, hmR i * grad (fun i => |a i|) (absPoly q) i :=
    polyLin_eq_grad_aux (fun i => |a i|) hmR 7 (absPoly q) (length_absPoly q hlenq)
  have hax : (fun i => ((|x i| : ℤ) : ℝ) / D) = fun i => |a i| := funext fun i => by
    simp [a, abs_div, abs_of_pos hDr]
  have hup : (fun i => ((|x i| + max |lo i| |hi i| : ℤ) : ℝ) / D) =
      fun i => |a i| + hmR i := funext fun i => by
    simp only [a, hmR]
    rw [abs_div, abs_of_pos hDr]
    push_cast
    ring
  have Ev := valSum_cast S D N hD0 hN x
  have EV := absSum_cast S D N hD0 hN (fun i => |x i|)
  have ET := absSum_cast S D N hD0 hN (fun i => |x i| + max |lo i| |hi i|)
  rw [hax] at EV
  rw [hup] at ET
  have S1 : ∑ i ∈ Finset.range 7,
      ((min (gradSum S D N x i * lo i) (gradSum S D N x i * hi i) : ℤ) : ℝ) =
        (D : ℝ) ^ N * ∑ i ∈ Finset.range 7,
          min (grad a q i * ((lo i : ℝ) / D)) (grad a q i * ((hi i : ℝ) / D)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : grad a q i = (gradSum S D N x i : ℝ) * D / (D : ℝ) ^ N := by
      rw [gradSum_cast S D N hD0 hN x i]
      field_simp
      rfl
    rw [mul_min_of_nonneg _ _ hDN.le, hg]
    push_cast
    congr 1 <;> field_simp
  have S2 : ∑ i ∈ Finset.range 7,
      ((max |lo i| |hi i| * absGradSum S D N (fun i => |x i|) i : ℤ) : ℝ) =
        (D : ℝ) ^ N * ∑ i ∈ Finset.range 7, hmR i * grad (fun i => |a i|) (absPoly q) i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hG := absGradSum_cast S D N hD0 hN (fun i => |x i|) i
    rw [hax] at hG
    have hg : grad (fun i => |a i|) (absPoly q) i =
        (absGradSum S D N (fun i => |x i|) i : ℝ) * D / (D : ℝ) ^ N := by
      rw [hG]
      field_simp
      rfl
    rw [hg]
    simp only [hmR]
    push_cast
    field_simp
  simp only [cheapCore, decide_eq_true_eq] at hcore
  have hc : (0 : ℝ) ≤ _ := Int.cast_nonneg hcore
  simp only [Int.cast_add, Int.cast_sub, sum7_cast] at hc
  rw [Ev, EV, ET, S1, S2] at hc
  have hpos : 0 ≤ eval a q + ∑ i ∈ Finset.range 7,
      min (grad a q i * ((lo i : ℝ) / D)) (grad a q i * ((hi i : ℝ) / D)) -
      (eval (fun i => |a i| + hmR i) (absPoly q) - eval (fun i => |a i|) (absPoly q) -
        ∑ i ∈ Finset.range 7, hmR i * grad (fun i => |a i|) (absPoly q) i) := by
    have : 0 ≤ (D : ℝ) ^ N * (eval a q + ∑ i ∈ Finset.range 7,
        min (grad a q i * ((lo i : ℝ) / D)) (grad a q i * ((hi i : ℝ) / D)) -
        (eval (fun i => |a i| + hmR i) (absPoly q) - eval (fun i => |a i|) (absPoly q) -
          ∑ i ∈ Finset.range 7, hmR i * grad (fun i => |a i|) (absPoly q) i)) := by
      linarith
    exact (mul_nonneg_iff_of_pos_left hDN).mp this
  rw [hL] at cb
  linarith

end Noperts.Stellated.CornerKernel
