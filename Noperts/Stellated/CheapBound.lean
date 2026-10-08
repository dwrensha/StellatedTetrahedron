module

public import Noperts.Stellated.SparsePoly

@[expose] public section

/-!
# A cheap lower bound for a polynomial on a box

For a polynomial `q`, an anchor `a` and a displacement `h` with
`|hᵢ| ≤ hmᵢ`, write `q(a + h) = v + l + r` with `v = q(a)`, `l` linear in `h`
and `r` the higher-order remainder.  Then `|r|` is at most the same remainder
of `|q|` (absolute-value coefficients) at `|a|` and `hm`, so

  `q(a + h) ≥ q(a) + l - (|q|(|a| + hm) - |q|(|a|) - L)`

with `L` the linear part of `|q|` at `|a|` in direction `hm`.  No substitution
or expansion is needed: a handful of polynomial evaluations suffice.

The proof is a small "majorant algebra": `Maj v l t V L T` says the value,
linear part and remainder `t - v - l` of a quantity are dominated by those of
a majorant; it is preserved by products, scalar multiples and sums.
-/

namespace Noperts.Stellated.CheapBound

open SparsePoly

/-- `v, l, t` (value, linear part, total) are dominated by `V, L, T`:
`|v| ≤ V`, `|l| ≤ L` and `|t - v - l| ≤ T - V - L`. -/
structure Maj (v l t V L T : ℝ) : Prop where
  hv : |v| ≤ V
  hl : |l| ≤ L
  hr : |t - v - l| ≤ T - V - L

theorem Maj.mul {v₁ l₁ t₁ V₁ L₁ T₁ v₂ l₂ t₂ V₂ L₂ T₂ : ℝ}
    (h₁ : Maj v₁ l₁ t₁ V₁ L₁ T₁) (h₂ : Maj v₂ l₂ t₂ V₂ L₂ T₂) :
    Maj (v₁ * v₂) (v₁ * l₂ + l₁ * v₂) (t₁ * t₂) (V₁ * V₂) (V₁ * L₂ + L₁ * V₂) (T₁ * T₂) := by
  obtain ⟨hv₁, hl₁, hr₁⟩ := h₁
  obtain ⟨hv₂, hl₂, hr₂⟩ := h₂
  set r₁ := t₁ - v₁ - l₁ with hr₁def
  set r₂ := t₂ - v₂ - l₂ with hr₂def
  set R₁ := T₁ - V₁ - L₁ with hR₁def
  set R₂ := T₂ - V₂ - L₂ with hR₂def
  have V₁0 : 0 ≤ V₁ := (abs_nonneg _).trans hv₁
  have V₂0 : 0 ≤ V₂ := (abs_nonneg _).trans hv₂
  have L₁0 : 0 ≤ L₁ := (abs_nonneg _).trans hl₁
  have L₂0 : 0 ≤ L₂ := (abs_nonneg _).trans hl₂
  have R₁0 : 0 ≤ R₁ := (abs_nonneg _).trans hr₁
  have R₂0 : 0 ≤ R₂ := (abs_nonneg _).trans hr₂
  have m : ∀ {x y X Y : ℝ}, |x| ≤ X → |y| ≤ Y → |x * y| ≤ X * Y := fun hx hy => by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  refine ⟨m hv₁ hv₂, ?_, ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (m hv₁ hl₂) (m hl₁ hv₂))
  · have ht : t₁ * t₂ - v₁ * v₂ - (v₁ * l₂ + l₁ * v₂) =
        v₁ * r₂ + l₁ * l₂ + l₁ * r₂ + r₁ * v₂ + r₁ * l₂ + r₁ * r₂ := by
      rw [hr₁def, hr₂def]; ring
    have hT : T₁ * T₂ - V₁ * V₂ - (V₁ * L₂ + L₁ * V₂) =
        V₁ * R₂ + L₁ * L₂ + L₁ * R₂ + R₁ * V₂ + R₁ * L₂ + R₁ * R₂ := by
      rw [hR₁def, hR₂def]; ring
    rw [ht, hT]
    calc |v₁ * r₂ + l₁ * l₂ + l₁ * r₂ + r₁ * v₂ + r₁ * l₂ + r₁ * r₂|
        ≤ |v₁ * r₂| + |l₁ * l₂| + |l₁ * r₂| + |r₁ * v₂| + |r₁ * l₂| + |r₁ * r₂| := by
          have a1 := abs_add_le (v₁ * r₂ + l₁ * l₂ + l₁ * r₂ + r₁ * v₂ + r₁ * l₂) (r₁ * r₂)
          have a2 := abs_add_le (v₁ * r₂ + l₁ * l₂ + l₁ * r₂ + r₁ * v₂) (r₁ * l₂)
          have a3 := abs_add_le (v₁ * r₂ + l₁ * l₂ + l₁ * r₂) (r₁ * v₂)
          have a4 := abs_add_le (v₁ * r₂ + l₁ * l₂) (l₁ * r₂)
          have a5 := abs_add_le (v₁ * r₂) (l₁ * l₂)
          linarith
      _ ≤ _ := by
          gcongr
          · exact m hv₁ hr₂
          · exact m hl₁ hl₂
          · exact m hl₁ hr₂
          · exact m hr₁ hv₂
          · exact m hr₁ hl₂
          · exact m hr₁ hr₂

theorem Maj.smul {v l t V L T : ℝ} (h : Maj v l t V L T) (c : ℝ) :
    Maj (c * v) (c * l) (c * t) (|c| * V) (|c| * L) (|c| * T) := by
  obtain ⟨hv, hl, hr⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hv (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hl (abs_nonneg _)
  · have e1 : c * t - c * v - c * l = c * (t - v - l) := by ring
    have e2 : |c| * T - |c| * V - |c| * L = |c| * (T - V - L) := by ring
    rw [e1, e2, abs_mul]; exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)

theorem Maj.add {v₁ l₁ t₁ V₁ L₁ T₁ v₂ l₂ t₂ V₂ L₂ T₂ : ℝ}
    (h₁ : Maj v₁ l₁ t₁ V₁ L₁ T₁) (h₂ : Maj v₂ l₂ t₂ V₂ L₂ T₂) :
    Maj (v₁ + v₂) (l₁ + l₂) (t₁ + t₂) (V₁ + V₂) (L₁ + L₂) (T₁ + T₂) := by
  obtain ⟨hv₁, hl₁, hr₁⟩ := h₁
  obtain ⟨hv₂, hl₂, hr₂⟩ := h₂
  refine ⟨(abs_add_le _ _).trans (add_le_add hv₁ hv₂), (abs_add_le _ _).trans
    (add_le_add hl₁ hl₂), ?_⟩
  have e1 : t₁ + t₂ - (v₁ + v₂) - (l₁ + l₂) = (t₁ - v₁ - l₁) + (t₂ - v₂ - l₂) := by ring
  have e2 : T₁ + T₂ - (V₁ + V₂) - (L₁ + L₂) = (T₁ - V₁ - L₁) + (T₂ - V₂ - L₂) := by ring
  rw [e1, e2]
  exact (abs_add_le _ _).trans (add_le_add hr₁ hr₂)

theorem Maj.one : Maj 1 0 1 1 0 1 := ⟨by simp, by simp, by simp⟩

theorem Maj.zero : Maj 0 0 0 0 0 0 := ⟨by simp, by simp, by simp⟩

theorem Maj.var (a h hm : ℝ) (hh : |h| ≤ hm) : Maj a h (a + h) |a| hm (|a| + hm) :=
  ⟨le_rfl, hh, by simp⟩

/-! ## Monomials and polynomials -/

/-- The linear part of `x ↦ x ^ e` at `a` in direction `h`. -/
def powLin (a h : ℝ) : ℕ → ℝ
  | 0 => 0
  | e + 1 => a ^ e * h + powLin a h e * a

theorem Maj.pow (a h hm : ℝ) (hh : |h| ≤ hm) :
    ∀ e : ℕ, Maj (a ^ e) (powLin a h e) ((a + h) ^ e) (|a| ^ e) (powLin |a| hm e)
      ((|a| + hm) ^ e)
  | 0 => by simpa [powLin] using Maj.one
  | e + 1 => by
      have := (Maj.pow a h hm hh e).mul (Maj.var a h hm hh)
      simpa [powLin, pow_succ, mul_comm, add_comm] using this

/-- The linear part of `∏ᵢ x (k + i) ^ mᵢ` at `a` in direction `h`. -/
def monoLinFrom (a h : ℕ → ℝ) : ℕ → Mono → ℝ
  | _, [] => 0
  | k, e :: m => a k ^ e * monoLinFrom a h (k + 1) m +
      powLin (a k) (h k) e * monoEvalFrom a (k + 1) m

theorem Maj.mono (a h hm : ℕ → ℝ) (hh : ∀ i, |h i| ≤ hm i) :
    ∀ (k : ℕ) (m : Mono), Maj (monoEvalFrom a k m) (monoLinFrom a h k m)
      (monoEvalFrom (fun i => a i + h i) k m) (monoEvalFrom (fun i => |a i|) k m)
      (monoLinFrom (fun i => |a i|) hm k m)
      (monoEvalFrom (fun i => |a i| + hm i) k m)
  | k, [] => by simpa [monoEvalFrom, monoLinFrom] using Maj.one
  | k, e :: m => by
      have := (Maj.pow (a k) (h k) (hm k) (hh k) e).mul (Maj.mono a h hm hh (k + 1) m)
      simpa [monoEvalFrom, monoLinFrom] using this

/-- The linear part of `q` at `a` in direction `h`. -/
def polyLin (a h : ℕ → ℝ) (q : Poly) : ℝ :=
  (q.map fun t => (t.2 : ℝ) * monoLinFrom a h 0 t.1).sum

/-- `|q|`: the polynomial with absolute-value coefficients. -/
def absPoly (q : Poly) : Poly := q.map fun t => (t.1, |t.2|)

theorem Maj.poly (a h hm : ℕ → ℝ) (hh : ∀ i, |h i| ≤ hm i) :
    ∀ q : Poly, Maj (eval a q) (polyLin a h q) (eval (fun i => a i + h i) q)
      (eval (fun i => |a i|) (absPoly q)) (polyLin (fun i => |a i|) hm (absPoly q))
      (eval (fun i => |a i| + hm i) (absPoly q))
  | [] => by simpa [polyLin, absPoly] using Maj.zero
  | t :: q => by
      have ht := (Maj.mono a h hm hh 0 t.1).smul (t.2 : ℝ)
      have := ht.add (Maj.poly a h hm hh q)
      simpa [polyLin, absPoly, monoEval, Rat.cast_abs] using this

/-- The cheap lower bound. -/
theorem cheap_bound (a h hm : ℕ → ℝ) (hh : ∀ i, |h i| ≤ hm i) (q : Poly) :
    eval a q + polyLin a h q -
        (eval (fun i => |a i| + hm i) (absPoly q) - eval (fun i => |a i|) (absPoly q) -
          polyLin (fun i => |a i|) hm (absPoly q)) ≤
      eval (fun i => a i + h i) q := by
  have := (Maj.poly a h hm hh q).hr
  have := neg_abs_le (eval (fun i => a i + h i) q - eval a q - polyLin a h q)
  linarith

/-! ## The linear part as a gradient -/

theorem powLin_linear (a : ℝ) (h : ℝ) : ∀ e, powLin a h e = h * powLin a 1 e
  | 0 => by simp [powLin]
  | e + 1 => by simp only [powLin, powLin_linear a h e]; ring

/-- The linear part only reads `h` on the monomial's own coordinates. -/
theorem monoLinFrom_congr (a h h' : ℕ → ℝ) :
    ∀ (k : ℕ) (m : Mono), (∀ j, j < m.length → h (k + j) = h' (k + j)) →
      monoLinFrom a h k m = monoLinFrom a h' k m
  | k, [], _ => rfl
  | k, e :: m, hh => by
      simp only [monoLinFrom]
      have h0 := hh 0 (by simp)
      simp only [add_zero] at h0
      rw [h0, monoLinFrom_congr a h h' (k + 1) m fun j hj => by
        have := hh (j + 1) (by simp; omega)
        rwa [show k + (j + 1) = k + 1 + j by omega] at this]

/-- `h ↦ monoLinFrom a h k m` is additive and homogeneous. -/
theorem monoLinFrom_add (a h₁ h₂ : ℕ → ℝ) :
    ∀ (k : ℕ) (m : Mono), monoLinFrom a (fun i => h₁ i + h₂ i) k m =
      monoLinFrom a h₁ k m + monoLinFrom a h₂ k m
  | k, [] => by simp [monoLinFrom]
  | k, e :: m => by
      simp only [monoLinFrom, monoLinFrom_add a h₁ h₂ (k + 1) m]
      rw [powLin_linear _ (h₁ k + h₂ k), powLin_linear _ (h₁ k), powLin_linear _ (h₂ k)]
      ring

theorem monoLinFrom_smul (a h : ℕ → ℝ) (c : ℝ) :
    ∀ (k : ℕ) (m : Mono), monoLinFrom a (fun i => c * h i) k m = c * monoLinFrom a h k m
  | k, [] => by simp [monoLinFrom]
  | k, e :: m => by
      simp only [monoLinFrom, monoLinFrom_smul a h c (k + 1) m]
      rw [powLin_linear _ (c * h k), powLin_linear _ (h k)]
      ring

theorem monoLinFrom_zero (a : ℕ → ℝ) :
    ∀ (k : ℕ) (m : Mono), monoLinFrom a (fun _ => 0) k m = 0
  | k, [] => rfl
  | k, e :: m => by
      simp only [monoLinFrom, monoLinFrom_zero a (k + 1) m]
      rw [powLin_linear _ 0]; ring

/-- The unit displacement in coordinate `i`. -/
def unit (i : ℕ) : ℕ → ℝ := fun j => if j = i then 1 else 0

theorem monoLinFrom_sum (a h : ℕ → ℝ) (k : ℕ) (m : Mono) (s : Finset ℕ)
    (hs : ∀ j, j < m.length → k + j ∈ s) :
    monoLinFrom a h k m = ∑ i ∈ s, h i * monoLinFrom a (unit i) k m := by
  have hrep : monoLinFrom a h k m = monoLinFrom a (fun j => ∑ i ∈ s, h i * unit i j) k m :=
    monoLinFrom_congr a _ _ k m fun j hj => by
      simp [unit, hs j hj]
  rw [hrep]
  clear hrep hs
  induction s using Finset.induction_on with
  | empty => simpa using monoLinFrom_zero a k m
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [monoLinFrom_add a (fun j => h i * unit i j), monoLinFrom_smul, ih]

/-- The gradient component of `q` at `a` in coordinate `i`. -/
def grad (a : ℕ → ℝ) (q : Poly) (i : ℕ) : ℝ := polyLin a (unit i) q

/-- Number of coordinates `q` mentions. -/
def nvars (q : Poly) : ℕ := (q.map fun t => t.1.length).foldr max 0

theorem length_le_nvars (q : Poly) (t : Mono × ℚ) (ht : t ∈ q) : t.1.length ≤ nvars q := by
  induction q with
  | nil => simp at ht
  | cons u q ih =>
      simp only [nvars, List.map_cons, List.foldr_cons] at ih ⊢
      rcases List.mem_cons.mp ht with rfl | ht
      · exact le_max_left _ _
      · exact (ih ht).trans (le_max_right _ _)

theorem polyLin_eq_grad_aux (a h : ℕ → ℝ) (n : ℕ) :
    ∀ q : Poly, (∀ t ∈ q, t.1.length ≤ n) →
      polyLin a h q = ∑ i ∈ Finset.range n, h i * polyLin a (unit i) q
  | [], _ => by simp [polyLin]
  | t :: q, hq => by
      have ht := monoLinFrom_sum a h 0 t.1 (Finset.range n) fun j hj => by
        simpa using lt_of_lt_of_le hj (hq t (by simp))
      have ih := polyLin_eq_grad_aux a h n q fun u hu => hq u (by simp [hu])
      simp only [polyLin, List.map_cons, List.sum_cons] at ih ⊢
      rw [ht, ih, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem polyLin_eq_grad (a h : ℕ → ℝ) (q : Poly) :
    polyLin a h q = ∑ i ∈ Finset.range (nvars q), h i * grad a q i :=
  polyLin_eq_grad_aux a h _ q fun t ht => length_le_nvars q t ht

/-- The linear part over a box `lo ≤ h ≤ hi` is at least `Σ min(gᵢ loᵢ, gᵢ hiᵢ)`. -/
theorem polyLin_ge (a h lo hi : ℕ → ℝ) (hlo : ∀ i, lo i ≤ h i) (hhi : ∀ i, h i ≤ hi i)
    (q : Poly) :
    ∑ i ∈ Finset.range (nvars q), min (grad a q i * lo i) (grad a q i * hi i) ≤
      polyLin a h q := by
  rw [polyLin_eq_grad]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_total 0 (grad a q i) with hg | hg
  · exact (min_le_left _ _).trans (by rw [mul_comm (h i)]; exact mul_le_mul_of_nonneg_left (hlo i) hg)
  · exact (min_le_right _ _).trans (by rw [mul_comm (h i)]; exact mul_le_mul_of_nonpos_left (hhi i) hg)

end Noperts.Stellated.CheapBound
