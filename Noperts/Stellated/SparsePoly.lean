module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact sparse multivariate polynomials with rational coefficients

A polynomial is a list of terms `(exponents, coefficient)`; exponent lists are
indexed from variable `0` and may be shorter than the number of variables
(missing exponents are zero).  Everything is computable and every operation
comes with an evaluation lemma into `ℝ`.  Two sound lower bounds over boxes
are provided: the centered bound (expand around the box center, then
`const - Σ |coeff|`) and the corner bound (expand from a box corner over
`[0,1]ⁿ`, then `const + Σ negative coeffs`).
-/

namespace Noperts.Stellated.SparsePoly

abbrev Mono := List ℕ
abbrev Poly := List (Mono × ℚ)

/-- `∏ᵢ x (k + i) ^ mᵢ`. -/
def monoEvalFrom (x : ℕ → ℝ) : ℕ → Mono → ℝ
  | _, [] => 1
  | k, e :: m => x k ^ e * monoEvalFrom x (k + 1) m

noncomputable def monoEval (x : ℕ → ℝ) (m : Mono) : ℝ := monoEvalFrom x 0 m

noncomputable def eval (x : ℕ → ℝ) (p : Poly) : ℝ :=
  (p.map fun t => (t.2 : ℝ) * monoEval x t.1).sum

@[simp] theorem eval_nil (x : ℕ → ℝ) : eval x [] = 0 := rfl

@[simp] theorem eval_cons (x : ℕ → ℝ) (t : Mono × ℚ) (p : Poly) :
    eval x (t :: p) = (t.2 : ℝ) * monoEval x t.1 + eval x p := by
  simp [eval]

theorem eval_append (x : ℕ → ℝ) (p q : Poly) :
    eval x (p ++ q) = eval x p + eval x q := by
  simp [eval]

/-! ## Arithmetic -/

def add (p q : Poly) : Poly := p ++ q

theorem eval_add (x : ℕ → ℝ) (p q : Poly) :
    eval x (add p q) = eval x p + eval x q := eval_append x p q

def scale (c : ℚ) (p : Poly) : Poly := p.map fun t => (t.1, c * t.2)

theorem eval_scale (x : ℕ → ℝ) (c : ℚ) (p : Poly) :
    eval x (scale c p) = c * eval x p := by
  induction p with
  | nil => simp [scale]
  | cons t p ih =>
      simp only [scale, List.map_cons, eval_cons] at ih ⊢
      rw [ih]; push_cast; ring

def monoMul : Mono → Mono → Mono
  | [], m => m
  | m, [] => m
  | a :: m, b :: m' => (a + b) :: monoMul m m'

theorem monoEvalFrom_mul (x : ℕ → ℝ) :
    ∀ (k : ℕ) (m m' : Mono),
      monoEvalFrom x k (monoMul m m') =
        monoEvalFrom x k m * monoEvalFrom x k m'
  | k, [], m' => by simp [monoMul, monoEvalFrom]
  | k, a :: m, [] => by simp [monoMul, monoEvalFrom]
  | k, a :: m, b :: m' => by
      simp only [monoMul, monoEvalFrom, monoEvalFrom_mul x (k + 1) m m', pow_add]
      ring

theorem monoEval_mul (x : ℕ → ℝ) (m m' : Mono) :
    monoEval x (monoMul m m') = monoEval x m * monoEval x m' :=
  monoEvalFrom_mul x 0 m m'

def mulTerm (t : Mono × ℚ) (q : Poly) : Poly :=
  q.map fun s => (monoMul t.1 s.1, t.2 * s.2)

theorem eval_mulTerm (x : ℕ → ℝ) (t : Mono × ℚ) (q : Poly) :
    eval x (mulTerm t q) = t.2 * monoEval x t.1 * eval x q := by
  induction q with
  | nil => simp [mulTerm]
  | cons s q ih =>
      simp only [mulTerm, List.map_cons, eval_cons] at ih ⊢
      rw [ih, monoEval_mul]; push_cast; ring

def mul (p q : Poly) : Poly := p.flatMap fun t => mulTerm t q

theorem eval_mul (x : ℕ → ℝ) (p q : Poly) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
      simp only [mul, List.flatMap_cons, eval_append, eval_cons] at ih ⊢
      rw [eval_mulTerm, ih]; ring

def const (c : ℚ) : Poly := [([], c)]

@[simp] theorem eval_const (x : ℕ → ℝ) (c : ℚ) : eval x (const c) = c := by
  simp [const, monoEval, monoEvalFrom]

/-- The monomial `x_i`. -/
def varMono : ℕ → Mono
  | 0 => [1]
  | i + 1 => 0 :: varMono i

theorem monoEvalFrom_varMono (x : ℕ → ℝ) :
    ∀ (i k : ℕ), monoEvalFrom x k (varMono i) = x (k + i)
  | 0, k => by simp [varMono, monoEvalFrom]
  | i + 1, k => by
      simp only [varMono, monoEvalFrom, pow_zero, one_mul]
      rw [monoEvalFrom_varMono x i (k + 1)]
      congr 1; omega

theorem monoEval_varMono (x : ℕ → ℝ) (i : ℕ) : monoEval x (varMono i) = x i := by
  simp [monoEval, monoEvalFrom_varMono]

def var (i : ℕ) : Poly := [(varMono i, 1)]

@[simp] theorem eval_var (x : ℕ → ℝ) (i : ℕ) : eval x (var i) = x i := by
  simp [var, monoEval, monoEvalFrom_varMono]

def pow (p : Poly) : ℕ → Poly
  | 0 => const 1
  | k + 1 => mul (pow p k) p

theorem eval_pow (x : ℕ → ℝ) (p : Poly) (k : ℕ) :
    eval x (pow p k) = eval x p ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, eval_mul, ih, pow_succ]

/-! ## Normalization (merging equal monomials) -/

/-- `trim` for compiled code. -/
def trimNative (m : Mono) : Mono := (m.reverse.dropWhile (· == 0)).reverse

/-- Drop trailing zero exponents so equal monomials have equal lists (one pass by
`List.rec`, for the kernel). -/
@[implemented_by trimNative]
def trim (m : Mono) : Mono :=
  @List.rec ℕ (fun _ => Mono) [] (fun a _ r => cond (Nat.beq a 0 && r.isEmpty) [] (a :: r)) m

theorem monoEvalFrom_append_zero (x : ℕ → ℝ) :
    ∀ (k : ℕ) (m : Mono), monoEvalFrom x k (m ++ [0]) = monoEvalFrom x k m
  | k, [] => by simp [monoEvalFrom]
  | k, a :: m => by simp [monoEvalFrom, monoEvalFrom_append_zero x (k + 1) m]

theorem monoEvalFrom_append_zeros (x : ℕ → ℝ) (k : ℕ) (m : Mono) :
    ∀ n : ℕ, monoEvalFrom x k (m ++ List.replicate n 0) = monoEvalFrom x k m
  | 0 => by simp
  | n + 1 => by
      rw [List.replicate_succ', ← List.append_assoc,
        monoEvalFrom_append_zero, monoEvalFrom_append_zeros x k m n]

theorem trim_cons (a : ℕ) (m : Mono) :
    trim (a :: m) = cond (Nat.beq a 0 && (trim m).isEmpty) [] (a :: trim m) := rfl

theorem trim_spec (m : Mono) :
    ∃ n, m = trim m ++ List.replicate n 0 := by
  induction m with
  | nil => exact ⟨0, rfl⟩
  | cons a m ih =>
      obtain ⟨k, hk⟩ := ih
      rw [trim_cons]
      cases ha : Nat.beq a 0 <;> cases hr : (trim m).isEmpty
      · exact ⟨k, by simp only [Bool.false_and, Bool.cond_false, List.cons_append]; rw [← hk]⟩
      · exact ⟨k, by simp only [Bool.false_and, Bool.cond_false, List.cons_append]; rw [← hk]⟩
      · exact ⟨k, by simp only [Bool.true_and, Bool.cond_false, List.cons_append]; rw [← hk]⟩
      · have h0 : a = 0 := Nat.eq_of_beq_eq_true ha
        have he : trim m = [] := List.isEmpty_iff.mp hr
        refine ⟨k + 1, ?_⟩
        simp only [Bool.and_self, Bool.cond_true, List.nil_append, List.replicate_succ, h0]
        rw [hk, he]; simp

theorem monoEval_trim (x : ℕ → ℝ) (m : Mono) :
    monoEval x (trim m) = monoEval x m := by
  obtain ⟨n, hn⟩ := trim_spec m
  unfold monoEval
  conv_rhs => rw [hn]
  rw [monoEvalFrom_append_zeros]

/-- Insert a term, merging with an existing equal (trimmed) monomial. -/
def insertTerm (t : Mono × ℚ) : Poly → Poly
  | [] => [t]
  | s :: p => if s.1 = t.1 then (s.1, s.2 + t.2) :: p else s :: insertTerm t p

theorem eval_insertTerm (x : ℕ → ℝ) (t : Mono × ℚ) :
    ∀ p : Poly, eval x (insertTerm t p) = eval x (t :: p)
  | [] => rfl
  | s :: p => by
      unfold insertTerm
      split_ifs with h
      · simp only [eval_cons, h]; push_cast; ring
      · rw [eval_cons, eval_insertTerm x t p, eval_cons, eval_cons, eval_cons]
        ring

/-- Lexicographic order on monomials (a total order, so equal monomials end
up adjacent after sorting). -/
def monoLeLexNative : Mono → Mono → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: m, b :: n => a < b || (a == b && monoLeLexNative m n)

@[implemented_by monoLeLexNative]
def monoLeLex (m n : Mono) : Bool :=
  @List.rec ℕ (fun _ => Mono → Bool) (fun _ => true)
    (fun a _ ih n => List.casesOn (motive := fun _ => Bool) n false
      (fun b n' => cond (Nat.blt a b) true (cond (Nat.beq a b) (ih n') false))) m n

def monoEqNative (m n : Mono) : Bool := m == n

/-- Equality of monomials (by `List.rec` and `Nat.beq`, for the kernel). -/
@[implemented_by monoEqNative]
def monoEq (m n : Mono) : Bool :=
  @List.rec ℕ (fun _ => Mono → Bool) (fun n => n.isEmpty)
    (fun a _ ih n => List.casesOn (motive := fun _ => Bool) n false
      (fun b n' => cond (Nat.beq a b) (ih n') false)) m n

theorem monoEq_sound : ∀ (m n : Mono), monoEq m n = true → m = n
  | [], n, h => (List.isEmpty_iff.mp h).symm
  | a :: m, [], h => by simp [monoEq] at h
  | a :: m, b :: n, h => by
      have h' : cond (Nat.beq a b) (monoEq m n) false = true := h
      cases hab : Nat.beq a b
      · rw [hab] at h'; simp at h'
      · rw [hab, Bool.cond_true] at h'
        rw [Nat.eq_of_beq_eq_true hab, monoEq_sound m n h']

/-- Merge adjacent terms with equal monomials. -/
def mergeAdj : Poly → Poly
  | [] => []
  | t :: p =>
      match mergeAdj p with
      | s :: q => cond (monoEq s.1 t.1) ((t.1, t.2 + s.2) :: q) (t :: s :: q)
      | [] => [t]

/-- Merge two term lists by `monoLeLex`, recursing on `fuel` (structural, so
kernel reduction stays cheap; `List.mergeSort` uses well-founded recursion,
which the kernel unfolds very poorly). -/
def mergeF : ℕ → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | fuel + 1, s :: p, t :: q =>
      cond (monoLeLex s.1 t.1) (s :: mergeF fuel p (t :: q)) (t :: mergeF fuel (s :: p) q)

/-- Split a list into alternate elements. -/
def halves : Poly → Poly × Poly
  | [] => ([], [])
  | [t] => ([t], [])
  | s :: t :: p => let h := halves p; (s :: h.1, t :: h.2)

/-- Merge sort with `fuel` levels of recursion. -/
def msortF : ℕ → Poly → Poly
  | 0, p => p
  | fuel + 1, p =>
      match p with
      | [] => []
      | [t] => [t]
      | _ => let h := halves p
             mergeF (2 * p.length) (msortF fuel h.1) (msortF fuel h.2)

/-- Merge equal monomials and drop zero coefficients: trim, sort, merge
neighbours (`O(n log n)`; the insertion merge it replaces was quadratic and
dominated the corner checker). -/
def normalize (p : Poly) : Poly :=
  (mergeAdj (msortF p.length (p.map fun t => (trim t.1, t.2)))).filter (fun t => t.2 ≠ 0)

theorem eval_filter_nonzero (x : ℕ → ℝ) :
    ∀ p : Poly, eval x (p.filter fun t => t.2 ≠ 0) = eval x p
  | [] => rfl
  | t :: p => by
      have ih := eval_filter_nonzero x p
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simp [h]), ih, eval_cons, h]
        simp
      · rw [List.filter_cons_of_pos (by simp [h]), eval_cons, eval_cons, ih]

theorem eval_mergeAdj (x : ℕ → ℝ) : ∀ p : Poly, eval x (mergeAdj p) = eval x p
  | [] => rfl
  | t :: p => by
      have ih := eval_mergeAdj x p
      unfold mergeAdj
      split
      · rename_i s q hq
        rw [hq] at ih
        cases hm : monoEq s.1 t.1
        · simp only [Bool.cond_false, eval_cons] at ih ⊢
          rw [← ih]
        · have h := monoEq_sound _ _ hm
          simp only [Bool.cond_true, eval_cons] at ih ⊢
          rw [← ih, h]; push_cast; ring
      · rename_i hq
        rw [hq] at ih
        simp only [eval_cons] at ih ⊢
        rw [← ih]

theorem eval_perm (x : ℕ → ℝ) {p q : Poly} (h : p.Perm q) : eval x p = eval x q := by
  induction h with
  | nil => rfl
  | cons t _ ih => simp only [eval_cons, ih]
  | swap s t p => simp only [eval_cons]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem eval_trimTerms (x : ℕ → ℝ) :
    ∀ p : Poly, eval x (p.map fun t => (trim t.1, t.2)) = eval x p
  | [] => rfl
  | t :: p => by
      simp only [List.map_cons, eval_cons, monoEval_trim, eval_trimTerms x p]

theorem eval_mergeF (x : ℕ → ℝ) :
    ∀ (fuel : ℕ) (p q : Poly), eval x (mergeF fuel p q) = eval x p + eval x q
  | 0, p, q => eval_append x p q
  | _ + 1, [], q => by simp [mergeF, eval]
  | _ + 1, s :: p, [] => by simp [mergeF, eval]
  | fuel + 1, s :: p, t :: q => by
      unfold mergeF
      cases monoLeLex s.1 t.1
      · rw [Bool.cond_false, eval_cons, eval_mergeF x fuel (s :: p) q, eval_cons, eval_cons]; ring
      · rw [Bool.cond_true, eval_cons, eval_mergeF x fuel p (t :: q), eval_cons, eval_cons]; ring

theorem eval_halves (x : ℕ → ℝ) :
    ∀ p : Poly, eval x (halves p).1 + eval x (halves p).2 = eval x p
  | [] => by simp [halves, eval]
  | [t] => by simp [halves, eval]
  | s :: t :: p => by
      have ih := eval_halves x p
      simp only [halves, eval_cons]
      linarith

theorem eval_msortF (x : ℕ → ℝ) : ∀ (fuel : ℕ) (p : Poly), eval x (msortF fuel p) = eval x p
  | 0, p => rfl
  | fuel + 1, [] => rfl
  | fuel + 1, [t] => rfl
  | fuel + 1, s :: t :: p => by
      simp only [msortF]
      rw [eval_mergeF, eval_msortF x fuel, eval_msortF x fuel, eval_halves]

theorem eval_normalize (x : ℕ → ℝ) (p : Poly) :
    eval x (normalize p) = eval x p := by
  unfold normalize
  rw [eval_filter_nonzero, eval_mergeAdj, eval_msortF, eval_trimTerms]

/-- `p ^ k`, merging like terms after every multiplication.  Plain `pow`
keeps all `nᵏ` products of an `n`-term polynomial (15625 terms for a 5-term
affine form to the 6th), which made substitutions quadratic in that count. -/
def npow (p : Poly) : ℕ → Poly
  | 0 => const 1
  | k + 1 => normalize (mul (npow p k) p)

theorem eval_npow (x : ℕ → ℝ) (p : Poly) (k : ℕ) :
    eval x (npow p k) = eval x p ^ k := by
  induction k with
  | zero => simp [npow]
  | succ k ih => simp [npow, eval_normalize, eval_mul, ih, pow_succ]

/-! ## Affine substitution `xᵢ ↦ cᵢ + rᵢ yᵢ` -/

def affineVar (c r : ℕ → ℚ) (i : ℕ) : Poly :=
  add (const (c i)) (scale (r i) (var i))

theorem eval_affineVar (y : ℕ → ℝ) (c r : ℕ → ℚ) (i : ℕ) :
    eval y (affineVar c r i) = c i + r i * y i := by
  simp [affineVar, eval_add, eval_scale]

def substMonoFrom (c r : ℕ → ℚ) : ℕ → Mono → Poly
  | _, [] => const 1
  | k, e :: m => normalize (mul (npow (affineVar c r k) e) (substMonoFrom c r (k + 1) m))

theorem eval_substMonoFrom (y : ℕ → ℝ) (c r : ℕ → ℚ) :
    ∀ (k : ℕ) (m : Mono), eval y (substMonoFrom c r k m) =
      monoEvalFrom (fun i => c i + r i * y i) k m
  | k, [] => by simp [substMonoFrom, monoEvalFrom]
  | k, e :: m => by
      simp only [substMonoFrom, eval_normalize, eval_mul, eval_npow,
        eval_affineVar, eval_substMonoFrom y c r (k + 1) m, monoEvalFrom]

def subst (c r : ℕ → ℚ) (p : Poly) : Poly :=
  normalize (p.flatMap fun t => scale t.2 (substMonoFrom c r 0 t.1))

theorem eval_subst (y : ℕ → ℝ) (c r : ℕ → ℚ) (p : Poly) :
    eval y (subst c r p) = eval (fun i => c i + r i * y i) p := by
  unfold subst
  rw [eval_normalize]
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [List.flatMap_cons, eval_append, eval_scale, ih, eval_cons,
        eval_substMonoFrom, monoEval]

/-! ## Translation `xᵢ ↦ sᵢ + yᵢ` -/

/-- `sᵢ + yᵢ`, kept as the bare variable when `sᵢ = 0`. -/
def shiftVar (s : ℕ → ℚ) (i : ℕ) : Poly := if s i = 0 then var i else add (const (s i)) (var i)

theorem eval_shiftVar (y : ℕ → ℝ) (s : ℕ → ℚ) (i : ℕ) :
    eval y (shiftVar s i) = s i + y i := by
  unfold shiftVar
  split_ifs with h
  · simp [h]
  · simp [eval_add]

def shiftMonoFrom (s : ℕ → ℚ) : ℕ → Mono → Poly
  | _, [] => const 1
  | k, e :: m => normalize (mul (npow (shiftVar s k) e) (shiftMonoFrom s (k + 1) m))

theorem eval_shiftMonoFrom (y : ℕ → ℝ) (s : ℕ → ℚ) :
    ∀ (k : ℕ) (m : Mono), eval y (shiftMonoFrom s k m) =
      monoEvalFrom (fun i => s i + y i) k m
  | k, [] => by simp [shiftMonoFrom, monoEvalFrom]
  | k, e :: m => by
      simp only [shiftMonoFrom, eval_normalize, eval_mul, eval_npow,
        eval_shiftVar, eval_shiftMonoFrom y s (k + 1) m, monoEvalFrom]

/-- The polynomial `q(y) = p(s + y)`. -/
def shiftPoly (s : ℕ → ℚ) (p : Poly) : Poly :=
  normalize (p.flatMap fun t => scale t.2 (shiftMonoFrom s 0 t.1))

theorem eval_shiftPoly (y : ℕ → ℝ) (s : ℕ → ℚ) (p : Poly) :
    eval y (shiftPoly s p) = eval (fun i => s i + y i) p := by
  unfold shiftPoly
  rw [eval_normalize]
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [List.flatMap_cons, eval_append, eval_scale, ih, eval_cons,
        eval_shiftMonoFrom, monoEval]

/-! ## Composition `xᵢ ↦ fᵢ` -/

def compMonoFrom (f : ℕ → Poly) : ℕ → Mono → Poly
  | _, [] => const 1
  | k, e :: m => normalize (mul (npow (f k) e) (compMonoFrom f (k + 1) m))

theorem eval_compMonoFrom (y : ℕ → ℝ) (f : ℕ → Poly) :
    ∀ (k : ℕ) (m : Mono), eval y (compMonoFrom f k m) =
      monoEvalFrom (fun i => eval y (f i)) k m
  | k, [] => by simp [compMonoFrom, monoEvalFrom]
  | k, e :: m => by
      simp only [compMonoFrom, eval_normalize, eval_mul, eval_npow,
        eval_compMonoFrom y f (k + 1) m, monoEvalFrom]

/-- The polynomial `y ↦ p (f₀ y, f₁ y, …)`. -/
def comp (p : Poly) (f : ℕ → Poly) : Poly :=
  normalize (p.flatMap fun t => scale t.2 (compMonoFrom f 0 t.1))

theorem eval_comp (y : ℕ → ℝ) (p : Poly) (f : ℕ → Poly) :
    eval y (comp p f) = eval (fun i => eval y (f i)) p := by
  unfold comp
  rw [eval_normalize]
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [List.flatMap_cons, eval_append, eval_scale, ih, eval_cons,
        eval_compMonoFrom, monoEval]

/-! ## Lower bounds -/

def isConst (m : Mono) : Bool := m.all (· == 0)

theorem monoEvalFrom_const (x : ℕ → ℝ) :
    ∀ (k : ℕ) (m : Mono), isConst m = true → monoEvalFrom x k m = 1
  | _, [], _ => rfl
  | k, e :: m, h => by
      simp only [isConst, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      simp [monoEvalFrom, h.1, monoEvalFrom_const x (k + 1) m (by simpa [isConst] using h.2)]

/-- `|∏ yᵢ^eᵢ| ≤ 1` when every `|yᵢ| ≤ 1`. -/
theorem abs_monoEvalFrom_le_one (y : ℕ → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    ∀ (k : ℕ) (m : Mono), |monoEvalFrom y k m| ≤ 1
  | _, [] => by simp [monoEvalFrom]
  | k, e :: m => by
      simp only [monoEvalFrom, abs_mul, abs_pow]
      exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) (hy k)) (abs_monoEvalFrom_le_one y hy (k + 1) m)
        (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

/-- `0 ≤ ∏ yᵢ^eᵢ ≤ 1` when every `yᵢ ∈ [0,1]`. -/
theorem monoEvalFrom_mem_unit (y : ℕ → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    ∀ (k : ℕ) (m : Mono), 0 ≤ monoEvalFrom y k m ∧ monoEvalFrom y k m ≤ 1
  | _, [] => by simp [monoEvalFrom]
  | k, e :: m => by
      obtain ⟨h0, h1⟩ := monoEvalFrom_mem_unit y hy (k + 1) m
      simp only [monoEvalFrom]
      exact ⟨mul_nonneg (pow_nonneg (hy k).1 _) h0,
        (mul_le_mul (pow_le_one₀ (hy k).1 (hy k).2) h1 h0 zero_le_one).trans_eq (mul_one 1)⟩

/-- Constant term minus the absolute values of the other coefficients. -/
def centeredLowerOf (p : Poly) : ℚ :=
  (p.map fun t => if isConst t.1 then t.2 else -|t.2|).sum

theorem centeredLowerOf_le (y : ℕ → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    ∀ p : Poly, (centeredLowerOf p : ℝ) ≤ eval y p
  | [] => by simp [centeredLowerOf]
  | t :: p => by
      have ih := centeredLowerOf_le y hy p
      simp only [centeredLowerOf, List.map_cons, List.sum_cons, eval_cons] at ih ⊢
      rw [Rat.cast_add]
      have hterm : ((if isConst t.1 then t.2 else -|t.2| : ℚ) : ℝ) ≤
          (t.2 : ℝ) * monoEval y t.1 := by
        split_ifs with hc
        · simp [monoEval, monoEvalFrom_const y 0 t.1 hc]
        · have hm := abs_monoEvalFrom_le_one y hy 0 t.1
          have := neg_abs_le ((t.2 : ℝ) * monoEval y t.1)
          rw [abs_mul] at this
          push_cast
          have h2 : |(t.2 : ℝ)| * |monoEval y t.1| ≤ |(t.2 : ℝ)| :=
            mul_le_of_le_one_right (abs_nonneg _) hm
          linarith
      linarith

/-- Constant term plus the negative coefficients. -/
def cornerLowerOf (p : Poly) : ℚ :=
  (p.map fun t => if isConst t.1 then t.2 else min 0 t.2).sum

theorem cornerLowerOf_le (y : ℕ → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    ∀ p : Poly, (cornerLowerOf p : ℝ) ≤ eval y p
  | [] => by simp [cornerLowerOf]
  | t :: p => by
      have ih := cornerLowerOf_le y hy p
      simp only [cornerLowerOf, List.map_cons, List.sum_cons, eval_cons] at ih ⊢
      rw [Rat.cast_add]
      have hterm : ((if isConst t.1 then t.2 else min 0 t.2 : ℚ) : ℝ) ≤
          (t.2 : ℝ) * monoEval y t.1 := by
        split_ifs with hc
        · simp [monoEval, monoEvalFrom_const y 0 t.1 hc]
        · obtain ⟨h0, h1⟩ := monoEvalFrom_mem_unit y hy 0 t.1
          change 0 ≤ monoEval y t.1 at h0
          change monoEval y t.1 ≤ 1 at h1
          rcases le_total 0 (t.2 : ℝ) with hc2 | hc2
          · rw [min_eq_left (by exact_mod_cast hc2)]
            simpa using mul_nonneg hc2 h0
          · rw [min_eq_right (by exact_mod_cast hc2)]
            have := mul_le_mul_of_nonpos_left h1 hc2
            linarith
      linarith

/-- A box: center and half-width per variable. -/
structure Box where
  center : ℕ → ℚ
  radius : ℕ → ℚ

def Box.Mem (box : Box) (x : ℕ → ℝ) : Prop :=
  ∀ i, |x i - box.center i| ≤ box.radius i

/-! ## Pinning variables to fixed values -/

/-- The factor and the remaining monomial after setting the `pin`ned
variables to their values. -/
def pinMonoFrom (pin : ℕ → Option ℚ) : ℕ → Mono → ℚ × Mono
  | _, [] => (1, [])
  | k, e :: m =>
      match pin k with
      | some c => ((c : ℚ) ^ e * (pinMonoFrom pin (k + 1) m).1, 0 :: (pinMonoFrom pin (k + 1) m).2)
      | none => ((pinMonoFrom pin (k + 1) m).1, e :: (pinMonoFrom pin (k + 1) m).2)

theorem pinMonoFrom_eval (pin : ℕ → Option ℚ) (y : ℕ → ℝ)
    (hy : ∀ k c, pin k = some c → y k = c) :
    ∀ (k : ℕ) (m : Mono), ((pinMonoFrom pin k m).1 : ℝ) *
      monoEvalFrom y k (pinMonoFrom pin k m).2 = monoEvalFrom y k m
  | k, [] => by simp [pinMonoFrom, monoEvalFrom]
  | k, e :: m => by
      have ih := pinMonoFrom_eval pin y hy (k + 1) m
      cases h : pin k with
      | none =>
          simp only [pinMonoFrom, h, monoEvalFrom]
          rw [← ih]; ring
      | some c =>
          simp only [pinMonoFrom, h, monoEvalFrom, hy k c h, pow_zero, one_mul]
          rw [← ih]; push_cast; ring

/-- `p` with the `pin`ned variables set to their values. -/
def pinPoly (pin : ℕ → Option ℚ) (p : Poly) : Poly :=
  normalize (p.map fun t => ((pinMonoFrom pin 0 t.1).2, t.2 * (pinMonoFrom pin 0 t.1).1))

theorem eval_pinPoly (pin : ℕ → Option ℚ) (y : ℕ → ℝ)
    (hy : ∀ k c, pin k = some c → y k = c) (p : Poly) :
    eval y (pinPoly pin p) = eval y p := by
  unfold pinPoly
  rw [eval_normalize]
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [List.map_cons, eval_cons, ih, monoEval]
      rw [← pinMonoFrom_eval pin y hy 0 t.1]
      push_cast; ring

/-- The variables a box fixes (zero radius). -/
def Box.pin (box : Box) : ℕ → Option ℚ :=
  fun i => if box.radius i = 0 then some (box.center i) else none

theorem Box.pin_spec {box : Box} {y : ℕ → ℝ} (hmem : box.Mem y) :
    ∀ k c, box.pin k = some c → y k = c := by
  intro k c h
  unfold Box.pin at h
  split_ifs at h with hr
  cases h
  have := hmem k
  rw [hr] at this
  push_cast at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

/-- Centered bound: substitute `x = c + r y` with `|y| ≤ 1`. -/
def Box.lo (b : Box) (i : ℕ) : ℚ := b.center i - b.radius i

def Box.hi (b : Box) (i : ℕ) : ℚ := b.center i + b.radius i

/-- Variables that are `≥ 0` on the box and not identically zero there. -/
def Box.nonnegVars (b : Box) : ℕ → Bool :=
  fun v => decide (0 ≤ b.lo v ∧ 0 < b.hi v)

theorem Box.nonnegVars_sound (b : Box) {y : ℕ → ℝ} (hmem : b.Mem y) (v : ℕ)
    (hv : b.nonnegVars v = true) : 0 ≤ y v := by
  simp only [Box.nonnegVars, Box.lo] at hv
  replace hv := (of_decide_eq_true hv).1
  have := abs_le.mp (hmem v)
  have hv' : (0 : ℝ) ≤ (b.center v : ℝ) - b.radius v := by exact_mod_cast hv
  linarith [this.1]

def centeredLower (box : Box) (p : Poly) : ℚ :=
  centeredLowerOf (subst box.center box.radius p)

theorem centeredLower_le (box : Box) (p : Poly) {x : ℕ → ℝ}
    (hx : box.Mem x) (hr : ∀ i, 0 < box.radius i ∨ box.radius i = 0 ∧ x i = box.center i) :
    (centeredLower box p : ℝ) ≤ eval x p := by
  let y : ℕ → ℝ := fun i =>
    if box.radius i = 0 then 0 else (x i - box.center i) / box.radius i
  have hy : ∀ i, |y i| ≤ 1 := by
    intro i
    simp only [y]
    split_ifs with h
    · simp
    · have hpos : 0 < (box.radius i : ℝ) := by
        rcases hr i with h' | h'
        · exact_mod_cast h'
        · exact absurd h'.1 h
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hx i
  have hxy : (fun i => (box.center i : ℝ) + box.radius i * y i) = x := by
    funext i
    simp only [y]
    split_ifs with h
    · rcases hr i with h' | h'
      · exact absurd h (ne_of_gt h')
      · rw [h'.2]; simp [h]
    · have hne : (box.radius i : ℝ) ≠ 0 := by exact_mod_cast h
      field_simp
      ring
  have := centeredLowerOf_le y hy (subst box.center box.radius p)
  rw [eval_subst, hxy] at this
  exact this

/-- Corner bound from the lower corner: `x = lo + 2 r y` with `y ∈ [0,1]`. -/
def cornerLower (box : Box) (p : Poly) : ℚ :=
  cornerLowerOf (subst (fun i => box.center i - box.radius i)
    (fun i => 2 * box.radius i) p)

theorem cornerLower_le (box : Box) (p : Poly) {x : ℕ → ℝ}
    (hx : box.Mem x) (hr : ∀ i, 0 < box.radius i ∨ box.radius i = 0 ∧ x i = box.center i) :
    (cornerLower box p : ℝ) ≤ eval x p := by
  let y : ℕ → ℝ := fun i =>
    if box.radius i = 0 then 0
    else (x i - (box.center i - box.radius i)) / (2 * box.radius i)
  have hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by
    intro i
    simp only [y]
    split_ifs with h
    · simp
    · have hpos : 0 < (box.radius i : ℝ) := by
        rcases hr i with h' | h'
        · exact_mod_cast h'
        · exact absurd h'.1 h
      have hb := abs_le.mp (hx i)
      constructor
      · apply div_nonneg <;> linarith
      · rw [div_le_one (by linarith)]; linarith
  have hxy : (fun i => ((box.center i - box.radius i : ℚ) : ℝ) +
      ((2 * box.radius i : ℚ) : ℝ) * y i) = x := by
    funext i
    simp only [y]
    split_ifs with h
    · rcases hr i with h' | h'
      · exact absurd h (ne_of_gt h')
      · rw [h'.2]; simp [h]
    · have hne : (box.radius i : ℝ) ≠ 0 := by exact_mod_cast h
      push_cast
      field_simp
      ring
  have := cornerLowerOf_le y hy (subst (fun i => box.center i - box.radius i)
    (fun i => 2 * box.radius i) p)
  rw [eval_subst, hxy] at this
  exact this

/-- Corner bound from the upper corner: `x = hi - 2 r y` with `y ∈ [0,1]`. -/
def cornerLowerHi (box : Box) (p : Poly) : ℚ :=
  cornerLowerOf (subst (fun i => box.center i + box.radius i)
    (fun i => -(2 * box.radius i)) p)

theorem cornerLowerHi_le (box : Box) (p : Poly) {x : ℕ → ℝ}
    (hx : box.Mem x) (hr : ∀ i, 0 < box.radius i ∨ box.radius i = 0 ∧ x i = box.center i) :
    (cornerLowerHi box p : ℝ) ≤ eval x p := by
  let y : ℕ → ℝ := fun i =>
    if box.radius i = 0 then 0
    else ((box.center i + box.radius i) - x i) / (2 * box.radius i)
  have hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by
    intro i
    simp only [y]
    split_ifs with h
    · simp
    · have hpos : 0 < (box.radius i : ℝ) := by
        rcases hr i with h' | h'
        · exact_mod_cast h'
        · exact absurd h'.1 h
      have hb := abs_le.mp (hx i)
      constructor
      · apply div_nonneg <;> linarith
      · rw [div_le_one (by linarith)]; linarith
  have hxy : (fun i => ((box.center i + box.radius i : ℚ) : ℝ) +
      ((-(2 * box.radius i) : ℚ) : ℝ) * y i) = x := by
    funext i
    simp only [y]
    split_ifs with h
    · rcases hr i with h' | h'
      · exact absurd h (ne_of_gt h')
      · rw [h'.2]; simp [h]
    · have hne : (box.radius i : ℝ) ≠ 0 := by exact_mod_cast h
      push_cast
      field_simp
      ring
  have := cornerLowerOf_le y hy (subst (fun i => box.center i + box.radius i)
    (fun i => -(2 * box.radius i)) p)
  rw [eval_subst, hxy] at this
  exact this

/-- The best of the three sound lower bounds. -/
def boxLower (box : Box) (p : Poly) : ℚ :=
  max (centeredLower box p) (max (cornerLower box p) (cornerLowerHi box p))

theorem Box.hr_of_mem {box : Box} {x : ℕ → ℝ} (hx : box.Mem x)
    (hrad : ∀ i, 0 ≤ box.radius i) :
    ∀ i, 0 < box.radius i ∨ box.radius i = 0 ∧ x i = box.center i := by
  intro i
  rcases (hrad i).lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.symm, ?_⟩
    have := hx i
    rw [← h] at this
    push_cast at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

theorem boxLower_le (box : Box) (p : Poly) {x : ℕ → ℝ} (hx : box.Mem x)
    (hrad : ∀ i, 0 ≤ box.radius i) :
    (boxLower box p : ℝ) ≤ eval x p := by
  have hr := Box.hr_of_mem hx hrad
  unfold boxLower
  push_cast
  exact max_le (centeredLower_le box p hx hr)
    (max_le (cornerLower_le box p hx hr) (cornerLowerHi_le box p hx hr))

/-! ## Monomial division -/

/-- Pointwise truncated subtraction of exponent lists. -/
def monoSub : Mono → Mono → Mono
  | [], _ => []
  | e, [] => e
  | a :: e, b :: m => (a - b) :: monoSub e m

/-- `m ≤ e` pointwise (missing entries are zero). -/
def monoLe : Mono → Mono → Bool
  | [], _ => true
  | b :: m, [] => b == 0 && monoLe m []
  | b :: m, a :: e => decide (b ≤ a) && monoLe m e

theorem monoEvalFrom_sub (x : ℕ → ℝ) :
    ∀ (k : ℕ) (m e : Mono), monoLe m e = true →
      monoEvalFrom x k e = monoEvalFrom x k m * monoEvalFrom x k (monoSub e m)
  | k, [], e, _ => by cases e <;> simp [monoSub, monoEvalFrom]
  | k, b :: m, [], h => by
      simp only [monoLe, Bool.and_eq_true, beq_iff_eq] at h
      have ih := monoEvalFrom_sub x (k + 1) m [] h.2
      simp only [monoSub, monoEvalFrom, h.1, pow_zero, one_mul] at ih ⊢
      simpa [monoSub] using ih
  | k, b :: m, a :: e, h => by
      simp only [monoLe, Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := monoEvalFrom_sub x (k + 1) m e h.2
      simp only [monoSub, monoEvalFrom]
      rw [ih, show a = b + (a - b) by omega, pow_add]
      simp only [show b + (a - b) - b = a - b by omega]
      ring

def dividesAll (m : Mono) (p : Poly) : Bool := p.all fun t => monoLe m t.1

def divByMono (p : Poly) (m : Mono) : Poly := p.map fun t => (monoSub t.1 m, t.2)

theorem eval_divByMono (x : ℕ → ℝ) (m : Mono) :
    ∀ p : Poly, dividesAll m p = true →
      eval x p = monoEval x m * eval x (divByMono p m)
  | [], _ => by simp [divByMono]
  | t :: p, h => by
      simp only [dividesAll, List.all_cons, Bool.and_eq_true] at h
      have ih := eval_divByMono x m p (by simpa [dividesAll] using h.2)
      simp only [divByMono, List.map_cons, eval_cons] at ih ⊢
      rw [ih]
      unfold monoEval
      rw [monoEvalFrom_sub x 0 m t.1 h.1]
      ring

/-- Pointwise minimum exponent over the allowed variables (zero elsewhere). -/
def gcdMono (allowed : ℕ → Bool) (p : Poly) : Mono :=
  let len := (p.map fun t => t.1.length).foldr max 0
  (List.range len).map fun i =>
    if allowed i then (p.map fun t => t.1.getD i 0).foldr min
      ((p.head?.map fun t => t.1.getD i 0).getD 0) else 0

theorem monoEvalFrom_nonneg (x : ℕ → ℝ) :
    ∀ (k : ℕ) (m : Mono), (∀ i, i < m.length → 0 < m.getD i 0 → 0 ≤ x (k + i)) →
      0 ≤ monoEvalFrom x k m
  | _, [], _ => by simp [monoEvalFrom]
  | k, a :: m, h => by
      simp only [monoEvalFrom]
      apply mul_nonneg
      · rcases Nat.eq_zero_or_pos a with ha | ha
        · simp [ha]
        · exact pow_nonneg (by simpa using h 0 (by simp) (by simpa using ha)) _
      · apply monoEvalFrom_nonneg x (k + 1) m
        intro i hi hpos
        have := h (i + 1) (by simp; omega) (by simpa using hpos)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem monoEvalFrom_pos (x : ℕ → ℝ) :
    ∀ (k : ℕ) (m : Mono), (∀ i, i < m.length → 0 < m.getD i 0 → 0 < x (k + i)) →
      0 < monoEvalFrom x k m
  | _, [], _ => by simp [monoEvalFrom]
  | k, a :: m, h => by
      simp only [monoEvalFrom]
      apply mul_pos
      · rcases Nat.eq_zero_or_pos a with ha | ha
        · simp [ha]
        · exact pow_pos (by simpa using h 0 (by simp) (by simpa using ha)) _
      · apply monoEvalFrom_pos x (k + 1) m
        intro i hi hpos
        have := h (i + 1) (by simp; omega) (by simpa using hpos)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem getD_map_range (n i : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).getD i 0 = if i < n then f i else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · simp [hi]
  · simp [hi]

theorem gcdMono_getD_pos (allowed : ℕ → Bool) (p : Poly) (i : ℕ)
    (h : 0 < (gcdMono allowed p).getD i 0) : allowed i = true := by
  by_contra hna
  unfold gcdMono at h
  rw [getD_map_range] at h
  split_ifs at h <;> simp_all

theorem monoEval_nonneg_of (x : ℕ → ℝ) (m : Mono)
    (h : ∀ i, 0 < m.getD i 0 → 0 ≤ x i) : 0 ≤ monoEval x m :=
  monoEvalFrom_nonneg x 0 m (fun i _ hpos => by simpa using h i hpos)

theorem monoEval_pos_of (x : ℕ → ℝ) (m : Mono)
    (h : ∀ i, 0 < m.getD i 0 → 0 < x i) : 0 < monoEval x m :=
  monoEvalFrom_pos x 0 m (fun i _ hpos => by simpa using h i hpos)

/-- Terms whose exponent of variable `v` is positive. -/
def withVar (v : ℕ) (p : Poly) : Poly := p.filter fun t => 0 < t.1.getD v 0

/-- Terms whose exponent of variable `v` is zero. -/
def withoutVar (v : ℕ) (p : Poly) : Poly :=
  p.filter fun t => !decide (0 < t.1.getD v 0)

theorem eval_filter_split (x : ℕ → ℝ) (f : Mono × ℚ → Bool) :
    ∀ p : Poly, eval x p = eval x (p.filter f) + eval x (p.filter fun t => !f t)
  | [] => by simp
  | t :: p => by
      have ih := eval_filter_split x f p
      cases hf : f t <;> simp [hf, ih] <;> ring

theorem eval_withVar_add (x : ℕ → ℝ) (v : ℕ) (p : Poly) :
    eval x p = eval x (withVar v p) + eval x (withoutVar v p) := by
  have := eval_filter_split x (fun t => decide (0 < t.1.getD v 0)) p
  simpa [withVar, withoutVar] using this

end Noperts.Stellated.SparsePoly

end
