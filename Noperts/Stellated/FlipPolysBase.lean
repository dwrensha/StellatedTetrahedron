module

public import Noperts.Stellated.CornerTree
public import Noperts.Stellated.CornerKernelFast

@[expose] public section

/-!
# Integer data for the flip polynomials

`FlipOk fp seg kind k`: `flipPoly seg kind k = S / K` with integer `S`
(`fp.S`, signed magnitudes) and `K = fp.K > 0` (an evaluation identity, proved per
entry by `ring`); the monomial `fp.m` is unused.
A flip leaf then needs only `S ≥ 1` on its box, which the packed cheap bound
proves for `S - 1`.
-/

namespace Noperts.Stellated.CornerKernel

open SparsePoly CornerPoly CornerTree

/-- `flipPoly seg kind k = ε^e · S / K` pointwise (`fp.m = [e]` or `[]`), with `K > 0`
(proved per entry by `ring`). -/
def FlipOk (fp : FactPoly) (seg : Bool) (kind : ChartKind) (k : Fin 12) : Prop :=
  0 < fp.K ∧ fp.m.length ≤ 1 ∧ ∀ y : ℕ → ℝ,
    eval y (flipPoly seg kind k) = monoEval y fp.m * eval y (toIPoly fp.S).toPoly / fp.K

theorem FlipOk.eval_flip {fp : FactPoly} {seg : Bool} {kind : ChartKind} {k : Fin 12}
    (h : FlipOk fp seg kind k) (y : ℕ → ℝ) :
    eval y (flipPoly seg kind k) = monoEval y fp.m * eval y (toIPoly fp.S).toPoly / fp.K :=
  h.2.2 y

theorem monoEval_pos_of_len (y : ℕ → ℝ) (hε : 0 < y 0) : ∀ m : Mono, m.length ≤ 1 →
    0 < monoEval y m
  | [], _ => by simp [monoEval, monoEvalFrom]
  | [e], _ => by simp [monoEval, monoEvalFrom]; positivity
  | _ :: _ :: _, h => by simp at h

/-- `c · S - 1`: its nonnegativity gives `S ≥ 1 / c > 0`. -/
def scaleSub (fp : FactPoly) (c : ℕ) : FactPoly :=
  ⟨fp.S.map (fun t => (t.1, t.2.1 * c, t.2.2)) ++ [([], 1, true)], fp.m, fp.K⟩

theorem eval_scaleSub (fp : FactPoly) (c : ℕ) (y : ℕ → ℝ) :
    eval y (toIPoly (scaleSub fp c).S).toPoly = c * eval y (toIPoly fp.S).toPoly - 1 := by
  simp only [scaleSub, toIPoly, IPoly.toPoly, List.map_append, List.map_map, eval_append]
  have h : ∀ l : List (Mono × ℕ × Bool), eval y (l.map (fun t => (t.1,
      ((sgnI t.2.2 ((t.2.1 * c : ℕ) : ℤ) : ℤ) : ℚ)))) =
      c * eval y (l.map (fun t => (t.1, ((sgnI t.2.2 (t.2.1 : ℤ) : ℤ) : ℚ)))) := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
        simp only [List.map_cons, eval_cons, ih]
        cases t.2.2 <;> simp [sgnI] <;> ring
  simp only [Function.comp_def] at h ⊢
  rw [h]
  simp [sgnI, monoEval, monoEvalFrom]
  ring

end Noperts.Stellated.CornerKernel
