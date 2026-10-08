module

public import Noperts.Stellated.ChartKernelMixed
public import Noperts.Stellated.ChartKernelGlobalSound

@[expose] public section

/-!
# Soundness of the packed mixed-certificate checker
-/

namespace Noperts.Stellated.ChartKernelM

open ChartKernel ChartKernelG PackedSlots Noperts.Checker
open AtlasProjectiveMixedGlobalCertificate

theorem coefficient_add (vars : Fin 3 → RatBall) (p q : RatQuadratic3) (i j k : Fin 3) :
    QuadraticBernstein.coefficient vars (p + q) i j k =
      QuadraticBernstein.coefficient vars p i j k + QuadraticBernstein.coefficient vars q i j k := by
  simp only [QuadraticBernstein.coefficient, RatQuadratic3.evalQ, RatQuadratic3.add_c0,
    RatQuadratic3.add_cx, RatQuadratic3.add_cy, RatQuadratic3.add_cz, RatQuadratic3.add_cxx,
    RatQuadratic3.add_cxy, RatQuadratic3.add_cxz, RatQuadratic3.add_cyy, RatQuadratic3.add_cyz,
    RatQuadratic3.add_czz]
  split_ifs <;> ring

theorem wDen_pos (mb : Box) : 0 < wDen mb := lcmList_pos _

theorem aW_cast (mb : Box) (k : Fin 4) : (aW mb k : ℚ) = wDen mb * mb.weight k :=
  qScale_cast _ _ (dvd_lcmList _ _ (by fin_cases k <;> simp))

theorem getD_drop (l : List ℤ) (m i : ℕ) : (l.drop m).getD i 0 = l.getD (m + i) 0 := by
  simp [List.getD_eq_getElem?_getD]

/-- All components share the view, the box, and hence `σ₀`, `E`, the balls. -/
theorem σ0_comp (mb : Box) (k : Fin 4) : σ0 (mb.componentBox k) = σ0 (mb.componentBox 0) := rfl
theorem boxE_comp (mb : Box) (k : Fin 4) :
    boxE (shell (mb.componentBox k)) = boxE (shell (mb.componentBox 0)) := rfl
theorem balls_comp (mb : Box) (k : Fin 4) :
    (mb.componentBox k).relativeBalls = mb.relativeBalls := rfl

theorem μOther_mul (mb : Box) (k : Fin 4) : μOther mb k * μd mb k = μAll mb := by
  match k with
  | 0 => simp only [μOther, μAll]; ring
  | 1 => simp only [μOther, μAll]; ring
  | 2 => simp only [μOther, μAll]; ring
  | 3 => simp only [μOther, μAll]

theorem viewControl_comm (mb : Box) (i j : Fin 3) :
    mb.viewControlQuadratic j i = mb.viewControlQuadratic i j := by
  simp only [Box.viewControlQuadratic, ChartKernelG.viewControl_comm]

/-- The mixed control vector represents `8 E² σ₀ μAll D ·` the mixture's
Bernstein coefficients. -/
theorem mixPair_rep (mb : Box) (i j : Fin 3) :
    ∃ d : ℕ → ℤ, PRep KW 27 (mixPair mb i j).1 d (mixPair mb i j).2 ∧
      ∀ a b c : Fin 3, (d (9 * a.val + 3 * b.val + c.val) : ℚ) =
        8 * (boxE (shell (mb.componentBox 0)) : ℚ) ^ 2 * (σ0 (mb.componentBox 0) : ℚ) *
          (μAll mb : ℚ) * (wDen mb : ℚ) *
          QuadraticBernstein.coefficient mb.relativeBalls (mb.viewControlQuadratic i j) a b c := by
  obtain ⟨d0, r0, e0⟩ := ctlPair_rep (mb.componentBox 0) i j
  obtain ⟨d1, r1, e1⟩ := ctlPair_rep (mb.componentBox 1) i j
  obtain ⟨d2, r2, e2⟩ := ctlPair_rep (mb.componentBox 2) i j
  obtain ⟨d3, r3, e3⟩ := ctlPair_rep (mb.componentBox 3) i j
  refine ⟨_, (r0.smul _).add ((r1.smul _).add ((r2.smul _).add (r3.smul _))), fun a b c => ?_⟩
  push_cast
  rw [e0, e1, e2, e3]
  simp only [Box.viewControlQuadratic, coefficient_add, coefficient_scale, balls_comp, boxE_comp,
    σ0_comp]
  have m0 := μOther_mul mb 0
  have m1 := μOther_mul mb 1
  have m2 := μOther_mul mb 2
  have m3 := μOther_mul mb 3
  have q0 : ((μOther mb 0 : ℤ) : ℚ) * (μd mb 0 : ℚ) = μAll mb := by exact_mod_cast m0
  have q1 : ((μOther mb 1 : ℤ) : ℚ) * (μd mb 1 : ℚ) = μAll mb := by exact_mod_cast m1
  have q2 : ((μOther mb 2 : ℤ) : ℚ) * (μd mb 2 : ℚ) = μAll mb := by exact_mod_cast m2
  have q3 : ((μOther mb 3 : ℤ) : ℚ) * (μd mb 3 : ℚ) = μAll mb := by exact_mod_cast m3
  simp only [μd] at q0 q1 q2 q3
  rw [aW_cast, aW_cast, aW_cast, aW_cast]
  linear_combination
    (8 * (boxE (shell (mb.componentBox 0)) : ℚ) ^ 2 * (σ0 (mb.componentBox 0) : ℚ) * wDen mb) *
      (mb.weight 0 * QuadraticBernstein.coefficient mb.relativeBalls
          ((mb.componentBox 0).viewControlQuadratic i j) a b c * q0 +
        mb.weight 1 * QuadraticBernstein.coefficient mb.relativeBalls
          ((mb.componentBox 1).viewControlQuadratic i j) a b c * q1 +
        mb.weight 2 * QuadraticBernstein.coefficient mb.relativeBalls
          ((mb.componentBox 2).viewControlQuadratic i j) a b c * q2 +
        mb.weight 3 * QuadraticBernstein.coefficient mb.relativeBalls
          ((mb.componentBox 3).viewControlQuadratic i j) a b c * q3)

theorem mixOk_lower (mb : Box) (i j : Fin 3) (th : ℤ)
    (hE : 0 < boxE (shell (mb.componentBox 0))) (hP : 0 < μAll mb)
    (h : ctlOk (mixPair mb i j).1 (mixPair mb i j).2 th = true) :
    (th : ℚ) / (8 * (boxE (shell (mb.componentBox 0)) : ℚ) ^ 2 * (σ0 (mb.componentBox 0) : ℚ) *
        (μAll mb : ℚ) * (wDen mb : ℚ)) ≤
      QuadraticBernstein.lower mb.relativeBalls (mb.viewControlQuadratic i j) := by
  have hEq : (0 : ℚ) < boxE (shell (mb.componentBox 0)) := by exact_mod_cast hE
  have hσ : (0 : ℚ) < σ0 (mb.componentBox 0) := by
    have : (0 : ℤ) < σ0 (mb.componentBox 0) := by
      unfold σ0
      have : (0 : ℤ) < triL (shell (mb.componentBox 0)) := by exact_mod_cast lcmList_pos _
      positivity
    exact_mod_cast this
  have hPq : (0 : ℚ) < μAll mb := by exact_mod_cast hP
  have hD : (0 : ℚ) < wDen mb := by exact_mod_cast wDen_pos mb
  simp only [ctlOk, maskAll_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨d, r, e⟩ := mixPair_rep mb i j
  have hg := testGeM_sound r h.1 h.2
  apply le_lower
  intro a b c
  have h1 := hg (9 * a.val + 3 * b.val + c.val) (by omega) rfl
  have h2 : (th : ℚ) ≤ d (9 * a.val + 3 * b.val + c.val) := by exact_mod_cast h1
  rw [e] at h2
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem μAll_pos (mb : Box) : 0 < μAll mb := by
  have h := fun k => (mb.componentBox k).ballMultiplier.pos
  simp only [μAll, μd]
  have := h 0; have := h 1; have := h 2; have := h 3
  positivity

theorem validMixedK_sound (mb : Box) (hints : List ℤ) (h : validMixedK mb hints = true) :
    mb.Valid := by
  simp only [validMixedK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨⟨hcomp, hsum⟩, hctl⟩ := h
  have hcs := fun k => globalCore_sound (mb.componentBox k) _ (hcomp k).2
  have hcore0 := (hcomp 0).2
  simp only [globalCore, Bool.and_eq_true, decide_eq_true_eq] at hcore0
  have hE : 0 < boxE (shell (mb.componentBox 0)) := hcore0.1.1.1.1.1.1.2
  have hL : (0 : ℤ) < triL (shell (mb.componentBox 0)) := hcore0.1.1.1.1.1.1.1
  set c0 := mb.componentBox 0
  set D : ℤ := (wDen mb : ℤ) with hDdef
  set HA : ℤ := aW mb 0 * hintK hints 0 + (aW mb 1 * hintK hints 1 +
    (aW mb 2 * hintK hints 2 + aW mb 3 * hintK hints 3)) with hHA
  set th := ceilDiv (4 * μAll mb * dBoundNum (shell c0) * HA * 10 ^ 10 +
    2400 * μAll mb * D * σ0 c0 * dBoundNum (shell c0)) (10 ^ 10) with hth
  have hEq : (0 : ℚ) < boxE (shell c0) := by exact_mod_cast hE
  have hLq : (0 : ℚ) < triL (shell c0) := by exact_mod_cast hL
  have hσ : (σ0 c0 : ℚ) = (triL (shell c0) : ℚ) ^ 2 * 2560000000000000 := by simp [σ0]
  have hσq : (0 : ℚ) < σ0 c0 := by rw [hσ]; exact mul_pos (pow_pos hLq 2) (by norm_num)
  have hP := μAll_pos mb
  have hPq : (0 : ℚ) < μAll mb := by exact_mod_cast hP
  have hDq : (0 : ℚ) < wDen mb := by exact_mod_cast wDen_pos mb
  set X : ℚ := (th : ℚ) / (8 * (boxE (shell c0) : ℚ) ^ 2 * (σ0 c0 : ℚ) * (μAll mb : ℚ) *
    (wDen mb : ℚ)) with hX
  have lc := fun p (hp : p ∈ ctlIndices) => mixOk_lower mb p.1 p.2 th hE hP (hctl p hp)
  have hbern : X ≤ mb.bernsteinDisplacementLower := by
    have c10 := viewControl_comm mb 0 1
    have c20 := viewControl_comm mb 0 2
    have c21 := viewControl_comm mb 1 2
    have l00 := lc (0, 0) (by simp [ctlIndices])
    have l11 := lc (1, 1) (by simp [ctlIndices])
    have l22 := lc (2, 2) (by simp [ctlIndices])
    have l01 := lc (0, 1) (by simp [ctlIndices])
    have l02 := lc (0, 2) (by simp [ctlIndices])
    have l12 := lc (1, 2) (by simp [ctlIndices])
    simp only [Box.bernsteinDisplacementLower, QuadraticBernstein.min3, le_min_iff, c10, c20, c21]
    exact ⟨⟨l00, l01, l02⟩, ⟨l01, l11, l12⟩, ⟨l02, l12, l22⟩⟩
  -- the weights
  have hw : ∀ k, mb.weight k = (aW mb k : ℚ) / wDen mb := by
    intro k; rw [aW_cast]; field_simp
  have hw0 : ∀ k, 0 ≤ mb.weight k := by
    intro k; rw [hw]
    exact div_nonneg (by exact_mod_cast (hcomp k).1) hDq.le
  -- the weighted defects
  have hWD : ∀ k, (mb.componentBox k).weightedDefectUpper ≤
      (hintK hints k : ℚ) / (2 * (σ0 c0 : ℚ)) := by
    intro k
    have := (hcs k).2.2
    simp only [getD_drop, add_zero, σ0_comp] at this
    simpa [hintK, add_assoc] using this
  refine ⟨hw0, ?_, fun k => (hcs k).1, ?_⟩
  · have hs : ((aW mb 0 + aW mb 1 + aW mb 2 + aW mb 3 : ℤ) : ℚ) = wDen mb := by
      rw [hsum]; rfl
    push_cast at hs
    rw [Fin.sum_univ_four, hw, hw, hw, hw]
    field_simp
    linarith
  · have hdB : mb.dBound = (dBoundNum (shell c0) : ℚ) / (boxE (shell c0) : ℚ) ^ 2 :=
      dBound_eq (shell c0)
    have hdB0 : 0 ≤ mb.dBound := by
      rw [hdB]
      have : (0 : ℚ) ≤ c0.dBound := by
        have h1 := sq_nonneg (AtlasEdgeCertificate.endpointAbsBound c0.interval.min.x
          c0.interval.max.x)
        have h2 := sq_nonneg (AtlasEdgeCertificate.endpointAbsBound c0.interval.min.y
          c0.interval.max.y)
        have h3 := sq_nonneg (AtlasEdgeCertificate.endpointAbsBound c0.interval.min.z
          c0.interval.max.z)
        simp only [AtlasProjectiveGlobalCertificate.Box.dBound]
        linarith
      rw [← dBound_eq (shell c0)]
      exact this
    have hdisp : mb.displacementError = 300 * mb.dBound * (1 / 10 ^ 10) := by
      simp [Box.displacementError, Box.dBound,
        AtlasProjectiveGlobalCertificate.Box.displacementError, RationalApprox.κℚ]
    have hceil := le_ceilDiv_mul (4 * μAll mb * dBoundNum (shell c0) * HA * 10 ^ 10 +
      2400 * μAll mb * D * σ0 c0 * dBoundNum (shell c0)) (10 ^ 10) (by norm_num)
    rw [← hth] at hceil
    have hceilq : (4 * (μAll mb : ℚ) * dBoundNum (shell c0) * HA * 10 ^ 10 +
        2400 * (μAll mb : ℚ) * (wDen mb : ℚ) * σ0 c0 * dBoundNum (shell c0)) ≤
          (th : ℚ) * 10 ^ 10 := by
      have := hceil
      simp only [hDdef] at this
      exact_mod_cast this
    have hWDsum : mb.weightedDefectUpper ≤ (HA : ℚ) / (2 * (σ0 c0 : ℚ) * wDen mb) := by
      unfold Box.weightedDefectUpper
      rw [Fin.sum_univ_four]
      have e := fun k => mul_le_mul_of_nonneg_left (hWD k) (hw0 k)
      have hHAq : (HA : ℚ) / (2 * (σ0 c0 : ℚ) * wDen mb) =
          mb.weight 0 * ((hintK hints 0 : ℚ) / (2 * (σ0 c0 : ℚ))) +
          mb.weight 1 * ((hintK hints 1 : ℚ) / (2 * (σ0 c0 : ℚ))) +
          mb.weight 2 * ((hintK hints 2 : ℚ) / (2 * (σ0 c0 : ℚ))) +
          mb.weight 3 * ((hintK hints 3 : ℚ) / (2 * (σ0 c0 : ℚ))) := by
        rw [hw, hw, hw, hw, hHA]
        push_cast
        field_simp
        ring
      rw [hHAq]
      linarith [e 0, e 1, e 2, e 3]
    have hWD' := mul_le_mul_of_nonneg_left hWDsum hdB0
    have key : 300 * mb.dBound * (1 / 10 ^ 10) +
        mb.dBound * ((HA : ℚ) / (2 * (σ0 c0 : ℚ) * wDen mb)) ≤ X := by
      rw [hX, le_div_iff₀ (by positivity), hdB]
      have e : ((300 : ℚ) * (dBoundNum (shell c0) / (boxE (shell c0) : ℚ) ^ 2) * (1 / 10 ^ 10) +
          dBoundNum (shell c0) / (boxE (shell c0) : ℚ) ^ 2 *
            (HA / (2 * (σ0 c0 : ℚ) * wDen mb))) *
          (8 * (boxE (shell c0) : ℚ) ^ 2 * (σ0 c0 : ℚ) * (μAll mb : ℚ) * (wDen mb : ℚ)) =
          (4 * (μAll mb : ℚ) * dBoundNum (shell c0) * HA * 10 ^ 10 +
            2400 * (μAll mb : ℚ) * (wDen mb : ℚ) * σ0 c0 * dBoundNum (shell c0)) / 10 ^ 10 := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by norm_num)]
      exact hceilq
    rw [hdisp]
    linarith

end Noperts.Stellated.ChartKernelM
