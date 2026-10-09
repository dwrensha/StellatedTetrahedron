module

public import Noperts.Stellated.ChartKernelFastGlobal
public import Noperts.Stellated.ChartKernelMixedSound

@[expose] public section

/-!
# A faster kernel checker for mixed global chart leaves

`mixedZ mb mbR hints` decides the conditions of `ChartKernelM.validMixedK mb hints` with the
pair-arithmetic components of `ChartKernelFastGlobal` (`gcoreZ`, `ctlBQ`); `mbR` is `mb` with a
fixed interval and view.
-/

namespace Noperts.Stellated.ChartKernelF

open ChartKernel ChartKernelG ChartKernelM PackedSlots ZP
open AtlasProjectiveMixedGlobalCertificate

/-- The packed mixed control vector `(i, j)` (cf. `mixPair`). -/
def mixPairZ (mb mbR : Box) (i j : Fin 3) : BQ :=
  let c := fun k => ctlBQ (mb.componentBox k) (mbR.componentBox k) i j
  let f := fun k => ofI (aW mb k * μOther mb k)
  ⟨padd (psm (f 0) (c 0).u) (padd (psm (f 1) (c 1).u) (padd (psm (f 2) (c 2).u) (psm (f 3) (c 3).u))),
    Nat.add (Nat.mul (sz (f 0)) (c 0).m) (Nat.add (Nat.mul (sz (f 1)) (c 1).m)
      (Nat.add (Nat.mul (sz (f 2)) (c 2).m) (Nat.mul (sz (f 3)) (c 3).m)))⟩

def mixedZ (mb mbR : Box) (hints : List ℤ) : Bool :=
  let c0 := mb.componentBox 0
  let sh := shell c0
  let D : ℤ := wDen mb
  let HA : ℤ := aW mb 0 * hintK hints 0 + (aW mb 1 * hintK hints 1 +
    (aW mb 2 * hintK hints 2 + aW mb 3 * hintK hints 3))
  let th := ceilDiv (4 * μAll mb * dBoundNum sh * HA * 10 ^ 10 +
    2400 * μAll mb * D * σ0 c0 * dBoundNum sh) (10 ^ 10)
  let ok := fun (v : BQ) => bernOkZ v.u v.m th
  decide (0 ≤ aW mb 0) && gcoreZ (mb.componentBox 0) (mbR.componentBox 0) hints &&
  decide (0 ≤ aW mb 1) && gcoreZ (mb.componentBox 1) (mbR.componentBox 1) (hints.drop 3) &&
  decide (0 ≤ aW mb 2) && gcoreZ (mb.componentBox 2) (mbR.componentBox 2) (hints.drop 6) &&
  decide (0 ≤ aW mb 3) && gcoreZ (mb.componentBox 3) (mbR.componentBox 3) (hints.drop 9) &&
  decide (aW mb 0 + aW mb 1 + aW mb 2 + aW mb 3 = D) &&
  ok (mixPairZ mb mbR 0 0) && ok (mixPairZ mb mbR 1 1) && ok (mixPairZ mb mbR 2 2) &&
  ok (mixPairZ mb mbR 0 1) && ok (mixPairZ mb mbR 0 2) && ok (mixPairZ mb mbR 1 2)

theorem mixPairZ_rep (mb mbR : Box) (hR : mbR.chart = mb.chart) (hc : mbR.component = mb.component)
    (i j : Fin 3) :
    ∃ d : ℕ → ℤ, PRep KW 27 (mixPairZ mb mbR i j).u d (mixPairZ mb mbR i j).m ∧
      ∀ a b c : Fin 3, (d (9 * a.val + 3 * b.val + c.val) : ℚ) =
        8 * (boxE (shell (mb.componentBox 0)) : ℚ) ^ 2 * (σ0 (mb.componentBox 0) : ℚ) *
          (μAll mb : ℚ) * (wDen mb : ℚ) *
          QuadraticBernstein.coefficient mb.relativeBalls (mb.viewControlQuadratic i j) a b c := by
  obtain ⟨d0, r0, e0⟩ := ctlBQ_rep (mb.componentBox 0) (mbR.componentBox 0)
    (by simp [Box.componentBox, hR]) (by simp [Box.componentBox, hc]) (by simp [Box.componentBox, hc]) i j
  obtain ⟨d1, r1, e1⟩ := ctlBQ_rep (mb.componentBox 1) (mbR.componentBox 1)
    (by simp [Box.componentBox, hR]) (by simp [Box.componentBox, hc]) (by simp [Box.componentBox, hc]) i j
  obtain ⟨d2, r2, e2⟩ := ctlBQ_rep (mb.componentBox 2) (mbR.componentBox 2)
    (by simp [Box.componentBox, hR]) (by simp [Box.componentBox, hc]) (by simp [Box.componentBox, hc]) i j
  obtain ⟨d3, r3, e3⟩ := ctlBQ_rep (mb.componentBox 3) (mbR.componentBox 3)
    (by simp [Box.componentBox, hR]) (by simp [Box.componentBox, hc]) (by simp [Box.componentBox, hc]) i j
  refine ⟨_, (r0.psm _).padd ((r1.psm _).padd ((r2.psm _).padd (r3.psm _))), fun a b c => ?_⟩
  simp only [toZ_ofI]
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

theorem mixZ_lower (mb mbR : Box) (hR : mbR.chart = mb.chart) (hc : mbR.component = mb.component)
    (i j : Fin 3) (th : ℤ)
    (hE : 0 < boxE (shell (mb.componentBox 0))) (hP : 0 < μAll mb)
    (h : bernOkZ (mixPairZ mb mbR i j).u (mixPairZ mb mbR i j).m th = true) :
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
  obtain ⟨d, r, e⟩ := mixPairZ_rep mb mbR hR hc i j
  have hg := bernOkZ_sound r h
  apply le_lower
  intro a b c
  have h1 := hg a b c
  have h2 : (th : ℚ) ≤ d (9 * a.val + 3 * b.val + c.val) := by exact_mod_cast h1
  rw [e] at h2
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem mixedZ_sound (mb mbR : Box) (hints : List ℤ) (hR : mbR.chart = mb.chart)
    (hc : mbR.component = mb.component) (h : mixedZ mb mbR hints = true) : mb.Valid := by
  have hC : ∀ k, (mbR.componentBox k).certificate = (mb.componentBox k).certificate := fun k => by
    simp [Box.componentBox, hc]
  have hRk : ∀ k, (mbR.componentBox k).chart = (mb.componentBox k).chart := fun k => by
    simp [Box.componentBox, hR]
  have hI : ∀ k, (mbR.componentBox k).innerIndex = (mb.componentBox k).innerIndex := fun k => by
    simp [Box.componentBox, hc]
  unfold mixedZ at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0a, h0⟩, h1a⟩, h1⟩, h2a⟩, h2⟩, h3a⟩, h3⟩, hsum⟩, k00⟩, k11⟩, k22⟩, k01⟩, k02⟩,
    k12⟩ := h
  have hA : ∀ k, 0 ≤ aW mb k := fun k => match k with
    | 0 => h0a | 1 => h1a | 2 => h2a | 3 => h3a
  have hcs : ∀ k : Fin 4, (0 : ℤ) < triL (shell (mb.componentBox k)) ∧
      0 < boxE (shell (mb.componentBox k)) ∧ (mb.componentBox k).Admissible ∧
      (mb.componentBox k).weightedDefectUpper ≤ ((((hints.drop (3 * k.val)).getD 0 0 +
        ((hints.drop (3 * k.val)).getD 1 0 + (hints.drop (3 * k.val)).getD 2 0)) : ℤ) : ℚ) /
        (2 * (σ0 (mb.componentBox k) : ℚ)) := fun k => match k with
    | 0 => gcoreZ_sound _ _ _ (hC 0) h0
    | 1 => gcoreZ_sound _ _ _ (hC 1) h1
    | 2 => gcoreZ_sound _ _ _ (hC 2) h2
    | 3 => gcoreZ_sound _ _ _ (hC 3) h3
  have hE : 0 < boxE (shell (mb.componentBox 0)) := (hcs 0).2.1
  have hL : (0 : ℤ) < triL (shell (mb.componentBox 0)) := (hcs 0).1
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
  have hbern : X ≤ mb.bernsteinDisplacementLower := by
    have c10 := viewControl_comm mb 0 1
    have c20 := viewControl_comm mb 0 2
    have c21 := viewControl_comm mb 1 2
    have l00 := mixZ_lower mb mbR hR hc 0 0 th hE hP k00
    have l11 := mixZ_lower mb mbR hR hc 1 1 th hE hP k11
    have l22 := mixZ_lower mb mbR hR hc 2 2 th hE hP k22
    have l01 := mixZ_lower mb mbR hR hc 0 1 th hE hP k01
    have l02 := mixZ_lower mb mbR hR hc 0 2 th hE hP k02
    have l12 := mixZ_lower mb mbR hR hc 1 2 th hE hP k12
    simp only [Box.bernsteinDisplacementLower, QuadraticBernstein.min3, le_min_iff, c10, c20, c21]
    exact ⟨⟨l00, l01, l02⟩, ⟨l01, l11, l12⟩, ⟨l02, l12, l22⟩⟩
  -- the weights
  have hw : ∀ k, mb.weight k = (aW mb k : ℚ) / wDen mb := by
    intro k; rw [aW_cast]; field_simp
  have hw0 : ∀ k, 0 ≤ mb.weight k := by
    intro k; rw [hw]
    exact div_nonneg (by exact_mod_cast hA k) hDq.le
  -- the weighted defects
  have hWD : ∀ k, (mb.componentBox k).weightedDefectUpper ≤
      (hintK hints k : ℚ) / (2 * (σ0 c0 : ℚ)) := by
    intro k
    have := (hcs k).2.2.2
    simp only [getD_drop, add_zero, σ0_comp] at this
    simpa [hintK, add_assoc] using this
  refine ⟨hw0, ?_, fun k => (hcs k).2.2.1, ?_⟩
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


end Noperts.Stellated.ChartKernelF
