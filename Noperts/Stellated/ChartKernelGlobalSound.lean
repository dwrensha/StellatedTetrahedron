module

public import Noperts.Stellated.ChartKernelGlobal
public import Noperts.Stellated.ChartKernelEdgeSound
public import Noperts.Stellated.LocalKernelSound

@[expose] public section

/-!
# Soundness of the packed global checker

`validGlobalK_sound : validGlobalK box hints = true → box.Valid`.
-/

namespace Noperts.Stellated.ChartKernelG

open ChartKernel PackedSlots AtlasProjectiveGlobalCertificate AtlasProjectiveView
open LocalKernel (V3 edgeN wcN)
open Noperts.Checker

/-! ## Packed products with stride `24` -/

theorem kron_3_24 (w : ℕ) (a b : ℕ → ℕ) :
    packW (w * 24) a 3 * packW w b 24 = packW w (fun t => a (t / 24) * b (t % 24)) 72 := by
  simp only [packW_eq_sum, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

theorem pairMul_rep24 {A B : ℕ × ℕ} {f g : ℕ → ℤ} {Ma Mb : ℕ} (hA : PRep (KW * 24) 3 A f Ma)
    (hB : PRep KW 24 B g Mb) :
    PRep KW 72 (pairMul A B) (fun t => f (t / 24) * g (t % 24)) (2 * Ma * Mb) := by
  obtain ⟨a, b, rfl, hf, hMa⟩ := hA
  obtain ⟨a', b', rfl, hg, hMb⟩ := hB
  refine ⟨fun t => a (t / 24) * a' (t % 24) + b (t / 24) * b' (t % 24),
    fun t => a (t / 24) * b' (t % 24) + b (t / 24) * a' (t % 24), ?_, fun t => ?_, fun t => ?_⟩
  · simp only [pairMul, kron_3_24, ← packW_add]
  · push_cast
    rw [← hf, ← hg]; ring
  · have h1 := hMa (t / 24)
    have h2 := hMb (t % 24)
    have e1 := Nat.mul_le_mul h1.1 h2.1
    have e2 := Nat.mul_le_mul h1.2 h2.2
    have e3 := Nat.mul_le_mul h1.1 h2.2
    have e4 := Nat.mul_le_mul h1.2 h2.1
    have e : 2 * Ma * Mb = Ma * Mb + Ma * Mb := by ring
    rw [e]
    exact ⟨Nat.add_le_add e1 e2, Nat.add_le_add e3 e4⟩

/-! ## Weighted support defects -/

theorem le_sum9' (f : Fin 3 → ℕ → ℕ) (d : Fin 3) (j : ℕ) (hj : j < 3) :
    f d j ≤ f 0 0 + f 0 1 + f 0 2 + f 1 0 + f 1 1 + f 1 2 + f 2 0 + f 2 1 + f 2 2 := by
  interval_cases j <;> fin_cases d <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    omega

theorem le_sum3 (f : ℕ → ℕ) (j : ℕ) (hj : j < 3) : f j ≤ f 0 + f 1 + f 2 := by
  interval_cases j <;> omega

theorem mG_le (bx : Box) (i d : Fin 3) (j : ℕ) : (mG bx i d j).natAbs ≤ mBoundG bx i := by
  rcases Nat.lt_or_ge j 3 with hj | hj
  · exact le_sum9' (fun d j => (mG bx i d j).natAbs) d j hj
  · simp [mG, show ¬ j < 3 by omega]

theorem wG_le (bx : Box) (i : Fin 3) (j : ℕ) : (wG bx i j).natAbs ≤ wBoundG bx i := by
  rcases Nat.lt_or_ge j 3 with hj | hj
  · exact le_sum3 (fun j => (wG bx i j).natAbs) j hj
  · simp [wG, show ¬ j < 3 by omega]

/-- The support value `s_{b,k}` of contact `i` (scaled by `L · 40000 · 40`). -/
def supG (bx : Box) (i : Fin 3) (b k : ℕ) : ℤ :=
  mG bx i 0 b * δN (bx.certificate.index i) 0 k +
    (mG bx i 1 b * δN (bx.certificate.index i) 1 k +
      mG bx i 2 b * δN (bx.certificate.index i) 2 k)

/-- The slot values of `controlPack`. -/
def ctlSlot (bx : Box) (i : Fin 3) (t : ℕ) : ℤ :=
  wG bx i (t / 24) * supG bx i (t % 24 / 8) (t % 24 % 8) +
    wG bx i (t % 24 / 8) * supG bx i (t / 24) (t % 24 % 8)

theorem controlPack_rep (bx : Box) (i : Fin 3) :
    PRep KW 72 (controlPack bx i) (ctlSlot bx i) (1920 * wBoundG bx i * mBoundG bx i) := by
  set s := bx.certificate.index i
  have hd : ∀ d : Fin 3, PRep KW 8 (deltaT s d) (δN s d) 40 :=
    fun d => by rw [deltaT_eq]; exact pmPack_rep KW 8 _ 40 (δN_le _ d)
  have hm8 : ∀ d : Fin 3, PRep (KW * 8) 3 (pmPack (KW * 8) 3 (mG bx i d)) (mG bx i d)
      (mBoundG bx i) := fun d => pmPack_rep _ 3 _ _ (mG_le bx i d)
  have hm24 : ∀ d : Fin 3, PRep (KW * 24) 3 (pmPack (KW * 24) 3 (mG bx i d)) (mG bx i d)
      (mBoundG bx i) := fun d => pmPack_rep _ 3 _ _ (mG_le bx i d)
  have hw8 : PRep (KW * 8) 3 (pmPack (KW * 8) 3 (wG bx i)) (wG bx i) (wBoundG bx i) :=
    pmPack_rep _ 3 _ _ (wG_le bx i)
  have hw24 : PRep (KW * 24) 3 (pmPack (KW * 24) 3 (wG bx i)) (wG bx i) (wBoundG bx i) :=
    pmPack_rep _ 3 _ _ (wG_le bx i)
  have hS := (pairMul_rep (hm8 0) (hd 0)).add ((pairMul_rep (hm8 1) (hd 1)).add
    (pairMul_rep (hm8 2) (hd 2)))
  have hP1 := pairMul_rep24 hw24 hS
  have hY := fun d => pairMul_rep hw8 (hd d)
  have hP2 := (pairMul_rep24 (hm24 0) (hY 0)).add ((pairMul_rep24 (hm24 1) (hY 1)).add
    (pairMul_rep24 (hm24 2) (hY 2)))
  refine ((hP1.add hP2).congr fun t => ?_).mono ?_
  · simp only [ctlSlot, supG]
    ring
  · have e : 2 * wBoundG bx i * (2 * mBoundG bx i * 40 + (2 * mBoundG bx i * 40 +
        2 * mBoundG bx i * 40)) + (2 * mBoundG bx i * (2 * wBoundG bx i * 40) +
        (2 * mBoundG bx i * (2 * wBoundG bx i * 40) + 2 * mBoundG bx i * (2 * wBoundG bx i * 40))) =
        960 * (wBoundG bx i * mBoundG bx i) := by ring
    have e2 : 1920 * wBoundG bx i * mBoundG bx i = 1920 * (wBoundG bx i * mBoundG bx i) := by ring
    rw [e, e2]
    omega

/-! ## Casts -/

theorem shell_triangle (bx : Box) : (shell bx).triangle = bx.triangle := rfl

theorem trow_toQ (bx : Box) (a : Fin 3) :
    (trow bx a).toQ = ((triL (shell bx) : ℕ) : ℚ) • bx.triangle a := by
  funext c
  fin_cases c <;> simp [trow, LocalKernel.V3.toQ, T_cast, shell_triangle]

theorem vtx_x (k : VertexIndex) : (LocalKernel.vtx k).x = vI k 0 := by fin_cases k <;> rfl
theorem vtx_y (k : VertexIndex) : (LocalKernel.vtx k).y = vI k 1 := by fin_cases k <;> rfl
theorem vtx_z (k : VertexIndex) : (LocalKernel.vtx k).z = vI k 2 := by fin_cases k <;> rfl

theorem wG_cast (bx : Box) (i a : Fin 3) :
    (wG bx i a.val : ℚ) = (triL (shell bx) * (40000 * 40000) : ℚ) *
      bx.localShell.weightAt 0 a i := by
  have h := LocalKernel.weight_cast bx.localShell (triL (shell bx)) 0 a i (trow bx a)
    (trow_toQ bx a)
  simp only [wG, a.isLt, ↓reduceDIte]
  exact h

theorem supG_eq (bx : Box) (i b : Fin 3) (k : VertexIndex) :
    supG bx i b.val k.val =
      LocalKernel.V3.dot (LocalKernel.vtx k)
          (LocalKernel.V3.cross (trow bx b) (edgeN bx.certificate i)) -
        LocalKernel.V3.dot (LocalKernel.vtx
            ((bx.localShell.certificate 0).supportIndex bx.localShell i))
          (LocalKernel.V3.cross (trow bx b) (edgeN bx.certificate i)) := by
  have hs : (bx.localShell.certificate 0).supportIndex bx.localShell i =
      bx.certificate.index i := by
    simp [AtlasProjectiveLocalCertificate.AxisCertificate.supportIndex, Box.localShell]
  rw [hs]
  simp only [supG, mG, δN, b.isLt, k.isLt, ↓reduceDIte, LocalKernel.V3.dot, LocalKernel.V3.get,
    LocalKernel.V3.cross, vtx_x, vtx_y, vtx_z, LocalKernel.int_add_eq, LocalKernel.int_sub_eq,
    LocalKernel.int_mul_eq, Fin.eta]
  ring

theorem supG_cast (bx : Box) (i b : Fin 3) (k : VertexIndex) :
    (supG bx i b.val k.val : ℚ) = (triL (shell bx) * (40000 * 40) : ℚ) *
      bx.localShell.supportAt 0 b i k := by
  rw [supG_eq]
  exact LocalKernel.support_cast bx.localShell (triL (shell bx)) 0 b i k (trow bx b)
    (trow_toQ bx b)

/-! ## The weighted defect bound -/

theorem ctlSlot_at (bx : Box) (i a b : Fin 3) (k : VertexIndex) :
    ctlSlot bx i (24 * a.val + 8 * b.val + k.val) =
      wG bx i a.val * supG bx i b.val k.val + wG bx i b.val * supG bx i a.val k.val := by
  have h1 : (24 * a.val + 8 * b.val + k.val) / 24 = a.val := by omega
  have h2 : (24 * a.val + 8 * b.val + k.val) % 24 / 8 = b.val := by omega
  have h3 : (24 * a.val + 8 * b.val + k.val) % 24 % 8 = k.val := by omega
  simp only [ctlSlot, h1, h2, h3]

theorem wsc_le (bx : Box) (i : Fin 3) (k : VertexIndex) (a b : Fin 3) (h : ℤ) (hh : 0 ≤ h)
    (hL : 0 < triL (shell bx))
    (hslot : k ≠ bx.certificate.index i → ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ h) :
    bx.weightedSupportControl i k a b ≤
      (h : ℚ) / (2 * ((triL (shell bx) : ℚ) ^ 2 * 2560000000000000)) := by
  have hLq : (0 : ℚ) < triL (shell bx) := by exact_mod_cast hL
  have hσ : (0 : ℚ) < 2 * ((triL (shell bx) : ℚ) ^ 2 * 2560000000000000) := by positivity
  unfold Box.weightedSupportControl
  split_ifs with hk
  · exact div_nonneg (by exact_mod_cast hh) hσ.le
  · have hs := hslot hk
    rw [ctlSlot_at] at hs
    have hq : ((wG bx i a.val * supG bx i b.val k.val + wG bx i b.val * supG bx i a.val k.val : ℤ)
        : ℚ) ≤ h := by exact_mod_cast hs
    push_cast at hq
    rw [wG_cast, wG_cast, supG_cast, supG_cast] at hq
    rw [LocalKernel.supportError_eq, le_div_iff₀ hσ]
    linear_combination hq

theorem contactDefect_le (bx : Box) (i : Fin 3) (h : ℤ) (hh : 0 ≤ h)
    (hL : 0 < triL (shell bx))
    (hslot : ∀ (a b : Fin 3) (k : VertexIndex), k ≠ bx.certificate.index i →
      ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ h) :
    bx.contactDefectUpper i ≤
      (h : ℚ) / (2 * ((triL (shell bx) : ℚ) ^ 2 * 2560000000000000)) := by
  have hL' : (0 : ℚ) < 2 * ((triL (shell bx) : ℚ) ^ 2 * 2560000000000000) := by
    have : (0 : ℚ) < triL (shell bx) := by exact_mod_cast hL
    positivity
  unfold Box.contactDefectUpper
  refine max_le (div_nonneg (by exact_mod_cast hh) hL'.le) (Finset.max'_le _ _ _ ?_)
  intro y hy
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
  have hw := fun a b => wsc_le bx i k a b h hh hL (hslot a b k)
  simp only [Box.weightedSupportUpper, AtlasProjectiveEdgeCertificate.max3, max_le_iff]
  exact ⟨⟨hw 0 0, hw 0 1, hw 0 2⟩, ⟨hw 1 0, hw 1 1, hw 1 2⟩, ⟨hw 2 0, hw 2 1, hw 2 2⟩⟩

theorem weightedDefect_le (bx : Box) (h : Fin 3 → ℤ) (hh : ∀ i, 0 ≤ h i)
    (hL : 0 < triL (shell bx))
    (hslot : ∀ (i a b : Fin 3) (k : VertexIndex), k ≠ bx.certificate.index i →
      ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ h i) :
    bx.weightedDefectUpper ≤
      ((h 0 + h 1 + h 2 : ℤ) : ℚ) / (2 * ((triL (shell bx) : ℚ) ^ 2 * 2560000000000000)) := by
  unfold Box.weightedDefectUpper
  rw [Fin.sum_univ_three]
  have e := fun i => contactDefect_le bx i (h i) (hh i) hL (hslot i)
  push_cast
  rw [add_div, add_div]
  linarith [e 0, e 1, e 2]

/-! ## Contact and view quadratics -/

theorem dispT_eq (ch : CayleyAtlas.ChartIndex) (u o : VertexIndex) (c : Fin 3) :
    dispT ch u o c = dispI ch u o c := by
  simp only [dispT, dispTab, getD_ofFn]

theorem cqG_toQ (bx : Box) (i c : Fin 3) :
    (cqG bx i c).toQ = RatQuadratic3.scale 1600000 (bx.contactQuadratic i c) := by
  have hd := fun c => dispI_toQ bx.chart (bx.innerIndex i) (bx.certificate.index i) c
  have he := LocalKernel.edgeN_toQ bx.certificate i
  have hx : ((edgeN bx.certificate i).x : ℚ) = 40000 * bx.certificate.edgeQ i 0 := by
    rw [← LocalKernel.V3.toQ_zero, he]; rfl
  have hy : ((edgeN bx.certificate i).y : ℚ) = 40000 * bx.certificate.edgeQ i 1 := by
    rw [← LocalKernel.V3.toQ_one, he]; rfl
  have hz : ((edgeN bx.certificate i).z : ℚ) = 40000 * bx.certificate.edgeQ i 2 := by
    rw [← LocalKernel.V3.toQ_two, he]; rfl
  fin_cases c <;>
    simp only [cqG, dispT_eq, IQ.toQ_sub, IQ.toQ_smul, Box.contactQuadratic, hd] <;>
    (apply RatQuadratic3.ext' <;> simp [RatQuadratic3.scale, hx, hy, hz] <;> ring)

/-- `σ ·` the adjusted view quadratic at `t`, as an integer quadratic (the
quantity whose packed Bernstein vector `viewVec` computes). -/
def viewIQ (bx : Box) (t : V3) (s : ℤ) : IQ :=
  let μ := bx.ballMultiplier
  let α := fun i c => (μ.den : ℤ) * V3.dot t (wcN bx.certificate i) * V3.get t c
  let row := fun i => IQ.add (IQ.smul (α i 0) (cqG bx i 0))
    (IQ.add (IQ.smul (α i 1) (cqG bx i 1)) (IQ.smul (α i 2) (cqG bx i 2)))
  IQ.add (IQ.add (row 0) (IQ.add (row 1) (row 2))) (IQ.smul (μ.num * s * σ0 bx) cayI)

theorem V3.get_cast (t : V3) (c : Fin 3) : (V3.get t c : ℚ) = t.toQ c := by
  fin_cases c <;> rfl

theorem viewIQ_toQ (bx : Box) (t : V3) (r : ℤ) (n : AtlasProjectiveLocalCertificate.VectorQ)
    (ht : t.toQ = ((r * triL (shell bx) : ℤ) : ℚ) • n) :
    (viewIQ bx t (r ^ 2)).toQ = RatQuadratic3.scale
      ((bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ) * (r : ℚ) ^ 2)
      (bx.adjustedViewDisplacementQuadratic n) := by
  set L : ℚ := (triL (shell bx) : ℚ)
  have hdot : ∀ i, (V3.dot t (wcN bx.certificate i) : ℚ) =
      r * L * (40000 * 40000) *
        AtlasProjectiveEdgeCertificate.dotQ n (bx.certificate.weightCoefficient i) := by
    intro i
    rw [LocalKernel.V3.dot_cast, ht, LocalKernel.wcN_toQ, LocalKernel.dotQ_smul_left,
      LocalKernel.dotQ_smul_right]
    push_cast; ring
  have hget : ∀ c, (V3.get t c : ℚ) = r * L * n c := by
    intro c; rw [V3.get_cast, ht]; simp [L]
  have hμ : (bx.ballMultiplier.den : ℚ) * bx.ballMultiplier = bx.ballMultiplier.num :=
    Rat.den_mul_eq_num _
  have hσ : (σ0 bx : ℚ) = L ^ 2 * 2560000000000000 := by simp [σ0, L]
  have hcay : cayI.toQ = bx.cayleyConstraintQuadratic := rfl
  simp only [viewIQ, IQ.toQ_add, IQ.toQ_smul, cqG_toQ, hcay]
  apply RatQuadratic3.ext' <;>
    simp [RatQuadratic3.scale, Box.adjustedViewDisplacementQuadratic,
      Box.viewDisplacementQuadratic, Box.viewContactQuadratic, Box.weightQ, hdot, hget, hσ,
      Box.cayleyConstraintQuadratic] <;>
    (try rw [← hμ]) <;> ring

/-! ## Packed view vectors -/

theorem bvec_rep (bx : Box) (q : IQ) :
    PRep KW 27 (bvec bx q) (bernSlot ((bernWeights (shell bx) q).zip basisTriples)) (bbound bx q) :=
  bernPairK_rep _

theorem viewVec_rep (bx : Box) (t : V3) (s : ℤ) :
    ∃ d : ℕ → ℤ, PRep KW 27 (viewVec bx (fun i c => bvec bx (cqG bx i c)) (bvec bx cayI) t s) d
        (viewBound bx (fun i c => bbound bx (cqG bx i c)) (bbound bx cayI) t s) ∧
      ∀ a b c : Fin 3, d (9 * a.val + 3 * b.val + c.val) =
        bernI (shell bx) (viewIQ bx t s) a.val b.val c.val := by
  set μ := bx.ballMultiplier
  set α := fun i c => (μ.den : ℤ) * V3.dot t (wcN bx.certificate i) * V3.get t c
  have r := fun i c => (bvec_rep bx (cqG bx i c)).smul (α i c)
  have row := fun i => (r i 0).add ((r i 1).add (r i 2))
  have hc := (bvec_rep bx cayI).smul (μ.num * s * σ0 bx)
  refine ⟨_, ((row 0).add ((row 1).add (row 2))).add hc, fun a b c => ?_⟩
  simp only [bernSlot_eq, viewIQ, bernI_add, bernI_smul]
  ring

/-! ## Controls -/

theorem coefficient_scale (vars : Fin 3 → RatBall) (c : ℚ) (q : RatQuadratic3) (i j k : Fin 3) :
    QuadraticBernstein.coefficient vars (RatQuadratic3.scale c q) i j k =
      c * QuadraticBernstein.coefficient vars q i j k :=
  QuadraticBernstein.coefficient_scale vars c q i j k

theorem trow_toQ1 (bx : Box) (a : Fin 3) :
    (trow bx a).toQ = (((1 : ℤ) * triL (shell bx) : ℤ) : ℚ) • bx.triangle a := by
  rw [trow_toQ]; simp

theorem mid_toQ (bx : Box) (a b : Fin 3) :
    (V3.add (trow bx a) (trow bx b)).toQ = (((2 : ℤ) * triL (shell bx) : ℤ) : ℚ) •
      Noperts.ProjectiveView.midpoint (bx.triangle a) (bx.triangle b) := by
  rw [LocalKernel.V3.add_toQ, trow_toQ, trow_toQ]
  funext c
  simp [Noperts.ProjectiveView.midpoint]
  ring

theorem diag_toQ (bx : Box) (j : Fin 3) :
    (IQ.smul 2 (viewIQ bx (trow bx j) 1)).toQ = RatQuadratic3.scale
      (2 * ((bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ))) (bx.viewControlQuadratic j j) := by
  have h := viewIQ_toQ bx (trow bx j) 1 (bx.triangle j) (trow_toQ1 bx j)
  rw [one_pow] at h
  rw [IQ.toQ_smul, h]
  simp only [Box.viewControlQuadratic, ↓reduceIte]
  apply RatQuadratic3.ext' <;> simp [RatQuadratic3.scale] <;> ring

theorem off_toQ (bx : Box) (i j : Fin 3) (hij : i ≠ j) :
    (IQ.sub (viewIQ bx (V3.add (trow bx i) (trow bx j)) 4)
      (IQ.add (viewIQ bx (trow bx i) 1) (viewIQ bx (trow bx j) 1))).toQ = RatQuadratic3.scale
      (2 * ((bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ))) (bx.viewControlQuadratic i j) := by
  have hm := viewIQ_toQ bx _ 2 _ (mid_toQ bx i j)
  have hi := viewIQ_toQ bx (trow bx i) 1 (bx.triangle i) (trow_toQ1 bx i)
  have hj := viewIQ_toQ bx (trow bx j) 1 (bx.triangle j) (trow_toQ1 bx j)
  rw [one_pow] at hi hj
  rw [show ((2 : ℤ) ^ 2) = 4 by norm_num] at hm
  rw [IQ.toQ_sub, IQ.toQ_add, hm, hi, hj]
  simp only [Box.viewControlQuadratic, hij, ↓reduceIte]
  apply RatQuadratic3.ext' <;> simp [RatQuadratic3.scale] <;> ring

/-! ## Admissibility facts -/

theorem weightAt_cast (bx : Box) (a i : Fin 3) :
    ((V3.dot (trow bx a) (wcN bx.certificate i) : ℤ) : ℚ) =
      (triL (shell bx) * (40000 * 40000) : ℚ) * bx.localShell.weightAt 0 a i :=
  LocalKernel.weight_cast bx.localShell (triL (shell bx)) 0 a i (trow bx a) (trow_toQ bx a)

theorem scaleW_pos (bx : Box) (hL : 0 < triL (shell bx)) :
    (0 : ℚ) < triL (shell bx) * (40000 * 40000) := by
  have : (0 : ℚ) < triL (shell bx) := by exact_mod_cast hL
  positivity

theorem weightAt_nonneg (bx : Box) (hL : 0 < triL (shell bx)) (a i : Fin 3)
    (h : 0 ≤ V3.dot (trow bx a) (wcN bx.certificate i)) : 0 ≤ bx.localShell.weightAt 0 a i := by
  have hq : (0 : ℚ) ≤ ((V3.dot (trow bx a) (wcN bx.certificate i) : ℤ) : ℚ) := by exact_mod_cast h
  rw [weightAt_cast] at hq
  exact (mul_nonneg_iff_of_pos_left (scaleW_pos bx hL)).mp hq

theorem weightAt_pos (bx : Box) (hL : 0 < triL (shell bx)) (a i : Fin 3)
    (h : 0 < V3.dot (trow bx a) (wcN bx.certificate i)) : 0 < bx.localShell.weightAt 0 a i := by
  have hq : (0 : ℚ) < ((V3.dot (trow bx a) (wcN bx.certificate i) : ℤ) : ℚ) := by exact_mod_cast h
  rw [weightAt_cast] at hq
  exact (mul_pos_iff_of_pos_left (scaleW_pos bx hL)).mp hq

theorem V3.dot_sub (a b x : V3) : V3.dot (V3.sub a b) x = V3.dot a x - V3.dot b x := by
  simp only [V3.dot, V3.sub, LocalKernel.int_add_eq, LocalKernel.int_sub_eq,
    LocalKernel.int_mul_eq]
  ring

theorem supportAt_neg (bx : Box) (hL : 0 < triL (shell bx)) (a i : Fin 3) (k : VertexIndex)
    (h : V3.dot (V3.sub (LocalKernel.vtx k) (LocalKernel.vtx (bx.certificate.index i)))
      (V3.cross (trow bx a) (edgeN bx.certificate i)) < 0) :
    bx.localShell.supportAt 0 a i k < 0 := by
  have hs : (bx.localShell.certificate 0).supportIndex bx.localShell i =
      bx.certificate.index i := by
    simp [AtlasProjectiveLocalCertificate.AxisCertificate.supportIndex, Box.localShell]
  have hc := LocalKernel.support_cast bx.localShell (triL (shell bx)) 0 a i k (trow bx a)
    (trow_toQ bx a)
  rw [hs, show bx.localShell.certificate 0 = bx.certificate from rfl] at hc
  rw [V3.dot_sub] at h
  have hq : ((V3.dot (LocalKernel.vtx k) (V3.cross (trow bx a) (edgeN bx.certificate i)) -
      V3.dot (LocalKernel.vtx (bx.certificate.index i))
        (V3.cross (trow bx a) (edgeN bx.certificate i)) : ℤ) : ℚ) < 0 := by exact_mod_cast h
  rw [hc] at hq
  have : (0 : ℚ) < triL (shell bx) * (40000 * 40) := by
    have : (0 : ℚ) < triL (shell bx) := by exact_mod_cast hL
    positivity
  exact (Rat.mul_neg_iff_of_pos_left this).mp hq

theorem defectMaskT_eq (idx : VertexIndex) :
    defectMaskT idx = maskK (fun t => t % 8 != idx.val) 72 := by
  simp only [defectMaskT, defectMaskTabL_eq, defectMaskTab, getD_ofFn]

theorem viewControl_comm (bx : Box) (i j : Fin 3) :
    bx.viewControlQuadratic j i = bx.viewControlQuadratic i j := by
  unfold Box.viewControlQuadratic
  by_cases h : i = j
  · subst h; rfl
  · have h' : j ≠ i := fun e => h e.symm
    simp only [h, h', ↓reduceIte]
    have hm : Noperts.ProjectiveView.midpoint (bx.triangle j) (bx.triangle i) =
        Noperts.ProjectiveView.midpoint (bx.triangle i) (bx.triangle j) := by
      funext c; simp [Noperts.ProjectiveView.midpoint, add_comm]
    rw [hm]
    apply RatQuadratic3.ext' <;> simp [RatQuadratic3.scale] <;> ring

theorem relativeBalls_eq (bx : Box) :
    (shell bx).edgeShell.variableBalls = bx.relativeBalls := rfl

/-- The control vector `(i, j)` represents `8 E² S ·` the Bernstein coefficients of the
specification's control quadratic, `S = μ.den · σ₀`. -/
theorem ctlPair_rep (bx : Box) (i j : Fin 3) :
    ∃ d : ℕ → ℤ, PRep KW 27 (ctlPair bx i j).1 d (ctlPair bx i j).2 ∧
      ∀ a b c : Fin 3, (d (9 * a.val + 3 * b.val + c.val) : ℚ) =
        4 * (boxE (shell bx) : ℚ) ^ 2 * (2 * ((bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ))) *
          QuadraticBernstein.coefficient bx.relativeBalls (bx.viewControlQuadratic i j) a b c := by
  unfold ctlPair
  split_ifs with hij
  · subst hij
    obtain ⟨d, r, e⟩ := viewVec_rep bx (trow bx i) 1
    refine ⟨_, (r.smul 2).mono (le_of_eq (by norm_num)), fun a b c => ?_⟩
    have h1 : (2 * d (9 * a.val + 3 * b.val + c.val) : ℤ) =
        bernI (shell bx) (IQ.smul 2 (viewIQ bx (trow bx i) 1)) a.val b.val c.val := by
      rw [e, bernI_smul]
    rw [h1, bernI_cast, relativeBalls_eq, diag_toQ, coefficient_scale]
    ring
  · obtain ⟨dm, rm, em⟩ := viewVec_rep bx ((trow bx i).add (trow bx j)) 4
    obtain ⟨di, ri, ei⟩ := viewVec_rep bx (trow bx i) 1
    obtain ⟨dj, rj, ej⟩ := viewVec_rep bx (trow bx j) 1
    refine ⟨_, rm.add (ri.add rj).neg, fun a b c => ?_⟩
    have h1 : dm (9 * a.val + 3 * b.val + c.val) +
        -(di (9 * a.val + 3 * b.val + c.val) + dj (9 * a.val + 3 * b.val + c.val)) =
        bernI (shell bx) (IQ.sub (viewIQ bx ((trow bx i).add (trow bx j)) 4)
          (IQ.add (viewIQ bx (trow bx i) 1) (viewIQ bx (trow bx j) 1))) a.val b.val c.val := by
      rw [em, ei, ej]
      simp only [IQ.sub, bernI_add, bernI_smul]
      ring
    rw [h1, bernI_cast, relativeBalls_eq, off_toQ bx i j hij, coefficient_scale]
    ring

theorem ctlOk_lower (bx : Box) (i j : Fin 3) (th : ℤ) (hE : 0 < boxE (shell bx))
    (h : ctlOk (ctlPair bx i j).1 (ctlPair bx i j).2 th = true) :
    (th : ℚ) / (8 * (boxE (shell bx) : ℚ) ^ 2 *
        ((bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ))) ≤
      QuadraticBernstein.lower bx.relativeBalls (bx.viewControlQuadratic i j) := by
  have hEq : (0 : ℚ) < boxE (shell bx) := by exact_mod_cast hE
  have hS : (0 : ℚ) < (bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ) := by
    have h1 : (0 : ℚ) < bx.ballMultiplier.den := by exact_mod_cast bx.ballMultiplier.pos
    have h2 : (0 : ℚ) < σ0 bx := by
      have : (0 : ℤ) < σ0 bx := by
        unfold σ0
        have : (0 : ℤ) < triL (shell bx) := by exact_mod_cast lcmList_pos _
        positivity
      exact_mod_cast this
    positivity
  simp only [ctlOk, maskAll_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨d, r, e⟩ := ctlPair_rep bx i j
  have hg := testGeM_sound r h.1 h.2
  apply le_lower
  intro a b c
  have h1 := hg (9 * a.val + 3 * b.val + c.val) (by omega) rfl
  have h2 : (th : ℚ) ≤ d (9 * a.val + 3 * b.val + c.val) := by exact_mod_cast h1
  rw [e] at h2
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- What the core checks give: admissibility and the weighted-defect bound. -/
theorem globalCore_sound (bx : Box) (hints : List ℤ) (h : globalCore bx hints = true) :
    bx.Admissible ∧ (∀ i : Fin 3, 0 ≤ hints.getD i.val 0) ∧
      bx.weightedDefectUpper ≤ (((hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) : ℤ)) : ℚ) /
        (2 * (σ0 bx : ℚ)) := by
  simp only [globalCore, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.mem_finRange, forall_const, true_and, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hL, hE⟩, hμ⟩, htri⟩, hw⟩, hwp⟩, hdir⟩, hdef⟩ := h
  have hLn : 0 < triL (shell bx) := by exact_mod_cast hL
  have hσ : (σ0 bx : ℚ) = (triL (shell bx) : ℚ) ^ 2 * 2560000000000000 := by simp [σ0]
  -- the weighted support defect
  have hslot : ∀ (i a b : Fin 3) (k : VertexIndex), k ≠ bx.certificate.index i →
      ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ hints.getD i.val 0 := by
    intro i a b k hk
    obtain ⟨⟨_, hb⟩, ht⟩ := hdef i
    rw [defectMaskT_eq] at ht
    have hb' : 4 * (1920 * wBoundG bx i * mBoundG bx i + (-hints.getD i.val 0).natAbs) <
        2 ^ (KW - 1) := by rwa [Int.natAbs_neg]
    have hg := testGeM_sound (controlPack_rep bx i).neg hb' ht
      (24 * a.val + 8 * b.val + k.val) (by omega) (by
        have : (24 * a.val + 8 * b.val + k.val) % 8 = k.val := by omega
        rw [this]
        simpa [Fin.val_eq_val] using hk)
    linarith
  have hWD := weightedDefect_le bx (fun i => hints.getD i.val 0) (fun i => (hdef i).1.1) hLn hslot
  have hHq : (((fun i : Fin 3 => hints.getD i.val 0) 0 + (fun i : Fin 3 => hints.getD i.val 0) 1 +
      (fun i : Fin 3 => hints.getD i.val 0) 2 : ℤ) : ℚ) =
      ((hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) : ℤ) : ℚ) := by
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
    push_cast
    ring
  rw [hHq, ← hσ] at hWD
  refine ⟨?_, fun i => (hdef i).1.1, hWD⟩
  refine ⟨signedTriangle_of_T (shell bx) hL htri, fun i => ?_, ?_, fun i => ?_, ?_⟩
  · -- weights are nonnegative
    simp only [Box.weightLower, AtlasProjectiveLocalCertificate.Box.weightLower,
      LocalKernel.supportError_eq, sub_zero, AtlasProjectiveEdgeCertificate.min3, le_min_iff]
    exact ⟨weightAt_nonneg bx hLn 0 i (hw i 0), weightAt_nonneg bx hLn 1 i (hw i 1),
      weightAt_nonneg bx hLn 2 i (hw i 2)⟩
  · -- some weight is positive
    obtain ⟨i, hi⟩ := hwp
    refine ⟨i, ?_⟩
    simp only [Box.weightLower, AtlasProjectiveLocalCertificate.Box.weightLower,
      LocalKernel.supportError_eq, sub_zero, AtlasProjectiveEdgeCertificate.min3, lt_min_iff]
    exact ⟨weightAt_pos bx hLn 0 i (hi 0), weightAt_pos bx hLn 1 i (hi 1),
      weightAt_pos bx hLn 2 i (hi 2)⟩
  · -- direction witnesses
    obtain ⟨htie, hs⟩ := hdir i
    simp only [Box.supportUpper, AtlasProjectiveLocalCertificate.Box.supportUpper, htie,
      ↓reduceIte, LocalKernel.supportError_eq, add_zero, AtlasProjectiveEdgeCertificate.max3,
      max_lt_iff]
    exact ⟨supportAt_neg bx hLn 0 i _ (hs 0), supportAt_neg bx hLn 1 i _ (hs 1),
      supportAt_neg bx hLn 2 i _ (hs 2)⟩
  · -- the ball multiplier
    exact Rat.num_nonneg.mp hμ

theorem validGlobalK_sound (bx : Box) (hints : List ℤ) (h : validGlobalK bx hints = true) :
    bx.Valid := by
  simp only [validGlobalK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hcore, hctl⟩ := h
  obtain ⟨hadm, hh0, hWD⟩ := globalCore_sound bx hints hcore
  have hcore' := hcore
  simp only [globalCore, Bool.and_eq_true, decide_eq_true_eq] at hcore'
  have hL : (0 : ℤ) < triL (shell bx) := hcore'.1.1.1.1.1.1.1
  have hE : 0 < boxE (shell bx) := hcore'.1.1.1.1.1.1.2
  set μ := bx.ballMultiplier with hμdef
  set H : ℤ := hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) with hH
  set th := ceilDiv (4 * (μ.den : ℤ) * dBoundNum (shell bx) * H * 10 ^ 10 +
    2400 * (μ.den : ℤ) * σ0 bx * dBoundNum (shell bx)) (10 ^ 10) with hth
  have hLq : (0 : ℚ) < triL (shell bx) := by exact_mod_cast hL
  have hEq : (0 : ℚ) < boxE (shell bx) := by exact_mod_cast hE
  have hσ : (σ0 bx : ℚ) = (triL (shell bx) : ℚ) ^ 2 * 2560000000000000 := by simp [σ0]
  have hS : (0 : ℚ) < (μ.den : ℚ) * (σ0 bx : ℚ) := by
    rw [hσ]; have : (0 : ℚ) < μ.den := by exact_mod_cast μ.pos
    positivity
  set S : ℚ := (μ.den : ℚ) * (σ0 bx : ℚ) with hSdef
  set X : ℚ := (th : ℚ) / (8 * (boxE (shell bx) : ℚ) ^ 2 * S) with hX
  have lc := fun p (hp : p ∈ ctlIndices) => ctlOk_lower bx p.1 p.2 th hE (hctl p hp)
  have hbern : X ≤ bx.bernsteinDisplacementLower := by
    have c10 := viewControl_comm bx 0 1
    have c20 := viewControl_comm bx 0 2
    have c21 := viewControl_comm bx 1 2
    have l00 := lc (0, 0) (by simp [ctlIndices])
    have l11 := lc (1, 1) (by simp [ctlIndices])
    have l22 := lc (2, 2) (by simp [ctlIndices])
    have l01 := lc (0, 1) (by simp [ctlIndices])
    have l02 := lc (0, 2) (by simp [ctlIndices])
    have l12 := lc (1, 2) (by simp [ctlIndices])
    simp only [Box.bernsteinDisplacementLower, AtlasProjectiveEdgeCertificate.min3, le_min_iff,
      c10, c20, c21]
    exact ⟨⟨l00, l01, l02⟩, ⟨l01, l11, l12⟩, ⟨l02, l12, l22⟩⟩
  refine ⟨hadm, ?_⟩
  have hcert : bx.bernsteinDisplacementLower ≤ bx.certifiedDisplacementLower :=
    le_max_right _ _
  have hdB : bx.dBound = (dBoundNum (shell bx) : ℚ) / (boxE (shell bx) : ℚ) ^ 2 :=
    dBound_eq (shell bx)
  have hdB0 : 0 ≤ bx.dBound := by
    have h1 := sq_nonneg (AtlasEdgeCertificate.endpointAbsBound bx.interval.min.x
      bx.interval.max.x)
    have h2 := sq_nonneg (AtlasEdgeCertificate.endpointAbsBound bx.interval.min.y
      bx.interval.max.y)
    have h3 := sq_nonneg (AtlasEdgeCertificate.endpointAbsBound bx.interval.min.z
      bx.interval.max.z)
    simp only [Box.dBound]
    linarith
  have hdisp : bx.displacementError = 300 * bx.dBound * (1 / 10 ^ 10) := by
    simp [Box.displacementError, RationalApprox.κℚ]
  have hceil := le_ceilDiv_mul (4 * (μ.den : ℤ) * dBoundNum (shell bx) * H * 10 ^ 10 +
    2400 * (μ.den : ℤ) * σ0 bx * dBoundNum (shell bx)) (10 ^ 10) (by norm_num)
  rw [← hth] at hceil
  have hceilq : (4 * (μ.den : ℚ) * dBoundNum (shell bx) * H * 10 ^ 10 +
      2400 * (μ.den : ℚ) * σ0 bx * dBoundNum (shell bx)) ≤ (th : ℚ) * 10 ^ 10 := by
    exact_mod_cast hceil
  have hσq : (0 : ℚ) < σ0 bx := by rw [hσ]; exact mul_pos (pow_pos hLq 2) (by norm_num)
  have hWD' : bx.dBound * bx.weightedDefectUpper ≤ bx.dBound * ((H : ℚ) / (2 * σ0 bx)) :=
    mul_le_mul_of_nonneg_left hWD hdB0
  have key : 300 * bx.dBound * (1 / 10 ^ 10) + bx.dBound * ((H : ℚ) / (2 * σ0 bx)) ≤ X := by
    rw [hX, le_div_iff₀ (mul_pos (mul_pos (by norm_num) (pow_pos hEq 2)) hS), hdB]
    have e : ((300 : ℚ) * (dBoundNum (shell bx) / (boxE (shell bx) : ℚ) ^ 2) * (1 / 10 ^ 10) +
        dBoundNum (shell bx) / (boxE (shell bx) : ℚ) ^ 2 * (H / (2 * σ0 bx))) *
        (8 * (boxE (shell bx) : ℚ) ^ 2 * ((μ.den : ℚ) * σ0 bx)) =
        (4 * (μ.den : ℚ) * dBoundNum (shell bx) * H * 10 ^ 10 +
          2400 * (μ.den : ℚ) * σ0 bx * dBoundNum (shell bx)) / 10 ^ 10 := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by norm_num)]
    exact hceilq
  rw [hdisp]
  linarith

end Noperts.Stellated.ChartKernelG
