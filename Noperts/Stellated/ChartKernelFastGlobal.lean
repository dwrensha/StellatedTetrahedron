module

public import Noperts.Stellated.ChartKernelFast

@[expose] public section

/-!
# A faster kernel checker for global chart leaves

`globalZ bx bxR hints` decides the conditions of `ChartKernelG.validGlobalK bx hints` in
`Nat`-pair arithmetic, with the packed Bernstein vectors of `ChartKernelFast`.  The box
`bxR` is `bx` with a fixed interval and view (so that certificate-only data, like the
contact quadratics, is shared between leaves by the kernel's cache); only its certificate,
chart and inner indices are used.
-/

namespace Noperts.Stellated.ChartKernelF

open ChartKernel ChartKernelG PackedSlots AtlasProjectiveEdgeCertificate AtlasProjectiveView ZP
open LocalKernel (V3 edgeN wcN)

/-! ## Pair vectors -/

structure V3Z where
  x : Z
  y : Z
  z : Z

namespace V3Z

def toV3 (a : V3Z) : V3 := ⟨toZ a.x, toZ a.y, toZ a.z⟩
def ofV3 (a : V3) : V3Z := ⟨ofI a.x, ofI a.y, ofI a.z⟩
def dot (a b : V3Z) : Z := add (add (mul a.x b.x) (mul a.y b.y)) (mul a.z b.z)
def cross (a b : V3Z) : V3Z :=
  ⟨sub (mul a.y b.z) (mul a.z b.y), sub (mul a.z b.x) (mul a.x b.z), sub (mul a.x b.y) (mul a.y b.x)⟩
def vadd (a b : V3Z) : V3Z := ⟨add a.x b.x, add a.y b.y, add a.z b.z⟩
def sz3 (a : V3Z) : ℕ := Nat.add (Nat.add (sz a.x) (sz a.y)) (sz a.z)

@[simp] theorem toV3_ofV3 (a : V3) : toV3 (ofV3 a) = a := by simp [toV3, ofV3]
theorem toZ_dot (a b : V3Z) : toZ (dot a b) = V3.dot a.toV3 b.toV3 := by
  simp [dot, V3.dot, toV3]
theorem toV3_cross (a b : V3Z) : (cross a b).toV3 = V3.cross a.toV3 b.toV3 := by
  simp [cross, V3.cross, toV3, LocalKernel.int_sub_eq]
theorem toV3_vadd (a b : V3Z) : (vadd a b).toV3 = V3.add a.toV3 b.toV3 := by
  simp [vadd, V3.add, toV3]

end V3Z

/-! ## Frame data -/

/-- `qScale L q` as a pair. -/
def qS (L : ℕ) (q : ℚ) : Z :=
  match q.num with
  | .ofNat n => (Nat.mul n (Nat.div L q.den), 0)
  | .negSucc n => (0, Nat.mul (Nat.succ n) (Nat.div L q.den))

theorem toZ_qS (L : ℕ) (q : ℚ) : toZ (qS L q) = qScale L q := by
  unfold qS qScale
  have hd : Nat.div L q.den = L / q.den := rfl
  rw [hd]
  generalize L / q.den = m
  cases h : q.num <;> simp [ZP.toZ, Nat.mul_eq, Int.negSucc_eq]
  ring

/-- Row `a` of the scaled view triangle. -/
def rowZ (L : ℕ) (tri : Triangle ℚ) (a : Fin 3) : V3Z := ⟨qS L (tri a 0), qS L (tri a 1), qS L (tri a 2)⟩

theorem rowZ_toV3 (bx : AtlasProjectiveGlobalCertificate.Box) (a : Fin 3) :
    (rowZ (triL (shell bx)) bx.triangle a).toV3 = trow bx a := by
  simp only [rowZ, V3Z.toV3, toZ_qS, trow]
  rfl

/-- The sign of coordinate `c` for root `root` is negative iff bit `2 - c` is set. -/
def rsNeg (root : Fin 8) (c : ℕ) : Bool := Nat.testBit root.val (2 - c)

def sgnZ (root : Fin 8) (c : ℕ) (a : Z) : Z := bif rsNeg root c then neg a else a

theorem toZ_sgnZ (root : Fin 8) (c : Fin 3) (a : Z) :
    toZ (sgnZ root c.val a) = (rootSign root c).num * toZ a := by
  unfold sgnZ rsNeg
  fin_cases root <;> fin_cases c <;> simp (config := { decide := true }) [rootSign, ZP.toZ, neg]

/-- The view triangle conditions for one scaled row. -/
def triOkZ (root : Fin 8) (L : ℕ) (r : V3Z) : Bool :=
  let a := sgnZ root 0 r.x
  let b := sgnZ root 1 r.y
  let c := sgnZ root 2 r.z
  nonneg a && nonneg b && nonneg c && eqZ (add (add a b) c) (L, 0)

theorem triOkZ_sound (bx : AtlasProjectiveGlobalCertificate.Box) (i : Fin 3)
    (h : triOkZ bx.root (triL (shell bx)) (rowZ (triL (shell bx)) bx.triangle i) = true) :
    (∀ c : Fin 3, 0 ≤ (rootSign bx.root c).num * T (shell bx) i c) ∧
      (rootSign bx.root 0).num * T (shell bx) i 0 + (rootSign bx.root 1).num * T (shell bx) i 1 +
        (rootSign bx.root 2).num * T (shell bx) i 2 = triL (shell bx) := by
  have hT : ∀ c : Fin 3, T (shell bx) i c = toZ (qS (triL (shell bx)) (bx.triangle i c)) := by
    intro c; rw [toZ_qS]; rfl
  simp only [triOkZ, Bool.and_eq_true, nonneg_iff, eqZ_iff, toZ_add, toZ_mk0] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have e0 := toZ_sgnZ bx.root 0 (rowZ (triL (shell bx)) bx.triangle i).x
  have e1 := toZ_sgnZ bx.root 1 (rowZ (triL (shell bx)) bx.triangle i).y
  have e2 := toZ_sgnZ bx.root 2 (rowZ (triL (shell bx)) bx.triangle i).z
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  simp only [rowZ] at e0 e1 e2 h0 h1 h2 h3
  rw [e0] at h0 h3; rw [e1] at h1 h3; rw [e2] at h2 h3
  refine ⟨fun c => ?_, ?_⟩
  · fin_cases c
    · rw [hT]; exact h0
    · rw [hT]; exact h1
    · rw [hT]; exact h2
  · rw [hT, hT, hT]; exact h3

/-! ## The core facts -/

open AtlasProjectiveGlobalCertificate in
/-- `globalCore_sound`, from the facts its checks establish. -/
theorem core_of_facts (bx : AtlasProjectiveGlobalCertificate.Box) (h : Fin 3 → ℤ) (hL : 0 < (triL (shell bx) : ℤ))
    (hμ : 0 ≤ bx.ballMultiplier.num)
    (htri : ∀ i : Fin 3, (∀ c : Fin 3, 0 ≤ (rootSign bx.root c).num * T (shell bx) i c) ∧
      (rootSign bx.root 0).num * T (shell bx) i 0 + (rootSign bx.root 1).num * T (shell bx) i 1 +
        (rootSign bx.root 2).num * T (shell bx) i 2 = triL (shell bx))
    (hw : ∀ i a : Fin 3, 0 ≤ V3.dot (trow bx a) (wcN bx.certificate i))
    (hwp : ∃ i : Fin 3, ∀ a : Fin 3, 0 < V3.dot (trow bx a) (wcN bx.certificate i))
    (hdir : ∀ i : Fin 3, ¬ bx.localShell.exactSupportTie 0 i (bx.certificate.nonzeroWitness i) ∧
      ∀ a : Fin 3, V3.dot (V3.sub (LocalKernel.vtx (bx.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bx.certificate.index i))) (V3.cross (trow bx a) (edgeN bx.certificate i)) < 0)
    (hh : ∀ i, 0 ≤ h i)
    (hslot : ∀ (i a b : Fin 3) (k : VertexIndex), k ≠ bx.certificate.index i →
      ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ h i) :
    bx.Admissible ∧ bx.weightedDefectUpper ≤ ((h 0 + h 1 + h 2 : ℤ) : ℚ) / (2 * (σ0 bx : ℚ)) := by
  have hLn : 0 < triL (shell bx) := by exact_mod_cast hL
  have hσ : (σ0 bx : ℚ) = (triL (shell bx) : ℚ) ^ 2 * 2560000000000000 := by simp [σ0]
  have hWD := weightedDefect_le bx h hh hLn hslot
  rw [← hσ] at hWD
  refine ⟨?_, hWD⟩
  refine ⟨signedTriangle_of_T (shell bx) hL htri, fun i => ?_, ?_, fun i => ?_, ?_⟩
  · simp only [Box.weightLower, AtlasProjectiveLocalCertificate.Box.weightLower,
      LocalKernel.supportError_eq, sub_zero, AtlasProjectiveEdgeCertificate.min3, le_min_iff]
    exact ⟨weightAt_nonneg bx hLn 0 i (hw i 0), weightAt_nonneg bx hLn 1 i (hw i 1),
      weightAt_nonneg bx hLn 2 i (hw i 2)⟩
  · obtain ⟨i, hi⟩ := hwp
    refine ⟨i, ?_⟩
    simp only [AtlasProjectiveGlobalCertificate.Box.weightLower,
      AtlasProjectiveLocalCertificate.Box.weightLower,
      LocalKernel.supportError_eq, sub_zero, AtlasProjectiveEdgeCertificate.min3, lt_min_iff]
    exact ⟨weightAt_pos bx hLn 0 i (hi 0), weightAt_pos bx hLn 1 i (hi 1),
      weightAt_pos bx hLn 2 i (hi 2)⟩
  · obtain ⟨htie, hs⟩ := hdir i
    simp only [AtlasProjectiveGlobalCertificate.Box.supportUpper,
      AtlasProjectiveLocalCertificate.Box.supportUpper, htie,
      ↓reduceIte, LocalKernel.supportError_eq, add_zero, AtlasProjectiveEdgeCertificate.max3,
      max_lt_iff]
    exact ⟨supportAt_neg bx hLn 0 i _ (hs 0), supportAt_neg bx hLn 1 i _ (hs 1),
      supportAt_neg bx hLn 2 i _ (hs 2)⟩
  · exact Rat.num_nonneg.mp hμ

/-! ## Weighted support defects -/

def P8a : ℕ := 2 ^ (KW * 8)
def P8b : ℕ := 2 ^ (2 * (KW * 8))
def P24a : ℕ := 2 ^ (KW * 24)
def P24b : ℕ := 2 ^ (2 * (KW * 24))

/-- The packed slots of `controlPack` for contact `i`, from the weights `w_a` and the normals
`m_a = t_a × e_i` of the three triangle rows. -/
def ctlPackZ (wa wb wc : Z) (ma mb mc : V3Z) (s : VertexIndex) : ℕ × ℕ :=
  let d0 := deltaT s 0
  let d1 := deltaT s 1
  let d2 := deltaT s 2
  let S := padd (pmul (pk3 P8a P8b ma.x mb.x mc.x) d0)
    (padd (pmul (pk3 P8a P8b ma.y mb.y mc.y) d1) (pmul (pk3 P8a P8b ma.z mb.z mc.z) d2))
  let W8 := pk3 P8a P8b wa wb wc
  let P1 := pmul (pk3 P24a P24b wa wb wc) S
  let P2 := padd (pmul (pk3 P24a P24b ma.x mb.x mc.x) (pmul W8 d0))
    (padd (pmul (pk3 P24a P24b ma.y mb.y mc.y) (pmul W8 d1))
      (pmul (pk3 P24a P24b ma.z mb.z mc.z) (pmul W8 d2)))
  padd P1 P2

def mbZ (ma mb mc : V3Z) : ℕ := Nat.add (Nat.add ma.sz3 mb.sz3) mc.sz3
def wbZ (wa wb wc : Z) : ℕ := Nat.add (Nat.add (sz wa) (sz wb)) (sz wc)

theorem pmul_eq (A B : ℕ × ℕ) : pmul A B = pairMul A B := rfl

open AtlasProjectiveGlobalCertificate in
theorem ctlPackZ_rep (bx : AtlasProjectiveGlobalCertificate.Box) (i : Fin 3) (wa wb wc : Z) (ma mb mc : V3Z)
    (hwa : toZ wa = V3.dot (trow bx 0) (wcN bx.certificate i))
    (hwb : toZ wb = V3.dot (trow bx 1) (wcN bx.certificate i))
    (hwc : toZ wc = V3.dot (trow bx 2) (wcN bx.certificate i))
    (hma : ma.toV3 = V3.cross (trow bx 0) (edgeN bx.certificate i))
    (hmb : mb.toV3 = V3.cross (trow bx 1) (edgeN bx.certificate i))
    (hmc : mc.toV3 = V3.cross (trow bx 2) (edgeN bx.certificate i)) :
    PRep KW 72 (ctlPackZ wa wb wc ma mb mc (bx.certificate.index i)) (ctlSlot bx i)
      (1920 * wbZ wa wb wc * mbZ ma mb mc) := by
  set s := bx.certificate.index i
  set Mm := mbZ ma mb mc
  set Mw := wbZ wa wb wc
  have hd : ∀ d : Fin 3, PRep KW 8 (deltaT s d) (δN s d) 40 :=
    fun d => by rw [deltaT_eq]; exact pmPack_rep KW 8 _ 40 (δN_le _ d)
  have szx : ∀ v : V3Z, sz v.x ≤ v.sz3 := fun v => by simp only [V3Z.sz3, Nat.add_eq]; omega
  have szy : ∀ v : V3Z, sz v.y ≤ v.sz3 := fun v => by simp only [V3Z.sz3, Nat.add_eq]; omega
  have szz : ∀ v : V3Z, sz v.z ≤ v.sz3 := fun v => by simp only [V3Z.sz3, Nat.add_eq]; omega
  have ha : ma.sz3 ≤ Mm := by simp only [Mm, mbZ, Nat.add_eq]; omega
  have hb : mb.sz3 ≤ Mm := by simp only [Mm, mbZ, Nat.add_eq]; omega
  have hc : mc.sz3 ≤ Mm := by simp only [Mm, mbZ, Nat.add_eq]; omega
  -- the slot functions of the packed normals: coordinate `d` of `m_j`
  have hmG : ∀ (d : Fin 3) (f : V3Z → Z), (∀ v : V3Z, toZ (f v) = V3.get v.toV3 d) →
      ∀ j, sel3Z (toZ (f ma)) (toZ (f mb)) (toZ (f mc)) j = mG bx i d j := by
    intro d f hf j
    simp only [sel3Z, hf, hma, hmb, hmc, mG]
    rcases j with _ | _ | _ | j <;> simp
  have hgx : ∀ v : V3Z, toZ v.x = V3.get v.toV3 0 := fun v => rfl
  have hgy : ∀ v : V3Z, toZ v.y = V3.get v.toV3 1 := fun v => rfl
  have hgz : ∀ v : V3Z, toZ v.z = V3.get v.toV3 2 := fun v => rfl
  have hm8 : ∀ (d : Fin 3) (f : V3Z → Z), (∀ v, sz (f v) ≤ v.sz3) →
      (∀ v : V3Z, toZ (f v) = V3.get v.toV3 d) →
      PRep (KW * 8) 3 (pk3 P8a P8b (f ma) (f mb) (f mc)) (mG bx i d) Mm := by
    intro d f hs hf
    exact (pk3_rep (KW * 8) _ _ _ Mm ((hs ma).trans ha) ((hs mb).trans hb) ((hs mc).trans hc)).congr
      (hmG d f hf)
  have hm24 : ∀ (d : Fin 3) (f : V3Z → Z), (∀ v, sz (f v) ≤ v.sz3) →
      (∀ v : V3Z, toZ (f v) = V3.get v.toV3 d) →
      PRep (KW * 24) 3 (pk3 P24a P24b (f ma) (f mb) (f mc)) (mG bx i d) Mm := by
    intro d f hs hf
    exact (pk3_rep (KW * 24) _ _ _ Mm ((hs ma).trans ha) ((hs mb).trans hb) ((hs mc).trans hc)).congr
      (hmG d f hf)
  have hwG : ∀ j, sel3Z (toZ wa) (toZ wb) (toZ wc) j = wG bx i j := by
    intro j
    simp only [sel3Z, hwa, hwb, hwc, wG]
    rcases j with _ | _ | _ | j <;> simp
  have hw8 : PRep (KW * 8) 3 (pk3 P8a P8b wa wb wc) (wG bx i) Mw :=
    (pk3_rep (KW * 8) wa wb wc Mw (by simp only [Mw, wbZ, Nat.add_eq]; omega)
      (by simp only [Mw, wbZ, Nat.add_eq]; omega) (by simp only [Mw, wbZ, Nat.add_eq]; omega)).congr hwG
  have hw24 : PRep (KW * 24) 3 (pk3 P24a P24b wa wb wc) (wG bx i) Mw :=
    (pk3_rep (KW * 24) wa wb wc Mw (by simp only [Mw, wbZ, Nat.add_eq]; omega)
      (by simp only [Mw, wbZ, Nat.add_eq]; omega) (by simp only [Mw, wbZ, Nat.add_eq]; omega)).congr hwG
  have hS := (pairMul_rep (hm8 0 V3Z.x szx hgx) (hd 0)).add ((pairMul_rep (hm8 1 V3Z.y szy hgy) (hd 1)).add
    (pairMul_rep (hm8 2 V3Z.z szz hgz) (hd 2)))
  have hP1 := pairMul_rep24 hw24 hS
  have hY := fun d => pairMul_rep hw8 (hd d)
  have hP2 := (pairMul_rep24 (hm24 0 V3Z.x szx hgx) (hY 0)).add
    ((pairMul_rep24 (hm24 1 V3Z.y szy hgy) (hY 1)).add (pairMul_rep24 (hm24 2 V3Z.z szz hgz) (hY 2)))
  refine ((hP1.add hP2).congr fun t => ?_).mono ?_
  · simp only [ctlSlot, supG]
    ring
  · have e : 2 * Mw * (2 * Mm * 40 + (2 * Mm * 40 + 2 * Mm * 40)) + (2 * Mm * (2 * Mw * 40) +
        (2 * Mm * (2 * Mw * 40) + 2 * Mm * (2 * Mw * 40))) = 960 * (Mw * Mm) := by ring
    have e2 : 1920 * Mw * Mm = 1920 * (Mw * Mm) := by ring
    rw [e, e2]
    omega

/-! ## View and control vectors -/

/-- A packed vector with its slot bound. -/
structure BQ where
  u : ℕ × ℕ
  m : ℕ

/-- `Σᵢ Σ_c (μd xᵢ t_c) B_{ic} + kc B_c`: the packed Bernstein vector of `viewIQ` at view
`t`, given `xᵢ = t · wcᵢ`. -/
def rowV (μd : ℕ) (t : V3Z) (x : Z) (Ba Bb Bc : BQ) : BQ :=
  let k0 := nmul μd (mul x t.x)
  let k1 := nmul μd (mul x t.y)
  let k2 := nmul μd (mul x t.z)
  ⟨padd (psm k0 Ba.u) (padd (psm k1 Bb.u) (psm k2 Bc.u)),
    Nat.add (Nat.mul (sz k0) Ba.m) (Nat.add (Nat.mul (sz k1) Bb.m) (Nat.mul (sz k2) Bc.m))⟩

def viewZ (μd : ℕ) (kc : Z) (t : V3Z) (x0 x1 x2 : Z)
    (B00 B01 B02 B10 B11 B12 B20 B21 B22 Bc : BQ) : BQ :=
  let r0 := rowV μd t x0 B00 B01 B02
  let r1 := rowV μd t x1 B10 B11 B12
  let r2 := rowV μd t x2 B20 B21 B22
  ⟨padd (padd r0.u (padd r1.u r2.u)) (psm kc Bc.u),
    Nat.add (Nat.add r0.m (Nat.add r1.m r2.m)) (Nat.mul (sz kc) Bc.m)⟩

theorem rowV_rep {μd : ℕ} {t : V3Z} {x : Z} {Ba Bb Bc : BQ} {fa fb fc : ℕ → ℤ}
    (ha : PRep KW 27 Ba.u fa Ba.m) (hb : PRep KW 27 Bb.u fb Bb.m) (hc : PRep KW 27 Bc.u fc Bc.m) :
    PRep KW 27 (rowV μd t x Ba Bb Bc).u
      (fun s => (μd : ℤ) * toZ x * (toZ t.x * fa s + toZ t.y * fb s + toZ t.z * fc s))
      (rowV μd t x Ba Bb Bc).m := by
  refine ((ha.psm _).padd ((hb.psm _).padd (hc.psm _))).congr fun s => ?_
  simp only [toZ_nmul, toZ_mul]
  ring

theorem viewZ_rep {μd : ℕ} {kc : Z} {t : V3Z} {x0 x1 x2 : Z}
    {B00 B01 B02 B10 B11 B12 B20 B21 B22 Bc : BQ}
    {f00 f01 f02 f10 f11 f12 f20 f21 f22 fc : ℕ → ℤ}
    (h00 : PRep KW 27 B00.u f00 B00.m) (h01 : PRep KW 27 B01.u f01 B01.m)
    (h02 : PRep KW 27 B02.u f02 B02.m) (h10 : PRep KW 27 B10.u f10 B10.m)
    (h11 : PRep KW 27 B11.u f11 B11.m) (h12 : PRep KW 27 B12.u f12 B12.m)
    (h20 : PRep KW 27 B20.u f20 B20.m) (h21 : PRep KW 27 B21.u f21 B21.m)
    (h22 : PRep KW 27 B22.u f22 B22.m) (hc : PRep KW 27 Bc.u fc Bc.m) :
    PRep KW 27 (viewZ μd kc t x0 x1 x2 B00 B01 B02 B10 B11 B12 B20 B21 B22 Bc).u
      (fun s => (μd : ℤ) * toZ x0 * (toZ t.x * f00 s + toZ t.y * f01 s + toZ t.z * f02 s) +
        ((μd : ℤ) * toZ x1 * (toZ t.x * f10 s + toZ t.y * f11 s + toZ t.z * f12 s) +
          (μd : ℤ) * toZ x2 * (toZ t.x * f20 s + toZ t.y * f21 s + toZ t.z * f22 s)) +
        toZ kc * fc s)
      (viewZ μd kc t x0 x1 x2 B00 B01 B02 B10 B11 B12 B20 B21 B22 Bc).m :=
  ((rowV_rep h00 h01 h02).padd ((rowV_rep h10 h11 h12).padd (rowV_rep h20 h21 h22))).padd
    (hc.psm kc)

/-- The diagonal and off-diagonal control vectors. -/
def diagZ (v : BQ) : BQ := ⟨psm (2, 0) v.u, Nat.mul (sz ((2, 0) : Z)) v.m⟩
def offZ (vm vi vj : BQ) : BQ :=
  ⟨padd vm.u ((padd vi.u vj.u).2, (padd vi.u vj.u).1), Nat.add vm.m (Nat.add vi.m vj.m)⟩

open AtlasProjectiveGlobalCertificate in
/-- A Bernstein lower bound of the control quadratic `(i, j)` from bounds on the Bernstein
coefficients of `ctlQ` (`ctlOk_lower`). -/
theorem ctl_lower (bx : AtlasProjectiveGlobalCertificate.Box) (i j : Fin 3) (th : ℤ) (hE : 0 < boxE (shell bx))
    (h : ∀ a b c : Fin 3, th ≤ bernI (shell bx) (if i = j then IQ.smul 2 (viewIQ bx (trow bx i) 1)
      else IQ.sub (viewIQ bx (V3.add (trow bx i) (trow bx j)) 4)
        (IQ.add (viewIQ bx (trow bx i) 1) (viewIQ bx (trow bx j) 1))) a.val b.val c.val) :
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
  apply le_lower
  intro a b c
  have h1 := h a b c
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte] at h1
    have h2 : (th : ℚ) ≤ (bernI (shell bx) (IQ.smul 2 (viewIQ bx (trow bx i) 1)) a.val b.val c.val
        : ℚ) := by exact_mod_cast h1
    rw [bernI_cast, relativeBalls_eq, diag_toQ, coefficient_scale] at h2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · simp only [hij, ↓reduceIte] at h1
    have h2 : (th : ℚ) ≤ (bernI (shell bx) (IQ.sub (viewIQ bx (V3.add (trow bx i) (trow bx j)) 4)
        (IQ.add (viewIQ bx (trow bx i) 1) (viewIQ bx (trow bx j) 1))) a.val b.val c.val : ℚ) := by
      exact_mod_cast h1
    rw [bernI_cast, relativeBalls_eq, off_toQ bx i j hij, coefficient_scale] at h2
    rw [div_le_iff₀ (by positivity)]
    nlinarith

open AtlasProjectiveGlobalCertificate in
/-- The conclusion of `validGlobalK_sound` from the core facts and the control bounds. -/
theorem valid_of_ctl (bx : AtlasProjectiveGlobalCertificate.Box) (hints : List ℤ) (hadm : bx.Admissible)
    (hWD : bx.weightedDefectUpper ≤ (((hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) : ℤ)) : ℚ) /
        (2 * (σ0 bx : ℚ)))
    (hL : (0 : ℤ) < triL (shell bx)) (hE : 0 < boxE (shell bx))
    (hctl : ∀ i j : Fin 3, ((ceilDiv (4 * (bx.ballMultiplier.den : ℤ) * dBoundNum (shell bx) *
        (hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0)) * 10 ^ 10 +
        2400 * (bx.ballMultiplier.den : ℤ) * σ0 bx * dBoundNum (shell bx)) (10 ^ 10) : ℤ) : ℚ) /
        (8 * (boxE (shell bx) : ℚ) ^ 2 * ((bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ))) ≤
      QuadraticBernstein.lower bx.relativeBalls (bx.viewControlQuadratic i j)) :
    bx.Valid := by
  set μ := bx.ballMultiplier with hμdef
  set H : ℤ := hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) with hH
  set th := ceilDiv (4 * (μ.den : ℤ) * dBoundNum (shell bx) * H * 10 ^ 10 +
    2400 * (μ.den : ℤ) * σ0 bx * dBoundNum (shell bx)) (10 ^ 10) with hth
  have lc := fun (p : Fin 3 × Fin 3) (_ : p ∈ ctlIndices) => hctl p.1 p.2
  have hLq : (0 : ℚ) < triL (shell bx) := by exact_mod_cast hL
  have hEq : (0 : ℚ) < boxE (shell bx) := by exact_mod_cast hE
  have hσ : (σ0 bx : ℚ) = (triL (shell bx) : ℚ) ^ 2 * 2560000000000000 := by simp [σ0]
  have hS : (0 : ℚ) < (μ.den : ℚ) * (σ0 bx : ℚ) := by
    rw [hσ]; have : (0 : ℚ) < μ.den := by exact_mod_cast μ.pos
    positivity
  set S : ℚ := (μ.den : ℚ) * (σ0 bx : ℚ) with hSdef
  set X : ℚ := (th : ℚ) / (8 * (boxE (shell bx) : ℚ) ^ 2 * S) with hX
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


/-! ## The checker -/

open AtlasProjectiveGlobalCertificate in
/-- The conditions of `validGlobalK bx hints`; `bxR` must have the chart, certificate and
inner indices of `bx` (it serves certificate-only data). -/
def globalZ (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hints : List ℤ) : Bool :=
  let sh := shell bx
  let L := triL sh
  let E := boxE sh
  let root := bx.root
  let t0 := rowZ L bx.triangle 0
  let t1 := rowZ L bx.triangle 1
  let t2 := rowZ L bx.triangle 2
  let cert := bxR.certificate
  let e0 := V3Z.ofV3 (edgeN cert 0)
  let e1 := V3Z.ofV3 (edgeN cert 1)
  let e2 := V3Z.ofV3 (edgeN cert 2)
  let c0 := V3Z.ofV3 (wcN cert 0)
  let c1 := V3Z.ofV3 (wcN cert 1)
  let c2 := V3Z.ofV3 (wcN cert 2)
  let w00 := V3Z.dot t0 c0
  let w01 := V3Z.dot t0 c1
  let w02 := V3Z.dot t0 c2
  let w10 := V3Z.dot t1 c0
  let w11 := V3Z.dot t1 c1
  let w12 := V3Z.dot t1 c2
  let w20 := V3Z.dot t2 c0
  let w21 := V3Z.dot t2 c1
  let w22 := V3Z.dot t2 c2
  let m00 := V3Z.cross t0 e0
  let m01 := V3Z.cross t0 e1
  let m02 := V3Z.cross t0 e2
  let m10 := V3Z.cross t1 e0
  let m11 := V3Z.cross t1 e1
  let m12 := V3Z.cross t1 e2
  let m20 := V3Z.cross t2 e0
  let m21 := V3Z.cross t2 e1
  let m22 := V3Z.cross t2 e2
  let dirOk := fun (i : Fin 3) (ma mb mc : V3Z) =>
    let d := V3Z.ofV3 (V3.sub (LocalKernel.vtx (cert.nonzeroWitness i)) (LocalKernel.vtx (cert.index i)))
    !decide (bxR.localShell.exactSupportTie 0 i (cert.nonzeroWitness i)) &&
      isNeg (V3Z.dot d ma) && isNeg (V3Z.dot d mb) && isNeg (V3Z.dot d mc)
  let defOk := fun (i : Fin 3) (wa wb wc : Z) (ma mb mc : V3Z) =>
    let h := hints.getD i.val 0
    decide (0 ≤ h) &&
      Nat.blt (Nat.mul 4 (Nat.add (Nat.mul (Nat.mul 1920 (wbZ wa wb wc)) (mbZ ma mb mc)) h.natAbs)) KK &&
      testGeZ ((ctlPackZ wa wb wc ma mb mc (cert.index i)).2, (ctlPackZ wa wb wc ma mb mc (cert.index i)).1)
        ones72L (defectMaskT (cert.index i)) (-h)
  -- Bernstein
  let iv := bx.interval
  let lx := qS E (iv.min.get 2)
  let ly := qS E (iv.min.get 3)
  let lz := qS E (iv.min.get 4)
  let P := pbZ E lx ly lz (sub (qS E (iv.max.get 2)) lx) (sub (qS E (iv.max.get 3)) ly)
    (sub (qS E (iv.max.get 4)) lz)
  let B := fun (i c : Fin 3) => (⟨bvZ P (qzOf (cqG bxR i c)), bmZ P (qzOf (cqG bxR i c))⟩ : BQ)
  let B00 := B 0 0
  let B01 := B 0 1
  let B02 := B 0 2
  let B10 := B 1 0
  let B11 := B 1 1
  let B12 := B 1 2
  let B20 := B 2 0
  let B21 := B 2 1
  let B22 := B 2 2
  let Bc : BQ := ⟨bvZ P (qzOf cayI), bmZ P (qzOf cayI)⟩
  let μ := bx.ballMultiplier
  let σ := Nat.mul (Nat.mul L L) 2560000000000000
  let k1 := nmul σ (ofI μ.num)
  let k4 := nmul (Nat.mul 4 σ) (ofI μ.num)
  let view := fun (k : Z) (t : V3Z) (x0 x1 x2 : Z) =>
    viewZ μ.den k t x0 x1 x2 B00 B01 B02 B10 B11 B12 B20 B21 B22 Bc
  let v0 := view k1 t0 w00 w01 w02
  let v1 := view k1 t1 w10 w11 w12
  let v2 := view k1 t2 w20 w21 w22
  let v01 := view k4 (V3Z.vadd t0 t1) (add w00 w10) (add w01 w11) (add w02 w12)
  let v02 := view k4 (V3Z.vadd t0 t2) (add w00 w20) (add w01 w21) (add w02 w22)
  let v12 := view k4 (V3Z.vadd t1 t2) (add w10 w20) (add w11 w21) (add w12 w22)
  let H : ℤ := hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0)
  let dB := dBoundNum sh
  let th := ceilDiv (4 * (μ.den : ℤ) * dB * H * 10 ^ 10 + 2400 * (μ.den : ℤ) * σ0 bx * dB) (10 ^ 10)
  let ok := fun (v : BQ) => bernOkZ v.u v.m th
  Nat.blt 0 L && Nat.blt 0 E && decide (0 ≤ μ.num) &&
    triOkZ root L t0 && triOkZ root L t1 && triOkZ root L t2 &&
    nonneg w00 && nonneg w01 && nonneg w02 && nonneg w10 && nonneg w11 && nonneg w12 &&
    nonneg w20 && nonneg w21 && nonneg w22 &&
    ((pos w00 && pos w10 && pos w20) || (pos w01 && pos w11 && pos w21) ||
      (pos w02 && pos w12 && pos w22)) &&
    dirOk 0 m00 m10 m20 && dirOk 1 m01 m11 m21 && dirOk 2 m02 m12 m22 &&
    defOk 0 w00 w10 w20 m00 m10 m20 && defOk 1 w01 w11 w21 m01 m11 m21 &&
    defOk 2 w02 w12 w22 m02 m12 m22 &&
    ok (diagZ v0) && ok (diagZ v1) && ok (diagZ v2) &&
    ok (offZ v01 v0 v1) && ok (offZ v02 v0 v2) && ok (offZ v12 v1 v2)

/-! ## Soundness -/

section
open AtlasProjectiveGlobalCertificate
variable (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hC : bxR.certificate = bx.certificate)
include hC

theorem w_eq (a i : Fin 3) :
    toZ (V3Z.dot (rowZ (triL (shell bx)) bx.triangle a) (V3Z.ofV3 (wcN bxR.certificate i))) =
      V3.dot (trow bx a) (wcN bx.certificate i) := by
  rw [V3Z.toZ_dot, rowZ_toV3, V3Z.toV3_ofV3, hC]

theorem m_eq (a i : Fin 3) :
    (V3Z.cross (rowZ (triL (shell bx)) bx.triangle a) (V3Z.ofV3 (edgeN bxR.certificate i))).toV3 =
      V3.cross (trow bx a) (edgeN bx.certificate i) := by
  rw [V3Z.toV3_cross, rowZ_toV3, V3Z.toV3_ofV3, hC]

theorem dir_eq (i a : Fin 3) :
    toZ (V3Z.dot (V3Z.ofV3 (V3.sub (LocalKernel.vtx (bxR.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bxR.certificate.index i))))
      (V3Z.cross (rowZ (triL (shell bx)) bx.triangle a) (V3Z.ofV3 (edgeN bxR.certificate i)))) =
      V3.dot (V3.sub (LocalKernel.vtx (bx.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bx.certificate.index i))) (V3.cross (trow bx a) (edgeN bx.certificate i)) := by
  rw [V3Z.toZ_dot, V3Z.toV3_ofV3, m_eq bx bxR hC, hC]

theorem tie_iff (i : Fin 3) (k : VertexIndex) :
    bxR.localShell.exactSupportTie 0 i k ↔ bx.localShell.exactSupportTie 0 i k := by
  simp only [AtlasProjectiveLocalCertificate.Box.exactSupportTie,
    AtlasProjectiveLocalCertificate.AxisCertificate.supportIndex, Box.localShell, hC]

end

open AtlasProjectiveGlobalCertificate in
theorem def_slot (bx : AtlasProjectiveGlobalCertificate.Box) (i : Fin 3) (wa wb wc : Z) (ma mb mc : V3Z)
    (hwa : toZ wa = V3.dot (trow bx 0) (wcN bx.certificate i))
    (hwb : toZ wb = V3.dot (trow bx 1) (wcN bx.certificate i))
    (hwc : toZ wc = V3.dot (trow bx 2) (wcN bx.certificate i))
    (hma : ma.toV3 = V3.cross (trow bx 0) (edgeN bx.certificate i))
    (hmb : mb.toV3 = V3.cross (trow bx 1) (edgeN bx.certificate i))
    (hmc : mc.toV3 = V3.cross (trow bx 2) (edgeN bx.certificate i)) (h : ℤ) (s : VertexIndex)
    (hs : s = bx.certificate.index i)
    (hb : Nat.mul 4 (Nat.add (Nat.mul (Nat.mul 1920 (wbZ wa wb wc)) (mbZ ma mb mc)) h.natAbs) < KK)
    (ht : testGeZ ((ctlPackZ wa wb wc ma mb mc s).2, (ctlPackZ wa wb wc ma mb mc s).1) ones72L
        (defectMaskT s) (-h) = true) :
    ∀ (a b : Fin 3) (k : VertexIndex), k ≠ bx.certificate.index i →
      ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ h := by
  intro a b k hk
  subst hs
  have r := (ctlPackZ_rep bx i wa wb wc ma mb mc hwa hwb hwc hma hmb hmc).neg
  rw [show ones72L = onesL 72 by simp [onesL], testGeZ_eq, defectMaskT_eq] at ht
  have hb' : 4 * (1920 * wbZ wa wb wc * mbZ ma mb mc + (-h).natAbs) < 2 ^ (KW - 1) := by
    have e : KK = 2 ^ (KW - 1) := rfl
    rw [e] at hb
    rw [Int.natAbs_neg]; simpa only [Nat.mul_eq, Nat.add_eq] using hb
  have hg := testGeM_sound r hb' ht (24 * a.val + 8 * b.val + k.val) (by omega) (by
    have : (24 * a.val + 8 * b.val + k.val) % 8 = k.val := by omega
    rw [this]
    simpa [Fin.val_eq_val] using hk)
  linarith

open AtlasProjectiveGlobalCertificate in
theorem globalZ_core (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hints : List ℤ) (hC : bxR.certificate = bx.certificate)
    (h : globalZ bx bxR hints = true) :
    (0 : ℤ) < triL (shell bx) ∧ 0 < boxE (shell bx) ∧ bx.Admissible ∧
      bx.weightedDefectUpper ≤ (((hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) : ℤ)) : ℚ) /
        (2 * (σ0 bx : ℚ)) := by
  unfold globalZ at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, hE⟩, hμ⟩, ht0⟩, ht1⟩, ht2⟩, hw00⟩, hw01⟩, hw02⟩, hw10⟩, hw11⟩, hw12⟩, hw20⟩, hw21⟩, hw22⟩, hwp⟩, hd0⟩, hd1⟩, hd2⟩, hf0⟩, hf1⟩, hf2⟩, hk0⟩, hk1⟩, hk2⟩, hk3⟩, hk4⟩, hk5⟩ := h
  have hLz : (0 : ℤ) < triL (shell bx) := by exact_mod_cast hL
  refine ⟨hLz, hE, ?_⟩
  have W : ∀ a i : Fin 3, nonneg (V3Z.dot (rowZ (triL (shell bx)) bx.triangle a)
      (V3Z.ofV3 (wcN bxR.certificate i))) = true → 0 ≤ V3.dot (trow bx a) (wcN bx.certificate i) :=
    fun a i h => by rw [← w_eq bx bxR hC]; exact (nonneg_iff _).1 h
  have Wp : ∀ a i : Fin 3, pos (V3Z.dot (rowZ (triL (shell bx)) bx.triangle a)
      (V3Z.ofV3 (wcN bxR.certificate i))) = true → 0 < V3.dot (trow bx a) (wcN bx.certificate i) :=
    fun a i h => by rw [← w_eq bx bxR hC]; exact (pos_iff _).1 h
  have hw : ∀ i a : Fin 3, 0 ≤ V3.dot (trow bx a) (wcN bx.certificate i) := by
    intro i a
    fin_cases i <;> fin_cases a
    exacts [W 0 0 hw00, W 1 0 hw10, W 2 0 hw20, W 0 1 hw01, W 1 1 hw11, W 2 1 hw21,
      W 0 2 hw02, W 1 2 hw12, W 2 2 hw22]
  have hwp' : ∃ i : Fin 3, ∀ a : Fin 3, 0 < V3.dot (trow bx a) (wcN bx.certificate i) := by
    rcases hwp with (⟨⟨h0, h1⟩, h2⟩ | ⟨⟨h0, h1⟩, h2⟩) | ⟨⟨h0, h1⟩, h2⟩
    · exact ⟨0, fun a => by fin_cases a; exacts [Wp 0 0 h0, Wp 1 0 h1, Wp 2 0 h2]⟩
    · exact ⟨1, fun a => by fin_cases a; exacts [Wp 0 1 h0, Wp 1 1 h1, Wp 2 1 h2]⟩
    · exact ⟨2, fun a => by fin_cases a; exacts [Wp 0 2 h0, Wp 1 2 h1, Wp 2 2 h2]⟩
  have D : ∀ i : Fin 3, ((¬bxR.localShell.exactSupportTie 0 i (bxR.certificate.nonzeroWitness i) ∧
      isNeg (V3Z.dot (V3Z.ofV3 (V3.sub (LocalKernel.vtx (bxR.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bxR.certificate.index i))))
        (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))) = true) ∧
      isNeg (V3Z.dot (V3Z.ofV3 (V3.sub (LocalKernel.vtx (bxR.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bxR.certificate.index i))))
        (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))) = true) ∧
      isNeg (V3Z.dot (V3Z.ofV3 (V3.sub (LocalKernel.vtx (bxR.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bxR.certificate.index i))))
        (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))) = true →
      ¬ bx.localShell.exactSupportTie 0 i (bx.certificate.nonzeroWitness i) ∧
      ∀ a : Fin 3, V3.dot (V3.sub (LocalKernel.vtx (bx.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bx.certificate.index i))) (V3.cross (trow bx a) (edgeN bx.certificate i)) < 0 := by
    intro i ⟨⟨⟨ht, h0⟩, h1⟩, h2⟩
    refine ⟨fun h => ht ((tie_iff bx bxR hC i _).2 (hC ▸ h)), fun a => ?_⟩
    rw [← dir_eq bx bxR hC]
    fin_cases a
    exacts [(isNeg_iff _).1 h0, (isNeg_iff _).1 h1, (isNeg_iff _).1 h2]
  have F : ∀ i : Fin 3, ∀ (hh : ℤ), (0 ≤ hh ∧
      Nat.mul 4 (Nat.add (Nat.mul (Nat.mul 1920
        (wbZ (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (wcN bxR.certificate i)))))
        (mbZ (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))))
        hh.natAbs) < KK) ∧
      testGeZ ((ctlPackZ (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (bxR.certificate.index i)).2,
        (ctlPackZ (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (bxR.certificate.index i)).1) ones72L (defectMaskT (bxR.certificate.index i)) (-hh) = true →
      0 ≤ hh ∧ ∀ (a b : Fin 3) (k : VertexIndex), k ≠ bx.certificate.index i →
        ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ hh := by
    intro i hh ⟨⟨h0, hb⟩, ht⟩
    exact ⟨h0, def_slot bx i _ _ _ _ _ _ (w_eq bx bxR hC 0 i) (w_eq bx bxR hC 1 i)
      (w_eq bx bxR hC 2 i) (m_eq bx bxR hC 0 i) (m_eq bx bxR hC 1 i) (m_eq bx bxR hC 2 i) hh _
      (by rw [hC]) hb ht⟩
  obtain ⟨hh0, hs0⟩ := F 0 _ hf0
  obtain ⟨hh1, hs1⟩ := F 1 _ hf1
  obtain ⟨hh2, hs2⟩ := F 2 _ hf2
  have hc := core_of_facts bx (fun i => hints.getD i.val 0) hLz hμ
    (fun i => by fin_cases i; exacts [triOkZ_sound bx 0 ht0, triOkZ_sound bx 1 ht1, triOkZ_sound bx 2 ht2])
    hw hwp' (fun i => by fin_cases i; exacts [D 0 hd0, D 1 hd1, D 2 hd2])
    (fun i => by fin_cases i; exacts [hh0, hh1, hh2])
    (fun i => by fin_cases i; exacts [hs0, hs1, hs2])
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hc
  refine ⟨hc.1, ?_⟩
  have e : ((hints.getD 0 0 + hints.getD 1 0 + hints.getD 2 0 : ℤ) : ℚ) =
      ((hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) : ℤ) : ℚ) := by push_cast; ring
  rw [← e]; exact hc.2

open AtlasProjectiveGlobalCertificate in
theorem cqG_congr (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hR : bxR.chart = bx.chart)
    (hC : bxR.certificate = bx.certificate) (hI : bxR.innerIndex = bx.innerIndex) (i c : Fin 3) :
    cqG bxR i c = cqG bx i c := by
  unfold cqG; rw [hR, hC, hI]

theorem V3.dot_add_left (a b c : V3) : V3.dot (V3.add a b) c = V3.dot a c + V3.dot b c := by
  simp only [V3.dot, V3.add, LocalKernel.int_add_eq, LocalKernel.int_mul_eq]; ring

open AtlasProjectiveGlobalCertificate in
theorem viewZ_bern (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hR : bxR.chart = bx.chart)
    (hC : bxR.certificate = bx.certificate) (hI : bxR.innerIndex = bx.innerIndex) (P : PB)
    (hP : ∀ q : IQ, PRep KW 27 (bvZ P (qzOf q)) (bernSlot ((bernWeights (shell bx) q).zip basisTriples))
      (bmZ P (qzOf q)))
    (kc : Z) (t : V3Z) (x0 x1 x2 : Z) (tv : V3) (sc : ℤ) (ht : t.toV3 = tv)
    (hx0 : toZ x0 = V3.dot tv (wcN bx.certificate 0)) (hx1 : toZ x1 = V3.dot tv (wcN bx.certificate 1))
    (hx2 : toZ x2 = V3.dot tv (wcN bx.certificate 2))
    (hkc : toZ kc = bx.ballMultiplier.num * sc * σ0 bx) :
    ∃ d : ℕ → ℤ, PRep KW 27 (viewZ bx.ballMultiplier.den kc t x0 x1 x2
        ⟨bvZ P (qzOf (cqG bxR 0 0)), bmZ P (qzOf (cqG bxR 0 0))⟩
        ⟨bvZ P (qzOf (cqG bxR 0 1)), bmZ P (qzOf (cqG bxR 0 1))⟩
        ⟨bvZ P (qzOf (cqG bxR 0 2)), bmZ P (qzOf (cqG bxR 0 2))⟩
        ⟨bvZ P (qzOf (cqG bxR 1 0)), bmZ P (qzOf (cqG bxR 1 0))⟩
        ⟨bvZ P (qzOf (cqG bxR 1 1)), bmZ P (qzOf (cqG bxR 1 1))⟩
        ⟨bvZ P (qzOf (cqG bxR 1 2)), bmZ P (qzOf (cqG bxR 1 2))⟩
        ⟨bvZ P (qzOf (cqG bxR 2 0)), bmZ P (qzOf (cqG bxR 2 0))⟩
        ⟨bvZ P (qzOf (cqG bxR 2 1)), bmZ P (qzOf (cqG bxR 2 1))⟩
        ⟨bvZ P (qzOf (cqG bxR 2 2)), bmZ P (qzOf (cqG bxR 2 2))⟩
        ⟨bvZ P (qzOf cayI), bmZ P (qzOf cayI)⟩).u d
      (viewZ bx.ballMultiplier.den kc t x0 x1 x2
        ⟨bvZ P (qzOf (cqG bxR 0 0)), bmZ P (qzOf (cqG bxR 0 0))⟩
        ⟨bvZ P (qzOf (cqG bxR 0 1)), bmZ P (qzOf (cqG bxR 0 1))⟩
        ⟨bvZ P (qzOf (cqG bxR 0 2)), bmZ P (qzOf (cqG bxR 0 2))⟩
        ⟨bvZ P (qzOf (cqG bxR 1 0)), bmZ P (qzOf (cqG bxR 1 0))⟩
        ⟨bvZ P (qzOf (cqG bxR 1 1)), bmZ P (qzOf (cqG bxR 1 1))⟩
        ⟨bvZ P (qzOf (cqG bxR 1 2)), bmZ P (qzOf (cqG bxR 1 2))⟩
        ⟨bvZ P (qzOf (cqG bxR 2 0)), bmZ P (qzOf (cqG bxR 2 0))⟩
        ⟨bvZ P (qzOf (cqG bxR 2 1)), bmZ P (qzOf (cqG bxR 2 1))⟩
        ⟨bvZ P (qzOf (cqG bxR 2 2)), bmZ P (qzOf (cqG bxR 2 2))⟩
        ⟨bvZ P (qzOf cayI), bmZ P (qzOf cayI)⟩).m ∧
      ∀ a b c : Fin 3, d (9 * a.val + 3 * b.val + c.val) =
        bernI (shell bx) (viewIQ bx tv sc) a.val b.val c.val := by
  refine ⟨_, viewZ_rep (hP _) (hP _) (hP _) (hP _) (hP _) (hP _) (hP _) (hP _) (hP _) (hP _),
    fun a b c => ?_⟩
  have htx : toZ t.x = tv.x := congrArg V3.x ht
  have hty : toZ t.y = tv.y := congrArg V3.y ht
  have htz : toZ t.z = tv.z := congrArg V3.z ht
  simp only [bernSlot_eq, cqG_congr bx bxR hR hC hI, hx0, hx1, hx2, hkc, htx, hty, htz]
  simp only [viewIQ, bernI_add, bernI_smul, V3.get]
  ring

open AtlasProjectiveGlobalCertificate in
theorem globalZ_sound (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hints : List ℤ)
    (hR : bxR.chart = bx.chart) (hC : bxR.certificate = bx.certificate)
    (hI : bxR.innerIndex = bx.innerIndex) (h : globalZ bx bxR hints = true) : bx.Valid := by
  obtain ⟨hL, hE, hadm, hWD⟩ := globalZ_core bx bxR hints hC h
  unfold globalZ at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hE⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hk0⟩, hk1⟩, hk2⟩, hk3⟩, hk4⟩, hk5⟩ := h
  set sh := shell bx
  set E := boxE sh
  set iv := bx.interval
  have hP : ∀ q : IQ, PRep KW 27 (bvZ (pbZ E (qS E (iv.min.get 2)) (qS E (iv.min.get 3))
      (qS E (iv.min.get 4)) (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2)))
      (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3))) (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4))))
      (qzOf q)) (bernSlot ((bernWeights sh q).zip basisTriples))
      (bmZ (pbZ E (qS E (iv.min.get 2)) (qS E (iv.min.get 3))
      (qS E (iv.min.get 4)) (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2)))
      (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3))) (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4))))
      (qzOf q)) := by
    intro q
    have r := bvZ_rep sh (qS E (iv.min.get 2)) (qS E (iv.min.get 3)) (qS E (iv.min.get 4))
      (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2))) (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3)))
      (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4))) (by rw [toZ_qS]; rfl) (by rw [toZ_qS]; rfl)
      (by rw [toZ_qS]; rfl) (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl) (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl)
      (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl) (qzOf q)
    rwa [qzOf_toIQ] at r
  have hσ : ∀ k : ℕ, toZ (nmul (Nat.mul k (Nat.mul (Nat.mul (triL sh) (triL sh)) 2560000000000000))
      (ofI bx.ballMultiplier.num)) = bx.ballMultiplier.num * k * σ0 bx := by
    intro k
    simp only [toZ_nmul, toZ_ofI, σ0, Nat.mul_eq]
    push_cast; ring
  have hσ1 := hσ 1
  rw [show Nat.mul 1 (Nat.mul (Nat.mul (triL sh) (triL sh)) 2560000000000000) =
    Nat.mul (Nat.mul (triL sh) (triL sh)) 2560000000000000 from Nat.one_mul _] at hσ1
  have V := fun (a : Fin 3) => viewZ_bern bx bxR hR hC hI _ hP _ (rowZ (triL sh) bx.triangle a)
    (V3Z.dot (rowZ (triL sh) bx.triangle a) (V3Z.ofV3 (wcN bxR.certificate 0)))
    (V3Z.dot (rowZ (triL sh) bx.triangle a) (V3Z.ofV3 (wcN bxR.certificate 1)))
    (V3Z.dot (rowZ (triL sh) bx.triangle a) (V3Z.ofV3 (wcN bxR.certificate 2)))
    (trow bx a) 1 (rowZ_toV3 bx a) (w_eq bx bxR hC a 0) (w_eq bx bxR hC a 1) (w_eq bx bxR hC a 2)
    (by rw [hσ1]; ring)
  have VV := fun (a b : Fin 3) => viewZ_bern bx bxR hR hC hI _ hP _
    (V3Z.vadd (rowZ (triL sh) bx.triangle a) (rowZ (triL sh) bx.triangle b))
    (add (V3Z.dot (rowZ (triL sh) bx.triangle a) (V3Z.ofV3 (wcN bxR.certificate 0)))
      (V3Z.dot (rowZ (triL sh) bx.triangle b) (V3Z.ofV3 (wcN bxR.certificate 0))))
    (add (V3Z.dot (rowZ (triL sh) bx.triangle a) (V3Z.ofV3 (wcN bxR.certificate 1)))
      (V3Z.dot (rowZ (triL sh) bx.triangle b) (V3Z.ofV3 (wcN bxR.certificate 1))))
    (add (V3Z.dot (rowZ (triL sh) bx.triangle a) (V3Z.ofV3 (wcN bxR.certificate 2)))
      (V3Z.dot (rowZ (triL sh) bx.triangle b) (V3Z.ofV3 (wcN bxR.certificate 2))))
    (V3.add (trow bx a) (trow bx b)) 4 (by rw [V3Z.toV3_vadd, rowZ_toV3, rowZ_toV3])
    (by rw [toZ_add, w_eq bx bxR hC, w_eq bx bxR hC, V3.dot_add_left])
    (by rw [toZ_add, w_eq bx bxR hC, w_eq bx bxR hC, V3.dot_add_left])
    (by rw [toZ_add, w_eq bx bxR hC, w_eq bx bxR hC, V3.dot_add_left]) (hσ 4)
  have diag : ∀ (a : Fin 3) {v : BQ} {d : ℕ → ℤ} {th : ℤ}, PRep KW 27 v.u d v.m →
      (∀ x y z : Fin 3, d (9 * x.val + 3 * y.val + z.val) =
        bernI sh (viewIQ bx (trow bx a) 1) x.val y.val z.val) →
      bernOkZ (diagZ v).u (diagZ v).m th = true →
      ∀ x y z : Fin 3, th ≤ bernI sh (IQ.smul 2 (viewIQ bx (trow bx a) 1)) x.val y.val z.val := by
    intro a v d th r e hk x y z
    have := bernOkZ_sound (r.psm (2, 0)) hk x y z
    rw [e, toZ_mk0] at this
    rw [bernI_smul]; exact_mod_cast this
  have off : ∀ (a b : Fin 3) {vm va vb : BQ} {dm da db : ℕ → ℤ} {th : ℤ},
      PRep KW 27 vm.u dm vm.m → PRep KW 27 va.u da va.m → PRep KW 27 vb.u db vb.m →
      (∀ x y z : Fin 3, dm (9 * x.val + 3 * y.val + z.val) =
        bernI sh (viewIQ bx (V3.add (trow bx a) (trow bx b)) 4) x.val y.val z.val) →
      (∀ x y z : Fin 3, da (9 * x.val + 3 * y.val + z.val) =
        bernI sh (viewIQ bx (trow bx a) 1) x.val y.val z.val) →
      (∀ x y z : Fin 3, db (9 * x.val + 3 * y.val + z.val) =
        bernI sh (viewIQ bx (trow bx b) 1) x.val y.val z.val) →
      bernOkZ (offZ vm va vb).u (offZ vm va vb).m th = true →
      ∀ x y z : Fin 3, th ≤ bernI sh (IQ.sub (viewIQ bx (V3.add (trow bx a) (trow bx b)) 4)
        (IQ.add (viewIQ bx (trow bx a) 1) (viewIQ bx (trow bx b) 1))) x.val y.val z.val := by
    intro a b vm va vb dm da db th rm ra rb em ea eb hk x y z
    have := bernOkZ_sound (rm.padd (ra.padd rb).neg) hk x y z
    simp only [em, ea, eb] at this
    simp only [IQ.sub, bernI_add, bernI_smul]
    linarith
  obtain ⟨d0, r0, e0⟩ := V 0
  obtain ⟨d1, r1, e1⟩ := V 1
  obtain ⟨d2, r2, e2⟩ := V 2
  obtain ⟨d01, r01, e01⟩ := VV 0 1
  obtain ⟨d02, r02, e02⟩ := VV 0 2
  obtain ⟨d12, r12, e12⟩ := VV 1 2
  have c00 := diag 0 r0 e0 hk0
  have c11 := diag 1 r1 e1 hk1
  have c22 := diag 2 r2 e2 hk2
  have c01 := off 0 1 r01 r0 r1 e01 e0 e1 hk3
  have c02 := off 0 2 r02 r0 r2 e02 e0 e2 hk4
  have c12 := off 1 2 r12 r1 r2 e12 e1 e2 hk5
  refine valid_of_ctl bx hints hadm hWD hL hE fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact ctl_lower bx 0 0 _ hE (by simpa using c00)
  · exact ctl_lower bx 0 1 _ hE (by simpa using c01)
  · exact ctl_lower bx 0 2 _ hE (by simpa using c02)
  · rw [viewControl_comm]; exact ctl_lower bx 0 1 _ hE (by simpa using c01)
  · exact ctl_lower bx 1 1 _ hE (by simpa using c11)
  · exact ctl_lower bx 1 2 _ hE (by simpa using c12)
  · rw [viewControl_comm]; exact ctl_lower bx 0 2 _ hE (by simpa using c02)
  · rw [viewControl_comm]; exact ctl_lower bx 1 2 _ hE (by simpa using c12)
  · exact ctl_lower bx 2 2 _ hE (by simpa using c22)

/-! ## Components (for mixed certificates) -/

open AtlasProjectiveGlobalCertificate in
/-- The packed Bernstein vectors of the monomials on the box of `bx`. -/
def pbOf (bx : AtlasProjectiveGlobalCertificate.Box) : PB :=
  let E := boxE (shell bx)
  let iv := bx.interval
  pbZ E (qS E (iv.min.get 2)) (qS E (iv.min.get 3)) (qS E (iv.min.get 4))
    (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2))) (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3)))
    (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4)))

open AtlasProjectiveGlobalCertificate in
theorem pbOf_rep (bx : AtlasProjectiveGlobalCertificate.Box) (q : IQ) :
    PRep KW 27 (bvZ (pbOf bx) (qzOf q)) (bernSlot ((bernWeights (shell bx) q).zip basisTriples))
      (bmZ (pbOf bx) (qzOf q)) := by
  have r := bvZ_rep (shell bx) (qS (boxE (shell bx)) (bx.interval.min.get 2))
    (qS (boxE (shell bx)) (bx.interval.min.get 3)) (qS (boxE (shell bx)) (bx.interval.min.get 4))
    (sub (qS (boxE (shell bx)) (bx.interval.max.get 2)) (qS (boxE (shell bx)) (bx.interval.min.get 2)))
    (sub (qS (boxE (shell bx)) (bx.interval.max.get 3)) (qS (boxE (shell bx)) (bx.interval.min.get 3)))
    (sub (qS (boxE (shell bx)) (bx.interval.max.get 4)) (qS (boxE (shell bx)) (bx.interval.min.get 4)))
    (by rw [toZ_qS]; rfl) (by rw [toZ_qS]; rfl) (by rw [toZ_qS]; rfl)
    (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl) (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl)
    (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl) (qzOf q)
  rw [qzOf_toIQ] at r
  exact r

open AtlasProjectiveGlobalCertificate in
/-- The view vector of `bx` at view `t` (weights `x_i = t · wc_i`) and scale `s`. -/
def viewOf (bx bxR : AtlasProjectiveGlobalCertificate.Box) (s : ℕ) (t : V3Z) (x0 x1 x2 : Z) : BQ :=
  let P := pbOf bx
  let B := fun (i c : Fin 3) => (⟨bvZ P (qzOf (cqG bxR i c)), bmZ P (qzOf (cqG bxR i c))⟩ : BQ)
  let L := triL (shell bx)
  let k := nmul (Nat.mul s (Nat.mul (Nat.mul L L) 2560000000000000)) (ofI bx.ballMultiplier.num)
  viewZ bx.ballMultiplier.den k t x0 x1 x2 (B 0 0) (B 0 1) (B 0 2) (B 1 0) (B 1 1) (B 1 2)
    (B 2 0) (B 2 1) (B 2 2) ⟨bvZ P (qzOf cayI), bmZ P (qzOf cayI)⟩

open AtlasProjectiveGlobalCertificate in
/-- The view vector at corner `a`. -/
def cornerView (bx bxR : AtlasProjectiveGlobalCertificate.Box) (a : Fin 3) : BQ :=
  let t := rowZ (triL (shell bx)) bx.triangle a
  viewOf bx bxR 1 t (V3Z.dot t (V3Z.ofV3 (wcN bxR.certificate 0)))
    (V3Z.dot t (V3Z.ofV3 (wcN bxR.certificate 1))) (V3Z.dot t (V3Z.ofV3 (wcN bxR.certificate 2)))

open AtlasProjectiveGlobalCertificate in
/-- The view vector at the (doubled) midpoint of corners `a, b`. -/
def midView (bx bxR : AtlasProjectiveGlobalCertificate.Box) (a b : Fin 3) : BQ :=
  let ta := rowZ (triL (shell bx)) bx.triangle a
  let tb := rowZ (triL (shell bx)) bx.triangle b
  viewOf bx bxR 4 (V3Z.vadd ta tb)
    (add (V3Z.dot ta (V3Z.ofV3 (wcN bxR.certificate 0))) (V3Z.dot tb (V3Z.ofV3 (wcN bxR.certificate 0))))
    (add (V3Z.dot ta (V3Z.ofV3 (wcN bxR.certificate 1))) (V3Z.dot tb (V3Z.ofV3 (wcN bxR.certificate 1))))
    (add (V3Z.dot ta (V3Z.ofV3 (wcN bxR.certificate 2))) (V3Z.dot tb (V3Z.ofV3 (wcN bxR.certificate 2))))

open AtlasProjectiveGlobalCertificate in
/-- The packed control vector `(i, j)` (cf. `ctlPair`). -/
def ctlBQ (bx bxR : AtlasProjectiveGlobalCertificate.Box) (i j : Fin 3) : BQ :=
  if i = j then diagZ (cornerView bx bxR i)
  else offZ (midView bx bxR i j) (cornerView bx bxR i) (cornerView bx bxR j)

open AtlasProjectiveGlobalCertificate in
theorem ctlBQ_rep (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hR : bxR.chart = bx.chart) (hC : bxR.certificate = bx.certificate)
    (hI : bxR.innerIndex = bx.innerIndex) (i j : Fin 3) :
    ∃ d : ℕ → ℤ, PRep KW 27 (ctlBQ bx bxR i j).u d (ctlBQ bx bxR i j).m ∧
      ∀ a b c : Fin 3, (d (9 * a.val + 3 * b.val + c.val) : ℚ) =
        4 * (boxE (shell bx) : ℚ) ^ 2 * (2 * ((bx.ballMultiplier.den : ℚ) * (σ0 bx : ℚ))) *
          QuadraticBernstein.coefficient bx.relativeBalls (bx.viewControlQuadratic i j) a b c := by
  have hσ : ∀ k : ℕ, toZ (nmul (Nat.mul k (Nat.mul (Nat.mul (triL (shell bx)) (triL (shell bx)))
      2560000000000000)) (ofI bx.ballMultiplier.num)) = bx.ballMultiplier.num * k * σ0 bx := by
    intro k
    simp only [toZ_nmul, toZ_ofI, σ0, Nat.mul_eq]
    push_cast; ring
  have CV : ∀ a : Fin 3, ∃ d : ℕ → ℤ, PRep KW 27 (cornerView bx bxR a).u d (cornerView bx bxR a).m ∧
      ∀ x y z : Fin 3, d (9 * x.val + 3 * y.val + z.val) =
        bernI (shell bx) (viewIQ bx (trow bx a) 1) x.val y.val z.val := by
    intro a
    exact viewZ_bern bx bxR hR hC hI _ (pbOf_rep bx) _ _ _ _ _ (trow bx a) 1 (rowZ_toV3 bx a)
      (w_eq bx bxR hC a 0) (w_eq bx bxR hC a 1) (w_eq bx bxR hC a 2) (by rw [hσ 1]; ring)
  have MV : ∀ a b : Fin 3, ∃ d : ℕ → ℤ, PRep KW 27 (midView bx bxR a b).u d (midView bx bxR a b).m ∧
      ∀ x y z : Fin 3, d (9 * x.val + 3 * y.val + z.val) =
        bernI (shell bx) (viewIQ bx (V3.add (trow bx a) (trow bx b)) 4) x.val y.val z.val := by
    intro a b
    exact viewZ_bern bx bxR hR hC hI _ (pbOf_rep bx) _ _ _ _ _ (V3.add (trow bx a) (trow bx b)) 4
      (by rw [V3Z.toV3_vadd, rowZ_toV3, rowZ_toV3])
      (by rw [toZ_add, w_eq bx bxR hC, w_eq bx bxR hC, V3.dot_add_left])
      (by rw [toZ_add, w_eq bx bxR hC, w_eq bx bxR hC, V3.dot_add_left])
      (by rw [toZ_add, w_eq bx bxR hC, w_eq bx bxR hC, V3.dot_add_left]) (hσ 4)
  unfold ctlBQ
  split_ifs with hij
  · subst hij
    obtain ⟨d, r, e⟩ := CV i
    refine ⟨_, r.psm (2, 0), fun a b c => ?_⟩
    have h1 : (ZP.toZ (2, 0) * d (9 * a.val + 3 * b.val + c.val) : ℤ) =
        bernI (shell bx) (IQ.smul 2 (viewIQ bx (trow bx i) 1)) a.val b.val c.val := by
      rw [e, bernI_smul, toZ_mk0]; rfl
    rw [show ((ZP.toZ (2, 0) * d (9 * a.val + 3 * b.val + c.val) : ℤ) : ℚ) =
      ((bernI (shell bx) (IQ.smul 2 (viewIQ bx (trow bx i) 1)) a.val b.val c.val : ℤ) : ℚ) from
      congrArg _ h1]
    rw [bernI_cast, relativeBalls_eq, diag_toQ, coefficient_scale]
    ring
  · obtain ⟨dm, rm, em⟩ := MV i j
    obtain ⟨di, ri, ei⟩ := CV i
    obtain ⟨dj, rj, ej⟩ := CV j
    refine ⟨_, rm.padd (ri.padd rj).neg, fun a b c => ?_⟩
    have h1 : (dm (9 * a.val + 3 * b.val + c.val) +
        -(di (9 * a.val + 3 * b.val + c.val) + dj (9 * a.val + 3 * b.val + c.val)) : ℤ) =
        bernI (shell bx) (IQ.sub (viewIQ bx (V3.add (trow bx i) (trow bx j)) 4)
          (IQ.add (viewIQ bx (trow bx i) 1) (viewIQ bx (trow bx j) 1))) a.val b.val c.val := by
      rw [em, ei, ej]
      simp only [IQ.sub, bernI_add, bernI_smul]
      ring
    rw [show ((dm (9 * a.val + 3 * b.val + c.val) +
        -(di (9 * a.val + 3 * b.val + c.val) + dj (9 * a.val + 3 * b.val + c.val)) : ℤ) : ℚ) =
      ((bernI (shell bx) (IQ.sub (viewIQ bx (V3.add (trow bx i) (trow bx j)) 4)
          (IQ.add (viewIQ bx (trow bx i) 1) (viewIQ bx (trow bx j) 1))) a.val b.val c.val : ℤ) : ℚ)
      from congrArg _ h1]
    rw [bernI_cast, relativeBalls_eq, off_toQ bx i j hij, coefficient_scale]
    ring

open AtlasProjectiveGlobalCertificate in
/-- The admissibility and weighted-defect conditions of `globalZ`. -/
def gcoreZ (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hints : List ℤ) : Bool :=
  let sh := shell bx
  let L := triL sh
  let E := boxE sh
  let root := bx.root
  let t0 := rowZ L bx.triangle 0
  let t1 := rowZ L bx.triangle 1
  let t2 := rowZ L bx.triangle 2
  let cert := bxR.certificate
  let e0 := V3Z.ofV3 (edgeN cert 0)
  let e1 := V3Z.ofV3 (edgeN cert 1)
  let e2 := V3Z.ofV3 (edgeN cert 2)
  let c0 := V3Z.ofV3 (wcN cert 0)
  let c1 := V3Z.ofV3 (wcN cert 1)
  let c2 := V3Z.ofV3 (wcN cert 2)
  let w00 := V3Z.dot t0 c0
  let w01 := V3Z.dot t0 c1
  let w02 := V3Z.dot t0 c2
  let w10 := V3Z.dot t1 c0
  let w11 := V3Z.dot t1 c1
  let w12 := V3Z.dot t1 c2
  let w20 := V3Z.dot t2 c0
  let w21 := V3Z.dot t2 c1
  let w22 := V3Z.dot t2 c2
  let m00 := V3Z.cross t0 e0
  let m01 := V3Z.cross t0 e1
  let m02 := V3Z.cross t0 e2
  let m10 := V3Z.cross t1 e0
  let m11 := V3Z.cross t1 e1
  let m12 := V3Z.cross t1 e2
  let m20 := V3Z.cross t2 e0
  let m21 := V3Z.cross t2 e1
  let m22 := V3Z.cross t2 e2
  let dirOk := fun (i : Fin 3) (ma mb mc : V3Z) =>
    let d := V3Z.ofV3 (V3.sub (LocalKernel.vtx (cert.nonzeroWitness i)) (LocalKernel.vtx (cert.index i)))
    !decide (bxR.localShell.exactSupportTie 0 i (cert.nonzeroWitness i)) &&
      isNeg (V3Z.dot d ma) && isNeg (V3Z.dot d mb) && isNeg (V3Z.dot d mc)
  let defOk := fun (i : Fin 3) (wa wb wc : Z) (ma mb mc : V3Z) =>
    let h := hints.getD i.val 0
    decide (0 ≤ h) &&
      Nat.blt (Nat.mul 4 (Nat.add (Nat.mul (Nat.mul 1920 (wbZ wa wb wc)) (mbZ ma mb mc)) h.natAbs)) KK &&
      testGeZ ((ctlPackZ wa wb wc ma mb mc (cert.index i)).2, (ctlPackZ wa wb wc ma mb mc (cert.index i)).1)
        ones72L (defectMaskT (cert.index i)) (-h)
  Nat.blt 0 L && Nat.blt 0 E && decide (0 ≤ bx.ballMultiplier.num) &&
    triOkZ root L t0 && triOkZ root L t1 && triOkZ root L t2 &&
    nonneg w00 && nonneg w01 && nonneg w02 && nonneg w10 && nonneg w11 && nonneg w12 &&
    nonneg w20 && nonneg w21 && nonneg w22 &&
    ((pos w00 && pos w10 && pos w20) || (pos w01 && pos w11 && pos w21) ||
      (pos w02 && pos w12 && pos w22)) &&
    dirOk 0 m00 m10 m20 && dirOk 1 m01 m11 m21 && dirOk 2 m02 m12 m22 &&
    defOk 0 w00 w10 w20 m00 m10 m20 && defOk 1 w01 w11 w21 m01 m11 m21 &&
    defOk 2 w02 w12 w22 m02 m12 m22

open AtlasProjectiveGlobalCertificate in
theorem gcoreZ_sound (bx bxR : AtlasProjectiveGlobalCertificate.Box) (hints : List ℤ) (hC : bxR.certificate = bx.certificate)
    (h : gcoreZ bx bxR hints = true) :
    (0 : ℤ) < triL (shell bx) ∧ 0 < boxE (shell bx) ∧ bx.Admissible ∧
      bx.weightedDefectUpper ≤ (((hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) : ℤ)) : ℚ) /
        (2 * (σ0 bx : ℚ)) := by
  unfold gcoreZ at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, hE⟩, hμ⟩, ht0⟩, ht1⟩, ht2⟩, hw00⟩, hw01⟩, hw02⟩, hw10⟩, hw11⟩, hw12⟩, hw20⟩, hw21⟩, hw22⟩, hwp⟩, hd0⟩, hd1⟩, hd2⟩, hf0⟩, hf1⟩, hf2⟩ := h
  have hLz : (0 : ℤ) < triL (shell bx) := by exact_mod_cast hL
  refine ⟨hLz, hE, ?_⟩
  have W : ∀ a i : Fin 3, nonneg (V3Z.dot (rowZ (triL (shell bx)) bx.triangle a)
      (V3Z.ofV3 (wcN bxR.certificate i))) = true → 0 ≤ V3.dot (trow bx a) (wcN bx.certificate i) :=
    fun a i h => by rw [← w_eq bx bxR hC]; exact (nonneg_iff _).1 h
  have Wp : ∀ a i : Fin 3, pos (V3Z.dot (rowZ (triL (shell bx)) bx.triangle a)
      (V3Z.ofV3 (wcN bxR.certificate i))) = true → 0 < V3.dot (trow bx a) (wcN bx.certificate i) :=
    fun a i h => by rw [← w_eq bx bxR hC]; exact (pos_iff _).1 h
  have hw : ∀ i a : Fin 3, 0 ≤ V3.dot (trow bx a) (wcN bx.certificate i) := by
    intro i a
    fin_cases i <;> fin_cases a
    exacts [W 0 0 hw00, W 1 0 hw10, W 2 0 hw20, W 0 1 hw01, W 1 1 hw11, W 2 1 hw21,
      W 0 2 hw02, W 1 2 hw12, W 2 2 hw22]
  have hwp' : ∃ i : Fin 3, ∀ a : Fin 3, 0 < V3.dot (trow bx a) (wcN bx.certificate i) := by
    rcases hwp with (⟨⟨h0, h1⟩, h2⟩ | ⟨⟨h0, h1⟩, h2⟩) | ⟨⟨h0, h1⟩, h2⟩
    · exact ⟨0, fun a => by fin_cases a; exacts [Wp 0 0 h0, Wp 1 0 h1, Wp 2 0 h2]⟩
    · exact ⟨1, fun a => by fin_cases a; exacts [Wp 0 1 h0, Wp 1 1 h1, Wp 2 1 h2]⟩
    · exact ⟨2, fun a => by fin_cases a; exacts [Wp 0 2 h0, Wp 1 2 h1, Wp 2 2 h2]⟩
  have D : ∀ i : Fin 3, ((¬bxR.localShell.exactSupportTie 0 i (bxR.certificate.nonzeroWitness i) ∧
      isNeg (V3Z.dot (V3Z.ofV3 (V3.sub (LocalKernel.vtx (bxR.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bxR.certificate.index i))))
        (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))) = true) ∧
      isNeg (V3Z.dot (V3Z.ofV3 (V3.sub (LocalKernel.vtx (bxR.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bxR.certificate.index i))))
        (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))) = true) ∧
      isNeg (V3Z.dot (V3Z.ofV3 (V3.sub (LocalKernel.vtx (bxR.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bxR.certificate.index i))))
        (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))) = true →
      ¬ bx.localShell.exactSupportTie 0 i (bx.certificate.nonzeroWitness i) ∧
      ∀ a : Fin 3, V3.dot (V3.sub (LocalKernel.vtx (bx.certificate.nonzeroWitness i))
        (LocalKernel.vtx (bx.certificate.index i))) (V3.cross (trow bx a) (edgeN bx.certificate i)) < 0 := by
    intro i ⟨⟨⟨ht, h0⟩, h1⟩, h2⟩
    refine ⟨fun h => ht ((tie_iff bx bxR hC i _).2 (hC ▸ h)), fun a => ?_⟩
    rw [← dir_eq bx bxR hC]
    fin_cases a
    exacts [(isNeg_iff _).1 h0, (isNeg_iff _).1 h1, (isNeg_iff _).1 h2]
  have F : ∀ i : Fin 3, ∀ (hh : ℤ), (0 ≤ hh ∧
      Nat.mul 4 (Nat.add (Nat.mul (Nat.mul 1920
        (wbZ (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (wcN bxR.certificate i)))))
        (mbZ (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))))
        hh.natAbs) < KK) ∧
      testGeZ ((ctlPackZ (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (bxR.certificate.index i)).2,
        (ctlPackZ (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.dot (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (wcN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 0) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 1) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (V3Z.cross (rowZ (triL (shell bx)) bx.triangle 2) (V3Z.ofV3 (edgeN bxR.certificate i)))
          (bxR.certificate.index i)).1) ones72L (defectMaskT (bxR.certificate.index i)) (-hh) = true →
      0 ≤ hh ∧ ∀ (a b : Fin 3) (k : VertexIndex), k ≠ bx.certificate.index i →
        ctlSlot bx i (24 * a.val + 8 * b.val + k.val) ≤ hh := by
    intro i hh ⟨⟨h0, hb⟩, ht⟩
    exact ⟨h0, def_slot bx i _ _ _ _ _ _ (w_eq bx bxR hC 0 i) (w_eq bx bxR hC 1 i)
      (w_eq bx bxR hC 2 i) (m_eq bx bxR hC 0 i) (m_eq bx bxR hC 1 i) (m_eq bx bxR hC 2 i) hh _
      (by rw [hC]) hb ht⟩
  obtain ⟨hh0, hs0⟩ := F 0 _ hf0
  obtain ⟨hh1, hs1⟩ := F 1 _ hf1
  obtain ⟨hh2, hs2⟩ := F 2 _ hf2
  have hc := core_of_facts bx (fun i => hints.getD i.val 0) hLz hμ
    (fun i => by fin_cases i; exacts [triOkZ_sound bx 0 ht0, triOkZ_sound bx 1 ht1, triOkZ_sound bx 2 ht2])
    hw hwp' (fun i => by fin_cases i; exacts [D 0 hd0, D 1 hd1, D 2 hd2])
    (fun i => by fin_cases i; exacts [hh0, hh1, hh2])
    (fun i => by fin_cases i; exacts [hs0, hs1, hs2])
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hc
  refine ⟨hc.1, ?_⟩
  have e : ((hints.getD 0 0 + hints.getD 1 0 + hints.getD 2 0 : ℤ) : ℚ) =
      ((hints.getD 0 0 + (hints.getD 1 0 + hints.getD 2 0) : ℤ) : ℚ) := by push_cast; ring
  rw [← e]; exact hc.2

end Noperts.Stellated.ChartKernelF
