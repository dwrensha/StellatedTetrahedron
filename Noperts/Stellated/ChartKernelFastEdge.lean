module

public import Noperts.Stellated.ChartKernelFastGlobal

@[expose] public section

/-!
# A faster kernel checker for projective edge leaves

`edgeZ box box₀ hints` decides the conditions of `ChartKernel.validEdgeK box hints` in
`Nat`-pair arithmetic, with the packed Bernstein vectors of `ChartKernelFast`.  The box
`box₀` is `box` with a fixed interval and view; it serves the edge totals, which depend
only on the edge cycle (so the kernel's cache shares them between leaves).
-/

namespace Noperts.Stellated.ChartKernelF

open ChartKernel PackedSlots AtlasProjectiveEdgeCertificate AtlasProjectiveView ZP
open LocalKernel (V3)

/-- The successor in the edge cycle (`cycleNext`), by arithmetic. -/
def nextF (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val = n then ⟨0, by omega⟩ else ⟨i.val + 1, by omega⟩

open Noperts.BalancedSupport in
theorem nextF_eq (n : ℕ) (i : Fin (n + 1)) : nextF n i = cycleNext n i := by
  unfold nextF cycleNext
  split_ifs with h
  · have : i = Fin.last n := Fin.ext h
    subst this; simp
  · have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) (fun e => h (congrArg Fin.val e))
    rw [Fin.cycleRange_of_lt hlt]; ext; simp [Fin.val_add_one_of_lt hlt]

theorem next_eq (box : Box) (i : Fin (box.edgePred + 1)) :
    box.edgeShell.next i = nextF box.edgePred i := (nextF_eq _ _).symm

theorem triOkZ_sound' (box : Box) (i : Fin 3)
    (h : triOkZ box.root (triL box) (rowZ (triL box) box.triangle i) = true) :
    (∀ c : Fin 3, 0 ≤ (rootSign box.root c).num * T box i c) ∧
      (rootSign box.root 0).num * T box i 0 + (rootSign box.root 1).num * T box i 1 +
        (rootSign box.root 2).num * T box i 2 = triL box := by
  have hT : ∀ c : Fin 3, T box i c = ZP.toZ (qS (triL box) (box.triangle i c)) := by
    intro c; rw [toZ_qS]; rfl
  simp only [triOkZ, Bool.and_eq_true, nonneg_iff, eqZ_iff, toZ_add, toZ_mk0] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have e0 := toZ_sgnZ box.root 0 (rowZ (triL box) box.triangle i).x
  have e1 := toZ_sgnZ box.root 1 (rowZ (triL box) box.triangle i).y
  have e2 := toZ_sgnZ box.root 2 (rowZ (triL box) box.triangle i).z
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  simp only [rowZ] at e0 e1 e2 h0 h1 h2 h3
  rw [e0] at h0 h3; rw [e1] at h1 h3; rw [e2] at h2 h3
  refine ⟨fun c => ?_, ?_⟩
  · fin_cases c
    · rw [hT]; exact h0
    · rw [hT]; exact h1
    · rw [hT]; exact h2
  · rw [hT, hT, hT]; exact h3

/-! ## Supports -/

/-- The edge vector `v_s - v_f` as a pair vector. -/
def edgeZv (s f : VertexIndex) : V3Z := ⟨ofI (edgeT s f 0), ofI (edgeT s f 1), ofI (edgeT s f 2)⟩

/-- The packed supports of an edge (slot `8 j + k`: support of vertex `k` at corner `j`). -/
def supPackZ (r0 r1 r2 : V3Z) (s f : VertexIndex) : ℕ × ℕ :=
  let e := edgeZv s f
  let m0 := V3Z.cross r0 e
  let m1 := V3Z.cross r1 e
  let m2 := V3Z.cross r2 e
  padd (pmul (pk3 P8a P8b m0.x m1.x m2.x) (deltaT s 0))
    (padd (pmul (pk3 P8a P8b m0.y m1.y m2.y) (deltaT s 1)) (pmul (pk3 P8a P8b m0.z m1.z m2.z) (deltaT s 2)))

def supBoundZ (r0 r1 r2 : V3Z) (s f : VertexIndex) : ℕ :=
  Nat.mul 240 (mbZ (V3Z.cross r0 (edgeZv s f)) (V3Z.cross r1 (edgeZv s f)) (V3Z.cross r2 (edgeZv s f)))

theorem supPackZ_rep (box : Box) (i : Fin (box.edgePred + 1)) (r0 r1 r2 : V3Z)
    (h0 : r0.toV3 = ⟨T box 0 0, T box 0 1, T box 0 2⟩) (h1 : r1.toV3 = ⟨T box 1 0, T box 1 1, T box 1 2⟩)
    (h2 : r2.toV3 = ⟨T box 2 0, T box 2 1, T box 2 2⟩) :
    PRep KW 24 (supPackZ r0 r1 r2 (box.outerIndex i) (box.outerIndex (nextF box.edgePred i)))
      (supSlot box i) (supBoundZ r0 r1 r2 (box.outerIndex i) (box.outerIndex (nextF box.edgePred i))) := by
  set s := box.outerIndex i
  set f := box.outerIndex (nextF box.edgePred i)
  set e := edgeZv s f
  set Mm := mbZ (V3Z.cross r0 e) (V3Z.cross r1 e) (V3Z.cross r2 e)
  have hd : ∀ d : Fin 3, PRep KW 8 (deltaT s d) (δN s d) 40 :=
    fun d => by rw [deltaT_eq]; exact pmPack_rep KW 8 _ 40 (δN_le _ d)
  have ha : (V3Z.cross r0 e).sz3 ≤ Mm := by simp only [Mm, mbZ, Nat.add_eq]; omega
  have hb : (V3Z.cross r1 e).sz3 ≤ Mm := by simp only [Mm, mbZ, Nat.add_eq]; omega
  have hc : (V3Z.cross r2 e).sz3 ≤ Mm := by simp only [Mm, mbZ, Nat.add_eq]; omega
  have szx : ∀ v : V3Z, sz v.x ≤ v.sz3 := fun v => by simp only [V3Z.sz3, Nat.add_eq]; omega
  have szy : ∀ v : V3Z, sz v.y ≤ v.sz3 := fun v => by simp only [V3Z.sz3, Nat.add_eq]; omega
  have szz : ∀ v : V3Z, sz v.z ≤ v.sz3 := fun v => by simp only [V3Z.sz3, Nat.add_eq]; omega
  have he : ∀ d : Fin 3, ZP.toZ (match d with | 0 => e.x | 1 => e.y | 2 => e.z) = edgeT s f d := by
    intro d; fin_cases d <;> simp [e, edgeZv]
  have tx : ∀ j : Fin 3, ZP.toZ (match j with | 0 => r0 | 1 => r1 | 2 => r2).x = T box j 0 := by
    intro j; fin_cases j
    · exact congrArg V3.x h0
    · exact congrArg V3.x h1
    · exact congrArg V3.x h2
  have ty : ∀ j : Fin 3, ZP.toZ (match j with | 0 => r0 | 1 => r1 | 2 => r2).y = T box j 1 := by
    intro j; fin_cases j
    · exact congrArg V3.y h0
    · exact congrArg V3.y h1
    · exact congrArg V3.y h2
  have tz : ∀ j : Fin 3, ZP.toZ (match j with | 0 => r0 | 1 => r1 | 2 => r2).z = T box j 2 := by
    intro j; fin_cases j
    · exact congrArg V3.z h0
    · exact congrArg V3.z h1
    · exact congrArg V3.z h2
  have k := fun (F : V3Z → Z) (hF : ∀ v, sz (F v) ≤ v.sz3) =>
    pk3_rep (KW * 8) (F (V3Z.cross r0 e)) (F (V3Z.cross r1 e)) (F (V3Z.cross r2 e)) Mm
      ((hF _).trans ha) ((hF _).trans hb) ((hF _).trans hc)
  have hS := (pairMul_rep (k V3Z.x szx) (hd 0)).add ((pairMul_rep (k V3Z.y szy) (hd 1)).add
    (pairMul_rep (k V3Z.z szz) (hd 2)))
  refine (hS.congr fun t => ?_).mono ?_
  · simp only [supSlot, Fin.sum_univ_three, next_eq]
    have hx := tx 0; have hx1 := tx 1; have hx2 := tx 2
    have hy := ty 0; have hy1 := ty 1; have hy2 := ty 2
    have hz := tz 0; have hz1 := tz 1; have hz2 := tz 2
    have he0 := he 0; have he1 := he 1; have he2 := he 2
    simp only at hx hx1 hx2 hy hy1 hy2 hz hz1 hz2 he0 he1 he2
    rcases Nat.lt_or_ge (t / 8) 3 with hj | hj
    · have : t / 8 = 0 ∨ t / 8 = 1 ∨ t / 8 = 2 := by omega
      rcases this with h | h | h <;>
        simp [sel3Z, tN, h, V3Z.cross, toZ_sub, toZ_mul, hx, hx1, hx2, hy, hy1, hy2, hz, hz1, hz2,
          he0, he1, he2] <;> ring
    · simp [sel3Z, tN, show ¬ t / 8 < 3 by omega, show t / 8 ≠ 0 by omega, show t / 8 ≠ 1 by omega,
        show t / 8 ≠ 2 by omega]
  · show _ ≤ 240 * Mm
    omega

/-- The support conditions of edge `i` (hinted defect and direction witness). -/
def supOkZ (box : Box) (r0 r1 r2 : V3Z) (L : ℕ) (hints : List ℤ) (i : Fin (box.edgePred + 1)) : Bool :=
  let s := box.outerIndex i
  let f := box.outerIndex (nextF box.edgePred i)
  let S := supPackZ r0 r1 r2 s f
  let M := supBoundZ r0 r1 r2 s f
  let h := hints.getD i.val 0
  let thw : ℤ := (-16000 * (L : ℤ) - 1) / 10 ^ 10
  Nat.blt (Nat.mul 4 (Nat.add M h.natAbs)) KK && Nat.blt (Nat.mul 4 (Nat.add M thw.natAbs)) KK &&
    testGeZ (S.2, S.1) ones24L mask24L (-h) &&
    testGeZ (S.2, S.1) ones24L (maskT (box.nonzeroWitness i)) (-thw)

theorem supOkZ_sound (box : Box) (r0 r1 r2 : V3Z) (hints : List ℤ) (i : Fin (box.edgePred + 1))
    (h0 : r0.toV3 = ⟨T box 0 0, T box 0 1, T box 0 2⟩) (h1 : r1.toV3 = ⟨T box 1 0, T box 1 1, T box 1 2⟩)
    (h2 : r2.toV3 = ⟨T box 2 0, T box 2 1, T box 2 2⟩)
    (h : supOkZ box r0 r1 r2 (triL box) hints i = true) :
    supportMaxI box i (box.nonzeroWitness i) * 10 ^ 10 + 16000 * triL box < 0 ∧
      defectI box i ≤ hints.getD i.val 0 := by
  simp only [supOkZ, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hf⟩, hw⟩ := h
  have r := (supPackZ_rep box i r0 r1 r2 h0 h1 h2).neg
  have e : KK = 2 ^ (KW - 1) := rfl
  rw [e] at ha hb
  rw [show ones24L = onesL 24 by simp [onesL], testGeZ_eq] at hf hw
  rw [show mask24L = maskK (fun _ => true) 24 by rw [← maskAll_eq]; simp [maskAll]] at hf
  rw [maskT_eq] at hw
  constructor
  · set wv := box.nonzeroWitness i
    have hb' : 4 * (supBoundZ r0 r1 r2 (box.outerIndex i) (box.outerIndex (nextF box.edgePred i)) +
        (-((-16000 * (triL box : ℤ) - 1) / 10 ^ 10)).natAbs) < 2 ^ (KW - 1) := by
      rw [Int.natAbs_neg]; simpa only [Nat.mul_eq, Nat.add_eq] using hb
    have hr := testGeM_sound r hb' hw
    have hmax : supportMaxI box i wv ≤ (-16000 * triL box - 1) / 10 ^ 10 := by
      refine supportMaxI_le box i wv _ fun j => ?_
      have := hr (8 * j.val + wv.val) (by omega) (by simp)
      rw [supportSlot] at this
      linarith
    have := Int.ediv_mul_le (-16000 * (triL box : ℤ) - 1) (show (10 : ℤ) ^ 10 ≠ 0 by norm_num)
    have := mul_le_mul_of_nonneg_right hmax (show (0 : ℤ) ≤ 10 ^ 10 by norm_num)
    linarith
  · have ha' : 4 * (supBoundZ r0 r1 r2 (box.outerIndex i) (box.outerIndex (nextF box.edgePred i)) +
        (-hints.getD i.val 0).natAbs) < 2 ^ (KW - 1) := by
      rw [Int.natAbs_neg]; simpa only [Nat.mul_eq, Nat.add_eq] using ha
    have hr := testGeM_sound r ha' hf
    have hall : ∀ k : VertexIndex, supportMaxI box i k ≤ hints.getD i.val 0 := by
      intro k
      refine supportMaxI_le box i _ _ fun j => ?_
      have := hr (8 * j.val + k.val) (by omega) rfl
      rw [supportSlot] at this
      linarith
    exact foldr_max_le _ _ _ _ (fun k _ => hall k) (hall 0)

/-! ## Bernstein conditions -/

def cayIQ : IQ := ⟨-3, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩

/-- The Bernstein conditions of `validEdgeK` at the three triangle corners; the edge totals
are taken from `box₀`. -/
def bernEdgeZ (box box₀ : Box) (r0 r1 r2 : V3Z) (hints : List ℤ) : Bool :=
  let L := triL box
  let E := boxE box
  let iv := box.interval
  let P := pbZ E (qS E (iv.min.get 2)) (qS E (iv.min.get 3)) (qS E (iv.min.get 4))
    (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2))) (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3)))
    (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4)))
  let B0 : BQ := ⟨bvZ P (qzOf (totalT box₀ 0)), bmZ P (qzOf (totalT box₀ 0))⟩
  let B1 : BQ := ⟨bvZ P (qzOf (totalT box₀ 1)), bmZ P (qzOf (totalT box₀ 1))⟩
  let B2 : BQ := ⟨bvZ P (qzOf (totalT box₀ 2)), bmZ P (qzOf (totalT box₀ 2))⟩
  let Bc : BQ := ⟨bvZ P (qzOf cayIQ), bmZ P (qzOf cayIQ)⟩
  let TD : ℤ := hintSum box₀ hints
  let n : ℤ := box.edgePred + 1
  let dB := dBoundNum box
  let one := fun (j : Fin 3) (r : V3Z) =>
    let μ := box.ballMultiplier j
    let row := rowV μ.den r (1, 0) B0 B1 B2
    let kc := ofI (μ.num * 1600 * L)
    bernOkZ (padd row.u (psm kc Bc.u)) (Nat.add row.m (Nat.mul (sz kc) Bc.m))
      (ceilDiv (dB * (TD * 10 ^ 10 + 32000 * n * L) * 4 * μ.den) (10 ^ 10))
  one 0 r0 && one 1 r1 && one 2 r2

/-- The conditions of `validEdgeK box hints`; `box₀` is `box` with another interval and view. -/
def edgeZ (box box₀ : Box) (hints : List ℤ) : Bool :=
  let L := triL box
  let r0 := rowZ L box.triangle 0
  let r1 := rowZ L box.triangle 1
  let r2 := rowZ L box.triangle 2
  Nat.blt 0 L && Nat.blt 0 (boxE box) &&
    triOkZ box.root L r0 && triOkZ box.root L r1 && triOkZ box.root L r2 &&
    decide (0 ≤ (box.ballMultiplier 0).num) && decide (0 ≤ (box.ballMultiplier 1).num) &&
    decide (0 ≤ (box.ballMultiplier 2).num) &&
    (List.finRange (box.edgePred + 1)).all (supOkZ box r0 r1 r2 L hints) &&
    bernEdgeZ box box₀ r0 r1 r2 hints

theorem rowZ_toV3' (box : Box) (a : Fin 3) :
    (rowZ (triL box) box.triangle a).toV3 = ⟨T box a 0, T box a 1, T box a 2⟩ := by
  simp only [rowZ, V3Z.toV3, toZ_qS]; rfl

theorem edgeZ_sound (box box₀ : Box) (hints : List ℤ)
    (h₀ : box₀ = { box with interval := iv₀, root := 0, triangle := chamberTriangle })
    (h : edgeZ box box₀ hints = true) : box.Valid := by
  unfold edgeZ at h
  simp only [Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, hE⟩, ht0⟩, ht1⟩, ht2⟩, hμ0⟩, hμ1⟩, hμ2⟩, hsup⟩, hbern⟩ := h
  have hLz : (0 : ℤ) < triL box := by exact_mod_cast hL
  have R := rowZ_toV3' box
  have S := fun i => supOkZ_sound box _ _ _ hints i (R 0) (R 1) (R 2) (hsup i)
  refine valid_of_facts box (hintSum box hints) hLz hE (fun i => ?_) (fun j => ?_)
    (fun i => (S i).1) ?_ (fun j a b c => ?_)
  · fin_cases i
    exacts [triOkZ_sound' box 0 ht0, triOkZ_sound' box 1 ht1, triOkZ_sound' box 2 ht2]
  · fin_cases j
    exacts [hμ0, hμ1, hμ2]
  · unfold totalDefectI hintSum
    exact foldr_sum_le _ _ _ fun i _ => (S i).2
  · have hT : ∀ c, totalT box₀ c = totalI box c := by
      intro c; rw [totalT_eq, h₀]; rfl
    have hTD : hintSum box₀ hints = hintSum box hints := by rw [h₀]; rfl
    set E := boxE box
    set iv := box.interval
    have hP : ∀ q : IQ, PRep KW 27 (bvZ (pbZ E (qS E (iv.min.get 2)) (qS E (iv.min.get 3))
        (qS E (iv.min.get 4)) (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2)))
        (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3))) (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4))))
        (qzOf q)) (bernSlot ((bernWeights box q).zip basisTriples))
        (bmZ (pbZ E (qS E (iv.min.get 2)) (qS E (iv.min.get 3))
        (qS E (iv.min.get 4)) (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2)))
        (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3))) (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4))))
        (qzOf q)) := by
      intro q
      have r := bvZ_rep box (qS E (iv.min.get 2)) (qS E (iv.min.get 3)) (qS E (iv.min.get 4))
        (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2))) (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3)))
        (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4))) (by rw [toZ_qS]; rfl) (by rw [toZ_qS]; rfl)
        (by rw [toZ_qS]; rfl) (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl)
        (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl) (by rw [toZ_sub, toZ_qS, toZ_qS]; rfl) (qzOf q)
      rwa [qzOf_toIQ] at r
    set P := pbZ E (qS E (iv.min.get 2)) (qS E (iv.min.get 3))
        (qS E (iv.min.get 4)) (sub (qS E (iv.max.get 2)) (qS E (iv.min.get 2)))
        (sub (qS E (iv.max.get 3)) (qS E (iv.min.get 3))) (sub (qS E (iv.max.get 4)) (qS E (iv.min.get 4)))
      with hPdef
    have one : ∀ (j : Fin 3), bernOkZ (padd (rowV (box.ballMultiplier j).den
          (rowZ (triL box) box.triangle j) (1, 0)
          ⟨bvZ P (qzOf (totalT box₀ 0)), bmZ P (qzOf (totalT box₀ 0))⟩
          ⟨bvZ P (qzOf (totalT box₀ 1)), bmZ P (qzOf (totalT box₀ 1))⟩
          ⟨bvZ P (qzOf (totalT box₀ 2)), bmZ P (qzOf (totalT box₀ 2))⟩).u
          (psm (ofI ((box.ballMultiplier j).num * 1600 * triL box)) (bvZ P (qzOf cayIQ))))
        (Nat.add (rowV (box.ballMultiplier j).den (rowZ (triL box) box.triangle j) (1, 0)
          ⟨bvZ P (qzOf (totalT box₀ 0)), bmZ P (qzOf (totalT box₀ 0))⟩
          ⟨bvZ P (qzOf (totalT box₀ 1)), bmZ P (qzOf (totalT box₀ 1))⟩
          ⟨bvZ P (qzOf (totalT box₀ 2)), bmZ P (qzOf (totalT box₀ 2))⟩).m
          (Nat.mul (sz (ofI ((box.ballMultiplier j).num * 1600 * triL box))) (bmZ P (qzOf cayIQ))))
        (ceilDiv (dBoundNum box * (hintSum box₀ hints * 10 ^ 10 + 32000 * ((box.edgePred : ℤ) + 1) *
          triL box) * 4 * (box.ballMultiplier j).den) (10 ^ 10)) = true →
        ∀ a b c : Fin 3, dBoundNum box * (hintSum box hints * 10 ^ 10 + 32000 * (box.edgePred + 1) *
          triL box) * 4 * (box.ballMultiplier j).den ≤
            bernI box (adjI box j) a.val b.val c.val * 10 ^ 10 := by
      intro j hk a b c
      have rU := (rowV_rep (μd := (box.ballMultiplier j).den) (t := rowZ (triL box) box.triangle j)
        (x := (1, 0)) (Ba := ⟨bvZ P (qzOf (totalT box₀ 0)), bmZ P (qzOf (totalT box₀ 0))⟩)
        (Bb := ⟨bvZ P (qzOf (totalT box₀ 1)), bmZ P (qzOf (totalT box₀ 1))⟩)
        (Bc := ⟨bvZ P (qzOf (totalT box₀ 2)), bmZ P (qzOf (totalT box₀ 2))⟩)
        (hP _) (hP _) (hP _)).padd ((hP cayIQ).psm (ofI ((box.ballMultiplier j).num * 1600 * triL box)))
      have hr := bernOkZ_sound rU hk a b c
      simp only [bernSlot_eq, hT, toZ_mk0, toZ_ofI] at hr
      have rx : ZP.toZ (rowZ (triL box) box.triangle j).x = T box j 0 := congrArg V3.x (R j)
      have ry : ZP.toZ (rowZ (triL box) box.triangle j).y = T box j 1 := congrArg V3.y (R j)
      have rz : ZP.toZ (rowZ (triL box) box.triangle j).z = T box j 2 := congrArg V3.z (R j)
      rw [rx, ry, rz, hTD] at hr
      have hadj : bernI box (adjI box j) a.val b.val c.val =
          (box.ballMultiplier j).den * (T box j 0 * bernI box (totalI box 0) a.val b.val c.val +
            (T box j 1 * bernI box (totalI box 1) a.val b.val c.val +
              T box j 2 * bernI box (totalI box 2) a.val b.val c.val)) +
            (box.ballMultiplier j).num * 1600 * triL box * bernI box cayIQ a.val b.val c.val := by
        simp only [adjI, bernI_add, bernI_smul, cayIQ]
        ring
      have hc := le_ceilDiv_mul (dBoundNum box * (hintSum box hints * 10 ^ 10 +
        32000 * ((box.edgePred : ℤ) + 1) * triL box) * 4 * (box.ballMultiplier j).den) (10 ^ 10)
        (by norm_num)
      have := mul_le_mul_of_nonneg_right hr (show (0 : ℤ) ≤ ((10 ^ 10 : ℕ) : ℤ) by positivity)
      rw [hadj]
      push_cast at hc this ⊢
      nlinarith
    simp only [bernEdgeZ, Bool.and_eq_true] at hbern
    obtain ⟨⟨h0, h1⟩, h2⟩ := hbern
    fin_cases j
    · exact one 0 h0 a b c
    · exact one 1 h1 a b c
    · exact one 2 h2 a b c

end Noperts.Stellated.ChartKernelF
