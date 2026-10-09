module

public import Noperts.Stellated.ChartKernelEdgeSound
public import Noperts.Stellated.ChartKernelGlobalSound
public import Noperts.Stellated.PairInt

@[expose] public section

/-!
# Faster kernel checkers for chart leaves: packed Bernstein vectors

The leaf checkers `ChartKernel.validEdgeK` and `ChartKernelG.validGlobalK` pack the
Bernstein coefficients of each quadratic `q` on the leaf's box by first computing its ten
Bernstein weights (`bernWeights`) in `Int` arithmetic.  Since the packed vector is linear in
`q`, it is cheaper to compute, once per box, the packed vectors of the ten monomials
(`pbZ`) and combine them (`bvZ`), all in `Nat`-pair arithmetic (`ZP`), which the kernel
evaluates with GMP in a few steps per operation.
-/

namespace Noperts.Stellated.ChartKernelF

open ChartKernel PackedSlots AtlasProjectiveEdgeCertificate AtlasProjectiveView ZP

/-- The ten packed Bernstein vectors of the monomials `1, x, y, z, x², xy, xz, y², yz, z²`
on a box, with slot bounds. -/
structure PB where
  p0 : ℕ × ℕ
  p1 : ℕ × ℕ
  p2 : ℕ × ℕ
  p3 : ℕ × ℕ
  p4 : ℕ × ℕ
  p5 : ℕ × ℕ
  p6 : ℕ × ℕ
  p7 : ℕ × ℕ
  p8 : ℕ × ℕ
  p9 : ℕ × ℕ
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  m3 : ℕ
  m4 : ℕ
  m5 : ℕ
  m6 : ℕ
  m7 : ℕ
  m8 : ℕ
  m9 : ℕ

/-- A fixed interval, for boxes that serve only interval-independent data. -/
def iv₀ : AtlasInterval ℚ := AtlasPose.rootInterval ℚ

/-- Basis vector `m` as a packed pair. -/
def bV (m : ℕ) : ℕ × ℕ := (basisVecsL.getD m 0, 0)

/-- The monomial vectors for the box `[l, l + w] / E` (scaled as in `bernI`). -/
def pbZ (E : ℕ) (lx ly lz wx wy wz : Z) : PB :=
  let V0 := bV 0
  let V1 := bV 1
  let V2 := bV 2
  let V3 := bV 3
  let V4 := bV 4
  let V5 := bV 5
  let V6 := bV 6
  let V7 := bV 7
  let V8 := bV 8
  let V9 := bV 9
  let E4 := Nat.mul 4 E
  let E2 := Nat.mul 2 E
  let c00 : Z := (Nat.mul E4 E, 0)
  let c10 := nmul E4 lx
  let c11 := nmul E2 wx
  let c20 := nmul E4 ly
  let c22 := nmul E2 wy
  let c30 := nmul E4 lz
  let c33 := nmul E2 wz
  let lx4 := nmul 4 lx
  let ly4 := nmul 4 ly
  let lz4 := nmul 4 lz
  let wx2 := nmul 2 wx
  let wy2 := nmul 2 wy
  let wz2 := nmul 2 wz
  let wx4 := nmul 4 wx
  let wy4 := nmul 4 wy
  let wz4 := nmul 4 wz
  let c40 := mul lx4 lx
  let c41 := mul wx4 lx
  let c44 := mul wx4 wx
  let c50 := mul lx4 ly
  let c51 := mul wx2 ly
  let c52 := mul wy2 lx
  let c57 := mul wx wy
  let c60 := mul lx4 lz
  let c61 := mul wx2 lz
  let c63 := mul wz2 lx
  let c68 := mul wx wz
  let c70 := mul ly4 ly
  let c72 := mul wy4 ly
  let c75 := mul wy4 wy
  let c80 := mul ly4 lz
  let c82 := mul wy2 lz
  let c83 := mul wz2 ly
  let c89 := mul wy wz
  let c90 := mul lz4 lz
  let c93 := mul wz4 lz
  let c96 := mul wz4 wz
  { p0 := psm c00 V0
    p1 := padd (psm c10 V0) (psm c11 V1)
    p2 := padd (psm c20 V0) (psm c22 V2)
    p3 := padd (psm c30 V0) (psm c33 V3)
    p4 := padd (padd (psm c40 V0) (psm c41 V1)) (psm c44 V4)
    p5 := padd (padd (psm c50 V0) (psm c51 V1)) (padd (psm c52 V2) (psm c57 V7))
    p6 := padd (padd (psm c60 V0) (psm c61 V1)) (padd (psm c63 V3) (psm c68 V8))
    p7 := padd (padd (psm c70 V0) (psm c72 V2)) (psm c75 V5)
    p8 := padd (padd (psm c80 V0) (psm c82 V2)) (padd (psm c83 V3) (psm c89 V9))
    p9 := padd (padd (psm c90 V0) (psm c93 V3)) (psm c96 V6)
    m0 := Nat.mul (sz c00) 4
    m1 := Nat.add (Nat.mul (sz c10) 4) (Nat.mul (sz c11) 4)
    m2 := Nat.add (Nat.mul (sz c20) 4) (Nat.mul (sz c22) 4)
    m3 := Nat.add (Nat.mul (sz c30) 4) (Nat.mul (sz c33) 4)
    m4 := Nat.add (Nat.add (Nat.mul (sz c40) 4) (Nat.mul (sz c41) 4)) (Nat.mul (sz c44) 4)
    m5 := Nat.add (Nat.add (Nat.mul (sz c50) 4) (Nat.mul (sz c51) 4))
      (Nat.add (Nat.mul (sz c52) 4) (Nat.mul (sz c57) 4))
    m6 := Nat.add (Nat.add (Nat.mul (sz c60) 4) (Nat.mul (sz c61) 4))
      (Nat.add (Nat.mul (sz c63) 4) (Nat.mul (sz c68) 4))
    m7 := Nat.add (Nat.add (Nat.mul (sz c70) 4) (Nat.mul (sz c72) 4)) (Nat.mul (sz c75) 4)
    m8 := Nat.add (Nat.add (Nat.mul (sz c80) 4) (Nat.mul (sz c82) 4))
      (Nat.add (Nat.mul (sz c83) 4) (Nat.mul (sz c89) 4))
    m9 := Nat.add (Nat.add (Nat.mul (sz c90) 4) (Nat.mul (sz c93) 4)) (Nat.mul (sz c96) 4) }

/-- An integer quadratic with pair coefficients. -/
structure QZ where
  c0 : Z
  cx : Z
  cy : Z
  cz : Z
  cxx : Z
  cxy : Z
  cxz : Z
  cyy : Z
  cyz : Z
  czz : Z

def QZ.toIQ (q : QZ) : IQ :=
  ⟨toZ q.c0, toZ q.cx, toZ q.cy, toZ q.cz, toZ q.cxx, toZ q.cxy, toZ q.cxz, toZ q.cyy,
    toZ q.cyz, toZ q.czz⟩

def qzOf (q : IQ) : QZ :=
  ⟨ofI q.c0, ofI q.cx, ofI q.cy, ofI q.cz, ofI q.cxx, ofI q.cxy, ofI q.cxz, ofI q.cyy,
    ofI q.cyz, ofI q.czz⟩

@[simp] theorem qzOf_toIQ (q : IQ) : (qzOf q).toIQ = q := by
  simp [qzOf, QZ.toIQ]

/-- The packed Bernstein vector of `q` on the box of `P`. -/
def bvZ (P : PB) (q : QZ) : ℕ × ℕ :=
  padd (padd (padd (psm q.c0 P.p0) (psm q.cx P.p1)) (padd (psm q.cy P.p2) (psm q.cz P.p3)))
    (padd (padd (padd (psm q.cxx P.p4) (psm q.cxy P.p5)) (padd (psm q.cxz P.p6) (psm q.cyy P.p7)))
      (padd (psm q.cyz P.p8) (psm q.czz P.p9)))

/-- The slot bound of `bvZ P q`. -/
def bmZ (P : PB) (q : QZ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.mul (sz q.c0) P.m0) (Nat.mul (sz q.cx) P.m1))
      (Nat.add (Nat.mul (sz q.cy) P.m2) (Nat.mul (sz q.cz) P.m3)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (sz q.cxx) P.m4) (Nat.mul (sz q.cxy) P.m5))
        (Nat.add (Nat.mul (sz q.cxz) P.m6) (Nat.mul (sz q.cyy) P.m7)))
      (Nat.add (Nat.mul (sz q.cyz) P.m8) (Nat.mul (sz q.czz) P.m9)))

/-! ## Soundness of the packed vectors -/

theorem bV_rep (m : ℕ) (hm : m < 10) :
    PRep KW 27 (bV m) (betaK (basisTriples.getD m ((0, 0, 0), (0, 0, 0), (0, 0, 0)))) 4 := by
  have hl : m < basisTriples.length := by simp [basisTriples]; omega
  have h := basis_rep (basisTriples[m]) (List.getElem_mem hl)
  rw [List.getD_eq_getElem _ _ hl]
  have e : bV m = (vec27 (2 ^ KW) (basisTriples[m]).1 (basisTriples[m]).2.1
      (basisTriples[m]).2.2, 0) := by
    simp only [bV, basisVecsL_eq, basisVecs]
    rw [List.getD_eq_getElem _ _ (by simpa using hl)]
    simp
  rw [e]; exact h

/-- The slot values of `bvZ` for a box whose corner and widths are `l`, `w` (over `E`). -/
theorem bvZ_rep (box : Box) (lx ly lz wx wy wz : Z) (hlx : toZ lx = lo box 0)
    (hly : toZ ly = lo box 1) (hlz : toZ lz = lo box 2) (hwx : toZ wx = hi box 0 - lo box 0)
    (hwy : toZ wy = hi box 1 - lo box 1) (hwz : toZ wz = hi box 2 - lo box 2) (q : QZ) :
    PRep KW 27 (bvZ (pbZ (boxE box) lx ly lz wx wy wz) q)
      (bernSlot ((bernWeights box q.toIQ).zip basisTriples))
      (bmZ (pbZ (boxE box) lx ly lz wx wy wz) q) := by
  have r0 := (bV_rep 0 (by norm_num)).psm
  have r1 := (bV_rep 1 (by norm_num)).psm
  have r2 := (bV_rep 2 (by norm_num)).psm
  have r3 := (bV_rep 3 (by norm_num)).psm
  have r4 := (bV_rep 4 (by norm_num)).psm
  have r5 := (bV_rep 5 (by norm_num)).psm
  have r6 := (bV_rep 6 (by norm_num)).psm
  have r7 := (bV_rep 7 (by norm_num)).psm
  have r8 := (bV_rep 8 (by norm_num)).psm
  have r9 := (bV_rep 9 (by norm_num)).psm
  set E := boxE box
  have f0 := (r0 ((Nat.mul (Nat.mul 4 E) E, 0) : Z)).psm q.c0
  have f1 := ((r0 (nmul (Nat.mul 4 E) lx)).padd (r1 (nmul (Nat.mul 2 E) wx))).psm q.cx
  have f2 := ((r0 (nmul (Nat.mul 4 E) ly)).padd (r2 (nmul (Nat.mul 2 E) wy))).psm q.cy
  have f3 := ((r0 (nmul (Nat.mul 4 E) lz)).padd (r3 (nmul (Nat.mul 2 E) wz))).psm q.cz
  have f4 := (((r0 (mul (nmul 4 lx) lx)).padd (r1 (mul (nmul 4 wx) lx))).padd
    (r4 (mul (nmul 4 wx) wx))).psm q.cxx
  have f5 := (((r0 (mul (nmul 4 lx) ly)).padd (r1 (mul (nmul 2 wx) ly))).padd
    ((r2 (mul (nmul 2 wy) lx)).padd (r7 (mul wx wy)))).psm q.cxy
  have f6 := (((r0 (mul (nmul 4 lx) lz)).padd (r1 (mul (nmul 2 wx) lz))).padd
    ((r3 (mul (nmul 2 wz) lx)).padd (r8 (mul wx wz)))).psm q.cxz
  have f7 := (((r0 (mul (nmul 4 ly) ly)).padd (r2 (mul (nmul 4 wy) ly))).padd
    (r5 (mul (nmul 4 wy) wy))).psm q.cyy
  have f8 := (((r0 (mul (nmul 4 ly) lz)).padd (r2 (mul (nmul 2 wy) lz))).padd
    ((r3 (mul (nmul 2 wz) ly)).padd (r9 (mul wy wz)))).psm q.cyz
  have f9 := (((r0 (mul (nmul 4 lz) lz)).padd (r3 (mul (nmul 4 wz) lz))).padd
    (r6 (mul (nmul 4 wz) wz))).psm q.czz
  have hP := ((f0.padd f1).padd (f2.padd f3)).padd (((f4.padd f5).padd (f6.padd f7)).padd
    (f8.padd f9))
  refine (hP.congr fun t => ?_).mono (le_of_eq ?_)
  · simp only [bernSlot, bernWeights, basisTriples, List.zip_cons_cons, List.zip_nil_right,
      List.foldr_cons, List.foldr_nil, List.getD_cons_succ, List.getD_cons_zero, QZ.toIQ,
      toZ_mul, toZ_nmul, toZ_mk0, hlx, hly, hlz, hwx, hwy, hwz, Nat.mul_eq]
    push_cast
    ring
  · simp only [bmZ, pbZ, Nat.add_eq, Nat.mul_eq]

/-! ## The packed slot test -/

/-- `2 ^ (KW - 1)`. -/
def KK : ℕ := 2 ^ (KW - 1)

/-- `testGeM U n mask th`, given `ones = onesL n`, by a match on `th`. -/
def testGeZ (U : ℕ × ℕ) (ones mask : ℕ) (th : ℤ) : Bool :=
  match th with
  | .ofNat n => Nat.beq (Nat.land (Nat.sub (Nat.add U.1 (Nat.mul KK ones))
      (Nat.add U.2 (Nat.mul n ones))) mask) mask
  | .negSucc n => Nat.beq (Nat.land (Nat.sub (Nat.add (Nat.add U.1 (Nat.mul KK ones))
      (Nat.mul (Nat.succ n) ones)) U.2) mask) mask

theorem testGeZ_eq (U : ℕ × ℕ) (n mask : ℕ) (th : ℤ) :
    testGeZ U (onesL n) mask th = testGeM U n mask th := by
  unfold testGeZ testGeM KK
  cases th with
  | ofNat m =>
      simp only [Int.ofNat_eq_natCast, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Int.natAbs_natCast]
      have h1 : ¬ ((m : ℤ) < 0) := by omega
      have h2 : (0 : ℤ) ≤ m := by omega
      simp only [h1, h2, ↓reduceIte, Nat.add_zero]
      rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  | negSucc m =>
      simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      have h1 : Int.negSucc m < 0 := Int.negSucc_lt_zero m
      have h2 : ¬ (0 : ℤ) ≤ Int.negSucc m := by omega
      simp only [h1, h2, ↓reduceIte, Nat.add_zero, Int.natAbs_negSucc]
      rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

/-- Every slot of `U` (slot bound `M`) selected by the 27-slot mask is at least `th`. -/
def bernOkZ (U : ℕ × ℕ) (M : ℕ) (th : ℤ) : Bool :=
  Nat.blt (Nat.mul 4 (Nat.add M th.natAbs)) KK && testGeZ U ones27L mask27L th

theorem bernOkZ_sound {U : ℕ × ℕ} {d : ℕ → ℤ} {M : ℕ} (hU : PRep KW 27 U d M) {th : ℤ}
    (h : bernOkZ U M th = true) : ∀ a b c : Fin 3, th ≤ d (9 * a.val + 3 * b.val + c.val) := by
  simp only [bernOkZ, Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.add_eq, KK] at h
  have h2 := h.2
  rw [show ones27L = onesL 27 by simp [onesL], testGeZ_eq,
    show mask27L = maskK (fun _ => true) 27 by rw [← maskAll_eq]; simp [maskAll]] at h2
  intro a b c
  exact testGeM_sound hU h.1 h2 _ (by omega) rfl

end Noperts.Stellated.ChartKernelF
