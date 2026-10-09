module

public import Noperts.Stellated.LocalKernelSound
public import Noperts.Stellated.PairInt

@[expose] public section

/-!
# The local integer checker in `Nat`-pair arithmetic

`axisZ` computes the same `AxisOut` as `LocalKernel.axisN` (`axisZ_eq`), with the weight,
budget and variation-ball arithmetic on `Nat` pairs (`ZP`), which the kernel evaluates in
fewer steps than `Int`; `viewValidZ` is `viewValidN` with `axisZ` (`viewValidZ_eq`).
-/

namespace Noperts.Stellated.LocalKernel

open ZP AtlasProjectiveLocalCertificate

structure V3P where
  x : Z
  y : Z
  z : Z

namespace V3P
def of (a : V3) : V3P := ⟨ofI a.x, ofI a.y, ofI a.z⟩
def dot (a b : V3P) : Z := add (add (mul a.x b.x) (mul a.y b.y)) (mul a.z b.z)
theorem toZ_dot (a b : V3) : toZ (dot (of a) (of b)) = V3.dot a b := by
  simp [dot, of, V3.dot]
end V3P

/-- `max` on pairs. -/
def maxZ (a b : Z) : Z := cond (Nat.ble (Nat.add a.1 b.2) (Nat.add b.1 a.2)) b a

theorem toZ_maxZ (a b : Z) : toZ (maxZ a b) = max (toZ a) (toZ b) := by
  unfold maxZ
  by_cases h : a.1 + b.2 ≤ b.1 + a.2
  · have e : Nat.ble (Nat.add a.1 b.2) (Nat.add b.1 a.2) = true := Nat.ble_eq.mpr h
    rw [e, Bool.cond_true, max_eq_right]; simp only [ZP.toZ]; omega
  · have e : Nat.ble (Nat.add a.1 b.2) (Nat.add b.1 a.2) = false := by
      rw [Bool.eq_false_iff]; intro h'; exact h (Nat.ble_eq.mp h')
    rw [e, Bool.cond_false, max_eq_left]; simp only [ZP.toZ]; omega

/-- `|·|` on pairs. -/
def absZ (a : Z) : Z := (Nat.add (Nat.sub a.1 a.2) (Nat.sub a.2 a.1), 0)

theorem toZ_absZ (a : Z) : toZ (absZ a) = |toZ a| := by
  simp only [absZ, ZP.toZ, Nat.add_eq, Nat.sub_eq]
  rcases le_total a.2 a.1 with h | h
  · rw [abs_of_nonneg (by omega)]; omega
  · rw [abs_of_nonpos (by omega)]; omega

/-- The integer value of a pair, by `Int.subNatNat`. -/
def toI (a : Z) : ℤ := Int.subNatNat a.1 a.2

theorem toI_eq (a : Z) : toI a = toZ a := by
  simp [toI, ZP.toZ, Int.subNatNat_eq_coe]

structure Q6P where
  xx : Z
  xy : Z
  xz : Z
  yy : Z
  yz : Z
  zz : Z

def Q6P.toQ6 (q : Q6P) : Q6 := ⟨toZ q.xx, toZ q.xy, toZ q.xz, toZ q.yy, toZ q.yz, toZ q.zz⟩

def mulLinearZ (a b : V3P) : Q6P :=
  ⟨mul a.x b.x, add (mul a.x b.y) (mul a.y b.x), add (mul a.x b.z) (mul a.z b.x),
    mul a.y b.y, add (mul a.y b.z) (mul a.z b.y), mul a.z b.z⟩

def Q6P.add (p q : Q6P) : Q6P :=
  ⟨ZP.add p.xx q.xx, ZP.add p.xy q.xy, ZP.add p.xz q.xz, ZP.add p.yy q.yy, ZP.add p.yz q.yz,
    ZP.add p.zz q.zz⟩

/-- `crossLiftN` on pairs. -/
def crossLiftZ (s e : V3P) (coordinate : Fin 3) : V3P :=
  match coordinate with
  | 0 => ⟨sub (mul s.y e.y) (mul s.z (neg e.z)), sub (mul s.y (neg e.x)) (mul s.z (0, 0)),
      sub (mul s.y (0, 0)) (mul s.z e.x)⟩
  | 1 => ⟨sub (mul s.z (0, 0)) (mul s.x e.y), sub (mul s.z e.z) (mul s.x (neg e.x)),
      sub (mul s.z (neg e.y)) (mul s.x (0, 0))⟩
  | 2 => ⟨sub (mul s.x (neg e.z)) (mul s.y (0, 0)), sub (mul s.x (0, 0)) (mul s.y e.z),
      sub (mul s.x e.x) (mul s.y (neg e.y))⟩

theorem crossLiftZ_eq (s e : V3) (c : Fin 3) :
    (let r := crossLiftZ (V3P.of s) (V3P.of e) c; (⟨toZ r.x, toZ r.y, toZ r.z⟩ : V3)) =
      crossLiftN s e c := by
  fin_cases c <;>
    simp [crossLiftZ, crossLiftN, V3P.of, V3.sub, V3.smul, int_sub_eq]

structure BoxP where
  mx : Z
  my : Z
  mz : Z
  rx : Z
  ry : Z
  rz : Z

def BoxP.of (b : BoxN) : BoxP := ⟨ofI b.mx, ofI b.my, ofI b.mz, ofI b.rx, ofI b.ry, ofI b.rz⟩

/-- `ballN` on pairs. -/
def ballZ (q : Q6P) (b : BoxP) : Z × Z :=
  let center := add (add (add (add (add (mul (mul q.xx b.mx) b.mx) (mul (mul q.xy b.mx) b.my))
    (mul (mul q.xz b.mx) b.mz)) (mul (mul q.yy b.my) b.my)) (mul (mul q.yz b.my) b.mz))
    (mul (mul q.zz b.mz) b.mz)
  let gx := add (add (mul (nmul 2 q.xx) b.mx) (mul q.xy b.my)) (mul q.xz b.mz)
  let gy := add (add (mul q.xy b.mx) (mul (nmul 2 q.yy) b.my)) (mul q.yz b.mz)
  let gz := add (add (mul q.xz b.mx) (mul q.yz b.my)) (mul (nmul 2 q.zz) b.mz)
  let radius := add (add (add (add (add (add (add (add (mul (absZ gx) b.rx) (mul (absZ gy) b.ry))
    (mul (absZ gz) b.rz)) (mul (mul (absZ q.xx) b.rx) b.rx)) (mul (mul (absZ q.xy) b.rx) b.ry))
    (mul (mul (absZ q.xz) b.rx) b.rz)) (mul (mul (absZ q.yy) b.ry) b.ry))
    (mul (mul (absZ q.yz) b.ry) b.rz)) (mul (mul (absZ q.zz) b.rz) b.rz)
  (center, radius)

theorem ballZ_eq (q : Q6P) (b : BoxN) :
    (toZ (ballZ q (BoxP.of b)).1, toZ (ballZ q (BoxP.of b)).2) = ballN q.toQ6 b := by
  simp only [ballZ, ballN, Q6P.toQ6, BoxP.of, toZ_add, toZ_mul, toZ_nmul, toZ_absZ, toZ_ofI,
    Prod.mk.injEq]
  constructor <;> push_cast
  ring

def axisZ (box : Box) (L : Int) (t0 t1 t2 : V3) (bn : BoxN) (j : Fin 4) : AxisOut :=
  let cert := box.certificate j
  let e0 := edgeN cert 0
  let e1 := edgeN cert 1
  let e2 := edgeN cert 2
  let T0 := V3P.of t0
  let T1 := V3P.of t1
  let T2 := V3P.of t2
  let W0 := V3P.of (wcN cert 0)
  let W1 := V3P.of (wcN cert 1)
  let W2 := V3P.of (wcN cert 2)
  let w00 := V3P.dot T0 W0
  let w10 := V3P.dot T1 W0
  let w20 := V3P.dot T2 W0
  let w01 := V3P.dot T0 W1
  let w11 := V3P.dot T1 W1
  let w21 := V3P.dot T2 W1
  let w02 := V3P.dot T0 W2
  let w12 := V3P.dot T1 W2
  let w22 := V3P.dot T2 W2
  let B := cert.B
  let weightsOk := nonneg w00 && nonneg w10 && nonneg w20 && nonneg w01 && nonneg w11 &&
    nonneg w21 && nonneg w02 && nonneg w12 && nonneg w22 &&
    ((pos w00 && pos w10 && pos w20) || (pos w01 && pos w11 && pos w21) ||
      (pos w02 && pos w12 && pos w22))
  let hs := toI (add (add (maxZ w00 (maxZ w10 w20)) (maxZ w01 (maxZ w11 w21)))
    (maxZ w02 (maxZ w12 w22)))
  let budgetOk := decide (2 * B.den * hs ≤ B.num * L * 1600000000)
  let s0 := cert.supportIndex box 0
  let s1 := cert.supportIndex box 1
  let s2 := cert.supportIndex box 2
  let supportsOk := supportFast t0 t1 t2 e0 s0 (cert.mix 0).val (cert.edgeStart 0)
      (cert.edgeFinish 0) (cert.edgeStart₂ 0) (cert.edgeFinish₂ 0) (cert.nonzeroWitness 0) &&
    supportFast t0 t1 t2 e1 s1 (cert.mix 1).val (cert.edgeStart 1)
      (cert.edgeFinish 1) (cert.edgeStart₂ 1) (cert.edgeFinish₂ 1) (cert.nonzeroWitness 1) &&
    supportFast t0 t1 t2 e2 s2 (cert.mix 2).val (cert.edgeStart 2)
      (cert.edgeFinish 2) (cert.edgeStart₂ 2) (cert.edgeFinish₂ 2) (cert.nonzeroWitness 2)
  let E0 := V3P.of e0
  let E1 := V3P.of e1
  let E2 := V3P.of e2
  let S0 := V3P.of (vtx s0)
  let S1 := V3P.of (vtx s1)
  let S2 := V3P.of (vtx s2)
  let q := fun (c : Fin 3) => Q6P.add (Q6P.add (mulLinearZ W0 (crossLiftZ S0 E0 c))
      (mulLinearZ W1 (crossLiftZ S1 E1 c))) (mulLinearZ W2 (crossLiftZ S2 E2 c))
  let bp := BoxP.of bn
  let b0 := ballZ (q 0) bp
  let b1 := ballZ (q 1) bp
  let b2 := ballZ (q 2) bp
  let δ := box.δ
  let scale : Int := 4 * L * L * 2560000000000000
  let variationOk := decide (toI (add (add b0.2 b1.2) b2.2) * 200000000 * B.den * δ.den +
      9 * scale * B.den * δ.den ≤ B.num * δ.num * scale * 200000000)
  { ok := decide (0 < B) && weightsOk && budgetOk && supportsOk && variationOk
    center := ⟨toI b0.1, toI b1.1, toI b2.1⟩ }

def V3P.toV3 (a : V3P) : V3 := ⟨toZ a.x, toZ a.y, toZ a.z⟩

@[simp] theorem V3P.toV3_of (a : V3) : (V3P.of a).toV3 = a := by simp [V3P.toV3, V3P.of]

theorem mulLinearZ_toQ6 (a b : V3P) : (mulLinearZ a b).toQ6 = mulLinearN a.toV3 b.toV3 := by
  simp only [mulLinearZ, Q6P.toQ6, mulLinearN, V3P.toV3, toZ_add, toZ_mul]

theorem Q6P.add_toQ6 (p q : Q6P) : (p.add q).toQ6 = Q6.add p.toQ6 q.toQ6 := by
  simp only [Q6P.add, Q6P.toQ6, Q6.add, toZ_add]

theorem crossLiftZ_toV3 (s e : V3) (c : Fin 3) :
    (crossLiftZ (V3P.of s) (V3P.of e) c).toV3 = crossLiftN s e c := crossLiftZ_eq s e c

theorem weights_eq (a0 a1 a2 b0 b1 b2 c0 c1 c2 : Z) :
    (nonneg a0 && nonneg a1 && nonneg a2 && nonneg b0 && nonneg b1 && nonneg b2 && nonneg c0 &&
      nonneg c1 && nonneg c2 &&
      ((pos a0 && pos a1 && pos a2) || (pos b0 && pos b1 && pos b2) || (pos c0 && pos c1 && pos c2))) =
    decide (0 ≤ min3 (toZ a0) (toZ a1) (toZ a2) ∧ 0 ≤ min3 (toZ b0) (toZ b1) (toZ b2) ∧
      0 ≤ min3 (toZ c0) (toZ c1) (toZ c2) ∧ (0 < min3 (toZ a0) (toZ a1) (toZ a2) ∨
        0 < min3 (toZ b0) (toZ b1) (toZ b2) ∨ 0 < min3 (toZ c0) (toZ c1) (toZ c2))) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, nonneg_iff, pos_iff, decide_eq_true_eq, min3,
    le_min_iff, lt_min_iff]
  tauto

theorem axisZ_eq (box : Box) (L : Int) (t0 t1 t2 : V3) (bn : BoxN) (j : Fin 4) :
    axisZ box L t0 t1 t2 bn j = axisN box L t0 t1 t2 bn j := by
  have hq : ∀ (c : Fin 3), (Q6P.add (Q6P.add
      (mulLinearZ (V3P.of (wcN (box.certificate j) 0))
        (crossLiftZ (V3P.of (vtx ((box.certificate j).supportIndex box 0)))
          (V3P.of (edgeN (box.certificate j) 0)) c))
      (mulLinearZ (V3P.of (wcN (box.certificate j) 1))
        (crossLiftZ (V3P.of (vtx ((box.certificate j).supportIndex box 1)))
          (V3P.of (edgeN (box.certificate j) 1)) c)))
      (mulLinearZ (V3P.of (wcN (box.certificate j) 2))
        (crossLiftZ (V3P.of (vtx ((box.certificate j).supportIndex box 2)))
          (V3P.of (edgeN (box.certificate j) 2)) c))).toQ6 =
      Q6.add (Q6.add (mulLinearN (wcN (box.certificate j) 0)
          (crossLiftN (vtx ((box.certificate j).supportIndex box 0)) (edgeN (box.certificate j) 0) c))
        (mulLinearN (wcN (box.certificate j) 1)
          (crossLiftN (vtx ((box.certificate j).supportIndex box 1)) (edgeN (box.certificate j) 1) c)))
        (mulLinearN (wcN (box.certificate j) 2)
          (crossLiftN (vtx ((box.certificate j).supportIndex box 2)) (edgeN (box.certificate j) 2) c)) := by
    intro c
    simp only [Q6P.add_toQ6, mulLinearZ_toQ6, crossLiftZ_toV3, V3P.toV3_of]
  have hb : ∀ (q : Q6P), ballN q.toQ6 bn = (toZ (ballZ q (BoxP.of bn)).1, toZ (ballZ q (BoxP.of bn)).2) :=
    fun q => (ballZ_eq q bn).symm
  simp only [axisZ, axisN, ← hq, hb]
  congr 1
  · simp only [toI_eq, toZ_add, toZ_maxZ, V3P.toZ_dot, weights_eq, max3]
    rfl
  · simp only [toI_eq]

/-- `viewValidCore` with `axisZ`. -/
def viewValidCoreZ (box : Box) (L : Nat) (t0 t1 t2 : V3) : Bool :=
  let Li : Int := L
  let bn := boxNOf t0 t1 t2
  let o0 := axisZ box Li t0 t1 t2 bn 0
  let o1 := axisZ box Li t0 t1 t2 bn 1
  let o2 := axisZ box Li t0 t1 t2 bn 2
  let o3 := axisZ box Li t0 t1 t2 bn 3
  decide (0 < L) && triOkN box.root Li t0 && triOkN box.root Li t1 && triOkN box.root Li t2 &&
    decide (0 ≤ box.c ∧ 0 ≤ box.δ ∧ 0 ≤ box.r) &&
    o0.ok && o1.ok && o2.ok && o3.ok &&
    baryN box Li o0.center o1.center o2.center o3.center &&
    decide (box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2)

def viewValidZ (box : Box) : Bool :=
  let L := lcm9 box.triangle
  viewValidCoreZ box L (triRow L box.triangle 0) (triRow L box.triangle 1)
    (triRow L box.triangle 2)

theorem viewValidZ_eq (box : Box) : viewValidZ box = viewValidN box := by
  simp only [viewValidZ, viewValidN, viewValidCoreZ, viewValidCore, axisZ_eq]

theorem viewValidZ_sound (box : Box) (h : viewValidZ box = true) : box.ViewValid :=
  viewValidN_sound box (viewValidZ_eq box ▸ h)

end Noperts.Stellated.LocalKernel
