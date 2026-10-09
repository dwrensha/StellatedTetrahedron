module

public import Noperts.Stellated.CornerCertificate
public import Noperts.Stellated.CornerKernelLeaf
public import Noperts.Stellated.FlipPrune
public import Noperts.ParallelBool

@[expose] public section

/-!
# Box trees in the corner blow-up charts

A `Frame` is a box in the chart coordinates of one segment and chart kind.
`Covered` is its claim: no flip-reduced pose whose chart coordinates lie in
the box is Rupert.  Trees split boxes at arbitrary rational points; leaves
are balanced-triple certificates (`CornerCertificate.Row`), flip prunes in
chart coordinates, or hand-offs to a sub-blow-up chart, whose soundness is
supplied from outside as a hypothesis (`CornerHandoff`).
-/

namespace Noperts.Stellated.CornerTree

open SparsePoly CornerPoly CornerCertificate
open AtlasProjectiveView FlipPrune

structure Frame where
  seg : Bool
  kind : ChartKind
  center : List ℚ
  radius : List ℚ
  /-- An affine reparametrization of `u, a, b, c` (`CornerCertificate.affPoly`). -/
  aff : List (List ℚ)
deriving DecidableEq

/-- The frame as a certificate row with an irrelevant triple. -/
def Frame.toRow (f : Frame) : Row where
  seg := f.seg
  kind := f.kind
  center := f.center
  radius := f.radius
  triple := ⟨fun _ _ => 0, fun _ => 0, fun _ => 0⟩
  split := []
  aff := f.aff

def Frame.box (f : Frame) : SparsePoly.Box := f.toRow.box

def Frame.lo (f : Frame) (i : ℕ) : ℚ := f.toRow.lo i

def Frame.hi (f : Frame) (i : ℕ) : ℚ := f.toRow.hi i

/-- The claim of a frame. -/
def Covered (f : Frame) : Prop :=
  ∀ (p : AtlasPose ℝ) (offset : ℝ²) (y : ℕ → ℝ), Coords f.seg f.kind p (affY f.aff y) →
    f.box.Mem y → 0 < y 0 → (f.kind.hasRho = true → 0 < y 6) → (0 < f.hi 1 → 0 < y 1) →
    p.FlipReduced → 1 ≤ viewScale 0 p →
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull

/-- A frame without reparametrization claims its chart coordinates directly. -/
theorem Covered.apply_nil {f : Frame} (hf : Covered f) (haff : f.aff = [])
    (p : AtlasPose ℝ) (offset : ℝ²) (y : ℕ → ℝ) (hc : Coords f.seg f.kind p y)
    (hmem : f.box.Mem y) (hε : 0 < y 0) (hρ : f.kind.hasRho = true → 0 < y 6)
    (hlam : 0 < f.hi 1 → 0 < y 1) (hflip : p.FlipReduced) (hscale : 1 ≤ viewScale 0 p) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull :=
  hf p offset y (by rw [haff, affY_nil]; exact hc) hmem hε hρ hlam hflip hscale

theorem Frame.mem_bounds (f : Frame) {y : ℕ → ℝ} (h : f.box.Mem y) (i : ℕ) :
    (f.lo i : ℝ) ≤ y i ∧ y i ≤ f.hi i := by
  have := abs_le.mp (h i)
  simp only [Frame.lo, Frame.hi, Row.lo, Row.hi]
  push_cast
  simp only [Frame.box] at this
  constructor <;> linarith [this.1, this.2]

/-! ## Splitting -/

def Frame.withVar (f : Frame) (v : ℕ) (lo hi : ℚ) : Frame :=
  { f with center := f.center.set v ((lo + hi) / 2),
           radius := f.radius.set v ((hi - lo) / 2) }

def Frame.lower (f : Frame) (v : ℕ) (m : ℚ) : Frame := f.withVar v (f.lo v) m

def Frame.upper (f : Frame) (v : ℕ) (m : ℚ) : Frame := f.withVar v m (f.hi v)

theorem getD_set_self {l : List ℚ} {v : ℕ} (hv : v < l.length) (a : ℚ) :
    (l.set v a).getD v 0 = a := by
  simp [List.getD_eq_getElem?_getD, hv]

theorem getD_set_ne {l : List ℚ} {v i : ℕ} (h : i ≠ v) (a : ℚ) :
    (l.set v a).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

theorem Frame.mem_withVar (f : Frame) {v : ℕ} (hc : v < f.center.length)
    (hr : v < f.radius.length) {lo hi : ℚ} {y : ℕ → ℝ} (h : f.box.Mem y)
    (hlo : (lo : ℝ) ≤ y v) (hhi : y v ≤ hi) : (f.withVar v lo hi).box.Mem y := by
  intro i
  simp only [Frame.box, Frame.toRow, Row.box, Frame.withVar]
  by_cases hi' : i = v
  · subst hi'
    rw [getD_set_self hc, getD_set_self hr]
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · rw [getD_set_ne hi', getD_set_ne hi']
    exact h i

theorem Frame.withVar_hi (f : Frame) {v : ℕ} (hc : v < f.center.length)
    (hr : v < f.radius.length) (lo hi : ℚ) (i : ℕ) :
    (f.withVar v lo hi).hi i = if i = v then hi else f.hi i := by
  simp only [Frame.hi, Frame.toRow, Row.hi, Row.box, Frame.withVar]
  split_ifs with h
  · subst h; rw [getD_set_self hc, getD_set_self hr]; ring
  · rw [getD_set_ne h, getD_set_ne h]

theorem Frame.lower_hi_le (f : Frame) {v : ℕ} (hc : v < f.center.length)
    (hr : v < f.radius.length) {m : ℚ} (hm : m ≤ f.hi v) (i : ℕ) :
    (f.lower v m).hi i ≤ f.hi i := by
  simp only [Frame.lower]
  rw [f.withVar_hi hc hr]
  split_ifs with h
  · subst h; exact hm
  · exact le_rfl

theorem Frame.upper_hi_le (f : Frame) {v : ℕ} (hc : v < f.center.length)
    (hr : v < f.radius.length) (m : ℚ) (i : ℕ) :
    (f.upper v m).hi i ≤ f.hi i := by
  simp only [Frame.upper]
  rw [f.withVar_hi hc hr]
  split_ifs with h
  · subst h; exact le_rfl
  · exact le_rfl

theorem Frame.mem_split (f : Frame) {v : ℕ} (hc : v < f.center.length)
    (hr : v < f.radius.length) {m : ℚ} {y : ℕ → ℝ} (h : f.box.Mem y) :
    (f.lower v m).box.Mem y ∨ (f.upper v m).box.Mem y := by
  have hb := f.mem_bounds h v
  rcases le_total (y v) m with hm | hm
  · exact Or.inl (f.mem_withVar hc hr h hb.1 hm)
  · exact Or.inr (f.mem_withVar hc hr h hm hb.2)

/-! ## Stellar splits of reparametrized (cone) charts

With `X = Σₖ tₖ vₖ` (the columns of `aff`), the generators `vᵢ, vⱼ` are
joined by `r = α vᵢ + β vⱼ`: where `α tⱼ ≤ β tᵢ` the point is
`(tᵢ - α tⱼ / β) vᵢ + (tⱼ / β) r`, so column `j` becomes `r`. -/

/-- The value of an affine row `[o, c₂, c₃, c₄, c₅]`. -/
noncomputable def affVal (row : List ℚ) (y : ℕ → ℝ) : ℝ :=
  row.getD 0 0 + (row.getD 1 0 * y 2 + row.getD 2 0 * y 3) +
    (row.getD 3 0 * y 4 + row.getD 4 0 * y 5)

theorem affY_eq (aff : List (List ℚ)) (y : ℕ → ℝ) (k : ℕ) :
    affY aff y k = if 2 ≤ k ∧ k ≤ 5 ∧ aff ≠ [] then affVal (aff.getD (k - 2) []) y
      else y k := by
  simp only [affY, affPoly]
  split_ifs
  · simp [affVal, eval_add, eval_scale]; ring
  · simp

def stellarRow (i j : ℕ) (α β : ℚ) (row : List ℚ) : List ℚ :=
  List.ofFn fun k : Fin 5 =>
    if k.val = j - 1 then α * row.getD (i - 1) 0 + β * row.getD (j - 1) 0
    else row.getD k.val 0

def stellarAff (aff : List (List ℚ)) (i j : ℕ) (α β : ℚ) : List (List ℚ) :=
  aff.map (stellarRow i j α β)

/-- The stellar coordinates of a point. -/
noncomputable def stellarPt (y : ℕ → ℝ) (i j : ℕ) (α β : ℚ) : ℕ → ℝ :=
  Function.update (Function.update y j (y j / β)) i (y i - α * y j / β)

theorem getD_ofFn5 (g : Fin 5 → ℚ) (k : ℕ) :
    (List.ofFn g).getD k 0 = if h : k < 5 then g ⟨k, h⟩ else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with h <;> simp

theorem affVal_stellar (row : List ℚ) (y : ℕ → ℝ) {i j : ℕ} (hi : 2 ≤ i ∧ i ≤ 5)
    (hj : 2 ≤ j ∧ j ≤ 5) (hij : i ≠ j) {α β : ℚ} (hβ : β ≠ 0) :
    affVal (stellarRow i j α β row) (stellarPt y i j α β) = affVal row y := by
  have hβ' : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
  obtain ⟨hi0, hi1⟩ := hi
  obtain ⟨hj0, hj1⟩ := hj
  simp only [affVal, stellarRow, getD_ofFn5, stellarPt]
  interval_cases i <;> interval_cases j <;> simp at hij <;>
    simp <;> field_simp <;> ring

theorem affY_stellar (aff : List (List ℚ)) (y : ℕ → ℝ) {i j : ℕ} (hi : 2 ≤ i ∧ i ≤ 5)
    (hj : 2 ≤ j ∧ j ≤ 5) (hij : i ≠ j) {α β : ℚ} (hβ : β ≠ 0) (hne : aff ≠ []) :
    affY (stellarAff aff i j α β) (stellarPt y i j α β) = affY aff y := by
  funext k
  rw [affY_eq, affY_eq]
  have hne' : stellarAff aff i j α β ≠ [] := by simpa [stellarAff] using hne
  by_cases hk : 2 ≤ k ∧ k ≤ 5
  · rw [ite_eq_left ⟨hk.1, hk.2, hne'⟩, ite_eq_left ⟨hk.1, hk.2, hne⟩]
    simp only [stellarAff, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : aff[k - 2]? with
    | none =>
        simp only [Option.map_none, Option.getD_none]
        simp [affVal]
    | some row =>
        simp only [Option.map_some, Option.getD_some]
        exact affVal_stellar row y hi hj hij hβ
  · rw [ite_eq_right (by tauto), ite_eq_right (by tauto)]
    simp only [stellarPt]
    rw [Function.update_apply, Function.update_apply, ite_eq_right (by omega), ite_eq_right (by omega)]

def Frame.stellar (f : Frame) (i j : ℕ) (α β : ℚ) : Frame :=
  { f.withVar j 0 (min (f.hi i / α) (f.hi j / β)) with
    aff := stellarAff f.aff i j α β }

theorem Frame.mem_withVar_of (f : Frame) {v : ℕ} (hc : v < f.center.length)
    (hr : v < f.radius.length) {lo hi : ℚ} {y : ℕ → ℝ}
    (h : ∀ i, i ≠ v → |y i - f.box.center i| ≤ f.box.radius i)
    (hlo : (lo : ℝ) ≤ y v) (hhi : y v ≤ hi) : (f.withVar v lo hi).box.Mem y := by
  intro i
  simp only [Frame.box, Frame.toRow, Row.box, Frame.withVar]
  by_cases hi' : i = v
  · subst hi'
    rw [getD_set_self hc, getD_set_self hr]
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · rw [getD_set_ne hi', getD_set_ne hi']
    exact h i hi'

/-- One half of a stellar split: points with `α tⱼ ≤ β tᵢ`. -/
theorem Frame.mem_stellar (f : Frame) {i j : ℕ} (hij : i ≠ j)
    (hjc : j < f.center.length) (hjr : j < f.radius.length)
    (hloi : f.lo i = 0) (hloj : f.lo j = 0) {α β : ℚ} (hα : 0 < α) (hβ : 0 < β)
    {y : ℕ → ℝ} (hmem : f.box.Mem y) (hcase : (α : ℝ) * y j ≤ β * y i) :
    (f.stellar i j α β).box.Mem (stellarPt y i j α β) := by
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hβ' : (0 : ℝ) < β := by exact_mod_cast hβ
  have bi := f.mem_bounds hmem i
  have bj := f.mem_bounds hmem j
  rw [hloi] at bi
  rw [hloj] at bj
  push_cast at bi bj
  have hq : α * y j / β ≤ y i := by rw [div_le_iff₀ hβ']; linarith
  have hq0 : 0 ≤ α * y j / β := div_nonneg (mul_nonneg hα'.le bj.1) hβ'.le
  have hbox : (f.stellar i j α β).box = (f.withVar j 0 (min (f.hi i / α) (f.hi j / β))).box := rfl
  rw [hbox]
  apply f.mem_withVar_of hjc hjr
  · intro k hk
    by_cases hki : k = i
    · subst hki
      simp only [stellarPt, Function.update_self]
      have := hmem k
      have hl : ((f.lo k : ℚ) : ℝ) = f.box.center k - f.box.radius k := by
        simp [Frame.lo, Frame.toRow, Row.lo, Frame.box]
      have hh : ((f.hi k : ℚ) : ℝ) = f.box.center k + f.box.radius k := by
        simp [Frame.hi, Frame.toRow, Row.hi, Frame.box]
      have bi' := f.mem_bounds hmem k
      rw [hloi] at bi'
      push_cast at bi'
      rw [abs_le]
      have e1 : (0 : ℝ) = f.box.center k - f.box.radius k := by rw [← hl, hloi]; simp
      constructor <;> linarith [bi'.2, hh]
    · simp only [stellarPt]
      rw [Function.update_apply, ite_eq_right hki, Function.update_apply, ite_eq_right hk]
      exact hmem k
  · simp only [stellarPt]
    rw [Function.update_apply, ite_eq_right (Ne.symm hij), Function.update_self]
    push_cast
    exact div_nonneg bj.1 hβ'.le
  · simp only [stellarPt]
    rw [Function.update_apply, ite_eq_right (Ne.symm hij), Function.update_self]
    push_cast
    apply le_min
    · rw [div_le_div_iff₀ hβ' hα']; nlinarith [bi.2]
    · exact div_le_div_of_nonneg_right bj.2 hβ'.le

theorem Frame.stellar_hi_one (f : Frame) (i j : ℕ) (α β : ℚ) (hj : 2 ≤ j)
    (hjc : j < f.center.length) (hjr : j < f.radius.length) :
    (f.stellar i j α β).hi 1 = f.hi 1 := by
  have := f.withVar_hi hjc hjr 0 (min (f.hi i / α) (f.hi j / β)) 1
  rw [ite_eq_right (by omega)] at this
  exact this

/-- The two halves of a stellar split cover the frame. -/
theorem Frame.stellar_cover (f : Frame) {i j : ℕ} (hi : 2 ≤ i ∧ i ≤ 5)
    (hj : 2 ≤ j ∧ j ≤ 5) (hij : i ≠ j) {α β : ℚ} (hα : 0 < α) (hβ : 0 < β)
    (hne : f.aff ≠ []) (hloi : f.lo i = 0) (hloj : f.lo j = 0)
    (hic : i < f.center.length) (hir : i < f.radius.length)
    (hjc : j < f.center.length) (hjr : j < f.radius.length)
    (covL : Covered (f.stellar i j α β)) (covU : Covered (f.stellar j i β α)) :
    Covered f := by
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rcases le_total ((α : ℝ) * y j) (β * y i) with hcase | hcase
  · have e0 : stellarPt y i j α β 0 = y 0 := by
      simp only [stellarPt]; rw [Function.update_apply, Function.update_apply,
        ite_eq_right (by omega), ite_eq_right (by omega)]
    have e1 : stellarPt y i j α β 1 = y 1 := by
      simp only [stellarPt]; rw [Function.update_apply, Function.update_apply,
        ite_eq_right (by omega), ite_eq_right (by omega)]
    have e6 : stellarPt y i j α β 6 = y 6 := by
      simp only [stellarPt]; rw [Function.update_apply, Function.update_apply,
        ite_eq_right (by omega), ite_eq_right (by omega)]
    apply covL p offset (stellarPt y i j α β)
      (by
        show Coords f.seg f.kind p (affY (stellarAff f.aff i j α β) (stellarPt y i j α β))
        rw [affY_stellar f.aff y hi hj hij (ne_of_gt hβ) hne]; exact hc)
      (f.mem_stellar hij hjc hjr hloi hloj hα hβ hmem hcase) (e0 ▸ hε)
      (fun h => e6 ▸ hρ h)
      (fun h => e1 ▸ hlam (f.stellar_hi_one i j α β hj.1 hjc hjr ▸ h)) hflip hscale
  · have e0 : stellarPt y j i β α 0 = y 0 := by
      simp only [stellarPt]; rw [Function.update_apply, Function.update_apply,
        ite_eq_right (by omega), ite_eq_right (by omega)]
    have e1 : stellarPt y j i β α 1 = y 1 := by
      simp only [stellarPt]; rw [Function.update_apply, Function.update_apply,
        ite_eq_right (by omega), ite_eq_right (by omega)]
    have e6 : stellarPt y j i β α 6 = y 6 := by
      simp only [stellarPt]; rw [Function.update_apply, Function.update_apply,
        ite_eq_right (by omega), ite_eq_right (by omega)]
    have hmin : min (f.hi j / β) (f.hi i / α) = min (f.hi i / α) (f.hi j / β) := min_comm _ _
    apply covU p offset (stellarPt y j i β α)
      (by
        show Coords f.seg f.kind p (affY (stellarAff f.aff j i β α) (stellarPt y j i β α))
        rw [affY_stellar f.aff y hj hi (Ne.symm hij) (ne_of_gt hα) hne]; exact hc)
      (f.mem_stellar (Ne.symm hij) hic hir hloj hloi hβ hα hmem (by linarith))
      (e0 ▸ hε) (fun h => e6 ▸ hρ h)
      (fun h => e1 ▸ hlam (f.stellar_hi_one j i β α hi.1 hic hir ▸ h)) hflip hscale

/-! ## Flip prunes in chart coordinates -/

def flipLin (seg : Bool) (kind : ChartKind) (k : Fin 12) : Poly :=
  let X := xPolyK seg kind
  add (add
    (mul (wPoly seg 0) (add (add (add (const (flipCoeff k 0 0))
      (scale (flipCoeff k 0 1) (X 0))) (scale (flipCoeff k 0 2) (X 1)))
      (scale (flipCoeff k 0 3) (X 2))))
    (mul (wPoly seg 1) (add (add (add (const (flipCoeff k 1 0))
      (scale (flipCoeff k 1 1) (X 0))) (scale (flipCoeff k 1 2) (X 1)))
      (scale (flipCoeff k 1 3) (X 2)))))
    (mul (wPoly seg 2) (add (add (add (const (flipCoeff k 2 0))
      (scale (flipCoeff k 2 1) (X 0))) (scale (flipCoeff k 2 2) (X 1)))
      (scale (flipCoeff k 2 3) (X 2))))

def flipPoly (seg : Bool) (kind : ChartKind) (k : Fin 12) : Poly :=
  add (mul (flipLin seg kind k) (flipLin seg kind k))
    (scale (-2) (add (add (mul (wPoly seg 0) (wPoly seg 0))
      (mul (wPoly seg 1) (wPoly seg 1))) (mul (wPoly seg 2) (wPoly seg 2))))

theorem eval_flipLin {seg : Bool} {kind : ChartKind} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (h : Coords seg kind p y) (k : Fin 12) :
    eval y (flipLin seg kind k) =
      flipForm k p.x p.y p.z (normalizedView 0 p) := by
  simp only [flipLin, flipForm, Fin.sum_univ_three, eval_add, eval_mul, eval_scale,
    eval_const, eval_wPoly, ← h.view, ← h.cx, ← h.cy, ← h.cz]

theorem eval_flipPoly {seg : Bool} {kind : ChartKind} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (h : Coords seg kind p y) (k : Fin 12) :
    eval y (flipPoly seg kind k) =
      flipForm k p.x p.y p.z (normalizedView 0 p) ^ 2 -
        2 * (normalizedView 0 p 0 ^ 2 + normalizedView 0 p 1 ^ 2 +
          normalizedView 0 p 2 ^ 2) := by
  simp only [flipPoly, eval_add, eval_mul, eval_scale, eval_flipLin h, eval_wPoly,
    ← h.view]
  push_cast
  ring

theorem not_flipReduced_of_flipPoly_pos {seg : Bool} {kind : ChartKind}
    {p : AtlasPose ℝ} {y : ℕ → ℝ} (h : Coords seg kind p y) (k : Fin 12)
    (hscale : 1 ≤ viewScale 0 p) (hpos : 0 < eval y (flipPoly seg kind k)) :
    ¬ p.FlipReduced := by
  intro hflip
  have hsq := flipForm_sq_le_of_flipReduced hflip k
  rw [eval_flipPoly h] at hpos
  set σ := viewScale 0 p with hσ
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hscale
  have hview : p.view = fun c => σ * normalizedView 0 p c := by
    funext c
    simp only [normalizedView, ← viewVector_eq_view]
    rw [hσ, mul_div_cancel₀ _ (ne_of_gt (hσ ▸ hσ0))]
  have hlin : flipForm k p.x p.y p.z p.view =
      σ * flipForm k p.x p.y p.z (normalizedView 0 p) := by
    rw [hview]
    simp only [flipForm, Fin.sum_univ_three]
    ring
  have hn := view_norm_sq p
  rw [hview] at hn
  simp only at hn
  rw [hlin] at hsq
  have h2 : σ ^ 2 * (flipForm k p.x p.y p.z (normalizedView 0 p) ^ 2 -
      2 * (normalizedView 0 p 0 ^ 2 + normalizedView 0 p 1 ^ 2 +
        normalizedView 0 p 2 ^ 2)) ≤ 0 := by
    linear_combination hsq - 2 * hn
  have := mul_pos (pow_pos hσ0 2) hpos
  linarith

/-! ## Trees -/

/-- Hand-off targets: the tube around `X = 0`, the wedge, the wedge tube. -/
inductive Handoff where
  | tube | wedge | wtube | skew | cone | pocket | spocket | ppocket | cpocket
deriving DecidableEq

inductive Leaf where
  | cert (row : Row)
  | flip (k : Fin 12)
  | handoff (target : Handoff)
  /-- A certificate citing the table's shared fact row `fact` (see
  `Row.SharedValid`). -/
  | shared (row : Row) (fact : ℕ)
  /-- A certificate citing shared fact row `fact` and its polynomial data, checked
  by the kernel-friendly cheap bound (`CornerKernel.SharedPValid`). -/
  | sharedP (row : Row) (fact : ℕ)
deriving DecidableEq

inductive Node where
  | split (id : ℕ) (frame : Frame) (v : ℕ) (m : ℚ) (lower upper : ℕ)
  /-- A stellar split of a cone chart: `lower` takes `α tⱼ ≤ β tᵢ`. -/
  | stellar (id : ℕ) (frame : Frame) (i j : ℕ) (α β : ℚ) (lower upper : ℕ)
  | leaf (id : ℕ) (frame : Frame) (leaf : Leaf)
deriving DecidableEq

def Node.id : Node → ℕ
  | .split id .. | .stellar id .. | .leaf id .. => id

def Node.frame : Node → Frame
  | .split _ frame _ _ _ _ | .stellar _ frame _ _ _ _ _ _ | .leaf _ frame _ => frame

/-- The hand-off obligations: which frames a hand-off leaf may rely on is
decided by `HandoffValid`, and the hypothesis `HandoffSound` turns a valid
hand-off into coverage. -/
structure Handoffs where
  Valid : Handoff → Frame → Prop
  [dec : ∀ h f, Decidable (Valid h f)]

attribute [instance] Handoffs.dec

/-- `row` is valid against the shared fact row `facts[k]`. -/
def SharedFactOk (facts : Array Row) (k : ℕ) (row : Row) : Prop :=
  match facts[k]? with
  | some fact => row.SharedValid fact
  | none => False

instance (facts : Array Row) (k : ℕ) (row : Row) : Decidable (SharedFactOk facts k row) := by
  unfold SharedFactOk
  cases facts[k]? <;> infer_instance

/-- `row` is valid against fact row `facts[k]` with polynomial data `fps[k]`. -/
def SharedPFactOk (facts : Array Row) (fps : Array CornerKernel.FactPoly) (k : ℕ)
    (row : Row) : Prop :=
  match facts[k]?, fps[k]? with
  | some fact, some fp => CornerKernel.SharedPValid row fact fp
  | _, _ => False

instance (facts : Array Row) (fps : Array CornerKernel.FactPoly) (k : ℕ) (row : Row) :
    Decidable (SharedPFactOk facts fps k row) := by
  unfold SharedPFactOk
  cases facts[k]? <;> cases fps[k]? <;> infer_instance

/-- The polynomial data `fps[k]` is correct for fact row `facts[k]`. -/
def FactPolyAt (facts : Array Row) (fps : Array CornerKernel.FactPoly) (k : Fin fps.size) :
    Prop :=
  match facts[k.val]? with
  | some fact => fps[k].Ok fact
  | none => False

instance (facts : Array Row) (fps : Array CornerKernel.FactPoly) (k : Fin fps.size) :
    Decidable (FactPolyAt facts fps k) := by
  unfold FactPolyAt
  split <;> infer_instance

/-- Each fact's polynomial data is correct. -/
def FactPolysOk (facts : Array Row) (fps : Array CornerKernel.FactPoly) : Prop :=
  ∀ k : Fin fps.size, FactPolyAt facts fps k

instance (facts : Array Row) (fps : Array CornerKernel.FactPoly) :
    Decidable (FactPolysOk facts fps) := by
  unfold FactPolysOk; infer_instance

def Leaf.Valid (H : Handoffs) (facts : Array Row) (fps : Array CornerKernel.FactPoly)
    (f : Frame) : Leaf → Prop
  | .cert row => row.seg = f.seg ∧ row.kind = f.kind ∧ row.center = f.center ∧
      row.radius = f.radius ∧ row.aff = f.aff ∧ row.Valid
  | .flip k => (∀ x ∈ f.radius, 0 ≤ x) ∧
      PosOk f.toRow.positiveVars f.box (cmp f.aff (flipPoly f.seg f.kind k))
  | .handoff h => H.Valid h f
  | .shared row k => row.seg = f.seg ∧ row.kind = f.kind ∧ row.center = f.center ∧
      row.radius = f.radius ∧ row.aff = f.aff ∧ SharedFactOk facts k row
  | .sharedP row k => row.seg = f.seg ∧ row.kind = f.kind ∧ row.center = f.center ∧
      row.radius = f.radius ∧ row.aff = f.aff ∧ SharedPFactOk facts fps k row

instance (H : Handoffs) (facts : Array Row) (fps : Array CornerKernel.FactPoly) (f : Frame)
    (leaf : Leaf) : Decidable (leaf.Valid H facts fps f) := by
  cases leaf <;> unfold Leaf.Valid <;> infer_instance

def Node.ValidAt (H : Handoffs) (facts : Array Row) (fps : Array CornerKernel.FactPoly)
    (get : ℕ → Node) (size : ℕ) :
    Node → Prop
  | .split id f v m lower upper =>
      v < f.center.length ∧ v < f.radius.length ∧ m ≤ f.hi v ∧
      id < lower ∧ lower < size ∧ id < upper ∧ upper < size ∧
      (get lower).frame = f.lower v m ∧ (get upper).frame = f.upper v m
  | .stellar id f i j α β lower upper =>
      (2 ≤ i ∧ i ≤ 5) ∧ (2 ≤ j ∧ j ≤ 5) ∧ i ≠ j ∧ 0 < α ∧ 0 < β ∧ f.aff ≠ [] ∧
      f.lo i = 0 ∧ f.lo j = 0 ∧ i < f.center.length ∧ i < f.radius.length ∧
      j < f.center.length ∧ j < f.radius.length ∧
      id < lower ∧ lower < size ∧ id < upper ∧ upper < size ∧
      (get lower).frame = f.stellar i j α β ∧ (get upper).frame = f.stellar j i β α
  | .leaf _ f l => l.Valid H facts fps f

instance (H : Handoffs) (facts : Array Row) (fps : Array CornerKernel.FactPoly)
    (get : ℕ → Node) (size : ℕ) (n : Node) :
    Decidable (n.ValidAt H facts fps get size) := by
  cases n <;> unfold Node.ValidAt <;> infer_instance

structure Table where
  get : ℕ → Node
  size : ℕ
  /-- Shared fact rows cited by `Leaf.shared`. -/
  facts : Array Row := #[]
  /-- Polynomial data of the facts, cited by `Leaf.sharedP`. -/
  fpolys : Array CornerKernel.FactPoly := #[]

def Table.Valid (H : Handoffs) (t : Table) (root : Frame) : Prop :=
  0 < t.size ∧ (t.get 0).frame = root ∧ (∀ fact ∈ t.facts, fact.KeyFacts) ∧
    FactPolysOk t.facts t.fpolys ∧ ∀ i : Fin t.size, (t.get i).id = i ∧ (t.get i).ValidAt H t.facts t.fpolys t.get t.size

instance (H : Handoffs) (t : Table) (root : Frame) : Decidable (t.Valid H root) := by
  unfold Table.Valid; infer_instance

/-- One row of `Table.Valid`, as a Boolean.  Indices past the end are
vacuously true: `allParB`'s last chunk can run past `t.size`. -/
def Table.rowB (H : Handoffs) (t : Table) (i : ℕ) : Bool :=
  if i < t.size then decide ((t.get i).id = i ∧ (t.get i).ValidAt H t.facts t.fpolys t.get t.size)
  else true

/-- `Table.Valid`, with the rows checked in parallel chunks. -/
def Table.validParB (H : Handoffs) (t : Table) (root : Frame) (taskCount : ℕ) : Bool :=
  decide (0 < t.size ∧ (t.get 0).frame = root ∧ (∀ fact ∈ t.facts, fact.KeyFacts) ∧
      FactPolysOk t.facts t.fpolys) &&
    Noperts.ParallelBool.allParB (t.rowB H) t.size taskCount

theorem Table.Valid.of_parB {H : Handoffs} {t : Table} {root : Frame} {taskCount : ℕ}
    (h : t.validParB H root taskCount = true) : t.Valid H root := by
  unfold Table.validParB at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  refine ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, fun i => ?_⟩
  have := Noperts.ParallelBool.all_of_parB h.2 i.val i.isLt
  simpa [Table.rowB, i.isLt] using this

theorem leaf_covered (H : Handoffs) (hH : ∀ h f, H.Valid h f → Covered f)
    (facts : Array Row) (hfacts : ∀ fact ∈ facts, fact.KeyFacts)
    (fps : Array CornerKernel.FactPoly) (hfps : FactPolysOk facts fps)
    (f : Frame) (leaf : Leaf) (hv : leaf.Valid H facts fps f) : Covered f := by
  intro p offset y hc hmem hε hρ hlam hflip hscale
  cases leaf with
  | cert row =>
      obtain ⟨hseg, hkind, hcenter, hradius, haff, hrow⟩ := hv
      have hbox : row.box = f.box := by
        simp [Frame.box, Frame.toRow, Row.box, hcenter, hradius]
      have hhi : row.hi 1 = f.hi 1 := by
        simp [Row.hi, Frame.hi, Frame.toRow, Row.box, hcenter, hradius]
      apply row.not_rupert hrow p offset y (hseg ▸ hkind ▸ haff ▸ hc) (hbox ▸ hmem) hε
        (fun ht => hρ (by simpa [Row.isTube, hkind] using ht))
        (fun h => hlam (hhi ▸ h)) hscale
  | flip k =>
      obtain ⟨hrad, hpos⟩ := hv
      exact absurd hflip (not_flipReduced_of_flipPoly_pos hc k hscale
        (eval_cmp f.aff y _ ▸ PosOk.sound hpos hmem (f.toRow.radius_nonneg hrad)
          (f.toRow.positiveVars_sound hε
            (fun ht => hρ (by simpa [Row.isTube, Frame.toRow] using ht)) hlam)))
  | handoff h => exact hH h f hv p offset y hc hmem hε hρ hlam hflip hscale
  | shared row k =>
      obtain ⟨hseg, hkind, hcenter, hradius, haff, hrow⟩ := hv
      unfold SharedFactOk at hrow
      cases hk : facts[k]? with
      | none => simp [hk] at hrow
      | some fact =>
          simp only [hk] at hrow
          have hfact : fact.KeyFacts := hfacts fact (Array.mem_of_getElem? hk)
          have hbox : row.box = f.box := by
            simp [Frame.box, Frame.toRow, Row.box, hcenter, hradius]
          have hhi : row.hi 1 = f.hi 1 := by
            simp [Row.hi, Frame.hi, Frame.toRow, Row.box, hcenter, hradius]
          apply row.not_rupert_shared fact hfact hrow p offset y
            (hseg ▸ hkind ▸ haff ▸ hc) (hbox ▸ hmem) hε
            (fun ht => hρ (by simpa [Row.isTube, hkind] using ht))
            (fun h => hlam (hhi ▸ h)) hscale

  | sharedP row k =>
      obtain ⟨hseg, hkind, hcenter, hradius, haff, hrow⟩ := hv
      unfold SharedPFactOk at hrow
      cases hk : facts[k]? with
      | none => simp [hk] at hrow
      | some fact =>
          cases hp : fps[k]? with
          | none => simp [hk, hp] at hrow
          | some fp =>
              simp only [hk, hp] at hrow
              have hfact : fact.KeyFacts := hfacts fact (Array.mem_of_getElem? hk)
              have hkl : k < fps.size := by
                by_contra h
                simp [Array.getElem?_eq_none (by omega : fps.size ≤ k)] at hp
              have hok := hfps ⟨k, hkl⟩
              simp only [FactPolyAt, hk, Fin.getElem_fin] at hok
              have hfp' : fps[k] = fp := by
                exact Array.getElem_eq_iff.mpr hp
              rw [hfp'] at hok
              have hbox : row.box = f.box := by
                simp [Frame.box, Frame.toRow, Row.box, hcenter, hradius]
              have hhi : row.hi 1 = f.hi 1 := by
                simp [Row.hi, Frame.hi, Frame.toRow, Row.box, hcenter, hradius]
              apply CornerKernel.not_rupert_sharedP row fact fp hfact hok hrow p offset y
                (hseg ▸ hkind ▸ haff ▸ hc) (hbox ▸ hmem) hε
                (fun ht => hρ (by simpa [Row.isTube, hkind] using ht))
                (fun h => hlam (hhi ▸ h)) hscale

theorem Table.covered_ix (H : Handoffs) (hH : ∀ h f, H.Valid h f → Covered f)
    (t : Table)
    (hfacts : ∀ fact ∈ t.facts, fact.KeyFacts) (hfps : FactPolysOk t.facts t.fpolys)
    (hrows : ∀ i : Fin t.size, (t.get i).id = i ∧ (t.get i).ValidAt H t.facts t.fpolys t.get t.size)
    (i : ℕ) (hi : i < t.size) : Covered (t.get i).frame := by
  obtain ⟨hid, hvalid⟩ := hrows ⟨i, hi⟩
  generalize hn : t.get i = n at hid hvalid ⊢
  cases n with
  | leaf id f l => exact leaf_covered H hH t.facts hfacts t.fpolys hfps f l hvalid
  | split id f v m lower upper =>
      obtain ⟨hc, hr, hm, hl, hls, hu, hus, hlf, huf⟩ := hvalid
      have hid' : id = i := by simpa [Node.id] using hid
      have covL := Table.covered_ix H hH t hfacts hfps hrows lower hls
      have covU := Table.covered_ix H hH t hfacts hfps hrows upper hus
      rw [hlf] at covL
      rw [huf] at covU
      intro p offset y hcoords hmem hε hρ hlam hflip hscale
      rcases f.mem_split hc hr (m := m) hmem with h | h
      · exact covL p offset y hcoords h hε hρ
          (fun h' => hlam (lt_of_lt_of_le h' (f.lower_hi_le hc hr hm 1))) hflip hscale
      · exact covU p offset y hcoords h hε hρ
          (fun h' => hlam (lt_of_lt_of_le h' (f.upper_hi_le hc hr m 1))) hflip hscale
  | stellar id f vi vj α β lower upper =>
      obtain ⟨hi, hj, hij, hα, hβ, hne, hloi, hloj, hic, hir, hjc, hjr, hl, hls, hu, hus,
        hlf, huf⟩ := hvalid
      have hid' : id = i := by simpa [Node.id] using hid
      have covL := Table.covered_ix H hH t hfacts hfps hrows lower hls
      have covU := Table.covered_ix H hH t hfacts hfps hrows upper hus
      rw [hlf] at covL
      rw [huf] at covU
      intro p offset y hcoords hmem hε hρ hlam hflip hscale
      exact f.stellar_cover hi hj hij hα hβ hne hloi hloj hic hir hjc hjr covL covU
        p offset y hcoords hmem hε hρ hlam hflip hscale
termination_by t.size - i
decreasing_by
  all_goals omega

theorem Table.covered (H : Handoffs) (hH : ∀ h f, H.Valid h f → Covered f)
    (t : Table) (root : Frame) (hv : t.Valid H root) : Covered root := by
  obtain ⟨hsize, hroot, hfacts, hfps, hrows⟩ := hv
  have := t.covered_ix H hH hfacts hfps hrows 0 hsize
  rwa [hroot] at this

end Noperts.Stellated.CornerTree

end
