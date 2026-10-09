module

public import Noperts.Stellated.CornerTree
public import Noperts.Stellated.SelfShadow

@[expose] public section

/-!
# Root frames and hand-offs of the corner blow-up

Chart variables: `0 ε, 1 λ, 2 u, 3 a, 4 b, 5 c` and, in the tube charts,
`6 ρ` (tube) or `6 σ` (wedge tube).  The plain chart has seven root faces:
`λ = 1`, and `a, b, c = ±1` with `λ ∈ [0, 1]`.  Near `X̂ = 0` on the `λ = 1`
face the tube chart `X̂ = ρ d̂` takes over (six faces of `d̂`), and near the
first-order degenerate wedge the wedge chart (`α, τ, η`) and then the wedge
tube (`α = σ ᾱ`, `η = σ η̄`, four faces) take over.
-/

namespace Noperts.Stellated.CornerHandoff

open SparsePoly CornerPoly CornerCertificate CornerTree
open AtlasProjectiveView

def rho0 : ℚ := 1 / 16
def alpha0 : ℚ := 1 / 8
def eta0 : ℚ := 1 / 8
def tau0 : ℚ := 1 / 8
def tau1 : ℚ := 3 / 4
def sigma0 : ℚ := 1 / 16
def skewB0 : ℚ := 1 / 64
def skewB1 : ℚ := 5 / 12
def skewDelta : ℚ := 1 / 8

/-- `±1` for a face index: even faces are `+1`. -/
def faceSign (face : ℕ) : ℚ := if face % 2 = 0 then 1 else -1

/-- The plain root faces: `0` is `λ = 1`; `1 + k` puts variable `3 + k / 2` at
`faceSign k`. -/
def plainRoot (e0 : ℚ) (seg : Bool) (face : Fin 7) : Frame :=
  if face.val = 0 then
    ⟨seg, .plain, [e0 / 2, 1, 1 / 2, 0, 0, 0], [e0 / 2, 0, 1 / 2, 1, 1, 1], []⟩
  else
    let k := face.val - 1
    ⟨seg, .plain,
      ([e0 / 2, 1 / 2, 1 / 2, 0, 0, 0].set (3 + k / 2) (faceSign k)),
      ([e0 / 2, 1 / 2, 1 / 2, 1, 1, 1].set (3 + k / 2) 0), []⟩

def tubeRoot (e0 : ℚ) (seg : Bool) (face : Fin 6) : Frame :=
  ⟨seg, .tube,
    ([e0 / 2, 1, 1 / 2, 0, 0, 0, rho0 / 2].set (3 + face.val / 2) (faceSign face.val)),
    ([e0 / 2, 0, 1 / 2, 1, 1, 1, rho0 / 2].set (3 + face.val / 2) 0), []⟩

def wedgeRoot (e0 : ℚ) (seg : Bool) : Frame :=
  ⟨seg, .wedge, [e0 / 2, 1, 1 / 2, 0, (tau0 + tau1) / 2, 0],
    [e0 / 2, 0, 1 / 2, alpha0, (tau1 - tau0) / 2, eta0], []⟩

/-- Wedge-tube faces: `ᾱ = ±1` (faces 0, 1) and `η̄ = ±1` (faces 2, 3). -/
def wtubeRoot (e0 : ℚ) (seg : Bool) (face : Fin 4) : Frame :=
  ⟨seg, .wtube,
    ([e0 / 2, 1, 1 / 2, 0, (tau0 + tau1) / 2, 0, sigma0 / 2].set
      (3 + 2 * (face.val / 2)) (faceSign face.val)),
    ([e0 / 2, 0, 1 / 2, 1, (tau1 - tau0) / 2, 1, sigma0 / 2].set
      (3 + 2 * (face.val / 2)) 0), []⟩

/-- The skew chart root (segment B only): `b ∈ [skewB0, skewB1]` (smaller
`b` near the line is inside the tube),
`|c + skewK b| ≤ skewDelta`. -/
def skewRoot (e0 : ℚ) : Frame :=
  ⟨true, .skew, [e0 / 2, 1, 1 / 2, 0, (skewB0 + skewB1) / 2, 0],
    [e0 / 2, 0, 1 / 2, 1, (skewB1 - skewB0) / 2, skewDelta], []⟩

/-- The exact corner view (`λ = 0`, `u = 0`, segment A), with `X̂` on the
cube face `3 + face / 2 = faceSign face`. -/
def zeroRoot (e0 : ℚ) (face : Fin 6) : Frame :=
  ⟨false, .plain,
    ([e0 / 2, 0, 0, 0, 0, 0].set (3 + face.val / 2) (faceSign face.val)),
    ([e0 / 2, 0, 0, 1, 1, 1].set (3 + face.val / 2) 0), []⟩

/-! ## Cone charts at the view tie `u = 9/11` of segment A

Near the tie with `X̂` small, the first-order clearance is linear in
`(u - 9/11, X̂)` and kinks along hyperplanes through `(9/11, 0)`.  Cone charts
`(u, a, b, c) = (9/11, 0, 0, 0) + Σₖ tₖ vₖ`, refined by stellar splits, align
with them.  The sixteen roots are the orthants of `|u - 9/11| ≤ coneDU`,
`|a|, |b|, |c| ≤ coneR`, with `t ∈ [0, 1]⁴`. -/

def coneTie : ℚ := 9 / 11
def coneDU : ℚ := 1 / 64
def coneR : ℚ := 1 / 16

def coneSign (b : Bool) : ℚ := if b then -1 else 1

def coneAff (neg : Fin 4 → Bool) : List (List ℚ) :=
  [[coneTie, coneSign (neg 0) * coneDU, 0, 0, 0],
   [0, 0, coneSign (neg 1) * coneR, 0, 0],
   [0, 0, 0, coneSign (neg 2) * coneR, 0],
   [0, 0, 0, 0, coneSign (neg 3) * coneR]]

def coneRoot (e0 : ℚ) (neg : Fin 4 → Bool) : Frame :=
  ⟨false, .plain, [e0 / 2, 1, 1 / 2, 1 / 2, 1 / 2, 1 / 2],
    [e0 / 2, 0, 1 / 2, 1 / 2, 1 / 2, 1 / 2], coneAff neg⟩

/-! ## Pockets: the scale `a ~ ε` on the tube face near `b = 9/22`

Near `a = 0`, `b = 9/22` to `b = 1` on the tube faces `c = ±1`, the certificate changes
along `a = κ ε`; the charts `atube` (`a = ε α`, `|α| ≤ atubeA`) and `btube`
(`a = ±atubeA ε + w`) resolve this scale. -/

def pocketB0 : ℚ := 9 / 22 - 1 / 32
def pocketB1 : ℚ := 1
def pocketW : ℚ := 1 / 64

/-- The pockets: segment, tube face (`4`: `c = 1`, `5`: `c = -1`), `u` range. -/
def pocketSpec : Fin 3 → Bool × Fin 6 × ℚ × ℚ
  | 0 => (false, 4, coneTie + coneDU, 1)
  | 1 => (true, 4, 0, 1)
  | 2 => (true, 5, 0, 1)

/-- The chart of each pocket root: `0` atube, `1` btube (`+`), `2` btube (`-`). -/
def pocketKind : Fin 3 → ChartKind
  | 0 => .atube
  | 1 => .btube false
  | 2 => .btube true

def pocketVar3 : Fin 3 → ℚ × ℚ
  | 0 => (-atubeA, atubeA)
  | 1 => (0, pocketW)
  | 2 => (-pocketW, 0)

def pocketRoot (e0 : ℚ) (k m : Fin 3) : Frame :=
  ⟨(pocketSpec k).1, pocketKind m,
    [e0 / 2, 1, ((pocketSpec k).2.2.1 + (pocketSpec k).2.2.2) / 2,
      ((pocketVar3 m).1 + (pocketVar3 m).2) / 2, (pocketB0 + pocketB1) / 2,
      faceSign (pocketSpec k).2.1.val, rho0 / 2],
    [e0 / 2, 0, ((pocketSpec k).2.2.2 - (pocketSpec k).2.2.1) / 2,
      ((pocketVar3 m).2 - (pocketVar3 m).1) / 2, (pocketB1 - pocketB0) / 2, 0, rho0 / 2], []⟩

/-- The u-range of the tie pockets beyond the view tie (wider than the cone's
`coneDU`: stellar sub-cones of the truncated cone reach a little past it). -/
def tpocketDU : ℚ := 1

/-- The `a`-range of the tie pockets (in tube coordinates, `|a| ≤ tpocketW · ρ`): the
cone frames that reach the tie pockets carry `|a|` up to about `ρ / 2`. -/
def tpocketW : ℚ := 1

/-- The tie pockets' third coordinate: `a = ε α` (`|α| ≤ atubeA`) or `a = ± atubeA ε + w`. -/
def tpocketVar3 : Fin 3 → ℚ × ℚ
  | 0 => (-atubeA, atubeA)
  | 1 => (0, tpocketW)
  | 2 => (-tpocketW, 0)

/-- The tie pocket roots, reached from cone frames: tube face `b = 1` (`face 0`, with
`c ∈ [0, 1]`) or `c = 1` (`face 1`, with `b ∈ [0, 1]`), `u ∈ [coneTie, coneTie + tpocketDU]`,
in the pocket chart `m`. -/
def tpocketRoot (e0 : ℚ) (face : Fin 2) (m : Fin 3) : Frame :=
  ⟨false, pocketKind m,
    [e0 / 2, 1, coneTie + tpocketDU / 2, ((tpocketVar3 m).1 + (tpocketVar3 m).2) / 2,
      if face = 0 then 1 else 1 / 2, if face = 0 then 1 / 2 else 1, rho0 / 2],
    [e0 / 2, 0, tpocketDU / 2, ((tpocketVar3 m).2 - (tpocketVar3 m).1) / 2,
      if face = 0 then 0 else 1 / 2, if face = 0 then 1 / 2 else 0, rho0 / 2], []⟩

/-- A cone frame's hand-off to the tie pockets, in its reparametrized coordinates
`u, a, b, c`: `u` in the pocket range, `0 ≤ b, c ≤ ρ₀`, and `|a| ≤ tpocketW · (b + c) / 2`
(so `|a| ≤ tpocketW · max b c`; each point uses the tube face of its larger coordinate). -/
def cpocketIneqs (aff : List (List ℚ)) : List Poly :=
  let U := affPoly aff 2
  let A := affPoly aff 3
  let B := affPoly aff 4
  let C := affPoly aff 5
  [add U (const (-coneTie)), add (const (coneTie + tpocketDU)) (scale (-1) U), B, C,
    add (const rho0) (scale (-1) B), add (const rho0) (scale (-1) C),
    add (scale (tpocketW / 2) (add B C)) A,
    add (scale (tpocketW / 2) (add B C)) (scale (-1) A)].map normalize

/-- The skew pocket roots (the scale `a ~ ε` in the skew chart): `0` askew,
`1` bskew (`+`), `2` bskew (`-`); the skew root's `u, b, η'` ranges. -/
def spocketKind : Fin 3 → ChartKind
  | 0 => .askew
  | 1 => .bskew false
  | 2 => .bskew true

def spocketRoot (e0 : ℚ) (m : Fin 3) : Frame :=
  ⟨true, spocketKind m,
    [e0 / 2, 1, 1 / 2, ((pocketVar3 m).1 + (pocketVar3 m).2) / 2, (skewB0 + skewB1) / 2, 0],
    [e0 / 2, 0, 1 / 2, ((pocketVar3 m).2 - (pocketVar3 m).1) / 2, (skewB1 - skewB0) / 2,
      skewDelta], []⟩

/-- The plain pocket roots (segment B, `λ = 1`, the scale `a ~ ε` for
`b ∈ [0, 1]`, `c ∈ [1/32, 1]`, away from `X̂ = 0`): `0` aplain, `1` bplain
(`+`), `2` bplain (`-`). -/
def ppocketKind : Fin 3 → ChartKind
  | 0 => .aplain
  | 1 => .bplain false
  | 2 => .bplain true

/-- The plain pockets: segment and `u` range (segment A above the cone at the
tie, segment B throughout). -/
def ppocketSpec : Fin 3 → Bool × ℚ × ℚ × ℚ
  | 0 => (true, 0, 1, 33 / 64)
  | 1 => (false, coneTie + coneDU, 1, 33 / 64)
  | 2 => (true, 0, 1, -33 / 64)

def ppocketRoot (e0 : ℚ) (k : Fin 3) (m : Fin 3) : Frame :=
  ⟨(ppocketSpec k).1, ppocketKind m,
    [e0 / 2, 1, ((ppocketSpec k).2.1 + (ppocketSpec k).2.2.1) / 2,
      ((pocketVar3 m).1 + (pocketVar3 m).2) / 2, 1 / 2, (ppocketSpec k).2.2.2],
    [e0 / 2, 0, ((ppocketSpec k).2.2.1 - (ppocketSpec k).2.1) / 2,
      ((pocketVar3 m).2 - (pocketVar3 m).1) / 2, 1 / 2, 31 / 64], []⟩

/-! ## Points given by lists -/

/-- Chart coordinates given by a list (zero beyond it). -/
noncomputable def ofList (l : List ℝ) : ℕ → ℝ := fun i => l.getD i 0

theorem mem_ofList {f : Frame} {l : List ℝ} (hc : f.center.length = l.length)
    (hr : f.radius.length = l.length)
    (h : ∀ i < l.length, |l.getD i 0 - f.center.getD i 0| ≤ f.radius.getD i 0) :
    f.box.Mem (ofList l) := by
  intro i
  simp only [Frame.box, Frame.toRow, Row.box, ofList]
  by_cases hi : i < l.length
  · exact h i hi
  · have h1 : l.getD i 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]
    have h2 : f.center.getD i 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hc ▸ not_lt.mp hi)]
    have h3 : f.radius.getD i 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hr ▸ not_lt.mp hi)]
    simp only [List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
    simp

/-- Beyond the frame's lists, a member point vanishes. -/
theorem _root_.Noperts.Stellated.CornerTree.Frame.eq_zero_of_mem {f : Frame} {y : ℕ → ℝ} (h : f.box.Mem y) {i : ℕ}
    (hc : f.center.length ≤ i) (hr : f.radius.length ≤ i) : y i = 0 := by
  have := h i
  simp only [Frame.box, Frame.toRow, Row.box, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none hc, List.getElem?_eq_none hr, Option.getD_none,
    Rat.cast_zero, sub_zero] at this
  exact abs_nonpos_iff.mp this

/-! ## Self-shadow: `X = 0` -/

theorem hull_isBounded : Bornology.IsBounded exactPolyhedron.hull := by
  rw [exactPolyhedron_hull]
  exact ((Finset.finite_toSet _).isCompact_convexHull (𝕜 := ℝ)).isBounded

theorem hull_nonempty : exactPolyhedron.hull.Nonempty := by
  rw [exactPolyhedron_hull, convexHull_nonempty_iff]
  exact ⟨exactVertex 0, by simp [exactVerts]⟩

theorem not_rupert_of_cayley_zero {p : AtlasPose ℝ} (hx : p.x = 0) (hy : p.y = 0)
    (hz : p.z = 0) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  apply not_rupertPose_of_innerRot_eq_outerRot _ hull_isBounded hull_nonempty
  apply Subtype.ext
  rw [AtlasPose.matrixPoseWithOffset_innerRot_val, AtlasPose.matrixPoseWithOffset_outerRot_val,
    hx, hy, hz]
  have hchart : CayleyAtlas.chartMatrix 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CayleyAtlas.chartMatrix]
  have hcayley : cayleyMatrix 0 0 0 = 1 := cayleyMatrix_zero
  rw [hchart, hcayley, Matrix.mul_one, Matrix.mul_one]

/-! ## Face selection -/

/-- A nonzero vector, divided by its max norm, lies on a face of the cube. -/
theorem exists_face3 (a b c : ℝ) (hρ : 0 < max (max |a| |b|) |c|) :
    ∃ face : Fin 6, ∀ k : Fin 3,
      let v := ![a, b, c] k / max (max |a| |b|) |c|
      |v| ≤ 1 ∧ (k.val = face.val / 2 → v = faceSign face.val) := by
  set ρ := max (max |a| |b|) |c| with hρdef
  have ha : |a| ≤ ρ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb : |b| ≤ ρ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc : |c| ≤ ρ := le_max_right _ _
  have hbound : ∀ k : Fin 3, |![a, b, c] k / ρ| ≤ 1 := by
    intro k
    rw [abs_div, abs_of_pos hρ, div_le_one hρ]
    fin_cases k <;> simpa
  have hcases : ρ = |a| ∨ ρ = |b| ∨ ρ = |c| := by
    rcases le_total (max |a| |b|) |c| with h | h
    · right; right; rw [hρdef, max_eq_right h]
    · rw [hρdef, max_eq_left h]
      rcases le_total |a| |b| with h' | h'
      · right; left; exact max_eq_right h'
      · left; exact max_eq_left h'
  have hsgn : ∀ t : ℝ, ρ = |t| → (t / ρ = 1 ∨ t / ρ = -1) := by
    intro t ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [abs_zero] at ht
      linarith
    rcases le_or_gt 0 t with h | h
    · left; rw [ht, abs_of_nonneg h, div_self ht0]
    · right; rw [ht, abs_of_neg h, div_neg, div_self ht0]
  rcases hcases with h | h | h
  · rcases hsgn a h with hs | hs
    · refine ⟨0, fun k => ⟨hbound k, fun hk => ?_⟩⟩
      fin_cases k <;> first | (norm_num at hk; done) | (norm_num [faceSign]; exact hs)
    · refine ⟨1, fun k => ⟨hbound k, fun hk => ?_⟩⟩
      fin_cases k <;> first | (norm_num at hk; done) | (norm_num [faceSign]; exact hs)
  · rcases hsgn b h with hs | hs
    · refine ⟨2, fun k => ⟨hbound k, fun hk => ?_⟩⟩
      fin_cases k <;> first | (norm_num at hk; done) | (norm_num [faceSign]; exact hs)
    · refine ⟨3, fun k => ⟨hbound k, fun hk => ?_⟩⟩
      fin_cases k <;> first | (norm_num at hk; done) | (norm_num [faceSign]; exact hs)
  · rcases hsgn c h with hs | hs
    · refine ⟨4, fun k => ⟨hbound k, fun hk => ?_⟩⟩
      fin_cases k <;> first | (norm_num at hk; done) | (norm_num [faceSign]; exact hs)
    · refine ⟨5, fun k => ⟨hbound k, fun hk => ?_⟩⟩
      fin_cases k <;> first | (norm_num at hk; done) | (norm_num [faceSign]; exact hs)

theorem exists_face2 (a c : ℝ) (hρ : 0 < max |a| |c|) :
    ∃ face : Fin 4, abs (a / max |a| |c|) ≤ 1 ∧ abs (c / max |a| |c|) ≤ 1 ∧
      (face.val / 2 = 0 → a / max |a| |c| = faceSign face.val) ∧
      (face.val / 2 = 1 → c / max |a| |c| = faceSign face.val) := by
  obtain ⟨face, h⟩ := exists_face3 a 0 c (by simpa using hρ)
  have hm : max (max |a| |(0 : ℝ)|) |c| = max |a| |c| := by simp
  have h0 := h 0
  have h2 := h 2
  simp only [hm, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h0 h2
  have h1 := (h 1).2
  simp only [hm, Matrix.cons_val_one] at h1
  fin_cases face
  · exact ⟨0, h0.1, h2.1, fun _ => h0.2 rfl, fun h => by simp at h⟩
  · exact ⟨1, h0.1, h2.1, fun _ => h0.2 rfl, fun h => by simp at h⟩
  · exact absurd (h1 rfl) (by norm_num [faceSign])
  · exact absurd (h1 rfl) (by norm_num [faceSign])
  · exact ⟨2, h0.1, h2.1, fun h => by simp at h, fun _ => h2.2 rfl⟩
  · exact ⟨3, h0.1, h2.1, fun h => by simp at h, fun _ => h2.2 rfl⟩

/-! ## Hand-off conditions -/

def normPoly (seg : Bool) : Poly :=
  add (mul (sPoly seg) (sPoly seg)) (scale (1 / 4) (mul (tPoly seg) (tPoly seg)))

/-- `(b, c) · D₁` and `(b, c) · D₂` in plain-chart variables. -/
def tauNum (seg : Bool) : Poly :=
  add (mul (var 4) (scale (-1 / 2) (tPoly seg))) (mul (var 5) (scale (-1) (sPoly seg)))

def etaNum (seg : Bool) : Poly :=
  add (mul (var 4) (sPoly seg)) (mul (var 5) (scale (-1 / 2) (tPoly seg)))

def wedgeIneqs (seg : Bool) : List Poly :=
  [add (tauNum seg) (scale (-tau0) (normPoly seg)),
   add (scale tau1 (normPoly seg)) (scale (-1) (tauNum seg)),
   add (scale eta0 (normPoly seg)) (scale (-1) (etaNum seg)),
   add (scale eta0 (normPoly seg)) (etaNum seg)]

/-- Shared conditions: `λ = 1`, `ε ∈ [0, e0]`, `u ∈ [0, 1]`, six variables. -/
def baseOk (e0 : ℚ) (f : Frame) : Prop :=
  f.center.length = 6 ∧ f.radius.length = 6 ∧ f.lo 1 = 1 ∧ f.hi 1 = 1 ∧
    0 ≤ f.lo 0 ∧ f.hi 0 ≤ e0 ∧ 0 ≤ f.lo 2 ∧ f.hi 2 ≤ 1 ∧ f.aff = []

theorem baseOk.aff {e0 : ℚ} {f : Frame} (h : baseOk e0 f) : f.aff = [] := h.2.2.2.2.2.2.2.2

instance (e0 : ℚ) (f : Frame) : Decidable (baseOk e0 f) := by
  unfold baseOk; infer_instance

def HandoffValid (e0 : ℚ) : Handoff → Frame → Prop
  | .tube, f => f.kind = .plain ∧ baseOk e0 f ∧
      ∀ v ∈ [3, 4, 5], -rho0 ≤ f.lo v ∧ f.hi v ≤ rho0
  | .wedge, f => f.kind = .plain ∧ baseOk e0 f ∧
      -alpha0 ≤ f.lo 3 ∧ f.hi 3 ≤ alpha0 ∧ (∀ x ∈ f.radius, 0 ≤ x) ∧
      ∀ q ∈ wedgeIneqs f.seg, NonnegOk f.toRow.nonnegVars f.box q
  | .skew, f => f.kind = .plain ∧ f.seg = true ∧ baseOk e0 f ∧
      -1 ≤ f.lo 3 ∧ f.hi 3 ≤ 1 ∧ skewB0 ≤ f.lo 4 ∧ f.hi 4 ≤ skewB1 ∧
      -skewDelta ≤ f.lo 5 + skewK * f.lo 4 ∧ f.hi 5 + skewK * f.hi 4 ≤ skewDelta
  | .wtube, f => f.kind = .wedge ∧ baseOk e0 f ∧
      tau0 ≤ f.lo 4 ∧ f.hi 4 ≤ tau1 ∧
      ∀ v ∈ [3, 5], -sigma0 ≤ f.lo v ∧ f.hi v ≤ sigma0
  | .pocket, f => f.kind = .tube ∧ f.aff = [] ∧ f.center.length = 7 ∧
      f.radius.length = 7 ∧ f.lo 1 = 1 ∧ f.hi 1 = 1 ∧ 0 ≤ f.lo 0 ∧ f.hi 0 ≤ e0 ∧
      -pocketW ≤ f.lo 3 ∧ f.hi 3 ≤ pocketW ∧ pocketB0 ≤ f.lo 4 ∧ f.hi 4 ≤ pocketB1 ∧
      0 ≤ f.lo 6 ∧ f.hi 6 ≤ rho0 ∧
      ∃ k : Fin 3, (pocketSpec k).1 = f.seg ∧ (pocketSpec k).2.2.1 ≤ f.lo 2 ∧
        f.hi 2 ≤ (pocketSpec k).2.2.2 ∧
        f.lo 5 = faceSign (pocketSpec k).2.1.val ∧ f.hi 5 = faceSign (pocketSpec k).2.1.val
  | .ppocket, f => f.kind = .plain ∧ f.aff = [] ∧ f.center.length = 6 ∧
      f.radius.length = 6 ∧ f.lo 1 = 1 ∧ f.hi 1 = 1 ∧ 0 ≤ f.lo 0 ∧ f.hi 0 ≤ e0 ∧
      -pocketW ≤ f.lo 3 ∧ f.hi 3 ≤ pocketW ∧
      0 ≤ f.lo 4 ∧ f.hi 4 ≤ 1 ∧
      ∃ k : Fin 3, (ppocketSpec k).1 = f.seg ∧ (ppocketSpec k).2.1 ≤ f.lo 2 ∧
        f.hi 2 ≤ (ppocketSpec k).2.2.1 ∧ (ppocketSpec k).2.2.2 - 31 / 64 ≤ f.lo 5 ∧
        f.hi 5 ≤ (ppocketSpec k).2.2.2 + 31 / 64
  | .spocket, f => f.kind = .skew ∧ f.seg = true ∧ f.aff = [] ∧ f.center.length = 6 ∧
      f.radius.length = 6 ∧ f.lo 1 = 1 ∧ f.hi 1 = 1 ∧ 0 ≤ f.lo 0 ∧ f.hi 0 ≤ e0 ∧
      0 ≤ f.lo 2 ∧ f.hi 2 ≤ 1 ∧ -pocketW ≤ f.lo 3 ∧ f.hi 3 ≤ pocketW ∧
      skewB0 ≤ f.lo 4 ∧ f.hi 4 ≤ skewB1 ∧ -skewDelta ≤ f.lo 5 ∧ f.hi 5 ≤ skewDelta
  | .cpocket, f => f.kind = .plain ∧ f.seg = false ∧ f.center.length = 6 ∧
      f.radius.length = 6 ∧ f.lo 1 = 1 ∧ f.hi 1 = 1 ∧ 0 ≤ f.lo 0 ∧ f.hi 0 ≤ e0 ∧
      (∀ x ∈ f.radius, 0 ≤ x) ∧
      ∀ q ∈ cpocketIneqs f.aff, NonnegOk f.toRow.nonnegVars f.box q
  | .cone, f => f.seg = false ∧ f.aff = [] ∧ f.lo 1 = 1 ∧ f.hi 1 = 1 ∧
      0 ≤ f.lo 0 ∧ f.hi 0 ≤ e0 ∧ coneTie - coneDU ≤ f.lo 2 ∧ f.hi 2 ≤ coneTie + coneDU ∧
      ((f.kind = .plain ∧ ∀ v ∈ [3, 4, 5], -coneR ≤ f.lo v ∧ f.hi v ≤ coneR) ∨
       (f.kind = .tube ∧ (∀ v ∈ [3, 4, 5], -1 ≤ f.lo v ∧ f.hi v ≤ 1) ∧
         0 ≤ f.lo 6 ∧ f.hi 6 ≤ coneR))

instance (e0 : ℚ) (h : Handoff) (f : Frame) : Decidable (HandoffValid e0 h f) := by
  cases h <;> unfold HandoffValid <;> infer_instance

def handoffs (e0 : ℚ) : Handoffs := ⟨HandoffValid e0⟩

structure Base (y : ℕ → ℝ) (e0 : ℚ) : Prop where
  lam : y 1 = 1
  eps0 : 0 ≤ y 0
  eps1 : y 0 ≤ e0
  u0 : 0 ≤ y 2
  u1 : y 2 ≤ 1

theorem Base.of_ok {e0 : ℚ} {f : Frame} (h : baseOk e0 f) {y : ℕ → ℝ}
    (hmem : f.box.Mem y) : Base y e0 := by
  obtain ⟨-, -, hl1, hh1, hl0, hh0, hl2, hh2, -⟩ := h
  have b0 := f.mem_bounds hmem 0
  have b1 := f.mem_bounds hmem 1
  have b2 := f.mem_bounds hmem 2
  rw [hl1, hh1] at b1
  push_cast at b1
  have l0 : (0 : ℝ) ≤ f.lo 0 := by exact_mod_cast hl0
  have h0 : (f.hi 0 : ℝ) ≤ e0 := by exact_mod_cast hh0
  have l2 : (0 : ℝ) ≤ f.lo 2 := by exact_mod_cast hl2
  have h2 : (f.hi 2 : ℝ) ≤ 1 := by exact_mod_cast hh2
  exact ⟨le_antisymm b1.2 b1.1, by linarith [b0.1], by linarith [b0.2],
    by linarith [b2.1], by linarith [b2.2]⟩

theorem _root_.Noperts.Stellated.CornerTree.Frame.abs_le_of {f : Frame} {y : ℕ → ℝ} (hmem : f.box.Mem y) {v : ℕ} {r : ℚ}
    (hlo : -r ≤ f.lo v) (hhi : f.hi v ≤ r) : |y v| ≤ r := by
  have b := f.mem_bounds hmem v
  have l : ((-r : ℚ) : ℝ) ≤ f.lo v := by exact_mod_cast hlo
  have h : (f.hi v : ℝ) ≤ r := by exact_mod_cast hhi
  push_cast at l
  rw [abs_le]
  constructor <;> linarith [b.1, b.2]

theorem getD_set_eq (l : List ℚ) (j i : ℕ) (a : ℚ) (hj : j < l.length) :
    (l.set j a).getD i 0 = if i = j then a else l.getD i 0 := by
  split_ifs with h
  · subst h; exact CornerTree.getD_set_self hj a
  · exact CornerTree.getD_set_ne h a

theorem wVal_congr (seg : Bool) {y y' : ℕ → ℝ} (h0 : y' 0 = y 0) (h1 : y' 1 = y 1)
    (h2 : y' 2 = y 2) (c : Fin 3) : wVal seg y' c = wVal seg y c := by
  simp only [wVal, sVal, tVal, h0, h1, h2]

theorem _root_.Noperts.Stellated.CornerCertificate.Coords.plain_xyz {seg : Bool} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (hc : Coords seg .plain p y) :
    p.x = y 0 * (y 3 + y 4) ∧ p.y = y 0 * (y 3 - y 4) ∧ p.z = y 0 * y 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.cx]; simp [xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]
  · rw [hc.cy]; simp [xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3, sub_eq_add_neg]
  · rw [hc.cz]; simp [xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]

theorem tube_sound (e0 : ℚ) (f : Frame)
    (hT : ∀ face, Covered (tubeRoot e0 f.seg face)) (hv : HandoffValid e0 .tube f) :
    Covered f := by
  obtain ⟨hkind, hbase, hbox⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [hbase.aff, affY_nil] at hc
  have B := Base.of_ok hbase hmem
  rw [hkind] at hc
  have h3 := f.abs_le_of hmem (hbox 3 (by simp)).1 (hbox 3 (by simp)).2
  have h4 := f.abs_le_of hmem (hbox 4 (by simp)).1 (hbox 4 (by simp)).2
  have h5 := f.abs_le_of hmem (hbox 5 (by simp)).1 (hbox 5 (by simp)).2
  obtain ⟨hx, hy, hz⟩ := hc.plain_xyz
  set ρ := max (max |y 3| |y 4|) |y 5| with hρdef
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg _) (le_max_right _ _)
  have hρ1 : ρ ≤ rho0 := max_le (max_le h3 h4) h5
  rcases hρ0.eq_or_lt with h0 | hpos
  · have z3 : y 3 = 0 := abs_nonpos_iff.mp (h0 ▸ le_trans (le_max_left _ _) (le_max_left _ _))
    have z4 : y 4 = 0 := abs_nonpos_iff.mp (h0 ▸ le_trans (le_max_right _ _) (le_max_left _ _))
    have z5 : y 5 = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_right _ _)
    exact not_rupert_of_cayley_zero (by rw [hx, z3, z4]; ring) (by rw [hy, z3, z4]; ring)
      (by rw [hz, z5]; ring) offset
  · obtain ⟨face, hface⟩ := exists_face3 (y 3) (y 4) (y 5) hpos
    have hρne : ρ ≠ 0 := ne_of_gt hpos
    set y' := ofList [y 0, y 1, y 2, y 3 / ρ, y 4 / ρ, y 5 / ρ, ρ] with hy'
    have e0' : y' 0 = y 0 := rfl
    have e1' : y' 1 = y 1 := rfl
    have e2' : y' 2 = y 2 := rfl
    have hc' : Coords f.seg .tube p y' := by
      refine ⟨fun c => (hc.view c).trans (wVal_congr f.seg e0' e1' e2' c).symm, ?_, ?_, ?_⟩
      · rw [hx]; simp [y', ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]
        field_simp
      · rw [hy]; simp [y', ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]
        field_simp; ring
      · rw [hz]; simp [y', ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]
        field_simp
    have hk : ∀ k : Fin 3, |![y 3, y 4, y 5] k / ρ| ≤ 1 := fun k => (hface k).1
    have hk3 := hk 0
    have hk4 := hk 1
    have hk5 := hk 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hk3 hk4 hk5
    have he : ∀ k : Fin 3, k.val = face.val / 2 →
        ![y 3, y 4, y 5] k / ρ = faceSign face.val := fun k => (hface k).2
    have hf : face.val / 2 < 3 := by omega
    have hmem' : (tubeRoot e0 f.seg face).box.Mem y' := by
      apply mem_ofList (by simp [tubeRoot]) (by simp [tubeRoot])
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      simp only [tubeRoot]
      rw [getD_set_eq _ _ _ _ (by simp; omega), getD_set_eq _ _ _ _ (by simp; omega)]
      have hrho : (rho0 : ℝ) = 1 / 16 := by norm_num [rho0]
      have hρ1' : ρ ≤ 1 / 16 := hrho ▸ hρ1
      interval_cases i
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
        constructor <;> linarith [B.eps0, B.eps1]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [B.lam]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
        constructor <;> linarith [B.u0, B.u1]
      · split_ifs with h
        · have := he 0 (by simp; omega); simp at this; simp [this]
        · simp; exact hk3
      · split_ifs with h
        · have := he 1 (by simp; omega); simp at this; simp [this]
        · simp; exact hk4
      · split_ifs with h
        · have := he 2 (by simp; omega); simp at this; simp [this]
        · simp; exact hk5
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le, rho0]
        constructor <;> linarith
    exact (hT face).apply_nil rfl p offset y' hc' hmem' hε (fun _ => hpos)
      (fun _ => by simp [y', ofList, B.lam]) hflip hscale

theorem wedge_inv (s t b c : ℝ) (hN : s ^ 2 + t ^ 2 / 4 ≠ 0) :
    (b * (-1 / 2 * t) + c * (-s)) / (s ^ 2 + t ^ 2 / 4) * (-1 / 2 * t) +
        (b * s + c * (-1 / 2 * t)) / (s ^ 2 + t ^ 2 / 4) * s = b ∧
      (b * (-1 / 2 * t) + c * (-s)) / (s ^ 2 + t ^ 2 / 4) * (-s) +
        (b * s + c * (-1 / 2 * t)) / (s ^ 2 + t ^ 2 / 4) * (-1 / 2 * t) = c := by
  set N := s ^ 2 + t ^ 2 / 4
  constructor
  · calc _ = ((b * (-1 / 2 * t) + c * (-s)) * (-1 / 2 * t) +
            (b * s + c * (-1 / 2 * t)) * s) / N := by ring
      _ = b * N / N := by congr 1; simp only [N]; ring
      _ = b := by rw [mul_div_assoc, div_self hN, mul_one]
  · calc _ = ((b * (-1 / 2 * t) + c * (-s)) * (-s) +
            (b * s + c * (-1 / 2 * t)) * (-1 / 2 * t)) / N := by ring
      _ = c * N / N := by congr 1; simp only [N]; ring
      _ = c := by rw [mul_div_assoc, div_self hN, mul_one]

theorem norm_pos_of_lam {seg : Bool} {y : ℕ → ℝ} (h : y 1 = 1) :
    0 < sVal seg y ^ 2 + tVal seg y ^ 2 / 4 := by
  cases seg <;> simp [sVal, tVal, h] <;> positivity

theorem eval_xPolyK_wedge (seg : Bool) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (xPolyK seg .wedge c) = y 0 * ((M1 c : ℝ) * y 3 +
      (M2 c : ℝ) * (y 4 * (-1 / 2 * tVal seg y) + y 5 * sVal seg y) +
      (M3 c : ℝ) * (y 4 * (-sVal seg y) + y 5 * (-1 / 2 * tVal seg y))) := by
  simp only [xPolyK, wedgeB, wedgeC, eval_add, eval_mul, eval_scale, eval_var,
    eval_sPoly, eval_tPoly]
  push_cast
  ring

theorem eval_xPolyK_wtube (seg : Bool) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (xPolyK seg .wtube c) = y 0 * ((M1 c : ℝ) * (y 6 * y 3) +
      (M2 c : ℝ) * (y 4 * (-1 / 2 * tVal seg y) + y 6 * y 5 * sVal seg y) +
      (M3 c : ℝ) * (y 4 * (-sVal seg y) + y 6 * y 5 * (-1 / 2 * tVal seg y))) := by
  simp only [xPolyK, wedgeB, wedgeC, eval_add, eval_mul, eval_scale, eval_var,
    eval_sPoly, eval_tPoly]
  push_cast
  ring

theorem eval_xPolyK_plain (seg : Bool) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (xPolyK seg .plain c) =
      y 0 * ((M1 c : ℝ) * y 3 + (M2 c : ℝ) * y 4 + (M3 c : ℝ) * y 5) := by
  simp [xPolyK, eval_xPoly, xVal, scaleVal]

theorem sVal_congr (seg : Bool) {y y' : ℕ → ℝ} (h1 : y' 1 = y 1) (h2 : y' 2 = y 2) :
    sVal seg y' = sVal seg y := by simp [sVal, h1, h2]

theorem tVal_congr (seg : Bool) {y y' : ℕ → ℝ} (h1 : y' 1 = y 1) (h2 : y' 2 = y 2) :
    tVal seg y' = tVal seg y := by simp [tVal, h1, h2]

theorem wedge_sound (e0 : ℚ) (f : Frame)
    (hW : Covered (wedgeRoot e0 f.seg)) (hv : HandoffValid e0 .wedge f) :
    Covered f := by
  obtain ⟨hkind, hbase, hlo3, hhi3, hrad, hineq⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [hbase.aff, affY_nil] at hc
  have B := Base.of_ok hbase hmem
  rw [hkind] at hc
  have h3 := f.abs_le_of hmem hlo3 hhi3
  set s := sVal f.seg y
  set t := tVal f.seg y
  set N := s ^ 2 + t ^ 2 / 4 with hN
  have hNpos : 0 < N := norm_pos_of_lam B.lam
  set τ := (y 4 * (-1 / 2 * t) + y 5 * (-s)) / N with hτ
  set η := (y 4 * s + y 5 * (-1 / 2 * t)) / N with hη
  obtain ⟨hb, hcc⟩ := wedge_inv s t (y 4) (y 5) (ne_of_gt hNpos)
  set y' := ofList [y 0, y 1, y 2, y 3, τ, η] with hy'
  have e0' : y' 0 = y 0 := rfl
  have e1' : y' 1 = y 1 := rfl
  have e2' : y' 2 = y 2 := rfl
  have hs' : sVal f.seg y' = s := sVal_congr f.seg e1' e2'
  have ht' : tVal f.seg y' = t := tVal_congr f.seg e1' e2'
  have hx : ∀ c, eval y' (xPolyK f.seg .wedge c) = eval y (xPolyK f.seg .plain c) := by
    intro c
    rw [eval_xPolyK_wedge, eval_xPolyK_plain, hs', ht']
    have e3' : y' 3 = y 3 := rfl
    have e4' : y' 4 = τ := rfl
    have e5' : y' 5 = η := rfl
    rw [e0', e3', e4', e5', hb, hcc]
  have hc' : Coords f.seg .wedge p y' :=
    ⟨fun c => (hc.view c).trans (wVal_congr f.seg e0' e1' e2' c).symm,
      by rw [hc.cx, hx], by rw [hc.cy, hx], by rw [hc.cz, hx]⟩
  -- the hand-off inequalities
  have hvars := fun v hv => f.toRow.nonnegVars_sound hmem v hv
  have hradf := f.toRow.radius_nonneg hrad
  have ev : ∀ q ∈ wedgeIneqs f.seg, 0 ≤ eval y q := fun q hq =>
    NonnegOk.sound (hineq q hq) hmem hradf hvars
  have htn : eval y (tauNum f.seg) = y 4 * (-1 / 2 * t) + y 5 * (-s) := by
    simp [tauNum, eval_add, eval_mul, eval_scale, eval_var, eval_sPoly, eval_tPoly, s, t]
  have hen : eval y (etaNum f.seg) = y 4 * s + y 5 * (-1 / 2 * t) := by
    simp [etaNum, eval_add, eval_mul, eval_scale, eval_var, eval_sPoly, eval_tPoly, s, t]
  have hnp : eval y (normPoly f.seg) = N := by
    simp [normPoly, eval_add, eval_mul, eval_scale, eval_sPoly, eval_tPoly, N, s, t]
    ring
  have i0 := ev (add (tauNum f.seg) (scale (-tau0) (normPoly f.seg))) (by simp [wedgeIneqs])
  have i1 := ev (add (scale tau1 (normPoly f.seg)) (scale (-1) (tauNum f.seg)))
    (by simp [wedgeIneqs])
  have i2 := ev (add (scale eta0 (normPoly f.seg)) (scale (-1) (etaNum f.seg)))
    (by simp [wedgeIneqs])
  have i3 := ev (add (scale eta0 (normPoly f.seg)) (etaNum f.seg)) (by simp [wedgeIneqs])
  simp only [eval_add, eval_scale, htn, hen, hnp] at i0 i1 i2 i3
  have hτ0 : (tau0 : ℝ) ≤ τ := by rw [hτ, le_div_iff₀ hNpos]; push_cast at i0 ⊢; linarith
  have hτ1 : τ ≤ tau1 := by rw [hτ, div_le_iff₀ hNpos]; push_cast at i1 ⊢; linarith
  have hη0 : |η| ≤ eta0 := by
    rw [hη, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos, abs_le]
    push_cast at i2 i3 ⊢
    constructor <;> linarith
  have hmem' : (wedgeRoot e0 f.seg).box.Mem y' := by
    apply mem_ofList (by simp [wedgeRoot]) (by simp [wedgeRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp [wedgeRoot, abs_le]; constructor <;> linarith [B.eps0, B.eps1]
    · simp [wedgeRoot, B.lam]
    · simp [wedgeRoot, abs_le]; constructor <;> linarith [B.u0, B.u1]
    · simpa [y', ofList, wedgeRoot] using h3
    · simp only [wedgeRoot]
      simp [abs_le, tau0, tau1] at hτ0 hτ1 ⊢
      constructor <;> linarith
    · simpa [y', ofList, wedgeRoot] using hη0
  exact (hW).apply_nil rfl p offset y' hc' hmem' hε (fun h => by simp [wedgeRoot] at h)
    (fun _ => by simp [y', ofList, B.lam]) hflip hscale

theorem wtube_sound (e0 : ℚ) (f : Frame)
    (hWT : ∀ face, Covered (wtubeRoot e0 f.seg face)) (hv : HandoffValid e0 .wtube f) :
    Covered f := by
  obtain ⟨hkind, hbase, hlo4, hhi4, hbox⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [hbase.aff, affY_nil] at hc
  have B := Base.of_ok hbase hmem
  rw [hkind] at hc
  have h3 := f.abs_le_of hmem (hbox 3 (by simp)).1 (hbox 3 (by simp)).2
  have h5 := f.abs_le_of hmem (hbox 5 (by simp)).1 (hbox 5 (by simp)).2
  have b4 := f.mem_bounds hmem 4
  have l4 : (tau0 : ℝ) ≤ f.lo 4 := by exact_mod_cast hlo4
  have u4 : (f.hi 4 : ℝ) ≤ tau1 := by exact_mod_cast hhi4
  have hsig : (sigma0 : ℝ) = 1 / 16 := by norm_num [sigma0]
  have ht0 : (tau0 : ℝ) = 1 / 8 := by norm_num [tau0]
  have ht1 : (tau1 : ℝ) = 3 / 4 := by norm_num [tau1]
  set σ := max |y 3| |y 5| with hσdef
  have hσ0 : 0 ≤ σ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hσ1 : σ ≤ 1 / 16 := hsig ▸ max_le h3 h5
  -- the chart point with given `ᾱ, η̄, σ`
  have key : ∀ (ab eb sg : ℝ), sg * ab = y 3 → sg * eb = y 5 →
      Coords f.seg .wtube p (ofList [y 0, y 1, y 2, ab, y 4, eb, sg]) := by
    intro ab eb sg ha he
    have e0' : ofList [y 0, y 1, y 2, ab, y 4, eb, sg] 0 = y 0 := rfl
    have e1' : ofList [y 0, y 1, y 2, ab, y 4, eb, sg] 1 = y 1 := rfl
    have e2' : ofList [y 0, y 1, y 2, ab, y 4, eb, sg] 2 = y 2 := rfl
    have hx : ∀ c, eval (ofList [y 0, y 1, y 2, ab, y 4, eb, sg]) (xPolyK f.seg .wtube c) =
        eval y (xPolyK f.seg .wedge c) := by
      intro c
      rw [eval_xPolyK_wtube, eval_xPolyK_wedge, sVal_congr f.seg e1' e2',
        tVal_congr f.seg e1' e2']
      have e3' : ofList [y 0, y 1, y 2, ab, y 4, eb, sg] 3 = ab := rfl
      have e4' : ofList [y 0, y 1, y 2, ab, y 4, eb, sg] 4 = y 4 := rfl
      have e5' : ofList [y 0, y 1, y 2, ab, y 4, eb, sg] 5 = eb := rfl
      have e6' : ofList [y 0, y 1, y 2, ab, y 4, eb, sg] 6 = sg := rfl
      rw [e0', e3', e4', e5', e6', ha, he]
    exact ⟨fun c => (hc.view c).trans (wVal_congr f.seg e0' e1' e2' c).symm,
      by rw [hc.cx, hx], by rw [hc.cy, hx], by rw [hc.cz, hx]⟩
  -- membership in a face, given the face coordinates
  have memFace : ∀ (face : Fin 4) (ab eb sg : ℝ), |ab| ≤ 1 → |eb| ≤ 1 → 0 ≤ sg →
      sg ≤ 1 / 16 → (face.val / 2 = 0 → ab = faceSign face.val) →
      (face.val / 2 = 1 → eb = faceSign face.val) →
      (wtubeRoot e0 f.seg face).box.Mem (ofList [y 0, y 1, y 2, ab, y 4, eb, sg]) := by
    intro face ab eb sg hab heb hs0 hs1 hfa hfe
    apply mem_ofList (by simp [wtubeRoot]) (by simp [wtubeRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    simp only [wtubeRoot]
    have hf : face.val / 2 < 2 := by omega
    rw [getD_set_eq _ _ _ _ (by simp; omega), getD_set_eq _ _ _ _ (by simp; omega)]
    interval_cases i
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
      constructor <;> linarith [B.eps0, B.eps1]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [B.lam]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
      constructor <;> linarith [B.u0, B.u1]
    · split_ifs with h
      · have : face.val / 2 = 0 := by omega
        simp [hfa this]
      · simpa [ofList] using hab
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
      rw [ht0, ht1]
      constructor <;> linarith [b4.1, b4.2]
    · split_ifs with h
      · have : face.val / 2 = 1 := by omega
        simp [hfe this]
      · simpa [ofList] using heb
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
      rw [hsig]
      constructor <;> linarith
  rcases hσ0.eq_or_lt with h0 | hpos
  · have z3 : y 3 = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_left _ _)
    have z5 : y 5 = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_right _ _)
    exact (hWT 0).apply_nil rfl p offset _ (key 1 0 0 (by simp [z3]) (by simp [z5]))
      (memFace 0 1 0 0 (by simp) (by simp) le_rfl (by norm_num)
        (fun _ => by simp [faceSign]) (fun h => by simp at h)) hε
      (fun h => by simp [wtubeRoot] at h) (fun _ => by simp [ofList, B.lam]) hflip hscale
  · obtain ⟨face, ha, he, hfa, hfe⟩ := exists_face2 (y 3) (y 5) hpos
    have hne : σ ≠ 0 := ne_of_gt hpos
    exact (hWT face).apply_nil rfl p offset _ (key (y 3 / σ) (y 5 / σ) σ (by field_simp) (by field_simp))
      (memFace face _ _ σ ha he hσ0 hσ1 hfa hfe) hε
      (fun h => by simp [wtubeRoot] at h) (fun _ => by simp [ofList, B.lam]) hflip hscale

theorem skew_sound (e0 : ℚ) (f : Frame) (hS : Covered (skewRoot e0))
    (hv : HandoffValid e0 .skew f) : Covered f := by
  obtain ⟨hkind, hseg, hbase, hlo3, hhi3, hlo4, hhi4, hlo5, hhi5⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [hbase.aff, affY_nil] at hc
  have B := Base.of_ok hbase hmem
  rw [hkind, hseg] at hc
  have b3 := f.mem_bounds hmem 3
  have b4 := f.mem_bounds hmem 4
  have b5 := f.mem_bounds hmem 5
  have l3 : ((-1 : ℚ) : ℝ) ≤ f.lo 3 := by exact_mod_cast hlo3
  have u3 : (f.hi 3 : ℝ) ≤ 1 := by exact_mod_cast hhi3
  have l4 : (skewB0 : ℝ) ≤ f.lo 4 := by exact_mod_cast hlo4
  have u4 : (f.hi 4 : ℝ) ≤ skewB1 := by exact_mod_cast hhi4
  have l5 : ((-skewDelta : ℚ) : ℝ) ≤ ((f.lo 5 + skewK * f.lo 4 : ℚ) : ℝ) := by
    exact_mod_cast hlo5
  have u5 : ((f.hi 5 + skewK * f.hi 4 : ℚ) : ℝ) ≤ skewDelta := by exact_mod_cast hhi5
  push_cast at l3 l5 u5
  have hk : (0 : ℝ) ≤ skewK := by norm_num [skewK]
  set y' := ofList [y 0, y 1, y 2, y 3, y 4, y 5 + skewK * y 4] with hy'
  have e0' : y' 0 = y 0 := rfl
  have e1' : y' 1 = y 1 := rfl
  have e2' : y' 2 = y 2 := rfl
  have hx : ∀ c, eval y' (xPolyK true .skew c) = eval y (xPolyK true .plain c) := by
    intro c
    rw [eval_xPolyK_plain]
    simp only [xPolyK, eval_add, eval_mul, eval_scale, eval_var]
    simp only [y', ofList, List.getD_cons_zero, List.getD_cons_succ]
    push_cast
    ring
  have hc' : Coords true .skew p y' :=
    ⟨fun c => (hc.view c).trans (wVal_congr true e0' e1' e2' c).symm,
      by rw [hc.cx, hx], by rw [hc.cy, hx], by rw [hc.cz, hx]⟩
  have hB1 : (skewB1 : ℝ) = 5 / 12 := by norm_num [skewB1]
  have hmem' : (skewRoot e0).box.Mem y' := by
    apply mem_ofList (by simp [skewRoot]) (by simp [skewRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp [skewRoot, abs_le]; constructor <;> linarith [B.eps0, B.eps1]
    · simp [skewRoot, B.lam]
    · simp [skewRoot, abs_le]; constructor <;> linarith [B.u0, B.u1]
    · simp [skewRoot, abs_le]; constructor <;> linarith [b3.1, b3.2]
    · simp only [skewRoot, List.getD_cons_zero, List.getD_cons_succ]
      push_cast
      rw [abs_le]; constructor <;> linarith [b4.1, b4.2]
    · simp only [skewRoot, List.getD_cons_zero, List.getD_cons_succ]
      push_cast
      have := mul_le_mul_of_nonneg_left b4.1 hk
      have := mul_le_mul_of_nonneg_left b4.2 hk
      rw [abs_le]; constructor <;> linarith [b5.1, b5.2]
  exact hS.apply_nil rfl p offset y' hc' hmem' hε (fun h => by simp [skewRoot] at h)
    (fun _ => by simp [y', ofList, B.lam]) hflip hscale

/-- Plain chart coordinates from the Cayley vector. -/
theorem _root_.Noperts.Stellated.CornerCertificate.Coords.plain_of_xyz {seg : Bool}
    {kind : ChartKind} {p : AtlasPose ℝ} {y z : ℕ → ℝ}
    (hc : Coords seg kind p y) (h0 : z 0 = y 0) (h1 : z 1 = y 1) (h2 : z 2 = y 2)
    (hx : p.x = z 0 * (z 3 + z 4)) (hy : p.y = z 0 * (z 3 - z 4)) (hz : p.z = z 0 * z 5) :
    Coords seg .plain p z := by
  refine ⟨fun c => (hc.view c).trans (wVal_congr seg h0 h1 h2 c).symm, ?_, ?_, ?_⟩
  · rw [hx, eval_xPolyK_plain]; simp [M1, M2, M3]
  · rw [hy, eval_xPolyK_plain]; simp [M1, M2, M3, sub_eq_add_neg]
  · rw [hz, eval_xPolyK_plain]; simp [M1, M2, M3]

theorem coneSign_mul_abs (x : ℝ) : ((coneSign (decide (x < 0)) : ℚ) : ℝ) * |x| = x := by
  by_cases h : x < 0
  · simp [coneSign, h, abs_of_neg h]
  · simp [coneSign, h, abs_of_nonneg (not_lt.mp h)]

theorem cone_sound (e0 : ℚ) (f : Frame) (hC : ∀ neg, Covered (coneRoot e0 neg))
    (hv : HandoffValid e0 .cone f) : Covered f := by
  obtain ⟨hseg, haff, hl1, hh1, hl0, hh0, hl2, hh2, hk⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [haff, affY_nil, hseg] at hc
  have b1 := f.mem_bounds hmem 1
  rw [hl1, hh1] at b1
  push_cast at b1
  have hy1 : y 1 = 1 := le_antisymm b1.2 b1.1
  have b0 := f.mem_bounds hmem 0
  have b2 := f.mem_bounds hmem 2
  have hh0' : (f.hi 0 : ℝ) ≤ e0 := by exact_mod_cast hh0
  have hl2' : ((coneTie - coneDU : ℚ) : ℝ) ≤ f.lo 2 := by exact_mod_cast hl2
  have hh2' : (f.hi 2 : ℝ) ≤ ((coneTie + coneDU : ℚ) : ℝ) := by exact_mod_cast hh2
  push_cast at hl2' hh2'
  have hR : (coneR : ℝ) = 1 / 16 := by norm_num [coneR]
  have hDU : (coneDU : ℝ) = 1 / 64 := by norm_num [coneDU]
  -- plain coordinates of the pose
  obtain ⟨A, B, C, hcz, hA, hB, hCb⟩ : ∃ A B C : ℝ,
      Coords false .plain p (ofList [y 0, y 1, y 2, A, B, C]) ∧
      |A| ≤ coneR ∧ |B| ≤ coneR ∧ |C| ≤ coneR := by
    rcases hk with ⟨hkind, hbox⟩ | ⟨hkind, hbox, hl6, hh6⟩
    · rw [hkind] at hc
      obtain ⟨hx, hy, hz⟩ := hc.plain_xyz
      exact ⟨y 3, y 4, y 5, hc.plain_of_xyz rfl rfl rfl hx hy hz,
        f.abs_le_of hmem (hbox 3 (by simp)).1 (hbox 3 (by simp)).2,
        f.abs_le_of hmem (hbox 4 (by simp)).1 (hbox 4 (by simp)).2,
        f.abs_le_of hmem (hbox 5 (by simp)).1 (hbox 5 (by simp)).2⟩
    · rw [hkind] at hc
      have h3 := f.abs_le_of hmem (hbox 3 (by simp)).1 (hbox 3 (by simp)).2
      have h4 := f.abs_le_of hmem (hbox 4 (by simp)).1 (hbox 4 (by simp)).2
      have h5 := f.abs_le_of hmem (hbox 5 (by simp)).1 (hbox 5 (by simp)).2
      have b6 := f.mem_bounds hmem 6
      have hl6' : (0 : ℝ) ≤ f.lo 6 := by exact_mod_cast hl6
      have hh6' : (f.hi 6 : ℝ) ≤ coneR := by exact_mod_cast hh6
      have y6a : 0 ≤ y 6 := by linarith [b6.1]
      have y6b : y 6 ≤ coneR := by linarith [b6.2]
      have bound : ∀ v, |v| ≤ ((1 : ℚ) : ℝ) → |y 6 * v| ≤ coneR := by
        intro v hv
        rw [abs_mul, abs_of_nonneg y6a]
        push_cast at hv
        calc y 6 * |v| ≤ y 6 * 1 := mul_le_mul_of_nonneg_left hv y6a
          _ ≤ coneR := by linarith
      refine ⟨y 6 * y 3, y 6 * y 4, y 6 * y 5, hc.plain_of_xyz rfl rfl rfl ?_ ?_ ?_,
        bound _ h3, bound _ h4, bound _ h5⟩
      · rw [hc.cx]; simp [ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]; ring
      · rw [hc.cy]; simp [ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]; ring
      · rw [hc.cz]; simp [ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]; ring
  -- the orthant and the cone coordinates
  set U := y 2 - coneTie with hU
  have hU1 : |U| ≤ coneDU := by
    rw [abs_le]; constructor <;> linarith [b2.1, b2.2]
  set neg : Fin 4 → Bool := ![decide (U < 0), decide (A < 0), decide (B < 0), decide (C < 0)]
  set t := ofList [y 0, 1, |U| / coneDU, |A| / coneR, |B| / coneR, |C| / coneR] with ht
  have hDU0 : (coneDU : ℝ) ≠ 0 := by rw [hDU]; norm_num
  have hR0 : (coneR : ℝ) ≠ 0 := by rw [hR]; norm_num
  have haffY : affY (coneAff neg) t = ofList [y 0, y 1, y 2, A, B, C] := by
    funext k
    rw [affY_eq]
    by_cases hk : 2 ≤ k ∧ k ≤ 5
    · rw [ite_eq_left ⟨hk.1, hk.2, by simp [coneAff]⟩]
      obtain ⟨hk1, hk2⟩ := hk
      interval_cases k
      · simp only [affVal, coneAff, t, ofList, neg]
        simp
        rw [mul_assoc, mul_div_cancel₀ _ hDU0, coneSign_mul_abs]
        simp [hU]
      · simp only [affVal, coneAff, t, ofList, neg]
        simp
        rw [mul_assoc, mul_div_cancel₀ _ hR0, coneSign_mul_abs]
      · simp only [affVal, coneAff, t, ofList, neg]
        simp
        rw [mul_assoc, mul_div_cancel₀ _ hR0, coneSign_mul_abs]
      · simp only [affVal, coneAff, t, ofList, neg]
        simp
        rw [mul_assoc, mul_div_cancel₀ _ hR0, coneSign_mul_abs]
    · rw [ite_eq_right (by tauto)]
      rcases (by omega : k = 0 ∨ k = 1 ∨ 6 ≤ k) with rfl | rfl | h6
      · rfl
      · simp [t, ofList, hy1]
      · simp [t, ofList, List.getD_eq_getElem?_getD, h6]
  have hmem' : (coneRoot e0 neg).box.Mem t := by
    apply mem_ofList (by simp [coneRoot]) (by simp [coneRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have unit : ∀ x D : ℝ, 0 < D → |x| ≤ D → |(|x| / D) - 1 / 2| ≤ 1 / 2 := by
      intro x D hD hx
      have h0 : 0 ≤ |x| / D := div_nonneg (abs_nonneg x) hD.le
      have h1 : |x| / D ≤ 1 := (div_le_one hD).mpr hx
      rw [abs_le]; constructor <;> linarith
    have hDUp : (0 : ℝ) < coneDU := by rw [hDU]; norm_num
    have hRp : (0 : ℝ) < coneR := by rw [hR]; norm_num
    interval_cases i
    · simp [coneRoot, abs_le]; constructor <;> linarith [b0.2]
    · simp [coneRoot]
    · simpa [t, ofList, coneRoot] using unit U coneDU hDUp hU1
    · simpa [t, ofList, coneRoot] using unit A coneR hRp hA
    · simpa [t, ofList, coneRoot] using unit B coneR hRp hB
    · simpa [t, ofList, coneRoot] using unit C coneR hRp hCb
  exact hC neg p offset t
    (by show Coords false .plain p (affY (coneAff neg) t); rw [haffY]; exact hcz)
    hmem' hε (fun h => by simp [coneRoot] at h) (fun _ => by simp [t, ofList]) hflip hscale

theorem eval_tubeX (a : Poly) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (tubeX a c) = y 0 * y 6 * ((M1 c : ℝ) * eval y a + (M2 c : ℝ) * y 4 +
      (M3 c : ℝ) * y 5) := by
  simp [tubeX, eval_mul, eval_add, eval_scale]

theorem eval_xPolyK_tube (seg : Bool) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (xPolyK seg .tube c) =
      y 0 * y 6 * ((M1 c : ℝ) * y 3 + (M2 c : ℝ) * y 4 + (M3 c : ℝ) * y 5) := by
  simp [xPolyK, eval_xPoly, xVal, scaleVal]

/-- A point of a pocket root, given its seven coordinates within bounds. -/
theorem mem_pocketRoot (e0 : ℚ) (k m : Fin 3) (l : List ℝ) (hl : l.length = 7)
    (h : ∀ i < 7, |l.getD i 0 - ((pocketRoot e0 k m).center.getD i 0 : ℚ)| ≤
      (((pocketRoot e0 k m).radius.getD i 0 : ℚ) : ℝ)) :
    (pocketRoot e0 k m).box.Mem (ofList l) :=
  mem_ofList (by simp [pocketRoot, hl]) (by simp [pocketRoot, hl]) (fun i hi => h i (hl ▸ hi))

theorem abs_sub_mid_le {x lo hi : ℝ} (h0 : lo ≤ x) (h1 : x ≤ hi) :
    |x - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
  rw [abs_le]; constructor <;> linarith

/-- The pocket charts reparametrize a tube point with `|y 3| ≤ pocketW`:
`atube` (`y 3 = ε α`, `|α| ≤ atubeA`) or `btube` (`y 3 = ± atubeA ε + w`). -/
theorem pocket_chart (seg : Bool) (y : ℕ → ℝ) (hε : 0 < y 0)
    (e3 : -(pocketW : ℝ) ≤ y 3 ∧ y 3 ≤ pocketW) :
    ∃ (m : Fin 3) (w : ℝ), ((pocketVar3 m).1 : ℝ) ≤ w ∧ w ≤ (pocketVar3 m).2 ∧
      ∀ c, eval (ofList [y 0, y 1, y 2, w, y 4, y 5, y 6]) (xPolyK seg (pocketKind m) c) =
        eval y (xPolyK seg .tube c) := by
  have hA : (0 : ℝ) < atubeA := by norm_num [atubeA]
  rcases le_or_gt |y 3| (atubeA * y 0) with h | h
  · refine ⟨0, y 3 / y 0, ?_⟩
    have hle : |y 3 / y 0| ≤ atubeA := by
      rw [abs_div, abs_of_pos hε, div_le_iff₀ hε]; linarith
    have hb := abs_le.mp hle
    refine ⟨by simpa [pocketVar3] using hb.1, by simpa [pocketVar3] using hb.2, fun c => ?_⟩
    rw [eval_xPolyK_tube]
    simp only [pocketKind, xPolyK, eval_tubeX, eval_mul, eval_var, ofList]
    simp
    field_simp
    try simp
  · have hy3 : y 3 ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      have := mul_pos hA hε
      linarith
    rcases lt_or_gt_of_ne hy3 with hneg | hpos
    · have : y 3 < -(atubeA * y 0) := by
        rw [abs_of_neg hneg] at h; linarith
      refine ⟨2, y 3 + atubeA * y 0, by simp [pocketVar3]; linarith [e3.1, mul_pos hA hε],
        by simp [pocketVar3]; linarith, fun c => ?_⟩
      rw [eval_xPolyK_tube]
      simp only [pocketKind, xPolyK, eval_tubeX, eval_add, eval_scale, eval_var, ofList]
      simp
    · have : atubeA * y 0 < y 3 := by
        rw [abs_of_pos hpos] at h; linarith
      refine ⟨1, y 3 - atubeA * y 0, by simp [pocketVar3]; linarith,
        by simp [pocketVar3]; linarith [e3.2, mul_pos hA hε], fun c => ?_⟩
      rw [eval_xPolyK_tube]
      simp only [pocketKind, xPolyK, eval_tubeX, eval_add, eval_scale, eval_var, ofList]
      simp

/-- The tie-pocket version of `pocket_chart` (`|y 3| ≤ tpocketW`):
`atube` (`y 3 = ε α`, `|α| ≤ atubeA`) or `btube` (`y 3 = ± atubeA ε + w`). -/
theorem pocket_chart_tp (seg : Bool) (y : ℕ → ℝ) (hε : 0 < y 0)
    (e3 : -(tpocketW : ℝ) ≤ y 3 ∧ y 3 ≤ tpocketW) :
    ∃ (m : Fin 3) (w : ℝ), ((tpocketVar3 m).1 : ℝ) ≤ w ∧ w ≤ (tpocketVar3 m).2 ∧
      ∀ c, eval (ofList [y 0, y 1, y 2, w, y 4, y 5, y 6]) (xPolyK seg (pocketKind m) c) =
        eval y (xPolyK seg .tube c) := by
  have hA : (0 : ℝ) < atubeA := by norm_num [atubeA]
  rcases le_or_gt |y 3| (atubeA * y 0) with h | h
  · refine ⟨0, y 3 / y 0, ?_⟩
    have hle : |y 3 / y 0| ≤ atubeA := by
      rw [abs_div, abs_of_pos hε, div_le_iff₀ hε]; linarith
    have hb := abs_le.mp hle
    refine ⟨by simpa [tpocketVar3] using hb.1, by simpa [tpocketVar3] using hb.2, fun c => ?_⟩
    rw [eval_xPolyK_tube]
    simp only [pocketKind, xPolyK, eval_tubeX, eval_mul, eval_var, ofList]
    simp
    field_simp
    try simp
  · have hy3 : y 3 ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      have := mul_pos hA hε
      linarith
    rcases lt_or_gt_of_ne hy3 with hneg | hpos
    · have : y 3 < -(atubeA * y 0) := by
        rw [abs_of_neg hneg] at h; linarith
      refine ⟨2, y 3 + atubeA * y 0, by simp [tpocketVar3]; linarith [e3.1, mul_pos hA hε],
        by simp [tpocketVar3]; linarith, fun c => ?_⟩
      rw [eval_xPolyK_tube]
      simp only [pocketKind, xPolyK, eval_tubeX, eval_add, eval_scale, eval_var, ofList]
      simp
    · have : atubeA * y 0 < y 3 := by
        rw [abs_of_pos hpos] at h; linarith
      refine ⟨1, y 3 - atubeA * y 0, by simp [tpocketVar3]; linarith,
        by simp [tpocketVar3]; linarith [e3.2, mul_pos hA hε], fun c => ?_⟩
      rw [eval_xPolyK_tube]
      simp only [pocketKind, xPolyK, eval_tubeX, eval_add, eval_scale, eval_var, ofList]
      simp

theorem pocket_sound (e0 : ℚ) (f : Frame) (hP : ∀ k m, Covered (pocketRoot e0 k m))
    (hv : HandoffValid e0 .pocket f) : Covered f := by
  obtain ⟨hkind, haff, -, -, hl1, hh1, hl0, hh0, hl3, hh3, hl4, hh4, hl6, hh6, k, hseg, hu0,
    hu1, hl5, hh5⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [haff, affY_nil, hkind] at hc
  have hy6 : 0 < y 6 := hρ (by simp [hkind])
  have bd : ∀ v, (f.lo v : ℝ) ≤ y v ∧ y v ≤ f.hi v := f.mem_bounds hmem
  have b0 := bd 0
  have b1 := bd 1
  have b2 := bd 2
  have b3 := bd 3
  have b4 := bd 4
  have b5 := bd 5
  have b6 := bd 6
  have q : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ b := fun h => by exact_mod_cast h
  have hy1 : y 1 = 1 := by
    have := q hl1.ge; have := q hh1.le; push_cast at *; linarith [b1.1, b1.2]
  have hy5 : y 5 = faceSign (pocketSpec k).2.1.val := by
    have e1 := q hl5.ge; have e2 := q hh5.le; linarith [b5.1, b5.2]
  have ey0 : 0 ≤ y 0 ∧ y 0 ≤ e0 := ⟨by linarith [q hl0, b0.1], by linarith [q hh0, b0.2]⟩
  have eu : ((pocketSpec k).2.2.1 : ℝ) ≤ y 2 ∧ y 2 ≤ (pocketSpec k).2.2.2 :=
    ⟨by linarith [q hu0, b2.1], by linarith [q hu1, b2.2]⟩
  have e3 : -(pocketW : ℝ) ≤ y 3 ∧ y 3 ≤ pocketW := by
    have := q hl3; have := q hh3; push_cast at *; constructor <;> linarith [b3.1, b3.2]
  have e4 : (pocketB0 : ℝ) ≤ y 4 ∧ y 4 ≤ pocketB1 :=
    ⟨by linarith [q hl4, b4.1], by linarith [q hh4, b4.2]⟩
  have e6 : 0 ≤ y 6 ∧ y 6 ≤ rho0 := ⟨by linarith [q hl6, b6.1], by linarith [q hh6, b6.2]⟩
  obtain ⟨m, w, hw, hw2, hwx⟩ := pocket_chart f.seg y hε e3
  set y' := ofList [y 0, y 1, y 2, w, y 4, y 5, y 6] with hy'
  have hc' : Coords (pocketRoot e0 k m).seg (pocketRoot e0 k m).kind p y' := by
    simp only [pocketRoot, hseg]
    exact ⟨fun c => (hc.view c).trans (wVal_congr f.seg rfl rfl rfl c).symm,
      hc.cx.trans (hwx 0).symm, hc.cy.trans (hwx 1).symm, hc.cz.trans (hwx 2).symm⟩
  have hmem' : (pocketRoot e0 k m).box.Mem y' := by
    apply mem_pocketRoot e0 k m _ (by simp)
    intro i hi
    interval_cases i
    · simp only [pocketRoot]; simp; rw [abs_le]; constructor <;> linarith [ey0.1, ey0.2]
    · simp [pocketRoot, hy1]
    · simp only [pocketRoot]; simp; exact abs_sub_mid_le eu.1 eu.2
    · simp only [pocketRoot]; simp; exact abs_sub_mid_le hw hw2
    · simp only [pocketRoot]; simp; exact abs_sub_mid_le e4.1 e4.2
    · simp [pocketRoot, hy5]
    · simp only [pocketRoot]; simp; rw [abs_le]; constructor <;> linarith [e6.1, e6.2]
  exact (hP k m).apply_nil rfl p offset y' hc' hmem' (by exact hε) (fun _ => by exact hy6)
    (fun _ => by simp [hy', ofList, hy1]) hflip hscale

theorem eval_skewX (a : Poly) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (skewX a c) = y 0 * ((M1 c : ℝ) * eval y a + (M2 c : ℝ) * y 4 +
      (M3 c : ℝ) * (y 5 + -(skewK : ℝ) * y 4)) := by
  simp [skewX, eval_mul, eval_add, eval_scale]

theorem eval_xPolyK_skew (seg : Bool) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (xPolyK seg .skew c) = y 0 * ((M1 c : ℝ) * y 3 + (M2 c : ℝ) * y 4 +
      (M3 c : ℝ) * (y 5 + -(skewK : ℝ) * y 4)) := by
  simp [xPolyK, eval_mul, eval_add, eval_scale]

theorem spocket_sound (e0 : ℚ) (f : Frame) (hP : ∀ m, Covered (spocketRoot e0 m))
    (hv : HandoffValid e0 .spocket f) : Covered f := by
  obtain ⟨hkind, hseg, haff, -, -, hl1, hh1, hl0, hh0, hl2, hh2, hl3, hh3, hl4, hh4, hl5,
    hh5⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [haff, affY_nil, hkind] at hc
  have bd : ∀ v, (f.lo v : ℝ) ≤ y v ∧ y v ≤ f.hi v := f.mem_bounds hmem
  have q : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ b := fun h => by exact_mod_cast h
  have hy1 : y 1 = 1 := by
    have := q hl1.ge; have := q hh1.le; push_cast at *; linarith [(bd 1).1, (bd 1).2]
  have ey0 : 0 ≤ y 0 ∧ y 0 ≤ e0 := ⟨by linarith [q hl0, (bd 0).1], by linarith [q hh0, (bd 0).2]⟩
  have eu : (0 : ℝ) ≤ y 2 ∧ y 2 ≤ 1 := by
    have := q hl2; have := q hh2; push_cast at *; constructor <;> linarith [(bd 2).1, (bd 2).2]
  have e3 : -(pocketW : ℝ) ≤ y 3 ∧ y 3 ≤ pocketW := by
    have := q hl3; have := q hh3; push_cast at *; constructor <;> linarith [(bd 3).1, (bd 3).2]
  have e4 : (skewB0 : ℝ) ≤ y 4 ∧ y 4 ≤ skewB1 :=
    ⟨by linarith [q hl4, (bd 4).1], by linarith [q hh4, (bd 4).2]⟩
  have e5 : -(skewDelta : ℝ) ≤ y 5 ∧ y 5 ≤ skewDelta := by
    have := q hl5; have := q hh5; push_cast at *; constructor <;> linarith [(bd 5).1, (bd 5).2]
  have hA : (0 : ℝ) < atubeA := by norm_num [atubeA]
  obtain ⟨m, w, hw, hw2, hwx⟩ : ∃ (m : Fin 3) (w : ℝ),
      ((pocketVar3 m).1 : ℝ) ≤ w ∧ w ≤ (pocketVar3 m).2 ∧
      ∀ c, eval (ofList [y 0, y 1, y 2, w, y 4, y 5]) (xPolyK f.seg (spocketKind m) c) =
        eval y (xPolyK f.seg .skew c) := by
    rcases le_or_gt |y 3| (atubeA * y 0) with h | h
    · refine ⟨0, y 3 / y 0, ?_⟩
      have hle : |y 3 / y 0| ≤ atubeA := by
        rw [abs_div, abs_of_pos hε, div_le_iff₀ hε]; linarith
      have hb := abs_le.mp hle
      refine ⟨by simpa [pocketVar3] using hb.1, by simpa [pocketVar3] using hb.2, fun c => ?_⟩
      rw [eval_xPolyK_skew]
      simp only [spocketKind, xPolyK, eval_skewX, eval_mul, eval_var, ofList]
      simp
      field_simp
      try simp
    · have hy3 : y 3 ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at h
        have := mul_pos hA hε
        linarith
      rcases lt_or_gt_of_ne hy3 with hneg | hpos
      · have : y 3 < -(atubeA * y 0) := by
          rw [abs_of_neg hneg] at h; linarith
        refine ⟨2, y 3 + atubeA * y 0, by simp [pocketVar3]; linarith [e3.1, mul_pos hA hε],
          by simp [pocketVar3]; linarith, fun c => ?_⟩
        rw [eval_xPolyK_skew]
        simp only [spocketKind, xPolyK, eval_skewX, eval_add, eval_scale, eval_var, ofList]
        simp
      · have : atubeA * y 0 < y 3 := by
          rw [abs_of_pos hpos] at h; linarith
        refine ⟨1, y 3 - atubeA * y 0, by simp [pocketVar3]; linarith,
          by simp [pocketVar3]; linarith [e3.2, mul_pos hA hε], fun c => ?_⟩
        rw [eval_xPolyK_skew]
        simp only [spocketKind, xPolyK, eval_skewX, eval_add, eval_scale, eval_var, ofList]
        simp
  set y' := ofList [y 0, y 1, y 2, w, y 4, y 5] with hy'
  have hc' : Coords (spocketRoot e0 m).seg (spocketRoot e0 m).kind p y' := by
    simp only [spocketRoot, ← hseg]
    exact ⟨fun c => (hc.view c).trans (wVal_congr f.seg rfl rfl rfl c).symm,
      hc.cx.trans (hwx 0).symm, hc.cy.trans (hwx 1).symm, hc.cz.trans (hwx 2).symm⟩
  have hmem' : (spocketRoot e0 m).box.Mem y' := by
    apply mem_ofList (by simp [spocketRoot]) (by simp [spocketRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp only [spocketRoot]; simp; rw [abs_le]; constructor <;> linarith [ey0.1, ey0.2]
    · simp [spocketRoot, hy1]
    · simp only [spocketRoot]; simp; rw [abs_le]; constructor <;> linarith [eu.1, eu.2]
    · simp only [spocketRoot]; simp; exact abs_sub_mid_le hw hw2
    · simp only [spocketRoot]; simp; exact abs_sub_mid_le e4.1 e4.2
    · simp only [spocketRoot]; simp; rw [abs_le]; constructor <;> linarith [e5.1, e5.2]
  exact (hP m).apply_nil rfl p offset y' hc' hmem' (by exact hε)
    (fun h => by simp [spocketRoot, spocketKind] at h; fin_cases m <;> simp at h)
    (fun _ => by simp [hy', ofList, hy1]) hflip hscale

theorem eval_plainX (a : Poly) (y : ℕ → ℝ) (c : Fin 3) :
    eval y (plainX a c) = y 0 * ((M1 c : ℝ) * eval y a + (M2 c : ℝ) * y 4 +
      (M3 c : ℝ) * y 5) := by
  simp [plainX, eval_mul, eval_add, eval_scale]

theorem ppocket_sound (e0 : ℚ) (f : Frame) (hP : ∀ k m, Covered (ppocketRoot e0 k m))
    (hv : HandoffValid e0 .ppocket f) : Covered f := by
  obtain ⟨hkind, haff, -, -, hl1, hh1, hl0, hh0, hl3, hh3, hl4, hh4, k, hseg, hl2, hh2,
    hl5, hh5⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [haff, affY_nil, hkind] at hc
  have bd : ∀ v, (f.lo v : ℝ) ≤ y v ∧ y v ≤ f.hi v := f.mem_bounds hmem
  have q : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ b := fun h => by exact_mod_cast h
  have hy1 : y 1 = 1 := by
    have := q hl1.ge; have := q hh1.le; push_cast at *; linarith [(bd 1).1, (bd 1).2]
  have ey0 : 0 ≤ y 0 ∧ y 0 ≤ e0 := ⟨by linarith [q hl0, (bd 0).1], by linarith [q hh0, (bd 0).2]⟩
  have eu : ((ppocketSpec k).2.1 : ℝ) ≤ y 2 ∧ y 2 ≤ (ppocketSpec k).2.2.1 :=
    ⟨by linarith [q hl2, (bd 2).1], by linarith [q hh2, (bd 2).2]⟩
  have e3 : -(pocketW : ℝ) ≤ y 3 ∧ y 3 ≤ pocketW := by
    have := q hl3; have := q hh3; push_cast at *; constructor <;> linarith [(bd 3).1, (bd 3).2]
  have e4 : (0 : ℝ) ≤ y 4 ∧ y 4 ≤ 1 := by
    have := q hl4; have := q hh4; push_cast at *; constructor <;> linarith [(bd 4).1, (bd 4).2]
  have e5 : ((ppocketSpec k).2.2.2 - 31 / 64 : ℝ) ≤ y 5 ∧
      y 5 ≤ (ppocketSpec k).2.2.2 + 31 / 64 := by
    have := q hl5; have := q hh5; push_cast at *; constructor <;> linarith [(bd 5).1, (bd 5).2]
  have hA : (0 : ℝ) < atubeA := by norm_num [atubeA]
  obtain ⟨m, w, hw, hw2, hwx⟩ : ∃ (m : Fin 3) (w : ℝ),
      ((pocketVar3 m).1 : ℝ) ≤ w ∧ w ≤ (pocketVar3 m).2 ∧
      ∀ c, eval (ofList [y 0, y 1, y 2, w, y 4, y 5]) (xPolyK f.seg (ppocketKind m) c) =
        eval y (xPolyK f.seg .plain c) := by
    rcases le_or_gt |y 3| (atubeA * y 0) with h | h
    · refine ⟨0, y 3 / y 0, ?_⟩
      have hle : |y 3 / y 0| ≤ atubeA := by
        rw [abs_div, abs_of_pos hε, div_le_iff₀ hε]; linarith
      have hb := abs_le.mp hle
      refine ⟨by simpa [pocketVar3] using hb.1, by simpa [pocketVar3] using hb.2, fun c => ?_⟩
      rw [eval_xPolyK_plain]
      simp only [ppocketKind, xPolyK, eval_plainX, eval_mul, eval_var, ofList]
      simp
      field_simp
      try simp
    · have hy3 : y 3 ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at h
        have := mul_pos hA hε
        linarith
      rcases lt_or_gt_of_ne hy3 with hneg | hpos
      · have : y 3 < -(atubeA * y 0) := by
          rw [abs_of_neg hneg] at h; linarith
        refine ⟨2, y 3 + atubeA * y 0, by simp [pocketVar3]; linarith [e3.1, mul_pos hA hε],
          by simp [pocketVar3]; linarith, fun c => ?_⟩
        rw [eval_xPolyK_plain]
        simp only [ppocketKind, xPolyK, eval_plainX, eval_add, eval_scale, eval_var, ofList]
        simp
      · have : atubeA * y 0 < y 3 := by
          rw [abs_of_pos hpos] at h; linarith
        refine ⟨1, y 3 - atubeA * y 0, by simp [pocketVar3]; linarith,
          by simp [pocketVar3]; linarith [e3.2, mul_pos hA hε], fun c => ?_⟩
        rw [eval_xPolyK_plain]
        simp only [ppocketKind, xPolyK, eval_plainX, eval_add, eval_scale, eval_var, ofList]
        simp
  set y' := ofList [y 0, y 1, y 2, w, y 4, y 5] with hy'
  have hc' : Coords (ppocketRoot e0 k m).seg (ppocketRoot e0 k m).kind p y' := by
    simp only [ppocketRoot, hseg]
    exact ⟨fun c => (hc.view c).trans (wVal_congr f.seg rfl rfl rfl c).symm,
      hc.cx.trans (hwx 0).symm, hc.cy.trans (hwx 1).symm, hc.cz.trans (hwx 2).symm⟩
  have hmem' : (ppocketRoot e0 k m).box.Mem y' := by
    apply mem_ofList (by simp [ppocketRoot]) (by simp [ppocketRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp only [ppocketRoot]; simp; rw [abs_le]; constructor <;> linarith [ey0.1, ey0.2]
    · simp [ppocketRoot, hy1]
    · simp only [ppocketRoot]; simp; exact abs_sub_mid_le eu.1 eu.2
    · simp only [ppocketRoot]; simp; exact abs_sub_mid_le hw hw2
    · simp only [ppocketRoot]; simp; rw [abs_le]; constructor <;> linarith [e4.1, e4.2]
    · simp only [ppocketRoot]; simp; rw [abs_le]; constructor <;> linarith [e5.1, e5.2]
  exact (hP k m).apply_nil rfl p offset y' hc' hmem' (by exact hε)
    (fun h => by simp [ppocketRoot, ppocketKind] at h; fin_cases m <;> simp at h)
    (fun _ => by simp [hy', ofList, hy1]) hflip hscale

/-! ### Cone frames into the tie pockets -/

/-- Rescaling plain coordinates by `ρ ≠ 0` gives tube coordinates. -/
theorem tube_of_plain {seg : Bool} {p : AtlasPose ℝ} {y : ℕ → ℝ}
    (hc : Coords seg .plain p y) {ρ : ℝ} (hρ : ρ ≠ 0) :
    Coords seg .tube p (ofList [y 0, y 1, y 2, y 3 / ρ, y 4 / ρ, y 5 / ρ, ρ]) := by
  obtain ⟨hx, hy, hz⟩ := hc.plain_xyz
  refine ⟨fun c => (hc.view c).trans (wVal_congr seg rfl rfl rfl c).symm, ?_, ?_, ?_⟩
  · rw [hx]; simp [ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]
    field_simp
  · rw [hy]; simp [ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]
    field_simp; ring
  · rw [hz]; simp [ofList, xPolyK, eval_xPoly, xVal, scaleVal, M1, M2, M3]
    field_simp

/-- A plain point near the tie whose face coordinate is `ρ > 0` lies in a tie pocket. -/
theorem cpocket_core (e0 : ℚ) (face : Fin 2) (hT : ∀ m, Covered (tpocketRoot e0 face m))
    {p : AtlasPose ℝ} (offset : ℝ²) {z : ℕ → ℝ} (hc : Coords false .plain p z)
    (hε : 0 < z 0) (hz0 : z 0 ≤ e0) (hz1 : z 1 = 1)
    (hu0 : (coneTie : ℝ) ≤ z 2) (hu1 : z 2 ≤ coneTie + tpocketDU)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ rho0) (ha : |z 3| ≤ tpocketW * ρ)
    (h4 : |z 4 / ρ - ((if face = 0 then 1 else 1 / 2 : ℚ) : ℝ)| ≤
      ((if face = 0 then 0 else 1 / 2 : ℚ) : ℝ))
    (h5 : |z 5 / ρ - ((if face = 0 then 1 / 2 else 1 : ℚ) : ℝ)| ≤
      ((if face = 0 then 1 / 2 else 0 : ℚ) : ℝ))
    (hflip : p.FlipReduced) (hscale : 1 ≤ viewScale 0 p) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hc' := tube_of_plain hc (ne_of_gt hρ)
  set y' := ofList [z 0, z 1, z 2, z 3 / ρ, z 4 / ρ, z 5 / ρ, ρ] with hy'
  have e3 : -(tpocketW : ℝ) ≤ y' 3 ∧ y' 3 ≤ tpocketW := by
    have : |z 3 / ρ| ≤ tpocketW := by
      rw [abs_div, abs_of_pos hρ, div_le_iff₀ hρ]; exact ha
    exact abs_le.mp this
  have hε' : 0 < y' 0 := hε
  obtain ⟨m, w, hw, hw2, hwx⟩ := pocket_chart_tp false y' hε' e3
  set y'' := ofList [y' 0, y' 1, y' 2, w, y' 4, y' 5, y' 6] with hy''
  have hc'' : Coords (tpocketRoot e0 face m).seg (tpocketRoot e0 face m).kind p y'' :=
    ⟨fun c => (hc'.view c).trans (wVal_congr false rfl rfl rfl c).symm,
      hc'.cx.trans (hwx 0).symm, hc'.cy.trans (hwx 1).symm, hc'.cz.trans (hwx 2).symm⟩
  have hmem : (tpocketRoot e0 face m).box.Mem y'' := by
    apply mem_ofList (by simp [tpocketRoot]) (by simp [tpocketRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp [y', ofList, tpocketRoot, abs_le]; constructor <;> linarith
    · simp [y', ofList, tpocketRoot, hz1]
    · simp [y', ofList, tpocketRoot, abs_le]; constructor <;> linarith
    · simp only [tpocketRoot]; simp; exact abs_sub_mid_le hw hw2
    · simpa [y'', y', ofList, tpocketRoot] using h4
    · simpa [y'', y', ofList, tpocketRoot] using h5
    · simp [y', ofList, tpocketRoot, abs_le, rho0]
      have : ρ ≤ 1 / 16 := by simpa [rho0] using hρ1
      constructor <;> linarith
  exact (hT m).apply_nil rfl p offset y'' hc'' hmem hε' (fun _ => hρ)
    (fun _ => by simp [y'', y', ofList, hz1]) hflip hscale

theorem cpocket_sound (e0 : ℚ) (f : Frame) (hT : ∀ face m, Covered (tpocketRoot e0 face m))
    (hv : HandoffValid e0 .cpocket f) : Covered f := by
  obtain ⟨hkind, hseg, -, -, hl1, hh1, hl0, hh0, hrad, hineq⟩ := hv
  intro p offset y hc hmem hε hρ hlam hflip hscale
  rw [hkind, hseg] at hc
  set z := affY f.aff y with hz
  have bd : ∀ v, (f.lo v : ℝ) ≤ y v ∧ y v ≤ f.hi v := f.mem_bounds hmem
  have q : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ b := fun h => by exact_mod_cast h
  have z0 : z 0 = y 0 := affY_of_not_mem _ _ (by omega)
  have z1 : z 1 = y 1 := affY_of_not_mem _ _ (by omega)
  have hy1 : y 1 = 1 := by
    have := q hl1.ge; have := q hh1.le; push_cast at *; linarith [(bd 1).1, (bd 1).2]
  have hy0 : y 0 ≤ e0 := by linarith [q hh0, (bd 0).2]
  have hε' : 0 < z 0 := by rw [z0]; exact hε
  have hz0 : z 0 ≤ e0 := by rw [z0]; exact hy0
  have hz1 : z 1 = 1 := by rw [z1]; exact hy1
  have hvars := fun v hv => f.toRow.nonnegVars_sound hmem v hv
  have hradf := f.toRow.radius_nonneg hrad
  have g : ∀ P, normalize P ∈ cpocketIneqs f.aff → 0 ≤ eval y P := fun P hP => by
    have := NonnegOk.sound (hineq _ hP) hmem hradf hvars
    rwa [eval_normalize] at this
  have ez : ∀ k, eval y (affPoly f.aff k) = z k := fun k => rfl
  obtain ⟨hx, hy, hzz⟩ := hc.plain_xyz
  have i0 := g (add (affPoly f.aff 2) (const (-coneTie))) (by simp [cpocketIneqs])
  have i1 := g (add (const (coneTie + tpocketDU)) (scale (-1) (affPoly f.aff 2)))
    (by simp [cpocketIneqs])
  have i2 := g (affPoly f.aff 4) (by simp [cpocketIneqs])
  have i3 := g (affPoly f.aff 5) (by simp [cpocketIneqs])
  have i4 := g (add (const rho0) (scale (-1) (affPoly f.aff 4))) (by simp [cpocketIneqs])
  have i5 := g (add (const rho0) (scale (-1) (affPoly f.aff 5))) (by simp [cpocketIneqs])
  have i6 := g (add (scale (tpocketW / 2) (add (affPoly f.aff 4) (affPoly f.aff 5)))
    (affPoly f.aff 3)) (by simp [cpocketIneqs])
  have i7 := g (add (scale (tpocketW / 2) (add (affPoly f.aff 4) (affPoly f.aff 5)))
    (scale (-1) (affPoly f.aff 3))) (by simp [cpocketIneqs])
  simp only [eval_add, eval_const, eval_scale, ez] at i0 i1 i2 i3 i4 i5 i6 i7
  push_cast at i0 i1 i2 i3 i4 i5 i6 i7
  have hu0 : (coneTie : ℝ) ≤ z 2 := by linarith
  have hu1 : z 2 ≤ coneTie + tpocketDU := by linarith
  have hW : (0 : ℝ) < tpocketW := by norm_num [tpocketW]
  rcases le_total (z 5) (z 4) with hcb | hbc
  · -- face `b = +1`
    rcases i2.eq_or_lt with h0 | hpos
    · have z4 : z 4 = 0 := h0.symm
      have z5 : z 5 = 0 := by linarith
      have z3 : z 3 = 0 := by rw [z4, z5] at i6 i7; linarith
      exact not_rupert_of_cayley_zero (by rw [hx, z3, z4]; ring) (by rw [hy, z3, z4]; ring)
        (by rw [hzz, z5]; ring) offset
    · have hm : (tpocketW : ℝ) * z 5 ≤ tpocketW * z 4 := mul_le_mul_of_nonneg_left hcb hW.le
      have ha : |z 3| ≤ tpocketW * z 4 := abs_le.mpr ⟨by linarith, by linarith⟩
      refine cpocket_core e0 0 (hT 0) offset hc hε' hz0 hz1 hu0 hu1 hpos (by linarith) ha
        ?_ ?_ hflip hscale
      · simp [div_self (ne_of_gt hpos)]
      · simp only; push_cast
        rw [abs_le]
        have : z 5 / z 4 ≤ 1 := (div_le_one hpos).mpr hcb
        have : 0 ≤ z 5 / z 4 := div_nonneg i3 hpos.le
        constructor <;> linarith
  · -- face `c = +1`
    rcases i3.eq_or_lt with h0 | hpos
    · have z5 : z 5 = 0 := h0.symm
      have z4 : z 4 = 0 := by linarith
      have z3 : z 3 = 0 := by rw [z4, z5] at i6 i7; linarith
      exact not_rupert_of_cayley_zero (by rw [hx, z3, z4]; ring) (by rw [hy, z3, z4]; ring)
        (by rw [hzz, z5]; ring) offset
    · have hm : (tpocketW : ℝ) * z 4 ≤ tpocketW * z 5 := mul_le_mul_of_nonneg_left hbc hW.le
      have ha : |z 3| ≤ tpocketW * z 5 := abs_le.mpr ⟨by linarith, by linarith⟩
      refine cpocket_core e0 1 (hT 1) offset hc hε' hz0 hz1 hu0 hu1 hpos (by linarith) ha
        ?_ ?_ hflip hscale
      · simp only [show ¬ ((1 : Fin 2) = 0) by decide, ite_false]; push_cast
        rw [abs_le]
        have : z 4 / z 5 ≤ 1 := (div_le_one hpos).mpr hbc
        have : 0 ≤ z 4 / z 5 := div_nonneg i2 hpos.le
        constructor <;> linarith
      · simp [div_self (ne_of_gt hpos)]

/-- The hand-offs are sound once the tube, wedge, wedge-tube and skew roots
are covered. -/
theorem handoffs_sound (e0 : ℚ)
    (hT : ∀ seg face, Covered (tubeRoot e0 seg face))
    (hW : ∀ seg, Covered (wedgeRoot e0 seg))
    (hWT : ∀ seg face, Covered (wtubeRoot e0 seg face))
    (hS : Covered (skewRoot e0)) (hC : ∀ neg, Covered (coneRoot e0 neg))
    (hP : ∀ k m, Covered (pocketRoot e0 k m)) (hSP : ∀ m, Covered (spocketRoot e0 m))
    (hPP : ∀ k m, Covered (ppocketRoot e0 k m))
    (hTP : ∀ face m, Covered (tpocketRoot e0 face m)) :
    ∀ h f, (handoffs e0).Valid h f → Covered f := by
  intro h f hv
  cases h
  · exact tube_sound e0 f (hT f.seg) hv
  · exact wedge_sound e0 f (hW f.seg) hv
  · exact wtube_sound e0 f (hWT f.seg) hv
  · exact skew_sound e0 f hS hv
  · exact cone_sound e0 f hC hv
  · exact pocket_sound e0 f hP hv
  · exact spocket_sound e0 f hSP hv
  · exact ppocket_sound e0 f hPP hv
  · exact cpocket_sound e0 f hTP hv

end Noperts.Stellated.CornerHandoff

end
