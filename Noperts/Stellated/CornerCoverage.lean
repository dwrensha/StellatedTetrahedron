module

public import Noperts.Stellated.CornerHandoff

@[expose] public section

/-!
# The corner theorem

Blow-up coordinates exist for every pose near the corner: with
`S = w₀ - w₁`, `T = 2 w₂` (normalized view `w`) and the Cayley vector
`X = A' M₁ + B' M₂ + C' M₃`, the scale is `ε = max (S, T, |A'|, |B'|, |C'|)`.
If `ε = 0` the relative rotation is the identity (`SelfShadow`); otherwise the
pose lies in one of the seven plain root faces of the segment chosen by
`S ≥ T` (segment A) or `S < T` (segment B).

The trees are checked in three stages, so that hand-offs only point to
already covered roots: tube and wedge-tube tables (no hand-offs), wedge
tables (to the wedge tube), and plain tables (to the tube and the wedge).
-/

namespace Noperts.Stellated.CornerCoverage

open SparsePoly CornerPoly CornerCertificate CornerTree CornerHandoff
open AtlasProjectiveView

/-- Hand-offs restricted to the allowed targets. -/
def stage (e0 : ℚ) (allowed : Handoff → Bool) : Handoffs :=
  ⟨fun h f => allowed h = true ∧ HandoffValid e0 h f⟩

theorem stage_sound (e0 : ℚ) (allowed : Handoff → Bool)
    (hT : allowed .tube = true → ∀ seg face, Covered (tubeRoot e0 seg face))
    (hW : allowed .wedge = true → ∀ seg, Covered (wedgeRoot e0 seg))
    (hWT : allowed .wtube = true → ∀ seg face, Covered (wtubeRoot e0 seg face))
    (hS : allowed .skew = true → Covered (skewRoot e0))
    (hC : allowed .cone = true → ∀ neg, Covered (coneRoot e0 neg))
    (hP : allowed .pocket = true → ∀ k m, Covered (pocketRoot e0 k m))
    (hSP : allowed .spocket = true → ∀ m, Covered (spocketRoot e0 m))
    (hPP : allowed .ppocket = true → ∀ k m, Covered (ppocketRoot e0 k m))
    (hTP : allowed .cpocket = true → ∀ face m, Covered (tpocketRoot e0 face m)) :
    ∀ h f, (stage e0 allowed).Valid h f → Covered f := by
  intro h f ⟨ha, hv⟩
  cases h
  · exact tube_sound e0 f (hT ha f.seg) hv
  · exact wedge_sound e0 f (hW ha f.seg) hv
  · exact wtube_sound e0 f (hWT ha f.seg) hv
  · exact skew_sound e0 f (hS ha) hv
  · exact cone_sound e0 f (hC ha) hv
  · exact pocket_sound e0 f (hP ha) hv
  · exact spocket_sound e0 f (hSP ha) hv
  · exact ppocket_sound e0 f (hPP ha) hv
  · exact cpocket_sound e0 f (hTP ha) hv

def noHandoff : Handoff → Bool := fun _ => false
def coneStage : Handoff → Bool := fun h => h == .cone || h == .pocket
def wedgeStage : Handoff → Bool := fun h => h == .wtube
def skewStage : Handoff → Bool := fun h => h == .spocket
def cpocketStage : Handoff → Bool := fun h => h == .cpocket
def plainStage : Handoff → Bool :=
  fun h => h == .tube || h == .wedge || h == .skew || h == .cone || h == .ppocket

structure Tables where
  plain : Bool → Fin 7 → Table
  tube : Bool → Fin 6 → Table
  wedge : Bool → Table
  wtube : Bool → Fin 4 → Table
  skew : Table
  zero : Fin 6 → Table
  cone : (Fin 4 → Bool) → Table
  pocket : Fin 3 → Fin 3 → Table
  spocket : Fin 3 → Table
  ppocket : Fin 3 → Fin 3 → Table
  tpocket : Fin 2 → Fin 3 → Table

def Tables.Valid (e0 : ℚ) (t : Tables) : Prop :=
  (∀ face m, (t.tpocket face m).Valid (stage e0 noHandoff) (tpocketRoot e0 face m)) ∧
  (∀ k m, (t.ppocket k m).Valid (stage e0 noHandoff) (ppocketRoot e0 k m)) ∧
  (∀ m, (t.spocket m).Valid (stage e0 noHandoff) (spocketRoot e0 m)) ∧
  (∀ k m, (t.pocket k m).Valid (stage e0 noHandoff) (pocketRoot e0 k m)) ∧
  (∀ neg, (t.cone neg).Valid (stage e0 cpocketStage) (coneRoot e0 neg)) ∧
  (∀ seg face, (t.tube seg face).Valid (stage e0 coneStage) (tubeRoot e0 seg face)) ∧
  (∀ seg face, (t.wtube seg face).Valid (stage e0 noHandoff) (wtubeRoot e0 seg face)) ∧
  (∀ seg, (t.wedge seg).Valid (stage e0 wedgeStage) (wedgeRoot e0 seg)) ∧
  t.skew.Valid (stage e0 skewStage) (skewRoot e0) ∧
  (∀ face, (t.zero face).Valid (stage e0 noHandoff) (zeroRoot e0 face)) ∧
  (∀ seg face, (t.plain seg face).Valid (stage e0 plainStage) (plainRoot e0 seg face))

/-- `Tables.Valid` with every table's rows checked in parallel chunks. -/
def Tables.ValidPar (e0 : ℚ) (t : Tables) (tc : ℕ) : Prop :=
  (∀ face m, (t.tpocket face m).validParB (stage e0 noHandoff) (tpocketRoot e0 face m) tc =
    true) ∧
  (∀ k m,
    (t.ppocket k m).validParB (stage e0 noHandoff) (ppocketRoot e0 k m) tc = true) ∧
  (∀ m, (t.spocket m).validParB (stage e0 noHandoff) (spocketRoot e0 m) tc = true) ∧
  (∀ k m,
    (t.pocket k m).validParB (stage e0 noHandoff) (pocketRoot e0 k m) tc = true) ∧
  (∀ neg, (t.cone neg).validParB (stage e0 cpocketStage) (coneRoot e0 neg) tc = true) ∧
  (∀ seg face,
    (t.tube seg face).validParB (stage e0 coneStage) (tubeRoot e0 seg face) tc = true) ∧
  (∀ seg face,
    (t.wtube seg face).validParB (stage e0 noHandoff) (wtubeRoot e0 seg face) tc = true) ∧
  (∀ seg, (t.wedge seg).validParB (stage e0 wedgeStage) (wedgeRoot e0 seg) tc = true) ∧
  t.skew.validParB (stage e0 skewStage) (skewRoot e0) tc = true ∧
  (∀ face, (t.zero face).validParB (stage e0 noHandoff) (zeroRoot e0 face) tc = true) ∧
  (∀ seg face,
    (t.plain seg face).validParB (stage e0 plainStage) (plainRoot e0 seg face) tc = true)

instance (e0 : ℚ) (t : Tables) (tc : ℕ) : Decidable (t.ValidPar e0 tc) := by
  unfold Tables.ValidPar; infer_instance

theorem Tables.Valid.of_par {e0 : ℚ} {t : Tables} {tc : ℕ} (h : t.ValidPar e0 tc) :
    t.Valid e0 := by
  obtain ⟨tp, z, a, b, c, d, e, f, g, k, l⟩ := h
  exact ⟨fun x y => Table.Valid.of_parB (tp x y), fun x y => Table.Valid.of_parB (z x y), fun x => Table.Valid.of_parB (a x), fun x y => Table.Valid.of_parB (b x y),
    fun x => Table.Valid.of_parB (c x), fun x y => Table.Valid.of_parB (d x y),
    fun x y => Table.Valid.of_parB (e x y), fun x => Table.Valid.of_parB (f x),
    Table.Valid.of_parB g, fun x => Table.Valid.of_parB (k x),
    fun x y => Table.Valid.of_parB (l x y)⟩

instance (e0 : ℚ) (t : Tables) : Decidable (t.Valid e0) := by
  unfold Tables.Valid; infer_instance

/-- Coverage of every table root, each assuming the hand-offs its stage allows
are sound; supplied by `Tables.Valid` (native) or by kernel checkers. -/
structure Cov (e0 : ℚ) : Prop where
  tpocket : ∀ face m, (∀ h f, (stage e0 noHandoff).Valid h f → Covered f) →
    Covered (tpocketRoot e0 face m)
  ppocket : ∀ k m, (∀ h f, (stage e0 noHandoff).Valid h f → Covered f) →
    Covered (ppocketRoot e0 k m)
  spocket : ∀ m, (∀ h f, (stage e0 noHandoff).Valid h f → Covered f) →
    Covered (spocketRoot e0 m)
  pocket : ∀ k m, (∀ h f, (stage e0 noHandoff).Valid h f → Covered f) →
    Covered (pocketRoot e0 k m)
  cone : ∀ neg, (∀ h f, (stage e0 cpocketStage).Valid h f → Covered f) →
    Covered (coneRoot e0 neg)
  tube : ∀ seg face, (∀ h f, (stage e0 coneStage).Valid h f → Covered f) →
    Covered (tubeRoot e0 seg face)
  wtube : ∀ seg face, (∀ h f, (stage e0 noHandoff).Valid h f → Covered f) →
    Covered (wtubeRoot e0 seg face)
  wedge : ∀ seg, (∀ h f, (stage e0 wedgeStage).Valid h f → Covered f) →
    Covered (wedgeRoot e0 seg)
  skew : (∀ h f, (stage e0 skewStage).Valid h f → Covered f) → Covered (skewRoot e0)
  zero : ∀ face, (∀ h f, (stage e0 noHandoff).Valid h f → Covered f) →
    Covered (zeroRoot e0 face)
  plain : ∀ seg face, (∀ h f, (stage e0 plainStage).Valid h f → Covered f) →
    Covered (plainRoot e0 seg face)

theorem Tables.Valid.cov {e0 : ℚ} {t : Tables} (hv : t.Valid e0) : Cov e0 := by
  obtain ⟨htpocket, hppocket, hspocket, hpocket, hcone, htube, hwtube, hwedge, hskew, hzero,
    hplain⟩ := hv
  exact ⟨fun face m hH => Table.covered _ hH _ _ (htpocket face m),
    fun k m hH => Table.covered _ hH _ _ (hppocket k m),
    fun m hH => Table.covered _ hH _ _ (hspocket m),
    fun k m hH => Table.covered _ hH _ _ (hpocket k m),
    fun neg hH => Table.covered _ hH _ _ (hcone neg),
    fun seg face hH => Table.covered _ hH _ _ (htube seg face),
    fun seg face hH => Table.covered _ hH _ _ (hwtube seg face),
    fun seg hH => Table.covered _ hH _ _ (hwedge seg),
    fun hH => Table.covered _ hH _ _ hskew,
    fun face hH => Table.covered _ hH _ _ (hzero face),
    fun seg face hH => Table.covered _ hH _ _ (hplain seg face)⟩

theorem Cov.covered {e0 : ℚ} (hv : Cov e0) :
    (∀ seg face, Covered (plainRoot e0 seg face)) ∧
      ∀ face, Covered (zeroRoot e0 face) := by
  have none := stage_sound e0 noHandoff (by simp [noHandoff]) (by simp [noHandoff])
    (by simp [noHandoff]) (by simp [noHandoff]) (by simp [noHandoff]) (by simp [noHandoff])
    (by simp [noHandoff]) (by simp [noHandoff]) (by simp [noHandoff])
  have cTP : ∀ face m, Covered (tpocketRoot e0 face m) := fun face m => hv.tpocket face m none
  have sCP := stage_sound e0 cpocketStage (by simp [cpocketStage]) (by simp [cpocketStage])
    (by simp [cpocketStage]) (by simp [cpocketStage]) (by simp [cpocketStage])
    (by simp [cpocketStage]) (by simp [cpocketStage]) (by simp [cpocketStage]) (fun _ => cTP)
  have cSP : ∀ m, Covered (spocketRoot e0 m) := fun m => hv.spocket m none
  have cPP : ∀ k m, Covered (ppocketRoot e0 k m) := fun k m => hv.ppocket k m none
  have cP : ∀ k m, Covered (pocketRoot e0 k m) := fun k m => hv.pocket k m none
  have cC : ∀ neg, Covered (coneRoot e0 neg) := fun neg => hv.cone neg sCP
  have sC := stage_sound e0 coneStage (by simp [coneStage]) (by simp [coneStage])
    (by simp [coneStage]) (by simp [coneStage]) (fun _ => cC) (fun _ => cP)
    (by simp [coneStage]) (by simp [coneStage]) (by simp [coneStage])
  have cT : ∀ seg face, Covered (tubeRoot e0 seg face) := fun seg face => hv.tube seg face sC
  have cWT : ∀ seg face, Covered (wtubeRoot e0 seg face) := fun seg face =>
    hv.wtube seg face none
  have sS := stage_sound e0 skewStage (by simp [skewStage]) (by simp [skewStage])
    (by simp [skewStage]) (by simp [skewStage]) (by simp [skewStage]) (by simp [skewStage])
    (fun _ => cSP) (by simp [skewStage]) (by simp [skewStage])
  have cS : Covered (skewRoot e0) := hv.skew sS
  have sW := stage_sound e0 wedgeStage (by simp [wedgeStage]) (by simp [wedgeStage])
    (fun _ => cWT) (by simp [wedgeStage]) (by simp [wedgeStage]) (by simp [wedgeStage])
    (by simp [wedgeStage]) (by simp [wedgeStage]) (by simp [wedgeStage])
  have cW : ∀ seg, Covered (wedgeRoot e0 seg) := fun seg => hv.wedge seg sW
  have sP := stage_sound e0 plainStage (fun _ => cT) (fun _ => cW)
    (by simp [plainStage]) (fun _ => cS) (fun _ => cC) (by simp [plainStage])
    (by simp [plainStage]) (fun _ => cPP) (by simp [plainStage])
  exact ⟨fun seg face => hv.plain seg face sP, fun face => hv.zero face none⟩

theorem Tables.covered (e0 : ℚ) (t : Tables) (hv : t.Valid e0) :
    (∀ seg face, Covered (plainRoot e0 seg face)) ∧
      ∀ face, Covered (zeroRoot e0 face) :=
  hv.cov.covered

/-! ## Blow-up coordinates of a pose -/

theorem normalizedView_sum (p : AtlasPose ℝ) (hscale : 1 ≤ viewScale 0 p) :
    normalizedView 0 p 0 + normalizedView 0 p 1 + normalizedView 0 p 2 = 1 := by
  have h0 : viewScale 0 p ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hscale)
  simp only [normalizedView]
  rw [← add_div, ← add_div, div_eq_one_iff_eq h0]
  simp [viewScale, rootSign, Fin.sum_univ_three]

/-- The corner claim: views with `0 ≤ S, T ≤ e0` and Cayley vectors with
`|A'|, |B'|, |C'| ≤ e0`. -/
theorem corner_not_rupert (e0 : ℚ) (hcov : ∀ seg face, Covered (plainRoot e0 seg face))
    (hzero : ∀ face, Covered (zeroRoot e0 face)) (p : AtlasPose ℝ) (hflip : p.FlipReduced)
    (hscale : 1 ≤ viewScale 0 p)
    (hS0 : 0 ≤ normalizedView 0 p 0 - normalizedView 0 p 1)
    (hS1 : normalizedView 0 p 0 - normalizedView 0 p 1 ≤ e0)
    (hT0 : 0 ≤ 2 * normalizedView 0 p 2) (hT1 : 2 * normalizedView 0 p 2 ≤ e0)
    (hA : |(p.x + p.y) / 2| ≤ e0) (hB : |(p.x - p.y) / 2| ≤ e0) (hC : |p.z| ≤ e0)
    (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  set w := normalizedView 0 p with hw
  set S := w 0 - w 1 with hSdef
  set T := 2 * w 2 with hTdef
  set A := (p.x + p.y) / 2 with hAdef
  set B := (p.x - p.y) / 2 with hBdef
  set C := p.z with hCdef
  have hsum := normalizedView_sum p hscale
  set ρ := max (max |A| |B|) |C| with hρdef
  set ε := max (max S T) ρ with hεdef
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg _) (le_max_right _ _)
  have hST : max S T ≤ ε := le_max_left _ _
  have hρε : ρ ≤ ε := le_max_right _ _
  have hε1 : ε ≤ e0 := max_le (max_le hS1 hT1) (max_le (max_le hA hB) hC)
  have hA' : |A| ≤ ε := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hρε
  have hB' : |B| ≤ ε := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hρε
  have hC' : |C| ≤ ε := le_trans (le_max_right _ _) hρε
  rcases (le_trans hρ0 hρε).eq_or_lt with h0 | hpos
  · have zA : A = 0 := abs_nonpos_iff.mp (h0 ▸ hA')
    have zB : B = 0 := abs_nonpos_iff.mp (h0 ▸ hB')
    have zC : C = 0 := abs_nonpos_iff.mp (h0 ▸ hC')
    exact not_rupert_of_cayley_zero (by linarith) (by linarith) zC offset
  have hne : ε ≠ 0 := ne_of_gt hpos
  -- the segment and the view coordinates `(λ, u)`
  obtain ⟨seg, lam, u, hlam0, hlam1, hu0, hu1, hs, ht, hface0, hlampos, hzeroview⟩ :
      ∃ (seg : Bool) (lam u : ℝ), 0 ≤ lam ∧ lam ≤ 1 ∧ 0 ≤ u ∧ u ≤ 1 ∧
        ε * sVal seg (ofList [ε, lam, u]) = S ∧
        ε * tVal seg (ofList [ε, lam, u]) = -T ∧
        (max S T = ε → lam = 1) ∧ (0 < max S T → 0 < lam) ∧
        (max S T = 0 → seg = false ∧ lam = 0 ∧ u = 0) := by
    rcases le_or_gt T S with hts | hts
    · refine ⟨false, S / ε, if S = 0 then 0 else T / S, div_nonneg hS0 hpos.le,
        (div_le_one hpos).mpr (le_trans (le_max_left _ _) hST), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · split_ifs; · exact le_rfl
        · exact div_nonneg hT0 hS0
      · split_ifs with h; · norm_num
        · exact (div_le_one (lt_of_le_of_ne hS0 (Ne.symm h))).mpr hts
      · simp [sVal, ofList]; field_simp
      · simp only [tVal, ofList, List.getD_cons_succ, List.getD_cons_zero, Bool.false_eq_true,
          ite_false]
        split_ifs with h
        · have : T = 0 := le_antisymm (h ▸ hts) hT0
          simp [this]
        · field_simp
      · intro h; rw [max_eq_left hts] at h; rw [h, div_self hne]
      · intro h; rw [max_eq_left hts] at h; exact div_pos h hpos
      · intro h
        rw [max_eq_left hts] at h
        refine ⟨rfl, by rw [h, zero_div], by rw [ite_eq_left h]⟩
    · refine ⟨true, T / ε, S / T, div_nonneg hT0 hpos.le,
        (div_le_one hpos).mpr (le_trans (le_max_right _ _) hST),
        div_nonneg hS0 (le_trans hS0 hts.le), (div_le_one (lt_of_le_of_lt hS0 hts)).mpr hts.le,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [sVal, ofList]; field_simp [ne_of_gt (lt_of_le_of_lt hS0 hts)]
      · simp [tVal, ofList]; field_simp
      · intro h; rw [max_eq_right hts.le] at h; rw [h, div_self hne]
      · intro h; rw [max_eq_right hts.le] at h; exact div_pos h hpos
      · intro h; rw [max_eq_right hts.le] at h; linarith
  -- the plain chart point
  set y := ofList [ε, lam, u, A / ε, B / ε, C / ε] with hy
  have ey0 : y 0 = ε := rfl
  have ey1 : y 1 = lam := rfl
  have ey2 : y 2 = u := rfl
  have hsv : sVal seg y = sVal seg (ofList [ε, lam, u]) := sVal_congr seg rfl rfl
  have htv : tVal seg y = tVal seg (ofList [ε, lam, u]) := tVal_congr seg rfl rfl
  have hc : Coords seg .plain p y := by
    refine ⟨fun c => ?_, ?_, ?_, ?_⟩
    · simp only [wVal, ey0, hsv, htv]
      have e1 : ε * (↑(F1 c) * sVal seg (ofList [ε, lam, u]) +
          ↑(F2 c) * tVal seg (ofList [ε, lam, u])) = F1 c * S - F2 c * T := by
        linear_combination (↑(F1 c) : ℝ) * hs + (↑(F2 c) : ℝ) * ht
      rw [e1]
      fin_cases c <;> simp [B0, F1, F2, hSdef, hTdef, w] <;> linarith [hsum]
    · rw [eval_xPolyK_plain]
      simp [y, ofList, M1, M2, M3]
      field_simp
      simp [hAdef, hBdef]; ring
    · rw [eval_xPolyK_plain]
      simp [y, ofList, M1, M2, M3]
      field_simp
      simp [hAdef, hBdef]; ring
    · rw [eval_xPolyK_plain]
      simp [y, ofList, M1, M2, M3]
      field_simp
      exact hCdef.symm
  -- the root face
  have hA1 : |A / ε| ≤ 1 := by rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hA'
  have hB1 : |B / ε| ≤ 1 := by rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hB'
  have hC1 : |C / ε| ≤ 1 := by rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hC'
  have hε0 : (0 : ℝ) ≤ ε := hpos.le
  by_cases hmax : max S T = ε
  · have hl := hface0 hmax
    apply (hcov seg 0).apply_nil (by simp [plainRoot]) p offset y hc ?_ hpos
      (fun h => by simp [plainRoot] at h)
      (fun _ => by rw [ey1, hl]; norm_num) hflip hscale
    apply mem_ofList (by simp [plainRoot]) (by simp [plainRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp [plainRoot, abs_le]; constructor <;> linarith
    · simp [plainRoot, hl]
    · simp [plainRoot, abs_le]; constructor <;> linarith
    · simpa [plainRoot, y, ofList] using hA1
    · simpa [plainRoot, y, ofList] using hB1
    · simpa [plainRoot, y, ofList] using hC1
  · have hρeq : ε = ρ := by
      rcases le_total (max S T) ρ with h' | h'
      · exact max_eq_right h'
      · exact absurd (max_eq_left h').symm hmax
    obtain ⟨face, hface⟩ := exists_face3 A B C (by rw [← hρdef, ← hρeq]; exact hpos)
    have he : ∀ k : Fin 3, k.val = face.val / 2 →
        ![A, B, C] k / ρ = faceSign face.val := fun k => (hface k).2
    have hf : face.val / 2 < 3 := by omega
    by_cases hz : max S T = 0
    · obtain ⟨hsegA, hl0, hu0'⟩ := hzeroview hz
      subst hsegA
      apply (hzero face).apply_nil rfl p offset y hc ?_ hpos (fun h => by simp [zeroRoot] at h)
        (fun h => by
          exfalso
          have h0 : (zeroRoot e0 face).hi 1 = 0 := by
            simp only [zeroRoot, Frame.hi, Frame.toRow, Row.hi, Row.box]
            rw [getD_set_eq _ _ _ _ (by simp; omega), getD_set_eq _ _ _ _ (by simp; omega),
              ite_eq_right (by omega), ite_eq_right (by omega)]
            simp
          rw [h0] at h
          exact lt_irrefl _ h) hflip hscale
      apply mem_ofList (by simp [zeroRoot]) (by simp [zeroRoot])
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      simp only [zeroRoot]
      rw [getD_set_eq _ _ _ _ (by simp; omega), getD_set_eq _ _ _ _ (by simp; omega)]
      interval_cases i
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
        constructor <;> linarith
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [hl0]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [hu0']
      · split_ifs with h
        · have := he 0 (by simp; omega); simp [← hρeq] at this; simp [this]
        · simpa [y, ofList] using hA1
      · split_ifs with h
        · have := he 1 (by simp; omega); simp [← hρeq] at this; simp [this]
        · simpa [y, ofList] using hB1
      · split_ifs with h
        · have := he 2 (by simp; omega); simp [← hρeq] at this; simp [this]
        · simpa [y, ofList] using hC1
    have hlp : 0 < lam := hlampos (lt_of_le_of_ne (le_trans hS0 (le_max_left _ _)) (Ne.symm hz))
    apply (hcov seg ⟨face.val + 1, by omega⟩).apply_nil (by simp [plainRoot]) p offset y hc
      ?_ hpos
      (fun h => by simp [plainRoot] at h) (fun _ => by rw [ey1]; exact hlp) hflip hscale
    apply mem_ofList (by simp [plainRoot]) (by simp [plainRoot])
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    simp only [plainRoot, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]
    rw [getD_set_eq _ _ _ _ (by simp; omega), getD_set_eq _ _ _ _ (by simp; omega)]
    have hlam : |lam - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    interval_cases i
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
      constructor <;> linarith
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simpa [y, ofList] using hlam
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [abs_le]
      constructor <;> linarith
    · split_ifs with h
      · have := he 0 (by simp; omega); simp [← hρeq] at this; simp [this]
      · simpa [y, ofList] using hA1
    · split_ifs with h
      · have := he 1 (by simp; omega); simp [← hρeq] at this; simp [this]
      · simpa [y, ofList] using hB1
    · split_ifs with h
      · have := he 2 (by simp; omega); simp [← hρeq] at this; simp [this]
      · simpa [y, ofList] using hC1

end Noperts.Stellated.CornerCoverage

end
