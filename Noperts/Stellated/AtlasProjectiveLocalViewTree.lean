module

public import Noperts.Stellated.AtlasProjectiveLocalCertificate

@[expose] public section

/-!
# Shared projective-view atlas for symmetry-local rigidity

The expensive balanced-support geometry depends on the outer view but not on
the Cayley interval or chart.  This tree checks that geometry once.  A small
`Tube` then supplies only the chart-dependent mismatch bound, allowing every
near-symmetry leaf in the main search to reuse the same view atlas.
-/

namespace Noperts.Stellated.AtlasProjectiveLocalViewTree

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open Noperts.ProjectiveView

structure Tube where
  interval : AtlasInterval ℚ
  chart : CayleyAtlas.ChartIndex
  symmetryIndex : OrbitIndex
  r : ℚ
deriving DecidableEq

def Tube.shell (tube : Tube) : AtlasLocalCertificate.Box where
  interval := tube.interval
  chart := tube.chart
  symmetryIndex := tube.symmetryIndex
  certificate := fun _ => { contact := fun _ => { index := 0, direction := 0 } }
  c := 0
  r := tube.r

abbrev Tube.mismatchRadius (tube : Tube) : ℚ := tube.shell.mismatchRadius

def Tube.Valid (tube : Tube) : Prop := tube.mismatchRadius ≤ tube.r

instance (tube : Tube) : Decidable tube.Valid := by
  unfold Tube.Valid
  infer_instance

/-! ## Cutting a triangle at an interior point -/

/-- The point with barycentric weights `weights`. -/
def cutPoint (triangle : AtlasProjectiveView.Triangle ℚ) (weights : Fin 3 → ℚ) :
    AtlasProjectiveView.Vector ℚ :=
  fun c => weights 0 * triangle 0 c + weights 1 * triangle 1 c +
    weights 2 * triangle 2 c

/-- Replace corner `k` by the cut point. -/
def cutTriangle (triangle : AtlasProjectiveView.Triangle ℚ) (weights : Fin 3 → ℚ)
    (k : Fin 3) : AtlasProjectiveView.Triangle ℚ :=
  fun i => if i = k then cutPoint triangle weights else triangle i

theorem cut_affine (triangle : AtlasProjectiveView.Triangle ℚ) (weights : Fin 3 → ℚ)
    (μ : AtlasProjectiveView.Vector ℝ) (k : Fin 3) (t : ℝ)
    (htk : t * (weights k : ℝ) = μ k) :
    affinePoint (toReal triangle) μ =
      affinePoint (toReal (cutTriangle triangle weights k))
        (fun j => μ j - t * (weights j : ℝ) + if j = k then t else 0) := by
  funext c
  fin_cases k <;>
    simp [affinePoint, cutTriangle, cutPoint, toReal, Fin.sum_univ_three] at htk ⊢
  · linear_combination ((weights 0 : ℝ) * triangle 0 c + (weights 1 : ℝ) * triangle 1 c +
      (weights 2 : ℝ) * triangle 2 c - (triangle 0 c : ℝ)) * htk
  · linear_combination ((weights 0 : ℝ) * triangle 0 c + (weights 1 : ℝ) * triangle 1 c +
      (weights 2 : ℝ) * triangle 2 c - (triangle 1 c : ℝ)) * htk
  · linear_combination ((weights 0 : ℝ) * triangle 0 c + (weights 1 : ℝ) * triangle 1 c +
      (weights 2 : ℝ) * triangle 2 c - (triangle 2 c : ℝ)) * htk

/-- The children of a cut cover their parent.  A child whose weight is zero is
degenerate and may be omitted. -/
theorem mem_cut {triangle : AtlasProjectiveView.Triangle ℚ} {weights : Fin 3 → ℚ}
    (hw0 : ∀ j, 0 ≤ weights j) (hw1 : weights 0 + weights 1 + weights 2 = 1)
    {point : AtlasProjectiveView.Vector ℝ}
    (h : InTriangle (toReal triangle) point) :
    ∃ k, 0 < weights k ∧ InTriangle (toReal (cutTriangle triangle weights k)) point := by
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := h
  have hw0' : ∀ j, (0 : ℝ) ≤ weights j := fun j => by exact_mod_cast hw0 j
  have hwsum : ∑ j, (weights j : ℝ) = 1 := by
    simp only [Fin.sum_univ_three]; exact_mod_cast hw1
  let S : Finset (Fin 3) := Finset.univ.filter (fun j => (0 : ℝ) < weights j)
  have hS : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have hz : ∀ j, (weights j : ℝ) = 0 :=
      fun j => le_antisymm (not_lt.mp (hne (Finset.mem_univ j))) (hw0' j)
    simp [hz] at hwsum
  obtain ⟨k, hkS, hkmin⟩ := S.exists_min_image (fun j => μ j / weights j) hS
  have hk : (0 : ℝ) < weights k := (Finset.mem_filter.mp hkS).2
  refine ⟨k, by exact_mod_cast hk, ?_⟩
  have ht0 : 0 ≤ μ k / weights k := div_nonneg (hμ0 k) hk.le
  have htk : μ k / weights k * (weights k : ℝ) = μ k := by field_simp
  have hle : ∀ j, μ k / weights k * (weights j : ℝ) ≤ μ j := by
    intro j
    rcases (hw0' j).lt_or_eq with hj | hj
    · have := hkmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      rw [le_div_iff₀ hj] at this
      linarith
    · rw [← hj, mul_zero]; exact hμ0 j
  refine ⟨_, ?_, ?_, cut_affine triangle weights μ k _ htk⟩
  · intro j
    by_cases hj : j = k
    · subst hj; simp only [ite_true]; linarith
    · simp only [hj, ite_false]; linarith [hle j]
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hμ1, hwsum]
    ring

inductive Row where
  | split (id : ℕ) (children : Fin 4 → ℕ)
      (root : Fin 8) (triangle : AtlasProjectiveView.Triangle ℚ)
  | certificate (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
  | cut (id : ℕ) (children : Fin 3 → ℕ) (root : Fin 8)
      (triangle : AtlasProjectiveView.Triangle ℚ) (weights : Fin 3 → ℚ)
deriving DecidableEq

def Row.id : Row → ℕ
  | .split id .. | .certificate id .. | .cut id .. => id

def Row.root : Row → Fin 8
  | .split _ _ root _ | .certificate _ { root, .. } | .cut _ _ root _ _ => root

def Row.triangle : Row → AtlasProjectiveView.Triangle ℚ
  | .split _ _ _ triangle | .certificate _ { triangle, .. }
  | .cut _ _ _ triangle _ => triangle

instance : Inhabited Row where
  default := .split 0 (fun _ => 0) 0 chamberTriangle

def Row.ValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Row → Prop
  | .split id children root triangle => ∀ child,
      id < children child ∧ children child < size ∧
      (get (children child)).root = root ∧
      (get (children child)).triangle =
        Noperts.ProjectiveView.split triangle child
  | .certificate _ box =>
      box.symmetryIndex = symmetryIndex ∧ r ≤ box.r ∧ box.ViewValid
  | .cut id children root triangle weights =>
      (∀ j, 0 ≤ weights j) ∧ weights 0 + weights 1 + weights 2 = 1 ∧
      ∀ k, 0 < weights k →
        id < children k ∧ children k < size ∧
        (get (children k)).root = root ∧
        (get (children k)).triangle = cutTriangle triangle weights k

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) (row : Row) :
    Decidable (row.ValidAt symmetryIndex r get size) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Prop :=
  ∀ i : Fin size,
    (get i).id = i ∧ (get i).ValidAt symmetryIndex r get size

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) : Decidable (RowsValidAt symmetryIndex r get size) := by
  unfold RowsValidAt
  infer_instance

/-- A kernel-checkable slice of `RowsValidAt`.  Generated local-view tables
prove small slices independently and join them, so kernel reduction never has
to unfold the entire certificate atlas at once. -/
def RowsValidRangeAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size start count : ℕ) : Prop :=
  start + count ≤ size ∧ ∀ j : Fin count,
    (get (start + j.val)).id = start + j.val ∧
      (get (start + j.val)).ValidAt symmetryIndex r get size

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size start count : ℕ) :
    Decidable (RowsValidRangeAt symmetryIndex r get size start count) := by
  unfold RowsValidRangeAt
  infer_instance

theorem rowsValidRange_append {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size start left right : ℕ}
    (hleft : RowsValidRangeAt symmetryIndex r get size start left)
    (hright : RowsValidRangeAt symmetryIndex r get size (start + left) right) :
    RowsValidRangeAt symmetryIndex r get size start (left + right) := by
  unfold RowsValidRangeAt at hleft hright ⊢
  constructor
  · omega
  · intro j
    by_cases hmid : j.val < left
    · simpa using hleft.2 ⟨j.val, hmid⟩
    · have hjright : j.val - left < right := by omega
      have hr := hright.2 ⟨j.val - left, hjright⟩
      have hi : start + left + (j.val - left) = start + j.val := by omega
      simpa [hi] using hr

theorem rowsValidAt_of_range {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size : ℕ}
    (h : RowsValidRangeAt symmetryIndex r get size 0 size) :
    RowsValidAt symmetryIndex r get size := by
  intro i
  simpa using h.2 ⟨i.val, i.isLt⟩

theorem valid_imp_not_rupert_ix (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt symmetryIndex r get size)
    (i : ℕ) (hi : i < size) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = symmetryIndex)
    (htubeRadius : tube.r = r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale (get i).root p)
    (hmem : InTriangle (toReal (get i).triangle)
      (normalizedView (get i).root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      exactPolyhedron.hull := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid hscale hmem ⊢
  cases row with
  | split id children root triangle =>
      obtain ⟨child, hchildMem⟩ := mem_split hmem
      obtain ⟨hforward, hchildSize, hchildRoot, hchildTriangle⟩ :=
        hvalid child
      have hchild := valid_imp_not_rupert_ix symmetryIndex r get size
        rowsValid (children child) hchildSize tube htubeSymmetry
        htubeRadius htube hp offset
      rw [hchildRoot, hchildTriangle] at hchild
      exact hchild hscale hchildMem
  | certificate id box =>
      obtain ⟨hboxSymmetry, hboxRadius, hview⟩ := hvalid
      let actual := box.retarget tube.interval tube.chart
      have hactualView : actual.ViewValid :=
        hview.retarget tube.interval tube.chart
      have hmismatch : actual.mismatchRadius ≤ actual.r := by
        have hsym : box.symmetryIndex = tube.symmetryIndex :=
          hboxSymmetry.trans htubeSymmetry.symm
        have hmismatchTube : actual.mismatchRadius ≤ tube.r := by
          simpa [actual, Box.retarget, Box.mismatchRadius,
            Box.mismatchShell, Tube.Valid, Tube.mismatchRadius, Tube.shell,
            AtlasLocalCertificate.Box.mismatchRadius,
            AtlasLocalCertificate.Box.mismatchFrobeniusSqUpper,
            AtlasLocalCertificate.Box.entryAbsUpper,
            AtlasLocalCertificate.Box.mismatchBall,
            AtlasLocalCertificate.Box.variableBalls,
            AtlasLocalCertificate.Box.mismatchQuadratic,
            hsym]
            using htube
        have hr : tube.r ≤ box.r := le_of_eq_of_le htubeRadius hboxRadius
        simpa [actual, Box.retarget] using hmismatchTube.trans hr
      have hactual : actual.Valid :=
        Box.Valid.of_viewValid hactualView hmismatch
      exact actual.valid_imp_not_translated_rupert hactual hp offset
        hscale hmem
  | cut id children root triangle weights =>
      obtain ⟨hw0, hw1, hchildren⟩ := hvalid
      obtain ⟨k, hk, hchildMem⟩ := mem_cut hw0 hw1 hmem
      obtain ⟨hforward, hchildSize, hchildRoot, hchildTriangle⟩ := hchildren k hk
      have hchild := valid_imp_not_rupert_ix symmetryIndex r get size
        rowsValid (children k) hchildSize tube htubeSymmetry
        htubeRadius htube hp offset
      rw [hchildRoot, hchildTriangle] at hchild
      exact hchild hscale hchildMem
termination_by size - i
decreasing_by
  all_goals
    have : id = i := by simpa [Row.id, hrow] using hid
    omega

structure Table where
  symmetryIndex : OrbitIndex
  r : ℚ
  root : Fin 8 := 0
  triangle : AtlasProjectiveView.Triangle ℚ := chamberTriangle
  get : ℕ → Row
  size : ℕ

def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.symmetryIndex table.r table.get table.size ∧
    (table.get 0).root = table.root ∧
    (table.get 0).triangle = table.triangle

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

theorem Table.valid_imp_not_translated_rupert_in_triangle (table : Table)
    (hvalid : table.Valid) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r = table.r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal)
    (hscale : 1 ≤ viewScale table.root p)
    (hmem : InTriangle (toReal table.triangle)
      (normalizedView table.root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      exactPolyhedron.hull := by
  obtain ⟨hnonempty, hrows, hroot, htriangle⟩ := hvalid
  have hchecked := valid_imp_not_rupert_ix table.symmetryIndex table.r
    table.get table.size hrows 0 hnonempty tube htubeSymmetry htubeRadius
    htube hp offset
  rw [hroot, htriangle] at hchecked
  exact hchecked hscale hmem

theorem Table.valid_imp_not_translated_rupert (table : Table)
    (hvalid : table.Valid) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r = table.r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal)
    (hchamber : p.InChamber) (offset : ℝ²)
    (hroot : table.root = 0) (htriangle : table.triangle = chamberTriangle) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      exactPolyhedron.hull := by
  obtain ⟨hscale, hmem⟩ := chamber_mem_triangle p hchamber
  apply table.valid_imp_not_translated_rupert_in_triangle hvalid tube
    htubeSymmetry htubeRadius htube hp
  · simpa [hroot] using hscale
  · simpa [hroot, htriangle] using hmem

end Noperts.Stellated.AtlasProjectiveLocalViewTree

end
