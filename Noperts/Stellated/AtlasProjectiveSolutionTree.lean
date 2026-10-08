module

public import Noperts.Stellated.AtlasProjectiveEdgeCertificate
public import Noperts.Stellated.FlipPrune
public import Noperts.Stellated.AtlasReduction
public import Noperts.Stellated.AtlasLocalCertificate
public import Noperts.Stellated.AtlasProjectiveLocalCertificate
public import Noperts.Stellated.AtlasProjectiveLocalViewTree
public import Noperts.Stellated.AtlasProjectiveGlobalCertificate
public import Noperts.Stellated.AtlasProjectiveMixedGlobalCertificate
public import Noperts.ParallelBool
public import Noperts.Stellated.CornerCoverage

@[expose] public section

/-!
# Mixed Cayley/projective solution trees for the stellated tetrahedron

Only Cayley chart zero is needed: every chart half-turn lies in `T`.  The
relative Cayley box is split along `x,y,z`; the outer view starts in the
chamber triangle and is split by four-way midpoint subdivision.  Besides
geometric certificates, leaves may prune boxes outside the octahedron
`|x|+|y|+|z| ≤ 1` or outside the view-dependent flip cell.
-/

namespace Noperts.Stellated.AtlasProjectiveSolutionTree

open CayleyAtlas AtlasProjectiveView
open Noperts.ProjectiveView

abbrev Interval := AtlasInterval ℚ
abbrev Triangle := AtlasProjectiveView.Triangle ℚ

/-- Shared local-view tables, one per depth-3 chamber subtriangle (or none). -/
abbrev SharedLocalTables := Fin 64 → Option AtlasProjectiveLocalViewTree.Table

def OptionalLocalValid : Option AtlasProjectiveLocalViewTree.Table → Prop
  | none => True
  | some table => table.Valid

instance (table : Option AtlasProjectiveLocalViewTree.Table) :
    Decidable (OptionalLocalValid table) := by
  cases table <;> simp only [OptionalLocalValid] <;> infer_instance

def SharedLocalValid (shared : SharedLocalTables) : Prop :=
  ∀ index, OptionalLocalValid (shared index)

instance (shared : SharedLocalTables) :
    Decidable (SharedLocalValid shared) := by
  unfold SharedLocalValid
  infer_instance

inductive Region where
  | sphere
  | triangle (root : Fin 8) (value : Triangle)
deriving DecidableEq

def Region.Mem : Region → AtlasPose ℝ → Prop
  | .sphere, _ => True
  | .triangle root value, p =>
      1 ≤ viewScale root p ∧
        InTriangle (toReal value) (normalizedView root p)

def NoRupert (chart : ChartIndex) (interval : Interval)
    (region : Region) : Prop :=
  ¬ ∃ p ∈ interval.toReal, p.Reduced ∧
    ∃ offset : ℝ²,
    region.Mem p ∧
      RupertPose (p.matrixPoseWithOffset chart offset)
        exactPolyhedron.hull

theorem _root_.Noperts.Stellated.AtlasPose.Reduced.cayleyBounded
    {p : AtlasPose ℝ} (h : p.Reduced) : p.CayleyBounded := by
  obtain ⟨-, hoct, -⟩ := h
  unfold AtlasPose.InOctahedron at hoct
  unfold AtlasPose.CayleyBounded
  have hx := abs_nonneg p.x
  have hy := abs_nonneg p.y
  have hz := abs_nonneg p.z
  have hsq : p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ (|p.x| + |p.y| + |p.z|) ^ 2 := by
    rw [← sq_abs p.x, ← sq_abs p.y, ← sq_abs p.z]
    nlinarith [mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz]
  have h1 : (|p.x| + |p.y| + |p.z|) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ |p.x| + |p.y| + |p.z| := by linarith
    nlinarith
  linarith

theorem noRupert_halves (chart : ChartIndex) (interval : Interval)
    (region : Region) (coordinate : Fin 5)
    (hlower : NoRupert chart (interval.lowerHalf coordinate) region)
    (hupper : NoRupert chart (interval.upperHalf coordinate) region) :
    NoRupert chart interval region := by
  rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
  rcases AtlasInterval.mem_imp_mem_lowerHalf_or_upperHalf coordinate hp with
    hl | hu
  · exact hlower ⟨p, hl, hred, offset, hregion, hrupert⟩
  · exact hupper ⟨p, hu, hred, offset, hregion, hrupert⟩

def minAbsBound (lo hi : ℚ) : ℚ :=
  if lo ≤ 0 ∧ 0 ≤ hi then 0 else min |lo| |hi|

def Interval.outsideOctahedron (interval : Interval) : Prop :=
  minAbsBound interval.min.x interval.max.x +
    minAbsBound interval.min.y interval.max.y +
    minAbsBound interval.min.z interval.max.z > 1

instance (interval : Interval) : Decidable interval.outsideOctahedron := by
  unfold Interval.outsideOctahedron minAbsBound
  infer_instance

private theorem minAbsBound_le_abs {lo hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    (minAbsBound lo hi : ℚ) ≤ |x| := by
  unfold minAbsBound
  split_ifs with hcross
  · norm_num
  · by_cases hlo : lo ≤ 0
    · have hhi : ¬ 0 ≤ hi := fun hhi => hcross ⟨hlo, hhi⟩
      have hhiQ : hi < 0 := lt_of_not_ge hhi
      have hhiR : (hi : ℝ) < 0 := by exact_mod_cast hhiQ
      have hx0 : x < 0 := hx.2.trans_lt hhiR
      have hmin : min |lo| |hi| ≤ |hi| := min_le_right _ _
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ ((|hi| : ℚ) : ℝ) := by
        exact_mod_cast hmin
      exact hminR.trans (by
        rw [Rat.cast_abs, abs_of_neg hhiR, abs_of_neg hx0]
        linarith [hx.2])
    · have hloQ : 0 < lo := lt_of_not_ge hlo
      have hloR : (0 : ℝ) < lo := by exact_mod_cast hloQ
      have hx0 : 0 < x := hloR.trans_le hx.1
      have hmin : min |lo| |hi| ≤ |lo| := min_le_left _ _
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ ((|lo| : ℚ) : ℝ) := by
        exact_mod_cast hmin
      exact hminR.trans (by
        rw [Rat.cast_abs, abs_of_pos hloR, abs_of_pos hx0]
        exact hx.1)

theorem noRupert_of_outsideOctahedron (chart : ChartIndex)
    (interval : Interval) (region : Region)
    (h : interval.outsideOctahedron) : NoRupert chart interval region := by
  rintro ⟨p, hp, ⟨-, hoct, -⟩, offset, hregion, hrupert⟩
  have hmem := AtlasInterval.mem_toReal_iff.mp hp
  have hx := minAbsBound_le_abs (hmem 2)
  have hy := minAbsBound_le_abs (hmem 3)
  have hz := minAbsBound_le_abs (hmem 4)
  have hout : (1 : ℝ) <
      (minAbsBound interval.min.x interval.max.x : ℚ) +
      (minAbsBound interval.min.y interval.max.y : ℚ) +
      (minAbsBound interval.min.z interval.max.z : ℚ) := by
    exact_mod_cast h
  unfold AtlasPose.InOctahedron at hoct
  simp [AtlasPose.get, AtlasPose.equivPi] at hx hy hz
  linarith

inductive Row where
  | cayleySplit (id lowerChild upperChild : ℕ) (coordinate : Fin 5)
      (interval : Interval) (region : Region)
  | viewRoot (id child : ℕ) (interval : Interval)
  | viewSplit (id : ℕ) (children : Fin 4 → ℕ)
      (interval : Interval) (root : Fin 8) (triangle : Triangle)
  | projective (id : ℕ) (box : AtlasProjectiveEdgeCertificate.Box)
  | projectiveGlobal (id : ℕ)
      (box : AtlasProjectiveGlobalCertificate.Box)
  | projectiveMixedGlobal (id : ℕ)
      (box : AtlasProjectiveMixedGlobalCertificate.Box)
  | symmetryLocal (id : ℕ) (box : AtlasLocalCertificate.Box)
      (region : Region)
  | projectiveLocal (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
  | symmetryTube (id : ℕ) (tube : AtlasProjectiveLocalViewTree.Tube)
      (sharedIndex : Fin 64) (region : Region) (within : Fin 3 → Fin 3 → ℚ)
  | octahedronPrune (id : ℕ) (interval : Interval) (region : Region)
  | flipPrune (id : ℕ) (box : FlipPrune.Box)
  | corner (id : ℕ) (interval : Interval) (triangle : Triangle)
  | viewCut (id : ℕ) (children : Fin 3 → ℕ) (interval : Interval) (root : Fin 8)
      (triangle : Triangle) (weights : Fin 3 → ℚ)

def Row.id : Row → ℕ
  | .cayleySplit id .. | .viewRoot id .. | .viewSplit id .. |
      .projective id .. | .projectiveGlobal id .. |
      .projectiveMixedGlobal id .. |
      .symmetryLocal id .. | .octahedronPrune id .. |
      .flipPrune id .. | .symmetryTube id .. => id
  | .projectiveLocal id .. | .corner id .. | .viewCut id .. => id

def Row.interval : Row → Interval
  | .cayleySplit _ _ _ _ interval _ => interval
  | .viewRoot _ _ interval => interval
  | .viewSplit _ _ interval _ _ => interval
  | .projective _ box => box.interval
  | .projectiveGlobal _ box => box.interval
  | .projectiveMixedGlobal _ box => box.interval
  | .symmetryLocal _ box _ => box.interval
  | .projectiveLocal _ box => box.interval
  | .symmetryTube _ tube _ _ _ => tube.interval
  | .octahedronPrune _ interval _ => interval
  | .flipPrune _ box => box.interval
  | .corner _ interval _ => interval
  | .viewCut _ _ interval _ _ _ => interval

def Row.region : Row → Region
  | .cayleySplit _ _ _ _ _ region => region
  | .viewRoot .. => .sphere
  | .viewSplit _ _ _ root triangle => .triangle root triangle
  | .projective _ box => .triangle box.root box.triangle
  | .projectiveGlobal _ box => .triangle box.root box.triangle
  | .projectiveMixedGlobal _ box => .triangle box.root box.triangle
  | .symmetryLocal _ _ region => region
  | .projectiveLocal _ box => .triangle box.root box.triangle
  | .symmetryTube _ _ _ region _ => region
  | .octahedronPrune _ _ region => region
  | .flipPrune _ box => .triangle 0 box.triangle
  | .corner _ _ triangle => .triangle 0 triangle
  | .viewCut _ _ _ root triangle _ => .triangle root triangle

instance : Inhabited Row where
  default := .viewRoot 0 0 (AtlasPose.rootInterval ℚ)

/-- `weights i` expresses corner `i` of `small` as a convex combination of the
corners of `big`. -/
def TriangleWithin (small big : Triangle) (weights : Fin 3 → Fin 3 → ℚ) :
    Prop :=
  ∀ i, (∀ j, 0 ≤ weights i j) ∧ ∑ j, weights i j = 1 ∧
    ∀ c, small i c = ∑ j, weights i j * big j c

instance (small big : Triangle) (weights : Fin 3 → Fin 3 → ℚ) :
    Decidable (TriangleWithin small big weights) := by
  unfold TriangleWithin
  infer_instance

theorem inTriangle_of_within {small big : Triangle}
    {weights : Fin 3 → Fin 3 → ℚ} (h : TriangleWithin small big weights)
    {point : AtlasProjectiveView.Vector ℝ}
    (hmem : InTriangle (toReal small) point) :
    InTriangle (toReal big) point := by
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := hmem
  refine ⟨fun j => ∑ i, μ i * (weights i j : ℝ), ?_, ?_, ?_⟩
  · intro j
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hμ0 i) (by exact_mod_cast (h i).1 j)
  · rw [Finset.sum_comm]
    calc ∑ i, ∑ j, μ i * (weights i j : ℝ) = ∑ i, μ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          have : (∑ j, (weights i j : ℝ)) = 1 := by exact_mod_cast (h i).2.1
          rw [this, mul_one]
      _ = 1 := hμ1
  · funext c
    simp only [affinePoint, toReal]
    have hc : ∀ i, (small i c : ℝ) = ∑ j, (weights i j : ℝ) * big j c := by
      intro i; exact_mod_cast (h i).2.2 c
    simp only [hc, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring

def SymmetryTubeMatches (tube : AtlasProjectiveLocalViewTree.Tube)
    (region : Region) (within : Fin 3 → Fin 3 → ℚ) :
    Option AtlasProjectiveLocalViewTree.Table → Prop
  | none => False
  | some table =>
      tube.symmetryIndex = table.symmetryIndex ∧ tube.r = table.r ∧
        match region with
        | .sphere => False
        | .triangle root triangle =>
            root = table.root ∧ TriangleWithin triangle table.triangle within

instance (tube : AtlasProjectiveLocalViewTree.Tube) (region : Region)
    (within : Fin 3 → Fin 3 → ℚ)
    (table : Option AtlasProjectiveLocalViewTree.Table) :
    Decidable (SymmetryTubeMatches tube region within table) := by
  cases table <;> cases region <;> simp only [SymmetryTubeMatches] <;>
    infer_instance

/-- The blow-up scale of the corner charts. -/
def cornerEps : ℚ := 3 / 16

/-- The corner claim covers the box: views with `0 ≤ w₀ - w₁, 2 w₂ ≤ ε₀` and
`|x|, |y|, |z| ≤ ε₀`. -/
def CornerOk (interval : Interval) (triangle : Triangle) : Prop :=
  (∀ k : Fin 3, 0 ≤ triangle k 0 - triangle k 1 ∧
      triangle k 0 - triangle k 1 ≤ cornerEps ∧
      0 ≤ 2 * triangle k 2 ∧ 2 * triangle k 2 ≤ cornerEps) ∧
    ∀ i : Fin 5, 2 ≤ i.val →
      -cornerEps ≤ interval.min.get i ∧ interval.max.get i ≤ cornerEps

instance (interval : Interval) (triangle : Triangle) :
    Decidable (CornerOk interval triangle) := by
  unfold CornerOk; infer_instance

/-- The corner charts cover the corner claim at `cornerEps`. -/
def CornerCovered : Prop :=
  (∀ seg face, CornerTree.Covered (CornerHandoff.plainRoot cornerEps seg face)) ∧
    ∀ face, CornerTree.Covered (CornerHandoff.zeroRoot cornerEps face)

theorem noRupert_of_cornerOk (hcorner : CornerCovered) (interval : Interval)
    (triangle : Triangle) (hok : CornerOk interval triangle) :
    NoRupert 0 interval (.triangle 0 triangle) := by
  rintro ⟨p, hp, hred, offset, ⟨hscale, hmem⟩, hrupert⟩
  obtain ⟨hview, hbox⟩ := hok
  rw [AtlasInterval.mem_toReal_iff] at hp
  have hcoord : ∀ i : Fin 5, 2 ≤ i.val → |p.get i| ≤ cornerEps := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hbox i hi
    obtain ⟨h1, h2⟩ := hp i
    have hlo' : ((-cornerEps : ℚ) : ℝ) ≤ interval.min.get i := by exact_mod_cast hlo
    have hhi' : (interval.max.get i : ℝ) ≤ cornerEps := by exact_mod_cast hhi
    push_cast at hlo'
    rw [abs_le]; constructor <;> linarith
  have hx := hcoord 2 (by decide)
  have hy := hcoord 3 (by decide)
  have hz := hcoord 4 (by decide)
  simp only [AtlasPose.get_two, AtlasPose.get_three, AtlasPose.get_four] at hx hy hz
  have lin : ∀ (a : AtlasProjectiveView.Vector ℝ) (bound : ℝ),
      (∀ k, linearValue (toReal triangle k) a ≤ bound) →
      linearValue (normalizedView 0 p) a ≤ bound :=
    fun a bound h => linearValue_le_of_mem hmem h
  have e0 : (0 : ℝ) ≤ cornerEps := by norm_num [cornerEps]
  have hS1 := lin ![1, -1, 0] cornerEps (fun k => by
    have := (hview k).2.1
    have : ((triangle k 0 - triangle k 1 : ℚ) : ℝ) ≤ cornerEps := by exact_mod_cast this
    simp [linearValue, toReal]; push_cast at this; linarith)
  have hS0 := lin ![-1, 1, 0] 0 (fun k => by
    have := (hview k).1
    have : (0 : ℝ) ≤ ((triangle k 0 - triangle k 1 : ℚ) : ℝ) := by exact_mod_cast this
    simp [linearValue, toReal]; push_cast at this; linarith)
  have hT1 := lin ![0, 0, 2] cornerEps (fun k => by
    have := (hview k).2.2.2
    have : ((2 * triangle k 2 : ℚ) : ℝ) ≤ cornerEps := by exact_mod_cast this
    simp [linearValue, toReal]; push_cast at this; linarith)
  have hT0 := lin ![0, 0, -2] 0 (fun k => by
    have := (hview k).2.2.1
    have : (0 : ℝ) ≤ ((2 * triangle k 2 : ℚ) : ℝ) := by exact_mod_cast this
    simp [linearValue, toReal]; push_cast at this; linarith)
  simp [linearValue] at hS1 hS0 hT1 hT0
  apply CornerCoverage.corner_not_rupert cornerEps hcorner.1 hcorner.2 p hred.2.2 hscale
    (by linarith) (by linarith) (by linarith) (by linarith) ?_ ?_ hz offset hrupert
  · rw [abs_le] at hx hy ⊢; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · rw [abs_le] at hx hy ⊢; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

def Row.ValidAt (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables) : Row → Prop
  | .cayleySplit id lowerChild upperChild coordinate interval region =>
      id < lowerChild ∧ id < upperChild ∧
      lowerChild < size ∧ upperChild < size ∧
      (get lowerChild).interval = interval.lowerHalf coordinate ∧
      (get upperChild).interval = interval.upperHalf coordinate ∧
      (get lowerChild).region = region ∧
      (get upperChild).region = region
  | .viewRoot id child interval =>
      id < child ∧ child < size ∧
      (get child).interval = interval ∧
      (get child).region = .triangle 0 chamberTriangle
  | .viewSplit id children interval root triangle => ∀ child,
      id < children child ∧ children child < size ∧
      (get (children child)).interval = interval ∧
      (get (children child)).region =
        .triangle root (split triangle child)
  | .projective _ box => box.chart = chart ∧ box.Valid
  | .projectiveGlobal _ box => box.chart = chart ∧ box.Valid
  | .projectiveMixedGlobal _ box => box.chart = chart ∧ box.Valid
  | .symmetryLocal _ box _ => box.chart = chart ∧ box.Valid
  | .projectiveLocal _ box => box.chart = chart ∧ box.Valid
  | .symmetryTube _ tube sharedIndex region within =>
      tube.chart = chart ∧ tube.Valid ∧
        SymmetryTubeMatches tube region within (shared sharedIndex)
  | .octahedronPrune _ interval _ => interval.outsideOctahedron
  | .flipPrune _ box => chart = 0 ∧ box.Valid
  | .corner _ interval triangle => chart = 0 ∧ CornerOk interval triangle
  | .viewCut id children interval root triangle weights =>
      (∀ j, 0 ≤ weights j) ∧ weights 0 + weights 1 + weights 2 = 1 ∧
      ∀ k, 0 < weights k →
        id < children k ∧ children k < size ∧
        (get (children k)).interval = interval ∧
        (get (children k)).region = .triangle root
          (AtlasProjectiveLocalViewTree.cutTriangle triangle weights k)

instance (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) (row : Row) :
    Decidable (row.ValidAt chart get size shared) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables) : Prop :=
  ∀ i : Fin size,
    (get i).id = i ∧ (get i).ValidAt chart get size shared

instance (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) :
    Decidable (RowsValidAt chart get size shared) := by
  unfold RowsValidAt
  infer_instance

/-- A kernel-checkable slice of `RowsValidAt`.  Generated tables prove small
slices independently and join them with `rowsValidRange_append`, avoiding one
enormous reduction in the kernel evaluator. -/
def RowsValidRangeAt (chart : ChartIndex) (get : ℕ → Row) (size start count : ℕ)
    (shared : SharedLocalTables) :
    Prop :=
  start + count ≤ size ∧ ∀ j : Fin count,
    (get (start + j.val)).id = start + j.val ∧
      (get (start + j.val)).ValidAt chart get size shared

instance (chart : ChartIndex) (get : ℕ → Row) (size start count : ℕ)
    (shared : SharedLocalTables) :
    Decidable (RowsValidRangeAt chart get size start count shared) := by
  unfold RowsValidRangeAt
  infer_instance

theorem rowsValidRange_append {chart : ChartIndex} {get : ℕ → Row}
    {size start left right : ℕ}
    {shared : SharedLocalTables}
    (hleft : RowsValidRangeAt chart get size start left shared)
    (hright : RowsValidRangeAt chart get size (start + left) right shared) :
    RowsValidRangeAt chart get size start (left + right) shared := by
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

theorem rowsValidAt_of_range {chart : ChartIndex} {get : ℕ → Row} {size : ℕ}
    {shared : SharedLocalTables}
    (h : RowsValidRangeAt chart get size 0 size shared) :
    RowsValidAt chart get size shared := by
  intro i
  simpa using h.2 ⟨i.val, i.isLt⟩

theorem valid_imp_noRupert_ix (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables)
    (sharedValid : SharedLocalValid shared) (hcorner : CornerCovered)
    (rowsValid : RowsValidAt chart get size shared)
    (i : ℕ) (hi : i < size) :
    NoRupert chart (get i).interval (get i).region := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid ⊢
  cases row with
  | projective id box =>
      unfold NoRupert
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      have hbounded := hred.cayleyBounded
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox hp hbounded offset
        hregion.1 hregion.2 hrupert
  | projectiveGlobal id box =>
      unfold NoRupert
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      have hbounded := hred.cayleyBounded
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox p hp hbounded
        hregion.1 hregion.2 offset hrupert
  | projectiveMixedGlobal id box =>
      unfold NoRupert
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      have hbounded := hred.cayleyBounded
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox p hp hbounded
        hregion.1 hregion.2 offset hrupert
  | symmetryLocal id box region =>
      unfold NoRupert
      rintro ⟨p, hp, -, offset, -, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox p hp offset hrupert
  | projectiveLocal id box =>
      unfold NoRupert
      rintro ⟨p, hp, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox hp offset
        hregion.1 hregion.2 hrupert
  | symmetryTube id tube sharedIndex region within =>
      unfold NoRupert
      rintro ⟨p, hp, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, htube, hmatch⟩ := hvalid
      subst hchart
      cases hshared : shared sharedIndex with
      | none =>
          have : False := by
            simp [SymmetryTubeMatches, hshared] at hmatch
          contradiction
      | some table =>
          have htable : table.Valid := by
            simpa [OptionalLocalValid, hshared] using sharedValid sharedIndex
          rw [hshared] at hmatch
          obtain ⟨hsymmetry, hradius, hregionMatch⟩ := hmatch
          cases region with
          | sphere => exact hregionMatch.elim
          | triangle root triangle =>
              obtain ⟨hroot, hwithin⟩ := hregionMatch
              obtain ⟨hscale, hmem⟩ := hregion
              subst hroot
              exact table.valid_imp_not_translated_rupert_in_triangle htable
                tube hsymmetry hradius htube hp hscale
                (inTriangle_of_within hwithin hmem) offset hrupert
  | cayleySplit id lowerChild upperChild coordinate interval region =>
      obtain ⟨hlower, hupper, hlowerSize, hupperSize,
        hlowerInterval, hupperInterval, hlowerRegion, hupperRegion⟩ := hvalid
      apply noRupert_halves chart interval region coordinate
      · rw [← hlowerInterval, ← hlowerRegion]
        exact valid_imp_noRupert_ix chart get size shared sharedValid hcorner rowsValid
          lowerChild hlowerSize
      · rw [← hupperInterval, ← hupperRegion]
        exact valid_imp_noRupert_ix chart get size shared sharedValid hcorner rowsValid
          upperChild hupperSize
  | viewRoot id child interval =>
      unfold NoRupert
      rintro ⟨p, hp, hred, offset, -, hrupert⟩
      obtain ⟨hscale, hmem⟩ := chamber_mem_triangle p hred.1
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ := hvalid
      have hchild := valid_imp_noRupert_ix chart get size shared sharedValid hcorner rowsValid
        child hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, hred, offset, ⟨hscale, hmem⟩, hrupert⟩
  | viewSplit id children interval root triangle =>
      unfold NoRupert
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      obtain ⟨child, hchildMem⟩ := mem_split hregion.2
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ :=
        hvalid child
      have hchild := valid_imp_noRupert_ix chart get size shared sharedValid hcorner rowsValid
        (children child) hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, hred, offset, ⟨hregion.1, hchildMem⟩, hrupert⟩
  | octahedronPrune id interval region =>
      exact noRupert_of_outsideOctahedron chart interval region hvalid
  | flipPrune id box =>
      unfold NoRupert
      rintro ⟨p, hp, hred, offset, hregion, -⟩
      exact box.valid_not_flipReduced hvalid.2 hp hregion.1 hregion.2 hred.2.2
  | viewCut id children interval root triangle weights =>
      unfold NoRupert
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      obtain ⟨hw0, hw1, hchildren⟩ := hvalid
      obtain ⟨k, hk, hchildMem⟩ :=
        AtlasProjectiveLocalViewTree.mem_cut hw0 hw1 hregion.2
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ := hchildren k hk
      have hchild := valid_imp_noRupert_ix chart get size shared sharedValid hcorner
        rowsValid (children k) hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, hred, offset, ⟨hregion.1, hchildMem⟩, hrupert⟩
  | corner id interval triangle =>
      obtain ⟨hchart, hok⟩ := hvalid
      subst hchart
      exact noRupert_of_cornerOk hcorner interval triangle hok
termination_by size - i
decreasing_by
  all_goals
    have : id = i := by simpa [Row.id, hrow] using hid
    omega

structure Table where
  chart : ChartIndex
  get : ℕ → Row
  size : ℕ
  sharedLocal : SharedLocalTables := fun _ => none

def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.chart table.get table.size table.sharedLocal ∧
    (table.get 0).interval = AtlasPose.rootInterval ℚ ∧
    (table.get 0).region = .sphere ∧
    SharedLocalValid table.sharedLocal

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

/-! ## Parallel executable checker -/

/-- One global-tree row check as a Boolean, vacuously true past `size`. -/
def validIxAtB (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) (i : ℕ) : Bool :=
  if i < size then
    decide ((get i).id = i ∧ (get i).ValidAt chart get size shared)
  else true

theorem validIxAtB_eq_true_iff (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables) (i : ℕ) :
    validIxAtB chart get size shared i = true ↔
      (i < size → (get i).id = i ∧
        (get i).ValidAt chart get size shared) := by
  unfold validIxAtB
  split
  · rename_i h
    rw [decide_eq_true_iff]
    exact ⟨fun hv _ => hv, fun hv => hv h⟩
  · rename_i h
    simp only [true_iff]
    exact fun h' => absurd h' h

/-- Native parallel Boolean check of every row in a global chart table. -/
def rowsValidAtParB (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) (taskCount : ℕ) : Bool :=
  Noperts.ParallelBool.allParB
    (validIxAtB chart get size shared) size taskCount

theorem rowsValidAt_of_parB {chart : ChartIndex} {get : ℕ → Row}
    {size : ℕ} {shared : SharedLocalTables} {taskCount : ℕ}
    (h : rowsValidAtParB chart get size shared taskCount = true) :
    RowsValidAt chart get size shared := by
  intro i
  have hindex := Noperts.ParallelBool.all_of_parB h i.val i.isLt
  rw [validIxAtB_eq_true_iff] at hindex
  exact hindex i.isLt

/-- Check the computational portion of `Table.Valid`.  Validity of shared
local tables is supplied separately, so chart 0 does not recompute them. -/
def tableCoreValidParB (table : Table) (taskCount : ℕ) : Bool :=
  decide (0 < table.size ∧
    (table.get 0).interval = AtlasPose.rootInterval ℚ ∧
    (table.get 0).region = .sphere) &&
  rowsValidAtParB table.chart table.get table.size table.sharedLocal taskCount

/-- The native row tasks used by `tableCoreValidParB`, exposed for executable
progress reporting. -/
def tableCoreTasks (table : Table) (taskCount : ℕ) : List (Task Bool) :=
  let chunkSize := table.size / taskCount + 1
  Noperts.ParallelBool.chunkTasks
    (validIxAtB table.chart table.get table.size table.sharedLocal)
    taskCount chunkSize

/-- The global table checker supplied with its already spawned task list. -/
def tableCoreValidWithTasksB (table : Table) (taskCount : ℕ)
    (tasks : List (Task Bool)) : Bool :=
  let chunkSize := table.size / taskCount + 1
  decide (0 < table.size ∧
    (table.get 0).interval = AtlasPose.rootInterval ℚ ∧
    (table.get 0).region = .sphere) &&
  Noperts.ParallelBool.allWithTasksB table.size taskCount chunkSize tasks

theorem Table.Valid.of_parB {table : Table} {taskCount : ℕ}
    (hshared : SharedLocalValid table.sharedLocal)
    (h : tableCoreValidParB table taskCount = true) : table.Valid := by
  unfold tableCoreValidParB at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  exact ⟨h.1.1, rowsValidAt_of_parB h.2, h.1.2.1, h.1.2.2, hshared⟩

theorem Table.Valid.of_withTasksB {table : Table} {taskCount : ℕ}
    (hshared : SharedLocalValid table.sharedLocal)
    (h : tableCoreValidWithTasksB table taskCount
      (tableCoreTasks table taskCount) = true) : table.Valid := by
  apply Table.Valid.of_parB hshared
  exact h

theorem Table.valid_imp_no_reduced_pose
    (table : Table) (h : table.Valid) (hcorner : CornerCovered) :
    ¬ ∃ p ∈ AtlasPose.rootInterval ℝ, p.Reduced ∧ ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset table.chart offset)
        exactPolyhedron.hull := by
  obtain ⟨hnonempty, hrows, hrootInterval, hrootRegion, hshared⟩ := h
  have hchecked := valid_imp_noRupert_ix table.chart table.get table.size
    table.sharedLocal hshared hcorner hrows 0 hnonempty
  rw [hrootInterval, hrootRegion] at hchecked
  rintro ⟨p, hp, hred, offset, hrupert⟩
  exact hchecked ⟨p, by rwa [AtlasInterval.rootInterval_toReal], hred, offset,
    trivial, hrupert⟩

/-- A valid chart-zero table excludes every matrix pose. -/
theorem no_matrixPose_of_valid_table (table : Table)
    (hchart : table.chart = 0) (hvalid : table.Valid) (hcorner : CornerCovered) :
    ¬ ∃ p : MatrixPose, RupertPose p exactPolyhedron.hull := by
  rintro ⟨p, hrupert⟩
  obtain ⟨p', hred, hrupert'⟩ := exists_reduced_rupert p hrupert
  obtain ⟨q, hq, hqred, offset, hqrupert⟩ :=
    exists_reduced_atlas_pose p' hred hrupert'
  have hno := table.valid_imp_no_reduced_pose hvalid hcorner
  rw [hchart] at hno
  exact hno ⟨q, hq, hqred, offset, hqrupert⟩

/-- Exclusion on the whole chart-zero root box (sphere region) excludes every
matrix pose. -/
theorem no_matrixPose_of_root (h : NoRupert 0 (AtlasPose.rootInterval ℚ) .sphere) :
    ¬ ∃ p : MatrixPose, RupertPose p exactPolyhedron.hull := by
  rintro ⟨p, hrupert⟩
  obtain ⟨p', hred, hrupert'⟩ := exists_reduced_rupert p hrupert
  obtain ⟨q, hq, hqred, offset, hqrupert⟩ :=
    exists_reduced_atlas_pose p' hred hrupert'
  exact h ⟨q, by rwa [AtlasInterval.rootInterval_toReal], hqred, offset, trivial, hqrupert⟩

end Noperts.Stellated.AtlasProjectiveSolutionTree

end
