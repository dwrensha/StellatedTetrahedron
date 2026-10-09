module

public import Noperts.Stellated.AtlasProjectiveSolutionTree
public import Noperts.Stellated.ChartKernelEdgeSound
public import Noperts.Stellated.ChartKernelGlobalSound
public import Noperts.Stellated.ChartKernelMixedSound
public import Noperts.Stellated.LocalKernelSound
public import Noperts.Stellated.ChartKernelFastEdge
public import Noperts.Stellated.ChartKernelFastMixed
public import Noperts.Stellated.LocalKernelFast

@[expose] public section

/-!
# A recursive chart tree for the kernel

`AtlasProjectiveSolutionTree` stores the chart tree as a table of rows that
carry their own interval and region, linked by row ids.  For `decide +kernel`
the same tree is better presented recursively: the checker passes the current
interval and region down, so split nodes cost only the halving of one
coordinate (or the subdivision of the view triangle), and leaves carry only
the certificate data that is not implied by their position.  Leaves are
checked by the integer kernel checkers (`validEdgeK`, `validGlobalK`,
`validMixedK`, `viewValidN`) with generator-supplied hints.

`CTree.hole iv reg` marks a subtree proved elsewhere; `CTree.check_sound`
takes the coverage of all holes as a hypothesis, so large trees are checked
in independent chunks.
-/

namespace Noperts.Stellated.ChartKernelTree

open CayleyAtlas AtlasProjectiveView AtlasProjectiveSolutionTree
open Noperts.ProjectiveView

/-- The data of a projective edge leaf not implied by its position. -/
structure EdgeRest where
  edgePred : ℕ
  outerIndex : Fin (edgePred + 1) → VertexIndex
  innerIndex : Fin (edgePred + 1) → VertexIndex
  nonzeroWitness : Fin (edgePred + 1) → VertexIndex
  ballMultiplier : Fin 3 → ℚ

def EdgeRest.box (e : EdgeRest) (iv : Interval) (root : Fin 8) (tri : Triangle)
    (ch : ChartIndex) : AtlasProjectiveEdgeCertificate.Box :=
  ⟨iv, root, tri, ch, e.edgePred, e.outerIndex, e.innerIndex, e.nonzeroWitness,
    e.ballMultiplier⟩

structure GlobalRest where
  certificate : AtlasProjectiveLocalCertificate.AxisCertificate
  innerIndex : Fin 3 → VertexIndex
  ballMultiplier : ℚ

def GlobalRest.box (g : GlobalRest) (iv : Interval) (root : Fin 8) (tri : Triangle)
    (ch : ChartIndex) : AtlasProjectiveGlobalCertificate.Box :=
  ⟨iv, root, tri, ch, g.certificate, g.innerIndex, g.ballMultiplier⟩

structure MixedRest where
  component : Fin 4 → AtlasProjectiveMixedGlobalCertificate.Component
  weight : Fin 4 → ℚ

def MixedRest.box (m : MixedRest) (iv : Interval) (root : Fin 8) (tri : Triangle)
    (ch : ChartIndex) : AtlasProjectiveMixedGlobalCertificate.Box :=
  ⟨iv, root, tri, ch, m.component, m.weight⟩

structure LocalRest where
  symmetryIndex : OrbitIndex
  certificate : Fin 4 → AtlasProjectiveLocalCertificate.AxisCertificate
  c : ℚ
  δ : ℚ
  r : ℚ

def LocalRest.box (l : LocalRest) (iv : Interval) (root : Fin 8) (tri : Triangle)
    (ch : ChartIndex) : AtlasProjectiveLocalCertificate.Box :=
  ⟨iv, root, tri, ch, l.symmetryIndex, l.certificate, l.c, l.δ, l.r⟩

/-! ## Paths from the root -/

/-- One step from a node to a child. -/
inductive Step where
  | half (coordinate : Fin 5) (upper : Bool)
  | root
  | view (k : Fin 4)
  | cut (weights : Fin 3 → ℚ) (k : Fin 3)

/-- The triangle with rows `a, b, c`. -/
def tri3K (a b c : Noperts.ProjectiveView.Vector ℚ) : Noperts.ProjectiveView.Triangle ℚ :=
  fun i => match i with | 0 => a | 1 => b | 2 => c

/-- `split tri k`, with the children's rows from shared midpoints (no `![…]` lookups). -/
def splitK (t : Noperts.ProjectiveView.Triangle ℚ) (k : Fin 4) : Noperts.ProjectiveView.Triangle ℚ :=
  let m01 := Noperts.ProjectiveView.midpoint (t 0) (t 1)
  let m02 := Noperts.ProjectiveView.midpoint (t 0) (t 2)
  let m12 := Noperts.ProjectiveView.midpoint (t 1) (t 2)
  match k with
  | 0 => tri3K (t 0) m01 m02
  | 1 => tri3K m01 (t 1) m12
  | 2 => tri3K m02 m12 (t 2)
  | 3 => tri3K m01 m12 (Noperts.ProjectiveView.midpoint (t 2) (t 0))

theorem splitK_eq (t : Noperts.ProjectiveView.Triangle ℚ) (k : Fin 4) : splitK t k = split t k := by
  funext i
  fin_cases k <;> fin_cases i <;> rfl

def Step.apply : Step → Interval × Region → Interval × Region
  | .half c false, (iv, reg) => (iv.lowerHalf c, reg)
  | .half c true, (iv, reg) => (iv.upperHalf c, reg)
  | .root, (iv, _) => (iv, .triangle 0 chamberTriangle)
  | .view k, (iv, .triangle r t) => (iv, .triangle r (splitK t k))
  | .cut w k, (iv, .triangle r t) =>
      (iv, .triangle r (AtlasProjectiveLocalViewTree.cutTriangle t w k))
  | _, f => f

/-- The frame reached from the chart-zero root box along `steps`. -/
def framePath (steps : List Step) : Interval × Region :=
  steps.foldl (fun f s => s.apply f) (AtlasPose.rootInterval ℚ, .sphere)

/-- The header of a shared local table (what tube leaves match against). -/
structure Header where
  symmetryIndex : OrbitIndex
  r : ℚ
  root : Fin 8
  triangle : Triangle
deriving DecidableEq

/-- What a valid shared local table with header `h` provides: no valid tube
with its symmetry index and radius has a Rupert pose whose view lies in the
header's triangle. -/
def LocalCovered (h : Header) : Prop :=
  ∀ tube : AtlasProjectiveLocalViewTree.Tube, tube.symmetryIndex = h.symmetryIndex →
    tube.r = h.r → tube.Valid → ∀ {p : AtlasPose ℝ}, p ∈ tube.interval.toReal →
      1 ≤ viewScale h.root p → InTriangle (toReal h.triangle) (normalizedView h.root p) →
        ∀ offset : ℝ², ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
          exactPolyhedron.hull

/-- Every header in `hdr` is covered. -/
def HeadersCovered (hdr : Fin 64 → Option Header) : Prop :=
  ∀ idx h, hdr idx = some h → LocalCovered h

theorem localCovered_of_table (table : AtlasProjectiveLocalViewTree.Table)
    (hvalid : table.Valid) :
    LocalCovered ⟨table.symmetryIndex, table.r, table.root, table.triangle⟩ :=
  fun tube hs hr htube _ hp hscale hmem offset =>
    table.valid_imp_not_translated_rupert_in_triangle hvalid tube hs hr htube hp hscale hmem
      offset

inductive CTree where
  | cayleySplit (coordinate : Fin 5) (lower upper : CTree)
  | viewRoot (child : CTree)
  | viewSplit (c0 c1 c2 c3 : CTree)
  | viewCut (weights : Fin 3 → ℚ) (c0 c1 c2 : CTree)
  | projective (rest : EdgeRest) (hints : List ℤ)
  | global (rest : GlobalRest) (hints : List ℤ)
  | mixed (rest : MixedRest) (hints : List ℤ)
  | projectiveLocal (rest : LocalRest)
  | tube (symmetryIndex : OrbitIndex) (r : ℚ) (sharedIndex : Fin 64)
      (within : Fin 3 → Fin 3 → ℚ)
  | octahedron
  | flip (form : Fin 12) (negate : Bool)
  | corner
  | hole (steps : List Step)

def viewChild (k : Fin 4) (c0 c1 c2 c3 : CTree) : CTree :=
  match k with
  | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3

def cutChild (k : Fin 3) (c0 c1 c2 : CTree) : CTree :=
  match k with
  | 0 => c0 | 1 => c1 | 2 => c2

/-- The leaf condition at a triangle region. -/
def leafOk (hdr : Fin 64 → Option Header) (ch : ChartIndex) (iv : Interval) (root : Fin 8)
    (tri : Triangle) : CTree → Bool
  | .projective e h => ChartKernelF.edgeZ (e.box iv root tri ch)
      (e.box ChartKernelF.iv₀ 0 chamberTriangle ch) h
  | .global g h => ChartKernelF.globalZ (g.box iv root tri ch)
      (g.box ChartKernelF.iv₀ 0 chamberTriangle ch) h
  | .mixed m h => ChartKernelF.mixedZ (m.box iv root tri ch)
      (m.box ChartKernelF.iv₀ 0 chamberTriangle ch) h
  | .projectiveLocal l =>
      LocalKernel.viewValidZ (l.box iv root tri ch) &&
        decide ((l.box iv root tri ch).mismatchRadius ≤ (l.box iv root tri ch).r)
  | .tube s r idx within =>
      match hdr idx with
      | some h => decide ((⟨iv, ch, s, r⟩ : AtlasProjectiveLocalViewTree.Tube).Valid ∧
          s = h.symmetryIndex ∧ r = h.r ∧ root = h.root ∧ TriangleWithin tri h.triangle within)
      | none => false
  | .flip form negate =>
      decide (ch = 0 ∧ root = 0 ∧ (⟨iv, tri, form, negate⟩ : FlipPrune.Box).Valid)
  | .corner => decide (ch = 0 ∧ root = 0 ∧ CornerOk iv tri)
  | _ => false

def CTree.check (hdr : Fin 64 → Option Header) (ch : ChartIndex) :
    Interval → Region → CTree → Bool
  | iv, reg, .cayleySplit c lo hi =>
      CTree.check hdr ch (iv.lowerHalf c) reg lo && CTree.check hdr ch (iv.upperHalf c) reg hi
  | iv, _, .viewRoot child => CTree.check hdr ch iv (.triangle 0 chamberTriangle) child
  | iv, .triangle root tri, .viewSplit c0 c1 c2 c3 =>
      CTree.check hdr ch iv (.triangle root (splitK tri 0)) c0 &&
      CTree.check hdr ch iv (.triangle root (splitK tri 1)) c1 &&
      CTree.check hdr ch iv (.triangle root (splitK tri 2)) c2 &&
      CTree.check hdr ch iv (.triangle root (splitK tri 3)) c3
  | iv, .triangle root tri, .viewCut w c0 c1 c2 =>
      decide ((∀ j, 0 ≤ w j) ∧ w 0 + w 1 + w 2 = 1) &&
      (!decide (0 < w 0) ||
        CTree.check hdr ch iv
          (.triangle root (AtlasProjectiveLocalViewTree.cutTriangle tri w 0)) c0) &&
      (!decide (0 < w 1) ||
        CTree.check hdr ch iv
          (.triangle root (AtlasProjectiveLocalViewTree.cutTriangle tri w 1)) c1) &&
      (!decide (0 < w 2) ||
        CTree.check hdr ch iv
          (.triangle root (AtlasProjectiveLocalViewTree.cutTriangle tri w 2)) c2)
  | iv, _, .octahedron => decide iv.outsideOctahedron
  | iv, reg, .hole steps => decide (framePath steps = (iv, reg))
  | iv, .triangle root tri, t => leafOk hdr ch iv root tri t
  | _, .sphere, _ => false

def CTree.holes : CTree → List (List Step)
  | .cayleySplit _ lo hi => lo.holes ++ hi.holes
  | .viewRoot child => child.holes
  | .viewSplit c0 c1 c2 c3 => c0.holes ++ c1.holes ++ c2.holes ++ c3.holes
  | .viewCut _ c0 c1 c2 => c0.holes ++ c1.holes ++ c2.holes
  | .hole steps => [steps]
  | _ => []

/-! ## Soundness -/

theorem leafOk_sound (hdr : Fin 64 → Option Header) (hhdr : HeadersCovered hdr)
    (hcorner : CornerCovered) (ch : ChartIndex) (iv : Interval) (root : Fin 8) (tri : Triangle)
    (t : CTree) (h : leafOk hdr ch iv root tri t = true) :
    NoRupert ch iv (.triangle root tri) := by
  cases t with
  | projective e hints =>
      have hbox := ChartKernelF.edgeZ_sound _ _ _ rfl h
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      exact (e.box iv root tri ch).valid_imp_not_translated_rupert hbox hp hred.cayleyBounded
        offset hregion.1 hregion.2 hrupert
  | global g hints =>
      have hbox := ChartKernelF.globalZ_sound _ _ _ rfl rfl rfl h
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      exact (g.box iv root tri ch).valid_imp_not_translated_rupert hbox p hp hred.cayleyBounded
        hregion.1 hregion.2 offset hrupert
  | mixed m hints =>
      have hbox := ChartKernelF.mixedZ_sound _ _ _ rfl rfl h
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      exact (m.box iv root tri ch).valid_imp_not_translated_rupert hbox p hp hred.cayleyBounded
        hregion.1 hregion.2 offset hrupert
  | projectiveLocal l =>
      simp only [leafOk, Bool.and_eq_true, decide_eq_true_eq] at h
      have hbox := AtlasProjectiveLocalCertificate.Box.Valid.of_viewValid
        (LocalKernel.viewValidZ_sound _ h.1) h.2
      rintro ⟨p, hp, -, offset, hregion, hrupert⟩
      exact (l.box iv root tri ch).valid_imp_not_translated_rupert hbox hp offset
        hregion.1 hregion.2 hrupert
  | tube s r idx within =>
      simp only [leafOk] at h
      cases hh : hdr idx with
      | none => simp [hh] at h
      | some hd =>
          simp only [hh, decide_eq_true_eq] at h
          obtain ⟨htube, hs, hr, hroot, hwithin⟩ := h
          rintro ⟨p, hp, -, offset, hregion, hrupert⟩
          obtain ⟨hscale, hmem⟩ := hregion
          rw [hroot] at hscale hmem
          exact hhdr idx hd hh ⟨iv, ch, s, r⟩ hs hr htube hp hscale
            (inTriangle_of_within hwithin hmem) offset hrupert
  | flip form negate =>
      simp only [leafOk, decide_eq_true_eq] at h
      obtain ⟨hch, hroot, hvalid⟩ := h
      subst hroot
      rintro ⟨p, hp, hred, offset, hregion, -⟩
      exact (⟨iv, tri, form, negate⟩ : FlipPrune.Box).valid_not_flipReduced hvalid hp
        hregion.1 hregion.2 hred.2.2
  | corner =>
      simp only [leafOk, decide_eq_true_eq] at h
      obtain ⟨hch, hroot, hok⟩ := h
      subst hch hroot
      exact noRupert_of_cornerOk hcorner iv tri hok
  | cayleySplit => simp [leafOk] at h
  | viewRoot => simp [leafOk] at h
  | viewSplit => simp [leafOk] at h
  | viewCut => simp [leafOk] at h
  | octahedron => simp [leafOk] at h
  | hole => simp [leafOk] at h

theorem CTree.check_sound (hdr : Fin 64 → Option Header) (hhdr : HeadersCovered hdr)
    (hcorner : CornerCovered) (ch : ChartIndex) :
    ∀ (t : CTree) (iv : Interval) (reg : Region), t.check hdr ch iv reg = true →
      (∀ h ∈ t.holes, NoRupert ch (framePath h).1 (framePath h).2) → NoRupert ch iv reg
  | .cayleySplit c lo hi, iv, reg, h, hh => by
      simp only [CTree.check, Bool.and_eq_true] at h
      simp only [CTree.holes, List.mem_append] at hh
      exact noRupert_halves ch iv reg c
        (lo.check_sound hdr hhdr hcorner ch _ _ h.1 fun x hx => hh x (.inl hx))
        (hi.check_sound hdr hhdr hcorner ch _ _ h.2 fun x hx => hh x (.inr hx))
  | .viewRoot child, iv, reg, h, hh => by
      simp only [CTree.check] at h
      have hc := child.check_sound hdr hhdr hcorner ch _ _ h hh
      rintro ⟨p, hp, hred, offset, -, hrupert⟩
      exact hc ⟨p, hp, hred, offset, chamber_mem_triangle p hred.1, hrupert⟩
  | .viewSplit c0 c1 c2 c3, iv, .triangle root tri, h, hh => by
      simp only [CTree.check, Bool.and_eq_true] at h
      simp only [CTree.holes, List.mem_append] at hh
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
      have k0 := c0.check_sound hdr hhdr hcorner ch _ _ h0
        fun x hx => hh x (.inl (.inl (.inl hx)))
      have k1 := c1.check_sound hdr hhdr hcorner ch _ _ h1
        fun x hx => hh x (.inl (.inl (.inr hx)))
      have k2 := c2.check_sound hdr hhdr hcorner ch _ _ h2
        fun x hx => hh x (.inl (.inr hx))
      have k3 := c3.check_sound hdr hhdr hcorner ch _ _ h3 fun x hx => hh x (.inr hx)
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      obtain ⟨child, hmem⟩ := mem_split hregion.2
      fin_cases child
      · exact k0 ⟨p, hp, hred, offset, ⟨hregion.1, hmem⟩, hrupert⟩
      · exact k1 ⟨p, hp, hred, offset, ⟨hregion.1, hmem⟩, hrupert⟩
      · exact k2 ⟨p, hp, hred, offset, ⟨hregion.1, hmem⟩, hrupert⟩
      · exact k3 ⟨p, hp, hred, offset, ⟨hregion.1, hmem⟩, hrupert⟩
  | .viewCut w c0 c1 c2, iv, .triangle root tri, h, hh => by
      simp only [CTree.check, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq] at h
      simp only [CTree.holes, List.mem_append] at hh
      obtain ⟨⟨⟨⟨hw0, hw1⟩, h0⟩, h1⟩, h2⟩ := h
      rintro ⟨p, hp, hred, offset, hregion, hrupert⟩
      obtain ⟨k, hk, hmem⟩ := AtlasProjectiveLocalViewTree.mem_cut hw0 hw1 hregion.2
      fin_cases k
      · exact (c0.check_sound hdr hhdr hcorner ch _ _ (h0.resolve_left (not_not.mpr hk))
            fun x hx => hh x (.inl (.inl hx))) ⟨p, hp, hred, offset, ⟨hregion.1, hmem⟩, hrupert⟩
      · exact (c1.check_sound hdr hhdr hcorner ch _ _ (h1.resolve_left (not_not.mpr hk))
            fun x hx => hh x (.inl (.inr hx))) ⟨p, hp, hred, offset, ⟨hregion.1, hmem⟩, hrupert⟩
      · exact (c2.check_sound hdr hhdr hcorner ch _ _ (h2.resolve_left (not_not.mpr hk))
            fun x hx => hh x (.inr hx)) ⟨p, hp, hred, offset, ⟨hregion.1, hmem⟩, hrupert⟩
  | .octahedron, iv, reg, h, _ => by
      simp only [CTree.check, decide_eq_true_eq] at h
      exact noRupert_of_outsideOctahedron ch iv reg h
  | .hole steps, iv, reg, h, hh => by
      simp only [CTree.check, decide_eq_true_eq] at h
      have := hh steps (by simp [CTree.holes])
      rw [h] at this
      exact this
  | .viewSplit .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .viewCut .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .projective e hints, iv, .triangle root tri, h, _ =>
      leafOk_sound hdr hhdr hcorner ch iv root tri _ h
  | .global g hints, iv, .triangle root tri, h, _ =>
      leafOk_sound hdr hhdr hcorner ch iv root tri _ h
  | .mixed m hints, iv, .triangle root tri, h, _ =>
      leafOk_sound hdr hhdr hcorner ch iv root tri _ h
  | .projectiveLocal l, iv, .triangle root tri, h, _ =>
      leafOk_sound hdr hhdr hcorner ch iv root tri _ h
  | .tube s r idx w, iv, .triangle root tri, h, _ =>
      leafOk_sound hdr hhdr hcorner ch iv root tri _ h
  | .flip f n, iv, .triangle root tri, h, _ =>
      leafOk_sound hdr hhdr hcorner ch iv root tri _ h
  | .corner, iv, .triangle root tri, h, _ =>
      leafOk_sound hdr hhdr hcorner ch iv root tri _ h
  | .projective .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .global .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .mixed .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .projectiveLocal .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .tube .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .flip .., _, .sphere, h, _ => by simp [CTree.check] at h
  | .corner, _, .sphere, h, _ => by simp [CTree.check] at h

/-- A chunk: its tree is checked at the frame of its path, its holes are other
chunks' frames. -/
theorem chunk_sound (hdr : Fin 64 → Option Header) (hhdr : HeadersCovered hdr)
    (hcorner : CornerCovered) (steps : List Step) (t : CTree)
    (h : t.check hdr 0 (framePath steps).1 (framePath steps).2 = true)
    (hh : ∀ x ∈ t.holes, NoRupert 0 (framePath x).1 (framePath x).2) :
    NoRupert 0 (framePath steps).1 (framePath steps).2 :=
  t.check_sound hdr hhdr hcorner 0 _ _ h hh

theorem holes_of {t : CTree} {L : List (List Step)} (h : t.holes = L)
    (hL : ∀ x ∈ L, NoRupert 0 (framePath x).1 (framePath x).2) :
    ∀ x ∈ t.holes, NoRupert 0 (framePath x).1 (framePath x).2 := h ▸ hL

end Noperts.Stellated.ChartKernelTree
