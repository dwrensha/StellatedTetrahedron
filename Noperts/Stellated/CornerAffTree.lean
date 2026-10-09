module

public import Noperts.Stellated.CornerTree
public import Noperts.Stellated.CornerKernelLeaf

@[expose] public section

/-!
# Recursive corner trees on reparametrized frames

The integer-frame kernel tree (`CornerKernel.KTree`) covers corner tables
without affine reparametrization.  Cone tables reparametrize `u, a, b, c`
(`Frame.aff`) and split stellarly; this file gives them a recursive tree on
rational frames (splits and stellar splits as in `Node.ValidAt`, frames
implied by the parent), whose shared leaves cite fact rows with the *same*
reparametrization (`SharedPValidA`, the `aff = f.aff` generalization of
`CornerKernel.SharedPValid`).
-/

namespace Noperts.Stellated.CornerAff

open SparsePoly CornerPoly CornerCertificate CornerTree CornerKernel
open AtlasProjectiveView

/-! ## Shared leaves with a common reparametrization -/

theorem not_rupert_sharedDA (r f : Row) (hf : f.KeyFacts) (hseg : r.seg = f.seg)
    (hkind : r.kind = f.kind) (htriple : r.triple = f.triple) (haff : r.aff = f.aff)
    (hsub : r.SubBox f) (hlamI : 0 < f.hi 1 → 0 < r.hi 1)
    (p : AtlasPose ℝ) (offset : ℝ²)
    (y : ℕ → ℝ) (hc : Coords r.seg r.kind p (affY r.aff y)) (hmem : r.box.Mem y)
    (hε : 0 < y 0) (hρ : r.isTube = true → 0 < y 6) (hlam : 0 < r.hi 1 → 0 < y 1)
    (hscale : 1 ≤ viewScale 0 p) (hD : 0 ≤ eval y r.D) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hradF := f.radius_nonneg hf.radius
  have hmemF := hsub.mem hmem
  have hcf : Coords f.seg f.kind p (affY f.aff y) := by
    rw [← haff, ← hseg, ← hkind]; exact hc
  have hρF : f.isTube = true → 0 < y 6 := fun h =>
    hρ (by simpa [Row.isTube, hkind] using h)
  apply not_rupertPose_of_corner_triple p offset r.triple hscale
  · intro i
    rw [htriple, ← eval_weightPoly hcf, ← eval_cmp]
    exact NonnegOk.sound (hf.weights i) hmemF hradF (f.nonnegVars_sound hmemF)
  · intro i
    obtain ⟨j, hji, hj⟩ := hf.weightsPos i
    refine ⟨j, hji, ?_⟩
    rw [htriple, ← eval_weightPoly hcf, ← eval_cmp]
    exact PosOk.sound hj hmemF hradF (f.positiveVars_sound hε hρF (fun h => hlam (hlamI h)))
  · intro i k
    rw [htriple, ← eval_gapPoly hcf, ← eval_cmp]
    have := NonnegOk.sound (hf.gaps i k) hmemF hradF (f.nonnegVars_sound hmemF)
    rw [eval_scale] at this
    push_cast at this
    linarith
  · have hdisp := eval_dispPoly hc r.triple
    have hD' : 0 ≤ eval (affY r.aff y) (dispPoly r.seg r.kind r.triple) := by
      rw [← eval_cmp, ← eval_normalize y, ← Row.D]
      exact hD
    rw [hdisp] at hD'
    have hd := cayleyDenom_pos p.x p.y p.z
    exact nonneg_of_mul_nonneg_right hD' hd

/-- `CornerKernel.SharedPValid` with a common (possibly nonempty) reparametrization. -/
structure SharedPValidA (r f : Row) (fp : FactPoly) : Prop where
  seg : r.seg = f.seg
  kind : r.kind = f.kind
  triple : r.triple = f.triple
  aff : r.aff = f.aff
  sub : r.SubBox f
  lam : 0 < f.hi 1 → 0 < r.hi 1
  radius : ∀ x ∈ r.radius, 0 ≤ x
  mpos : ∀ i < fp.m.length, 0 < fp.m.getD i 0 → 0 ≤ r.lo i
  cheap : cheapRow fp.S r = true

instance (r f : Row) (fp : FactPoly) : Decidable (SharedPValidA r f fp) :=
  decidable_of_iff (r.seg = f.seg ∧ r.kind = f.kind ∧ r.triple = f.triple ∧ r.aff = f.aff ∧
      r.SubBox f ∧ (0 < f.hi 1 → 0 < r.hi 1) ∧ (∀ x ∈ r.radius, 0 ≤ x) ∧
      (∀ i < fp.m.length, 0 < fp.m.getD i 0 → 0 ≤ r.lo i) ∧ cheapRow fp.S r = true)
    ⟨fun ⟨a, b, c, d, g, h, i, j, k⟩ => ⟨a, b, c, d, g, h, i, j, k⟩,
      fun ⟨a, b, c, d, g, h, i, j, k⟩ => ⟨a, b, c, d, g, h, i, j, k⟩⟩

theorem not_rupert_sharedPA (r f : Row) (fp : FactPoly) (hf : f.KeyFacts) (hfp : fp.Ok f)
    (hv : SharedPValidA r f fp) (p : AtlasPose ℝ) (offset : ℝ²)
    (y : ℕ → ℝ) (hc : Coords r.seg r.kind p (affY r.aff y)) (hmem : r.box.Mem y)
    (hε : 0 < y 0) (hρ : r.isTube = true → 0 < y 6) (hlam : 0 < r.hi 1 → 0 < y 1)
    (hscale : 1 ≤ viewScale 0 p) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) exactPolyhedron.hull := by
  have hrad := r.radius_nonneg hv.radius
  refine not_rupert_sharedDA r f hf hv.seg hv.kind hv.triple hv.aff hv.sub hv.lam
    p offset y hc hmem hε hρ hlam hscale ?_
  have hD : r.D = f.D := by
    unfold Row.D; rw [hv.seg, hv.kind, hv.triple, hv.aff]
  rw [hD, hfp.eval_D]
  have hK : (0 : ℝ) < fp.K := by exact_mod_cast hfp.1
  have hmono : 0 ≤ monoEval y fp.m := by
    apply monoEval_nonneg_of
    intro i hi
    have hlen : i < fp.m.length := by
      by_contra h
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : fp.m.length ≤ i)] at hi
    have hlo := hv.mpos i hlen hi
    have := abs_le.mp (hmem i)
    have hlo' : (0 : ℝ) ≤ (r.box.center i : ℝ) - r.box.radius i := by
      have : (0 : ℚ) ≤ r.box.center i - r.box.radius i := hlo
      exact_mod_cast this
    linarith [this.1]
  have hS := cheapRow_sound fp.S r hv.cheap hrad y hmem
  exact mul_nonneg hε.le (div_nonneg (mul_nonneg hmono hS) hK.le)

/-! ## The tree -/

/-- The certificate row of a leaf at frame `f`. -/
def frameRow (f : Frame) (triple : Triple) (split : List (ℕ × Bool)) (shift : List ℚ) : Row :=
  ⟨f.seg, f.kind, f.center, f.radius, triple, split, shift, f.aff⟩

inductive RTree where
  | split (v : ℕ) (m : ℚ) (lo hi : RTree)
  | stellar (i j : ℕ) (α β : ℚ) (lo hi : RTree)
  | leaf (l : Leaf)
  /-- A shared leaf citing fact `k` (same reparametrization). -/
  | sharedPA (triple : Triple) (split : List (ℕ × Bool)) (shift : List ℚ) (k : ℕ)
  | hole (f : Frame)

/-- The fact and its polynomial data cited by a shared leaf. -/
def sharedPAOk (facts : Array Row) (fps : Array FactPoly) (k : ℕ) (row : Row) : Bool :=
  match facts[k]?, fps[k]? with
  | some fact, some fp => decide (SharedPValidA row fact fp)
  | _, _ => false

def RTree.check (H : Handoffs) (facts : Array Row) (fps : Array FactPoly) :
    Frame → RTree → Bool
  | f, .split v m lo hi =>
      decide (v < f.center.length ∧ v < f.radius.length ∧ m ≤ f.hi v) &&
        RTree.check H facts fps (f.lower v m) lo && RTree.check H facts fps (f.upper v m) hi
  | f, .stellar i j α β lo hi =>
      decide ((2 ≤ i ∧ i ≤ 5) ∧ (2 ≤ j ∧ j ≤ 5) ∧ i ≠ j ∧ 0 < α ∧ 0 < β ∧ f.aff ≠ [] ∧
        f.lo i = 0 ∧ f.lo j = 0 ∧ i < f.center.length ∧ i < f.radius.length ∧
        j < f.center.length ∧ j < f.radius.length) &&
        RTree.check H facts fps (f.stellar i j α β) lo &&
          RTree.check H facts fps (f.stellar j i β α) hi
  | f, .leaf l => decide (l.Valid H facts fps f)
  | f, .sharedPA triple sp shift k => sharedPAOk facts fps k (frameRow f triple sp shift)
  | f, .hole g => decide (g = f)

def RTree.holes : RTree → List Frame
  | .split _ _ lo hi => lo.holes ++ hi.holes
  | .stellar _ _ _ _ lo hi => lo.holes ++ hi.holes
  | .leaf _ => []
  | .sharedPA .. => []
  | .hole g => [g]

theorem sharedPA_covered (facts : Array Row) (fps : Array FactPoly)
    (hfacts : ∀ fact ∈ facts, fact.KeyFacts) (hfps : FactPolysOk facts fps) (f : Frame)
    (triple : Triple) (sp : List (ℕ × Bool)) (shift : List ℚ) (k : ℕ)
    (h : sharedPAOk facts fps k (frameRow f triple sp shift) = true) : Covered f := by
  intro p offset y hc hmem hε hρ hlam hflip hscale
  unfold sharedPAOk at h
  cases hk : facts[k]? with
  | none => simp [hk] at h
  | some fact =>
      cases hp : fps[k]? with
      | none => simp [hk, hp] at h
      | some fp =>
          simp only [hk, hp, decide_eq_true_eq] at h
          have hfact : fact.KeyFacts := hfacts fact (Array.mem_of_getElem? hk)
          have hkl : k < fps.size := by
            by_contra h'
            simp [Array.getElem?_eq_none (by omega : fps.size ≤ k)] at hp
          have hok := hfps ⟨k, hkl⟩
          simp only [FactPolyAt, hk, Fin.getElem_fin] at hok
          have hfp' : fps[k] = fp := by
            exact Array.getElem_eq_iff.mpr hp
          rw [hfp'] at hok
          have hbox : (frameRow f triple sp shift).box = f.box := by
            simp [Frame.box, Frame.toRow, Row.box, frameRow]
          have hhi : (frameRow f triple sp shift).hi 1 = f.hi 1 := by
            simp [Row.hi, Frame.hi, Frame.toRow, Row.box, frameRow]
          exact not_rupert_sharedPA _ fact fp hfact hok h p offset y hc (hbox ▸ hmem) hε
            (fun ht => hρ (by simpa [Row.isTube, frameRow] using ht))
            (fun h => hlam (hhi ▸ h)) hscale

theorem RTree.check_sound (H : Handoffs) (hH : ∀ h f, H.Valid h f → Covered f)
    (facts : Array Row) (fps : Array FactPoly)
    (hfacts : ∀ fact ∈ facts, fact.KeyFacts) (hfps : FactPolysOk facts fps) :
    ∀ (t : RTree) (f : Frame), t.check H facts fps f = true →
      (∀ g ∈ t.holes, Covered g) → Covered f
  | .split v m lo hi, f, h, hh => by
      simp only [RTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hc, hr, hm⟩, hl⟩, hu⟩ := h
      simp only [RTree.holes, List.mem_append] at hh
      have covL := lo.check_sound H hH facts fps hfacts hfps _ hl fun g hg => hh g (.inl hg)
      have covU := hi.check_sound H hH facts fps hfacts hfps _ hu fun g hg => hh g (.inr hg)
      intro p offset y hcoords hmem hε hρ hlam hflip hscale
      rcases f.mem_split hc hr (m := m) hmem with h | h
      · exact covL p offset y hcoords h hε hρ
          (fun h' => hlam (lt_of_lt_of_le h' (f.lower_hi_le hc hr hm 1))) hflip hscale
      · exact covU p offset y hcoords h hε hρ
          (fun h' => hlam (lt_of_lt_of_le h' (f.upper_hi_le hc hr m 1))) hflip hscale
  | .stellar vi vj α β tl tu, f, h, hh => by
      simp only [RTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hi, hj, hij, hα, hβ, hne, hloi, hloj, hic, hir, hjc, hjr⟩, hl⟩, hu⟩ := h
      simp only [RTree.holes, List.mem_append] at hh
      have covL := tl.check_sound H hH facts fps hfacts hfps _ hl fun g hg => hh g (.inl hg)
      have covU := tu.check_sound H hH facts fps hfacts hfps _ hu fun g hg => hh g (.inr hg)
      intro p offset y hcoords hmem hε hρ hlam hflip hscale
      exact f.stellar_cover hi hj hij hα hβ hne hloi hloj hic hir hjc hjr covL covU
        p offset y hcoords hmem hε hρ hlam hflip hscale
  | .leaf l, f, h, _ => by
      simp only [RTree.check, decide_eq_true_eq] at h
      exact leaf_covered H hH facts hfacts fps hfps f l h
  | .sharedPA triple sp shift k, f, h, _ => sharedPA_covered facts fps hfacts hfps f
      triple sp shift k h
  | .hole g, f, h, hh => by
      simp only [RTree.check, decide_eq_true_eq] at h
      subst h
      exact hh g (by simp [RTree.holes])

theorem holes_of {t : RTree} {L : List Frame} (h : t.holes = L)
    (hL : ∀ g ∈ L, Covered g) : ∀ g ∈ t.holes, Covered g := h ▸ hL

end Noperts.Stellated.CornerAff
