import Mettapedia.GSLT.Causality.DoCalculus.CondMass
import Mettapedia.GSLT.Causality.DoCalculus.MultiIntervention

/-!
# Exchange and deletion for finite interventions

Rule 2 equates `P(y | do(x), do(z), w)` with `P(y | do(x), z, w)`. When every
parent of a `Z`-node already lies in `X ∪ Z ∪ W`, the `Z`-factor of the
g-formula is constant on that slice and cancels, once the `do(x)` mass of
`(z, w)` is positive and finite.

Rule 3 equates `P(y, w | do(x), do(z))` with `P(y, w | do(x))` when every edge
out of `Z` lands in `X ∪ Z`. In the graph with arrows into `X` deleted, no
`Z`-node is then an ancestor of a node outside `Z`, so `Z` is the whole set
`Z(W)` whenever `W` is disjoint from `Z`. The test graph that also deletes
arrows into `Z` isolates `Z`, and the g-formula marginal of any set disjoint
from `Z` is unchanged by the second intervention.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open DSeparation
open scoped BigOperators ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]

variable (hAcyclic : graph.IsAcyclic)
variable {β : Type} [Fintype β] [DecidableEq β] [MeasurableSpace β]

/-! ## Slices of the g-formula -/

/-- `f` agrees with `a` on `S`. -/
def agreesOn (S : Finset V) (a f : V → β) : Bool :=
  decide (∀ v ∈ S, f v = a v)

omit [DecidableRel graph.edges] [Fintype β] [MeasurableSpace β] in
lemma agreesOn_eq_true_iff {S : Finset V} {a f : V → β} :
    agreesOn S a f = true ↔ ∀ v ∈ S, f v = a v := by
  simp [agreesOn, decide_eq_true_eq]

/-- Mass of the configurations that agree with `anchor` on `S`. -/
noncomputable def truncSlice
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (assignment : V → Option β) (S : Finset V) (anchor : V → β) : ℝ≥0∞ :=
  ∑ f : V → β, if agreesOn S anchor f = true then
    truncatedWeight graph hAcyclic cpt assignment f else 0

omit [Fintype β] [DecidableEq V] in
lemma truncatedFactor_ne_top
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (assignment : V → Option β) (f : V → β) (v : V) :
    truncatedFactor graph hAcyclic cpt assignment f v ≠ ⊤ := by
  cases hassign : assignment v with
  | some a =>
      simp only [truncatedFactor, hassign]
      split
      · exact ENNReal.one_ne_top
      · exact ENNReal.zero_ne_top
  | none =>
      simp only [truncatedFactor, hassign, cptAt]
      exact PMF.apply_ne_top _ _

omit [DecidableEq V] [Fintype β] in
lemma truncatedWeight_ne_top
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (assignment : V → Option β) (f : V → β) :
    truncatedWeight graph hAcyclic cpt assignment f ≠ ⊤ := by
  unfold truncatedWeight
  exact ENNReal.prod_ne_top fun v _ =>
    truncatedFactor_ne_top graph hAcyclic cpt assignment f v

lemma truncSlice_ne_top
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (assignment : V → Option β) (S : Finset V) (anchor : V → β) :
    truncSlice graph hAcyclic cpt assignment S anchor ≠ ⊤ := by
  unfold truncSlice
  refine (ENNReal.sum_ne_top).2 fun f _ => ?_
  split
  · exact truncatedWeight_ne_top graph hAcyclic cpt assignment f
  · exact ENNReal.zero_ne_top

omit [DecidableRel graph.edges] [Fintype β] [MeasurableSpace β] in
lemma agrees_subset {S T : Finset V} {a f : V → β}
    (hST : S ⊆ T) (hf : agreesOn T a f = true) :
    agreesOn S a f = true := by
  rw [agreesOn_eq_true_iff] at hf ⊢
  intro v hv
  exact hf v (hST hv)

/-! ## Rule 2, when parents of `Z` are conditioned -/

/-- Product of the conditional tables of the nodes in `Z`. -/
noncomputable def zFactor (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (Z : Finset V) (f : V → β) : ℝ≥0∞ :=
  ∏ v ∈ Z, cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)

omit [DecidableEq V] [Fintype β] [DecidableEq β] in
lemma zFactor_ne_top
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT) (Z : Finset V) (f : V → β) :
    zFactor graph hAcyclic cpt Z f ≠ ⊤ := by
  unfold zFactor
  exact ENNReal.prod_ne_top fun v _ => by
    simp only [cptAt]
    exact PMF.apply_ne_top _ _

omit [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma parentFun_congr {v : V} {f g : V → β}
    (h : ∀ u, graph.edges u v → f u = g u) :
    parentFunOf graph f v = parentFunOf graph g v := by
  funext p
  exact h p.1 ((mem_parentsFinset_iff graph p.1 v).1 p.property)

omit [Fintype β] [DecidableEq β] in
lemma zFactor_congr
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z W : Finset V} {f g : V → β}
    (hparents : ∀ v ∈ Z, ∀ u, graph.edges u v → u ∈ X ∪ Z ∪ W)
    (hfg : ∀ u ∈ X ∪ Z ∪ W, f u = g u) :
    zFactor graph hAcyclic cpt Z f = zFactor graph hAcyclic cpt Z g := by
  unfold zFactor
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvXW : v ∈ X ∪ Z ∪ W :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv)))
  have hvEq : f v = g v := hfg v hvXW
  have hrow : parentFunOf graph f v = parentFunOf graph g v :=
    parentFun_congr graph fun u hu => hfg u (hparents v hv u hu)
  simp [cptAt, hrow, hvEq]

omit [Fintype β] in
/-- On the slice that agrees with the intervention, the `do(X)` weight is the
`do(X ∪ Z)` weight times the `Z`-factor. -/
lemma truncatedWeight_mul_zFactor
    {X Z : Finset V} (hdisj : Disjoint X Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z f : V → β)
    (hz : ∀ v ∈ Z, f v = z v) :
    truncatedWeight graph hAcyclic cpt (doFinset X x) f =
      truncatedWeight graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) f *
        zFactor graph hAcyclic cpt Z f := by
  unfold truncatedWeight zFactor
  let gX : V → ℝ≥0∞ := fun v =>
    truncatedFactor graph hAcyclic cpt (doFinset X x) f v
  let gXZ : V → ℝ≥0∞ := fun v =>
    truncatedFactor graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) f v
  have hcompl : ∀ v ∈ Zᶜ, gX v = gXZ v := by
    intro v hv
    have hvZ : v ∉ Z := by simpa using hv
    exact truncatedFactor_congr_assignment graph hAcyclic cpt
      ((doFinset_eq_doTwo_of_not_mem (z := z) hvZ).trans
        (congrArg (fun a : V → Option β => a v) (doTwo_eq_doFinset_union hdisj)))
  have hZcpt : ∀ v ∈ Z, gX v =
      cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v) := by
    intro v hv
    have hvX : v ∉ X := fun hX => Finset.disjoint_left.mp hdisj hX hv
    simp [gX, truncatedFactor, doFinset_eq_none hvX, cptAt]
  have hZone : ∀ v ∈ Z, gXZ v = 1 := by
    intro v hv
    have hvX : v ∉ X := fun hX => Finset.disjoint_left.mp hdisj hX hv
    have hmem : v ∈ X ∪ Z := Finset.mem_union.mpr (Or.inr hv)
    have hmerge : mergeAssign X x z v = z v := by simp [mergeAssign, hvX]
    have hfv : f v = mergeAssign X x z v := (hz v hv).trans hmerge.symm
    simp [gXZ, truncatedFactor, doFinset_eq_some hmem, hfv]
  have hZprod : ∏ v ∈ Z, gX v =
      ∏ v ∈ Z, cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v) :=
    Finset.prod_congr rfl hZcpt
  have hZoneProd : ∏ v ∈ Z, gXZ v = 1 := Finset.prod_eq_one hZone
  have hcomplProd : ∏ v ∈ Zᶜ, gX v = ∏ v ∈ Zᶜ, gXZ v :=
    Finset.prod_congr rfl hcompl
  calc
    ∏ v, gX v = (∏ v ∈ Z, gX v) * ∏ v ∈ Zᶜ, gX v :=
      (Finset.prod_mul_prod_compl Z gX).symm
    _ = (∏ v ∈ Z, cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)) *
          ∏ v ∈ Zᶜ, gXZ v := by rw [hZprod, hcomplProd]
    _ = (∏ v ∈ Z, cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)) *
          ((∏ v ∈ Z, gXZ v) * ∏ v ∈ Zᶜ, gXZ v) := by
            conv_lhs =>
              arg 2
              rw [← one_mul (∏ v ∈ Zᶜ, gXZ v), ← hZoneProd]
    _ = (∏ v ∈ Z, cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)) *
          ∏ v, gXZ v := by rw [Finset.prod_mul_prod_compl Z gXZ]
    _ = (∏ v, gXZ v) *
          ∏ v ∈ Z, cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v) := by
            rw [mul_comm]

lemma truncSlice_mul_zFactor
    {X Z W S : Finset V}
    (hdisj : Disjoint X Z)
    (hparents : ∀ v ∈ Z, ∀ u, graph.edges u v → u ∈ X ∪ Z ∪ W)
    (hS : X ∪ Z ∪ W ⊆ S)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β)
    (hz : ∀ v ∈ Z, anchor v = z v) :
    truncSlice graph hAcyclic cpt (doFinset X x) S anchor =
      zFactor graph hAcyclic cpt Z anchor *
        truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) S anchor := by
  unfold truncSlice
  let π : ℝ≥0∞ := zFactor graph hAcyclic cpt Z anchor
  have hterm : ∀ f,
      (if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt (doFinset X x) f else 0) =
      π * (if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) f else 0) := by
    intro f
    cases hbit : agreesOn S anchor f
    · simp [mul_zero]
    · have hall : ∀ v ∈ S, f v = anchor v := (agreesOn_eq_true_iff).mp hbit
      have hzS : ∀ v ∈ Z, f v = z v := by
        intro v hv
        have hvS : v ∈ S := hS (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr hv))))
        exact (hall v hvS).trans (hz v hv)
      have hfg : ∀ u ∈ X ∪ Z ∪ W, f u = anchor u := by
        intro u hu
        exact hall u (hS hu)
      have hπ : zFactor graph hAcyclic cpt Z f = π := by
        simpa [π] using zFactor_congr graph hAcyclic cpt hparents hfg
      simp only [ite_true]
      rw [truncatedWeight_mul_zFactor graph hAcyclic hdisj cpt x z f hzS, hπ, mul_comm]
  simp_rw [hterm, ← Finset.mul_sum]
  simp [π]

omit [Fintype V] [DecidableRel graph.edges] [MeasurableSpace β] in
lemma conditioning_subset_with_outcome (X Y Z W : Finset V) :
    X ∪ Z ∪ W ⊆ X ∪ Y ∪ Z ∪ W := by
  intro v hv
  rcases Finset.mem_union.mp hv with hvXZ | hvW
  · rcases Finset.mem_union.mp hvXZ with hvX | hvZ
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl hvX)))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hvZ)))
  · exact Finset.mem_union.mpr (Or.inr hvW)

/-- **Rule 2 when every parent of `Z` lies in `X ∪ Z ∪ W`.**

The numerator fixes `X, Y, Z, W` and the denominator fixes `X, Z, W`. Both
ratios are conditional masses of the g-formula. Positivity is the `do(X)` mass
of the denominator.
-/
theorem rule2_of_parents
    {X Y Z W : Finset V}
    (hdisj : Disjoint X Z)
    (hparents : ∀ v ∈ Z, ∀ u, graph.edges u v → u ∈ X ∪ Z ∪ W)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β)
    (hz : ∀ v ∈ Z, anchor v = z v)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Z ∪ W) anchor =
    truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor := by
  let numS : Finset V := X ∪ Y ∪ Z ∪ W
  let denS : Finset V := X ∪ Z ∪ W
  have hden : X ∪ Z ∪ W ⊆ denS := by
    dsimp [denS]
    exact Finset.Subset.refl _
  have hnum : X ∪ Z ∪ W ⊆ numS := conditioning_subset_with_outcome X Y Z W
  have hnumFac :=
    truncSlice_mul_zFactor graph hAcyclic hdisj hparents hnum cpt x z anchor hz
  have hdenFac :=
    truncSlice_mul_zFactor graph hAcyclic hdisj hparents hden cpt x z anchor hz
  let π : ℝ≥0∞ := zFactor graph hAcyclic cpt Z anchor
  have hdenXZ : truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) denS anchor ≠ ⊤ :=
    truncSlice_ne_top graph hAcyclic cpt _ denS anchor
  have hdenXTop : truncSlice graph hAcyclic cpt (doFinset X x) denS anchor ≠ ⊤ :=
    truncSlice_ne_top graph hAcyclic cpt _ denS anchor
  have hdenXZ0 : truncSlice graph hAcyclic cpt
      (doFinset (X ∪ Z) (mergeAssign X x z)) denS anchor ≠ 0 := by
    intro h0
    apply hpos
    have hfac := hdenFac
    rw [h0, mul_zero] at hfac
    simpa [denS] using hfac
  have hcross :
      truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) numS anchor *
        truncSlice graph hAcyclic cpt (doFinset X x) denS anchor =
      truncSlice graph hAcyclic cpt (doFinset X x) numS anchor *
        truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) denS anchor := by
    calc
      truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) numS anchor *
          truncSlice graph hAcyclic cpt (doFinset X x) denS anchor
        = truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) numS anchor *
            (π * truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) denS anchor) := by
              rw [hdenFac]
      _ = (π * truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) numS anchor) *
            truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) denS anchor := by
              rw [← mul_assoc, mul_comm
                (truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) numS anchor) π]
      _ = truncSlice graph hAcyclic cpt (doFinset X x) numS anchor *
            truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) denS anchor := by
              rw [← hnumFac]
  exact ennreal_div_eq_of_cross_mul hcross hdenXZ0 hdenXZ hpos hdenXTop 

/-! ## Rule 3, when `Z` has no child outside `X ∪ Z` -/

/-- A configuration split into the `Z` coordinates and the rest. -/
def glue (Z : Finset V) (inn : {v // v ∈ Z} → β) (out : {v // v ∉ Z} → β) : V → β :=
  fun v => if hv : v ∈ Z then inn ⟨v, hv⟩ else out ⟨v, hv⟩

/-- The `Z` coordinates of a fixed assignment `z`. -/
def innOf (Z : Finset V) (z : V → β) : {v // v ∈ Z} → β :=
  fun v => z v.1

omit [DecidableRel graph.edges] [DecidableEq β] [MeasurableSpace β] in
lemma sum_glue (Z : Finset V) (g : (V → β) → ℝ≥0∞) :
    ∑ f : V → β, g f =
      ∑ inn : {v // v ∈ Z} → β, ∑ out : {v // v ∉ Z} → β, g (glue Z inn out) := by
  let e : (V → β) ≃ ({v // v ∈ Z} → β) × ({v // v ∉ Z} → β) :=
    Equiv.piEquivPiSubtypeProd (fun v => v ∈ Z) (fun _ => β)
  calc
    ∑ f, g f = ∑ p, g (e.symm p) := (Equiv.sum_comp e.symm g).symm
    _ = ∑ inn, ∑ out, g (e.symm (inn, out)) := Fintype.sum_prod_type (fun p => g (e.symm p))
    _ = ∑ inn, ∑ out, g (glue Z inn out) := by
        refine Finset.sum_congr rfl fun inn _ => Finset.sum_congr rfl fun out _ => ?_
        apply congrArg g
        funext v
        rfl

omit [DecidableRel graph.edges] [Fintype β] [MeasurableSpace β] in
lemma agrees_glue_indep
    {S Z : Finset V} (hSZ : Disjoint S Z) (anchor : V → β)
    (inn₁ inn₂ : {v // v ∈ Z} → β) (out : {v // v ∉ Z} → β) :
    agreesOn S anchor (glue Z inn₁ out) = agreesOn S anchor (glue Z inn₂ out) := by
  unfold agreesOn
  rw [decide_eq_decide]
  constructor
  · intro h v hv
    have hvZ : v ∉ Z := Finset.disjoint_left.mp hSZ hv
    have hglue : glue Z inn₁ out v = glue Z inn₂ out v := by simp [glue, hvZ]
    exact hglue.symm.trans (h v hv)
  · intro h v hv
    have hvZ : v ∉ Z := Finset.disjoint_left.mp hSZ hv
    have hglue : glue Z inn₁ out v = glue Z inn₂ out v := by simp [glue, hvZ]
    exact hglue.trans (h v hv)

/-- Set every vertex outside `Z` and leave `Z` free. -/
def freeze (Z : Finset V) (out : {v // v ∉ Z} → β) : V → Option β :=
  fun v => if hv : v ∉ Z then some (out ⟨v, hv⟩) else none

omit [Fintype β] in
lemma freeze_diag_weight
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (Z : Finset V) (inn : {v // v ∈ Z} → β) (out : {v // v ∉ Z} → β) :
    truncatedWeight graph hAcyclic cpt (freeze Z out) (glue Z inn out) =
      ∏ v ∈ Z, cptAt graph hAcyclic cpt v
        (parentFunOf graph (glue Z inn out) v) (glue Z inn out v) := by
  unfold truncatedWeight
  have hcompl : ∏ v ∈ Zᶜ, truncatedFactor graph hAcyclic cpt (freeze Z out) (glue Z inn out) v = 1 := by
    refine Finset.prod_eq_one fun v hv => ?_
    have hvZ : v ∉ Z := by simpa using hv
    simp [truncatedFactor, freeze, glue, hvZ]
  have hZ : ∏ v ∈ Z, truncatedFactor graph hAcyclic cpt (freeze Z out) (glue Z inn out) v =
      ∏ v ∈ Z, cptAt graph hAcyclic cpt v
        (parentFunOf graph (glue Z inn out) v) (glue Z inn out v) := by
    refine Finset.prod_congr rfl fun v hv => ?_
    simp [truncatedFactor, freeze, glue, hv, cptAt]
  calc
    ∏ v, truncatedFactor graph hAcyclic cpt (freeze Z out) (glue Z inn out) v
      = (∏ v ∈ Z, truncatedFactor graph hAcyclic cpt (freeze Z out) (glue Z inn out) v) *
          ∏ v ∈ Zᶜ, truncatedFactor graph hAcyclic cpt (freeze Z out) (glue Z inn out) v :=
        (Finset.prod_mul_prod_compl Z _).symm
    _ = (∏ v ∈ Z, cptAt graph hAcyclic cpt v
          (parentFunOf graph (glue Z inn out) v) (glue Z inn out v)) * 1 := by
        rw [hZ, hcompl]
    _ = ∏ v ∈ Z, cptAt graph hAcyclic cpt v
          (parentFunOf graph (glue Z inn out) v) (glue Z inn out v) := by
        rw [mul_one]

omit [Fintype β] in
lemma freeze_off_weight
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (Z : Finset V) (inn : {v // v ∈ Z} → β)
    {out out' : {v // v ∉ Z} → β} (hne : out' ≠ out) :
    truncatedWeight graph hAcyclic cpt (freeze Z out) (glue Z inn out') = 0 := by
  rcases Function.ne_iff.mp hne with ⟨i, hi⟩
  unfold truncatedWeight
  refine Finset.prod_eq_zero (Finset.mem_univ i.1) ?_
  have hiZ : i.1 ∉ Z := i.2
  simp [truncatedFactor, freeze, glue, hiZ, hi]

/-- Summing the conditional tables of `Z`, with the outside held fixed, gives `1`. -/
lemma zCpt_sum_eq_one [Inhabited β]
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (Z : Finset V) (out : {v // v ∉ Z} → β) :
    ∑ inn : {v // v ∈ Z} → β,
      ∏ v ∈ Z, cptAt graph hAcyclic cpt v
        (parentFunOf graph (glue Z inn out) v) (glue Z inn out v) = 1 := by
  have h1 := truncatedWeight_sum_eq_one graph hAcyclic cpt (freeze Z out)
  rw [sum_glue Z (fun f => truncatedWeight graph hAcyclic cpt (freeze Z out) f)] at h1
  have hterm : ∀ inn out',
      truncatedWeight graph hAcyclic cpt (freeze Z out) (glue Z inn out') =
        if out' = out then
          ∏ v ∈ Z, cptAt graph hAcyclic cpt v
            (parentFunOf graph (glue Z inn out) v) (glue Z inn out v)
        else 0 := by
    intro inn out'
    by_cases hout : out' = out
    · subst hout
      rw [if_pos rfl]
      exact freeze_diag_weight graph hAcyclic cpt Z inn out'
    · simp [hout, freeze_off_weight graph hAcyclic cpt Z inn hout]
  simp_rw [hterm] at h1
  simp_rw [Fintype.sum_ite_eq'] at h1
  exact h1

/-- Product of the g-formula factors outside `Z`, under `do(X)`. -/
noncomputable def outsideProd
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (X : Finset V) (x : V → β) (Z : Finset V) (z : V → β)
    (out : {v // v ∉ Z} → β) : ℝ≥0∞ :=
  ∏ v ∈ Zᶜ, truncatedFactor graph hAcyclic cpt (doFinset X x) (glue Z (innOf Z z) out) v

omit [Fintype β] in
lemma outsideProd_glue
    {X Z : Finset V}
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z : V → β) (inn : {v // v ∈ Z} → β) (out : {v // v ∉ Z} → β) :
    ∏ v ∈ Zᶜ, truncatedFactor graph hAcyclic cpt (doFinset X x) (glue Z inn out) v =
      outsideProd graph hAcyclic cpt X x Z z out := by
  unfold outsideProd
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvZ : v ∉ Z := by simpa using hv
  by_cases hvX : v ∈ X
  · have hval : glue Z inn out v = glue Z (innOf Z z) out v := by simp [glue, hvZ]
    simp [truncatedFactor, doFinset, hvX, hval]
  · have hfree : doFinset X x v = none := doFinset_eq_none hvX
    have hparents : ∀ u, graph.edges u v → u ∉ Z := by
      intro u hu huZ
      have hvXZ : v ∈ X ∪ Z := hout0 u huZ v hu
      rcases Finset.mem_union.mp hvXZ with hvX' | hvZ'
      · exact hvX hvX'
      · exact hvZ hvZ'
    have hrow : parentFunOf graph (glue Z inn out) v =
        parentFunOf graph (glue Z (innOf Z z) out) v :=
      parentFun_congr graph fun u hu => by
        have huZ : u ∉ Z := hparents u hu
        simp [glue, huZ]
    have hval : glue Z inn out v = glue Z (innOf Z z) out v := by simp [glue, hvZ]
    simp [truncatedFactor, hfree, cptAt, hrow, hval]

omit [Fintype β] in
lemma weight_doX_split
    {X Z : Finset V} (hXZ : Disjoint X Z)
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z : V → β) (inn : {v // v ∈ Z} → β) (out : {v // v ∉ Z} → β) :
    truncatedWeight graph hAcyclic cpt (doFinset X x) (glue Z inn out) =
      (∏ v ∈ Z, cptAt graph hAcyclic cpt v
        (parentFunOf graph (glue Z inn out) v) (glue Z inn out v)) *
        outsideProd graph hAcyclic cpt X x Z z out := by
  unfold truncatedWeight
  have hZ : ∀ v ∈ Z, truncatedFactor graph hAcyclic cpt (doFinset X x) (glue Z inn out) v =
      cptAt graph hAcyclic cpt v
        (parentFunOf graph (glue Z inn out) v) (glue Z inn out v) := by
    intro v hv
    have hvX : v ∉ X := fun hvX => Finset.disjoint_left.mp hXZ hvX hv
    simp [truncatedFactor, doFinset_eq_none hvX, cptAt]
  calc
    ∏ v, truncatedFactor graph hAcyclic cpt (doFinset X x) (glue Z inn out) v
      = (∏ v ∈ Z, truncatedFactor graph hAcyclic cpt (doFinset X x) (glue Z inn out) v) *
          ∏ v ∈ Zᶜ, truncatedFactor graph hAcyclic cpt (doFinset X x) (glue Z inn out) v :=
        (Finset.prod_mul_prod_compl Z _).symm
    _ = (∏ v ∈ Z, cptAt graph hAcyclic cpt v
          (parentFunOf graph (glue Z inn out) v) (glue Z inn out v)) *
          outsideProd graph hAcyclic cpt X x Z z out := by
        rw [Finset.prod_congr rfl hZ,
          outsideProd_glue graph hAcyclic hout0 cpt x z inn out]

/-- The `Z` indicator of the merged intervention, as a product over `Z`. -/
noncomputable def zIndicator (Z : Finset V) (z : V → β) (inn : {v // v ∈ Z} → β) : ℝ≥0∞ :=
  ∏ v ∈ Z, if hv : v ∈ Z then if inn ⟨v, hv⟩ = z v then (1 : ℝ≥0∞) else 0 else 0

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [MeasurableSpace β] in
lemma zIndicator_eq (Z : Finset V) (z : V → β) (inn : {v // v ∈ Z} → β) :
    zIndicator Z z inn = if inn = innOf Z z then 1 else 0 := by
  by_cases h : inn = innOf Z z
  · subst h
    rw [if_pos rfl]
    unfold zIndicator innOf
    refine Finset.prod_eq_one fun v hv => ?_
    simp [hv]
  · rw [if_neg h]
    rcases Function.ne_iff.mp h with ⟨i, hi⟩
    unfold zIndicator
    have hne : inn i ≠ z i.1 := by simpa [innOf] using hi
    refine Finset.prod_eq_zero i.2 ?_
    simp [i.2, hne]

omit [Fintype β] in
lemma weight_doXZ_split
    {X Z : Finset V} (hXZ : Disjoint X Z)
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z : V → β) (inn : {v // v ∈ Z} → β) (out : {v // v ∉ Z} → β) :
    truncatedWeight graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) =
      zIndicator Z z inn * outsideProd graph hAcyclic cpt X x Z z out := by
  unfold truncatedWeight
  have hZ : ∀ v ∈ Z,
      truncatedFactor graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) v =
        if hv : v ∈ Z then if inn ⟨v, hv⟩ = z v then 1 else 0 else 0 := by
    intro v hv
    have hvX : v ∉ X := fun hvX => Finset.disjoint_left.mp hXZ hvX hv
    have hmem : v ∈ X ∪ Z := Finset.mem_union.mpr (Or.inr hv)
    have hmerge : mergeAssign X x z v = z v := by simp [mergeAssign, hvX]
    have hglue : glue Z inn out v = inn ⟨v, hv⟩ := by simp [glue, hv]
    simp [truncatedFactor, doFinset_eq_some hmem, hmerge, hglue, hv]
  have hcompl : ∏ v ∈ Zᶜ,
      truncatedFactor graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) v =
        outsideProd graph hAcyclic cpt X x Z z out := by
    refine Eq.trans ?_ (outsideProd_glue graph hAcyclic hout0 cpt x z inn out)
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvZ : v ∉ Z := by simpa using hv
    exact (truncatedFactor_congr_assignment graph hAcyclic cpt
      ((doFinset_eq_doTwo_of_not_mem (z := z) hvZ).trans
        (congrArg (fun a : V → Option β => a v) (doTwo_eq_doFinset_union hXZ)))).symm
  have hprod : ∏ v ∈ Z, truncatedFactor graph hAcyclic cpt
      (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) v = zIndicator Z z inn := by
    unfold zIndicator
    exact Finset.prod_congr rfl hZ
  calc
    ∏ v, truncatedFactor graph hAcyclic cpt
        (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) v
      = (∏ v ∈ Z, truncatedFactor graph hAcyclic cpt
          (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) v) *
          ∏ v ∈ Zᶜ, truncatedFactor graph hAcyclic cpt
            (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) v :=
        (Finset.prod_mul_prod_compl Z _).symm
    _ = zIndicator Z z inn * outsideProd graph hAcyclic cpt X x Z z out := by
        rw [hprod, hcompl]

lemma sum_inn_doX [Inhabited β]
    {X Z : Finset V} (hXZ : Disjoint X Z)
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z : V → β) (out : {v // v ∉ Z} → β) :
    ∑ inn : {v // v ∈ Z} → β,
      truncatedWeight graph hAcyclic cpt (doFinset X x) (glue Z inn out) =
        outsideProd graph hAcyclic cpt X x Z z out := by
  simp_rw [weight_doX_split graph hAcyclic hXZ hout0 cpt x z _ out]
  rw [← Finset.sum_mul, zCpt_sum_eq_one graph hAcyclic cpt Z out, one_mul]

lemma sum_inn_doXZ
    {X Z : Finset V} (hXZ : Disjoint X Z)
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z : V → β) (out : {v // v ∉ Z} → β) :
    ∑ inn : {v // v ∈ Z} → β,
      truncatedWeight graph hAcyclic cpt
        (doFinset (X ∪ Z) (mergeAssign X x z)) (glue Z inn out) =
        outsideProd graph hAcyclic cpt X x Z z out := by
  simp_rw [weight_doXZ_split graph hAcyclic hXZ hout0 cpt x z _ out]
  have hterm : ∀ inn, zIndicator Z z inn * outsideProd graph hAcyclic cpt X x Z z out =
      if inn = innOf Z z then outsideProd graph hAcyclic cpt X x Z z out else 0 := by
    intro inn
    rw [zIndicator_eq Z z inn]
    by_cases h : inn = innOf Z z
    · simp [h]
    · simp [h]
  simp_rw [hterm]
  exact Fintype.sum_ite_eq' (innOf Z z) (fun _ => outsideProd graph hAcyclic cpt X x Z z out)

/-- **Marginals that avoid `Z` ignore `do(Z)` when `Z` has no outside child.**

Every edge out of `Z` lands in `X ∪ Z`, and the summed set `S` is disjoint from
`Z`. The g-formula mass of `S` under `do(X, Z)` then equals the mass under
`do(X)`.
-/
theorem truncSlice_no_external_child [Inhabited β]
    {X Z S : Finset V}
    (hXZ : Disjoint X Z) (hSZ : Disjoint S Z)
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) S anchor =
      truncSlice graph hAcyclic cpt (doFinset X x) S anchor := by
  unfold truncSlice
  conv_lhs =>
    rw [sum_glue Z (fun f => if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) f else 0),
      Finset.sum_comm]
  conv_rhs =>
    rw [sum_glue Z (fun f => if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt (doFinset X x) f else 0),
      Finset.sum_comm]
  refine Finset.sum_congr rfl fun out _ => ?_
  have hagree : ∀ inn, agreesOn S anchor (glue Z inn out) =
      agreesOn S anchor (glue Z (innOf Z z) out) :=
    fun inn => agrees_glue_indep hSZ anchor inn (innOf Z z) out
  simp_rw [hagree]
  cases hbit : agreesOn S anchor (glue Z (innOf Z z) out)
  · rfl
  · simp only [ite_true]
    rw [sum_inn_doXZ graph hAcyclic hXZ hout0 cpt x z out,
      sum_inn_doX graph hAcyclic hXZ hout0 cpt x z out]

/-- **Rule 3 when `Z` has no child outside `X ∪ Z`.**

`P(y | do(x), do(z), w) = P(y | do(x), w)` for the g-formula masses. `Y` and
`W` are disjoint from `Z`, so neither side conditions on `Z`. Positivity is
the `do(x)` mass of `(x, w)`, and it is also the `do(x, z)` mass.
-/
theorem rule3_cond_of_no_external_child [Inhabited β]
    {X Y Z W : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z)
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ Y ∪ W) anchor /
        truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor =
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ W) anchor /
        truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor ∧
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor ≠ 0 := by
  have hdenS : Disjoint (X ∪ W) Z := by
    rw [Finset.disjoint_union_left]
    exact ⟨hXZ, hWZ⟩
  have hnumS : Disjoint (X ∪ Y ∪ W) Z := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨hXZ, hYZ⟩, hWZ⟩
  have hden := truncSlice_no_external_child graph hAcyclic hXZ hdenS hout0 cpt x z anchor
  have hnum :=
    truncSlice_no_external_child graph hAcyclic hXZ hnumS hout0 cpt x z anchor
  refine ⟨?_, ?_⟩
  · rw [hden, hnum]
  · rw [hden]
    exact hpos

/-! ## The same hypothesis isolates `Z` -/

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma directed_isolated
    {X Z : Finset V}
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    {u v : V}
    (hedge : (deleteIncoming (deleteIncoming graph X) Z).edges u v) :
    u ∉ Z ∧ v ∉ Z := by
  have hunion : (deleteIncoming graph (X ∪ Z)).edges u v :=
    (deleteIncoming_deleteIncoming_iff graph X Z u v).mp hedge
  have hvXZ : v ∉ X ∪ Z := hunion.2
  have hvZ : v ∉ Z := fun hv => hvXZ (Finset.mem_union.mpr (Or.inr hv))
  refine ⟨?_, hvZ⟩
  intro huZ
  exact hvXZ (hout0 u huZ v hunion.1)

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma undirected_isolated
    {X Z : Finset V}
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    {u v : V}
    (h : UndirectedEdge (deleteIncoming (deleteIncoming graph X) Z) u v) :
    u ∉ Z ∧ v ∉ Z := by
  rcases h with hdir | hrev
  · exact directed_isolated graph hout0 hdir
  · exact (directed_isolated graph hout0 hrev).symm

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma endpoint_outside
    {G : DirectedGraph V} {Z : Finset V} {cond : Set V} {p : List V}
    (hiso : ∀ {u v : V}, UndirectedEdge G u v → u ∉ Z ∧ v ∉ Z)
    (hact : ActiveTrail G cond p) :
    ∀ s e, PathEndpoints p = some (s, e) → s ≠ e → e ∉ Z :=
  ActiveTrail.rec
    (motive := fun p _ => ∀ s e, PathEndpoints p = some (s, e) → s ≠ e → e ∉ Z)
    (fun vtx s e hpe hne => by
      simp only [PathEndpoints] at hpe
      injection hpe with hpair
      have hs : s = vtx := ((Prod.ext_iff.mp hpair).1).symm
      have he : e = vtx := ((Prod.ext_iff.mp hpair).2).symm
      exact absurd (hs.trans he.symm) hne)
    (fun {u vNode} hedge s e hpe _ => by
      simp only [PathEndpoints, List.getLast_singleton] at hpe
      injection hpe with hpair
      have hev : e = vNode := ((Prod.ext_iff.mp hpair).2).symm
      exact hev ▸ (hiso hedge).2)
    (fun {a b c : V} {rest : List V} hab _ _ _ _ ih s e hpe hne => by
      have hsplit := pathEndpoints_of_cons (V := V) hpe
      by_cases hbe : b = e
      · exact hbe ▸ (hiso hab).2
      · exact ih b e hsplit.2 hbe)
    hact

omit [Fintype V] [DecidableRel graph.edges] in
/-- **With no outside child, `Z` is d-separated from every other set.**

In the graph with arrows into `X` and into `Z` deleted, no edge touches `Z`.
An active trail with distinct endpoints therefore cannot end in `Z`.
-/
theorem rule3_isolated_separated
    {X Z : Finset V}
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (Y conditioning : Set V) :
    DSeparatedFull (deleteIncoming (deleteIncoming graph X) Z)
      Y ((Z : Finset V) : Set V) conditioning := by
  intro y _ z hz hyz htrail
  rcases htrail with ⟨p, _, hpe, hact⟩
  have hiso : ∀ {u v : V},
      UndirectedEdge (deleteIncoming (deleteIncoming graph X) Z) u v → u ∉ Z ∧ v ∉ Z :=
    fun {_ _} h => undirected_isolated graph hout0 h
  exact endpoint_outside hiso hact y z hpe hyz (Finset.mem_coe.mp hz)

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma reachable_stays_in_Z
    {X Z : Finset V}
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    {u v : V} (hu : u ∈ Z)
    (hreach : (deleteIncoming graph X).Reachable u v) :
    v ∈ Z := by
  revert hu
  induction hreach with
  | refl =>
      intro hu
      exact hu
  | step hedge _ ih =>
      intro hu
      apply ih
      have hvXZ : _ ∈ X ∪ Z := hout0 _ hu _ hedge.1
      have hvX : _ ∉ X := hedge.2
      rcases Finset.mem_union.mp hvXZ with hvX' | hvZ
      · exact absurd hvX' hvX
      · exact hvZ

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma z_not_ancestor_of_outside
    {X Z W : Finset V}
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (hWZ : Disjoint W Z)
    {z w : V} (hz : z ∈ Z) (hw : w ∈ W) :
    z ∉ (deleteIncoming graph X).ancestors w := by
  intro hanc
  rcases hanc with ⟨hreach, _⟩
  exact Finset.disjoint_left.mp hWZ hw
    (reachable_stays_in_Z graph hout0 hz hreach)

/-- Nodes of `Z` that are not ancestors of `W` after the arrows into `X` are deleted. -/
def zOf (X Z W : Finset V) : Set V :=
  {z | z ∈ (Z : Set V) ∧ ∀ w ∈ (W : Set V), z ∉ (deleteIncoming graph X).ancestors w}

omit [Fintype V] [DecidableRel graph.edges] in
/-- **Under no outside child, `Z(W)` is all of `Z` whenever `W` misses `Z`.** -/
theorem zOf_eq_of_no_external_child
    {X Z W : Finset V}
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (hWZ : Disjoint W Z) :
    zOf graph X Z W = ((Z : Finset V) : Set V) := by
  ext z
  constructor
  · intro hz
    exact hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    intro w hw
    exact z_not_ancestor_of_outside graph hout0 hWZ (Finset.mem_coe.mp hz) (Finset.mem_coe.mp hw)

end Mettapedia.GSLT.Causality.DoCalculus
