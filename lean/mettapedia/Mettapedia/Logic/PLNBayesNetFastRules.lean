import Mettapedia.Logic.PLNDerivation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
import Mettapedia.ProbabilityTheory.BayesianNetworks.ScreeningOffFromCondIndep

/-!
# Bayesian Networks as a Tractable Sublayer: Exactness Conditions for Fast PLN Deduction

This file starts turning the “fast PLN rules” into *theorems* relative to a Bayes-net world-model
class.

In a chain BN `A → B → C`, the standard PLN *deduction* strength formula is exact under the
screening-off assumptions `P(C | A ∩ B) = P(C | B)` and `P(C | A ∩ Bᶜ) = P(C | Bᶜ)`.

For Bayesian networks, these assumptions arise from the graph structure (d-separation / Markov
properties).  A general d-separation soundness theorem is a larger project; here we prove the
chain case directly from the BN product-form semantics.
-/

noncomputable section

namespace Mettapedia.Logic.PLNBayesNetFastRules

open scoped Classical BigOperators ENNReal

open MeasureTheory ProbabilityTheory Set

open Mettapedia.Logic.PLN
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.DiscreteCPT
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

/-! ## The 3-node chain BN and its joint measure -/

abbrev ChainBN : BayesianNetwork Three := chainBN

namespace ChainBN

instance (v : Three) : Fintype (ChainBN.stateSpace v) :=
  inferInstanceAs (Fintype Bool)

instance (v : Three) : Nonempty (ChainBN.stateSpace v) :=
  inferInstanceAs (Nonempty Bool)

instance (v : Three) : MeasurableSingletonClass (ChainBN.stateSpace v) :=
  inferInstanceAs (MeasurableSingletonClass Bool)

variable (cpt : ChainBN.DiscreteCPT)

noncomputable abbrev μ (cpt : ChainBN.DiscreteCPT) : Measure ChainBN.JointSpace :=
  cpt.jointMeasure

instance (cpt : ChainBN.DiscreteCPT) : IsProbabilityMeasure (μ (cpt := cpt)) :=
  jointMeasure_isProbabilityMeasure (bn := ChainBN) cpt

/-! ## Events A,B,C as cylinder sets on the joint sample space -/

abbrev eventTrue (v : Three) : Set ChainBN.JointSpace :=
  (fun ω : ChainBN.JointSpace => ω v) ⁻¹'
    ({(show ChainBN.stateSpace v from true)} : Set (ChainBN.stateSpace v))

abbrev A : Set ChainBN.JointSpace := eventTrue Three.A
abbrev B : Set ChainBN.JointSpace := eventTrue Three.B
abbrev C : Set ChainBN.JointSpace := eventTrue Three.C

lemma measurable_eventTrue (v : Three) : MeasurableSet (eventTrue v) := by
  have hproj : Measurable (fun ω : ChainBN.JointSpace => ω v) := by
    fun_prop
  have hsing : MeasurableSet
      ({(show ChainBN.stateSpace v from true)} : Set (ChainBN.stateSpace v)) := by
    simp
  simpa [eventTrue] using hsing.preimage hproj

lemma measurable_A : MeasurableSet (A : Set ChainBN.JointSpace) :=
  measurable_eventTrue Three.A

lemma measurable_B : MeasurableSet (B : Set ChainBN.JointSpace) :=
  measurable_eventTrue Three.B

lemma measurable_C : MeasurableSet (C : Set ChainBN.JointSpace) :=
  measurable_eventTrue Three.C

/-! ## Joint-measure evaluation as a finite sum (PMF semantics) -/

lemma jointMeasure_apply (S : Set ChainBN.JointSpace) (hS : MeasurableSet S) :
    (μ (cpt := cpt)) S = ∑ ω : ChainBN.JointSpace, S.indicator cpt.jointWeight ω := by
  classical
  -- `jointMeasure` is `PMF.toMeasure`, so its value is a `tsum` of an indicator; on finite types, this is a sum.
  -- (We keep the statement in terms of `jointWeight`, since `jointPMF` coerces to it.)
  dsimp [μ]
  -- Unfold `jointMeasure` to the underlying `PMF.toMeasure`.
  dsimp [DiscreteCPT.jointMeasure]
  -- Expand `toMeasure_apply`.
  rw [PMF.toMeasure_apply (p := cpt.jointPMF) (s := S) hS]
  -- Convert the `tsum` to a finite sum over `Finset.univ`.
  rw [tsum_eq_sum (s := (Finset.univ : Finset ChainBN.JointSpace))
        (fun x hx => (hx (Finset.mem_univ x)).elim)]
  -- `Fintype.sum` is `Finset.univ.sum`.
  rfl

/-! ## Chain structure: C is a sink -/

lemma chainGraph_isSink_C : ChainBN.graph.IsSink Three.C := by
  -- In the chain graph, there are no outgoing edges from `C`.
  change chainGraph.IsSink Three.C
  rw [DirectedGraph.isSink_iff]
  intro w
  simp [chainGraph]

/-! ## Splitting configurations at the sink coordinate `C` -/

namespace SplitAtC

abbrev Rest : Type :=
  (v : { v : Three // v ≠ Three.C }) → ChainBN.stateSpace v.val

noncomputable abbrev cfg (c : ChainBN.stateSpace Three.C) (r : Rest) : ChainBN.JointSpace :=
  (Equiv.piSplitAt Three.C ChainBN.stateSpace).symm (c, r)

lemma cfg_apply_C (c : ChainBN.stateSpace Three.C) (r : Rest) : cfg c r Three.C = c := by
  simp [cfg, Equiv.piSplitAt_symm_apply]

lemma cfg_apply_of_ne_C {v : Three} (hv : v ≠ Three.C) (c : ChainBN.stateSpace Three.C) (r : Rest) :
    cfg c r v = r ⟨v, hv⟩ := by
  simp [cfg, Equiv.piSplitAt_symm_apply, hv]

lemma sum_piSplitAtC (f : ChainBN.JointSpace → ℝ≥0∞) :
    (∑ ω : ChainBN.JointSpace, f ω) =
      ∑ c : Bool, ∑ r : Rest, f (cfg c r) := by
  classical
  -- Sum over `JointSpace` via the equivalence `piSplitAt`, then split the product type.
  have h :
      (∑ ω : ChainBN.JointSpace, f ω) =
        ∑ p : ChainBN.stateSpace Three.C × Rest, f (cfg p.1 p.2) := by
    refine Fintype.sum_equiv (Equiv.piSplitAt Three.C ChainBN.stateSpace) f
      (fun p => f (cfg p.1 p.2)) ?_
    intro ω
    -- `piSplitAt` is an equivalence; unfold `cfg` and use `symm_apply_apply`.
    simpa [cfg] using
      congrArg f
        (Equiv.symm_apply_apply (Equiv.piSplitAt Three.C ChainBN.stateSpace) ω).symm
  calc
    (∑ ω : ChainBN.JointSpace, f ω) = ∑ p : ChainBN.stateSpace Three.C × Rest, f (cfg p.1 p.2) := h
    _ = ∑ c : Bool, ∑ r : Rest, f (cfg c r) := by
        -- `Fintype.sum_prod_type` turns the sum over pairs into a nested sum.
        change (∑ p : ChainBN.stateSpace Three.C × Rest, f (cfg p.1 p.2)) =
          ∑ c : ChainBN.stateSpace Three.C, ∑ r : Rest, f (cfg c r)
        simpa using
          (Fintype.sum_prod_type (f := fun p : ChainBN.stateSpace Three.C × Rest => f (cfg p.1 p.2)))

/-! ## Product-form lemmas specialized to the sink coordinate `C` -/

abbrev idxA : { v : Three // v ≠ Three.C } := ⟨Three.A, by decide⟩
abbrev idxB : { v : Three // v ≠ Three.C } := ⟨Three.B, by decide⟩

lemma cfg_apply_A (c : ChainBN.stateSpace Three.C) (r : Rest) :
    cfg c r Three.A = r idxA := by
  change cfg c r Three.A = r ⟨Three.A, idxA.property⟩
  exact cfg_apply_of_ne_C (v := Three.A) idxA.property c r

lemma cfg_apply_B (c : ChainBN.stateSpace Three.C) (r : Rest) :
    cfg c r Three.B = r idxB := by
  change cfg c r Three.B = r ⟨Three.B, idxB.property⟩
  exact cfg_apply_of_ne_C (v := Three.B) idxB.property c r

noncomputable def prodNonC (c : ChainBN.stateSpace Three.C) (r : Rest) : ℝ≥0∞ :=
  ∏ v : { v : Three // v ≠ Three.C }, nodeProb cpt (cfg c r) v.val

lemma cfg_eq_update (c c' : ChainBN.stateSpace Three.C) (r : Rest) :
    cfg c' r = Function.update (cfg c r) Three.C c' := by
  ext v
  by_cases hv : v = Three.C
  · subst hv
    simp [cfg, Equiv.piSplitAt_symm_apply]
  · have hv' : v ≠ Three.C := hv
    simp [cfg_apply_of_ne_C (v := v) hv' c r, cfg_apply_of_ne_C (v := v) hv' c' r, hv]

lemma prodNonC_indep (hs : ChainBN.graph.IsSink Three.C) (c c' : ChainBN.stateSpace Three.C) (r : Rest) :
    prodNonC (cpt := cpt) (c := c) r = prodNonC (cpt := cpt) (c := c') r := by
  classical
  unfold prodNonC
  -- Change `c` to `c'` by an `update` at the sink coordinate.
  have hcfg : cfg c' r = Function.update (cfg c r) Three.C c' :=
    cfg_eq_update (c := c) (c' := c') r
  -- Each factor for `v ≠ C` is unchanged.
  refine Fintype.prod_congr _ _ (fun v => ?_)
  have hv : v.val ≠ Three.C := v.property
  -- Rewrite the LHS config as an update of the RHS.
  simpa [hcfg] using
    (nodeProb_update_sink (bn := ChainBN) (cpt := cpt) Three.C hs v.val hv (cfg c r) c').symm

lemma jointWeight_split_C (c : ChainBN.stateSpace Three.C) (r : Rest) :
    cpt.jointWeight (cfg c r) =
      nodeProb cpt (cfg c r) Three.C * prodNonC (cpt := cpt) (c := c) r := by
  classical
  -- Split the product over all vertices into `C` and `v ≠ C`.
  unfold DiscreteCPT.jointWeight prodNonC
  -- `∏ v, f v = (∏ v≠C, f v) * f C`
  -- via `Fintype.prod_subtype_mul_prod_subtype`.
  have hsplit : (∏ v : Three, nodeProb cpt (cfg c r) v) =
      (∏ v : { v : Three // v ≠ Three.C }, nodeProb cpt (cfg c r) v.val) *
        (∏ v : { v : Three // ¬(v ≠ Three.C) }, nodeProb cpt (cfg c r) v.val) := by
    simpa using
      (Fintype.prod_subtype_mul_prod_subtype (p := fun v : Three => v ≠ Three.C)
        (f := fun v : Three => nodeProb cpt (cfg c r) v)).symm
  -- The second factor is a product over a singleton subtype `{v // v = C}`.
  have h_unique : Unique { v : Three // ¬(v ≠ Three.C) } := by
    refine ⟨⟨Three.C, ?_⟩, ?_⟩
    · simp
    · intro x
      ext
      -- `¬(x.val ≠ C)` implies `x.val = C`.
      have : x.val = Three.C := by
        have hx : ¬(x.val ≠ Three.C) := x.property
        simpa using (not_not.mp hx)
      exact this
  haveI : Unique { v : Three // ¬(v ≠ Three.C) } := h_unique
  have hC : (∏ v : { v : Three // ¬(v ≠ Three.C) }, nodeProb cpt (cfg c r) v.val) =
      nodeProb cpt (cfg c r) Three.C := by
    classical
    -- Product over a `Unique` type is just the single value; identify `default` with `C`.
    have hprod :
        (∏ v : { v : Three // ¬(v ≠ Three.C) }, nodeProb cpt (cfg c r) v.val) =
          nodeProb cpt (cfg c r) (default : { v : Three // ¬(v ≠ Three.C) }).val := by
      simp
    have hdef : (default : { v : Three // ¬(v ≠ Three.C) }).val = Three.C := by
      have : (default : { v : Three // ¬(v ≠ Three.C) }) = ⟨Three.C, by simp⟩ :=
        Subsingleton.elim _ _
      simpa using congrArg Subtype.val this
    rw [hdef] at hprod
    exact hprod
  -- Put it together, commuting the multiplication to match the statement.
  -- (The product split lemma gives `(prodNonC) * (nodeProb C)`; we want `nodeProb C * prodNonC`.)
  calc
    (∏ v : Three, nodeProb cpt (cfg c r) v) =
        (∏ v : { v : Three // v ≠ Three.C }, nodeProb cpt (cfg c r) v.val) *
          (∏ v : { v : Three // ¬(v ≠ Three.C) }, nodeProb cpt (cfg c r) v.val) := hsplit
    _ = (∏ v : { v : Three // v ≠ Three.C }, nodeProb cpt (cfg c r) v.val) *
          nodeProb cpt (cfg c r) Three.C := by
      rw [hC]
    _ = nodeProb cpt (cfg c r) Three.C *
          (∏ v : { v : Three // v ≠ Three.C }, nodeProb cpt (cfg c r) v.val) := by
      rw [mul_comm]


end SplitAtC

/-! ## Screening-off in the chain BN (C ⟂ A | B)

The PLN measure-theoretic deduction theorem assumes two screening-off equalities:

* `P(C | A ∩ B) = P(C | B)` and
* `P(C | A ∩ Bᶜ) = P(C | Bᶜ)`.

In a chain Bayesian network `A → B → C`, these follow from the BN factorization: the CPT row for
`C` depends only on `B`, so once `B` is fixed, changing `A` does not change the conditional
distribution of `C`.

We prove the required equalities for the cylinder events `A,B,C` defined above, and then package
them into an exactness theorem for the PLN deduction strength formula.
-/

namespace ScreeningOff

open SplitAtC

variable (cpt : ChainBN.DiscreteCPT)

noncomputable def restB (b : Bool) : Rest :=
  fun v => if v = idxB then b else false

lemma restB_idxB (b : Bool) : restB b idxB = b := by
  classical
  simp [restB]

lemma nodeProb_C_eq_of_B_eq (c : Bool) {r r' : Rest} (hB : r idxB = r' idxB) :
    nodeProb cpt (cfg c r) Three.C = nodeProb cpt (cfg c r') Three.C := by
  classical
  unfold DiscreteCPT.nodeProb
  -- Reduce to equality of parent-assignment functions for `C`.
  rw [cfg_apply_C, cfg_apply_C]
  have hpa : cpt.parentAssignOfConfig (cfg c r) Three.C = cpt.parentAssignOfConfig (cfg c r') Three.C := by
    funext u hu
    have hu' : u = Three.B := by
      simpa [ChainBN, chain_parents_C] using hu
    subst hu'
    simp [DiscreteCPT.parentAssignOfConfig, hB]
  simp [hpa]

noncomputable def qC_givenB (b : Bool) : ℝ≥0∞ :=
  nodeProb cpt (cfg true (restB b)) Three.C

lemma nodeProb_C_true_eq_qC_givenB {r : Rest} {b : Bool} (hb : r idxB = b) :
    nodeProb cpt (cfg true r) Three.C = qC_givenB (cpt := cpt) b := by
  classical
  -- Replace `r` by the canonical rest assignment that agrees on `B`.
  have hb' : r idxB = (restB b) idxB := by
    simp [restB, hb]
  simpa [qC_givenB] using nodeProb_C_eq_of_B_eq (cpt := cpt) (c := true) hb'

end ScreeningOff

/-! ## Exactness of fast PLN deduction (chain BN) -/

namespace Deduction

open SplitAtC

variable (cpt : ChainBN.DiscreteCPT)

private lemma mu_B_eq_sum_rest :
    (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) =
      ∑ r : Rest,
        (if r idxB = true then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
  classical
  -- Evaluate the joint measure as a finite sum over configurations.
  rw [jointMeasure_apply (cpt := cpt) (S := (B : Set ChainBN.JointSpace)) (hS := measurable_B)]
  -- Split the sum into the `C` coordinate and the rest.
  rw [sum_piSplitAtC (f := fun ω => (B : Set ChainBN.JointSpace).indicator cpt.jointWeight ω)]
  -- Simplify membership in `B`: it depends only on the `B` coordinate (i.e. on `r idxB`).
  simp [B, eventTrue, Set.indicator]
  calc
    ((∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg true r) else 0) +
        ∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg false r) else 0) =
      ∑ r : Rest,
        ((if r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          (if r idxB = true then cpt.jointWeight (cfg false r) else 0)) := by
      simpa [idxB] using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest => if r idxB = true then cpt.jointWeight (cfg true r) else 0)
          (g := fun r : Rest => if r idxB = true then cpt.jointWeight (cfg false r) else 0)).symm
    _ = ∑ r : Rest,
        (if r idxB = true then cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r) else 0) := by
      refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
      by_cases h : r idxB = true <;> simp [h]

private lemma mu_C_inter_B_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)) =
      ∑ r : Rest, (if r idxB = true then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (B : Set ChainBN.JointSpace))
        (hS := measurable_C.inter measurable_B)]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (B : Set ChainBN.JointSpace)).indicator cpt.jointWeight ω)]
  -- Only the `c = true` summand contributes to `C`.
  simp [C, B, eventTrue, Set.indicator]

private lemma mu_Bc_eq_sum_rest :
    (μ (cpt := cpt)) ((B : Set ChainBN.JointSpace)ᶜ) =
      ∑ r : Rest,
        (if r idxB = false then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := (B : Set ChainBN.JointSpace)ᶜ)
        (hS := measurable_B.compl)]
  rw [sum_piSplitAtC (f := fun ω => ((B : Set ChainBN.JointSpace)ᶜ).indicator cpt.jointWeight ω)]
  simp [B, eventTrue, Set.indicator]
  calc
    ((∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg true r)) +
        ∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg false r)) =
      ∑ r : Rest,
        ((if r idxB = true then 0 else cpt.jointWeight (cfg true r)) +
          (if r idxB = true then 0 else cpt.jointWeight (cfg false r))) := by
      simpa [idxB] using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest => if r idxB = true then 0 else cpt.jointWeight (cfg true r))
          (g := fun r : Rest => if r idxB = true then 0 else cpt.jointWeight (cfg false r))).symm
    _ = ∑ r : Rest,
        (if r idxB = true then 0 else
            (cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r))) := by
      refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
      by_cases h : r idxB = true <;> simp [h]
    _ = ∑ r : Rest,
        (if r idxB = false then cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r) else 0) := by
      refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
      cases hb : r idxB <;> simp

private lemma mu_C_inter_Bc_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)ᶜ) =
      ∑ r : Rest, (if r idxB = false then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (B : Set ChainBN.JointSpace)ᶜ)
        (hS := measurable_C.inter measurable_B.compl)]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (B : Set ChainBN.JointSpace)ᶜ).indicator cpt.jointWeight ω)]
  simp [C, B, eventTrue, Set.indicator]
  refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
  cases hb : r idxB <;> simp

private lemma mu_A_inter_B_eq_sum_rest :
    (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) =
      ∑ r : Rest,
        (if r idxA = true ∧ r idxB = true then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := A ∩ (B : Set ChainBN.JointSpace))
        (hS := measurable_A.inter measurable_B)]
  rw [sum_piSplitAtC (f := fun ω => (A ∩ (B : Set ChainBN.JointSpace)).indicator cpt.jointWeight ω)]
  simp [A, B, eventTrue, Set.indicator]
  calc
    ((∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) +
        ∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg false r) else 0) =
      ∑ r : Rest,
        ((if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          (if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg false r) else 0)) := by
      simpa [idxA, idxB] using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest =>
            if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0)
          (g := fun r : Rest =>
            if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg false r) else 0)).symm
    _ = ∑ r : Rest,
        (if r idxA = true ∧ r idxB = true then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
      refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
      by_cases h : r idxA = true ∧ r idxB = true <;> simp [h]

private lemma mu_C_inter_A_inter_B_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace))) =
      ∑ r : Rest, (if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (A ∩ (B : Set ChainBN.JointSpace)))
        (hS := measurable_C.inter (measurable_A.inter measurable_B))]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (A ∩ (B : Set ChainBN.JointSpace))).indicator cpt.jointWeight ω)]
  simp [C, A, B, eventTrue, Set.indicator]

private lemma mu_A_inter_Bc_eq_sum_rest :
    (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) =
      ∑ r : Rest,
        (if r idxA = true ∧ r idxB = false then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := A ∩ (B : Set ChainBN.JointSpace)ᶜ)
        (hS := measurable_A.inter measurable_B.compl)]
  rw [sum_piSplitAtC (f := fun ω => (A ∩ (B : Set ChainBN.JointSpace)ᶜ).indicator cpt.jointWeight ω)]
  simp [A, B, eventTrue, Set.indicator]
  -- Normalize `¬ r idxB = true` into `r idxB = false`.
  have hnormB (c : Bool) (r : Rest) :
      (if r idxA = true ∧ ¬r idxB = true then cpt.jointWeight (cfg c r) else 0) =
        (if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg c r) else 0) := by
    by_cases hA : r idxA = true
    · cases hb : r idxB <;> simp [hA]
    · simp [hA]
  simp_rw [hnormB]
  calc
    ((∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) +
        ∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg false r) else 0) =
      ∑ r : Rest,
        ((if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) +
          (if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg false r) else 0)) := by
      simpa [idxA, idxB] using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest =>
            if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0)
          (g := fun r : Rest =>
            if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg false r) else 0)).symm
    _ = ∑ r : Rest,
        (if r idxA = true ∧ r idxB = false then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
      refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
      by_cases h : r idxA = true ∧ r idxB = false <;> simp [h]

private lemma mu_C_inter_A_inter_Bc_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)) =
      ∑ r : Rest, (if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ))
        (hS := measurable_C.inter (measurable_A.inter measurable_B.compl))]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)).indicator cpt.jointWeight ω)]
  simp [C, A, B, eventTrue, Set.indicator]
  refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
  cases hA : r idxA <;> cases hb : r idxB <;> simp

/-! ### Screening-off equalities as BN theorems -/

open ScreeningOff

private lemma nodeProb_C_true_add_false (r : Rest) :
    nodeProb cpt (cfg true r) Three.C + nodeProb cpt (cfg false r) Three.C = 1 := by
  classical
  -- Fix the parent assignment for `C`; it depends only on `B` in the chain BN.
  let pa : ChainBN.ParentAssignment Three.C :=
    cpt.parentAssignOfConfig (cfg true r) Three.C
  have hpa : cpt.parentAssignOfConfig (cfg false r) Three.C = pa := by
    funext u hu
    have hu' : u = Three.B := by
      simpa [ChainBN, chain_parents_C] using hu
    subst hu'
    simp [pa, DiscreteCPT.parentAssignOfConfig]
  have hsum : (∑ c : Bool, (cpt.cpt Three.C pa c : ℝ≥0∞)) = 1 :=
    pmf_sum_eq_one (cpt.cpt Three.C pa)
  have hsum' :
      (cpt.cpt Three.C pa true : ℝ≥0∞) + (cpt.cpt Three.C pa false : ℝ≥0∞) = 1 := by
    simpa [Fintype.sum_bool] using hsum
  -- Expand `nodeProb` and rewrite parent assignments to `pa`.
  simpa [DiscreteCPT.nodeProb, cfg_apply_C, pa, hpa] using hsum'

private lemma mu_B_eq_sum_prodNonC :
    (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) =
      ∑ r : Rest, (if r idxB = true then prodNonC (cpt := cpt) (c := true) r else 0) := by
  classical
  rw [mu_B_eq_sum_rest (cpt := cpt)]
  refine Fintype.sum_congr _ _ (fun r => ?_)
  by_cases hb : r idxB = true
  · simp [hb]
    have hprod :
        prodNonC (cpt := cpt) (c := false) r = prodNonC (cpt := cpt) (c := true) r := by
      simpa using
        prodNonC_indep (cpt := cpt) (hs := chainGraph_isSink_C) (c := false) (c' := true) r
    calc
      (cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)) =
          (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := false) r) := by
        simp [jointWeight_split_C (cpt := cpt) (c := true) r, jointWeight_split_C (cpt := cpt) (c := false) r]
      _ = (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := true) r) := by
        simp [hprod]
      _ = (nodeProb cpt (cfg true r) Three.C + nodeProb cpt (cfg false r) Three.C) *
            prodNonC (cpt := cpt) (c := true) r := by
        simpa using
          (add_mul (nodeProb cpt (cfg true r) Three.C) (nodeProb cpt (cfg false r) Three.C)
            (prodNonC (cpt := cpt) (c := true) r)).symm
      _ = prodNonC (cpt := cpt) (c := true) r := by
        simp [nodeProb_C_true_add_false (cpt := cpt) r]
  · simp [hb]

private lemma mu_C_inter_B_eq_q_mul_mu_B :
    (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)) =
      qC_givenB (cpt := cpt) true * (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) := by
  classical
  -- Reduce both sides to the same `Rest`-sum and use the product-form semantics.
  rw [mu_C_inter_B_eq_sum_rest (cpt := cpt)]
  rw [mu_B_eq_sum_prodNonC (cpt := cpt)]
  -- Factor out `qC_givenB true` from the sum.
  let g : Rest → ℝ≥0∞ := fun r => if r idxB = true then prodNonC (cpt := cpt) (c := true) r else 0
  have hrewrite :
      (∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest, if r idxB = true then qC_givenB (cpt := cpt) true * prodNonC (cpt := cpt) (c := true) r else 0 := by
    refine Fintype.sum_congr (α := Rest) (M := ℝ≥0∞) _ _ (fun r => ?_)
    by_cases hb : r idxB = true
    · have hnode : nodeProb cpt (cfg true r) Three.C = qC_givenB (cpt := cpt) true := by
        simpa using
          nodeProb_C_true_eq_qC_givenB (cpt := cpt) (r := r) (b := true) hb
      simp [hb, jointWeight_split_C (cpt := cpt) (c := true) r, hnode]
    · simp [hb]
  -- Rewrite each summand as `q * g r`, then use `Finset.mul_sum`.
  calc
    (∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest, if r idxB = true then qC_givenB (cpt := cpt) true * prodNonC (cpt := cpt) (c := true) r else 0 := hrewrite
    _ = ∑ r : Rest, qC_givenB (cpt := cpt) true * g r := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases hb : r idxB = true <;> simp [g, hb]
    _ = qC_givenB (cpt := cpt) true * ∑ r : Rest, g r := by
      simpa using
        (Finset.mul_sum (a := qC_givenB (cpt := cpt) true) (s := (Finset.univ : Finset Rest)) (f := g)).symm
    _ = qC_givenB (cpt := cpt) true * ∑ r : Rest, if r idxB = true then prodNonC (cpt := cpt) (c := true) r else 0 := by
      rfl

private lemma mu_Bc_eq_sum_prodNonC :
    (μ (cpt := cpt)) ((B : Set ChainBN.JointSpace)ᶜ) =
      ∑ r : Rest, (if r idxB = false then prodNonC (cpt := cpt) (c := true) r else 0) := by
  classical
  rw [mu_Bc_eq_sum_rest (cpt := cpt)]
  refine Fintype.sum_congr _ _ (fun r => ?_)
  by_cases hb : r idxB = false
  · simp [hb]
    have hprod :
        prodNonC (cpt := cpt) (c := false) r = prodNonC (cpt := cpt) (c := true) r := by
      simpa using
        prodNonC_indep (cpt := cpt) (hs := chainGraph_isSink_C) (c := false) (c' := true) r
    calc
      (cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)) =
          (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := false) r) := by
        simp [jointWeight_split_C (cpt := cpt) (c := true) r, jointWeight_split_C (cpt := cpt) (c := false) r]
      _ = (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := true) r) := by
        simp [hprod]
      _ = (nodeProb cpt (cfg true r) Three.C + nodeProb cpt (cfg false r) Three.C) *
            prodNonC (cpt := cpt) (c := true) r := by
        simpa using
          (add_mul (nodeProb cpt (cfg true r) Three.C) (nodeProb cpt (cfg false r) Three.C)
            (prodNonC (cpt := cpt) (c := true) r)).symm
      _ = prodNonC (cpt := cpt) (c := true) r := by
        simp [nodeProb_C_true_add_false (cpt := cpt) r]
  · simp [hb]

private lemma mu_C_inter_Bc_eq_q_mul_mu_Bc :
    (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)ᶜ) =
      qC_givenB (cpt := cpt) false * (μ (cpt := cpt)) ((B : Set ChainBN.JointSpace)ᶜ) := by
  classical
  rw [mu_C_inter_Bc_eq_sum_rest (cpt := cpt)]
  rw [mu_Bc_eq_sum_prodNonC (cpt := cpt)]
  let g : Rest → ℝ≥0∞ := fun r => if r idxB = false then prodNonC (cpt := cpt) (c := true) r else 0
  have hrewrite :
      (∑ r : Rest, if r idxB = false then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest, if r idxB = false then qC_givenB (cpt := cpt) false * prodNonC (cpt := cpt) (c := true) r else 0 := by
    refine Fintype.sum_congr _ _ (fun r => ?_)
    by_cases hb : r idxB = false
    · have hnode : nodeProb cpt (cfg true r) Three.C = qC_givenB (cpt := cpt) false := by
        simpa using
          nodeProb_C_true_eq_qC_givenB (cpt := cpt) (r := r) (b := false) hb
      simp [hb, jointWeight_split_C (cpt := cpt) (c := true) r, hnode]
    · simp [hb]
  calc
    (∑ r : Rest, if r idxB = false then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest, if r idxB = false then qC_givenB (cpt := cpt) false * prodNonC (cpt := cpt) (c := true) r else 0 := hrewrite
    _ = ∑ r : Rest, qC_givenB (cpt := cpt) false * g r := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases hb : r idxB = false <;> simp [g, hb]
    _ = qC_givenB (cpt := cpt) false * ∑ r : Rest, g r := by
      simpa using
        (Finset.mul_sum (a := qC_givenB (cpt := cpt) false) (s := (Finset.univ : Finset Rest)) (f := g)).symm
    _ = qC_givenB (cpt := cpt) false * ∑ r : Rest, if r idxB = false then prodNonC (cpt := cpt) (c := true) r else 0 := by
      rfl

private lemma mu_A_inter_B_eq_sum_prodNonC :
    (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) =
      ∑ r : Rest,
        (if r idxA = true ∧ r idxB = true then prodNonC (cpt := cpt) (c := true) r else 0) := by
  classical
  rw [mu_A_inter_B_eq_sum_rest (cpt := cpt)]
  refine Fintype.sum_congr _ _ (fun r => ?_)
  by_cases hAB : r idxA = true ∧ r idxB = true
  · simp [hAB]
    have hprod :
        prodNonC (cpt := cpt) (c := false) r = prodNonC (cpt := cpt) (c := true) r := by
      simpa using
        prodNonC_indep (cpt := cpt) (hs := chainGraph_isSink_C) (c := false) (c' := true) r
    calc
      (cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)) =
          (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := false) r) := by
        simp [jointWeight_split_C (cpt := cpt) (c := true) r, jointWeight_split_C (cpt := cpt) (c := false) r]
      _ = (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := true) r) := by
        simp [hprod]
      _ = (nodeProb cpt (cfg true r) Three.C + nodeProb cpt (cfg false r) Three.C) *
            prodNonC (cpt := cpt) (c := true) r := by
        simpa using
          (add_mul (nodeProb cpt (cfg true r) Three.C) (nodeProb cpt (cfg false r) Three.C)
            (prodNonC (cpt := cpt) (c := true) r)).symm
      _ = prodNonC (cpt := cpt) (c := true) r := by
        simp [nodeProb_C_true_add_false (cpt := cpt) r]
  · simp [hAB]

private lemma mu_C_inter_A_inter_B_eq_q_mul_mu_A_inter_B :
    (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace))) =
      qC_givenB (cpt := cpt) true * (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) := by
  classical
  rw [mu_C_inter_A_inter_B_eq_sum_rest (cpt := cpt)]
  rw [mu_A_inter_B_eq_sum_prodNonC (cpt := cpt)]
  let g : Rest → ℝ≥0∞ := fun r =>
    if r idxA = true ∧ r idxB = true then prodNonC (cpt := cpt) (c := true) r else 0
  have hrewrite :
      (∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest,
          if r idxA = true ∧ r idxB = true then
            qC_givenB (cpt := cpt) true * prodNonC (cpt := cpt) (c := true) r
          else 0 := by
    refine Fintype.sum_congr _ _ (fun r => ?_)
    by_cases hAB : r idxA = true ∧ r idxB = true
    · have hb : r idxB = true := hAB.2
      have hnode : nodeProb cpt (cfg true r) Three.C = qC_givenB (cpt := cpt) true := by
        simpa using
          nodeProb_C_true_eq_qC_givenB (cpt := cpt) (r := r) (b := true) hb
      simp [hAB, jointWeight_split_C (cpt := cpt) (c := true) r, hnode]
    · simp [hAB]
  calc
    (∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest,
          if r idxA = true ∧ r idxB = true then
            qC_givenB (cpt := cpt) true * prodNonC (cpt := cpt) (c := true) r
          else 0 := hrewrite
    _ = ∑ r : Rest, qC_givenB (cpt := cpt) true * g r := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases hAB : r idxA = true ∧ r idxB = true <;> simp [g, hAB]
    _ = qC_givenB (cpt := cpt) true * ∑ r : Rest, g r := by
      simpa using
        (Finset.mul_sum (a := qC_givenB (cpt := cpt) true) (s := (Finset.univ : Finset Rest)) (f := g)).symm
    _ = qC_givenB (cpt := cpt) true *
          ∑ r : Rest, if r idxA = true ∧ r idxB = true then prodNonC (cpt := cpt) (c := true) r else 0 := by
      rfl

private lemma mu_A_inter_Bc_eq_sum_prodNonC :
    (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) =
      ∑ r : Rest,
        (if r idxA = true ∧ r idxB = false then prodNonC (cpt := cpt) (c := true) r else 0) := by
  classical
  rw [mu_A_inter_Bc_eq_sum_rest (cpt := cpt)]
  refine Fintype.sum_congr _ _ (fun r => ?_)
  by_cases hABc : r idxA = true ∧ r idxB = false
  · simp [hABc]
    have hprod :
        prodNonC (cpt := cpt) (c := false) r = prodNonC (cpt := cpt) (c := true) r := by
      simpa using
        prodNonC_indep (cpt := cpt) (hs := chainGraph_isSink_C) (c := false) (c' := true) r
    calc
      (cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)) =
          (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := false) r) := by
        simp [jointWeight_split_C (cpt := cpt) (c := true) r, jointWeight_split_C (cpt := cpt) (c := false) r]
      _ = (nodeProb cpt (cfg true r) Three.C * prodNonC (cpt := cpt) (c := true) r) +
            (nodeProb cpt (cfg false r) Three.C * prodNonC (cpt := cpt) (c := true) r) := by
        simp [hprod]
      _ = (nodeProb cpt (cfg true r) Three.C + nodeProb cpt (cfg false r) Three.C) *
            prodNonC (cpt := cpt) (c := true) r := by
        simpa using
          (add_mul (nodeProb cpt (cfg true r) Three.C) (nodeProb cpt (cfg false r) Three.C)
            (prodNonC (cpt := cpt) (c := true) r)).symm
      _ = prodNonC (cpt := cpt) (c := true) r := by
        simp [nodeProb_C_true_add_false (cpt := cpt) r]
  · simp [hABc]

private lemma mu_C_inter_A_inter_Bc_eq_q_mul_mu_A_inter_Bc :
    (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)) =
      qC_givenB (cpt := cpt) false * (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) := by
  classical
  rw [mu_C_inter_A_inter_Bc_eq_sum_rest (cpt := cpt)]
  rw [mu_A_inter_Bc_eq_sum_prodNonC (cpt := cpt)]
  let g : Rest → ℝ≥0∞ := fun r =>
    if r idxA = true ∧ r idxB = false then prodNonC (cpt := cpt) (c := true) r else 0
  have hrewrite :
      (∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest,
          if r idxA = true ∧ r idxB = false then
            qC_givenB (cpt := cpt) false * prodNonC (cpt := cpt) (c := true) r
          else 0 := by
    refine Fintype.sum_congr _ _ (fun r => ?_)
    by_cases hABc : r idxA = true ∧ r idxB = false
    · have hb : r idxB = false := hABc.2
      have hnode : nodeProb cpt (cfg true r) Three.C = qC_givenB (cpt := cpt) false := by
        simpa using
          nodeProb_C_true_eq_qC_givenB (cpt := cpt) (r := r) (b := false) hb
      simp [hABc, jointWeight_split_C (cpt := cpt) (c := true) r, hnode]
    · simp [hABc]
  calc
    (∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) =
        ∑ r : Rest,
          if r idxA = true ∧ r idxB = false then
            qC_givenB (cpt := cpt) false * prodNonC (cpt := cpt) (c := true) r
          else 0 := hrewrite
    _ = ∑ r : Rest, qC_givenB (cpt := cpt) false * g r := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases hABc : r idxA = true ∧ r idxB = false <;> simp [g, hABc]
    _ = qC_givenB (cpt := cpt) false * ∑ r : Rest, g r := by
      simpa using
        (Finset.mul_sum (a := qC_givenB (cpt := cpt) false) (s := (Finset.univ : Finset Rest)) (f := g)).symm
    _ = qC_givenB (cpt := cpt) false *
          ∑ r : Rest, if r idxA = true ∧ r idxB = false then prodNonC (cpt := cpt) (c := true) r else 0 := by
      rfl

private lemma real_ratio_eq_toReal_q {X Y : Set ChainBN.JointSpace} (hY_pos : (μ (cpt := cpt)) Y ≠ 0)
    {q : ℝ≥0∞} (hXY : (μ (cpt := cpt)) (X ∩ Y) = q * (μ (cpt := cpt)) Y) :
    (μ (cpt := cpt)).real (X ∩ Y) / (μ (cpt := cpt)).real Y = q.toReal := by
  have hY_real_pos : (μ (cpt := cpt)).real Y ≠ 0 := by
    have : 0 < (μ (cpt := cpt)).real Y := by
      simp only [Measure.real, ENNReal.toReal_pos_iff]
      exact ⟨pos_iff_ne_zero.mpr hY_pos, measure_lt_top _ _⟩
    exact ne_of_gt this
  -- Convert the ENNReal equality into a statement about real ratios.
  simp only [Measure.real] at ⊢
  -- Cancel using the nonzero denominator.
  calc
    ((μ (cpt := cpt)) (X ∩ Y)).toReal / ((μ (cpt := cpt)) Y).toReal =
        ((q * (μ (cpt := cpt)) Y).toReal) / ((μ (cpt := cpt)) Y).toReal := by
          simp [hXY]
    _ = (q.toReal * ((μ (cpt := cpt)) Y).toReal) / ((μ (cpt := cpt)) Y).toReal := by
          simp [ENNReal.toReal_mul]
    _ = q.toReal := by
          -- Cancel the denominator (it is nonzero by `hY_pos`).
          have hden : ((μ (cpt := cpt)) Y).toReal ≠ 0 := hY_real_pos
          calc
            q.toReal * ((μ (cpt := cpt)) Y).toReal / ((μ (cpt := cpt)) Y).toReal =
                ((μ (cpt := cpt)) Y).toReal * q.toReal / ((μ (cpt := cpt)) Y).toReal := by
                  simp [mul_comm]
            _ = q.toReal := by
                  simpa using (mul_div_cancel_left₀ q.toReal hden)

lemma chainBN_pos_screeningOff
    (hAB_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) ≠ 0)
    (hB_pos : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) ≠ 0) :
    (μ (cpt := cpt)).real (C ∩ (A ∩ (B : Set ChainBN.JointSpace))) /
        (μ (cpt := cpt)).real (A ∩ (B : Set ChainBN.JointSpace)) =
      (μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)) /
        (μ (cpt := cpt)).real (B : Set ChainBN.JointSpace) := by
  have hCAB : (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace))) =
      qC_givenB (cpt := cpt) true * (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) :=
    mu_C_inter_A_inter_B_eq_q_mul_mu_A_inter_B (cpt := cpt)
  have hCB : (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)) =
      qC_givenB (cpt := cpt) true * (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) :=
    mu_C_inter_B_eq_q_mul_mu_B (cpt := cpt)
  -- Both conditionals equal `qC_givenB true`.
  calc
    (μ (cpt := cpt)).real (C ∩ (A ∩ (B : Set ChainBN.JointSpace))) /
        (μ (cpt := cpt)).real (A ∩ (B : Set ChainBN.JointSpace)) =
        (qC_givenB (cpt := cpt) true).toReal := by
          simpa [Set.inter_assoc] using
            real_ratio_eq_toReal_q (cpt := cpt) (X := C) (Y := A ∩ (B : Set ChainBN.JointSpace))
              hAB_pos (q := qC_givenB (cpt := cpt) true) hCAB
    _ = (μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)) /
          (μ (cpt := cpt)).real (B : Set ChainBN.JointSpace) := by
          symm
          simpa using
            real_ratio_eq_toReal_q (cpt := cpt) (X := C) (Y := (B : Set ChainBN.JointSpace))
              hB_pos (q := qC_givenB (cpt := cpt) true) hCB

lemma chainBN_neg_screeningOff
    (hABc_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) ≠ 0)
    (hBc_pos : (μ (cpt := cpt)) ((B : Set ChainBN.JointSpace)ᶜ) ≠ 0) :
    (μ (cpt := cpt)).real (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)) /
        (μ (cpt := cpt)).real (A ∩ (B : Set ChainBN.JointSpace)ᶜ) =
      (μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)ᶜ) /
        (μ (cpt := cpt)).real ((B : Set ChainBN.JointSpace)ᶜ) := by
  have hCABc : (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)) =
      qC_givenB (cpt := cpt) false * (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) :=
    mu_C_inter_A_inter_Bc_eq_q_mul_mu_A_inter_Bc (cpt := cpt)
  have hCBc : (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)ᶜ) =
      qC_givenB (cpt := cpt) false * (μ (cpt := cpt)) ((B : Set ChainBN.JointSpace)ᶜ) :=
    mu_C_inter_Bc_eq_q_mul_mu_Bc (cpt := cpt)
  calc
    (μ (cpt := cpt)).real (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)) /
        (μ (cpt := cpt)).real (A ∩ (B : Set ChainBN.JointSpace)ᶜ) =
        (qC_givenB (cpt := cpt) false).toReal := by
          simpa [Set.inter_assoc] using
            real_ratio_eq_toReal_q (cpt := cpt) (X := C) (Y := A ∩ (B : Set ChainBN.JointSpace)ᶜ)
              hABc_pos (q := qC_givenB (cpt := cpt) false) hCABc
    _ = (μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)ᶜ) /
          (μ (cpt := cpt)).real ((B : Set ChainBN.JointSpace)ᶜ) := by
          symm
          simpa using
            real_ratio_eq_toReal_q (cpt := cpt) (X := C) (Y := (B : Set ChainBN.JointSpace)ᶜ)
              hBc_pos (q := qC_givenB (cpt := cpt) false) hCBc

theorem chainBN_plnDeductionStrength_exact
    (hA_pos : (μ (cpt := cpt)) (A : Set ChainBN.JointSpace) ≠ 0)
    (hB_pos : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) ≠ 0)
    (hB_lt1 : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) < 1)
    (hAB_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) ≠ 0)
    (hABc_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) ≠ 0) :
    (μ (cpt := cpt)).real (C ∩ (A : Set ChainBN.JointSpace)) /
        (μ (cpt := cpt)).real (A : Set ChainBN.JointSpace) =
      plnDeductionStrength ((μ (cpt := cpt)).real ((B : Set ChainBN.JointSpace) ∩ A) /
          (μ (cpt := cpt)).real (A : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)) /
          (μ (cpt := cpt)).real (B : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (B : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (C : Set ChainBN.JointSpace)) := by
  -- First, establish `P(Bᶜ) ≠ 0` from `P(B) < 1`.
  have hBc_pos : (μ (cpt := cpt)) ((B : Set ChainBN.JointSpace)ᶜ) ≠ 0 := by
    intro h
    have huniv := IsProbabilityMeasure.measure_univ (μ := (μ (cpt := cpt)))
    have hBunion : (B : Set ChainBN.JointSpace) ∪ (B : Set ChainBN.JointSpace)ᶜ = Set.univ :=
      Set.union_compl_self (B : Set ChainBN.JointSpace)
    rw [← hBunion] at huniv
    have hdisj : Disjoint (B : Set ChainBN.JointSpace) (B : Set ChainBN.JointSpace)ᶜ :=
      disjoint_compl_right
    rw [measure_union hdisj measurable_B.compl, h, add_zero] at huniv
    rw [huniv] at hB_lt1
    exact lt_irrefl 1 hB_lt1
  -- Now discharge the screening-off equalities and apply the general PLN theorem.
  have h_pos_indep :
      (μ (cpt := cpt)).real (C ∩ ((A : Set ChainBN.JointSpace) ∩ (B : Set ChainBN.JointSpace))) /
          (μ (cpt := cpt)).real ((A : Set ChainBN.JointSpace) ∩ (B : Set ChainBN.JointSpace)) =
        (μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)) /
          (μ (cpt := cpt)).real (B : Set ChainBN.JointSpace) := by
    simpa [Set.inter_assoc] using
      chainBN_pos_screeningOff (cpt := cpt) hAB_pos hB_pos
  have h_neg_indep :
      (μ (cpt := cpt)).real (C ∩ ((A : Set ChainBN.JointSpace) ∩ (B : Set ChainBN.JointSpace)ᶜ)) /
          (μ (cpt := cpt)).real ((A : Set ChainBN.JointSpace) ∩ (B : Set ChainBN.JointSpace)ᶜ) =
        (μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)ᶜ) /
          (μ (cpt := cpt)).real (B : Set ChainBN.JointSpace)ᶜ := by
    simpa [Set.inter_assoc] using
      chainBN_neg_screeningOff (cpt := cpt) hABc_pos hBc_pos
  simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
    Mettapedia.Logic.PLN.pln_deduction_from_total_probability
      (μ := (μ (cpt := cpt))) (A := (A : Set ChainBN.JointSpace))
      (B := (B : Set ChainBN.JointSpace)) (C := (C : Set ChainBN.JointSpace))
      (hA := measurable_A) (hB := measurable_B) (hC := measurable_C)
      hA_pos hB_pos hB_lt1 hAB_pos hABc_pos h_pos_indep h_neg_indep

end Deduction

end ChainBN

/-! ## Generic Screening-Off Ratio Bridge

Convert the ENNReal multiplicative equality `μ(A∩C∩B) * μ(B) = μ(A∩B) * μ(C∩B)`
(from `screeningOffMulEq_of_condIndepVertices_CA`) to the `.real` ratio form
`μ.real(C∩A∩B) / μ.real(A∩B) = μ.real(C∩B) / μ.real(B)` used by
`pln_deduction_from_total_probability`. -/

/-- Convert ENNReal multiplicative screening-off `a * d = b * c`
    to `.real` ratio form `a.toReal / b.toReal = c.toReal / d.toReal`. -/
lemma real_ratio_of_ennreal_mul_eq {a b c d : ℝ≥0∞}
    (hmul : a * d = b * c)
    (hb : b ≠ 0) (hb_fin : b ≠ ⊤)
    (hd : d ≠ 0) (hd_fin : d ≠ ⊤)
    (_ha_fin : a ≠ ⊤) (_hc_fin : c ≠ ⊤) :
    a.toReal / b.toReal = c.toReal / d.toReal := by
  have hb_real : (0 : ℝ) < b.toReal := by
    rw [ENNReal.toReal_pos_iff]; exact ⟨pos_iff_ne_zero.mpr hb, lt_top_iff_ne_top.mpr hb_fin⟩
  have hd_real : (0 : ℝ) < d.toReal := by
    rw [ENNReal.toReal_pos_iff]; exact ⟨pos_iff_ne_zero.mpr hd, lt_top_iff_ne_top.mpr hd_fin⟩
  rw [div_eq_div_iff (ne_of_gt hb_real) (ne_of_gt hd_real)]
  have := congr_arg ENNReal.toReal hmul
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
  linarith

/-! ## Fork BN Deduction-Strength Exactness (A ← B → C)

For the fork BN `A ← B → C`, the screening-off condition `C ⊥ A | B`
follows directly from the local Markov property at C. This gives both
positive and negative screening-off via `screeningOffMulEq_of_condIndepVertices_CA`
instantiated at `valB = true` and `valB = false` respectively.

Key advantage: This proof uses `CondIndepVertices` from the abstract local Markov
property, not chain-specific product decompositions. -/

section ForkBN

open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

instance forkBN_fintype (v : Three) : Fintype (forkBN.stateSpace v) :=
  inferInstanceAs (Fintype Bool)

instance forkBN_nonempty (v : Three) : Nonempty (forkBN.stateSpace v) :=
  inferInstanceAs (Nonempty Bool)

instance forkBN_inhabited (v : Three) : Inhabited (forkBN.stateSpace v) :=
  inferInstanceAs (Inhabited Bool)

instance forkBN_decidableEq (v : Three) : DecidableEq (forkBN.stateSpace v) :=
  inferInstanceAs (DecidableEq Bool)

instance forkBN_measurableSingletonClass (v : Three) :
    MeasurableSingletonClass (forkBN.stateSpace v) :=
  inferInstanceAs (MeasurableSingletonClass Bool)

variable (cpt : forkBN.DiscreteCPT)

instance : IsProbabilityMeasure cpt.jointMeasure :=
  jointMeasure_isProbabilityMeasure (bn := forkBN) cpt

-- Abbreviations for event sets
private abbrev fA := eventEq (bn := forkBN) Three.A true
private abbrev fB := eventEq (bn := forkBN) Three.B true
private abbrev fC := eventEq (bn := forkBN) Three.C true

-- Measurability lemmas
private lemma measurable_fA : MeasurableSet fA := measurable_eventEq forkBN Three.A true
private lemma measurable_fB : MeasurableSet fB := measurable_eventEq forkBN Three.B true
private lemma measurable_fC : MeasurableSet fC := measurable_eventEq forkBN Three.C true

-- Finiteness lemmas (probability measures on finite spaces)
private lemma fin_forkBN (S : Set forkBN.JointSpace) : cpt.jointMeasure S ≠ ⊤ :=
  measure_ne_top cpt.jointMeasure S

/-- Get the ENNReal multiplicative screening-off from CondIndepVertices for fork. -/
private lemma forkBN_screeningOff_mul
    [HasLocalMarkovProperty forkBN cpt.jointMeasure]
    (valA valB valC : Bool) :
    cpt.jointMeasure
        (eventEq (bn := forkBN) Three.A valA ∩
          eventEq (bn := forkBN) Three.C valC ∩
          eventEq (bn := forkBN) Three.B valB) *
      cpt.jointMeasure (eventEq (bn := forkBN) Three.B valB) =
    cpt.jointMeasure
        (eventEq (bn := forkBN) Three.A valA ∩
          eventEq (bn := forkBN) Three.B valB) *
      cpt.jointMeasure
        (eventEq (bn := forkBN) Three.C valC ∩
          eventEq (bn := forkBN) Three.B valB) := by
  have hci := fork_condIndep_CA_given_B_of_localMarkov (μ := cpt.jointMeasure)
  -- CondIndepVertices {C} {A} {B} → CondIndepOn C B A → CondIndepOn A B C (by symmetry)
  have hciOn : CondIndepOn (bn := forkBN) (μ := cpt.jointMeasure) Three.A Three.B Three.C := by
    have : CondIndepOn (bn := forkBN) (μ := cpt.jointMeasure) Three.C Three.B Three.A := by
      simpa [CondIndepOn, CondIndepVertices] using hci
    exact this.symm
  exact condIndep_eventEq_mul_cond (bn := forkBN) (μ := cpt.jointMeasure)
    Three.A Three.B Three.C valA valB valC hciOn

theorem forkBN_pos_screeningOff
    [HasLocalMarkovProperty forkBN cpt.jointMeasure]
    (hAB_pos : cpt.jointMeasure (fA ∩ fB) ≠ 0)
    (hB_pos : cpt.jointMeasure fB ≠ 0) :
    cpt.jointMeasure.real (fC ∩ (fA ∩ fB)) / cpt.jointMeasure.real (fA ∩ fB) =
      cpt.jointMeasure.real (fC ∩ fB) / cpt.jointMeasure.real fB := by
  have hmul := forkBN_screeningOff_mul cpt true true true
  have h := real_ratio_of_ennreal_mul_eq hmul hAB_pos (fin_forkBN cpt _) hB_pos (fin_forkBN cpt _)
    (fin_forkBN cpt _) (fin_forkBN cpt _)
  simp only [Set.inter_comm, Set.inter_left_comm] at h ⊢
  exact h

/-- Negative screening-off for fork BN: μ.real(C ∩ (A ∩ Bᶜ)) / μ.real(A ∩ Bᶜ) = μ.real(C ∩ Bᶜ) / μ.real(Bᶜ).
    Uses Bool complement + CondIndepVertices with valB = false. -/
theorem forkBN_neg_screeningOff
    [HasLocalMarkovProperty forkBN cpt.jointMeasure]
    (hABc_pos : cpt.jointMeasure (fA ∩ fBᶜ) ≠ 0)
    (hBc_pos : cpt.jointMeasure fBᶜ ≠ 0) :
    cpt.jointMeasure.real (fC ∩ (fA ∩ fBᶜ)) / cpt.jointMeasure.real (fA ∩ fBᶜ) =
      cpt.jointMeasure.real (fC ∩ fBᶜ) / cpt.jointMeasure.real fBᶜ := by
  have hmul := forkBN_screeningOff_mul cpt true false true
  -- Rewrite eventEq B false → (eventEq B true)ᶜ = fBᶜ
  have hBool : eventEq (bn := forkBN) Three.B false = fBᶜ := by
    ext ω; simp only [eventEq, Set.mem_setOf_eq, Set.mem_compl_iff]
    show ω Three.B = false ↔ ¬ω Three.B = true
    exact ⟨fun h => h ▸ Bool.false_ne_true, Bool.eq_false_iff.mpr⟩
  simp only [hBool] at hmul
  have h := real_ratio_of_ennreal_mul_eq hmul hABc_pos (fin_forkBN cpt _)
    hBc_pos (fin_forkBN cpt _) (fin_forkBN cpt _) (fin_forkBN cpt _)
  simp only [Set.inter_comm, Set.inter_left_comm] at h ⊢
  exact h

/-- For fork BN `A ← B → C`, the PLN deduction formula is exact:
    P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C)).

    This is the fork analog of `chainBN_plnDeductionStrength_exact`.
    The proof is dramatically shorter because it uses `CondIndepVertices` from the
    abstract local Markov property rather than chain-specific product decompositions. -/
theorem forkBN_plnDeductionStrength_exact
    [HasLocalMarkovProperty forkBN cpt.jointMeasure]
    (hA_pos : cpt.jointMeasure fA ≠ 0)
    (hB_pos : cpt.jointMeasure fB ≠ 0)
    (hB_lt1 : cpt.jointMeasure fB < 1)
    (hAB_pos : cpt.jointMeasure (fA ∩ fB) ≠ 0)
    (hABc_pos : cpt.jointMeasure (fA ∩ fBᶜ) ≠ 0) :
    cpt.jointMeasure.real (fC ∩ fA) / cpt.jointMeasure.real fA =
      plnDeductionStrength
        (cpt.jointMeasure.real (fB ∩ fA) / cpt.jointMeasure.real fA)
        (cpt.jointMeasure.real (fC ∩ fB) / cpt.jointMeasure.real fB)
        (cpt.jointMeasure.real fB)
        (cpt.jointMeasure.real fC) := by
  -- P(Bᶜ) ≠ 0 from P(B) < 1
  have hBc_pos : cpt.jointMeasure fBᶜ ≠ 0 := by
    intro h
    have huniv := IsProbabilityMeasure.measure_univ (μ := cpt.jointMeasure)
    rw [← Set.union_compl_self fB] at huniv
    rw [measure_union disjoint_compl_right measurable_fB.compl, h, add_zero] at huniv
    rw [huniv] at hB_lt1; exact lt_irrefl 1 hB_lt1
  have h_pos := forkBN_pos_screeningOff cpt hAB_pos hB_pos
  have h_neg := forkBN_neg_screeningOff cpt hABc_pos hBc_pos
  simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
    pln_deduction_from_total_probability
      (μ := cpt.jointMeasure) (A := fA) (B := fB) (C := fC)
      measurable_fA measurable_fB measurable_fC
      hA_pos hB_pos hB_lt1 hAB_pos hABc_pos h_pos h_neg

end ForkBN

end Mettapedia.Logic.PLNBayesNetFastRules
