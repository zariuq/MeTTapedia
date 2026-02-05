import Mettapedia.Logic.PLNDerivation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

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

instance (v : Three) : Fintype (ChainBN.stateSpace v) := by
  dsimp [ChainBN, chainBN]
  infer_instance

instance (v : Three) : Nonempty (ChainBN.stateSpace v) := by
  dsimp [ChainBN, chainBN]
  infer_instance

variable (cpt : ChainBN.DiscreteCPT)

noncomputable abbrev μ (cpt : ChainBN.DiscreteCPT) : Measure ChainBN.JointSpace :=
  cpt.jointMeasure

instance (cpt : ChainBN.DiscreteCPT) : IsProbabilityMeasure (μ (cpt := cpt)) :=
  jointMeasure_isProbabilityMeasure (bn := ChainBN) cpt

/-! ## Events A,B,C as cylinder sets on the joint sample space -/

abbrev eventTrue (v : Three) : Set ChainBN.JointSpace :=
  (fun ω : ChainBN.JointSpace => ω v) ⁻¹' ({true} : Set Bool)

abbrev A : Set ChainBN.JointSpace := eventTrue Three.A
abbrev B : Set ChainBN.JointSpace := eventTrue Three.B
abbrev C : Set ChainBN.JointSpace := eventTrue Three.C

lemma measurable_eventTrue (v : Three) : MeasurableSet (eventTrue v) := by
  have hproj : Measurable (fun ω : ChainBN.JointSpace => ω v) := by
    fun_prop
  have hsing : MeasurableSet ({true} : Set Bool) := by
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
      ∑ c : ChainBN.stateSpace Three.C, ∑ r : Rest, f (cfg c r) := by
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
    _ = ∑ c : ChainBN.stateSpace Three.C, ∑ r : Rest, f (cfg c r) := by
        -- `Fintype.sum_prod_type` turns the sum over pairs into a nested sum.
        simpa using
          (Fintype.sum_prod_type (f := fun p : ChainBN.stateSpace Three.C × Rest => f (cfg p.1 p.2)))

/-! ## Product-form lemmas specialized to the sink coordinate `C` -/

abbrev idxA : { v : Three // v ≠ Three.C } := ⟨Three.A, by decide⟩
abbrev idxB : { v : Three // v ≠ Three.C } := ⟨Three.B, by decide⟩

lemma cfg_apply_A (c : ChainBN.stateSpace Three.C) (r : Rest) :
    cfg c r Three.A = r idxA := by
  simpa [idxA] using cfg_apply_of_ne_C (v := Three.A) (by decide) c r

lemma cfg_apply_B (c : ChainBN.stateSpace Three.C) (r : Rest) :
    cfg c r Three.B = r idxB := by
  simpa [idxB] using cfg_apply_of_ne_C (v := Three.B) (by decide) c r

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
      simpa using
        (Fintype.prod_unique
          (fun v : { v : Three // ¬(v ≠ Three.C) } => nodeProb cpt (cfg c r) v.val))
    have hdef : (default : { v : Three // ¬(v ≠ Three.C) }).val = Three.C := by
      have : (default : { v : Three // ¬(v ≠ Three.C) }) = ⟨Three.C, by simp⟩ :=
        Subsingleton.elim _ _
      simpa using congrArg Subtype.val this
    simpa [hdef] using hprod
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
      simpa [mul_comm, mul_left_comm, mul_assoc]


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
    simp [DiscreteCPT.parentAssignOfConfig, cfg_apply_B, hB]
  simpa [hpa]

noncomputable def qC_givenB (b : Bool) : ℝ≥0∞ :=
  nodeProb cpt (cfg true (restB b)) Three.C

lemma nodeProb_C_true_eq_qC_givenB {r : Rest} {b : Bool} (hb : r idxB = b) :
    nodeProb cpt (cfg true r) Three.C = qC_givenB (cpt := cpt) b := by
  classical
  -- Replace `r` by the canonical rest assignment that agrees on `B`.
  have hb' : r idxB = (restB b) idxB := by
    simpa [restB, hb]
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
  -- Expand the sum over the Boolean `C` coordinate, then combine the two summands.
  -- First, expand the outer sum over the Boolean `C` coordinate.
  have hC :
      (∑ c : Bool, ∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg c r) else 0) =
        (∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          ∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg false r) else 0 := by
    simpa [Fintype.sum_bool]
  -- Then, combine the two `Rest` sums into one, and simplify the pointwise addition.
  calc
    (∑ c : Bool, ∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg c r) else 0) =
        (∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          ∑ r : Rest, if r idxB = true then cpt.jointWeight (cfg false r) else 0 := hC
    _ = ∑ r : Rest,
        ((if r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          (if r idxB = true then cpt.jointWeight (cfg false r) else 0)) := by
      simpa using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest => if r idxB = true then cpt.jointWeight (cfg true r) else 0)
          (g := fun r : Rest => if r idxB = true then cpt.jointWeight (cfg false r) else 0)).symm
    _ = ∑ r : Rest,
        (if r idxB = true then cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r) else 0) := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases h : r idxB = true <;> simp [h, add_assoc]

private lemma mu_C_inter_B_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)) =
      ∑ r : Rest, (if r idxB = true then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (B : Set ChainBN.JointSpace))
        (hS := measurable_C.inter measurable_B)]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (B : Set ChainBN.JointSpace)).indicator cpt.jointWeight ω)]
  -- Only the `c = true` summand contributes to `C`.
  simp [C, B, eventTrue, Set.indicator]
  -- Expand the sum over the Boolean `C` coordinate, and simplify away the `c = false` term.
  dsimp [ChainBN, chainBN] at ⊢
  -- Discharge proof-irrelevance in the `B`-index subtype used to access `r idxB`.
  -- We normalize all occurrences of the `B`-index to the canonical `idxB`.
  have hBnorm :
      (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) = idxB := by
    ext
    rfl
  -- Evaluate the explicit `{true,false}` sum, using `hBnorm` to normalize the `B`-index proof.
  simpa [idxB, hBnorm] using (by
    -- The only remaining mismatch is the proof component inside the subtype used for indexing `Rest`.
    -- We eliminate it via `Subtype.ext` inside a `Fintype.sum_congr`.
    refine Fintype.sum_congr _ _ (fun r => ?_)
    -- Any two `B`-indices are equal as subtypes, since their `.val` components agree.
    have hBidx :
        (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) =
          ⟨Three.B, idxB._proof_1⟩ := by
      ext
      rfl
    -- Rewrite the `Rest` lookup along `hBidx`.
    simpa [hBidx])

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
  -- Combine the two `C`-summands into a single sum over `r`.
  have hC :
      (∑ c : Bool, ∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg c r)) =
        (∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg true r)) +
          ∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg false r) := by
    simpa [Fintype.sum_bool]
  calc
    (∑ c : Bool, ∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg c r)) =
        (∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg true r)) +
          ∑ r : Rest, if r idxB = true then 0 else cpt.jointWeight (cfg false r) := hC
    _ = ∑ r : Rest,
        ((if r idxB = true then 0 else cpt.jointWeight (cfg true r)) +
          (if r idxB = true then 0 else cpt.jointWeight (cfg false r))) := by
      simpa using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest => if r idxB = true then 0 else cpt.jointWeight (cfg true r))
          (g := fun r : Rest => if r idxB = true then 0 else cpt.jointWeight (cfg false r))).symm
    _ = ∑ r : Rest,
        (if r idxB = true then 0 else
            (cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r))) := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases h : r idxB = true <;> simp [h, add_assoc]
    _ = ∑ r : Rest,
        (if r idxB = false then cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r) else 0) := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      cases hb : r idxB <;> simp [hb]

private lemma mu_C_inter_Bc_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (B : Set ChainBN.JointSpace)ᶜ) =
      ∑ r : Rest, (if r idxB = false then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (B : Set ChainBN.JointSpace)ᶜ)
        (hS := measurable_C.inter measurable_B.compl)]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (B : Set ChainBN.JointSpace)ᶜ).indicator cpt.jointWeight ω)]
  simp [C, B, eventTrue, Set.indicator]
  dsimp [ChainBN, chainBN] at ⊢
  have hBnorm :
      (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) = idxB := by
    ext
    rfl
  simpa [idxB, hBnorm] using (by
    refine Fintype.sum_congr _ _ (fun r => ?_)
    have hBidx :
        (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) =
          ⟨Three.B, idxB._proof_1⟩ := by
      ext
      rfl
    simpa [hBidx])

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
  have hC :
      (∑ c : Bool, ∑ r : Rest,
          if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg c r) else 0) =
        (∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          ∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg false r) else 0 := by
    simpa [Fintype.sum_bool]
  calc
    (∑ c : Bool, ∑ r : Rest,
        if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg c r) else 0) =
        (∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          ∑ r : Rest, if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg false r) else 0 := hC
    _ = ∑ r : Rest,
        ((if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) +
          (if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg false r) else 0)) := by
      simpa using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest =>
            if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0)
          (g := fun r : Rest =>
            if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg false r) else 0)).symm
    _ = ∑ r : Rest,
        (if r idxA = true ∧ r idxB = true then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases h : r idxA = true ∧ r idxB = true <;> simp [h, add_assoc]

private lemma mu_C_inter_A_inter_B_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace))) =
      ∑ r : Rest, (if r idxA = true ∧ r idxB = true then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (A ∩ (B : Set ChainBN.JointSpace)))
        (hS := measurable_C.inter (measurable_A.inter measurable_B))]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (A ∩ (B : Set ChainBN.JointSpace))).indicator cpt.jointWeight ω)]
  simp [C, A, B, eventTrue, Set.indicator]
  dsimp [ChainBN, chainBN] at ⊢
  have hBnorm :
      (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) = idxB := by
    ext
    rfl
  simpa [idxB, hBnorm] using (by
    refine Fintype.sum_congr _ _ (fun r => ?_)
    have hBidx :
        (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) =
          ⟨Three.B, idxB._proof_1⟩ := by
      ext
      rfl
    simpa [hBidx])

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
    · cases hb : r idxB <;> simp [hA, hb]
    · simp [hA]
  simp_rw [hnormB]
  have hC :
      (∑ c : Bool, ∑ r : Rest,
          if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg c r) else 0) =
        (∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) +
          ∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg false r) else 0 := by
    simpa [Fintype.sum_bool]
  calc
    (∑ c : Bool, ∑ r : Rest,
        if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg c r) else 0) =
        (∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) +
          ∑ r : Rest, if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg false r) else 0 := hC
    _ = ∑ r : Rest,
        ((if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) +
          (if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg false r) else 0)) := by
      simpa using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset Rest))
          (f := fun r : Rest =>
            if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0)
          (g := fun r : Rest =>
            if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg false r) else 0)).symm
    _ = ∑ r : Rest,
        (if r idxA = true ∧ r idxB = false then
            cpt.jointWeight (cfg true r) + cpt.jointWeight (cfg false r)
          else 0) := by
      refine Fintype.sum_congr _ _ (fun r => ?_)
      by_cases h : r idxA = true ∧ r idxB = false <;> simp [h, add_assoc]

private lemma mu_C_inter_A_inter_Bc_eq_sum_rest :
    (μ (cpt := cpt)) (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)) =
      ∑ r : Rest, (if r idxA = true ∧ r idxB = false then cpt.jointWeight (cfg true r) else 0) := by
  classical
  rw [jointMeasure_apply (cpt := cpt) (S := C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ))
        (hS := measurable_C.inter (measurable_A.inter measurable_B.compl))]
  rw [sum_piSplitAtC (f := fun ω => (C ∩ (A ∩ (B : Set ChainBN.JointSpace)ᶜ)).indicator cpt.jointWeight ω)]
  simp [C, A, B, eventTrue, Set.indicator]
  dsimp [ChainBN, chainBN] at ⊢
  have hBnorm :
      (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) = idxB := by
    ext
    rfl
  simpa [idxB, hBnorm] using (by
    refine Fintype.sum_congr _ _ (fun r => ?_)
    have hBidx :
        (⟨Three.B, (by decide : Three.B ≠ Three.C)⟩ : { v : Three // v ≠ Three.C }) =
          ⟨Three.B, idxB._proof_1⟩ := by
      ext
      rfl
    simpa [hBidx])

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
    simp [pa, DiscreteCPT.parentAssignOfConfig, cfg_apply_B]
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
    refine Fintype.sum_congr _ _ (fun r => ?_)
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
          simpa [hXY]
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

end Mettapedia.Logic.PLNBayesNetFastRules
