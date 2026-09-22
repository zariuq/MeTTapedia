import Mettapedia.GSLT.Logic.RhoBagReactiveSystem
import Mettapedia.GSLT.Logic.ParallelLeastEnablerFails
import Mettapedia.GSLT.Logic.TypeIPOContextCongruenceControls

/-!
# Conditions 20.1 and 20.2 on rho's closed COMM/parallel-bag presentation

Every chapter of the machinery part of *Finding Mind* assumes two conditions
of a theory `S`:

> **Condition 20.1 (Redex RPOs).** S has all redex-relative pushouts, so that
> the derived transition system exists.

> **Condition 20.2 (Congruence).** S comes equipped with a class A of
> contexts, containing those built from the rewrite constructors, such that
> context-labeled bisimilarity is a congruence with respect to A, and
> observations are restricted to A.

This module discharges both conditions for the closed COMM presentation whose
context category consists of parallel bags.  It does not establish Condition
20.2 for every rho context discussed in *Finding Mind*: the book also names
output-payload, input-continuation, and drop-after-quote contexts as admissible.
Those positions are quote-free but are not all parallel-bag contexts; see
`AdmissibleContexts.parallelPath_not_all_quoteFree`.  The wider rho context
category and its congruence proof remain separate obligations.

`RhoBagReactiveSystem` presents rho as a reactive system over the context
category of parallel bags: a process is the multiset of its parallel
components, and each closed COMM instance `{x!(q), for(y<-x)p}` is a reaction
rule.  The presentation is adequate: a closed process steps in the
established rho GSLT exactly when its components react
(`RhoBagReactiveSystem.step_iff_actIPO_identity`), and the same holds for the
paper relation `Reduction.Reduces` on the pure carrier
(`RhoBagReactiveSystem.reduces_iff_actIPO_identity`).  In that presentation:

* **20.1.**  Every span of an agent and a closed COMM redex has relative
  pushouts (`condition_20_1_rho`).  So the derived transition system exists:
  a reduction of a process beside a parallel partner is a transition of the
  process alone, whose least label is the part of the partner the redex used
  (`reduction_beside_partner_is_leastLabelledTransition`).
* **20.2.**  A is the class of parallel contexts, the arrows of the bag
  context category.  It contains every instance of the `ParCong` frame of this
  closed COMM GSLT presentation (`agent_fill_rhoParallelInstance`).
  Context-labelled bisimilarity, here IPO bisimilarity, is preserved by every
  parallel partner (`condition_20_2_rho`) and every `ParCong` instance
  (`ipoBisimilar_fill_rhoParallelInstance`).  The system has no observations
  besides its labels, and every label is a multiset of parallel partners drawn
  from one COMM redex (`RhoBagReactiveSystem.label_le_redex`).  Input
  prefixing is not in A (`inputPrefix_not_parallelContext`), matching the
  absence of reduction under a prefix (`RhoBagReactiveSystem.guardedComm_not_step`).

The generic congruence theorem with interface-changing contexts is exercised
in `TypeIPOContextCongruenceControls` on a different reactive system; that
example does not supply the missing rho context-category instance.

## An alternative reading that fails

One can read the congruence condition instead as composition of least
enablers: a least enabler at `C[p]` is a least enabler at `p` composed with
`C`.  That reading is false already for parallel contexts
(`everyContext_not_leastEnablerComposes`, from `ParallelLeastEnablerFails`):
composing with a context re-adds siblings the rule never needed.  It is not
the reading of Condition 20.2 used here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Conditions201202

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule ActIPO IPOBisimilar)
open Mettapedia.GSLT.BagRelativePushout (Bag bag bag_comp bag_injective bag_surjective
  hasRelativePushouts congruence)
open Mettapedia.GSLT.RhoBagReactiveSystem
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess rhoLanguageDefGSLT)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy (par par_pattern
  outputPartner)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
  (rhoParallelInstance rhoParallelInstance_fill)

/-! ## Condition 20.1 -/

/-- **Condition 20.1 for rho.**  Every span formed by an agent and the redex
of a closed COMM rule has relative pushouts.  (In the bag context category
every span does; the statement is the one the congruence theorem consumes.) -/
theorem condition_20_1_rho :
    ∀ (interface : SingleObj (Bag Pattern)) (observed : parallelInterface ⟶ interface)
      (rule : ReactionRule parallelInterface), closedCommRules rule →
        HasRelativePushouts observed rule.redex := by
  intro _ observed rule _
  obtain ⟨observedBag, observedEq⟩ := bag_surjective observed
  obtain ⟨redexBag, redexEq⟩ := bag_surjective rule.redex
  rw [observedEq, redexEq]
  exact hasRelativePushouts observedBag redexBag

/-- Parallel composition of closed processes is composition of their
agents. -/
theorem agent_par (left right : RhoProcess) :
    agent (par left right).1 = agent left.1 ≫ agent right.1 := by
  rw [agent, agent, agent, bag_comp, par_pattern, components_parallel]
  simp

/-- **The derived transition system exists.**  A step of a closed process `P`
beside a parallel partner `R` is a transition of `P` alone.  Its label is
least, it and the unused rest of `R` recompose `R`, and the transition's
target beside that rest is the step's target. -/
theorem reduction_beside_partner_is_leastLabelledTransition {P R Q : RhoProcess}
    (step : rhoLanguageDefGSLT.Step (par P R) Q) :
    ∃ (interface : SingleObj (Bag Pattern)) (label : parallelInterface ⟶ interface)
      (rest : interface ⟶ parallelInterface) (next : parallelInterface ⟶ interface),
      ActIPO closedCommRules label (agent P.1) next ∧
        label ≫ rest = agent R.1 ∧ next ≫ rest = agent Q.1 := by
  obtain ⟨rule, member, reaction, square, -, targetEq⟩ :=
    (step_iff_actIPO_identity (par P R) Q).mp step
  have bound : agent P.1 ≫ agent R.1 = rule.redex ≫ reaction := by
    rw [← agent_par, ← Category.comp_id (agent (par P R).1)]
    exact square
  obtain ⟨reduced, rpo⟩ :=
    condition_20_1_rho _ (agent P.1) rule member _ (agent R.1) reaction bound
  refine ⟨reduced.apex, reduced.inl, reduced.down, rule.reactum ≫ reduced.inr,
    ⟨rule, member, reduced.inr, reduced.comm, isIdemPushout_of_isRelativePushout rpo, rfl⟩,
    reduced.fac_left, ?_⟩
  rw [targetEq, Category.assoc, reduced.fac_right]

/-! ## Condition 20.2 -/

/-- **The rewrite constructor's contexts are parallel contexts.**  Filling an
instance of rho's `ParCong` frame is composing with the bag of the frame's
other components. -/
theorem agent_fill_rhoParallelInstance (before after : List Pattern) (process : Pattern) :
    agent ((rhoParallelInstance before after).fill process) =
      agent process ≫ bag ((before.map components).sum + (after.map components).sum) := by
  rw [rhoParallelInstance_fill, agent, agent, bag_comp, components_parallel]
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  exact congrArg bag (add_left_comm _ _ _)

/-- **Condition 20.2 for rho's parallel-bag presentation.**  IPO bisimilarity
for the closed COMM rules is a congruence for parallel composition: bisimilar
closed processes stay bisimilar beside any closed partner. -/
theorem condition_20_2_rho {left right : RhoProcess}
    (bisim : IPOBisimilar closedCommRules (agent left.1) (agent right.1)) (partner : RhoProcess) :
    IPOBisimilar closedCommRules (agent (par left partner).1) (agent (par right partner).1) := by
  rw [agent_par, agent_par]
  exact congruence closedCommRules bisim (agent partner.1)

/-- IPO bisimilarity for the closed COMM rules is preserved by every instance
of rho's `ParCong` frame. -/
theorem ipoBisimilar_fill_rhoParallelInstance {left right : Pattern}
    (bisim : IPOBisimilar closedCommRules (agent left) (agent right))
    (before after : List Pattern) :
    IPOBisimilar closedCommRules
      (agent ((rhoParallelInstance before after).fill left))
      (agent ((rhoParallelInstance before after).fill right)) := by
  rw [agent_fill_rhoParallelInstance, agent_fill_rhoParallelInstance]
  exact congruence closedCommRules bisim _

/-- **Input prefixing is not in A.**  No parallel context acts on components
as the input prefix `for(y <- x)[-]` does. -/
theorem inputPrefix_not_parallelContext (channel : Pattern) :
    ¬ ∃ context : parallelInterface ⟶ parallelInterface, ∀ body : Pattern,
      agent (.apply "PInput" [channel, .lambda none body]) = agent body ≫ context := by
  rintro ⟨context, acts⟩
  have coordinates : ∀ body : Pattern,
      components (.apply "PInput" [channel, .lambda none body]) =
        components body + (Multiplicative.toAdd context : Multiset Pattern) := by
    intro body
    have acted : bag (components (.apply "PInput" [channel, .lambda none body])) =
        bag (components body) ≫ bag (Multiplicative.toAdd context : Multiset Pattern) :=
      acts body
    rw [bag_comp] at acted
    exact bag_injective acted
  have atInert := congrArg Multiset.card (coordinates inert)
  have atOutput := congrArg Multiset.card (coordinates outputPartner.1)
  simp only [components_input, components_inert, outputPartner, components_output,
    Multiset.card_singleton, Multiset.card_add, zero_add] at atInert atOutput
  omega

/-! ## An alternative reading that fails -/

/-- **The least-enabler composition reading fails.**  In the bag theory of
`ParallelLeastEnablerFails`, with every parallel context admissible, least
enablers do not compose with contexts.  This is an alternative reading of the
congruence condition, not the one proved above. -/
theorem everyContext_not_leastEnablerComposes :
    ¬ Mettapedia.GSLT.ParallelLeastEnablerFails.everyContext.LeastEnablerComposes :=
  Mettapedia.GSLT.ParallelLeastEnablerFails.leastEnablerComposes_fails

#print axioms condition_20_1_rho
#print axioms reduction_beside_partner_is_leastLabelledTransition
#print axioms agent_fill_rhoParallelInstance
#print axioms condition_20_2_rho
#print axioms ipoBisimilar_fill_rhoParallelInstance
#print axioms inputPrefix_not_parallelContext
#print axioms everyContext_not_leastEnablerComposes

end Mettapedia.GSLT.Conditions201202
