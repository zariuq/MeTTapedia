/-
# The combinators as a bag reactive system

The rho calculus in this tree is already presented as a reactive system in the
relative-pushout sense: its parallel contexts form the bag context category, its
COMM instances are reaction rules, and its reduction relation coincides with the
identity-labelled transitions the idem-pushout construction produces.

The combinators admit the same reading, and this file supplies it.  What makes
the port cheap is that the load-bearing lemma of the bag construction — a bound
is least exactly when its two legs share nothing — is generic in the carrier and
now lives with the construction rather than with rho.  What makes it possible at
all is `step_iff_redex`: the reactive-system reading needs a step to *be* a
redex replaced beside an untouched context, and that is the decomposition
theorem.

The rule family is parameterized by an admissibility predicate on rule
instances, exactly as the rho side parameterizes over admissible COMM sources.
Restricting the observers to the image of a translation is then an instantiation
of this predicate rather than a different notion, which is the point worth
having: the restriction is an instance of the admission discipline already in
use, not a parallel one.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RedexDecomposition
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Inertness
import Mettapedia.GSLT.Logic.BagRelativePushout

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule ActIPO)
open Mettapedia.GSLT.BagRelativePushout (Bag bag bag_comp bag_injective bag_surjective
  isIdemPushout_bag isIdemPushout_bag_iff)
open Comb

/-! ## The interface and the rules -/

/-- The single interface of the bag context category over combinator soups. -/
abbrev parallelInterface : SingleObj (Bag Comb) :=
  Mettapedia.GSLT.BagRelativePushout.Obj Comb

/-- A soup, as an agent of the bag context category: its components. -/
def agent (t : Comb) : parallelInterface ⟶ parallelInterface := bag (components t)

/-- **A rule instance as a reaction rule**: its participants react to its
reactum. -/
def instanceRule (ri : RuleInstance) : ReactionRule parallelInterface where
  codomain := parallelInterface
  redex := bag (components ri.redexTerm)
  reactum := bag (components ri.reactumTerm)

/-- The valid rule instances satisfying an admissibility condition.  Restricting
the observers to a translation's image instantiates `admissible`. -/
def rulesWhere (admissible : RuleInstance → Prop) :
    ReactionRule parallelInterface → Prop :=
  fun rule => ∃ ri, ri.Valid ∧ admissible ri ∧ rule = instanceRule ri

/-- Every valid instance, with no restriction on the observer. -/
def validRules : ReactionRule parallelInterface → Prop := rulesWhere fun _ => True

/-! ## Labelled transitions -/

/-- **The labelled transitions of a rule family.**  A soup with components
`source` has a transition labelled by the parallel partners `label` exactly when
`source` together with `label` is a rule's redex beside a reaction context
sharing nothing with the label; the target is the reactum beside that context. -/
theorem actIPO_bag_iff (admissible : RuleInstance → Prop)
    (label source target : Multiset Comb) :
    ActIPO (rulesWhere admissible) (bag label) (bag source) (bag target) ↔
      ∃ ri, ri.Valid ∧ admissible ri ∧
        ∃ context : Multiset Comb,
          source + label = components ri.redexTerm + context ∧
          label ∩ context = 0 ∧
          target = components ri.reactumTerm + context := by
  constructor
  · rintro ⟨rule, ⟨ri, hvalid, hadm, rfl⟩, reaction, square, ipo, targetEq⟩
    let context : Multiset Comb := Multiplicative.toAdd reaction
    refine ⟨ri, hvalid, hadm, context, ?_, ?_, ?_⟩
    · have coordinates : bag source ≫ bag label =
          bag (components ri.redexTerm) ≫ bag context := square
      rw [bag_comp, bag_comp] at coordinates
      exact bag_injective coordinates
    · exact (isIdemPushout_bag_iff source _ label context square).mp ipo
    · have coordinates : bag target =
          bag (components ri.reactumTerm) ≫ bag context := targetEq
      rw [bag_comp] at coordinates
      exact bag_injective coordinates
  · rintro ⟨ri, hvalid, hadm, context, sourceEq, disjoint, targetEq⟩
    have square : bag source ≫ bag label =
        bag (components ri.redexTerm) ≫ bag context := by
      rw [bag_comp, bag_comp, sourceEq]
    refine ⟨instanceRule ri, ⟨ri, hvalid, hadm, rfl⟩, bag context, square,
      isIdemPushout_bag source _ label context square disjoint, ?_⟩
    change bag target = bag (components ri.reactumTerm) ≫ bag context
    rw [bag_comp, targetEq]

/-- **Identity-labelled transitions are the reactions**: a rule's redex beside a
reaction context becomes its reactum beside the same context.  The identity
label is always least. -/
theorem actIPO_identity_iff (admissible : RuleInstance → Prop)
    (source target : Multiset Comb) :
    ActIPO (rulesWhere admissible) (𝟙 parallelInterface) (bag source) (bag target) ↔
      ∃ ri, ri.Valid ∧ admissible ri ∧
        ∃ context : Multiset Comb,
          source = components ri.redexTerm + context ∧
          target = components ri.reactumTerm + context := by
  change ActIPO _ (bag 0) _ _ ↔ _
  rw [actIPO_bag_iff]
  simp only [add_zero, Multiset.zero_inter, true_and]

/-- **Every label is drawn from one redex.**  The least label of a transition
consists of parallel partners that, together with the soup, complete a single
rule instance — so a minimal label is never larger than one redex.  This is the
forward half of the minimal-label question, and it descends from the bag
construction without extra work. -/
theorem label_le_redex {admissible : RuleInstance → Prop}
    {label source target : Multiset Comb}
    (step : ActIPO (rulesWhere admissible) (bag label) (bag source) (bag target)) :
    ∃ ri, ri.Valid ∧ admissible ri ∧ label ≤ components ri.redexTerm := by
  obtain ⟨ri, hvalid, hadm, context, sourceEq, disjoint, -⟩ :=
    (actIPO_bag_iff admissible label source target).mp step
  refine ⟨ri, hvalid, hadm, Multiset.le_iff_count.mpr fun atom => ?_⟩
  have counts := congrArg (Multiset.count atom) sourceEq
  have shared := congrArg (Multiset.count atom) disjoint
  simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_zero] at counts shared
  omega

/-! ## The correspondence -/

/-- **Reduction is exactly the identity-labelled transition relation.**  This is
the combinator analogue of the correspondence already verified for rho, and it
is what licenses transporting the relative-pushout account of behaviour to this
calculus: the reduction relation authored by the rules and the transitions the
idem-pushout construction produces are the same relation, not two relations that
happen to agree on examples. -/
theorem step_iff_actIPO_identity (t t' : Comb) :
    Step Cong t t' ↔ ActIPO validRules (𝟙 parallelInterface) (agent t) (agent t') := by
  rw [agent, agent, validRules, actIPO_identity_iff]
  constructor
  · intro h
    obtain ⟨ri, ctx, hvalid, hsrc, htgt⟩ := components_of_step h
    exact ⟨ri, hvalid, trivial, ctx, hsrc, htgt⟩
  · rintro ⟨ri, hvalid, -, ctx, hsrc, htgt⟩
    have hle : ctx ≤ components t := by
      rw [hsrc]; exact Multiset.le_add_left _ _
    obtain ⟨ctxTerm, hctx⟩ := exists_components_eq hle
    refine step_of_decompose (ctx := ctxTerm) hvalid (cong_of_components ?_)
      (cong_of_components ?_)
    · simp only [components, hctx]; exact hsrc
    · simp only [components, hctx]; exact htgt

/-! ## Negative controls -/

/-- A gate has no transition at all: the correspondence carries inertness over
to the labelled-transition reading, so the gadget that must sit still does sit
still in the reactive system too. -/
theorem gate_no_transition {trigger store run continuation : Comb}
    (htrigger : ¬ Cong trigger store) (hrun : ¬ Cong run store) :
    ∀ t, ¬ ActIPO validRules (𝟙 parallelInterface)
      (agent (gate trigger store run continuation)) (agent t) :=
  fun t h => gate_inert htrigger hrun t
    ((step_iff_actIPO_identity _ t).mpr h)

/-- The transition relation is not empty: a message meeting its router reacts. -/
theorem duplicate_has_transition (a b c v : Comb) :
    ActIPO validRules (𝟙 parallelInterface)
      (agent (par (dd a b c) (mm a v))) (agent (par (mm b v) (mm c v))) :=
  (step_iff_actIPO_identity _ _).mp
    (Step.ofMinus (StepMinus.duplicate b c v (Cong.refl a)))

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
