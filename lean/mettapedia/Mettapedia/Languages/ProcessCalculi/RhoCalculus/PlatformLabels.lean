import Mettapedia.GSLT.Logic.BagRelativePushout
import Mettapedia.GSLT.Logic.IPOBox
import Mettapedia.OSLF.Framework.ObserverReconstruction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-!
# Item two on the platform: least labels, and the congruence

The platform's contexts are parallel remainders — a bag of processes placed
beside the hole — so its context category is the one-object category on bags,
which `BagRelativePushout` proves has relative pushouts for every span and every
bound.  That half runs with nothing assumed and is schema-independent: *any*
reaction over bags has a least label for its redex, and the induced bisimilarity
is a congruence.

**What is instantiated here is one ground reaction, not rho's reaction
relation.**  `joinReaction` fixes the channels, the values and the arity;
`platformRules` is the singleton containing it.  Rho's communication rule is a
schema over channels, values, arities and continuations, and the reaction set it
induces is infinite.  The congruence above does not care — it is proved for every
span of bags — but the *finiteness* results below do: `platformRules_finite` holds
because the set is a singleton, and is false for the schema.  So
`platform_backward_adequacy` is adequacy for one ground reaction.

**The reaction rules are the presentation's, not invented for the occasion.**
`reaction_realised` and `reaction_realised_in_context` check, in the kernel,
that the bag reaction below is exactly what the engine computes from the
platform's own join rule — first alone, then beside a process it must leave
alone.

**The admissible class is automatic here, and that is the content.**  A context
of this model places processes *beside* the hole; it cannot put the hole under a
quote, because a bag has no quote in it.  So the contexts of this model all lie
inside the class item 2 asks for, and the congruence needs no class parameter.

**The containment is strict, and in the limiting direction.**
`AdmissibleContexts.quoteFreePath_of_parallelPath` puts every parallel position
inside the quote-free class; `AdmissibleContexts.parallelPath_not_all_quoteFree`
shows the inclusion is proper, the payload position of an output being quote-free
but not parallel.  So this model does not *cover* the class -- it is a sub-class
of it, and congruence under output-payload contexts and under input prefixes is
neither obtained here nor claimed.  Reaching them needs a context category with
more than one object.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.BagRelativePushout
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-! ## The platform's reaction, as a bag rule -/

/-- Two channels and two values, as in `Guard`. -/
def channelA : Pattern := .apply "A" []
def channelB : Pattern := .apply "B" []
def valueP : Pattern := .apply "P" []
def valueQ : Pattern := .apply "Q" []

/-- The receiver of the binary join, with a continuation that returns what it
receives. -/
def receiverTerm : Pattern :=
  .apply (joinLabel 2) [channelA, channelB, .lambda none (.bvar 0)]

/-- The two outputs it consumes. -/
def outputA : Pattern := .apply outLabel [channelA, valueP]
def outputB : Pattern := .apply outLabel [channelB, valueQ]

/-- What the continuation is fed: the quote of the bundle. -/
def firedTerm : Pattern :=
  .apply quoteLabel [.apply (tupleLabel 2) [valueP, valueQ]]

/-- The redex, as a list of parallel components. -/
def redexParts : List Pattern := [receiverTerm, outputA, outputB]

/-- And the reactum. -/
def reactumParts : List Pattern := [firedTerm]

/-- A bag of components, as a process of the presentation. -/
def asProcess (parts : List Pattern) : Pattern := .collection .hashBag parts none

/-- The guard that admits the pair once. -/
def guard : RelationEnv where
  tuples := fun relation _ =>
    if relation = guardRelation then [[channelA, channelB]] else []

/-- The evaluator, and the presentation. -/
def evaluator : BasePremiseEvaluator := engineBasePremises guard

abbrev platform : LanguageDef := rhoPlatform [2]

/-- **The reaction is the presentation's own.**  The engine computes exactly the
reactum from the redex. -/
theorem reaction_realised :
    rewriteAt evaluator platform 6 (asProcess redexParts)
      = [asProcess reactumParts] := by
  decide +kernel

/-- **And it is contextual.**  Beside a process the rule does not touch, the
same reaction fires and the remainder is carried through — which is what makes
the bag beside the hole a *context* rather than a decoration. -/
theorem reaction_realised_in_context :
    rewriteAt evaluator platform 6
        (asProcess (redexParts ++ [.apply stopDeclaration.label []]))
      = [asProcess (reactumParts ++ [.apply stopDeclaration.label []])] := by
  decide +kernel

/-! ## The categorical rule, and the congruence -/

/-- The redex and reactum as bags. -/
def redexBag : Multiset Pattern := (redexParts : Multiset Pattern)

def reactumBag : Multiset Pattern := (reactumParts : Multiset Pattern)

/-- The agent, and the label that completes it. -/
def agentBag : Multiset Pattern := ([outputA] : List Pattern)

def labelBag : Multiset Pattern := ([receiverTerm, outputB] : List Pattern)

/-- The join, as a reaction rule of the bag category. -/
def joinReaction : ReactionRule (Mettapedia.GSLT.BagRelativePushout.Obj Pattern) where
  codomain := Mettapedia.GSLT.BagRelativePushout.Obj Pattern
  redex := bag redexBag
  reactum := bag reactumBag

/-- The one-rule theory. -/
def platformRules : ReactionRule (Mettapedia.GSLT.BagRelativePushout.Obj Pattern) → Prop := fun rule => rule = joinReaction

/-- **Every span of the platform's context category has relative pushouts.**  So
every reaction it can perform has a least label for its redex. -/
theorem platform_hasRelativePushouts (agent redex : Multiset Pattern) :
    HasRelativePushouts (bag agent) (bag redex) :=
  hasRelativePushouts agent redex

/-- **Item two, on this presentation.**  Context-labelled bisimilarity of the
platform's reactions is a congruence, for every context, with nothing assumed:
the existence hypothesis is discharged by the context category being bags. -/
theorem platform_congruence
    {left right : _root_.Mettapedia.GSLT.BagRelativePushout.Obj Pattern ⟶ _root_.Mettapedia.GSLT.BagRelativePushout.Obj Pattern}
    (bisim : IPOBisimilar platformRules left right)
    (context : _root_.Mettapedia.GSLT.BagRelativePushout.Obj Pattern ⟶ _root_.Mettapedia.GSLT.BagRelativePushout.Obj Pattern) :
    IPOBisimilar platformRules (_root_.CategoryTheory.CategoryStruct.comp left context) (_root_.CategoryTheory.CategoryStruct.comp right context) :=
  congruence platformRules bisim context

/-- **The labelled transition relation is inhabited.**  An agent supplying one
of the two outputs steps under the label that supplies the rest — and the label
is least for that redex, because the two legs of the bound share nothing. -/
theorem platform_act :
    ActIPO platformRules (bag labelBag) (bag agentBag)
      (_root_.CategoryTheory.CategoryStruct.comp (bag reactumBag) (bag (0 : Multiset Pattern))) := by
  refine ⟨joinReaction, rfl, bag (0 : Multiset Pattern), ?_, ?_, rfl⟩
  · show _root_.CategoryTheory.CategoryStruct.comp (bag agentBag) (bag labelBag)
        = _root_.CategoryTheory.CategoryStruct.comp (bag redexBag) (bag (0 : Multiset Pattern))
    rw [bag_comp, bag_comp]
    refine congrArg bag ?_
    simp only [agentBag, labelBag, redexBag, redexParts, add_zero]
    decide
  · exact isIdemPushout_bag agentBag redexBag labelBag 0 _ (by simp)

/-! ## The backward box on this presentation

`LeastEnablerBox` leaves `BackwardImageFiniteModulo` to each theory, and over
absolute least enablers it is not merely undischarged but unavailable: those
labels fail to exist at sources with two incomparable completions and fail to
compose.  Over idem-pushout labels the same hypothesis is arithmetic, and the
platform meets it. -/

/-- The instantiated rule set is a singleton, so it is finite.  This is not
finiteness of rho's reaction relation: `platformRules` is one ground instance of
the join schema, and the schema induces infinitely many bag reactions.  Backward
image finiteness for the schema is a different statement and is not proved. -/
theorem platformRules_finite : {rule | platformRules rule}.Finite :=
  Set.finite_singleton joinReaction

/-- **Backward image finiteness, discharged.**  The context monoid is bags,
which cancel, and there is one rule; so every agent has finitely many labelled
predecessors under each label. -/
theorem platform_backwardImageFiniteModulo
    (observations : Mettapedia.GSLT.IPOBox.Observations (Mettapedia.GSLT.BagRelativePushout.Bag Pattern)) :
    Mettapedia.GSLT.IPOBox.BackwardImageFiniteModulo platformRules observations :=
  Mettapedia.GSLT.IPOBox.backwardImageFiniteModulo_of_cancel platformRules
    platformRules_finite observations

/-- **The backward step family is inhabited**, so the adequacy below is not a
statement about an empty relation: it is the step of `platform_act`, read in the
direction the box reads it. -/
theorem platform_backwardAct
    (observations : Mettapedia.GSLT.IPOBox.Observations (Mettapedia.GSLT.BagRelativePushout.Bag Pattern)) :
    (Mettapedia.GSLT.IPOBox.ipoBackwardSystem platformRules observations).act (bag labelBag)
      (_root_.CategoryTheory.CategoryStruct.comp (bag reactumBag) (bag (0 : Multiset Pattern)))
      (bag agentBag) :=
  platform_act

/-- **And so the backward box is adequate here, with nothing left open.**
Logical equivalence in the backward labelled logic is backward bisimilarity, on
the presentation's own reaction, over the labels that carry the congruence. -/
theorem platform_backward_adequacy
    (observations : Mettapedia.GSLT.IPOBox.Observations (Mettapedia.GSLT.BagRelativePushout.Bag Pattern))
    (left right : _root_.Mettapedia.GSLT.BagRelativePushout.Obj Pattern ⟶ _root_.Mettapedia.GSLT.BagRelativePushout.Obj Pattern) :
    (Mettapedia.GSLT.IPOBox.ipoBackwardSystem platformRules observations).LogicallyEquivalent left right ↔
      (Mettapedia.GSLT.IPOBox.ipoBackwardSystem platformRules observations).Bisimilar left right :=
  Mettapedia.GSLT.IPOBox.backward_logicallyEquivalent_iff_bisimilar platformRules observations
    (platform_backwardImageFiniteModulo observations) left right

/-! ## The guard cannot smuggle in the observer's instruments

`ObserverReconstruction` closes the authored half of its argument under one
condition on the surroundings: the relation environment hands back no row
mentioning a constructor's argument former.  That condition is discharged here on
the environment this presentation actually uses, rather than left standing. -/

open Mettapedia.OSLF.Framework.ObserverExtension
  (argsLabel openedRules)
open Mettapedia.OSLF.MeTTaIL.OccurringLabels (labelsList)

/-- An argument former is never one of the guard's channel constants: it begins
with its own bracketed prefix and so is longer than either. -/
theorem argsLabel_ne_channel (constructor : String) :
    argsLabel constructor ≠ "A" ∧ argsLabel constructor ≠ "B" := by
  have prefixLen : "Args⟨".length = 5 := rfl
  have suffixLen : "⟩".length = 1 := rfl
  have oneA : "A".length = 1 := rfl
  have oneB : "B".length = 1 := rfl
  constructor
  · intro equal
    have lengths := congrArg String.length equal
    simp only [argsLabel, String.length_append, prefixLen, suffixLen, oneA] at lengths
    omega
  · intro equal
    have lengths := congrArg String.length equal
    simp only [argsLabel, String.length_append, prefixLen, suffixLen, oneB] at lengths
    omega

/-- **The platform's guard meets the condition.**  Its only row holds channel
constants, so no where-guard of this presentation can hand a rule an argument
bundle. -/
theorem guard_rows_avoid (constructor : String) :
    ∀ relation arguments tuple, tuple ∈ guard.tuples relation arguments →
      argsLabel constructor ∉ labelsList tuple := by
  intro relation arguments tuple member
  simp only [guard] at member
  split at member
  · simp only [List.mem_singleton] at member
    subst member
    obtain ⟨notA, notB⟩ := argsLabel_ne_channel constructor
    simp [labelsList, channelA, channelB,
      Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply, notA, notB]
  · simp at member

/-- **So the observer's argument runs on this presentation.**  The condition its
authored half rests on is discharged, not assumed. -/
theorem guard_evaluatorAvoids (constructor : String) :
    Mettapedia.OSLF.Framework.ObserverReconstruction.EvaluatorAvoids
      evaluator (argsLabel constructor) :=
  Mettapedia.OSLF.Framework.ObserverReconstruction.evaluatorAvoids_of_env
    (guard_rows_avoid constructor)

/-! ## The platform's authored rules are tame

`ObserverReconstruction.reads_head_iff` runs on presentations whose authored
rules meet three conditions, each of which a canary showed necessary.  The
platform meets all three, and at every arity list rather than at one: its two
rule families have a single relation-query premise apiece, that premise mentions
no constructor at all, and their right-hand sides cite only constructors the
presentation declares. -/

open Mettapedia.OSLF.MeTTaIL.OccurringLabels (labels labelsList)
open Mettapedia.OSLF.Framework.ObserverReconstruction
  (AuthoredRulesTame IsCongruence PremiseAvoids)

/-- Every rule of the platform is a join or a persistent join at a supported
arity. -/
theorem rhoPlatform_rule_shape {arities : List Nat} {rule : RewriteRule}
    (member : rule ∈ (rhoPlatform arities).rewrites) :
    ∃ arity ∈ arities, rule = joinRule arity ∨ rule = persistentJoinRule arity := by
  rw [rhoPlatform_rewrites] at member
  obtain ⟨arity, arityMember, ruleMember⟩ := List.mem_flatMap.mp member
  refine ⟨arity, arityMember, ?_⟩
  simpa using ruleMember

/-- A supported arity's tuple former and both join formers are declared. -/
theorem rhoPlatform_arity_declared {arities : List Nat} {arity : Nat}
    (member : arity ∈ arities) :
    tupleLabel arity ∈ (rhoPlatform arities).terms.map GrammarRule.label ∧
      persistentJoinLabel arity
        ∈ (rhoPlatform arities).terms.map GrammarRule.label := by
  constructor <;>
    · simp only [rhoPlatform, List.map_cons, List.mem_cons, List.map_flatMap,
        List.mem_flatMap]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨arity, member, ?_⟩))))
      simp [joinDeclaration, tupleDeclaration]

/-- The quote former is declared. -/
theorem rhoPlatform_quote_declared (arities : List Nat) :
    quoteLabel ∈ (rhoPlatform arities).terms.map GrammarRule.label := by
  simp [rhoPlatform, quoteDeclaration]

/-- **Tame, at every arity list.** -/
theorem rhoPlatform_tame (arities : List Nat) (constructor : String) :
    AuthoredRulesTame (rhoPlatform arities) (argsLabel constructor) where
  noSteps := by
    intro rule member premise premiseMember
    obtain ⟨arity, -, shape⟩ := rhoPlatform_rule_shape member
    rcases shape with rfl | rfl <;>
      · simp only [joinRule, persistentJoinRule, List.mem_singleton] at premiseMember
        subst premiseMember
        exact id
  clean := by
    intro rule member premise premiseMember
    obtain ⟨arity, -, shape⟩ := rhoPlatform_rule_shape member
    rcases shape with rfl | rfl <;>
      · simp only [joinRule, persistentJoinRule, List.mem_singleton] at premiseMember
        subst premiseMember
        simp [PremiseAvoids, Mettapedia.OSLF.MeTTaIL.OccurringLabels.premiseLabels,
          channelPatterns]
  rights := by
    have delivered : ∀ (arities : List Nat) (arity : Nat), arity ∈ arities →
        labels (firedContinuation arity)
          ⊆ (rhoPlatform arities).terms.map GrammarRule.label := by
      intro arities arity arityMember label occurs
      obtain ⟨tupleDecl, -⟩ := rhoPlatform_arity_declared arityMember
      simp only [firedContinuation, deliveredName, deliveredTuple,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_subst,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_fvar,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_cons,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_nil,
        valuePatterns, Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_fvars,
        List.nil_append, List.append_nil, List.mem_cons] at occurs
      rcases occurs with rfl | occurs
      · exact rhoPlatform_quote_declared arities
      · rcases occurs with rfl | impossible
        · exact tupleDecl
        · simp at impossible
    intro rule member label occurs
    obtain ⟨arity, arityMember, shape⟩ := rhoPlatform_rule_shape member
    obtain ⟨-, joinDecl⟩ := rhoPlatform_arity_declared arityMember
    rcases shape with rfl | rfl
    · simp only [joinRule,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_collection,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_cons,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_nil,
        List.append_nil] at occurs
      exact delivered arities arity arityMember occurs
    · simp only [persistentJoinRule, receiver,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_collection,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_cons,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_nil,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_apply,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_append,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_lambda,
        Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_fvar,
        channelPatterns, Mettapedia.OSLF.MeTTaIL.OccurringLabels.labelsList_fvars,
        List.append_nil, List.mem_append, List.mem_cons] at occurs
      rcases occurs with inDelivered | inReceiver
      · exact delivered arities arity arityMember inDelivered
      · rcases inReceiver with rfl | impossible
        · exact joinDecl
        · simp at impossible

/-- **The platform's left-hand sides are rigid**, at every arity list: both rule
families match on a bag, never on a bare metavariable, so no rule of theirs can
answer an instrument's request in place of the instrument's own rule. -/
theorem rhoPlatform_rigidHeads (arities : List Nat) :
    Mettapedia.OSLF.Framework.ObserverReconstruction.RigidHeads (rhoPlatform arities) := by
  intro rule member
  obtain ⟨arity, -, shape⟩ := rhoPlatform_rule_shape member
  rcases shape with rfl | rfl <;>
    simp [Mettapedia.OSLF.Framework.ObserverReconstruction.IsVariable,
      joinRule, persistentJoinRule]

/-- **The platform's left-hand sides cite only declared constructors**, at every
arity list: both rule families match on a bag, so the condition holds with
nothing to check. -/
theorem rhoPlatform_leftHeadsDeclared (arities : List Nat) :
    Mettapedia.OSLF.Framework.ObserverReconstruction.LeftHeadsDeclared
      (rhoPlatform arities) := by
  intro rule member
  obtain ⟨arity, -, shape⟩ := rhoPlatform_rule_shape member
  rcases shape with rfl | rfl <;>
    simp [Mettapedia.OSLF.Framework.ObserverReconstruction.LeftHeadDeclared,
      joinRule, persistentJoinRule]

/-- Opening the output former opens exactly one declaration. -/
theorem rhoPlatform_out_openedRules :
    openedRules (rhoPlatform [2]) ["Out"] = [outDeclaration] := by
  decide +kernel

/-- So arity agreement is immediate. -/
theorem rhoPlatform_out_arities :
    ∀ first ∈ openedRules (rhoPlatform [2]) ["Out"],
      ∀ second ∈ openedRules (rhoPlatform [2]) ["Out"],
        first.label = second.label → first.params.length = second.params.length := by
  intro first firstMember second secondMember _
  rw [rhoPlatform_out_openedRules] at firstMember secondMember
  simp only [List.mem_singleton] at firstMember secondMember
  rw [firstMember, secondMember]

/-- **The whole setting, discharged for rho.**  The observer's argument runs on
this presentation with every one of its five conditions proved rather than
assumed: freshness by computation, the guard by `guard_evaluatorAvoids`, tameness
and rigidity at every arity list, and arity agreement because exactly one
declaration is opened. -/
theorem rhoPlatform_observerSetting :
    Mettapedia.OSLF.Framework.ObserverReconstruction.ObserverSetting
      evaluator (rhoPlatform [2]) .hashBag ["Out"] "Out" :=
  { fresh := by decide +kernel
    confined := guard_evaluatorAvoids "Out"
    tame := rhoPlatform_tame [2] "Out"
    rigid := rhoPlatform_rigidHeads [2]
    cited := rhoPlatform_leftHeadsDeclared [2]
    arities := rhoPlatform_out_arities }

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels
