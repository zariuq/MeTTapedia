import Mettapedia.GSLT.Logic.IPOSystem
import Mettapedia.GSLT.Logic.HigherOrderContextClosure
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Types.Basic

/-!
# Context-labelled bisimilarity is a congruence

`AdmissibleContextCongruence` proves a congruence from `LeastEnablerComposes`,
and `RedexRelativeEnabling` proves that property cannot hold: a source
completable two incomparable ways has no least enabling context at all, so the
transition relation that demands one is blind.

This module proves the congruence the other way — from the universal property
that *does* hold.  A label is least for the redex it exposes, the two-square
lemmas of `RelativePushout` say how such labels compose, and the congruence
follows for **every** context in this literal-label, empty-observation system.
This does not eliminate admissibility conditions for observations or behavioral
comparison of process-bearing labels.

**The shape of the argument.**  A step out of a filled context presents a bound
at the filling; relative pushouts reduce it to a least one, so the filling has a
step of its own with a smaller label.  Bisimilarity matches that step.  Pasting
puts the context back, and the residual lemma says the square that puts it back
is itself least — so the matched step, refilled, carries the original label.
The local replay discharges a rule of the shared finite derivation closure;
the general coinduction theorem then gives contextual congruence.

**What is assumed.**  Relative pushouts for the spans that arise, which is the
hypothesis Leifer and Milner's development runs on and which
`RedexRelativeEnabling.twoChannel_hasRelativePushouts` discharges for a real
theory.

**Interfaces are carried.** Agents are arrows from a fixed origin into their
current interface; contexts and labels are arbitrary composable arrows. A
bisimulation is a family over interfaces, so matching a transition also matches
its result interface. The one-object context monoids are instances of this
construction, not its definition.

Relative pushouts are still a hypothesis to discharge in each context category.
Labels are matched literally; behavioral comparison of higher-order label
payloads is a separate obligation, not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RedexRelativeCongruence

open CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe v u

variable {C : Type u} [Category.{v} C] {origin : C}

/-- The single object whose endomorphisms are the contexts. -/
abbrev Obj (M : Type u) [Monoid M] : SingleObj M := SingleObj.star M

/-! ## Bisimilarity -/

theorem ipoBisimilar_forward {rules : ReactionRule origin → Prop} {interface nextInterface : C}
    {left right : origin ⟶ interface} (bisim : IPOBisimilar rules left right)
    {label : interface ⟶ nextInterface} {next : origin ⟶ nextInterface}
    (step : ActIPO rules label left next) :
    ∃ matched, ActIPO rules label right matched ∧ IPOBisimilar rules next matched := by
  obtain ⟨relation, isBisim, related⟩ := bisim
  obtain ⟨matched, matchedStep, matchedRelated⟩ := (isBisim left right related).1 label next step
  exact ⟨matched, matchedStep, ⟨relation, isBisim, matchedRelated⟩⟩

theorem ipoBisimilar_backward {rules : ReactionRule origin → Prop} {interface nextInterface : C}
    {left right : origin ⟶ interface} (bisim : IPOBisimilar rules left right)
    {label : interface ⟶ nextInterface} {next : origin ⟶ nextInterface}
    (step : ActIPO rules label right next) :
    ∃ matched, ActIPO rules label left matched ∧ IPOBisimilar rules matched next := by
  obtain ⟨relation, isBisim, related⟩ := bisim
  obtain ⟨matched, matchedStep, matchedRelated⟩ := (isBisim left right related).2 label next step
  exact ⟨matched, matchedStep, ⟨relation, isBisim, matchedRelated⟩⟩

/-! ## Local context replay and finite congruence -/

/-- Finite context rules use the same typed state-pair judgments as
higher-order coinduction. No separate closure relation is defined. -/
abbrev AgentJudgment (origin : C) :=
  HigherOrderBisimulation.Judgment (fun interface : C => origin ⟶ interface)

inductive ContextRules (origin : C) :
    List (AgentJudgment origin) → AgentJudgment origin → Prop
  | fill {interface nextInterface : C} (left right : origin ⟶ interface)
      (context : interface ⟶ nextInterface) :
      ContextRules origin [⟨interface, left, right⟩]
        ⟨nextInterface, left ≫ context, right ≫ context⟩

/-- One-direction replay factors the original bound, matches its inner IPO,
and pastes the matching square back. The candidate is merely structurally
closed; no bisimilarity or contextual-congruence premise is used. -/
theorem actIPO_context_replay {rules : ReactionRule origin → Prop}
    (hasRPO : ∀ (interface : C) (agent : origin ⟶ interface) (rule : ReactionRule origin),
      rules rule → HasRelativePushouts agent rule.redex)
    (relation : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop)
    (contextClosed : ∀ {interface targetInterface : C}
      {left right : origin ⟶ interface}, relation interface left right →
        (context : interface ⟶ targetInterface) →
          relation targetInterface (left ≫ context) (right ≫ context))
    {interface outerInterface : C} {left right : origin ⟶ interface}
    (matchesInner : ∀ {nextInterface : C} (label : interface ⟶ nextInterface) next,
      ActIPO rules label left next →
        ∃ matched, ActIPO rules label right matched ∧ relation nextInterface next matched)
    (context : interface ⟶ outerInterface)
    {nextInterface : C} {label : outerInterface ⟶ nextInterface}
    {next : origin ⟶ nextInterface} (step : ActIPO rules label (left ≫ context) next) :
    ∃ matched, ActIPO rules label (right ≫ context) matched ∧
      relation nextInterface next matched := by
  obtain ⟨rule, rulesMem, reaction, square, ipo, targetEq⟩ := step
  have bound : left ≫ (context ≫ label) = rule.redex ≫ reaction := by
    rw [← Category.assoc]
    exact square
  obtain ⟨reduced, rpo⟩ := hasRPO _ left rule rulesMem _ (context ≫ label) reaction bound
  have innerIPO : IsIdemPushout left rule.redex reduced.inl reduced.inr reduced.comm :=
    isIdemPushout_of_isRelativePushout rpo
  have innerStep : ActIPO rules reduced.inl left (rule.reactum ≫ reduced.inr) :=
    ⟨rule, rulesMem, reduced.inr, reduced.comm, innerIPO, rfl⟩
  obtain ⟨matched, matchedStep, matchedRelated⟩ := matchesInner reduced.inl _ innerStep
  obtain ⟨matchedRule, matchedMem, matchedReaction, matchedSquare, matchedIPO, matchedEq⟩ :=
    matchedStep
  have outerIPO :
      IsIdemPushout context reduced.inl label reduced.down reduced.fac_left.symm :=
    isIdemPushout_residual left rule.redex context label reaction square ipo reduced rpo
  have squarePasted : (right ≫ context) ≫ label =
      matchedRule.redex ≫ (matchedReaction ≫ reduced.down) := by
    calc (right ≫ context) ≫ label
        = right ≫ (context ≫ label) := Category.assoc _ _ _
      _ = right ≫ (reduced.inl ≫ reduced.down) := by rw [reduced.fac_left]
      _ = (right ≫ reduced.inl) ≫ reduced.down := (Category.assoc _ _ _).symm
      _ = (matchedRule.redex ≫ matchedReaction) ≫ reduced.down := by rw [matchedSquare]
      _ = matchedRule.redex ≫ (matchedReaction ≫ reduced.down) := Category.assoc _ _ _
  have pasted := isIdemPushout_paste right matchedRule.redex reduced.inl matchedReaction
    context label reduced.down matchedSquare reduced.fac_left.symm
    (hasRPO _ right matchedRule matchedMem) matchedIPO outerIPO
  refine ⟨matchedRule.reactum ≫ (matchedReaction ≫ reduced.down),
    ⟨matchedRule, matchedMem, matchedReaction ≫ reduced.down, squarePasted, pasted, rfl⟩, ?_⟩
  have nextEq : next = (rule.reactum ≫ reduced.inr) ≫ reduced.down := by
    rw [targetEq, Category.assoc, reduced.fac_right]
  rw [nextEq, ← Category.assoc, ← matchedEq]
  exact contextClosed matchedRelated reduced.down

open Mettapedia.Logic HigherOrderBisimulation

private theorem candidate_context_closed (candidate : AgentJudgment origin → Prop)
    (closed : FinitaryClosure.Closed (ContextRules origin) candidate) :
    ∀ {interface targetInterface : C} {left right : origin ⟶ interface},
      unpack candidate interface left right → (context : interface ⟶ targetInterface) →
        unpack candidate targetInterface (left ≫ context) (right ≫ context) := by
  intro interface targetInterface left right related context
  exact closed [⟨interface, left, right⟩] _
    (.fill left right context) (fun premise member => by
      have equal := List.mem_singleton.mp member
      subst premise
      exact related)

/-- RPO decomposition and replay discharge the local finite-context rule
obligation against arbitrary closed candidates, not only bisimilarity. -/
theorem contextRules_locally_respectful {rules : ReactionRule origin → Prop}
    (hasRPO : ∀ (interface : C) (agent : origin ⟶ interface) (rule : ReactionRule origin),
      rules rule → HasRelativePushouts agent rule.redex) :
    FinitaryClosure.LocallyRespectful (ContextRules origin)
      (ipoSystem rules).progressOnJudgments := by
  intro candidate closed premises conclusion rule _children advances
  cases rule with
  | fill left right context =>
    have inner := advances _ (List.mem_singleton_self _)
    obtain ⟨forward, backward, -⟩ := inner
    have preserves : ∀ {interface targetInterface : C}
        {first second : origin ⟶ interface}, unpack candidate interface first second →
          (surround : interface ⟶ targetInterface) →
            unpack candidate targetInterface (first ≫ surround) (second ≫ surround) :=
      candidate_context_closed candidate closed
    have matchesForward : ∀ {nextInterface : C} (label : _ ⟶ nextInterface) next,
        ActIPO rules label left next →
          ∃ matched, ActIPO rules label right matched ∧ unpack candidate nextInterface next matched := by
      intro nextInterface label next step
      obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
        forward (literalLabel label) next step
      have equal := Label.skeleton_eq labels
      change label = matchedLabel.skeleton at equal
      change ActIPO rules matchedLabel.skeleton right matched at matchedStep
      rw [← equal] at matchedStep
      exact ⟨matched, matchedStep, successors⟩
    have matchesBackward : ∀ {nextInterface : C} (label : _ ⟶ nextInterface) next,
        ActIPO rules label right next →
          ∃ matched, ActIPO rules label left matched ∧ unpack candidate nextInterface matched next := by
      intro nextInterface label next step
      obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
        backward (literalLabel label) next step
      have equal := Label.skeleton_eq labels
      change matchedLabel.skeleton = label at equal
      change ActIPO rules matchedLabel.skeleton left matched at matchedStep
      rw [equal] at matchedStep
      exact ⟨matched, matchedStep, successors⟩
    refine ⟨?_, ?_, fun atom => Empty.elim atom⟩
    · intro nextInterface label next step
      obtain ⟨matched, matchedStep, successors⟩ :=
        actIPO_context_replay hasRPO (unpack candidate) preserves matchesForward context step
      exact ⟨literalLabel label.skeleton, matched, matchedStep,
        (relates_literal_iff (unpack candidate) label (literalLabel label.skeleton)).mpr rfl,
        successors⟩
    · intro nextInterface label next step
      obtain ⟨matched, matchedStep, successors⟩ :=
        actIPO_context_replay hasRPO (fun interface first second =>
          unpack candidate interface second first)
          (fun related surround => preserves related surround) matchesBackward context step
      exact ⟨literalLabel label.skeleton, matched, matchedStep,
        (relates_literal_iff (unpack candidate) (literalLabel label.skeleton) label).mpr rfl,
        successors⟩

/-- Context-labelled bisimilarity is preserved by every composable context,
through the shared finite-closure construction and the actual local RPO replay. -/
theorem ipoBisimilar_comp {rules : ReactionRule origin → Prop}
    (hasRPO : ∀ (interface : C) (agent : origin ⟶ interface) (rule : ReactionRule origin),
      rules rule → HasRelativePushouts agent rule.redex)
    {interface outerInterface : C}
    {left right : origin ⟶ interface} (bisim : IPOBisimilar rules left right)
    (context : interface ⟶ outerInterface) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) := by
  have seed : (ipoSystem rules).Bisimilar interface left right :=
    (ipo_bisimilar_iff rules left right).mpr bisim
  have derivation : FinitaryClosure.close (ContextRules origin)
      (pack (ipoSystem rules).Bisimilar)
        ⟨outerInterface, left ≫ context, right ≫ context⟩ :=
    Derives.node [⟨interface, left, right⟩] _
      (Or.inr (.fill left right context)) (fun premise member => by
        have equal := List.mem_singleton.mp member
        subst premise
        exact FinitaryClosure.seeds_le_close _ _ _ seed)
  exact (ipo_bisimilar_iff rules (left ≫ context) (right ≫ context)).mp
    ((ipoSystem rules).finite_closure_bisimilar (ContextRules origin)
      (contextRules_locally_respectful hasRPO) derivation)

/-! ## Behavioral classes at each interface -/

theorem ipoBisimilar_refl (rules : ReactionRule origin → Prop) {interface : C}
    (agent : origin ⟶ interface) : IPOBisimilar rules agent agent := by
  exact (ipo_bisimilar_iff rules agent agent).mp
    ((ipoSystem rules).bisimilar_refl interface agent)

theorem ipoBisimilar_symm {rules : ReactionRule origin → Prop} {interface : C}
    {left right : origin ⟶ interface} (bisim : IPOBisimilar rules left right) :
    IPOBisimilar rules right left := by
  exact (ipo_bisimilar_iff rules right left).mp
    ((ipoSystem rules).bisimilar_symm ((ipo_bisimilar_iff rules left right).mpr bisim))

theorem ipoBisimilar_trans {rules : ReactionRule origin → Prop} {interface : C}
    {left middle right : origin ⟶ interface}
    (first : IPOBisimilar rules left middle) (second : IPOBisimilar rules middle right) :
    IPOBisimilar rules left right := by
  exact (ipo_bisimilar_iff rules left right).mp
    ((ipoSystem rules).bisimilar_trans
      ((ipo_bisimilar_iff rules left middle).mpr first)
      ((ipo_bisimilar_iff rules middle right).mpr second))

/-- Literal-label behavioral equivalence at one interface. -/
def bisimSetoid (rules : ReactionRule origin → Prop) (interface : C) :
    Setoid (origin ⟶ interface) where
  r := IPOBisimilar rules
  iseqv := ⟨ipoBisimilar_refl rules, ipoBisimilar_symm, ipoBisimilar_trans⟩

/-- Behavioral classes retain their interface. -/
def BisimClass (rules : ReactionRule origin → Prop) (interface : C) : Type v :=
  Quotient (bisimSetoid rules interface)

def toClass (rules : ReactionRule origin → Prop) {interface : C}
    (agent : origin ⟶ interface) : BisimClass rules interface :=
  Quotient.mk (bisimSetoid rules interface) agent

theorem class_eq_iff (rules : ReactionRule origin → Prop) {interface : C}
    (left right : origin ⟶ interface) :
    toClass rules left = toClass rules right ↔ IPOBisimilar rules left right :=
  Quotient.eq

/-- Context composition descends to behavioral classes by the congruence
theorem, without choosing a representative. -/
def contextClassMap {rules : ReactionRule origin → Prop}
    (hasRPO : ∀ (interface : C) (agent : origin ⟶ interface) (rule : ReactionRule origin),
      rules rule → HasRelativePushouts agent rule.redex)
    {interface nextInterface : C} (context : interface ⟶ nextInterface) :
    BisimClass rules interface → BisimClass rules nextInterface :=
  Quotient.map (fun agent => agent ≫ context)
    (fun _ _ bisim => ipoBisimilar_comp hasRPO bisim context)

@[simp] theorem contextClassMap_toClass {rules : ReactionRule origin → Prop}
    (hasRPO : ∀ (interface : C) (agent : origin ⟶ interface) (rule : ReactionRule origin),
      rules rule → HasRelativePushouts agent rule.redex)
    {interface nextInterface : C} (context : interface ⟶ nextInterface)
    (agent : origin ⟶ interface) :
    contextClassMap hasRPO context (toClass rules agent) = toClass rules (agent ≫ context) :=
  rfl

/-- A genuine functor from the context category to its interface-indexed
behavioral class sets. It concerns literal labels and the stated RPO hypothesis;
it does not supply higher-order label comparison or RPO existence. -/
def classFunctor {rules : ReactionRule origin → Prop}
    (hasRPO : ∀ (interface : C) (agent : origin ⟶ interface) (rule : ReactionRule origin),
      rules rule → HasRelativePushouts agent rule.redex) : C ⥤ Type v where
  obj := BisimClass rules
  map context := TypeCat.ofHom (contextClassMap hasRPO context)
  map_id interface := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext cls
    refine Quotient.inductionOn cls ?_
    intro agent
    change toClass rules (agent ≫ 𝟙 interface) = toClass rules agent
    rw [Category.comp_id]
  map_comp context next := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext cls
    refine Quotient.inductionOn cls ?_
    intro agent
    change toClass rules (agent ≫ (context ≫ next)) = toClass rules ((agent ≫ context) ≫ next)
    rw [Category.assoc]

/-! ## Interface-changing controls -/

namespace InterfaceControls

def grow : (Bool : Type) ⟶ Option Bool := TypeCat.ofHom Option.some

/-- The rule preserves its interface while changing its Boolean payload. -/
def flipRule : ReactionRule (Bool : Type) where
  codomain := Option Bool
  redex := grow
  reactum := TypeCat.ofHom (fun value => some (!value))

def rules : ReactionRule (Bool : Type) → Prop := fun rule => rule = flipRule

/-- A genuine labelled transition from the Bool interface to Option Bool.
The label is least for this redex by the candidate's universal property. -/
theorem interface_changing_step :
    ActIPO rules grow (𝟙 (Bool : Type)) flipRule.reactum := by
  unfold rules flipRule
  refine ⟨⟨Option Bool, grow, TypeCat.ofHom (fun value => some (!value))⟩,
    rfl, 𝟙 (Option Bool), by simp, ?_, by simp⟩
  intro candidate
  refine ⟨candidate.inr, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [Candidate.self] using candidate.comm.symm
  · change 𝟙 (Option Bool) ≫ candidate.inr = candidate.inr
    exact Category.id_comp candidate.inr
  · exact candidate.fac_right
  · rintro mediator ⟨-, right, -⟩
    dsimp only [Candidate.self] at mediator right ⊢
    exact (Category.id_comp mediator).symm.trans right

/-- The reactum depends on the input and differs from the redex. -/
theorem payloads_are_distinct :
    flipRule.reactum false = some true ∧ flipRule.reactum true = some false ∧
      flipRule.reactum ≠ flipRule.redex := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  have atFalse := congrArg (fun arrow : (Bool : Type) ⟶ Option Bool => arrow false) equal
  change some true = some false at atFalse
  cases atFalse

/-- A context shared by both legs enables the identity redex, but is not a
least label: its unused Option.none branch cannot be recovered through Bool. -/
theorem shared_context_is_not_least :
    ¬ IsIdemPushout (𝟙 (Bool : Type)) (𝟙 (Bool : Type)) grow grow (by simp) := by
  intro ipo
  let candidate : Candidate (𝟙 (Bool : Type)) (𝟙 (Bool : Type)) grow grow :=
    { apex := Bool
      inl := 𝟙 Bool
      inr := 𝟙 Bool
      down := grow
      comm := rfl
      fac_left := by simp
      fac_right := by simp }
  obtain ⟨section_, recovers⟩ := ipo.down_splits candidate
  have atNone := congrArg
    (fun arrow : (Option Bool : Type) ⟶ Option Bool => arrow none) recovers
  change some (section_ none) = none at atNone
  cases atNone

end InterfaceControls

#print axioms actIPO_context_replay
#print axioms contextRules_locally_respectful
#print axioms ipoBisimilar_comp
#print axioms ipoBisimilar_refl
#print axioms ipoBisimilar_symm
#print axioms ipoBisimilar_trans
#print axioms classFunctor
#print axioms InterfaceControls.interface_changing_step
#print axioms InterfaceControls.payloads_are_distinct
#print axioms InterfaceControls.shared_context_is_not_least

end Mettapedia.GSLT.RedexRelativeCongruence
