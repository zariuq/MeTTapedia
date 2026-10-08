import Mettapedia.OSLF.Framework.PartialStructuralObservers
import Mettapedia.OSLF.Framework.ObserverReconstruction

/-!
# Actual administrative firings of the labelled instrument calculus

A presentation supplies actual declared constructors, their arities, distinct
names, and projectable argument positions. These are local grammar conditions;
they exclude handing an open binder body back as a closed argument. Each
supplied ask/get/build event is realized by its actual observer-extension rule,
with a retained matching substitution and exact target computation.

Reflection of arbitrary runtime responses additionally uses the independently
defined observer setting. In particular, freshness alone does not license
reflection in the presence of authored interference.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentRuntime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.OccurringLabels
open ObserverExtension ObserverReconstruction InstrumentObservations

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

structure Presentation (Symbols : Type u) (arity : Symbols → Nat) where
  language : LanguageDef
  declaration : Symbols → GrammarRule
  declared : ∀ constructor, declaration constructor ∈ language.terms
  arity_eq : ∀ constructor, (declaration constructor).params.length = arity constructor
  names_injective : Function.Injective (fun constructor => (declaration constructor).label)
  projectable : ∀ constructor (position : Fin (arity constructor)),
    ∃ sort, (position.val, sort) ∈ projectablePositions (declaration constructor)

def lower (presentation : Presentation Symbols arity) : Tree Symbols arity → Pattern
  | .node constructor arguments =>
      .apply (presentation.declaration constructor).label
        (List.ofFn fun position => lower presentation (arguments position))

def lowerState (presentation : Presentation Symbols arity) : State Symbols arity → Pattern
  | .term tree => lower presentation tree
  | .bundle (.node constructor arguments) =>
      .apply (argsLabel (presentation.declaration constructor).label)
        (List.ofFn fun position => lower presentation (arguments position))

def request (presentation : Presentation Symbols arity) (cut : CollType)
    (source : State Symbols arity) : Label Symbols arity → Pattern
  | .ask constructor => .collection cut
      [.apply (askLabel (presentation.declaration constructor).label) [],
        lowerState presentation source] none
  | .get constructor position =>
      .apply (getLabel (presentation.declaration constructor).label position.val)
        [lowerState presentation source]
  | .build constructor => .apply (buildLabel (presentation.declaration constructor).label)
      [lowerState presentation source]

def ruleFor (presentation : Presentation Symbols arity) (cut : CollType) :
    Label Symbols arity → RewriteRule
  | .ask constructor => openingRule cut (presentation.declaration constructor).label
      (presentation.declaration constructor).params.length
  | .get constructor position => projectionRule (presentation.declaration constructor).label
      (presentation.declaration constructor).params.length position.val
  | .build constructor => buildRule (presentation.declaration constructor).label
      (presentation.declaration constructor).params.length

def openedNames (presentation : Presentation Symbols arity) (kit : List Symbols) : List String :=
  kit.map fun constructor => (presentation.declaration constructor).label

private theorem exists_mem_of_mem_labelsList {patterns : List Pattern} {label : String}
    (member : label ∈ labelsList patterns) :
    ∃ pattern ∈ patterns, label ∈ labels pattern := by
  induction patterns with
  | nil => cases member
  | cons first rest inductionHypothesis =>
    rcases List.mem_append.mp member with here | later
    · exact ⟨first, List.mem_cons_self, here⟩
    · obtain ⟨pattern, entry, occurs⟩ := inductionHypothesis later
      exact ⟨pattern, List.mem_cons_of_mem _ entry, occurs⟩

theorem opened_declaration (presentation : Presentation Symbols arity) (kit : List Symbols)
    {constructor : Symbols} (permission : constructor ∈ kit) :
    presentation.declaration constructor ∈
      openedRules presentation.language (openedNames presentation kit) := by
  simp only [openedRules, List.mem_filter, List.contains_iff_mem]
  exact ⟨presentation.declared constructor, List.mem_map_of_mem permission⟩

theorem lower_authored (presentation : Presentation Symbols arity) (tree : Tree Symbols arity) :
    labels (lower presentation tree) ⊆ presentation.language.terms.map GrammarRule.label := by
  induction tree with
  | node constructor arguments inductionHypothesis =>
    intro label member
    simp only [lower, labels_apply, List.mem_cons] at member
    rcases member with rfl | member
    · exact List.mem_map_of_mem (presentation.declared constructor)
    · obtain ⟨_, entry, occurs⟩ := exists_mem_of_mem_labelsList member
      obtain ⟨position, rfl⟩ := List.mem_ofFn.mp entry
      exact inductionHypothesis position occurs

theorem lower_injective (presentation : Presentation Symbols arity) :
    Function.Injective (lower presentation) := by
  intro left
  induction left with
  | node constructor arguments inductionHypothesis =>
    intro right same
    cases right with
    | node second compared =>
      have parts := Pattern.apply.inj same
      have names := presentation.names_injective parts.1
      subst second
      have entries := List.ofFn_injective parts.2
      congr 1
      funext position
      exact inductionHypothesis position (congrFun entries position)

structure AdministrativeFiring (language : LanguageDef) (rule : RewriteRule)
    (source target : Pattern) where
  member : rule ∈ language.rewrites
  premiseFree : rule.premises = []
  bindings : Bindings
  matched : bindings ∈ matchPatternForRule language rule source
  delivered : applyBindingsForRule language rule bindings = target

theorem AdministrativeFiring.step {language : LanguageDef} {rule : RewriteRule}
    {source target : Pattern} (firing : AdministrativeFiring language rule source target)
    (base : BasePremiseEvaluator) : Step base language source target := by
  rw [← firing.delivered]
  exact step_of_premiseFree_match firing.member firing.premiseFree firing.matched

theorem buildRule_match_of_bundle (constructor : String) (arity : Nat)
    {arguments : List Pattern} (length : arguments.length = arity) :
    ∃ bindings, bindings ∈ matchPattern (buildRule constructor arity).left
        (.apply (buildLabel constructor) [.apply (argsLabel constructor) arguments]) ∧
      applyBindings bindings (buildRule constructor arity).right = .apply constructor arguments := by
  obtain ⟨bindings, matched, nodup, _, pairs⟩ :=
    Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgs_fvars (argVars arity) arguments
      (argVars_nodup arity) (by rw [argVars_length, length])
  have inner : MatchRel (.apply (argsLabel constructor) (argPatterns arity))
      (.apply (argsLabel constructor) arguments) bindings :=
    .apply (matchArgs_iff_matchArgsRel.mp matched) (by rw [argPatterns_length, length])
  have merged : mergeBindings bindings [] = some bindings := by simp [mergeBindings]
  refine ⟨bindings, matchPattern_iff_matchRel.mpr
    (.apply (.cons inner .nil merged) rfl), ?_⟩
  have delivered := Mettapedia.OSLF.MeTTaIL.LinearMatch.applyBindings_fvars bindings nodup
    (argVars arity) arguments (by rw [argVars_length, length]) pairs
  simpa only [buildRule, applyBindings, argPatterns] using congrArg (Pattern.apply constructor) delivered

theorem applyRuleBindings_buildRule (constructor : String) (arity : Nat) (bindings : Bindings) :
    applyRuleBindings (buildRule constructor arity) bindings =
      applyBindings bindings (buildRule constructor arity).right :=
  applyBindingsScoped_zero_of_binderFree _ bindings _
    (by simp only [buildRule, binderFree, binderFreeList_argPatterns])

def realizeEvent (presentation : Presentation Symbols arity) (kit : List Symbols)
    (cut : CollType) {source : State Symbols arity} {label : Label Symbols arity}
    {target : State Symbols arity}
    (event : Event (fun constructor => constructor ∈ kit) source label target) :
    AdministrativeFiring (observerExtension presentation.language cut (openedNames presentation kit))
      (ruleFor presentation cut label) (request presentation cut source label)
      (lowerState presentation target) := by
  apply Classical.choice
  cases event with
  | ask constructor arguments permission =>
    have length : (List.ofFn fun position => lower presentation (arguments position)).length =
        (presentation.declaration constructor).params.length := by
      rw [List.length_ofFn, presentation.arity_eq]
    obtain ⟨bindings, matched, delivered⟩ := openingRule_match_of_headed cut
      (presentation.declaration constructor).label _ length
    exact ⟨⟨openingRule_mem _ _ _ (opened_declaration presentation kit permission), rfl, bindings,
      by rw [matchPatternForRule_eq_syntactic]; exact matched,
      by simpa only [ruleFor, lowerState, applyBindingsForRule, applyBindingsForRuleUsing_empty,
        applyRuleBindings_openingRule] using delivered⟩⟩
  | get constructor arguments permission position =>
    obtain ⟨sort, projectable⟩ := presentation.projectable constructor position
    have bounded : position.val < (presentation.declaration constructor).params.length := by
      rw [presentation.arity_eq]; exact position.isLt
    have length : (List.ofFn fun position => lower presentation (arguments position)).length =
        (presentation.declaration constructor).params.length := by
      rw [List.length_ofFn, presentation.arity_eq]
    obtain ⟨bindings, matched, delivered⟩ := projectionRule_exposes
      (presentation.declaration constructor).label bounded length
    exact ⟨⟨projectionRule_mem _ _ _ (opened_declaration presentation kit permission) projectable,
      rfl, bindings,
      by rw [matchPatternForRule_eq_syntactic]; exact matched,
      by simpa only [ruleFor, lowerState, applyBindingsForRule, applyBindingsForRuleUsing_empty,
        applyRuleBindings_projectionRule, List.getElem_ofFn] using delivered⟩⟩
  | build constructor arguments permission =>
    have length : (List.ofFn fun position => lower presentation (arguments position)).length =
        (presentation.declaration constructor).params.length := by
      rw [List.length_ofFn, presentation.arity_eq]
    obtain ⟨bindings, matched, delivered⟩ := buildRule_match_of_bundle
      (presentation.declaration constructor).label _ length
    exact ⟨⟨buildRule_mem _ _ _ (opened_declaration presentation kit permission), rfl, bindings,
      by rw [matchPatternForRule_eq_syntactic]; exact matched,
      by simpa only [ruleFor, lowerState, lower, applyBindingsForRule, applyBindingsForRuleUsing_empty,
        applyRuleBindings_buildRule] using delivered⟩⟩

structure RuntimeReceipt (Origins : Type u) (presentation : Presentation Symbols arity)
    (kit : List Symbols) (cut : CollType) (source : State Symbols arity)
    (label : Label Symbols arity) (target : State Symbols arity) where
  supplied : Receipt Origins (fun constructor => constructor ∈ kit) source label target
  firing : AdministrativeFiring
    (observerExtension presentation.language cut (openedNames presentation kit))
    (ruleFor presentation cut label) (request presentation cut source label)
    (lowerState presentation target)

def realizeReceipt {Origins : Type u} (presentation : Presentation Symbols arity)
    (kit : List Symbols) (cut : CollType) {source : State Symbols arity}
    {label : Label Symbols arity} {target : State Symbols arity}
    (receipt : Receipt Origins (fun constructor => constructor ∈ kit) source label target) :
    RuntimeReceipt Origins presentation kit cut source label target :=
  ⟨receipt, realizeEvent presentation kit cut receipt.event⟩

theorem realizeReceipt_retains {Origins : Type u} (presentation : Presentation Symbols arity)
    (kit : List Symbols) (cut : CollType) {source : State Symbols arity}
    {label : Label Symbols arity} {target : State Symbols arity}
    (receipt : Receipt Origins (fun constructor => constructor ∈ kit) source label target) :
    (realizeReceipt presentation kit cut receipt).supplied = receipt := rfl

theorem RuntimeReceipt.step {Origins : Type u} {presentation : Presentation Symbols arity}
    {kit : List Symbols} {cut : CollType} {source : State Symbols arity}
    {label : Label Symbols arity} {target : State Symbols arity}
    (receipt : RuntimeReceipt Origins presentation kit cut source label target)
    (base : BasePremiseEvaluator) :
    Step base (observerExtension presentation.language cut (openedNames presentation kit))
      (request presentation cut source label) (lowerState presentation target) :=
  receipt.firing.step base

theorem runtime_ask_reflects (presentation : Presentation Symbols arity) (kit : List Symbols)
    (cut : CollType) (base : BasePremiseEvaluator) (constructor : Symbols)
    (permission : constructor ∈ kit)
    (setting : ObserverSetting base presentation.language cut (openedNames presentation kit)
      (presentation.declaration constructor).label) (tree : Tree Symbols arity) :
    (∃ arguments, Step base
        (observerExtension presentation.language cut (openedNames presentation kit))
        (request presentation cut (.term tree) (.ask constructor))
        (.apply (argsLabel (presentation.declaration constructor).label) arguments)) ↔
      ∃ arguments, tree = .node constructor arguments := by
  rw [request, lowerState,
    reads_head_iff base presentation.language cut (openedNames presentation kit) setting
      (opened_declaration presentation kit permission) rfl (lower_authored presentation tree)
      (by cases tree with
          | node second _ => exact List.mem_map_of_mem (presentation.declared second))]
  constructor
  · rintro ⟨arguments, shape, _⟩
    cases tree with
    | node second children =>
      have names := presentation.names_injective (Pattern.apply.inj shape).1
      subst second
      exact ⟨children, rfl⟩
  · rintro ⟨arguments, rfl⟩
    exact ⟨List.ofFn fun position => lower presentation (arguments position), rfl,
      by rw [List.length_ofFn, presentation.arity_eq]⟩

theorem runtime_projection_reflects (presentation : Presentation Symbols arity)
    (kit : List Symbols) (cut : CollType) (base : BasePremiseEvaluator)
    (constructor : Symbols) (permission : constructor ∈ kit)
    (setting : ObserverSetting base presentation.language cut (openedNames presentation kit)
      (presentation.declaration constructor).label)
    (arguments : Fin (arity constructor) → Tree Symbols arity)
    (position : Fin (arity constructor)) {target : Pattern}
    (stepped : Step base
      (observerExtension presentation.language cut (openedNames presentation kit))
      (request presentation cut (.bundle (.node constructor arguments)) (.get constructor position))
      target) : target = lower presentation (arguments position) := by
  obtain ⟨sort, projectable⟩ := presentation.projectable constructor position
  have member := opened_declaration presentation kit permission
  have bounded : position.val < (presentation.declaration constructor).params.length := by
    rw [presentation.arity_eq]; exact position.isLt
  have length : (List.ofFn fun position => lower presentation (arguments position)).length =
      (presentation.declaration constructor).params.length := by
    rw [List.length_ofFn, presentation.arity_eq]
  have getMember : getLabel (presentation.declaration constructor).label position.val ∈
      adjoinedLabels presentation.language (openedNames presentation kit) :=
    getLabel_mem_adjoinedLabels presentation.language (openedNames presentation kit)
      (declaration := presentation.declaration constructor) member
      (position := (position.val, sort)) projectable
  have delivered := projection_response base presentation.language cut
    (openedNames presentation kit)
    (constructor := (presentation.declaration constructor).label)
    (index := position.val)
    (arguments := List.ofFn fun position => lower presentation (arguments position))
    (target := target) setting
    (declaration := presentation.declaration constructor) member rfl bounded length getMember stepped
  simpa only [List.getElem_ofFn] using delivered

/-- Any admitted actual runtime instrument bisimulation preserves the complete
reachable structural view. Its matched responses are unrestricted steps of the
observer extension; response determinacy is earned from the observer setting. -/
theorem runtime_bisimulation_preserves_view (presentation : Presentation Symbols arity)
    (kit : List Symbols) (cut : CollType) (base : BasePremiseEvaluator)
    (relation : Pattern → Pattern → Prop)
    (bisimulation : IsInstrumentBisimulation base presentation.language cut
      (openedNames presentation kit) relation)
    (settings : ∀ constructor, constructor ∈ kit →
      ObserverSetting base presentation.language cut (openedNames presentation kit)
        (presentation.declaration constructor).label)
    {left right : Tree Symbols arity} (related : relation (lower presentation left)
      (lower presentation right)) :
    view (fun constructor => constructor ∈ kit) left =
      view (fun constructor => constructor ∈ kit) right := by
  classical
  induction left generalizing right with
  | node constructor arguments inductionHypothesis =>
    cases right with
    | node second compared =>
      by_cases opened : constructor ∈ kit
      · have member := opened_declaration presentation kit opened
        have length : (List.ofFn fun position => lower presentation (arguments position)).length =
            (presentation.declaration constructor).params.length := by
          rw [List.length_ofFn, presentation.arity_eq]
        have otherHead : HasOperationHead (presentation.language.terms.map GrammarRule.label)
            (lower presentation (.node second compared)) :=
          List.mem_map_of_mem (presentation.declared second)
        obtain ⟨rawArguments, shape, _⟩ := head_agreement bisimulation
          (settings constructor opened) member rfl related
          (lower_authored presentation (.node second compared)) otherHead rfl length
        have same := presentation.names_injective (Pattern.apply.inj shape).1
        subst second
        simp only [view, if_pos opened]
        congr 1
        funext position
        obtain ⟨sort, projectable⟩ := presentation.projectable constructor position
        have bounded : position.val < (presentation.declaration constructor).params.length := by
          rw [presentation.arity_eq]; exact position.isLt
        have getMember := getLabel_mem_adjoinedLabels presentation.language
          (openedNames presentation kit) member (position := (position.val, sort)) projectable
        obtain ⟨rightArguments, rightShape, rightLength, relatedArguments⟩ :=
          argument_agreement bisimulation (settings constructor opened) member rfl related
            (lower_authored presentation (.node constructor compared)) otherHead rfl length
            (position := (position.val, sort)) projectable bounded getMember
        have argumentsEq := (Pattern.apply.inj rightShape).2
        subst rightArguments
        apply inductionHypothesis position
        simpa only [List.getElem_ofFn] using relatedArguments
      · by_cases otherOpened : second ∈ kit
        · have member := opened_declaration presentation kit otherOpened
          have length : (List.ofFn fun position => lower presentation (compared position)).length =
              (presentation.declaration second).params.length := by
            rw [List.length_ofFn, presentation.arity_eq]
          have reversed : IsInstrumentBisimulation base presentation.language cut
              (openedNames presentation kit) (fun first other => relation other first) := {
            forward := bisimulation.backward
            backward := bisimulation.forward
            barbs := fun held label => (bisimulation.barbs held label).symm }
          obtain ⟨_, shape, _⟩ := head_agreement reversed (settings second otherOpened) member
            rfl related (lower_authored presentation (.node constructor arguments))
            (List.mem_map_of_mem (presentation.declared constructor)) rfl length
          have same := presentation.names_injective (Pattern.apply.inj shape).1
          exact False.elim (opened (same ▸ otherOpened))
        · simp only [view, if_neg opened, if_neg otherOpened]

theorem runtime_bisimulation_preserves_tests (presentation : Presentation Symbols arity)
    (kit : List Symbols) (cut : CollType) (base : BasePremiseEvaluator)
    (relation : Pattern → Pattern → Prop)
    (bisimulation : IsInstrumentBisimulation base presentation.language cut
      (openedNames presentation kit) relation)
    (settings : ∀ constructor, constructor ∈ kit →
      ObserverSetting base presentation.language cut (openedNames presentation kit)
        (presentation.declaration constructor).label)
    {left right : Tree Symbols arity}
    (related : relation (lower presentation left) (lower presentation right)) :
    LogicallyEquivalent (fun constructor => constructor ∈ kit) left right :=
  (logicallyEquivalent_iff_view kit left right).2
    (runtime_bisimulation_preserves_view presentation kit cut base relation bisimulation
      settings related)

theorem runtime_complete_reconstruction (presentation : Presentation Symbols arity)
    (kit : List Symbols) (complete : ∀ constructor, constructor ∈ kit)
    (cut : CollType) (base : BasePremiseEvaluator) (relation : Pattern → Pattern → Prop)
    (bisimulation : IsInstrumentBisimulation base presentation.language cut
      (openedNames presentation kit) relation)
    (settings : ∀ constructor, constructor ∈ kit →
      ObserverSetting base presentation.language cut (openedNames presentation kit)
        (presentation.declaration constructor).label)
    {left right : Tree Symbols arity}
    (related : relation (lower presentation left) (lower presentation right)) : left = right :=
  complete_view_injective _ complete
    (runtime_bisimulation_preserves_view presentation kit cut base relation bisimulation
      settings related)

end Mettapedia.OSLF.Framework.InstrumentRuntime
