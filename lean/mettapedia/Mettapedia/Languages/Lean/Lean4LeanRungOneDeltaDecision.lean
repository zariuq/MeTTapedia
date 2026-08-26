import Mettapedia.Languages.Lean.Lean4LeanRungZeroDecision

/-!
# Executable finite-delta rung for the Lean GSLT family

Lean definition expressions already carry the delta request as a constant
name and a list of universe levels.  This rung supplies a finite definition
catalog, performs that lookup directly, validates the universe instantiation,
and combines delta with the previously verified beta/head evaluator.

Only the catalog's list is computationally inspected.  Its proof fields state
that the list contains exactly the environment's definitional equations; they
cannot select or alter runtime behavior.
-/

namespace Mettapedia.Languages.Lean.Lean4LeanRungOneDeltaDecision

open Lean4Lean
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.Languages.Lean.Lean4LeanDirectedReduction
open Mettapedia.Languages.Lean.Lean4LeanRungZeroDecision

/-! ## Finite definition catalogs -/

/-- First definition with the requested constant name. -/
def findDefinition : List VDefVal -> Name -> Option VDefVal
  | [], _ => none
  | definition :: rest, name =>
      if definition.name = name then some definition
      else findDefinition rest name

theorem findDefinition_sound
    {definitions : List VDefVal} {name : Name} {definition : VDefVal}
    (found : findDefinition definitions name = some definition) :
    definition ∈ definitions ∧ definition.name = name := by
  induction definitions with
  | nil => simp [findDefinition] at found
  | cons head tail inductionHypothesis =>
      simp only [findDefinition] at found
      split at found
      next nameEqual =>
        injection found with definitionEqual
        subst definition
        exact ⟨by simp, nameEqual⟩
      next nameDifferent =>
        obtain ⟨member, definitionName⟩ := inductionHypothesis found
        exact ⟨by simp [member], definitionName⟩

/-- A finite data catalog exactly presenting an environment's definitional
equations.  `lookupExact` is the executable-name uniqueness invariant. -/
structure DefinitionCatalog (environment : VEnv) where
  entries : List VDefVal
  lookupExact : forall definition, definition ∈ entries ->
    findDefinition entries definition.name = some definition
  sound : forall definition, definition ∈ entries ->
    environment.defeqs definition.toDefEq
  complete : forall equation, environment.defeqs equation ->
    exists definition, definition ∈ entries ∧ equation = definition.toDefEq

/-- Executable validation of one universe-level instantiation. -/
def levelsAccepted (universeParameters expectedCount : Nat)
    (levels : List VLevel) : Bool :=
  decide (levels.length = expectedCount) &&
    levels.all fun level => decide (level.WF universeParameters)

@[simp] theorem levelsAccepted_eq_true_iff
    (universeParameters expectedCount : Nat) (levels : List VLevel) :
    levelsAccepted universeParameters expectedCount levels = true <->
      levels.length = expectedCount ∧
        forall level, level ∈ levels -> level.WF universeParameters := by
  simp [levelsAccepted, List.all_eq_true]

/-- Executable occurrence receipt. -/
inductive CatalogHeadReceipt where
  | beta
  | delta (name : Name) (levels : List VLevel)
  | app (head : CatalogHeadReceipt)

/-! ## Catalog-presented operational events -/

/-- Beta, catalog delta, and recursive head-application occurrences, indexed
by their exact executable receipt.  The relation lives in `Prop`; the receipt
is the retained computational occurrence data. -/
inductive CatalogHeadEvent (definitions : List VDefVal)
    (universeParameters : Nat) :
    CatalogHeadReceipt -> VExpr -> VExpr -> Prop where
  | beta {domain body argument : VExpr} :
      CatalogHeadEvent definitions universeParameters .beta
        (.app (.lam domain body) argument)
        (body.inst argument)
  | delta {definition : VDefVal} {levels : List VLevel}
      (member : definition ∈ definitions)
      (levelsWellFormed : forall level, level ∈ levels ->
        level.WF universeParameters)
      (levelCount : levels.length = definition.uvars) :
      CatalogHeadEvent definitions universeParameters
        (.delta definition.name levels)
        (definition.toDefEq.lhs.instL levels)
        (definition.toDefEq.rhs.instL levels)
  | app {receipt : CatalogHeadReceipt}
      {function function' argument : VExpr}
      (head : CatalogHeadEvent definitions universeParameters receipt
        function function') :
      CatalogHeadEvent definitions universeParameters (.app receipt)
        (.app function argument)
        (.app function' argument)

/-- Catalog events erase propositionally to the existing raw Lean calculus
when the catalog is sound for the environment. -/
theorem catalogHeadEvent_to_coreRaw {environment : VEnv}
    (catalog : DefinitionCatalog environment)
    (universeParameters : Nat)
    {receipt : CatalogHeadReceipt} {source target : VExpr}
    (event : CatalogHeadEvent catalog.entries universeParameters
      receipt source target) :
    Nonempty (CoreRawHeadEvent environment universeParameters source target) := by
  induction event with
  | beta => exact ⟨.beta⟩
  | delta member levelsWellFormed levelCount =>
      exact ⟨.delta (catalog.sound _ member) levelsWellFormed levelCount⟩
  | app head inductionHypothesis =>
      rcases inductionHypothesis with ⟨rawHead⟩
      exact ⟨.app rawHead⟩

/-- Catalog completeness reflects every raw event back to a catalog event
with an explicit receipt. -/
theorem coreRawToCatalog {environment : VEnv}
    (catalog : DefinitionCatalog environment)
    (universeParameters : Nat)
    {source target : VExpr}
    (event : CoreRawHeadEvent environment universeParameters source target) :
    exists receipt, CatalogHeadEvent catalog.entries universeParameters
      receipt source target := by
  induction event with
  | beta => exact ⟨.beta, .beta⟩
  | @delta definition levels member levelsWellFormed levelCount =>
      obtain ⟨catalogDefinition, catalogMember, definitionEqual⟩ :=
        catalog.complete definition member
      subst definition
      exact ⟨.delta catalogDefinition.name levels,
        .delta catalogMember levelsWellFormed levelCount⟩
  | app head inductionHypothesis =>
      obtain ⟨receipt, catalogHead⟩ := inductionHypothesis
      exact ⟨.app receipt, .app catalogHead⟩

/-- Catalog events and the existing raw Lean events have exactly the same
one-step fibres. -/
theorem nonempty_catalogHeadEvent_iff_coreRawHeadEvent
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) (source target : VExpr) :
    (exists receipt, CatalogHeadEvent catalog.entries universeParameters
      receipt source target) <->
      Nonempty (CoreRawHeadEvent environment universeParameters source target) := by
  constructor
  · rintro ⟨receipt, event⟩
    exact catalogHeadEvent_to_coreRaw catalog universeParameters event
  · rintro ⟨event⟩
    exact coreRawToCatalog catalog universeParameters event

/-! ## Independent catalog-driven execution -/

/-- Compute one beta, delta, or recursive head step. -/
def catalogHeadStepWithReceipt? (definitions : List VDefVal)
    (universeParameters : Nat) : VExpr -> Option (VExpr × CatalogHeadReceipt)
  | .app (.lam _ body) argument =>
      some (body.inst argument, .beta)
  | .app function argument =>
      match catalogHeadStepWithReceipt? definitions universeParameters function with
      | some (target, receipt) => some (.app target argument, .app receipt)
      | none => none
  | .const name levels =>
      match findDefinition definitions name with
      | some definition =>
          if levelsAccepted universeParameters definition.uvars levels then
            some (definition.value.instL levels,
              .delta definition.name levels)
          else none
      | none => none
  | _ => none

/-- Every catalog event is computed with its exact receipt. -/
theorem catalogHeadStepWithReceipt_complete
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat)
    {receipt : CatalogHeadReceipt} {source target : VExpr}
    (event : CatalogHeadEvent catalog.entries universeParameters
      receipt source target) :
    catalogHeadStepWithReceipt? catalog.entries universeParameters source =
      some (target, receipt) := by
  induction event with
  | beta => rfl
  | @delta definition levels member levelsWellFormed levelCount =>
      have levelsAcceptedTrue :
          levelsAccepted universeParameters definition.uvars levels = true :=
        (levelsAccepted_eq_true_iff universeParameters definition.uvars levels).mpr
          ⟨levelCount, levelsWellFormed⟩
      simp [catalogHeadStepWithReceipt?, VDefVal.toDefEq, VExpr.instL,
        VLevel.inst_map_id levelCount, catalog.lookupExact definition member,
        levelsAcceptedTrue]
  | @app headReceipt function function' argument head inductionHypothesis =>
      cases head with
      | beta =>
          simp [catalogHeadStepWithReceipt?]
      | @delta definition levels member levelsWellFormed levelCount =>
          change
            (match catalogHeadStepWithReceipt? catalog.entries
                universeParameters (definition.toDefEq.lhs.instL levels) with
              | some (computedTarget, computedReceipt) =>
                  some (VExpr.app computedTarget argument,
                    CatalogHeadReceipt.app computedReceipt)
              | none => none) =
              some (VExpr.app (definition.toDefEq.rhs.instL levels) argument,
                CatalogHeadReceipt.app
                  (CatalogHeadReceipt.delta definition.name levels))
          rw [inductionHypothesis]
      | app nested =>
          change
            (match catalogHeadStepWithReceipt? catalog.entries
                universeParameters (.app _ _) with
              | some (computedTarget, computedReceipt) =>
                  some (VExpr.app computedTarget argument,
                    CatalogHeadReceipt.app computedReceipt)
              | none => none) = _
          rw [inductionHypothesis]

/-- Every computed target is justified by a catalog event. -/
theorem catalogHeadStepWithReceipt_sound
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat)
    {source target : VExpr} {receipt : CatalogHeadReceipt}
    (accepted :
      catalogHeadStepWithReceipt? catalog.entries universeParameters source =
        some (target, receipt)) :
    CatalogHeadEvent catalog.entries universeParameters receipt source target := by
  induction source generalizing target receipt with
  | bvar index => simp [catalogHeadStepWithReceipt?] at accepted
  | sort level => simp [catalogHeadStepWithReceipt?] at accepted
  | lam domain body domainInduction bodyInduction =>
      simp [catalogHeadStepWithReceipt?] at accepted
  | forallE domain body domainInduction bodyInduction =>
      simp [catalogHeadStepWithReceipt?] at accepted
  | const name levels =>
      simp only [catalogHeadStepWithReceipt?] at accepted
      cases found : findDefinition catalog.entries name with
      | none => simp [found] at accepted
      | some definition =>
          cases levelCheck :
              levelsAccepted universeParameters definition.uvars levels with
          | false => simp [found, levelCheck] at accepted
          | true =>
              simp only [found, levelCheck, if_true, Option.some.injEq,
                Prod.mk.injEq] at accepted
              rcases accepted with ⟨targetEqual, receiptEqual⟩
              subst target
              subst receipt
              obtain ⟨member, definitionName⟩ := findDefinition_sound found
              obtain ⟨levelCount, levelsWellFormed⟩ :=
                (levelsAccepted_eq_true_iff universeParameters
                  definition.uvars levels).mp levelCheck
              have event : CatalogHeadEvent catalog.entries universeParameters
                  (.delta definition.name levels)
                  (.const name levels) (definition.value.instL levels) := by
                simpa [VDefVal.toDefEq, VExpr.instL,
                  VLevel.inst_map_id levelCount, definitionName] using
                    (CatalogHeadEvent.delta member levelsWellFormed levelCount)
              exact event
  | app function argument functionInduction argumentInduction =>
      cases function with
      | bvar index => simp [catalogHeadStepWithReceipt?] at accepted
      | sort level => simp [catalogHeadStepWithReceipt?] at accepted
      | lam domain body =>
          simp only [catalogHeadStepWithReceipt?, Option.some.injEq,
            Prod.mk.injEq] at accepted
          rcases accepted with ⟨targetEqual, receiptEqual⟩
          subst target
          subst receipt
          exact .beta
      | forallE domain body =>
          simp [catalogHeadStepWithReceipt?] at accepted
      | const name levels =>
          change
            (match catalogHeadStepWithReceipt? catalog.entries
                universeParameters (.const name levels) with
              | some (computedTarget, computedReceipt) =>
                  some (VExpr.app computedTarget argument,
                    CatalogHeadReceipt.app computedReceipt)
              | none => none) = some (target, receipt) at accepted
          cases computed : catalogHeadStepWithReceipt? catalog.entries
              universeParameters (.const name levels) with
          | none => rw [computed] at accepted; contradiction
          | some result =>
              rcases result with ⟨targetFunction, headReceipt⟩
              have headEvent := functionInduction computed
              rw [computed] at accepted
              simp only [Option.some.injEq, Prod.mk.injEq] at accepted
              rcases accepted with ⟨targetEqual, receiptEqual⟩
              subst target
              subst receipt
              exact .app headEvent
      | app first second =>
          change
            (match catalogHeadStepWithReceipt? catalog.entries
                universeParameters (.app first second) with
              | some (computedTarget, computedReceipt) =>
                  some (VExpr.app computedTarget argument,
                    CatalogHeadReceipt.app computedReceipt)
              | none => none) = some (target, receipt) at accepted
          cases computed : catalogHeadStepWithReceipt? catalog.entries
              universeParameters (.app first second) with
          | none => rw [computed] at accepted; contradiction
          | some result =>
              rcases result with ⟨targetFunction, headReceipt⟩
              have headEvent := functionInduction computed
              rw [computed] at accepted
              simp only [Option.some.injEq, Prod.mk.injEq] at accepted
              rcases accepted with ⟨targetEqual, receiptEqual⟩
              subst target
              subst receipt
              exact .app headEvent

/-- Computation preserves the exact catalog occurrence receipt. -/
theorem catalogHeadStepWithReceipt_sound_exact
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat)
    {source target : VExpr} {receipt : CatalogHeadReceipt}
    (accepted :
      catalogHeadStepWithReceipt? catalog.entries universeParameters source =
        some (target, receipt)) :
    CatalogHeadEvent catalog.entries universeParameters receipt source target :=
  catalogHeadStepWithReceipt_sound catalog universeParameters accepted

/-- The computed pair is equivalent to the exact receipt-indexed event. -/
theorem catalogHeadStepWithReceipt_eq_some_iff
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) (source target : VExpr)
    (receipt : CatalogHeadReceipt) :
    catalogHeadStepWithReceipt? catalog.entries universeParameters source =
        some (target, receipt) <->
      CatalogHeadEvent catalog.entries universeParameters receipt source target := by
  constructor
  · exact catalogHeadStepWithReceipt_sound catalog universeParameters
  · exact catalogHeadStepWithReceipt_complete catalog universeParameters

/-- Finite enumeration of exact target/receipt occurrences.  Keeping this
separate from endpoint enumeration avoids silently erasing event identity. -/
def catalogHeadEvents (definitions : List VDefVal)
    (universeParameters : Nat) (source : VExpr) :
    List (VExpr × CatalogHeadReceipt) :=
  (catalogHeadStepWithReceipt? definitions universeParameters source).toList

theorem mem_catalogHeadEvents_iff
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) (source target : VExpr)
    (receipt : CatalogHeadReceipt) :
    (target, receipt) ∈
        catalogHeadEvents catalog.entries universeParameters source <->
      CatalogHeadEvent catalog.entries universeParameters receipt source target := by
  rw [← catalogHeadStepWithReceipt_eq_some_iff catalog universeParameters]
  simp [catalogHeadEvents]

/-- Extensional endpoint projection of the occurrence enumeration. -/
def catalogHeadSuccessors (definitions : List VDefVal)
    (universeParameters : Nat) (source : VExpr) : List VExpr :=
  (catalogHeadEvents definitions universeParameters source).map Prod.fst

theorem mem_catalogHeadSuccessors_iff
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) (source target : VExpr) :
    target ∈ catalogHeadSuccessors catalog.entries universeParameters source <->
      exists receipt, CatalogHeadEvent catalog.entries universeParameters
        receipt source target := by
  simp only [catalogHeadSuccessors, List.mem_map]
  constructor
  · rintro ⟨event, eventMember, targetEqual⟩
    rcases event with ⟨eventTarget, receipt⟩
    simp only at targetEqual
    subst target
    exact ⟨receipt,
      (mem_catalogHeadEvents_iff catalog universeParameters source
        eventTarget receipt).mp eventMember⟩
  · rintro ⟨receipt, event⟩
    exact ⟨(target, receipt),
      (mem_catalogHeadEvents_iff catalog universeParameters source
        target receipt).mpr event, rfl⟩

/-- Pairwise decision derived from the catalog-driven evaluator. -/
def catalogHeadDecideStep {environment : VEnv}
    (catalog : DefinitionCatalog environment) (universeParameters : Nat)
    (source target : VExpr) : Bool :=
  match catalogHeadStepWithReceipt? catalog.entries universeParameters source with
  | none => false
  | some (candidate, _) => vExprStructEq candidate target

theorem catalogHeadDecideStep_correct
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) (source target : VExpr) :
    catalogHeadDecideStep catalog universeParameters source target = true <->
      exists receipt, CatalogHeadEvent catalog.entries universeParameters
        receipt source target := by
  constructor
  · intro accepted
    unfold catalogHeadDecideStep at accepted
    cases computed : catalogHeadStepWithReceipt? catalog.entries
        universeParameters source with
    | none => simp [computed] at accepted
    | some result =>
        rcases result with ⟨candidate, receipt⟩
        simp only [computed] at accepted
        have candidateEqual : candidate = target :=
          (vExprStructEq_eq_true_iff candidate target).mp accepted
        subst target
        exact ⟨receipt,
          catalogHeadStepWithReceipt_sound catalog universeParameters computed⟩
  · rintro ⟨receipt, event⟩
    unfold catalogHeadDecideStep
    rw [catalogHeadStepWithReceipt_complete catalog universeParameters event]
    exact (vExprStructEq_eq_true_iff target target).mpr rfl

/-- Exact decision for the existing raw Lean core under a finite complete
definition catalog. -/
def coreRawStepDecisionOfCatalog
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) :
    EffectiveStructure.StepDecision
      (coreRawHeadGSLT environment universeParameters) where
  decideStep := catalogHeadDecideStep catalog universeParameters
  correct := by
    intro source target
    rw [catalogHeadDecideStep_correct]
    exact (nonempty_catalogHeadEvent_iff_coreRawHeadEvent catalog
      universeParameters source target)

/-- Exact finite endpoint enumeration for the existing raw Lean GSLT. -/
def coreRawSuccessorEnumerationOfCatalog
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) :
    EffectiveStructure.SuccessorEnumeration
      (coreRawHeadGSLT environment universeParameters) where
  successors := catalogHeadSuccessors catalog.entries universeParameters
  mem_iff := by
    intro source target
    change target ∈ catalogHeadSuccessors catalog.entries universeParameters
        source <->
      Nonempty (CoreRawHeadEvent environment universeParameters source target)
    exact (mem_catalogHeadSuccessors_iff catalog universeParameters
      source target).trans
        (nonempty_catalogHeadEvent_iff_coreRawHeadEvent catalog
          universeParameters source target)

/-- Catalog-driven execution accepts exactly the generated native target
type of the existing raw Lean GSLT. -/
theorem coreRawStepDecisionOfCatalog_accepts_iff_ntt
    {environment : VEnv} (catalog : DefinitionCatalog environment)
    (universeParameters : Nat) (source target : VExpr) :
    (coreRawStepDecisionOfCatalog catalog universeParameters).decideStep
        source target = true <->
      (gsltOSLF (coreRawHeadGSLT environment universeParameters)).satisfies
        source
        (exactCoreRawHeadTargetType environment universeParameters target).pred := by
  rw [(coreRawStepDecisionOfCatalog catalog universeParameters).correct,
    satisfies_exactCoreRawHeadTargetType_iff_event]
  rfl

/-! ## Controls -/

namespace Canary

private def definitionName : Name := `rungOnePolymorphic

private def definition : VDefVal where
  name := definitionName
  uvars := 1
  type := .sort (.succ (.param 0))
  value := .sort (.param 0)

private def environment : VEnv :=
  VEnv.empty.addDefEq definition.toDefEq

private def catalog : DefinitionCatalog environment where
  entries := [definition]
  lookupExact := by
    intro candidate member
    simp only [List.mem_singleton] at member
    subst candidate
    simp [findDefinition]
  sound := by
    intro candidate member
    simp only [List.mem_singleton] at member
    subst candidate
    exact Or.inl rfl
  complete := by
    intro equation member
    rcases member with equal | impossible
    · exact ⟨definition, by simp, equal⟩
    · exact impossible.elim

private def deltaSource : VExpr :=
  .const definitionName [.zero]

private def deltaTarget : VExpr :=
  .sort .zero

private def argument : VExpr :=
  .const `rungOneArgument []

private def headContextSource : VExpr :=
  .app deltaSource argument

private def headContextTarget : VExpr :=
  .app deltaTarget argument

theorem delta_computes_from_catalog :
    catalogHeadStepWithReceipt? catalog.entries 0 deltaSource =
      some (deltaTarget, .delta definitionName [.zero]) := by
  rfl

theorem delta_ntt_accepts :
    (gsltOSLF (coreRawHeadGSLT environment 0)).satisfies deltaSource
      (exactCoreRawHeadTargetType environment 0 deltaTarget).pred := by
  apply (coreRawStepDecisionOfCatalog_accepts_iff_ntt
    catalog 0 deltaSource deltaTarget).mp
  rfl

theorem delta_under_head_context_computes :
    catalogHeadStepWithReceipt? catalog.entries 0 headContextSource =
      some (headContextTarget,
        .app (.delta definitionName [.zero])) := by
  rfl

theorem bad_level_rejected :
    catalogHeadStepWithReceipt? catalog.entries 0
      (.const definitionName [.param 0]) = none := by
  rfl

theorem bad_level_ntt_rejected :
    ¬(gsltOSLF (coreRawHeadGSLT environment 0)).satisfies
      (.const definitionName [.param 0])
      (exactCoreRawHeadTargetType environment 0 deltaTarget).pred := by
  intro accepted
  have decided := (coreRawStepDecisionOfCatalog_accepts_iff_ntt
    catalog 0 (.const definitionName [.param 0]) deltaTarget).mpr accepted
  simp [coreRawStepDecisionOfCatalog, catalogHeadDecideStep,
    bad_level_rejected] at decided

theorem bad_arity_rejected :
    catalogHeadStepWithReceipt? catalog.entries 0
      (.const definitionName []) = none := by
  rfl

theorem bad_arity_ntt_rejected :
    ¬(gsltOSLF (coreRawHeadGSLT environment 0)).satisfies
      (.const definitionName [])
      (exactCoreRawHeadTargetType environment 0 deltaTarget).pred := by
  intro accepted
  have decided := (coreRawStepDecisionOfCatalog_accepts_iff_ntt
    catalog 0 (.const definitionName []) deltaTarget).mpr accepted
  simp [coreRawStepDecisionOfCatalog, catalogHeadDecideStep,
    bad_arity_rejected] at decided

theorem absent_definition_rejected :
    catalogHeadStepWithReceipt? catalog.entries 0
      (.const `notInCatalog [.zero]) = none := by
  rfl

theorem absent_definition_ntt_rejected :
    ¬(gsltOSLF (coreRawHeadGSLT environment 0)).satisfies
      (.const `notInCatalog [.zero])
      (exactCoreRawHeadTargetType environment 0 deltaTarget).pred := by
  intro accepted
  have decided := (coreRawStepDecisionOfCatalog_accepts_iff_ntt
    catalog 0 (.const `notInCatalog [.zero]) deltaTarget).mpr accepted
  simp [coreRawStepDecisionOfCatalog, catalogHeadDecideStep,
    absent_definition_rejected] at decided

theorem mutated_target_rejected :
    (coreRawStepDecisionOfCatalog catalog 0).decideStep deltaSource argument =
      false := by
  rfl

theorem mutated_target_ntt_rejected :
    ¬(gsltOSLF (coreRawHeadGSLT environment 0)).satisfies deltaSource
      (exactCoreRawHeadTargetType environment 0 argument).pred := by
  intro accepted
  have decided := (coreRawStepDecisionOfCatalog_accepts_iff_ntt
    catalog 0 deltaSource argument).mpr accepted
  simp [mutated_target_rejected] at decided

end Canary

section AxiomAudit

#print axioms findDefinition_sound
#print axioms levelsAccepted_eq_true_iff
#print axioms nonempty_catalogHeadEvent_iff_coreRawHeadEvent
#print axioms catalogHeadStepWithReceipt_complete
#print axioms catalogHeadStepWithReceipt_sound_exact
#print axioms catalogHeadStepWithReceipt_eq_some_iff
#print axioms mem_catalogHeadEvents_iff
#print axioms mem_catalogHeadSuccessors_iff
#print axioms catalogHeadDecideStep_correct
#print axioms coreRawSuccessorEnumerationOfCatalog
#print axioms coreRawStepDecisionOfCatalog_accepts_iff_ntt
#print axioms Canary.delta_ntt_accepts
#print axioms Canary.bad_level_rejected
#print axioms Canary.bad_level_ntt_rejected
#print axioms Canary.bad_arity_rejected
#print axioms Canary.bad_arity_ntt_rejected
#print axioms Canary.absent_definition_rejected
#print axioms Canary.absent_definition_ntt_rejected
#print axioms Canary.mutated_target_rejected
#print axioms Canary.mutated_target_ntt_rejected

end AxiomAudit

end Mettapedia.Languages.Lean.Lean4LeanRungOneDeltaDecision
