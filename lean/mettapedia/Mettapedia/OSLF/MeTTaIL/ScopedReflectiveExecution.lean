import Mettapedia.OSLF.MeTTaIL.ScopedRuleInstantiation
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveComparison
import Mettapedia.OSLF.MeTTaIL.ScopedMatchMonotonicity

/-!
# Source-selected reflective execution in an explicit context

The existing reflective profile selects the binder operation for the authored
rule. The shared scoped matcher retains contextual values and every match
occurrence. Literal and source-selected name comparison share the same
traversal, premise machine and binder operation. Canonical comparison changes
only repeated name-body acceptance; captured contexts and raw values remain
unchanged. Contextual interpretation of binder-opening premises is separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

open Syntax Reflection ReflectiveSubstitution RuleBinding ScopedRuleMatching

/-- Read binder activation from the source-selected reflective declaration. -/
def binderOperation (profile : ReflectionProfile) (rule : RewriteRule) :
    Pattern → Pattern → Pattern :=
  match substitutionPresentationForRule? profile rule with
  | none => Substitution.instantiateBVar
  | some declaration => ScopedRuleInstantiation.reflectiveOperation declaration

/-- Execute one authored rule without discarding its captured contexts. -/
def applyRuleAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (term : Pattern) : List Pattern :=
  ScopedRuleExecution.applyRuleWithAt (binderOperation profile rule)
    relEnv language ambient rule term

/-- Unselected rules retain ordinary binder elimination and exact answer lists. -/
theorem ordinary_of_unselected (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern)
    (unselected : substitutionPresentationForRule? profile rule = none) :
    applyRuleAt profile relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleAt relEnv language ambient rule term := by
  simp only [applyRuleAt, binderOperation, unselected]
  rfl

/-- A selected rule uses precisely that declaration's reflective operation. -/
theorem selected (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) (declaration : ReflectivePresentationDecl)
    (chosen : substitutionPresentationForRule? profile rule = some declaration) :
    applyRuleAt profile relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleWithAt
        (ScopedRuleInstantiation.reflectiveOperation declaration)
        relEnv language ambient rule term := by
  simp only [applyRuleAt, binderOperation, chosen]

/-- Output membership retains the actual matcher and ordered premise witnesses. -/
theorem mem_applyRuleAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term result : Pattern) :
    result ∈ applyRuleAt profile relEnv language ambient rule term ↔
      ∃ spec captured assignment,
        rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        captured ∈ matchRuleAt rule spec ambient term ∧
        assignment ∈ ScopedRuleExecution.completeAssignments
          relEnv language ambient rule spec captured ∧
        reductWith? (binderOperation profile rule) rule spec ambient assignment = some result :=
  ScopedRuleExecution.mem_applyRuleWithAt_iff _ _ _ _ _ _ _

/-- The authored declaration order and every matching occurrence are retained. -/
def rewriteStepAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (term : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule => applyRuleAt profile relEnv language ambient rule term

theorem mem_rewriteStepAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (term result : Pattern) :
    result ∈ rewriteStepAt profile relEnv language ambient term ↔
      ∃ rule ∈ language.rewrites,
        result ∈ applyRuleAt profile relEnv language ambient rule term :=
  List.mem_flatMap

/-- Use the authored matching presentation for name-valued captures, while
retaining the independently selected reflective binder operation. -/
def applyRuleCanonicalAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (term : Pattern) : List Pattern :=
  ScopedRuleExecution.applyRuleComparedWithAt
    (ScopedReflectiveComparison.bodyComparison profile rule)
    (binderOperation profile rule) relEnv language ambient rule term

/-- Canonical name comparison retains every literal firing in order,
including repeated identical results. -/
theorem literal_sublist_canonical (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) :
    (applyRuleAt profile relEnv language ambient rule term).Sublist
      (applyRuleCanonicalAt profile relEnv language ambient rule term) := by
  apply ScopedRuleMatching.applyRuleComparedWithAt_mono
  intro name left right accepted
  exact ScopedReflectiveComparison.bodyComparison_of_eq profile rule name
    (beq_iff_eq.mp accepted)

/-- Both source selections must be absent to recover ordinary execution:
matching and binder activation are independent declarations. -/
theorem canonical_ordinary_of_unselected (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern)
    (matchingUnselected : matchingPresentationForRule? profile rule = none)
    (substitutionUnselected : substitutionPresentationForRule? profile rule = none) :
    applyRuleCanonicalAt profile relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleAt relEnv language ambient rule term := by
  have comparison : ScopedReflectiveComparison.bodyComparison profile rule =
      literalBodyComparison := by
    funext name left right
    exact ScopedReflectiveComparison.bodyComparison_unselected profile rule
      matchingUnselected name left right
  simp only [applyRuleCanonicalAt, comparison, binderOperation, substitutionUnselected]
  rfl

/-- The result is witnessed by the actual contextual capture, ordered
premise completion and source-selected RHS instantiation. -/
theorem mem_applyRuleCanonicalAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term result : Pattern) :
    result ∈ applyRuleCanonicalAt profile relEnv language ambient rule term ↔
      ∃ spec captured assignment,
        rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        captured ∈ matchRuleWithAt
          (ScopedReflectiveComparison.bodyComparison profile rule) rule spec ambient term ∧
        assignment ∈ ScopedRuleExecution.completeAssignments
          relEnv language ambient rule spec captured ∧
        reductWith? (binderOperation profile rule) rule spec ambient assignment = some result :=
  ScopedRuleExecution.mem_applyRuleComparedWithAt_iff _ _ _ _ _ _ _ _

/-- Apply canonical name comparison in the authored declaration order. -/
def rewriteCanonicalStepAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (term : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule =>
    applyRuleCanonicalAt profile relEnv language ambient rule term

theorem mem_rewriteCanonicalStepAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (term result : Pattern) :
    result ∈ rewriteCanonicalStepAt profile relEnv language ambient term ↔
      ∃ rule ∈ language.rewrites,
        result ∈ applyRuleCanonicalAt profile relEnv language ambient rule term :=
  List.mem_flatMap

theorem literal_rewrite_sublist_canonical (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (term : Pattern) :
    (rewriteStepAt profile relEnv language ambient term).Sublist
      (rewriteCanonicalStepAt profile relEnv language ambient term) :=
  List.Sublist.flatMap_right language.rewrites fun rule _ =>
    literal_sublist_canonical profile relEnv language ambient rule term

end Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Reflection
open ReflectiveSubstitution
open ReflectiveInstantiation
open Substitution
open RuleBinding
open ScopedRuleMatching

theorem reflective_operation_free_within (footprint : List String)
    (declaration : ReflectivePresentationDecl) (replacement body : Pattern)
    (inserted : ∀ free ∈ replacement.freeFvarNames, free ∈ footprint)
    (original : ∀ free ∈ body.freeFvarNames, free ∈ footprint) :
    ∀ free ∈ (ScopedRuleInstantiation.reflectiveOperation declaration replacement body).freeFvarNames,
      free ∈ footprint := by
  apply reflective_instantiateDeclared_free_within footprint declaration 0 _ body _ original
  rw [normalize_replacement_free_names]
  exact inserted

theorem binder_operation_free_within (footprint : List String)
    (profile : ReflectionProfile) (rule : RewriteRule) (replacement body : Pattern)
    (inserted : ∀ free ∈ replacement.freeFvarNames, free ∈ footprint)
    (original : ∀ free ∈ body.freeFvarNames, free ∈ footprint) :
    ∀ free ∈ (ScopedReflectiveExecution.binderOperation profile rule replacement body).freeFvarNames,
      free ∈ footprint := by
  unfold ScopedReflectiveExecution.binderOperation
  cases substitutionPresentationForRule? profile rule with
  | none => exact instantiate_bvar_free_within footprint replacement body inserted original
  | some declaration => exact reflective_operation_free_within footprint declaration replacement body inserted original
theorem selected_reduct_free_within (footprint : List String)
    (profile : ReflectionProfile) (rule : RewriteRule) (spec : RuleBindingSpec)
    (admitted : admittedFor rule spec = true)
    (ambient : Nat) (assignment : ScopedRuleMatching.Assignment) (target : Pattern)
    (stored : assignmentFreeWithin footprint assignment)
    (success : reductWith? (ScopedReflectiveExecution.binderOperation profile rule)
      rule spec ambient assignment = some target) :
    ∀ name ∈ target.freeFvarNames, name ∈ footprint :=
  admitted_reduct_with_free_within footprint (ScopedReflectiveExecution.binderOperation profile rule)
    (binder_operation_free_within footprint profile rule) rule spec admitted ambient assignment target stored success

namespace FootprintControls

def declaration : ReflectivePresentationDecl :=
  { name := "footprint-reflection", processSort := "Proc", nameSort := "Name"
    quoteConstructor := "Quote", dropConstructor := "Drop", parallelCollection := .hashBag
    parallelUnitConstructor := "Zero", quoteDropEquation := "quote-drop",
    -- Closed: the footprint controls exercise the closed binder operation.
    quoteScope := .closed }

def bindings : RuleBindingSpec :=
  { dependencies := [("B", [.base "Name"]), ("P", []), ("R", [])]
    occurrences :=
      [{ name := "B", site := .left, path := [0, 0], arguments := [.bvar 0] }
       , { name := "B", site := .right, path := [0, 0], arguments := [.bvar 0] }] }

def rule (kind : CollType) : RewriteRule :=
  { name := "footprint-rule"
    typeContext := [("B", .base "Proc"), ("P", .base "Name"),
      ("R", .collection kind (.base "Proc"))]
    premises := []
    left := .apply "Triple" [.lambda "x" (.fvar "B"), .fvar "P", .collection kind [] (some "R")]
    right := .collection kind [.subst (.fvar "B") (.fvar "P")] (some "R")
    bindings := some bindings }

def profile : ReflectionProfile :=
  { presentations := [declaration]
    rules := [{ name := "footprint-selection"
                rewriteRule := "footprint-rule"
                matchingPresentation := declaration.name
                substitutionPresentation := declaration.name }] }

def assignment (kind : CollType) : ScopedRuleMatching.Assignment :=
  [("B", ⟨[.base "Name"], 0, .apply "Drop" [.bvar 0]⟩),
   ("P", ⟨[], 0, .apply "Quote" [.fvar "inserted"]⟩),
   ("R", ⟨[], 0, .collection kind [.fvar "residual-a", .fvar "residual-b"] none⟩)]

def footprint : List String := ["inserted", "residual-a", "residual-b"]

theorem nonzero_collection_admitted (kind : CollType) :
    admittedFor (rule kind) bindings = true := by
  cases kind <;> decide

theorem selected_collection_success (kind : CollType) :
    reductWith? (ScopedReflectiveExecution.binderOperation profile (rule kind))
      (rule kind) bindings 0 (assignment kind) =
      some (.collection kind [.fvar "inserted", .fvar "residual-a", .fvar "residual-b"] none) := by
  simp [reductWith?, instantiateWith?, instantiateArgsWith?, rule, bindings, assignment, lookup,
    arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, instantiateValue?,
    occurrenceAssignment, ContextSubstitution.substitute, ContextSubstitution.substituteList,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    ScopedReflectiveExecution.binderOperation, profile, declaration,
    substitutionPresentationForRule?, reflectiveRuleForRule?, presentationNamed?,
    ScopedRuleInstantiation.reflectiveOperation, ReflectiveInstantiation.instantiate,
    resolveQuotes, resolveQuotesList, finishResolveApply, substituteResolved, receive,
    normalizeReflectiveReplacement, normalizeReflective,
    Substitution.instantiateBVarAt,
    Substitution.liftBVars]

theorem ordinary_collection_success (kind : CollType) :
    reduct? (rule kind) bindings 0 (assignment kind) =
      some (.collection kind [.apply "Drop" [.apply "Quote" [.fvar "inserted"]],
        .fvar "residual-a", .fvar "residual-b"] none) := by
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, rule, bindings, assignment, lookup,
    arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, instantiateValue?,
    occurrenceAssignment, ContextSubstitution.substitute, ContextSubstitution.substituteList,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Substitution.instantiateBVar, Substitution.instantiateBVarAt, Substitution.liftBVars]

theorem selected_collection_earned_coverage (kind : CollType) :
    ∀ name ∈ (Pattern.collection kind
      [.fvar "inserted", .fvar "residual-a", .fvar "residual-b"] none).freeFvarNames,
      name ∈ footprint := by
  apply selected_reduct_free_within footprint profile (rule kind) bindings
    (nonzero_collection_admitted kind) 0 (assignment kind) _ _ (selected_collection_success kind)
  simp [assignmentFreeWithin, assignment, footprint, Pattern.freeFvarNames]

theorem residual_order_retained (kind : CollType) :
    (Pattern.collection kind [.fvar "inserted", .fvar "residual-a", .fvar "residual-b"] none).freeFvarNames =
      footprint := by
  simp [Pattern.freeFvarNames, footprint]

theorem literal_drop_quote_remains :
    ScopedRuleInstantiation.reflectiveOperation declaration (.fvar "unused")
      (.apply "Drop" [.apply "Quote" [.fvar "literal"]]) =
      .apply "Drop" [.apply "Quote" [.fvar "literal"]] := by
  decide

/-- Quoted code that mentions the eliminated binder is not admitted by the
closed scope, so the binder operation is never asked to look inside it. -/
theorem quoted_binder_not_admitted :
    ¬ QuotesClosed declaration (.apply "Quote" [.apply "F" [.bvar 0, .fvar "literal"]]) := by
  decide

/-- Admitted quoted code keeps its free names while the binder outside it is
replaced. -/
theorem opaque_quote_keeps_name :
    ScopedRuleInstantiation.reflectiveOperation declaration (.fvar "inserted")
      (.apply "Pair" [.bvar 0, .apply "Quote" [.apply "F" [.fvar "literal"]]]) =
      .apply "Pair" [.fvar "inserted", .apply "Quote" [.apply "F" [.fvar "literal"]]] := by
  decide +kernel

theorem static_quote_drop_keeps_names :
    (normalizeReflective declaration
      (.apply "Quote" [.apply "Drop" [.collection .hashSet [.fvar "literal"] (some "rest")]])).freeFvarNames =
      ["literal", "rest"] := by
  rw [normalize_reflective_free_names]
  simp [Pattern.freeFvarNames]

def openArgumentBindings : RuleBindingSpec :=
  { dependencies := [("T", [.base "Proc"])]
    occurrences :=
      [{ name := "T", site := .left, path := [0], arguments := [.fvar "argument"] },
       { name := "T", site := .right, path := [0], arguments := [.fvar "argument"] }] }

def openArgumentRule : RewriteRule :=
  { name := "open-argument-rule", typeContext := [("T", .base "Proc")], premises := []
    left := .lambda "x" (.fvar "T"), right := .lambda "x" (.fvar "T")
    bindings := some openArgumentBindings }

def closedStoredAssignment : ScopedRuleMatching.Assignment :=
  [("T", ⟨[.base "Proc"], 0, .bvar 0⟩)]

theorem unadmitted_argument_can_add_name :
    admittedFor openArgumentRule openArgumentBindings = false ∧
    assignmentFreeWithin [] closedStoredAssignment ∧
    reduct? openArgumentRule openArgumentBindings 0 closedStoredAssignment =
      some (.lambda "x" (.fvar "argument")) ∧
    ¬ (∀ name ∈ (Pattern.lambda "x" (.fvar "argument")).freeFvarNames, name ∈ ([] : List String)) := by
  constructor
  · decide
  constructor
  · simp [assignmentFreeWithin, closedStoredAssignment, Pattern.freeFvarNames]
  constructor
  · simp [reduct?, instantiateAt?, instantiateWith?, openArgumentRule, openArgumentBindings,
      closedStoredAssignment, lookup, arguments?, dependencies?, occurrenceDeclared, sitePattern?,
      occurrenceAt?, instantiateValue?, occurrenceAssignment, ContextSubstitution.substitute,
      Pattern.isWellScopedAt]
  · simp [Pattern.freeFvarNames]

theorem actual_occurrence_argument_coverage :
    ∀ name ∈ (Pattern.lambda "x" (.fvar "argument")).freeFvarNames,
      name ∈ ["argument"] := by
  apply instantiate_with_free_within ["argument"] Substitution.instantiateBVar
    (instantiate_bvar_free_within ["argument"]) openArgumentRule openArgumentBindings 0 .right [] 0
    closedStoredAssignment openArgumentRule.right _ _ _
    (by simpa only [reduct?, instantiateAt?] using unadmitted_argument_can_add_name.2.2.1)
  · simp [assignmentFreeWithin, closedStoredAssignment, Pattern.freeFvarNames]
  · intro name site path arguments selected
    unfold arguments? at selected
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨dependencies, _found, guardValue, _declared, selected⟩
    split at selected
    · split at selected <;> cases selected
      intro pattern member
      cases member
    · rename_i row rows
      split at selected <;> cases selected
      have selectedRow : row ∈ openArgumentBindings.occurrences.filter
          (fun candidate => candidate.name == name && candidate.site == site && candidate.path == path) := by
        rw [rows]
        simp
      have member : row ∈ openArgumentBindings.occurrences := (List.mem_filter.mp selectedRow).1
      simp only [openArgumentBindings, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [patternsFreeWithin, Pattern.freeFvarNames]
    · cases selected

theorem missing_inserted_name_is_not_covered (kind : CollType) :
    ¬ (∀ name ∈ (Pattern.collection kind
      [.fvar "inserted", .fvar "residual-a", .fvar "residual-b"] none).freeFvarNames,
      name ∈ ["residual-a", "residual-b"]) := by
  simp [Pattern.freeFvarNames]

end FootprintControls

#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.reflective_operation_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.binder_operation_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.selected_reduct_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.declaration
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.bindings
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.rule
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.profile
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.assignment
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.footprint
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.nonzero_collection_admitted
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.selected_collection_success
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.ordinary_collection_success
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.selected_collection_earned_coverage
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.residual_order_retained
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.literal_drop_quote_remains
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.quoted_binder_not_admitted
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.opaque_quote_keeps_name
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.static_quote_drop_keeps_names
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.openArgumentBindings
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.openArgumentRule
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.closedStoredAssignment
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.unadmitted_argument_can_add_name
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.actual_occurrence_argument_coverage
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.FootprintControls.missing_inserted_name_is_not_covered

end Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution
