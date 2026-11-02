import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedCatalogShapes
import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedKernel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequestLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MatchingReceiptSelection

/-!
# Constructing protected physical MM0 executions from source steps

The witness store has explicit immutable locations. A canonical arrangement
of source values provides an inexhaustible occurrence supply; it is used only
to construct completeness witnesses, never to authorize client publication.
Each source receipt opens the actual natural catalog activation and is lifted
with the same physical take/read/output lists into the real authority system.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedCompleteness

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintCatalog
open MM0ConstraintInputNormalization
open MM0ConstraintTheoremApplication (falseHead trueHead boolean_heads_distinct)
open MM0LocatedActivation (Value locate)
open MM0LocatedCatalogShapes

abbrev Occurrence := MM0ConstraintReaches.Occurrence
abbrev payload : Occurrence → Tm := IndexedOccurrences.label
def location (occurrence : Occurrence) : Space := layout (payload occurrence)
def label (occurrence : Occurrence) : Value := (location occurrence, payload occurrence)

def system (theory : Theory) (target : Context) : MM0LocatedKernel.System theory target Unit Unit Bool Occurrence location where
  clientActivation := fun _ _ => none
  authority :=
    { process := fun actor => if actor then
        ⟨fun _ _ => true, (catalog theory).map Sum.inl⟩
      else ⟨fun space _ => space == .requests, []⟩
      kernel := true
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        cases actor with
        | true => exact False.elim (notKernel rfl)
        | false =>
            change (location occurrence == Space.requests) = false
            rw [show location occurrence = Space.judgments from protectedHere]
            rfl }
  kernelSchemas := rfl

theorem source_firing_lifts {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (before : Configuration Value Occurrence)
    (coherent : LocatedRequestLifting.Coherent before.equations)
    (background : (MM0LocatedActivation.action target).Consistent before.equations)
    {after : Multiset Tm}
    (stepped : (process theory target (catalog theory)).Step (labels payload before.present) after) :
    ∃ final : Configuration Value Occurrence, (system theory target).Step payload true before final ∧
      LocatedRequestLifting.Coherent final.equations ∧ labels payload final.present = after := by
  obtain ⟨installed, member, sourceStep⟩ := stepped
  obtain ⟨key, keyInstalled, sourceRule, sourceRuleKnown, rfl⟩ := (compileRules_member _ _ _ _).mp member
  obtain ⟨schema, compiled, origin⟩ := source_rule_has_schema theory target key sourceRuleKnown
  rw [← origin] at sourceStep
  obtain ⟨receipt, sourceValid, destination⟩ := RequestOccurrenceLifting.receipt_of_step ContextualPatterns.layer
    (schema.requestRecipe target key.name) payload before.present (IndexedOccurrences.supply before.present) sourceStep
  have checked : schema.dataCondition receipt.assignment = true :=
    sourceValid.checks_hold ⟨(schema.requestRecipe target key.name).request,
      fun assignment _ => schema.dataCondition assignment = true⟩
      (by simp [RequestActivation.Recipe.matchingRule, Schema.requestRecipe, GuardedMultisetRewriting.requestRule])
  let rawBefore := LocatedProjection.configuration before
  have rawBackground : (MM0ConstraintParameters.action target).Consistent rawBefore.equations :=
    LocatedProjection.consistent_projected _ background
  obtain ⟨raw, activated, _⟩ := RequestActivation.step_of_matching_receipt ContextualPatterns.layer rfl
    falseHead trueHead boolean_heads_distinct target.length (schema.requestRecipe target key.name)
    payload rawBefore receipt sourceValid rawBackground
  have rawValid := MatchingReceiptSelection.valid ContextualPatterns.layer rfl falseHead trueHead boolean_heads_distinct
    target.length (schema.requestRecipe target key.name) payload rawBefore receipt sourceValid rawBackground activated
  obtain ⟨arguments, count, columns⟩ := data_arguments theory target key compiled receipt.assignment checked
  have fullAssignment : receipt.assignment = expressionAssignment target arguments := by
    funext index
    by_cases inside : index < schema.arity
    · exact columns index inside
    · have absent : receipt.assignment index = none := sourceValid.binds index (by
        intro pattern member present
        exact inside (gathers_bounded wellFormed target key compiled pattern member index present))
      rw [absent]
      simp [expressionAssignment, List.getElem?_eq_none (by omega : arguments.length ≤ index)]
  have compatible : MM0ScopedCatalogActivation.compatibilityActivate theory target key arguments = some raw := by
    simp only [MM0ScopedCatalogActivation.compatibilityActivate, compiled, Option.bind_eq_bind, Option.bind_some]
    rw [if_pos count, ← fullAssignment]
    exact activated
  have natural := MM0ScopedCatalogActivation.valid_compatibility_has_natural_activation theory target formed
    key arguments compatible rawValid
  have routing := schema_routed theory target key compiled
  have takes : ∀ occurrence ∈ receipt.takes, location occurrence = Space.requests := by
    intro occurrence present
    have member : payload occurrence ∈ receipt.takes.map payload := List.mem_map.mpr ⟨occurrence, present, rfl⟩
    obtain ⟨pattern, patternPresent, matched⟩ := GuardedMultisetRewriting.mem_of_forall₂ sourceValid.takesMatch (payload occurrence) member
    have same : pattern = (schema.requestRecipe target key.name).request := by
      simpa [RequestActivation.Recipe.matchingRule, GuardedMultisetRewriting.requestRule] using patternPresent
    subst pattern
    exact request_routed target.length schema.arity key.name receipt.assignment (payload occurrence)
      ((ContextualPatterns.solves_iff _ _ _).mp matched)
  have reads : ∀ occurrence ∈ receipt.reads, location occurrence = Space.judgments := by
    intro occurrence present
    obtain ⟨pattern, member, matched⟩ := GuardedMultisetRewriting.mem_of_forall₂ sourceValid.readsMatch
      (payload occurrence) (List.mem_map.mpr ⟨occurrence, present, rfl⟩)
    exact routing.1 pattern member receipt.assignment (payload occurrence)
      ((ContextualPatterns.solves_iff _ _ _).mp matched)
  have makes : ∀ occurrence ∈ receipt.outputs, location occurrence = Space.judgments := by
    intro occurrence present
    have instances := (RequestResolution.instTemplate_iff ContextualPatterns.layer receipt.assignment
      [(schema.requestRecipe target key.name).conclusion] (receipt.outputs.map payload)).mp sourceValid.makes
    obtain ⟨pattern, member, instantiated⟩ := GuardedMultisetRewriting.mem_of_forall₂ instances
      (payload occurrence) (List.mem_map.mpr ⟨occurrence, present, rfl⟩)
    have same : pattern = schema.conclusion := by simpa [Schema.requestRecipe] using member
    subst pattern
    exact routing.2 receipt.assignment (payload occurrence) instantiated
  let picked := RequestActivation.physicalSelection receipt
  have locatedValid := LocatedRequestLifting.valid (MM0ConstraintParameters.action target) location payload
    Space.requests Space.judgments Space.requests Space.judgments
    (MM0LocatedActivation.equality_checks theory target formed key arguments natural)
    coherent takes reads makes rawValid
  refine ⟨picked.result label (locate raw) before, ?_, ?_, ?_⟩
  · refine ⟨.inl key, List.mem_map.mpr ⟨key, keyInstalled, rfl⟩, .inl arguments,
      locate raw, ?_, picked, locatedValid, ?_, rfl⟩
    · change (MM0ScopedCatalogActivation.activate theory target key arguments).map locate = _
      rw [natural]
      rfl
    · intro occurrence made
      rfl
  · exact LocatedRequestLifting.problem_coherent location payload .requests .judgments .requests .judgments
      raw picked before coherent takes reads
  · simpa only [Selection.result, picked, RequestActivation.physicalSelection, Selection.commit,
      GuardedMultisetRewriting.FiringReceipt.commit, fire] using destination

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedCompleteness
