import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedActivation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DataRequestFootprint

/-!
# Located MM0 outputs are justified by actual selected protected premises

The proof uses the computed source key and natural activation. The ordinary
located selection projects with its complete payload equations. Its data-only
source receipt restricts to the actual take/read footprint, so unrelated
proof-shaped client data supplies no logical premise.

Request consumption contributes no proof authority. The independent MM0
judgments validate every fresh output from the actual selected premise
validity. This is a primitive-schema soundness result, not derived promotion.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedSoundness

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
open MM0ConstraintTheoremApplication (falseHead trueHead boolean_heads_distinct)
open MM0LocatedActivation (Value locate)

variable {O : Type*} [DecidableEq O]

theorem output_valid {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm)
    (key : RuleKey) (arguments : List Preterm) {raw : RuleInstance Tm}
    (computed : MM0ScopedCatalogActivation.activate theory target key arguments = some raw)
    (location : O → Space) (payload : O → Tm) {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid (MM0LocatedActivation.action target)
      (fun occurrence => (location occurrence, payload occurrence)) (locate raw) before)
    (assignment : ABTProtectedParameters.Assignment Head target.length)
    (solved : (MM0LocatedActivation.action target).Models assignment
      (picked.problem (fun occurrence => (location occurrence, payload occurrence)) (locate raw) before))
    (premisesValid : ∀ occurrence ∈ picked.read,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses
        ((MM0ConstraintParameters.action target).apply assignment (payload occurrence))) :
    ∀ occurrence ∈ picked.made,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses
        ((MM0ConstraintParameters.action target).apply assignment (payload occurrence)) := by
  obtain ⟨schema, compiled, _, sourceActivation⟩ := MM0LocatedActivation.source_origin theory target formed key arguments computed
  have rawValid := LocatedRequest.project_valid (MM0ConstraintParameters.action target)
    (fun occurrence => (location occurrence, payload occurrence)) .requests .judgments .requests .judgments
    (MM0LocatedActivation.equality_checks theory target formed key arguments computed) qualified
  have rawModels := LocatedRequest.project_models (MM0ConstraintParameters.action target)
    (fun occurrence => (location occurrence, payload occurrence)) .requests .judgments .requests .judgments
    qualified assignment solved
  let inputs := RequestActivation.boundedAssignment schema.arity (arguments.map (encode target))
  let source := schema.requestRecipe target key.name
  let resolved := fun occurrence => (MM0ConstraintParameters.action target).apply assignment (payload occurrence)
  let receipt := RequestResolution.resolvedReceipt ContextualPatterns.layer source inputs target.length assignment payload before.present picked
  have sourceValid : receipt.ValidAt ContextualPatterns.layer source.matchingRule resolved before.present :=
    RequestResolution.receipt_of_valid ContextualPatterns.layer rfl falseHead trueHead boolean_heads_distinct target.length
      source inputs sourceActivation (bounded_arguments_bind_only_the_request target key.name schema _)
      (templates_fixed theory target key compiled inputs) rawValid assignment rawModels
  have incoming : ∀ value ∈ labels resolved (DataRequestFootprint.gathers receipt),
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
    intro value member
    obtain ⟨occurrence, gathered, rfl⟩ := Multiset.mem_map.mp member
    have selected : occurrence ∈ receipt.takes.toFinset ∪ receipt.reads.toFinset := by
      simpa only [DataRequestFootprint.gathers, Finset.mem_val] using gathered
    rcases Finset.mem_union.mp selected with taken | read
    · have valuePresent : resolved occurrence ∈ receipt.takes.map resolved :=
        List.mem_map.mpr ⟨occurrence, by simpa using taken, rfl⟩
      obtain ⟨pattern, present, matched⟩ := GuardedMultisetRewriting.mem_of_forall₂ sourceValid.takesMatch
        (resolved occurrence) valuePresent
      have same : pattern = source.request := by
        simpa [RequestActivation.Recipe.matchingRule, GuardedMultisetRewriting.requestRule] using present
      subst pattern
      exact MM0LocatedActivation.request_instance_stays_data _ _ _ _ _ inputs target.length schema.arity key.name
        (resolved occurrence) ((ContextualPatterns.solves_iff _ _ _).mp matched)
    · exact premisesValid occurrence (by simpa only [receipt, RequestResolution.resolvedReceipt, List.mem_toFinset] using read)
  have afterValid := ruleFor_preserves wellFormed formed hypotheses key
    (compiled_schema_origin theory target key compiled) incoming (DataRequestFootprint.selected_step sourceValid)
  intro occurrence made
  apply afterValid (resolved occurrence)
  exact Multiset.mem_map.mpr ⟨occurrence,
    Finset.mem_val.mpr (DataRequestFootprint.made_in_selected_destination
      (layer := ContextualPatterns.layer) (recipe := source) (label := resolved) (receipt := receipt) made), rfl⟩

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedSoundness
