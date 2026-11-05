import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels

/-!
# Principal-solver count guards become actual data-region queries

A completed actual update supplies a model through which every source model
factors. Conditional matching persists under further assignment. A count
that holds in every model therefore forces the entire matching occurrence
set to equal the principal model's set. The native query observes actual
row labels; it does not validate a cached truth marker.

Completion of the equation solver alone does not establish a guard. The
resulting complete-region query is still required. Pending queues and
nonprincipal families are not covered by the completed-update premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalCountQueries

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalRealizations ContextualGuardMatching
open ContextualConditionalGuards ContextualPredicateQueryAdmission

variable {S : Signature} {Local V Next Later O : Type} (locals : Local → MetaArity S)
    {declaration : V → MetaArity S} {next : Next → MetaArity S} {later : Later → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

theorem matches_future (candidate : Assignment declaration next) (pattern : Term (signature S next) Γ sort)
    (row : Row locals declaration Γ sort) (change : Assignment next later)
    (matched : Matches locals declaration candidate pattern row) :
    Matches locals declaration (Assignment.compose change candidate) (instantiate change pattern) row := by
  obtain ⟨extension, realized⟩ := (ContextualConditionalRealizations.matches_iff locals declaration candidate pattern row).mp matched
  let extra := Extension.withLocals extension.complementDeclarations later
  have square : Assignment.compose (extension.liftModel change) extension.assignment =
      Assignment.compose extra.assignment change := extension.liftModel_square change
  have transported := realized.future locals declaration (extension.liftModel change)
  rw [Assignment.compose_associative candidate extension.assignment (extension.liftModel change),
    ← Assignment.instantiate_compose (extension.liftModel change) extension.assignment pattern, square] at transported
  erw [
    ← Assignment.compose_associative candidate change extra.assignment,
    Assignment.instantiate_compose extra.assignment change pattern] at transported
  exact (ContextualConditionalRealizations.matches_iff locals declaration _ _ row).mpr ⟨extra, transported⟩

theorem region_subset_future (candidate : Assignment declaration next) (change : Assignment next later)
    (rows : O → Row locals declaration Γ sort) (world : Finset O)
    (pattern : Term (signature S declaration) Γ sort) :
    region locals candidate rows world pattern ⊆ region locals (Assignment.compose change candidate) rows world pattern := by
  intro occurrence member
  obtain ⟨present, matched⟩ := (mem_region _ _ _ _ _ _).mp member
  apply (mem_region _ _ _ _ _ _).mpr
  refine ⟨present, ?_⟩
  rw [Assignment.instantiate_compose change candidate pattern]
  exact matches_future locals candidate (instantiate candidate pattern) (rows occurrence) change matched

noncomputable def table {problem : ContextualResidual.Problem declaration} (update : ContextualFrameUpdate.Update problem)
    (rows : O → Row locals declaration Γ sort) (world : Finset O) (pattern : Term (signature S declaration) Γ sort) : Finset O :=
  region locals update.answer rows world pattern

/-- The all-future query is essential: testing only the principal table's cardinality is insufficient. -/
theorem count_as_data_query_iff [DecidableEq O] {problem : ContextualResidual.Problem declaration}
    (update : ContextualFrameUpdate.Update problem) (finished : update.remaining = [])
    (rows : O → Row locals declaration Γ sort) (world : Finset O)
    (pattern : Term (signature S declaration) Γ sort) (number : Nat) :
    ContextualConditionalGuards.Ask locals problem rows world (.count pattern number) ↔
      (table locals update rows world pattern).card = number ∧
        AskData problem (matchingQuery locals pattern (table locals update rows world pattern))
          (fun occurrence => (occurrence, rows occurrence)) world := by
  constructor
  · intro counted
    have principal := counted update.Variables update.declaration update.answer (update.completed finished)
    change (table locals update rows world pattern).card = number at principal
    refine ⟨principal, ?_⟩
    intro Future future candidate model
    obtain ⟨residual, _conditions, images⟩ := update.factors future candidate model
    have same : candidate = Assignment.compose residual update.answer := funext images
    have subset : table locals update rows world pattern ⊆ region locals candidate rows world pattern := by
      rw [same]
      exact region_subset_future locals update.answer residual rows world pattern
    have cardinality := counted Future future candidate model
    change (region locals candidate rows world pattern).card = number at cardinality
    have equal : table locals update rows world pattern = region locals candidate rows world pattern :=
      Finset.eq_of_subset_of_card_le subset (by omega)
    exact (matching_holds_iff locals pattern _ rows world ⟨Future, future, candidate⟩).mpr equal.symm
  · rintro ⟨cardinality, queried⟩ Future future candidate model
    have equal := (matching_holds_iff locals pattern _ rows world ⟨Future, future, candidate⟩).mp
      (queried Future future candidate model)
    change (region locals candidate rows world pattern).card = number
    rw [equal]
    exact cardinality

section Native

variable [DecidableEq Local] [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {before : ContextualConditionalExecution.State locals O Γ sort}

/-- Uses the existing firing's actual update, information, conditional rows and entry world. -/
theorem native_count_admission_iff (firing : ContextualConditionalExecution.Firing locals before)
    (finished : firing.update.remaining = [])
    (pattern : Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort) (number : Nat) :
    ContextualConditionalGuards.Ask locals
        (ContextualConditionalExecution.information locals before.declarations before.occupied firing.selection firing.rule
          before.rows before.equations)
        (ContextualConditionalExecution.guardRows locals before.declarations before.rows) before.present (.count pattern number) ↔
      (table locals firing.update (ContextualConditionalExecution.guardRows locals before.declarations before.rows) before.present pattern).card = number ∧
        ∃ observed : WithQueries locals before, observed.firing = firing ∧
          observed.queries = [matchingQuery locals pattern
            (table locals firing.update (ContextualConditionalExecution.guardRows locals before.declarations before.rows) before.present pattern)] := by
  rw [count_as_data_query_iff locals firing.update finished, admit_data_query_iff locals firing]
  rfl

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalCountQueries
