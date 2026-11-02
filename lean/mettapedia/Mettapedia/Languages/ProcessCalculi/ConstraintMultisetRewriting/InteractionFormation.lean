import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution

/-!
# Full handle formation on the same two-sided located CMR firing

The existing interaction facets authorize receive, peek, observe and send.
Occurrence take/read/output formation reuses FormedUnder. Region checks also
require observe at their rigid location, even when the observed region is
empty. Equality checks are data equations and perform no store observation.

SchemaStep retains the same actual source activation and physical selection
as SchemaPublicationAuthority. Its execution remains the ordinary two-sided
CMR step; no one-sided rewriting execution is substituted for it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormation

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uN uO uI uR uX
variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO}
    {I : Type uI} {R : Type uR} {X : Type uX} [DecidableEq O]

def ObservationFormed (rights : Rights N) : Check (N × T) → Prop
  | .equal _ _ => True
  | .absent pattern => rights pattern.1 .observe = true
  | .count pattern _ => rights pattern.1 .observe = true

structure Formed (rights : Rights N) (label : O → N × T) (picked : Selection O) (rule : RuleInstance (N × T)) : Prop where
  physical : FormedUnder label Prod.fst rights picked.commit
  observations : ∀ check ∈ rule.checks, ObservationFormed rights check

theorem Formed.publication {rights : Rights N} {label : O → N × T} {picked : Selection O} {rule : RuleInstance (N × T)}
    (formed : Formed rights label picked rule) : PublicationAuthority.Formed rights (fun occurrence => (label occurrence).1) picked := by
  intro occurrence made
  exact formed.physical.made occurrence (by simpa [Selection.commit] using made)

def SchemaStep {location : O → N} {protectedOccurrence : O → Prop}
    (system : SchemaPublicationAuthority.System R N I O location protectedOccurrence)
    (activate : R → X → Option (RuleInstance (N × T))) (action : SubstitutionAction T S)
    (payload : O → T) (actor : I) (before after : Configuration (N × T) O) : Prop :=
  ∃ schema ∈ (system.process actor).schemas, ∃ inputs rule, activate schema inputs = some rule ∧
    ∃ picked : Selection O,
      picked.Valid (LocatedSubstitution.action action) (fun occurrence => (location occurrence, payload occurrence)) rule before ∧
      Formed (system.process actor).rights (fun occurrence => (location occurrence, payload occurrence)) picked rule ∧
      after = picked.result (fun occurrence => (location occurrence, payload occurrence)) rule before

theorem schemaStep_is_publication_step {location : O → N} {protectedOccurrence : O → Prop}
    {system : SchemaPublicationAuthority.System R N I O location protectedOccurrence}
    {activate : R → X → Option (RuleInstance (N × T))} {action : SubstitutionAction T S}
    {payload : O → T} {actor : I} {before after : Configuration (N × T) O}
    (stepped : SchemaStep system activate action payload actor before after) :
    system.Step activate (LocatedSubstitution.action action) (fun occurrence => (location occurrence, payload occurrence)) actor before after := by
  obtain ⟨schema, installed, inputs, rule, computed, picked, valid, formed, destination⟩ := stepped
  exact ⟨schema, installed, inputs, rule, computed, picked, valid, formed.publication, destination⟩

theorem schemaStep_is_ordinary {location : O → N} {protectedOccurrence : O → Prop}
    {system : SchemaPublicationAuthority.System R N I O location protectedOccurrence}
    {activate : R → X → Option (RuleInstance (N × T))} {action : SubstitutionAction T S}
    {payload : O → T} {actor : I} {before after : Configuration (N × T) O}
    (stepped : SchemaStep system activate action payload actor before after) :
    ∃ schema ∈ (system.process actor).schemas, ∃ inputs rule, activate schema inputs = some rule ∧
      ConstraintMultisetRewriting.Step (LocatedSubstitution.action action)
        (fun occurrence => (location occurrence, payload occurrence)) rule before after :=
  SchemaPublicationAuthority.Process.step_is_ordinary (schemaStep_is_publication_step stepped)

theorem no_receive_retains_occurrence {location : O → N} {protectedOccurrence : O → Prop}
    {system : SchemaPublicationAuthority.System R N I O location protectedOccurrence}
    {activate : R → X → Option (RuleInstance (N × T))} {action : SubstitutionAction T S}
    {payload : O → T} {actor : I} {before after : Configuration (N × T) O}
    (stepped : SchemaStep system activate action payload actor before after)
    (occurrence : O) (present : occurrence ∈ before.present)
    (denied : (system.process actor).rights (location occurrence) .receive = false) : occurrence ∈ after.present := by
  obtain ⟨schema, installed, inputs, rule, computed, picked, valid, formed, rfl⟩ := stepped
  apply mem_fire.mpr
  left
  refine ⟨present, ?_⟩
  intro taken
  have allowed := formed.physical.taken occurrence taken
  rw [denied] at allowed
  cases allowed

theorem no_peek_forbids_selected_read {rights : Rights N} {label : O → N × T} {picked : Selection O}
    {rule : RuleInstance (N × T)} (formed : Formed rights label picked rule)
    (occurrence : O) (selected : occurrence ∈ picked.read) (denied : rights (label occurrence).1 .peek = false) : False := by
  have allowed := formed.physical.kept occurrence (by simpa [Selection.commit] using selected)
  rw [denied] at allowed
  cases allowed

theorem no_observe_forbids_absence {rights : Rights N} {label : O → N × T} {picked : Selection O}
    {rule : RuleInstance (N × T)} (formed : Formed rights label picked rule)
    (pattern : N × T) (selected : Check.absent pattern ∈ rule.checks) (denied : rights pattern.1 .observe = false) : False := by
  have allowed := formed.observations (.absent pattern) selected
  change rights pattern.1 .observe = true at allowed
  rw [denied] at allowed
  cases allowed

theorem no_observe_forbids_count {rights : Rights N} {label : O → N × T} {picked : Selection O}
    {rule : RuleInstance (N × T)} (formed : Formed rights label picked rule)
    (pattern : N × T) (number : Nat) (selected : Check.count pattern number ∈ rule.checks)
    (denied : rights pattern.1 .observe = false) : False := by
  have allowed := formed.observations (.count pattern number) selected
  change rights pattern.1 .observe = true at allowed
  rw [denied] at allowed
  cases allowed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormation
