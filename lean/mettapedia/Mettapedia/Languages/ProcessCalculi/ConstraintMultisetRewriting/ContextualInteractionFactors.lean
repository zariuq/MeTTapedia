import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupation

/-!
# Formation, resources and information at a computed contextual activation

Typed interfaces supply the sorts and binding contexts. Formation aligns
the rule ports and actual output labels; resources execute the independent
occupation operator with the source freshness discipline; information uses
the joint problem and original asks of these same prepared views.
The three obligations share the selection and activation and cannot be
chosen as unrelated coordinates. Authority and complete-root scope coverage
are additional formation obligations at the situated interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInteractionFactors

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualActivatedStep

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

structure Formation (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (outputs : O → Term (signature S (target locals captures)) Γ sort) : Prop where
  take_length : rule.take.length = selection.taken.length
  read_length : rule.read.length = selection.read.length
  outputs : selection.made.map outputs = (prepared locals captures occupied selection rule rows).rule.produce

def Resources [DecidableEq O] (selection : Selection O) (world : Finset O) : Prop :=
  (∃ afterWorld, ResourceOccupation.commit selection.taken selection.read selection.made world = some afterWorld) ∧
    Disjoint selection.made.toFinset selection.taken.toFinset

theorem resources_iff [DecidableEq O] {T : Type*} (label : O → T)
    (selection : Selection O) (world : Finset O) :
    Resources selection world ↔ selection.taken.Nodup ∧ selection.made.Nodup ∧
      Enabled label world selection.commit :=
  (ResourceOccupation.enabled_iff_nonzero_and_fresh label selection world).symm

def Information (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) : Prop :=
  ContextualInformation.Admitted locals (problem locals captures occupied selection rule rows before)
    (fun occurrence => (rows occurrence).map locals (ContextualSelectionViews.capturedTarget locals captures))
    before.present (prepared locals captures occupied selection rule rows).rule.checks

structure Admitted [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputs : O → Term (signature S (target locals captures)) Γ sort) : Prop where
  formation : Formation locals captures occupied selection rule rows outputs
  resources : Resources selection before.present
  information : Information locals captures occupied selection rule rows before

theorem Admitted.resource_result [DecidableEq O] {occupied : Finset Nat} {selection : Selection O}
    {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    (admitted : Admitted locals captures occupied selection rule rows before outputs) :
    ResourceOccupation.commit selection.taken selection.read selection.made before.present =
      some (result locals captures occupied selection rule rows before).present := by
  obtain ⟨taken, made, enabled⟩ := (resources_iff outputs selection before.present).mp admitted.resources
  exact ResourceOccupation.commit_eq_fire outputs selection before.present taken made enabled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInteractionFactors
