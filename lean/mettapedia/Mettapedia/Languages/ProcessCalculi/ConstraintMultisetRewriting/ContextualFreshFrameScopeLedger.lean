import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation

/-!
# Scope ownership for actual solver-returned declaration frames

Original names retain their scopes under the computed frame inclusion.
Returned declarations occupy a newly reserved namespace, with their actual
identities and arities preserved. No enumeration of either declaration
family is needed: each observed term has finite support.

The actual endomorphic answer is covered by that extended ledger, including
images of earlier captures. This is scope ownership, independently of the
solver's consistency and factorization proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualScopeSupport
open ContextualFrameUpdate

variable {S : Signature} {V W Local : Type} {source : V → MetaArity S}

def frameScopes (oldScopes : V → Finset Nat) (helperScope : Nat) : V ⊕ (W ⊕ Empty) → Finset Nat
  | .inl identity => oldScopes identity
  | .inr (.inl _) => {helperScope}
  | .inr (.inr impossible) => nomatch impossible

def helperScope (occupied : Finset Nat) : Nat := ContextualActivationScopes.start occupied

def helperLedger (occupied : Finset Nat) : Finset Nat := insert (helperScope occupied) occupied

theorem helper_scope_fresh (occupied : Finset Nat) : helperScope occupied ∉ occupied := by
  intro member
  exact Nat.lt_irrefl _ (ContextualActivationScopes.occupied_lt_start occupied member)

theorem old_scopes_retained (occupied : Finset Nat) : occupied ⊆ helperLedger occupied :=
  Finset.subset_insert _ _

theorem helper_scope_retained (occupied : Finset Nat) : helperScope occupied ∈ helperLedger occupied :=
  Finset.mem_insert_self _ _

theorem includeSource_image {problem : ContextualResidual.Problem source} (update : Update problem) (identity : V) :
    ContextualComputedFreshFrame.includeSource update identity =
      generator (ContextualComputedFreshFrame.active source update.declaration) (.inl identity) := by
  unfold ContextualComputedFreshFrame.includeSource Assignment.compose ContextualComputedFreshFrame.sourceIntoOld
  rw [instantiate_generator]
  rfl

theorem includeReturned_image {problem : ContextualResidual.Problem source} (update : Update problem)
    (identity : update.Variables) :
    ContextualComputedFreshFrame.includeReturned update identity =
      generator (ContextualComputedFreshFrame.active source update.declaration) (.inr (.inl identity)) := by
  unfold ContextualComputedFreshFrame.includeReturned Assignment.compose ContextualComputedFreshFrame.returnedIntoTarget
  rw [instantiate_generator]
  rfl

theorem includeSource_respects {problem : ContextualResidual.Problem source} (update : Update problem)
    (scopes : V → Finset Nat) (allocated : Nat) :
    Respects scopes (frameScopes (W := update.Variables) scopes allocated)
      (ContextualComputedFreshFrame.includeSource update) := by
  intro identity
  unfold Covered
  rw [includeSource_image, term_generator (S := S)]
  exact Finset.Subset.refl _

theorem returned_term_covered {problem : ContextualResidual.Problem source} (update : Update problem)
    (scopes : V → Finset Nat) (allocated : Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S update.declaration) Γ sort) :
    Covered (frameScopes (W := update.Variables) scopes allocated) {allocated}
      (instantiate (ContextualComputedFreshFrame.includeReturned update) value) := by
  apply covered_instantiate _ _ _ value
  intro identity _
  unfold Covered
  rw [includeReturned_image, term_generator (S := S)]
  exact Finset.Subset.refl _

theorem answer_source_image {problem : ContextualResidual.Problem source} (update : Update problem)
    (identity : V) :
    ContextualComputedFreshFrame.answer update (.inl identity) =
      instantiate (ContextualComputedFreshFrame.includeReturned update) (update.answer identity) := by
  have equation := congrFun (ContextualComputedFreshFrame.answer_on_source update) identity
  rw [Assignment.compose, includeSource_image, instantiate_generator] at equation
  exact equation

theorem answer_image_covered {problem : ContextualResidual.Problem source} (update : Update problem)
    (scopes : V → Finset Nat) (allocated : Nat)
    (identity : V ⊕ (update.Variables ⊕ Empty)) :
    Covered (frameScopes scopes allocated) {allocated} (ContextualComputedFreshFrame.answer update identity) := by
  cases identity with
  | inl name =>
      rw [answer_source_image]
      exact returned_term_covered update scopes allocated (update.answer name)
  | inr other =>
      cases other with
      | inl name =>
          unfold Covered
          rw [ContextualComputedFreshFrame.helper_is_fixed, term_generator (S := S)]
          exact Finset.Subset.refl _
      | inr impossible => exact nomatch impossible

theorem answer_term_covered {problem : ContextualResidual.Problem source} (update : Update problem)
    (scopes : V → Finset Nat) (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S (ContextualComputedFreshFrame.active source update.declaration)) Γ sort) :
    Covered (frameScopes scopes (helperScope occupied)) (helperLedger occupied)
      (instantiate (ContextualComputedFreshFrame.answer update) value) := by
  apply covered_instantiate _ _ _ value
  intro identity _
  exact (answer_image_covered update scopes (helperScope occupied) identity).mono
    (Finset.singleton_subset_iff.mpr (helper_scope_retained occupied))

theorem inventory_includeSource_covered {O : Type} (locals : Local → MetaArity S)
    {problem : ContextualResidual.Problem source} (update : Update problem)
    (scopes : V → Finset Nat) {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    (inventory : ContextualWorldScopeLedger.Inventory locals source (O := O) Γ sort)
    (covered : ContextualWorldScopeLedger.CoveredWorld locals source scopes occupied inventory) :
    ContextualWorldScopeLedger.CoveredWorld locals (ContextualComputedFreshFrame.active source update.declaration)
      (frameScopes scopes (helperScope occupied)) (helperLedger occupied)
      (ContextualWorldScopeLedger.mapInventory locals source (ContextualComputedFreshFrame.includeSource update) inventory) := by
  exact (ContextualWorldScopeLedger.mapInventory_covered locals source scopes _ _
    (includeSource_respects update scopes (helperScope occupied)) inventory covered).mono _ _
    (old_scopes_retained occupied)

theorem computed_activation_inventory_covered {Shared : Type} {O : Type}
    [DecidableEq O] (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    (scopes : Shared → Finset Nat) (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (inventory : ContextualWorldScopeLedger.Inventory locals captures (O := O) Γ sort)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort)
    (covered : ContextualWorldScopeLedger.CoveredWorld locals captures scopes occupied inventory)
    (ruleCovered : ContextualWorldScopeLedger.RuleCovered (privateScopes scopes) occupied rule)
    (admitted : ContextualGuardedStep.Requirements locals captures occupied selection rule
      inventory.rows inventory.configuration outputs)
    (update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures occupied selection rule inventory.rows inventory.configuration))) :
    ContextualWorldScopeLedger.CoveredWorld locals
      (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals captures) update.declaration)
      (frameScopes (activeScopes scopes) (helperScope (ContextualActivationScopes.after occupied selection)))
      (helperLedger (ContextualActivationScopes.after occupied selection))
      (ContextualWorldScopeLedger.mapInventory locals (ContextualActivatedStep.target locals captures)
        (ContextualComputedFreshFrame.includeSource update)
        (ContextualWorldScopeLedger.afterInventory locals captures occupied selection rule inventory outputs)) := by
  exact inventory_includeSource_covered locals update _ _
    (ContextualWorldScopeLedger.afterInventory_covered locals captures scopes occupied selection rule inventory outputs
      covered ruleCovered admitted.occurrences admitted.outputs)

theorem later_reservation_cannot_reuse_helper {O : Type} (occupied : Finset Nat)
    (selection : Selection O) (port : ContextualActivationScopes.Port selection) :
    ContextualActivationScopes.scopeAt (helperLedger occupied) port ≠ helperScope occupied := by
  intro same
  exact ContextualActivationScopes.at_fresh (helperLedger occupied) port
    (same ▸ helper_scope_retained occupied)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger
