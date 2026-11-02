import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardReindexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceRelabeling
import Mathlib.Logic.Equiv.Fintype

/-!
# Original computed contextual views align with the common event inventory

A permutation extends the finite injection of actual activation ports into
the common event-port inventory. Reindexing that permutation transports the
original rule and every selected row equation, while fixing all captures.
The same invertible change reflects the original all-future asks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewRelocation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {Local Shared O : Type} {n : Nat}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def names (permutation : Equiv.Perm Nat) : ScopedVar Local ⊕ Shared → ScopedVar Local ⊕ Shared
  | .inl name => .inl (ScopedVar.at (permutation name.scope) name.name)
  | .inr name => .inr name

theorem preserves (permutation : Equiv.Perm Nat) (name : ScopedVar Local ⊕ Shared) :
    ContextualSelectionViews.target locals captures (names permutation name) =
      ContextualSelectionViews.target locals captures name := by
  cases name <;> rfl

def assignment (permutation : Equiv.Perm Nat) :
    Assignment (ContextualSelectionViews.target locals captures) (ContextualSelectionViews.target locals captures) :=
  reindex (names permutation) (preserves locals captures permutation)

theorem names_left_inverse (permutation : Equiv.Perm Nat) :
    Function.LeftInverse (names (Local := Local) (Shared := Shared) permutation.symm) (names permutation) := by
  intro name
  cases name with
  | inl name =>
      change Sum.inl (ScopedVar.at (permutation.symm (permutation name.scope)) name.name) = .inl name
      rw [permutation.symm_apply_apply]
      rfl
  | inr name => rfl

theorem assignment_inverse (permutation : Equiv.Perm Nat) :
    Assignment.compose (assignment locals captures permutation.symm) (assignment locals captures permutation) =
      generator (ContextualSelectionViews.target locals captures) :=
  reindex_left_inverse _ _ _ _ (names_left_inverse permutation)

theorem freshening_composes (permutation : Equiv.Perm Nat) (scope : Nat) :
    Assignment.compose (assignment locals captures permutation) (ContextualFreshening.assignment locals captures scope) =
      ContextualFreshening.assignment locals captures (permutation scope) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (assignment locals captures permutation)
        (generator (ContextualSelectionViews.target locals captures) (.inl (ScopedVar.at scope name))) = _
      rw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate (assignment locals captures permutation)
        (generator (ContextualSelectionViews.target locals captures) (.inr name)) = _
      rw [instantiate_generator]
      rfl

theorem termAt_relocated (permutation : Equiv.Perm Nat) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :
    instantiate (assignment locals captures permutation) (ContextualFreshening.termAt locals captures scope value) =
      ContextualFreshening.termAt locals captures (permutation scope) value := by
  change instantiate (assignment locals captures permutation)
      (instantiate (ContextualFreshening.assignment locals captures scope) value) = _
  rw [← Assignment.instantiate_compose, freshening_composes]
  rfl

theorem capture_assignment_fixed (permutation : Equiv.Perm Nat) :
    Assignment.compose (assignment locals captures permutation) (ContextualSelectionViews.capturedTarget locals captures) =
      ContextualSelectionViews.capturedTarget locals captures := by
  funext name
  change instantiate (assignment locals captures permutation)
      (generator (ContextualSelectionViews.target locals captures) (.inr name)) = _
  rw [instantiate_generator]
  rfl

theorem guard_rows_fixed (permutation : Equiv.Perm Nat) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    (fun occurrence => (ContextualGuardedStep.guardRows locals captures rows occurrence).map locals
      (assignment locals captures permutation)) = ContextualGuardedStep.guardRows locals captures rows := by
  funext occurrence
  change ((rows occurrence).map locals (ContextualSelectionViews.capturedTarget locals captures)).map locals _ = _
  rw [ContextualStoredRows.Row.map_compose, capture_assignment_fixed]
  rfl

variable (selections : Fin n → Selection O)

theorem exists_alignment (localLedger globalLedger : Finset Nat) (event : Fin n) :
    ∃ permutation : Equiv.Perm Nat,
      ∀ port : ContextualActivationScopes.Port (selections event),
        permutation (ContextualActivationScopes.scopeAt localLedger port) =
          ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩ := by
  apply Equiv.Perm.exists_extending_pair
  · exact ContextualActivationScopes.at_injective localLedger _
  · intro first second same
    exact eq_of_heq (Sigma.mk.inj (ContextualEventViewScopes.scope_injective selections globalLedger same)).2

variable {selections}

theorem prepared_rule_relocated (localLedger globalLedger : Finset Nat) (event : Fin n)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port (selections event),
      permutation (ContextualActivationScopes.scopeAt localLedger port) =
        ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    ((ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).rule).map
        (instantiate (assignment locals captures permutation)) =
      (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule := by
  change (rule.map (ContextualFreshening.termAt locals captures
      (ContextualActivationScopes.scopeAt localLedger (ContextualActivationScopes.rulePort (selections event))))).map _ = _
  rw [OccurrenceRelabeling.rule_map_comp]
  apply congrArg (fun function => rule.map function)
  funext value
  exact (termAt_relocated locals captures permutation _ value).trans
    (congrArg (fun scope => ContextualFreshening.termAt locals captures scope value)
      (aligned (ContextualActivationScopes.rulePort (selections event))))

theorem prepared_take_relocated (localLedger globalLedger : Finset Nat) (event : Fin n)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port (selections event),
      permutation (ContextualActivationScopes.scopeAt localLedger port) =
        ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (port : Fin (selections event).taken.length) :
    instantiate (assignment locals captures permutation)
        ((ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).taken port) =
      (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).taken port := by
  exact (termAt_relocated locals captures permutation _ _).trans
    (congrArg (fun scope => ContextualFreshening.termAt locals captures scope
      (ContextualStoredRows.asTemplate locals captures (rows ((selections event).taken.get port))))
      (aligned (ContextualActivationScopes.takePort (selections event) port)))

theorem prepared_read_relocated (localLedger globalLedger : Finset Nat) (event : Fin n)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port (selections event),
      permutation (ContextualActivationScopes.scopeAt localLedger port) =
        ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (port : Fin (selections event).read.length) :
    instantiate (assignment locals captures permutation)
        ((ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).read port) =
      (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).read port := by
  exact (termAt_relocated locals captures permutation _ _).trans
    (congrArg (fun scope => ContextualFreshening.termAt locals captures scope
      (ContextualStoredRows.asTemplate locals captures (rows ((selections event).read.get port))))
      (aligned (ContextualActivationScopes.readPort (selections event) port)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewRelocation
