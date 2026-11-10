import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceRelabeling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleTraversal
import Mettapedia.OSLF.Syntax.ContextualFamilyABTInstantiation

/-! # Physical preparation of fresh stored-schema views

Each rule and selected row use goes through the common contextual ABT
interpreter. The existing scope reservation determines private identities;
captures retain their shared identities. The computed views agree with the
actual contextual occurrence preparation, including every rule position.
Permission and execution policy are separate from this preparation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualABTPreparation

open Mettapedia.OSLF
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

abbrev Physical := CommonABT.Physical (ContextualSelectionViews.target locals captures)

def openTermAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :
    Option (Physical locals captures) :=
  CommonABT.instantiate (ContextualFreshening.assignment locals captures scope) term

theorem openTerm_exact (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :
    openTermAt locals captures scope term =
      some (Binding.CommonABT.lower (ContextualFreshening.termAt locals captures scope term)) :=
  CommonABT.instantiate_exact _ term

def openRuleAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort)) :
    Option (RuleInstance (Physical locals captures)) :=
  rule.traverse? (openTermAt locals captures scope)

theorem openRule_exact (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort)) :
    openRuleAt locals captures scope rule =
      some ((ContextualFreshening.ruleAt locals captures scope rule).map Binding.CommonABT.lower) := by
  rw [openRuleAt, RuleInstance.traverse?_eq_map _ _ (openTerm_exact locals captures scope)]
  rw [ContextualFreshening.ruleAt, OccurrenceRelabeling.rule_map_comp]
  rfl

def openRowAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) : Option (Physical locals captures) :=
  openTermAt locals captures scope (ContextualStoredRows.asTemplate locals captures row)

theorem openRow_exact (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    openRowAt locals captures scope row =
      some (Binding.CommonABT.lower (ContextualStoredRows.viewAt locals captures scope row)) := by
  rw [openRowAt, openTerm_exact, ContextualStoredRows.viewAt_eq_freshening]

def readAt (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (port : Fin selection.read.length) :
    Option (Physical locals captures) :=
  openRowAt locals captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))
    (rows (selection.read.get port))

def takeAt (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (port : Fin selection.taken.length) :
    Option (Physical locals captures) :=
  openRowAt locals captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))
    (rows (selection.taken.get port))

theorem read_exact (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (port : Fin selection.read.length) :
    readAt locals captures occupied selection rows port =
      some (Binding.CommonABT.lower
        ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).read port)) := by
  rw [readAt, openRow_exact, ContextualActivatedStep.prepared_read_view]

theorem take_exact (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (port : Fin selection.taken.length) :
    takeAt locals captures occupied selection rows port =
      some (Binding.CommonABT.lower
        ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).taken port)) := by
  rw [takeAt, openRow_exact, ContextualActivatedStep.prepared_taken_view]

theorem shared_row_unchanged_between_uses (first second : Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) :
    openRowAt locals captures first (.shared value) = openRowAt locals captures second (.shared value) := by
  rw [openRow_exact, openRow_exact]
  rfl

theorem openTerm_injective (scope : Nat) {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (openTermAt locals captures scope (Γ := Γ) (sort := sort)) := by
  intro first second same
  rw [openTerm_exact, openTerm_exact] at same
  apply ContextualFreshening.termAt_injective locals captures scope
  exact Binding.CommonABT.lower_injective _ _ (Option.some.inj same)

/-- Equal physical views cannot hide an accidental identification of private
locals from two distinct activations. Shared captures are still allowed. -/
theorem private_local_separates_uses {firstScope secondScope : Nat}
    (different : firstScope ≠ secondScope) {Γ : Ctx S} {sort : S.Srt}
    (first second : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort)
    (localName : Local) (occurs : Sum.inl localName ∈ support first) :
    openTermAt locals captures firstScope first ≠ openTermAt locals captures secondScope second := by
  intro same
  rw [openTerm_exact, openTerm_exact] at same
  have sameTerms := Binding.CommonABT.lower_injective _ _ (Option.some.inj same)
  have inFirst : Sum.inl (ScopedVar.at firstScope localName) ∈
      support (ContextualFreshening.termAt locals captures firstScope first) := by
    rw [ContextualFreshening.support_termAt]
    exact List.mem_map.mpr ⟨Sum.inl localName, occurs, rfl⟩
  have inSecond : Sum.inl (ScopedVar.at firstScope localName) ∈
      support (ContextualFreshening.termAt locals captures secondScope second) := sameTerms ▸ inFirst
  obtain ⟨sharedName, impossible⟩ :=
    ContextualFreshening.different_activations_only_share_captures locals captures different
      first second _ inFirst inSecond
  cases impossible

#print axioms openRule_exact
#print axioms read_exact
#print axioms private_local_separates_uses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualABTPreparation
