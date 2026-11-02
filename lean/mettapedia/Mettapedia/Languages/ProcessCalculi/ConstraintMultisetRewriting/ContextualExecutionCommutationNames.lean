import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewRelocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels

/-!
# A nonidentity declaration isomorphism exchanging two activation blocks

A zero-equation solver return still retains its actual returned declaration
copy. Two such returns therefore contain two live activation blocks and
their helper copies. The isomorphism exchanges the live blocks, reindexes
their scope names, fixes original captures, and retains every helper name.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationNames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {Local V : Type} (locals : Local → MetaArity S) (captures : V → MetaArity S)

abbrev Names (Local V : Type) := (ScopedVar Local ⊕ V) ⊕ ((ScopedVar Local ⊕ V) ⊕ Empty)
abbrev declarations := ContextualComputedFreshFrame.active
  (ContextualSelectionViews.target locals captures) (ContextualSelectionViews.target locals captures)
abbrev Twice := Names Local (Names Local V)
abbrev twiceDeclarations := declarations locals (declarations locals captures)

def capture (name : V) : Names Local V := .inl (.inr name)
def oldCapture (name : V) : Twice (Local := Local) (V := V) := capture (capture name)
def earlier (name : ScopedVar Local) : Twice (Local := Local) (V := V) := .inl (.inr (.inl (.inl name)))
def later (name : ScopedVar Local) : Twice (Local := Local) (V := V) := .inl (.inl name)

def scopeMap (permutation : Equiv.Perm Nat) (name : ScopedVar Local) : ScopedVar Local :=
  ⟨permutation name.scope, name.name⟩

def exchange (permutation : Equiv.Perm Nat) : Twice (Local := Local) (V := V) → Twice (Local := Local) (V := V)
  | .inl (.inl name) => earlier (scopeMap permutation.symm name)
  | .inl (.inr (.inl (.inl name))) => later (scopeMap permutation name)
  | .inl (.inr (.inl (.inr name))) => oldCapture name
  | .inl (.inr (.inr helper)) => .inl (.inr (.inr helper))
  | .inr helper => .inr helper

theorem exchange_involutive (permutation : Equiv.Perm Nat) : Function.Involutive
    (exchange (Local := Local) (V := V) permutation) := by
  intro name
  cases name with
  | inr helper => rfl
  | inl active =>
      cases active with
      | inl name => cases name; simp [exchange, earlier, later, scopeMap]
      | inr previous =>
          cases previous with
          | inr helper => rfl
          | inl active =>
              cases active with
              | inl name => cases name; simp [exchange, earlier, later, scopeMap]
              | inr name => rfl

def namesEquiv (permutation : Equiv.Perm Nat) : Twice (Local := Local) (V := V) ≃ Twice (Local := Local) (V := V) :=
  ⟨exchange permutation, exchange permutation, exchange_involutive permutation, exchange_involutive permutation⟩

theorem exchange_preserves (permutation : Equiv.Perm Nat) (name : Twice (Local := Local) (V := V)) :
    twiceDeclarations locals captures (exchange permutation name) = twiceDeclarations locals captures name := by
  cases name with
  | inr helper => rfl
  | inl active =>
      cases active with
      | inl name => rfl
      | inr previous =>
          cases previous with
          | inr helper => rfl
          | inl active => cases active <;> rfl

def assignment (permutation : Equiv.Perm Nat) : Assignment
    (twiceDeclarations locals captures) (twiceDeclarations locals captures) :=
  reindex (exchange permutation) (exchange_preserves locals captures permutation)

theorem assignment_involutive (permutation : Equiv.Perm Nat) :
    Assignment.compose (assignment locals captures permutation) (assignment locals captures permutation) =
      generator (twiceDeclarations locals captures) :=
  reindex_left_inverse _ _ _ _ (exchange_involutive permutation)

theorem terms_round_trip (permutation : Equiv.Perm Nat) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (twiceDeclarations locals captures)) Γ sort) :
    instantiate (assignment locals captures permutation) (instantiate (assignment locals captures permutation) term) = term :=
  instantiate_reindex_inverse _ _ _ _ (exchange_involutive permutation) term

def intoCapture : Assignment captures (declarations locals captures) :=
  fun name => generator _ (capture name)

def intoOldCaptures : Assignment captures (twiceDeclarations locals captures) :=
  fun name => generator _ (oldCapture name)

def intoCreated (scope : Nat) : Assignment (ContextualSelectionViews.source locals captures)
    (declarations locals captures)
  | .inl name => generator (declarations locals captures) (.inl (.inl (ScopedVar.at scope name)))
  | .inr name => generator _ (capture name)

def intoEarlier (scope : Nat) : Assignment (ContextualSelectionViews.source locals captures)
    (twiceDeclarations locals captures)
  | .inl name => generator _ (earlier (ScopedVar.at scope name))
  | .inr name => generator _ (oldCapture name)

def intoLater (scope : Nat) : Assignment (ContextualSelectionViews.source locals captures)
    (twiceDeclarations locals captures)
  | .inl name => generator _ (later (ScopedVar.at scope name))
  | .inr name => generator _ (oldCapture name)

theorem twice_captured :
    Assignment.compose (intoCapture locals (declarations locals captures)) (intoCapture locals captures) =
      intoOldCaptures locals captures := by
  funext name
  change instantiate _ (generator _ (capture name)) = _
  rw [instantiate_generator]
  rfl

theorem created_then_captured (scope : Nat) :
    Assignment.compose (intoCapture locals (declarations locals captures)) (intoCreated locals captures scope) =
      intoEarlier locals captures scope := by
  funext name
  cases name with
  | inl name =>
      change instantiate _ (generator (declarations locals captures) (.inl (.inl (ScopedVar.at scope name)))) = _
      rw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate _ (generator (declarations locals captures) (capture name)) = _
      rw [instantiate_generator]
      rfl

theorem captured_then_created (scope : Nat) :
    Assignment.compose (intoCreated locals (declarations locals captures) scope)
      (ContextualStoredRows.liftCaptures locals (intoCapture locals captures)) =
      intoLater locals captures scope := by
  funext name
  cases name with
  | inl name =>
      change instantiate _ (generator (ContextualSelectionViews.source locals (declarations locals captures)) (.inl name)) = _
      rw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate (intoCreated locals (declarations locals captures) scope)
        (instantiate (ContextualSelectionViews.capturedSource locals (declarations locals captures))
          (generator (declarations locals captures) (capture name))) = _
      rw [instantiate_generator]
      change instantiate (intoCreated locals (declarations locals captures) scope)
        (generator (ContextualSelectionViews.source locals (declarations locals captures)) (.inr (capture name))) = _
      rw [instantiate_generator]
      rfl

theorem captures_fixed (permutation : Equiv.Perm Nat) :
    Assignment.compose (assignment locals captures permutation) (intoOldCaptures locals captures) =
      intoOldCaptures locals captures := by
  funext name
  change instantiate (assignment locals captures permutation) (generator _ (oldCapture name)) = _
  rw [instantiate_generator]
  rfl

theorem earlier_into_later (permutation : Equiv.Perm Nat) (scope : Nat) :
    Assignment.compose (assignment locals captures permutation) (intoEarlier locals captures scope) =
      intoLater locals captures (permutation scope) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (assignment locals captures permutation) (generator _ (earlier (ScopedVar.at scope name))) = _
      rw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate (assignment locals captures permutation) (generator _ (oldCapture name)) = _
      rw [instantiate_generator]
      rfl

theorem later_into_earlier (permutation : Equiv.Perm Nat) (scope : Nat) :
    Assignment.compose (assignment locals captures permutation) (intoLater locals captures scope) =
      intoEarlier locals captures (permutation.symm scope) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (assignment locals captures permutation) (generator _ (later (ScopedVar.at scope name))) = _
      rw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate (assignment locals captures permutation) (generator _ (oldCapture name)) = _
      rw [instantiate_generator]
      rfl

theorem exchange_is_not_identity (permutation : Equiv.Perm Nat) (name : ScopedVar Local) :
    exchange (V := V) permutation (earlier name) ≠ earlier name := by
  intro same
  cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationNames

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching
open ContextualExecutionCommutationNames (scopeMap)

/-- The actual port allocator in either ledger can be aligned by a scope
permutation. Original captures live in a separate, fixed summand. -/
theorem exists_scope_relocation {O : Type} (selection : Selection O)
    (sourceLedger targetLedger : Finset Nat) :
    ∃ relocation : Equiv.Perm Nat, ∀ port : ContextualActivationScopes.Port selection,
      relocation (ContextualActivationScopes.scopeAt sourceLedger port) =
        ContextualActivationScopes.scopeAt targetLedger port := by
  apply Equiv.Perm.exists_extending_pair
  · exact ContextualActivationScopes.at_injective sourceLedger (ContextualActivationScopes.count selection)
  · exact ContextualActivationScopes.at_injective targetLedger (ContextualActivationScopes.count selection)

variable {S : Signature} {Local Shared Helper : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

/-- A common frame gives each event its own private variables and retains a
single original caller interface. Solver helpers are not part of this frame. -/
abbrev common := ContextualSelectionViews.target locals (ContextualSelectionViews.target locals captures)

def firstName : ScopedVar Local ⊕ Shared → ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared)
  | .inl privateName => .inl privateName
  | .inr sharedName => .inr (.inr sharedName)

def secondName : ScopedVar Local ⊕ Shared → ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared)
  | .inl privateName => .inr (.inl privateName)
  | .inr sharedName => .inr (.inr sharedName)

abbrev first : Extension (ContextualSelectionViews.target locals captures) where
  Names := ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared)
  declarations := common locals captures
  name := firstName
  injective := by
    intro one two same
    cases one <;> cases two <;> simp_all [firstName]
  preserves name := by cases name <;> rfl

abbrev second : Extension (ContextualSelectionViews.target locals captures) where
  Names := ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared)
  declarations := common locals captures
  name := secondName
  injective := by
    intro one two same
    cases one <;> cases two <;> simp_all [secondName]
  preserves name := by cases name <;> rfl

def caller : Assignment captures (common locals captures) :=
  fun name => generator (common locals captures) (.inr (.inr name))

theorem first_caller : Assignment.compose (first locals captures).assignment
    (ContextualSelectionViews.capturedTarget locals captures) = caller locals captures := by
  funext name
  change instantiate (first locals captures).assignment
    (generator (ContextualSelectionViews.target locals captures) (Sum.inr name)) = _
  rw [instantiate_generator]
  rfl

theorem second_caller : Assignment.compose (second locals captures).assignment
    (ContextualSelectionViews.capturedTarget locals captures) = caller locals captures := by
  funext name
  change instantiate (second locals captures).assignment
    (generator (ContextualSelectionViews.target locals captures) (Sum.inr name)) = _
  rw [instantiate_generator]
  rfl

variable (helpers : Helper → MetaArity S)

abbrev afterFirst := ContextualComputedFreshFrame.active
  (ContextualSelectionViews.target locals captures) helpers

abbrev firstSource : Extension (ContextualSelectionViews.target locals captures) where
  Names := (ScopedVar Local ⊕ Shared) ⊕ (Helper ⊕ Empty)
  declarations := afterFirst locals captures helpers
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

abbrev oldCaller : Extension captures where
  Names := (ScopedVar Local ⊕ Shared) ⊕ (Helper ⊕ Empty)
  declarations := afterFirst locals captures helpers
  name := Sum.inl ∘ Sum.inr
  injective := Sum.inl_injective.comp Sum.inr_injective
  preserves _ := rfl

theorem firstSource_actual
    {problem : ContextualResidual.Problem (ContextualSelectionViews.target locals captures)}
    (update : ContextualFrameUpdate.Update problem) :
    (firstSource locals captures update.declaration).assignment =
      ContextualComputedFreshFrame.includeSource update := by
  funext name
  change generator (afterFirst locals captures update.declaration) (Sum.inl name) =
    instantiate (ContextualFreshFrame.includeOld (ContextualSelectionViews.target locals captures)
      update.declaration ContextualComputedFreshFrame.noDeclarations)
      (generator (ContextualComputedFreshFrame.old (ContextualSelectionViews.target locals captures)) (Sum.inl name))
  rw [instantiate_generator]
  rfl

theorem oldCaller_square : Assignment.compose (firstSource locals captures helpers).assignment
    (ContextualSelectionViews.capturedTarget locals captures) = (oldCaller locals captures helpers).assignment := by
  funext name
  change instantiate (firstSource locals captures helpers).assignment
    (generator (ContextualSelectionViews.target locals captures) (Sum.inr name)) = _
  rw [instantiate_generator]
  rfl

def secondActiveName (relocation : Equiv.Perm Nat) :
    ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared) →
      ScopedVar Local ⊕ ((ScopedVar Local ⊕ Shared) ⊕ (Helper ⊕ Empty))
  | .inl earlierName => .inr (.inl (.inl earlierName))
  | .inr (.inl laterName) => .inl (scopeMap relocation laterName)
  | .inr (.inr sharedName) => .inr (.inl (.inr sharedName))

private theorem scopeMap_injective (relocation : Equiv.Perm Nat) :
    Function.Injective (scopeMap (Local := Local) relocation) := by
  intro one two same
  have scopes := relocation.injective (congrArg ScopedVar.scope same)
  have names := congrArg ScopedVar.name same
  cases one
  cases two
  simp_all only [scopeMap, ScopedVar.mk.injEq]

/-- The common frame embeds in the actual second activation for any helper
family returned by the first solver. Only the second event's private scope
addresses are relocated. Both events retain the same caller variables. -/
abbrev secondActive (relocation : Equiv.Perm Nat) : Extension (common locals captures) where
  Names := ScopedVar Local ⊕ ((ScopedVar Local ⊕ Shared) ⊕ (Helper ⊕ Empty))
  declarations := ContextualSelectionViews.target locals (afterFirst locals captures helpers)
  name := secondActiveName relocation
  injective := by
    intro one two same
    cases one with
    | inl one =>
      cases two with
      | inl two => simp_all [secondActiveName]
      | inr two => cases two <;> cases same
    | inr one =>
      cases one with
      | inl one =>
        cases two with
        | inl two => cases same
        | inr two =>
          cases two with
          | inl two => exact congrArg (Sum.inr ∘ Sum.inl) (scopeMap_injective relocation (Sum.inl.inj same))
          | inr two => cases same
      | inr one =>
        cases two with
        | inl two => cases same
        | inr two => cases two <;> simp_all [secondActiveName]
  preserves name := by
    cases name with
    | inl name => rfl
    | inr name => cases name <;> rfl

theorem first_activation_square (relocation : Equiv.Perm Nat) :
    Assignment.compose (secondActive locals captures helpers relocation).assignment
        (first locals captures).assignment =
      Assignment.compose (ContextualSelectionViews.capturedTarget locals (afterFirst locals captures helpers))
        (firstSource locals captures helpers).assignment := by
  funext name
  cases name with
  | inl name =>
    change instantiate (secondActive locals captures helpers relocation).assignment
      (generator (common locals captures) (Sum.inl name)) =
        instantiate (ContextualSelectionViews.capturedTarget locals (afterFirst locals captures helpers))
          (generator (afterFirst locals captures helpers) (Sum.inl (Sum.inl name)))
    rw [instantiate_generator, instantiate_generator]
    rfl
  | inr name =>
    change instantiate (secondActive locals captures helpers relocation).assignment
      (generator (common locals captures) (Sum.inr (Sum.inr name))) =
        instantiate (ContextualSelectionViews.capturedTarget locals (afterFirst locals captures helpers))
          (generator (afterFirst locals captures helpers) (Sum.inl (Sum.inr name)))
    rw [instantiate_generator, instantiate_generator]
    rfl

theorem second_activation_square (relocation : Equiv.Perm Nat) (scope : Nat) :
    Assignment.compose (secondActive locals captures helpers relocation).assignment
        (Assignment.compose (second locals captures).assignment (ContextualFreshening.assignment locals captures scope)) =
      Assignment.compose (ContextualFreshening.assignment locals (afterFirst locals captures helpers) (relocation scope))
        (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment) := by
  funext name
  cases name with
  | inl name =>
    change instantiate (secondActive locals captures helpers relocation).assignment
      (instantiate (second locals captures).assignment
        (generator (ContextualSelectionViews.target locals captures) (Sum.inl (ScopedVar.at scope name)))) =
      instantiate (ContextualFreshening.assignment locals (afterFirst locals captures helpers) (relocation scope))
        (generator (ContextualSelectionViews.source locals (afterFirst locals captures helpers)) (Sum.inl name))
    rw [instantiate_generator, instantiate_generator]
    change instantiate (secondActive locals captures helpers relocation).assignment
      (generator (common locals captures) (Sum.inr (Sum.inl (ScopedVar.at scope name)))) = _
    rw [instantiate_generator]
    rfl
  | inr name =>
    change instantiate (secondActive locals captures helpers relocation).assignment
      (instantiate (second locals captures).assignment
        (generator (ContextualSelectionViews.target locals captures) (Sum.inr name))) =
      instantiate (ContextualFreshening.assignment locals (afterFirst locals captures helpers) (relocation scope))
        (instantiate (ContextualSelectionViews.capturedSource locals (afterFirst locals captures helpers))
          (generator (afterFirst locals captures helpers) (Sum.inl (Sum.inr name))))
    rw [instantiate_generator, instantiate_generator]
    change instantiate (secondActive locals captures helpers relocation).assignment
      (generator (common locals captures) (Sum.inr (Sum.inr name))) =
      instantiate (ContextualFreshening.assignment locals (afterFirst locals captures helpers) (relocation scope))
        (generator (ContextualSelectionViews.source locals (afterFirst locals captures helpers))
          (Sum.inr (Sum.inl (Sum.inr name))))
    rw [instantiate_generator, instantiate_generator]
    rfl

def secondView (relocation : Equiv.Perm Nat) :
    Assignment (ContextualSelectionViews.target locals captures)
      (ContextualSelectionViews.target locals (afterFirst locals captures helpers)) :=
  Assignment.compose (secondActive locals captures helpers relocation).assignment (second locals captures).assignment

theorem second_view_opening (relocation : Equiv.Perm Nat) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :
    instantiate (secondView locals captures helpers relocation) (ContextualFreshening.termAt locals captures scope term) =
      ContextualFreshening.termAt locals (afterFirst locals captures helpers) (relocation scope)
        (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment) term) := by
  simp only [secondView, ContextualFreshening.termAt, ← Assignment.instantiate_compose]
  rw [← Assignment.compose_associative, second_activation_square]

theorem second_view_row (relocation : Equiv.Perm Nat) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : ContextualStoredRows.Row locals captures Γ sort) :
    instantiate (secondView locals captures helpers relocation) (ContextualStoredRows.viewAt locals captures scope row) =
      ContextualStoredRows.viewAt locals (afterFirst locals captures helpers) (relocation scope)
        (row.map locals (oldCaller locals captures helpers).assignment) := by
  rw [ContextualStoredRows.viewAt_eq_freshening, ContextualStoredRows.viewAt_eq_freshening,
    ContextualStoredRows.asTemplate_map]
  exact second_view_opening locals captures helpers relocation scope _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames
