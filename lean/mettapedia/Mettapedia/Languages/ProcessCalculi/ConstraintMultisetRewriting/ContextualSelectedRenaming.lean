import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedPair

/-! # Formation transport between unequal selected-port allocation orders -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedRenaming

open ContextualActivationScopes ContextualFreshFrameScopeLedger ContextualScopeSupport
open ContextualSelectedScopes ContextualExecutionCommutationNames

def earlierScopes (occupied : Finset Nat) (_first second : Nat) : Equiv.Perm Nat :=
  Equiv.swap (start occupied) (start (advance occupied second))
def laterScopes (occupied : Finset Nat) (first _second : Nat) : Equiv.Perm Nat :=
  Equiv.swap (start (advance occupied first)) (start occupied)

theorem swap_membership (world : Finset Nat) (first second name : Nat)
    (firstPresent : first ∈ world) (secondPresent : second ∈ world) :
    Equiv.swap first second name ∈ world ↔ name ∈ world := by
  by_cases one : name = first
  · subst name; simp [firstPresent, secondPresent]
  by_cases two : name = second
  · subst name; simp [firstPresent, secondPresent]
  rw [Equiv.swap_apply_of_ne_of_ne one two]

def scopesAfter {Local V : Type} (scopes : V → Finset Nat) (occupied : Finset Nat) (ports : Nat) :
    Names Local V → Finset Nat := frameScopes (activeScopes scopes) (helperScope (reserve occupied ports))

def scopesTwice {Local V : Type} (scopes : V → Finset Nat) (occupied : Finset Nat) (first second : Nat) :
    Twice (Local := Local) (V := V) → Finset Nat := scopesAfter (scopesAfter scopes occupied first) (advance occupied first) second

theorem last_helper_comm (occupied : Finset Nat) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    helperScope (reserve (advance occupied first) second) = helperScope (reserve (advance occupied second) first) := by
  rw [last_helper_scope occupied first second firstPositive secondPositive,
    last_helper_scope occupied second first secondPositive firstPositive]
  omega

theorem scope_coverage {Local V : Type} (scopes : V → Finset Nat) (occupied : Finset Nat) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) (name : Twice (Local := Local) (V := V)) :
    scopesTwice scopes occupied second first
        (ContextualSelectedNames.exchange (earlierScopes occupied first second) (laterScopes occupied first second) name) ⊆
        advance (advance occupied second) first ↔
      scopesTwice scopes occupied first second name ⊆ advance (advance occupied first) second := by
  rw [advance_comm occupied second first secondPositive firstPositive]
  have rules := rule_scope_in_final occupied first second firstPositive secondPositive
  have helpers := helper_scope_in_final occupied first second firstPositive secondPositive
  cases name with
  | inr helper =>
      cases helper with
      | inl _ =>
          change ({helperScope (reserve (advance occupied second) first)} : Finset Nat) ⊆ _ ↔
            ({helperScope (reserve (advance occupied first) second)} : Finset Nat) ⊆ _
          rw [last_helper_comm occupied first second firstPositive secondPositive]
      | inr impossible => exact nomatch impossible
  | inl active =>
      cases active with
      | inl name =>
          change ({laterScopes occupied first second name.scope} : Finset Nat) ⊆ _ ↔
            ({name.scope} : Finset Nat) ⊆ _
          simp only [Finset.singleton_subset_iff]
          exact swap_membership _ _ _ _ rules.2.1 rules.1
      | inr previous =>
          cases previous with
          | inr helper =>
              cases helper with
              | inl _ =>
                  change ({helperScope (reserve occupied second)} : Finset Nat) ⊆ _ ↔
                    ({helperScope (reserve occupied first)} : Finset Nat) ⊆ _
                  simp only [Finset.singleton_subset_iff]
                  exact iff_of_true helpers.2 helpers.1
              | inr impossible => exact nomatch impossible
          | inl active =>
              cases active with
              | inl name =>
                  change ({earlierScopes occupied first second name.scope} : Finset Nat) ⊆ _ ↔
                    ({name.scope} : Finset Nat) ⊆ _
                  simp only [Finset.singleton_subset_iff]
                  exact swap_membership _ _ _ _ rules.1 rules.2.2
              | inr _ => rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedRenaming
