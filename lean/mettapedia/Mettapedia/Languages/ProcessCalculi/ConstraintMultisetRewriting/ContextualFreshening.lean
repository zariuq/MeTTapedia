import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedVariables

/-!
# Fresh contextual schema activations with explicit captures

Each local identity receives the activation's scope, while a captured identity
remains shared. This is contextual instantiation in the existing binding terms,
not renaming by display names. Parameter contexts and sorts are preserved.
Different activations can share only captures, and opening is injective.

This operation prepares rule instances. A runtime still has to allocate fresh
activation scopes and connect stored-schema selection to these instances.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshening

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {Local Shared : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

abbrev declarations : Local ⊕ Shared → MetaArity S := Sum.elim locals captures

abbrev scopedDeclarations : ScopedVar Local ⊕ Shared → MetaArity S :=
  Sum.elim (fun localName => locals localName.name) captures

def assignment (scope : Nat) :
    Assignment (declarations locals captures) (scopedDeclarations locals captures)
  | .inl localName => generator (scopedDeclarations locals captures) (.inl (ScopedVar.at scope localName))
  | .inr sharedName => generator (scopedDeclarations locals captures) (.inr sharedName)

def forgetAssignment :
    Assignment (scopedDeclarations locals captures) (declarations locals captures)
  | .inl localName => generator (declarations locals captures) (.inl localName.name)
  | .inr sharedName => generator (declarations locals captures) (.inr sharedName)

def termAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (declarations locals captures)) Γ sort) :
    Term (signature S (scopedDeclarations locals captures)) Γ sort :=
  instantiate (assignment locals captures scope) term

def ruleAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (declarations locals captures)) Γ sort)) :
    RuleInstance (Term (signature S (scopedDeclarations locals captures)) Γ sort) :=
  rule.map (termAt locals captures scope)

theorem forget_termAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (declarations locals captures)) Γ sort) :
    instantiate (forgetAssignment locals captures) (termAt locals captures scope term) = term := by
  rw [termAt, instantiate_comp]
  have components :
      (fun identity => instantiate (forgetAssignment locals captures)
        (assignment locals captures scope identity)) = generator (declarations locals captures) := by
    funext identity
    cases identity with
    | inl name =>
        exact instantiate_generator (forgetAssignment locals captures) (.inl (ScopedVar.at scope name))
    | inr name => exact instantiate_generator (forgetAssignment locals captures) (.inr name)
  rw [components, instantiate_identity]

theorem termAt_injective (scope : Nat) {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (termAt locals captures scope (Γ := Γ) (sort := sort)) := by
  intro first second same
  have restored := congrArg (instantiate (forgetAssignment locals captures)) same
  simpa only [forget_termAt] using restored

mutual

theorem support_termAt (scope : Nat) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      (term : Term (signature S (declarations locals captures)) Γ sort),
      support (termAt locals captures scope term) =
        (support term).map (ScopedVariables.variableAt scope)
  | _, _, .var _ => rfl
  | _, _, .op (.inl _) arguments => supportArgs_assignment scope arguments
  | _, _, .op (.inr (.mk (.inl localName))) arguments => by
      have reapplied := bindArgs_selfArgs (T := signature S (scopedDeclarations locals captures))
        (locals localName).1 (instantiateArgs (assignment locals captures scope) arguments)
      simp only [termAt, instantiate, assignment, generator, Mettapedia.OSLF.Binding.bind,
        support, List.map_cons, ScopedVariables.variableAt]
      dsimp only [scopedDeclarations, declarations, ScopedVar.at, Sum.elim] at reapplied ⊢
      rw [reapplied]
      exact congrArg (List.cons (Sum.inl (ScopedVar.at scope localName)))
        (supportArgs_assignment scope arguments)
  | _, _, .op (.inr (.mk (.inr sharedName))) arguments => by
      have reapplied := bindArgs_selfArgs (T := signature S (scopedDeclarations locals captures))
        (captures sharedName).1 (instantiateArgs (assignment locals captures scope) arguments)
      simp only [termAt, instantiate, assignment, generator, Mettapedia.OSLF.Binding.bind,
        support, List.map_cons, ScopedVariables.variableAt]
      dsimp only [scopedDeclarations, declarations, Sum.elim] at reapplied ⊢
      rw [reapplied]
      exact congrArg (List.cons (Sum.inr sharedName))
        (supportArgs_assignment scope arguments)

theorem supportArgs_assignment (scope : Nat) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (signature S (declarations locals captures)) arities Γ),
      supportArgs (instantiateArgs (assignment locals captures scope) arguments) =
        (supportArgs arguments).map (ScopedVariables.variableAt scope)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [instantiateArgs, supportArgs, List.map_append]
      exact congrArg₂ List.append (support_termAt scope head)
        (supportArgs_assignment scope tail)

end

theorem local_scope (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (declarations locals captures)) Γ sort)
    (localName : ScopedVar Local)
    (member : Sum.inl localName ∈ support (termAt locals captures scope term)) :
    localName.scope = scope := by
  rw [support_termAt] at member
  obtain ⟨original, _, image⟩ := List.mem_map.mp member
  cases original with
  | inl name => exact congrArg ScopedVar.scope (Sum.inl.inj image).symm
  | inr name => cases image

theorem captured_iff (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (declarations locals captures)) Γ sort) (sharedName : Shared) :
    Sum.inr sharedName ∈ support (termAt locals captures scope term) ↔
      Sum.inr sharedName ∈ support term := by
  rw [support_termAt, List.mem_map]
  constructor
  · rintro ⟨original, member, image⟩
    cases original with
    | inl name => cases image
    | inr name => exact Sum.inr.inj image ▸ member
  · intro member
    exact ⟨.inr sharedName, member, rfl⟩

/-- Sharing an occurrence does not identify the schematic locals of its
separate activations. Explicit captures retain their shared identity. -/
theorem different_activations_only_share_captures {leftScope rightScope : Nat}
    (different : leftScope ≠ rightScope) {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S (declarations locals captures)) Γ sort)
    (identity : ScopedVar Local ⊕ Shared)
    (inLeft : identity ∈ support (termAt locals captures leftScope left))
    (inRight : identity ∈ support (termAt locals captures rightScope right)) :
    ∃ sharedName : Shared, identity = .inr sharedName := by
  cases identity with
  | inr sharedName => exact ⟨sharedName, rfl⟩
  | inl localName =>
      exact False.elim (different ((local_scope locals captures leftScope left localName inLeft).symm.trans
        (local_scope locals captures rightScope right localName inRight)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshening
