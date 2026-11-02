import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationNames

/-! # Independent scope maps for exchanging unequal selected-port blocks -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedNames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualExecutionCommutationNames

variable {S : Signature} {Local V : Type} (locals : Local → MetaArity S) (captures : V → MetaArity S)

def exchange (first second : Equiv.Perm Nat) : Twice (Local := Local) (V := V) → Twice (Local := Local) (V := V)
  | .inl (.inl name) => earlier (scopeMap second name)
  | .inl (.inr (.inl (.inl name))) => later (scopeMap first name)
  | .inl (.inr (.inl (.inr name))) => oldCapture name
  | .inl (.inr (.inr helper)) => .inl (.inr (.inr helper))
  | .inr helper => .inr helper

theorem inverse (first second : Equiv.Perm Nat) (name : Twice (Local := Local) (V := V)) :
    exchange second.symm first.symm (exchange first second name) = name := by
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

def namesEquiv (first second : Equiv.Perm Nat) : Twice (Local := Local) (V := V) ≃ Twice (Local := Local) (V := V) where
  toFun := exchange first second
  invFun := exchange second.symm first.symm
  left_inv := inverse first second
  right_inv name := by simpa only [Equiv.symm_symm] using inverse second.symm first.symm name

theorem preserves (first second : Equiv.Perm Nat) (name : Twice (Local := Local) (V := V)) :
    twiceDeclarations locals captures (exchange first second name) = twiceDeclarations locals captures name := by
  cases name with
  | inr helper => rfl
  | inl active =>
      cases active with
      | inl name => rfl
      | inr previous =>
          cases previous with
          | inr helper => rfl
          | inl active => cases active <;> rfl

def assignment (first second : Equiv.Perm Nat) : Assignment (twiceDeclarations locals captures) (twiceDeclarations locals captures) :=
  reindex (exchange first second) (preserves locals captures first second)

theorem assignment_inverse (first second : Equiv.Perm Nat) :
    Assignment.compose (assignment locals captures second.symm first.symm) (assignment locals captures first second) =
      generator (twiceDeclarations locals captures) :=
  reindex_left_inverse _ _ _ _ (inverse first second)

theorem captures_fixed (first second : Equiv.Perm Nat) :
    Assignment.compose (assignment locals captures first second) (intoOldCaptures locals captures) =
      intoOldCaptures locals captures := by
  funext name
  change instantiate (assignment locals captures first second) (generator _ (oldCapture name)) = _
  rw [instantiate_generator]
  rfl

theorem earlier_into_later (first second : Equiv.Perm Nat) (scope : Nat) :
    Assignment.compose (assignment locals captures first second) (intoEarlier locals captures scope) =
      intoLater locals captures (first scope) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (assignment locals captures first second) (generator _ (earlier (ScopedVar.at scope name))) = _
      rw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate (assignment locals captures first second) (generator _ (oldCapture name)) = _
      rw [instantiate_generator]
      rfl

theorem later_into_earlier (first second : Equiv.Perm Nat) (scope : Nat) :
    Assignment.compose (assignment locals captures first second) (intoLater locals captures scope) =
      intoEarlier locals captures (second scope) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (assignment locals captures first second) (generator _ (later (ScopedVar.at scope name))) = _
      rw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate (assignment locals captures first second) (generator _ (oldCapture name)) = _
      rw [instantiate_generator]
      rfl

theorem not_identity (first second : Equiv.Perm Nat) (name : ScopedVar Local) :
    exchange (V := V) first second (earlier name) ≠ earlier name := by intro same; cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedNames
