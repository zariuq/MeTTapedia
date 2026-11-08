import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ConstantInstances
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContractRowIsolation

/-!
# Constant guards in the residual coordinates of their actual derivation

The native row scan excludes CONSTANT parameters only after their declaration
match and fix-closed check. This module retains that evidence and uses the
existing selector theorem: every assignment of the derivation's residual
variables is compatible with that constant. The computed two-occurrence test
then proves that changing the paired residual variable leaves all other
nonconstant formals unchanged. Authored demand is never recomputed from those
instantiated types.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaConstantRowResidual

open Mettapedia.Logic.LP (Subst)
open ConstantInstances (Side derive readTy FixesClosed)
open TypeEquationSolver (signature)
open PettaContractRowIsolation (Parameter recognizes)

local instance : BEq Side := ⟨fun first second => decide (first = second)⟩
local instance : LawfulBEq Side where
  eq_of_beq := of_decide_eq_true
  rfl := by intro name; exact decide_eq_true rfl

structure AcceptedConstant where
  formal : Ty String
  declaration : Ty String
  solver : Subst (signature Side)
  derived : derive formal declaration = some solver
  fixesClosed : FixesClosed solver formal declaration

def assignment (entry : AcceptedConstant) (residual : Side → Ty Empty) : String → Ty Empty :=
  fun name => (readTy entry.solver (.inl name)).bind residual

/-- The compiler's actual MGU, not a chosen compatible-output oracle, earns
this compatibility for every residual assignment. FixesClosed is retained as
the native admission; MGU soundness gives the stronger algebraic fact. -/
theorem every_residual_assignment_fits (entry : AcceptedConstant) (residual : Side → Ty Empty) :
    ∃ declared : String → Ty Empty,
      entry.declaration.bind declared = entry.formal.bind (assignment entry residual) := by
  apply (ConstantInstances.derive_selects entry.derived (assignment entry residual)).mpr
  exact ⟨residual, fun _ _ => rfl⟩

/-- On the derived-instance coordinates, the constant's constraint does not
remove an otherwise allowed assignment. It can still introduce private
aliases in a concrete binding representation. -/
theorem constant_constraint_allows_exactly (entry : AcceptedConstant) (index : Nat)
    (store : List (Eqn CallVar)) (fresh : ∀ v, atGuard index v ∉ eqnVars store)
    (residual : Side → Ty Empty) :
    Allows (store ++ [(((entry.declaration.map DVar.own).map (atGuard index) : Ty CallVar),
      entry.formal.map Sum.inl)]) (assignment entry residual) ↔
      Allows store (assignment entry residual) := by
  rw [ConstantInstances.constant_allows index store fresh]
  constructor
  · exact And.left
  · intro allowed
    exact ⟨allowed, every_residual_assignment_fits entry residual⟩

theorem residual_update_still_fits (entry : AcceptedConstant) (residual : Side → Ty Empty)
    (name : Side) (type : Ty Empty) :
    ∃ declared : String → Ty Empty, entry.declaration.bind declared =
      entry.formal.bind (assignment entry (Function.update residual name type)) :=
  every_residual_assignment_fits entry _

theorem clear_residual_type_unchanged (type : Ty Side) (residual : Side → Ty Empty)
    (name : Side) (replacement : Ty Empty) (clear : name ∉ type.vars) :
    type.bind (Function.update residual name replacement) = type.bind residual := by
  apply Ty.bind_congr
  intro v member
  have apart : v ≠ name := fun same => clear (same ▸ member)
  exact Function.update_of_ne apart _ _

/-- Native occurrence counting earns this frame fact for every other
nonconstant formal. Constant compatibility above is the separate missing
half; exclusion from the count alone would not justify it. -/
theorem recognized_pair_preserves_other_requests
    (before : List (Parameter Side)) (current : Parameter Side) (after : List (Parameter Side))
    (authoredRange : Ty String) (resolvedRange : Ty Side) (name : Side)
    (recognized : recognizes before current after authoredRange resolvedRange = some name)
    (residual : Side → Ty Empty) (replacement : Ty Empty) :
    ∀ parameter ∈ before ++ after, parameter.constant = false →
      parameter.resolved.bind (Function.update residual name replacement) = parameter.resolved.bind residual := by
  intro parameter present ordinary
  exact clear_residual_type_unchanged parameter.resolved residual name replacement
    (PettaContractRowIsolation.recognition_clears_other_formals before current after
      authoredRange resolvedRange name recognized parameter present ordinary)

open Classical in
/-- A compatible constant whose symbol has one declaration has exactly one
actual guard continuation. No global functional declaration space is assumed. -/
theorem constant_guard_once (entry : AcceptedConstant) (declarations : Decls) (symbol : String)
    (oneDeclaration : declarations symbol = [entry.declaration]) (noMeta : NoMeta entry.formal)
    (grounded : String → Bool) (index : Nat) (store : List (Eqn CallVar))
    (fresh : ∀ v, atGuard index v ∉ eqnVars store)
    (residual : Side → Ty Empty) (allowed : Allows store (assignment entry residual)) :
    guard (atGuard index) store (entry.formal.map Sum.inl)
      (info declarations (.symbol symbol)) (metatype grounded (.symbol symbol)) =
      {store ++ [(((entry.declaration.map DVar.own).map (atGuard index) : Ty CallVar), entry.formal.map Sum.inl)]} := by
  rw [ConstantInstances.constant_guard oneDeclaration noMeta grounded index store fresh]
  exact if_pos ⟨assignment entry residual, allowed, every_residual_assignment_fits entry residual⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaConstantRowResidual
