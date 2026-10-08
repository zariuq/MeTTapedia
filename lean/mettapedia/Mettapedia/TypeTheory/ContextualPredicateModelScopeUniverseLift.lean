import Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift
import Mettapedia.TypeTheory.ContextualPredicateModelScopes
import Mettapedia.TypeTheory.ContextualTelescopeUniverseLift

/-!
# Mixed dependent scopes through complete predicate-model lifts

Data variables and proposition assumptions retain their ordered positions.
Lookup and every supplied component preserve the actual type and section.
Guarded assembly agrees with the original checker, including failure; no
assumption proof is erased into a fabricated data argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateModelScopes ContextualModelTelescopes
open ContextualPredicateModelUniverseLift
open ContextualCwfUniverseLift (Raised liftValue lowerValue liftValue_substitute
  liftValue_option_injective)

attribute [local instance] ContextualPredicateModelUniverseLift.liftedHeytingAlgebra

universe c s t m p uc vs wt ms ps

variable {C : CwfWithTerminal.{c, s, t, m}}
variable {doctrine : PredicateDoctrine.{c, s, t, m, p} C.toCwf}
variable {assumptions : AssumptionOperations doctrine}

/-- Every guard, including a rejected guard, keeps its original logical
value through the external predicate-carrier change. -/
theorem lifted_guard_iff {source target : C.toCwf.Ctx}
    (predicate : doctrine.Predicate target) (substitution : C.toCwf.Sub source target) :
    (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} (C := C.toCwf) doctrine).reindex
      (ULift.up substitution) (ULift.up predicate) =
        (⊤ : ULift.{ps} (doctrine.Predicate source)) ↔
      doctrine.reindex substitution predicate = ⊤ := by
  constructor
  · exact fun guard => congrArg ULift.down guard
  · exact fun guard => congrArg ULift.up guard

theorem liftSelect_eq_some_iff {source target : C.toCwf.Ctx}
    (predicate : doctrine.Predicate target) (substitution : C.toCwf.Sub source target)
    (selected : C.toCwf.Sub source (assumptions.assumed target predicate)) :
    select? (C := ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)
      (liftAssumptions.{c, s, t, m, p, uc, vs, wt, ms, ps} (C := C.toCwf) assumptions)
      (ULift.up predicate) (ULift.up substitution) = some (ULift.up selected) ↔
      select? (C := C) assumptions predicate substitution = some selected := by
  have liftedCriterion := select?_eq_some_iff
    (C := ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)
    (liftAssumptions.{c, s, t, m, p, uc, vs, wt, ms, ps} (C := C.toCwf) assumptions)
    (ULift.up predicate) (ULift.up substitution) (ULift.up selected)
  have nativeCriterion := select?_eq_some_iff (C := C) assumptions predicate substitution selected
  constructor
  · intro checked
    exact nativeCriterion.mpr (congrArg ULift.down (liftedCriterion.mp checked))
  · intro checked
    exact liftedCriterion.mpr (congrArg ULift.up (nativeCriterion.mp checked))

theorem liftSelect {source target : C.toCwf.Ctx}
    (predicate : doctrine.Predicate target) (substitution : C.toCwf.Sub source target) :
    select? (C := ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)
      (liftAssumptions.{c, s, t, m, p, uc, vs, wt, ms, ps} (C := C.toCwf) assumptions)
      (ULift.up predicate) (ULift.up substitution) =
      (select? (C := C) assumptions predicate substitution).map ULift.up := by
  cases original : select? (C := C) assumptions predicate substitution with
  | some selected => exact (liftSelect_eq_some_iff predicate substitution selected).mpr original
  | none =>
      cases lifted : select?
          (C := ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)
          (liftAssumptions.{c, s, t, m, p, uc, vs, wt, ms, ps} (C := C.toCwf) assumptions)
          (ULift.up predicate) (ULift.up substitution) with
      | none => rfl
      | some selected =>
          cases selected with
          | up selected =>
              have impossible := (liftSelect_eq_some_iff predicate substitution selected).mp lifted
              rw [original] at impossible
              cases impossible

def liftScopeData : {n : Nat} → {context : C.toCwf.Ctx} →
    ScopeData C doctrine assumptions n context →
      ScopeData (ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)
        (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine)
        (liftAssumptions assumptions) n (ULift.up context)
  | _, _, .nil => .nil
  | _, _, .snoc previous type => .snoc (liftScopeData previous) (ULift.up type)
  | _, _, .assume previous predicate => .assume (liftScopeData previous) (ULift.up predicate)

def liftScope {n : Nat} (scope : Scope C doctrine assumptions n) :
    Scope (ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)
      (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine)
      (liftAssumptions assumptions) n :=
  ⟨ULift.up scope.1, liftScopeData scope.2⟩

@[simp] theorem liftScope_nil :
    liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} (Scope.nil C doctrine assumptions) =
      Scope.nil (ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)
        (liftDoctrine doctrine) (liftAssumptions assumptions) := rfl

@[simp] theorem liftScope_snoc {n : Nat} (scope : Scope C doctrine assumptions n)
    (type : C.toCwf.Ty scope.1) :
    liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} (Scope.snoc scope type) =
      Scope.snoc (liftScope scope) (ULift.up type) := rfl

@[simp] theorem liftScope_assume {n : Nat} (scope : Scope C doctrine assumptions n)
    (predicate : doctrine.Predicate scope.1) :
    liftScope.{c, s, t, m, p, uc, vs, wt, ms, ps} (Scope.assume scope predicate) =
      Scope.assume (liftScope scope) (ULift.up predicate) := rfl

theorem liftScopeData_lookup : {n : Nat} → {context : C.toCwf.Ctx} →
    (scope : ScopeData C doctrine assumptions n context) → (index : Fin n) →
    (liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).lookup index =
      liftValue.{c, s, t, m, uc, vs, wt, ms} (scope.lookup index)
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .snoc previous type, index => by
      cases index using Fin.cases with
      | zero => rfl
      | succ preceding =>
          change Value.substitute
            ((liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} previous).lookup preceding)
              (ULift.up (C.toCwf.wk type)) = _
          rw [liftScopeData_lookup]
          rfl
  | _, _, .assume previous predicate, index => by
      change Value.substitute
        ((liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} previous).lookup index)
          (ULift.up (assumptions.inclusion predicate)) = _
      rw [liftScopeData_lookup]
      rfl

theorem liftScopeData_components {n : Nat} {source target : C.toCwf.Ctx}
    (scope : ScopeData C doctrine assumptions n target)
    (substitution : C.toCwf.Sub source target) (index : Fin n) :
    (liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).components
      (ULift.up substitution) index =
        liftValue.{c, s, t, m, uc, vs, wt, ms} (scope.components substitution index) := by
  change Value.substitute
    ((liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).lookup index)
      (ULift.up substitution) = _
  rw [liftScopeData_lookup]
  rfl

theorem lookup_readout {n : Nat} {context : C.toCwf.Ctx}
    (scope : ScopeData C doctrine assumptions n context) (index : Fin n) :
    lowerValue.{c, s, t, m, uc, vs, wt, ms}
      ((liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).lookup index) =
      scope.lookup index := by
  rw [liftScopeData_lookup, ContextualCwfUniverseLift.lower_liftValue]

theorem components_readout {n : Nat} {source target : C.toCwf.Ctx}
    (scope : ScopeData C doctrine assumptions n target)
    (substitution : C.toCwf.Sub source target) (index : Fin n) :
    lowerValue.{c, s, t, m, uc, vs, wt, ms}
      ((liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).components
        (ULift.up substitution) index) = scope.components substitution index := by
  rw [liftScopeData_components, ContextualCwfUniverseLift.lower_liftValue]

/-- A supplied actual arrow succeeds in the lifted mixed checker exactly
when it succeeds in the original one, including every assumption guard. -/
theorem liftScopeData_assemble_eq_some_iff {n : Nat} {source target : C.toCwf.Ctx}
    (scope : ScopeData C doctrine assumptions n target)
    (supplied : Fin n → Option (Value C.toCwf source))
    (substitution : C.toCwf.Sub source target) :
    (liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).assemble?
      (fun index => (supplied index).map liftValue.{c, s, t, m, uc, vs, wt, ms}) =
        some (ULift.up substitution) ↔ scope.assemble? supplied = some substitution := by
  constructor
  · intro checked
    apply (ScopeData.assemble?_eq_some_iff scope supplied substitution).mpr
    intro index
    have read := (ScopeData.assemble?_eq_some_iff
      (liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope) _
      (ULift.up substitution)).mp checked index
    rw [liftScopeData_components] at read
    apply liftValue_option_injective
    exact read
  · intro checked
    apply (ScopeData.assemble?_eq_some_iff
      (liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope) _
      (ULift.up substitution)).mpr
    intro index
    rw [(ScopeData.assemble?_eq_some_iff scope supplied substitution).mp checked index]
    exact congrArg some (liftScopeData_components scope substitution index).symm

theorem liftScopeData_assemble {n : Nat} {source target : C.toCwf.Ctx}
    (scope : ScopeData C doctrine assumptions n target)
    (supplied : Fin n → Option (Value C.toCwf source)) :
    (liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).assemble?
      (fun index => (supplied index).map liftValue.{c, s, t, m, uc, vs, wt, ms}) =
        (scope.assemble? supplied).map ULift.up := by
  cases original : scope.assemble? supplied with
  | some substitution =>
      exact (liftScopeData_assemble_eq_some_iff scope supplied substitution).mpr original
  | none =>
      cases raised : (liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).assemble?
          (fun index => (supplied index).map liftValue.{c, s, t, m, uc, vs, wt, ms}) with
      | none => rfl
      | some substitution =>
          cases substitution with
          | up substitution =>
              have impossible := (liftScopeData_assemble_eq_some_iff scope supplied substitution).mp raised
              rw [original] at impossible
              cases impossible

theorem assembly_readout {n : Nat} {source target : C.toCwf.Ctx}
    (scope : ScopeData C doctrine assumptions n target)
    (supplied : Fin n → Option (Value C.toCwf source)) :
    ((liftScopeData.{c, s, t, m, p, uc, vs, wt, ms, ps} scope).assemble?
      (fun index => (supplied index).map liftValue.{c, s, t, m, uc, vs, wt, ms})).map ULift.down =
        scope.assemble? supplied := by
  rw [liftScopeData_assemble]
  cases scope.assemble? supplied <;> rfl

end Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift
