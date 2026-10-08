import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractRenamingEvaluation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementBinderSubstitution

/-!
# Actual substitutions between mixed semantic scopes

The supplied raw components evaluate to the variable readouts of one actual
map. Ordered checking also verifies every target assumption. Lifting supplies
the new generic section and weakens each older component through the real
dependent comprehension projection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations

universe a c s t m p

variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C} {n k : Nat}

/-- The qualification concerns the supplied components of one map. -/
structure ModelSubstitution (model : ModelData S C localModel) (Γ : ModelScope C localModel k) (Δ : ModelScope C localModel n)
    (substitution : Substitution S n k) where
  arrow : C.toCwf.Sub Γ.1 Δ.1
  readout : ∀ index, model.evaluateTerm Γ (substitution index) =
    some ((Δ.2.lookup index).substitute arrow)

namespace ModelSubstitution

attribute [local irreducible] TypeOver.extensionSubstitution

set_option backward.isDefEq.respectTransparency false in
def identity (model : ModelData S C localModel) (Γ : ModelScope C localModel n) :
    ModelSubstitution model Γ Γ TermExpr.var where
  arrow := C.toCwf.idS Γ.1
  readout index := by
    simp only [ModelData.evaluateTerm, ModelData.evaluateTermLift, Value.substitute_identity]

def ofEvaluated (model : ModelData S C localModel) (Γ : ModelScope C localModel k) (Δ : ModelScope C localModel n)
    (substitution : Substitution S n k) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (evaluated : model.evaluateSubstitution Γ Δ substitution = some arrow) :
    ModelSubstitution model Γ Δ substitution where
  arrow := arrow
  readout := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp evaluated

theorem evaluate {model : ModelData S C localModel} {Γ : ModelScope C localModel k} {Δ : ModelScope C localModel n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution) :
    model.evaluateSubstitution Γ Δ substitution = some modelMap.arrow :=
  (model.evaluateSubstitution_eq_some_iff _ _ _ _).mpr modelMap.readout

set_option backward.isDefEq.respectTransparency false in
def lift {model : ModelData S C localModel} {Γ : ModelScope C localModel k} {Δ : ModelScope C localModel n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (stable : StrictPiSubstitution localModel.products) (A : C.toCwf.Ty Δ.1) :
    ModelSubstitution model (Γ.snoc (C.toCwf.tySub A modelMap.arrow)) (Δ.snoc A)
      (liftSubstitution substitution) where
  arrow := TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A
  readout index := by
    cases index using Fin.cases with
    | zero =>
        simp only [liftSubstitution_zero, ModelData.evaluateTerm, ModelData.evaluateTermLift, ContextualPredicateModelScopes.ScopeData.lookup_zero]
        apply congrArg some
        apply Sigma.ext
        · change C.toCwf.tySub (C.toCwf.tySub A modelMap.arrow)
            (C.toCwf.wk (C.toCwf.tySub A modelMap.arrow)) =
              C.toCwf.tySub (C.toCwf.tySub A (C.toCwf.wk A))
                (TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A)
          symm
          rw [← C.toCwf.tySub_comp, TypeOver.wk_extensionSubstitution,
            C.toCwf.tySub_comp]
        · exact (TypeOver.vz_extensionSubstitution (C := C.toCwf)
            modelMap.arrow A).symm
    | succ index =>
        simp only [liftSubstitution_succ]
        have weakened := model.evaluateTerm_rename stable (substitution index)
          (Γ.snoc (C.toCwf.tySub A modelMap.arrow)) Γ Fin.succ
          (ModelRenaming.weaken Γ _) _ (modelMap.readout index)
        rw [ContextualPredicateModelScopes.ScopeData.lookup_succ, ← Value.substitute_composition,
          TypeOver.wk_extensionSubstitution]
        simpa only [ModelRenaming.weaken, ← Value.substitute_composition] using weakened

set_option backward.isDefEq.respectTransparency false in
def liftAlong {model : ModelData S C localModel} {Γ : ModelScope C localModel k} {Δ : ModelScope C localModel n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (stable : StrictPiSubstitution localModel.products) (A : C.toCwf.Ty Δ.1)
    (A' : C.toCwf.Ty Γ.1)
    (equal : C.toCwf.tySub A modelMap.arrow = A') :
    ModelSubstitution model (Γ.snoc A') (Δ.snoc A) (liftSubstitution substitution) :=
  equal ▸ modelMap.lift stable A

set_option backward.isDefEq.respectTransparency false in
theorem liftAlong_arrow {model : ModelData S C localModel} {Γ : ModelScope C localModel k} {Δ : ModelScope C localModel n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (stable : StrictPiSubstitution localModel.products) (A : C.toCwf.Ty Δ.1)
    (A' : C.toCwf.Ty Γ.1)
    (equal : C.toCwf.tySub A modelMap.arrow = A') :
    (modelMap.liftAlong stable A A' equal).arrow =
      C.toCwf.compS
        (TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A)
        (ContextualTypePresentationCast.extensionCast (K := C.toCwf) equal.symm) := by
  cases equal
  change TypeOver.extensionSubstitution (C := C.toCwf) modelMap.arrow A = _
  rw [ContextualTypePresentationCast.extensionCast_refl]
  exact (C.toCwf.comp_id _).symm

theorem arrow_unique {model : ModelData S C localModel} {Γ : ModelScope C localModel k} {Δ : ModelScope C localModel n}
    {substitution : Substitution S n k}
    (first second : ModelSubstitution model Γ Δ substitution) : first.arrow = second.arrow :=
  Option.some.inj (first.evaluate.symm.trans second.evaluate)

end ModelSubstitution

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
