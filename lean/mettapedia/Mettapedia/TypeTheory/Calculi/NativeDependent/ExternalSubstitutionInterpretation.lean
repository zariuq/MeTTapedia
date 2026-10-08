import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalRenamingEvaluation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalBinderSubstitution

/-!
# Actual model substitutions for external expressions

A substitution is realized by evaluating its authored components to the
readouts of one actual model arrow. The evaluator's argument checker earns
the equivalence with this local qualification. Binder lifting evaluates
older components after actual weakening and supplies the new generic
section.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}} {n k : Nat}

/-- Component evaluation is a local readout condition, not a source
soundness or preservation theorem. -/
structure ModelSubstitution (model : ModelData S C) (Γ : Context C k) (Δ : Context C n)
    (substitution : Substitution S n k) where
  arrow : C.toCwf.Sub Γ.1 Δ.1
  readout : ∀ index, model.evaluateTerm Γ (substitution index) =
    some ((Δ.2.lookup index).substitute arrow)

namespace ModelSubstitution

def identity (model : ModelData S C) (Γ : Context C n) : ModelSubstitution model Γ Γ TermExpr.var where
  arrow := C.toCwf.idS Γ.1
  readout index := by simp only [ModelData.evaluateTerm, Value.substitute_identity]

def ofEvaluated (model : ModelData S C) (Γ : Context C k) (Δ : Context C n)
    (substitution : Substitution S n k) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (evaluated : model.evaluateSubstitution Γ Δ substitution = some arrow) :
    ModelSubstitution model Γ Δ substitution where
  arrow := arrow
  readout := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp evaluated

theorem evaluate {model : ModelData S C} {Γ : Context C k} {Δ : Context C n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution) :
    model.evaluateSubstitution Γ Δ substitution = some modelMap.arrow :=
  (model.evaluateSubstitution_eq_some_iff _ _ _ _).mpr modelMap.readout

def lift {model : ModelData S C} {Γ : Context C k} {Δ : Context C n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (stable : StrictPiSubstitution model.products) (A : C.toCwf.Ty Δ.1) :
    ModelSubstitution model (Γ.snoc (C.toCwf.tySub A modelMap.arrow)) (Δ.snoc A)
      (liftSubstitution substitution) where
  arrow := TypeOver.extensionSubstitution modelMap.arrow A
  readout index := by
    cases index using Fin.cases with
    | zero =>
        simp only [liftSubstitution_zero, ModelData.evaluateTerm, Telescope.variable_zero]
        apply congrArg some
        apply Sigma.ext
        · change C.toCwf.tySub (C.toCwf.tySub A modelMap.arrow)
            (C.toCwf.wk (C.toCwf.tySub A modelMap.arrow)) =
              C.toCwf.tySub (C.toCwf.tySub A (C.toCwf.wk A))
                (TypeOver.extensionSubstitution modelMap.arrow A)
          symm
          rw [← C.toCwf.tySub_comp, TypeOver.wk_extensionSubstitution, C.toCwf.tySub_comp]
        · exact (TypeOver.vz_extensionSubstitution modelMap.arrow A).symm
    | succ index =>
        simp only [liftSubstitution_succ]
        have weakened := model.evaluateTerm_rename stable (substitution index)
          (Γ.snoc (C.toCwf.tySub A modelMap.arrow)) Γ Fin.succ
          (ModelRenaming.weaken Γ _) _ (modelMap.readout index)
        rw [Telescope.variable_succ, ← Value.substitute_composition,
          TypeOver.wk_extensionSubstitution]
        simpa only [ModelRenaming.weaken, ← Value.substitute_composition] using weakened

def liftAlong {model : ModelData S C} {Γ : Context C k} {Δ : Context C n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (stable : StrictPiSubstitution model.products) (A : C.toCwf.Ty Δ.1)
    (A' : C.toCwf.Ty Γ.1) (equal : C.toCwf.tySub A modelMap.arrow = A') :
    ModelSubstitution model (Γ.snoc A') (Δ.snoc A) (liftSubstitution substitution) :=
  equal ▸ modelMap.lift stable A

theorem liftAlong_arrow {model : ModelData S C} {Γ : Context C k} {Δ : Context C n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (stable : StrictPiSubstitution model.products) (A : C.toCwf.Ty Δ.1)
    (A' : C.toCwf.Ty Γ.1) (equal : C.toCwf.tySub A modelMap.arrow = A') :
    (modelMap.liftAlong stable A A' equal).arrow =
      C.toCwf.compS (TypeOver.extensionSubstitution modelMap.arrow A)
        (TypeOver.isoOfValEq (C := C.toCwf)
          (A := ⟨A'⟩) (B := ⟨C.toCwf.tySub A modelMap.arrow⟩) equal.symm).hom.substitution := by
  cases equal
  exact (C.toCwf.comp_id _).symm

theorem arrow_unique {model : ModelData S C} {Γ : Context C k} {Δ : Context C n}
    {substitution : Substitution S n k} (first second : ModelSubstitution model Γ Δ substitution) :
    first.arrow = second.arrow :=
  Option.some.inj (first.evaluate.symm.trans second.evaluate)

end ModelSubstitution

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
