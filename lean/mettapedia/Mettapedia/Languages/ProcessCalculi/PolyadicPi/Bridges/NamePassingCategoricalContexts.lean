import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler

/-!
# Mixed source environments in the actual pi function model

Each ordinary term variable supplies a complete return function. The ordered
mixed context product stores those functions beside actual name values.
Every variable position and ambient substitution is compared with the
independently authored raw environment; extending a source reference binder
retains all old values through the genuine exponential restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingOpenInterpretation NamePassingConstructorInterpretation

def tailEnvironment {sort : NamePassing.Presentation.Srt}
    {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment (sort :: context) target) : Environment context target where
  name := fun position => environment.name (.succ position)
  program := fun position => environment.program (.succ position)

def contextPoint : {context : Ctx NamePassing.Presentation.signature} → {target : Ctx sig} →
    Environment context target → (contextValue operations context).obj (stage target)
  | [], _, _ => PUnit.unit
  | .nm :: _, _, environment =>
      (rawPoint (environment.name .zero), contextPoint (tailEnvironment environment))
  | .tm :: _, _, environment =>
      (rawBody (environment.program .zero), contextPoint (tailEnvironment environment))

def variablePoint {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) : {sort : NamePassing.Presentation.Srt} →
    Var context sort → (sortValue operations sort).obj (stage target)
  | .nm, position => rawPoint (environment.name position)
  | .tm, position => rawBody (environment.program position)

/-- Every ordered variable position reads the exact independently supplied
name or complete program function at that position. -/
theorem projection_readout : ∀ {context : Ctx NamePassing.Presentation.signature}
    {target : Ctx sig} {sort : NamePassing.Presentation.Srt} (position : Var context sort)
    (environment : Environment context target),
    (projection operations position).app (stage target) (contextPoint environment) =
      variablePoint environment position
  | _, _, .nm, .zero, _ => rfl
  | _, _, .tm, .zero, _ => rfl
  | _, _, sort, @Var.succ _ _ _ previous old, environment => by
      cases previous <;> cases sort <;> exact projection_readout old (tailEnvironment environment)

theorem nameMeaning_readout {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (name : NamePassing.Presentation.Name context) (environment : Environment context target) :
    (nameMeaning operations name).app (stage target) (contextPoint environment) =
      rawPoint (interpretName name environment) :=
  projection_readout (NamePassing.Presentation.nameVariable name) environment

/-- Both the ordinary name block and each whole return function reindex
through the actual supplied simultaneous target substitution. -/
theorem contextPoint_substitution : ∀ {context : Ctx NamePassing.Presentation.signature}
    {target future : Ctx sig} (environment : Environment context target)
    (assigned : Sub sig target future),
    (contextValue operations context).map (rawChange assigned) (contextPoint environment) =
      contextPoint (environment.substitute assigned)
  | [], _, _, _, _ => rfl
  | .nm :: _, _, _, environment, assigned => by
      apply Prod.ext
      · exact rawPoint_substitution assigned (environment.name .zero)
      · exact contextPoint_substitution (tailEnvironment environment) assigned
  | .tm :: _, _, _, environment, assigned => by
      apply Prod.ext
      · exact rawBody_substitution assigned (environment.program .zero)
      · exact contextPoint_substitution (tailEnvironment environment) assigned

theorem tailEnvironment_lift {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) :
    tailEnvironment environment.lift = environment.substitute weakening := by
  apply Environment.ext
  · funext position
    exact (bind_var_eq_rename (fun _ position => Var.succ position) (environment.name position)).symm
  · rfl

/-- The newly available reference is exactly the new name projection. The
old context is restricted as a whole, including its retained return binders. -/
theorem contextPoint_lift {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) :
    contextPoint environment.lift =
      (rawPoint (Term.var .zero : Name (.nm :: target)),
        (contextValue operations context).map (rawChange weakening) (contextPoint environment)) := by
  change (rawPoint (Term.var .zero : Name (.nm :: target)),
      contextPoint (tailEnvironment environment.lift)) = _
  rw [tailEnvironment_lift, contextPoint_substitution]

def extendName {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) (name : Name target) : Environment (.nm :: context) target where
  name := fun position => match position with
    | .zero => name
    | .succ old => environment.name old
  program := fun position => match position with
    | .succ old => environment.program old

theorem contextPoint_extendName {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) (name : Name target) :
    contextPoint (extendName environment name) = (rawPoint name, contextPoint environment) := rfl

def scopeWeakening {context : Ctx sig} (scope : Ctx sig) : Sub sig context (scope ++ context) :=
  fun _ position => Term.var (weakenVar scope position)

/-- The canonical ambient projection at an extended context is represented
by the actual raw weakening of all its ordered variables. -/
theorem rawChange_scopeWeakening (context scope : Ctx sig) :
    rawChange (scopeWeakening (context := context) scope) =
      Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
        algebra.substitution.toClone
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
          algebra.substitution.toClone scope) (stage context).unop) := by
  apply congrArg Quiver.Hom.op
  funext position
  exact (MultiBinderPresheaf.rightProjection_as_var algebra scope context position).symm

theorem lift_as_extendName {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) :
    environment.lift = extendName (environment.substitute weakening) (.var .zero) := by
  apply Environment.ext
  · funext position
    cases position with
    | zero => rfl
    | succ old =>
        exact (bind_var_eq_rename (fun _ position => Var.succ position) (environment.name old)).symm
  · funext position
    cases position
    rfl

theorem double_weakening {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) :
    (environment.substitute weakening).substitute weakening =
      environment.substitute (scopeWeakening [Srt.nm, Srt.nm]) := by
  rw [Environment.substitute_composition]
  rfl

theorem abstraction_environment {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) :
    (environment.substitute weakening).lift =
      extendName (environment.substitute (scopeWeakening [Srt.nm, Srt.nm])) (.var .zero) := by
  rw [lift_as_extendName, double_weakening]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler
