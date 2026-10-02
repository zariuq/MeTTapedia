import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetLaterArguments
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ExplicitDefinitions

/-!
# An explicit definition has a set model

A constant defined by one equation over a telescope of arguments, without recursion
(`explicitEquation`), is read as the value of its body abstracted over the arguments: the
traced graph of the body's values over the telescope (`ev_lams`). The equation holds in the
model because that graph applied to the values of the arguments is the body's value
(`explicitEquation_valid`, by `teleApply_teleGraph`).

**The theorem** (`explicit_setModel`): a package with a set model at every assignment that
agrees with a base assignment on the names it declares, extended by an explicit definition
whose context of arguments is formed, whose result type is a type there and whose body has
it, has a set model at every assignment that agrees, on the names it declares, with the base
assignment extended by that value. So explicit definitions, declared datatypes and
definitions by recursion can follow one another. Consistency:
`explicit_no_closed_inhabitant`.

Negative example: an equation whose right side mentions the constant is not of this form,
since the body of an explicit definition is typed before the constant is declared; the
constant `bad` with `bad ⟶ suc bad` of the executable model of the candidate
(`ObjectAppendByEquations.lean`) has no set model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (LevelModel)
open Mettapedia.Logic.HOL.Embedding
open UniverseLevel (LevelOrder)

universe u

variable {Head : Type} {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}} {m : Nat}
  {f : DeclName} {Ξ : CTele Head 0 m} {C body : CTm Head m}

/-- **The equation of an explicit definition holds in the model** in which the constant is
the value of the body abstracted over the arguments. -/
theorem explicitEquation_valid (value : consts f = ev heads consts (Ξ.lams body) Fin.elim0)
    (η : Env.{u} m) (sat : Sat heads consts (Ξ.extend .nil) η) :
    ev heads consts (Ξ.etaBody (.const f)) η = ev heads consts body η := by
  obtain ⟨-, satTele⟩ := (sat_extend heads consts Ξ .nil η).mp sat
  have dropped : (Fin.elim0 : Env.{u} 0) = teleDrop Ξ η := funext fun i => i.elim0
  rw [ev_etaBody]
  show teleApply Ξ (consts f) η = _
  rw [value, ev_lams, dropped, teleApply_teleGraph heads consts Ξ _ η satTele]

variable {R : Rules Head} {base : DeclName → ZFSet.{u}} {L : Type} [LevelOrder L]

/-- **A package extended by an explicit definition has a set model.** The package before the
definition has a set model at every assignment that agrees with the base assignment on the
names it declares; the defined name is new to it; the context of the arguments is formed, the
result type is a type there, and the body has it. The model is at every assignment that
agrees, on the names the package with the definition declares, with the base assignment
extended by the value of the body abstracted over the arguments. -/
theorem explicit_setModel (levels : LevelModel R L) (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (formed : CCtxFormed B (Ξ.extend .nil))
    (resultType : CIsType B (Ξ.extend .nil) C) (typed : CTyped B (Ξ.extend .nil) body C)
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withDefinition B f (Ξ.pis C) [explicitEquation f Ξ body]).constantType c ≠
        none →
      consts c = Function.update base f (ev heads base (Ξ.lams body) Fin.elim0) c) :
    SetModel heads consts (withDefinition B f (Ξ.pis C) [explicitEquation f Ξ body]) := by
  have witness : CTyped B .nil (Ξ.lams body) (Ξ.pis C) :=
    explicitWitness_typed levels formed resultType typed
  refine definition_setModel_of_value B baseModel new _
    (fun consts agreesBase _ => ?_) (fun consts agreesBase atDefined e member η sat => ?_)
    consts agrees
  · have same : ev heads consts (Ξ.lams body) Fin.elim0 = ev heads base (Ξ.lams body) Fin.elim0 :=
      CDerivable.ev_congr_declared heads agreesBase witness Fin.elim0
    rw [← same]
    exact CDerivable.sound (baseModel consts agreesBase) witness Fin.elim0
      (sat_nil heads consts Fin.elim0)
  · obtain rfl := List.mem_singleton.mp member
    have same : ev heads consts (Ξ.lams body) Fin.elim0 = ev heads base (Ξ.lams body) Fin.elim0 :=
      CDerivable.ev_congr_declared heads agreesBase witness Fin.elim0
    exact explicitEquation_valid (atDefined.trans same.symm) η sat

/-- **Consistency**: a closed type whose set is empty has no closed term in a package
extended by an explicit definition. -/
theorem explicit_no_closed_inhabitant (levels : LevelModel R L) (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (formed : CCtxFormed B (Ξ.extend .nil))
    (resultType : CIsType B (Ξ.extend .nil) C) (typed : CTyped B (Ξ.extend .nil) body C)
    {A : CTm Head 0}
    (empty : ∀ z, z ∉ ev heads
      (Function.update base f (ev heads base (Ξ.lams body) Fin.elim0)) A Fin.elim0)
    (t : CTm Head 0) :
    ¬ CTyped (withDefinition B f (Ξ.pis C) [explicitEquation f Ξ body]) .nil t A :=
  CDerivable.no_closed_inhabitant
    (explicit_setModel levels B baseModel new formed resultType typed _ fun _ _ => rfl) empty t

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
