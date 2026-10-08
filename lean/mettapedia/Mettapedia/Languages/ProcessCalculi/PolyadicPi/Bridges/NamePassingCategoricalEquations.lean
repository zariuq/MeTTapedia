import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompilerReadout

/-!
# Source static equations in the genuine target categorical model

Every point of the mixed categorical context has a supplied raw environment
representative, including complete function sections for program variables.
The authored static scope laws therefore yield equality of the entire
categorical arrows, rather than equality only on selected calls.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.Languages.LambdaCalculus
open NamePassingOpenInterpretation NamePassingConstructorInterpretation

theorem rawPoint_surjective {target : Ctx sig} {sort : Srt}
    (point : (programs algebra sort).obj (stage target)) :
    ∃ term : Term sig target sort, rawPoint term = point := by
  refine ⟨Quotient.out (programsAtEquiv algebra sort (stage target) point), ?_⟩
  apply (programsAtEquiv algebra sort (stage target)).injective
  rw [rawPoint_readout]
  exact Quotient.out_eq _

theorem rawBody_surjective {target : Ctx sig} (point : operations.termObject.obj (stage target)) :
    ∃ body : Proc (.nm :: target), rawBody body = point := by
  refine ⟨Quotient.out (scopedBodyEquiv algebra (stage target).unop [.nm] .pr point), ?_⟩
  apply (scopedBodyEquiv algebra (stage target).unop [.nm] .pr).injective
  rw [rawBody_readout]
  exact Quotient.out_eq _

/-- All categorical context points are covered by the independently typed
raw environment. Choice is used only for raw representatives of already
supplied equation classes. -/
theorem contextPoint_surjective : ∀ (context : Ctx NamePassing.Presentation.signature) (target : Ctx sig)
    (point : (contextValue operations context).obj (stage target)),
    ∃ environment : Environment context target, contextPoint environment = point
  | [], target, point => by
      let empty : Environment [] target := {
        name := fun position => nomatch position
        program := fun position => nomatch position }
      refine ⟨empty, ?_⟩
      cases point
      rfl
  | .nm :: context, target, point => by
      obtain ⟨name, named⟩ := rawPoint_surjective point.1
      obtain ⟨environment, represented⟩ := contextPoint_surjective context target point.2
      refine ⟨extendName environment name, ?_⟩
      rw [contextPoint_extendName, named, represented]
      rfl
  | .tm :: context, target, point => by
      obtain ⟨body, supplied⟩ := rawBody_surjective point.1
      obtain ⟨environment, represented⟩ := contextPoint_surjective context target point.2
      let extended : Environment (.tm :: context) target :=
        ⟨fun position => match position with | .succ old => environment.name old,
          fun position => match position with | .zero => body | .succ old => environment.program old⟩
      refine ⟨extended, ?_⟩
      change (rawBody body, contextPoint environment) = point
      rw [supplied, represented]
      rfl

theorem world_stage (world : Base) : stage world.unop.context = world := by
  cases world
  rename_i world
  cases world
  rfl

/-- An actual source static derivation identifies complete return functions
at every supplied raw environment, not merely their current returns. -/
theorem static_function {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    {first second : NamePassing.Presentation.Program context}
    (equal : NamePassing.Presentation.StaticEq first second) (environment : Environment context target) :
    (meaning operations first).app (stage target) (contextPoint environment) =
      (meaning operations second).app (stage target) (contextPoint environment) := by
  apply (scopedBodyEquiv algebra (stage target).unop [.nm] .pr).injective
  rw [whole_body_readout, whole_body_readout]
  exact Quotient.sound ((AuthoredEquations.eqClosure_iff_structuralEq _ _).mpr
    (static_preserved equal (environment.substitute weakening) (.var .zero)))

/-- The concrete communication algebra is a genuine categorical model of
every authored static equation, over every world and entire mixed context. -/
theorem static_arrow {context : Ctx NamePassing.Presentation.signature}
    {first second : NamePassing.Presentation.Program context}
    (equal : NamePassing.Presentation.StaticEq first second) :
    meaning operations first = meaning operations second := by
  apply NatTrans.ext
  funext world
  have worldEqual := world_stage world
  rw [← worldEqual]
  apply ConcreteCategory.hom_ext
  intro point
  obtain ⟨environment, represented⟩ := contextPoint_surjective context world.unop.context point
  rw [← represented]
  exact static_function equal environment

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler
