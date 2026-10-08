import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorSyntax

/-!
# Complete open-term readout through the closed constructor map

The categorical continuation semantics is constructed independently from
the raw encoder. It interprets ordered mixed contexts, every variable position
and all five constructors using the target category's real product and
function objects. The independent structural evaluator is then shown to read
every encoded tree as that complete semantic arrow. Consequently the actual
classifying map has the same whole arrow, including its interpreted endpoints.

This joins binding constructor syntax to its closed finite-limit completion.
It does not turn operational beta/fetch into equality or provide an internal
category of rewrites.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations NamePassingConstructorClassifying

universe u v

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

def sortValue (operations : Operations C) : NamePassing.Presentation.Srt → C
  | .nm => operations.names
  | .tm => operations.termObject

def contextValue (operations : Operations C) : Ctx NamePassing.Presentation.signature → C
  | [] => 𝟙_ C
  | sort :: context => sortValue operations sort ⊗ contextValue operations context

def projection (operations : Operations C) :
    {context : Ctx NamePassing.Presentation.signature} → {sort : NamePassing.Presentation.Srt} →
    Var context sort → (contextValue operations context ⟶ sortValue operations sort)
  | _ :: context, _, .zero => CartesianMonoidalCategory.fst _ (contextValue operations context)
  | old :: context, _, .succ position =>
      CartesianMonoidalCategory.snd (sortValue operations old) (contextValue operations context) ≫
        projection operations position

def nameMeaning (operations : Operations C) {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Name context) : contextValue operations context ⟶ operations.names :=
  projection operations (NamePassing.Presentation.nameVariable term)

def boundMeaning (operations : Operations C) {context : Ctx NamePassing.Presentation.signature}
    (body : operations.names ⊗ contextValue operations context ⟶ operations.termObject) :
    contextValue operations context ⟶ operations.boundBodyObject :=
  Interpretation.abstraction
    (Interpretation.exchange (contextValue operations context) operations.names ≫ body)

def meaning (operations : Operations C) : {context : Ctx NamePassing.Presentation.signature} →
    NamePassing.Presentation.Program context → (contextValue operations context ⟶ operations.termObject)
  | _, .var position => projection operations position
  | _, .op .reference (.cons reference .nil) => nameMeaning operations reference ≫ operations.reference
  | _, .op .abstraction (.cons body .nil) => boundMeaning operations (meaning operations body) ≫ operations.abstraction
  | _, .op .application (.cons function (.cons argument .nil)) =>
      CartesianMonoidalCategory.lift (meaning operations function) (nameMeaning operations argument) ≫
        operations.application
  | _, .op .definition (.cons value (.cons body .nil)) =>
      CartesianMonoidalCategory.lift (meaning operations value) (boundMeaning operations (meaning operations body)) ≫
        operations.definition
  | _, .op .carrier (.cons reference (.cons value (.cons body .nil))) =>
      CartesianMonoidalCategory.lift (nameMeaning operations reference)
        (CartesianMonoidalCategory.lift (meaning operations value) (meaning operations body)) ≫ operations.carrier
termination_by _ term => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

variable (operations : Operations C)

theorem sort_read (sort : NamePassing.Presentation.Srt) :
    (assignment operations).evaluateObject (NamePassingConstructorSyntax.sortObject.{v} sort).code =
      some (sortValue operations sort) := by
  cases sort <;> rfl

theorem context_read (context : Ctx NamePassing.Presentation.signature) :
    (assignment operations).evaluateObject (NamePassingConstructorSyntax.contextObject.{v} context).code =
      some (contextValue operations context) := by
  induction context with
  | nil => rfl
  | cons sort context ih => exact (assignment operations).evaluate_product (sort_read operations sort) ih

theorem projection_read {context : Ctx NamePassing.Presentation.signature}
    {sort : NamePassing.Presentation.Srt} (position : Var context sort) :
    (assignment operations).evaluateArrow (NamePassingConstructorSyntax.projection.{v} position).code =
      some (⟨contextValue operations context, sortValue operations sort,
        projection operations position⟩ : Interpretation.ArrowValue C) := by
  induction position with
  | @zero context sort =>
      exact (assignment operations).evaluate_first (sort_read operations sort) (context_read operations context)
  | @succ context sort old position ih =>
      exact (assignment operations).evaluate_compose _ _
        ((assignment operations).evaluate_second (sort_read operations old) (context_read operations context)) ih

theorem name_read {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Name context) :
    (assignment operations).evaluateArrow (NamePassingConstructorSyntax.name.{v} term).code =
      some (⟨contextValue operations context, operations.names,
        nameMeaning operations term⟩ : Interpretation.ArrowValue C) :=
  projection_read operations (NamePassing.Presentation.nameVariable term)

theorem exchange_read (context : Ctx NamePassing.Presentation.signature) :
    (assignment operations).evaluateArrow
        (NamePassingConstructorSyntax.exchange (NamePassingConstructorSyntax.contextObject.{v} context) nameObject).code =
      some (⟨contextValue operations context ⊗ operations.names,
        operations.names ⊗ contextValue operations context,
        Interpretation.exchange (contextValue operations context) operations.names⟩ : Interpretation.ArrowValue C) :=
  (assignment operations).evaluate_pair _ _
    ((assignment operations).evaluate_second (context_read operations context) (sort_read operations .nm))
    ((assignment operations).evaluate_first (context_read operations context) (sort_read operations .nm))

theorem bound_read {context : Ctx NamePassing.Presentation.signature}
    (raw : GeneratedCategory.RawHom (NamePassingConstructorSyntax.contextObject.{v} (.nm :: context)) termObject)
    (body : operations.names ⊗ contextValue operations context ⟶ operations.termObject)
    (read : (assignment operations).evaluateArrow raw.code =
      some (⟨operations.names ⊗ contextValue operations context, operations.termObject, body⟩ : Interpretation.ArrowValue C)) :
    (assignment operations).evaluateArrow (NamePassingConstructorSyntax.bindReference raw).code =
      some (⟨contextValue operations context, operations.boundBodyObject,
        boundMeaning operations body⟩ : Interpretation.ArrowValue C) :=
  (assignment operations).evaluate_abstraction _ (context_read operations context)
    (sort_read operations .nm) (sort_read operations .tm)
    ((assignment operations).evaluate_compose _ _ (exchange_read operations context) read)

theorem constructor_read (constructor : Constructor) :
    (assignment operations).evaluateArrow (constructorArrow.{v} constructor).code =
      some (constructorValue operations constructor) := rfl

theorem meaning_read : {context : Ctx NamePassing.Presentation.signature} →
    (term : NamePassing.Presentation.Program context) →
    (assignment operations).evaluateArrow (NamePassingConstructorSyntax.encode.{v} term).code =
      some (⟨contextValue operations context, operations.termObject,
        meaning operations term⟩ : Interpretation.ArrowValue C)
  | _, .var position => by
      simpa only [NamePassingConstructorSyntax.encode, meaning, sortValue] using
        projection_read operations position
  | _, .op .reference (.cons reference .nil) => by
      simp only [NamePassingConstructorSyntax.encode, meaning]
      exact (assignment operations).evaluate_compose _ _ (name_read operations reference) (constructor_read operations .reference)
  | _, .op .abstraction (.cons body .nil) => by
      simp only [NamePassingConstructorSyntax.encode, meaning]
      exact (assignment operations).evaluate_compose _ _
        (bound_read operations _ _ (meaning_read body)) (constructor_read operations .abstraction)
  | _, .op .application (.cons function (.cons argument .nil)) => by
      simp only [NamePassingConstructorSyntax.encode, meaning]
      exact (assignment operations).evaluate_compose _ _
        ((assignment operations).evaluate_pair _ _ (meaning_read function) (name_read operations argument))
        (constructor_read operations .application)
  | _, .op .definition (.cons value (.cons body .nil)) => by
      simp only [NamePassingConstructorSyntax.encode, meaning]
      exact (assignment operations).evaluate_compose _ _
        ((assignment operations).evaluate_pair _ _ (meaning_read value)
          (bound_read operations _ _ (meaning_read body))) (constructor_read operations .definition)
  | _, .op .carrier (.cons reference (.cons value (.cons body .nil))) => by
      simp only [NamePassingConstructorSyntax.encode, meaning]
      exact (assignment operations).evaluate_compose _ _
        ((assignment operations).evaluate_pair _ _ (name_read operations reference)
          ((assignment operations).evaluate_pair _ _ (meaning_read value) (meaning_read body)))
        (constructor_read operations .carrier)
termination_by _ term => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem complete_open_term_readout {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context) :
    (⟨(constructorMap operations).functor.obj (NamePassingConstructorSyntax.contextObject.{v} context),
      (constructorMap operations).functor.obj termObject,
      (constructorMap operations).functor.map (NamePassingConstructorSyntax.arrow term)⟩ : Interpretation.ArrowValue C) =
      ⟨contextValue operations context, operations.termObject, meaning operations term⟩ := by
  have whole := Interpretation.functor_complete_readout (assignment operations) (realization operations)
    (NamePassingConstructorSyntax.encode term)
  exact Option.some.inj (whole.symm.trans (meaning_read operations term))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorInterpretation
