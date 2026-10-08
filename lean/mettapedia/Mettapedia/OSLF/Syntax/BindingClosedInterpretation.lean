import Mettapedia.OSLF.Syntax.BindingClosedPresentation
import Mettapedia.OSLF.Syntax.CategoricalBindingModel

/-!
# Interpretation of generated binding headers in arbitrary closed targets

A target supplies only its sort objects and primitive operator arrows, with
their complete ordered argument and binder function domains. The partial
structural evaluator independently computes every header. Those computations
earn the local realization and the actual finite-limit and closed functor.

Target object and hom universes remain independent. The same primitive data
also supplies the existing categorical binding model; its whole-term action
is not assumed as a realization field.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open CategoricalBindingModel

universe u v

variable (binding : Mettapedia.OSLF.Binding.Signature)
variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

structure Operations where
  sort : binding.Srt → C
  operation : ∀ {result : binding.Srt} (operator : binding.Op result),
    familyOf (fun context result => contextOf sort context ⟶[C] sort result)
      (binding.arity operator) ⟶ sort result

variable {binding C}
variable [HasFiniteLimits C]

namespace Operations

variable (operations : Operations binding C)

def context (scope : Ctx binding) : C := contextOf operations.sort scope

def power (binders : Ctx binding) (result : binding.Srt) : C :=
  operations.context binders ⟶[C] operations.sort result

def family (arities : List (Ctx binding × binding.Srt)) : C := familyOf operations.power arities

private def emptyBase : Base.{v} ⥤ C where
  obj object := isEmptyElim object
  map {source} _ := isEmptyElim source
  map_id object := isEmptyElim object
  map_comp {source} _ _ := isEmptyElim source

def primitiveValue (origin : Sigma binding.Op) : Interpretation.ArrowValue C :=
  ⟨operations.family (binding.arity origin.2), operations.sort origin.1, operations.operation origin.2⟩

def assignment : Interpretation.Assignment Base.{v} (symbols.{v} binding) C where
  base := emptyBase
  object origin := operations.sort origin.down
  arrow origin := operations.primitiveValue origin.down

theorem sort_read (sort : binding.Srt) :
    operations.assignment.evaluateObject (sortCode binding sort) = some (operations.sort sort) := rfl

theorem context_read (scope : Ctx binding) :
    operations.assignment.evaluateObject (contextCode binding scope) = some (operations.context scope) := by
  induction scope with
  | nil => rfl
  | cons sort scope inductionHypothesis =>
      exact operations.assignment.evaluate_product (operations.sort_read sort) inductionHypothesis

theorem power_read (binders : Ctx binding) (sort : binding.Srt) :
    operations.assignment.evaluateObject (powerCode binding binders sort) = some (operations.power binders sort) :=
  operations.assignment.evaluate_exponential (operations.context_read binders) (operations.sort_read sort)

theorem family_read (arities : List (Ctx binding × binding.Srt)) :
    operations.assignment.evaluateObject (familyCode binding arities) = some (operations.family arities) := by
  induction arities with
  | nil => rfl
  | cons arity rest inductionHypothesis =>
      exact operations.assignment.evaluate_product (operations.power_read arity.1 arity.2) inductionHypothesis

theorem realization : Interpretation.Realization (signature.{v} binding) operations.assignment where
  source origin := operations.family_read (binding.arity origin.down.2)
  target origin := operations.sort_read origin.down.1
  equation origin := nomatch origin.down

set_option backward.isDefEq.respectTransparency false in
def interpretation :
    Mettapedia.GSLT.Core.LambdaTheoryMap (theory.{v} binding)
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory C) where
  functor := Interpretation.functor operations.assignment operations.realization
  preservesFiniteLimits := Interpretation.functor_preservesFiniteLimits operations.assignment operations.realization
  preservesExponentials := Interpretation.functor_closed operations.assignment operations.realization

theorem sort_object_readout (sort : binding.Srt) :
    operations.interpretation.functor.obj (sortObject.{v} binding sort) = operations.sort sort := by
  exact Interpretation.objectValue_unique operations.assignment operations.realization
    (sortObject binding sort) _ (operations.sort_read sort)

theorem context_object_readout (scope : Ctx binding) :
    operations.interpretation.functor.obj (contextObject.{v} binding scope) = operations.context scope := by
  exact Interpretation.objectValue_unique operations.assignment operations.realization
    (contextObject binding scope) _ (operations.context_read scope)

theorem power_object_readout (binders : Ctx binding) (sort : binding.Srt) :
    operations.interpretation.functor.obj (powerObject.{v} binding binders sort) = operations.power binders sort := by
  exact Interpretation.objectValue_unique operations.assignment operations.realization
    (powerObject binding binders sort) _ (operations.power_read binders sort)

theorem primitive_complete_readout (origin : Sigma binding.Op) :
    (⟨operations.interpretation.functor.obj (familyObject.{v} binding (binding.arity origin.2)),
      operations.interpretation.functor.obj (sortObject binding origin.1),
      operations.interpretation.functor.map (GeneratedCategory.classOf (operator binding origin.2))⟩ :
        Interpretation.ArrowValue C) = operations.primitiveValue origin := by
  have complete := Interpretation.functor_complete_readout operations.assignment operations.realization
    (operator binding origin.2)
  exact Option.some.inj complete.symm

def model : CategoricalBindingModel.Model binding C := ofClosed operations.sort operations.operation

end Operations

end Mettapedia.OSLF.Binding.ClosedPresentation
