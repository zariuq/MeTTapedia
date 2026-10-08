import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalPresentation
import Mettapedia.OSLF.Syntax.BindingClosedGeneratedEquations

/-!
# Binding operations inside the actual all-arity operational guest

The constructor inclusion into the rule-extended internal category determines
all target operations. Its structural schemas follow by mapping the original
authored declarations, rather than by supplying an operational model's laws.
The process-object comparison reaches the actual rule guest's category vertex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open Mettapedia.OSLF.Binding

universe k

abbrev Target := Object BindingClosedGeneratedOperational.signature.{k}

def ruleInclusion :=
  (RelativeClosedInternalCategory.RulePresentation.arrowInclusion
    BindingClosedGeneratedOperational.vertex BindingClosedGeneratedOperational.categoryMap
    BindingClosedGeneratedOperational.declaration).compose
      (RelativeClosedInternalCategory.RulePresentation.equationInclusion
        BindingClosedGeneratedOperational.vertex BindingClosedGeneratedOperational.categoryMap
        BindingClosedGeneratedOperational.declaration)

def ruleMap : Mettapedia.GSLT.Core.LambdaTheoryMap
    (Mettapedia.GSLT.Core.LambdaTheory.ofCategory BindingClosedGeneratedOperational.CategoryGuest.{k})
    BindingClosedGeneratedOperational.theory where
  functor := ruleInclusion.functor
  preservesFiniteLimits := SignatureMap.functor_preservesFiniteLimits ruleInclusion
  preservesExponentials := SignatureMap.functor_closed ruleInclusion

def constructors : Object (ClosedPresentation.signature.{k} AllArity.sig) ⥤ Target.{k} :=
  (BindingClosedGenerated.inclusion.functor ⋙ BindingClosedGeneratedOperational.base.functor) ⋙
    ruleMap.functor

instance constructors_finite : PreservesFiniteLimits constructors.{k} := by
  let : PreservesFiniteLimits BindingClosedGeneratedOperational.constructors.{k} :=
    BindingClosedGeneratedOperational.constructors_finite
  let : PreservesFiniteLimits ruleMap.{k}.functor := ruleMap.preservesFiniteLimits
  exact Limits.comp_preservesFiniteLimits BindingClosedGeneratedOperational.constructors ruleMap.functor

instance constructors_closed : MonoidalClosedFunctor constructors.{k} := by
  let : MonoidalClosedFunctor BindingClosedGeneratedOperational.constructors.{k} :=
    BindingClosedGeneratedOperational.constructors_closed
  let : MonoidalClosedFunctor ruleMap.{k}.functor := ruleMap.preservesExponentials
  exact Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition
    BindingClosedGeneratedOperational.constructors ruleMap.functor

def binding : ClosedPresentation.Operations AllArity.sig Target.{k} :=
  ClosedPresentation.GeneratedModel.operations (binding := AllArity.sig) constructors

def constructorComparison : constructors.{k} ≅ binding.interpretation.functor :=
  ClosedPresentation.GeneratedModel.comparison (binding := AllArity.sig) constructors

theorem structural_schemas : binding.{k}.model.SchemaFamilySatisfaction AllArity.equations := by
  intro origin
  apply (ClosedPresentation.GeneratedModel.schema_eq_iff (binding := AllArity.sig) constructors
    (AllArity.equations.get origin).lhs (AllArity.equations.get origin).rhs).mp
  exact congrArg (fun arrow => ruleMap.functor.map
    (BindingClosedGeneratedOperational.base.functor.map arrow))
      (ClosedPresentation.SchemaEquations.authored_equation AllArity.sig
        BindingClosedGenerated.equationMetas BindingClosedGenerated.equation (ULift.up origin))

theorem complete_structural_values (origin : Fin AllArity.equations.length) (stage : Target.{k})
    (parameters : stage ⟶ binding.family AllArity.structuralMetas)
    (environment : binding.model.Env stage (AllArity.equations.get origin).ctx) :
    (binding.model.interp AllArity.structuralMetas (AllArity.equations.get origin).lhs).value
        stage parameters environment =
      (binding.model.interp AllArity.structuralMetas (AllArity.equations.get origin).rhs).value
        stage parameters environment :=
  congrArg (fun body => body.value stage parameters environment) (structural_schemas origin)

def ordinary := BindingClosedPrimitiveOperations.continuation binding.{k}

def category : InternalCategory Target.{k} := BindingClosedGeneratedOperational.category

def processComparison : ordinary.{k}.processes ≅ category.vertex :=
  eqToIso (RelativeClosedInternalCategory.RulePresentation.programs_read
    BindingClosedGeneratedOperational.vertex BindingClosedGeneratedOperational.categoryMap
    BindingClosedGeneratedOperational.declaration)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalModel
