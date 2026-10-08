import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperations
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRulePresentation

/-!
# Independent all-arity pi operational evidence declarations

Every COMM arity uses the actual authored ordered schema and its complete
metavariable function object. Parallel and private closure have separate
edge domains, with their two program endpoints constructed from the actual
source/target maps and the independently generated pi operations.

The fresh evidence arrows and their endpoint equations are adjoined to the
genuine internal category presentation. They do not consult a runtime
firing, a source lambda term or a supplied rule-satisfaction theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperational

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open Mettapedia.OSLF.Binding

universe k

abbrev Static := BindingClosedGenerated.Guest.{k}
def vertex : Static.{k} := BindingClosedGenerated.processes
abbrev categorySignature := RelativeClosedInternalCategory.Presentation.nativeSignature vertex.{k}
abbrev categoryMap := RelativeClosedInternalCategory.Presentation.nativeInclusion vertex.{k}
abbrev CategoryGuest := Object categorySignature.{k}
def base := RelativeClosedInternalCategory.Presentation.baseMap vertex.{k}

def constructors := BindingClosedGenerated.inclusion.functor ⋙ base.functor

instance constructors_finite : PreservesFiniteLimits constructors.{k} :=
  Limits.comp_preservesFiniteLimits _ _

instance constructors_closed : MonoidalClosedFunctor constructors.{k} :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition _ _

def binding : ClosedPresentation.Operations AllArity.sig CategoryGuest.{k} := by
  letI : PreservesFiniteLimits constructors.{k} := constructors_finite
  letI : MonoidalClosedFunctor constructors.{k} := constructors_closed
  exact ClosedPresentation.GeneratedModel.operations (binding := AllArity.sig) constructors

def ordinary := BindingClosedPrimitiveOperations.continuation binding.{k}

def programs : CategoryGuest.{k} := RelativeClosedInternalCategory.NativeCategory.vertexObject vertex categoryMap
def edges : CategoryGuest.{k} := RelativeClosedInternalCategory.NativeCategory.edgeObject vertex categoryMap
def names : CategoryGuest.{k} := ordinary.names
def edgeSource : edges.{k} ⟶ programs := classOf (RelativeClosedInternalCategory.NativeCategory.source vertex categoryMap)
def edgeTarget : edges.{k} ⟶ programs := classOf (RelativeClosedInternalCategory.NativeCategory.target vertex categoryMap)

theorem programs_eq_ordinary : programs.{k} = ordinary.processes := rfl

def communicationStage (arity : Nat) : Static.{k} := BindingClosedGenerated.inclusion.functor.obj
  (ClosedPresentation.SchemaExpressions.genericStage.{k} AllArity.sig
    (AllArity.communicationMetas arity) (AllArity.comm arity).ctx)

def communicationBefore (arity : Nat) : communicationStage.{k} arity ⟶ vertex :=
  BindingClosedGenerated.inclusion.functor.map
    (classOf (ClosedPresentation.SchemaExpressions.expression AllArity.sig (AllArity.comm arity).lhs))

def communicationAfter (arity : Nat) : communicationStage.{k} arity ⟶ vertex :=
  BindingClosedGenerated.inclusion.functor.map
    (classOf (ClosedPresentation.SchemaExpressions.expression AllArity.sig (AllArity.comm arity).rhs))

inductive Origin where
  | communication (arity : Nat)
  | parallel
  | restriction
  deriving DecidableEq

def declaration : ULift.{k} Origin → RelativeClosedInternalCategory.RulePresentation.Declaration vertex categoryMap
  | ⟨.communication arity⟩ =>
      ⟨baseObject categorySignature (communicationStage arity),
        ⟨.base (communicationBefore arity),⟨.baseArrow (communicationBefore arity)⟩⟩,
        ⟨.base (communicationAfter arity),⟨.baseArrow (communicationAfter arity)⟩⟩⟩
  | ⟨.parallel⟩ =>
      ⟨edges ⊗ programs,
        representative (lift (fst _ _ ≫ edgeSource) (snd _ _) ≫ ordinary.parallel),
        representative (lift (fst _ _ ≫ edgeTarget) (snd _ _) ≫ ordinary.parallel)⟩
  | ⟨.restriction⟩ =>
      ⟨names ⟶[CategoryGuest] edges,
        representative ((ihom names).map edgeSource ≫ ordinary.fresh),
        representative ((ihom names).map edgeTarget ≫ ordinary.fresh)⟩

abbrev signature := RelativeClosedInternalCategory.RulePresentation.signature vertex categoryMap declaration.{k}
def headers : HeaderFormation signature.{k} := RelativeClosedInternalCategory.RulePresentation.headers
  vertex categoryMap declaration (RelativeClosedInternalCategory.Presentation.nativeHeaders vertex)
abbrev theory := Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object signature.{k})
abbrev category := RelativeClosedInternalCategory.RulePresentation.category vertex categoryMap declaration.{k}
abbrev fire := RelativeClosedInternalCategory.RulePresentation.fire vertex categoryMap declaration.{k}

theorem authored_source (origin : ULift.{k} Origin) :
    classOf ((fire origin).compose
      (RelativeClosedInternalCategory.RulePresentation.edgeSource vertex categoryMap declaration)) =
      classOf (RelativeClosedInternalCategory.RulePresentation.before vertex categoryMap declaration origin) :=
  RelativeClosedInternalCategory.RulePresentation.fire_source vertex categoryMap declaration origin

theorem authored_target (origin : ULift.{k} Origin) :
    classOf ((fire origin).compose
      (RelativeClosedInternalCategory.RulePresentation.edgeTarget vertex categoryMap declaration)) =
      classOf (RelativeClosedInternalCategory.RulePresentation.after vertex categoryMap declaration origin) :=
  RelativeClosedInternalCategory.RulePresentation.fire_target vertex categoryMap declaration origin

theorem complete_parallel_source : classOf (declaration.{k} ⟨.parallel⟩).before =
    lift (fst edges programs ≫ edgeSource) (snd edges programs) ≫ ordinary.parallel :=
  classOf_representative _

theorem complete_parallel_target : classOf (declaration.{k} ⟨.parallel⟩).after =
    lift (fst edges programs ≫ edgeTarget) (snd edges programs) ≫ ordinary.parallel :=
  classOf_representative _

theorem complete_private_source : classOf (declaration.{k} ⟨.restriction⟩).before =
    (ihom names).map edgeSource ≫ ordinary.fresh := classOf_representative _

theorem complete_private_target : classOf (declaration.{k} ⟨.restriction⟩).after =
    (ihom names).map edgeTarget ≫ ordinary.fresh := classOf_representative _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperational
