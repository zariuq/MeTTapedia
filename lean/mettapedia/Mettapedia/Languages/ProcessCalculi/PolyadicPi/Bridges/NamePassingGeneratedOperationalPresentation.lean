import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingPrimitiveOperations
import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredOperationalProfile
import Mettapedia.OSLF.Syntax.BindingClosedAuthoredPresentation
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRulePresentation

/-!
# The independent five-rule source operational guest

The authored beta and fetch schemas supply their two complete static arrows.
The three active-position declarations instead take actual source evidence,
with the passive arguments retained separately. Definition takes a full
reference-bound evidence function and an unbound stored term. Carrier keeps
both its reference and stored term passive. These domains do not depend on a
continuation representation or an operational target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus

universe k

abbrev sourceBinding := NamePassing.Presentation.signature
abbrev staticSignature := ClosedPresentation.AuthoredPresentation.signature.{k}
  NamePassing.AuthoredEquations.equations
abbrev Static := Object staticSignature.{k}
abbrev staticInclusion := ClosedPresentation.AuthoredPresentation.inclusion.{k}
  NamePassing.AuthoredEquations.equations

def vertex : Static.{k} := staticInclusion.functor.obj (ClosedPresentation.sortObject sourceBinding .tm)
abbrev categorySignature := RelativeClosedInternalCategory.Presentation.nativeSignature vertex.{k}
abbrev categoryMap := RelativeClosedInternalCategory.Presentation.nativeInclusion vertex.{k}
abbrev CategoryGuest := Object categorySignature.{k}
def base := RelativeClosedInternalCategory.Presentation.baseMap vertex.{k}
def constructors := staticInclusion.functor ⋙ base.{k}.functor

instance constructors_finite : PreservesFiniteLimits constructors.{k} := comp_preservesFiniteLimits _ _
instance constructors_closed : MonoidalClosedFunctor constructors.{k} :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition _ _

def binding : ClosedPresentation.Operations sourceBinding CategoryGuest.{k} := by
  letI : PreservesFiniteLimits constructors.{k} := constructors_finite
  letI : MonoidalClosedFunctor constructors.{k} := constructors_closed
  exact ClosedPresentation.GeneratedModel.operations constructors

def names : CategoryGuest.{k} := NamePassingBindingPrimitiveOperations.names binding
def programs : CategoryGuest.{k} := RelativeClosedInternalCategory.NativeCategory.vertexObject vertex categoryMap
def edges : CategoryGuest.{k} := RelativeClosedInternalCategory.NativeCategory.edgeObject vertex categoryMap
def edgeSource : edges.{k} ⟶ programs := classOf (RelativeClosedInternalCategory.NativeCategory.source vertex categoryMap)
def edgeTarget : edges.{k} ⟶ programs := classOf (RelativeClosedInternalCategory.NativeCategory.target vertex categoryMap)

theorem programs_eq_terms : programs.{k} = NamePassingBindingPrimitiveOperations.terms binding := rfl

def application : programs.{k} ⊗ names ⟶ programs := NamePassingBindingPrimitiveOperations.application binding
def definition : programs.{k} ⊗ (names ⟶[CategoryGuest] programs) ⟶ programs :=
  NamePassingBindingPrimitiveOperations.definition binding
def carrier : names.{k} ⊗ (programs ⊗ programs) ⟶ programs := NamePassingBindingPrimitiveOperations.carrier binding

inductive Origin where
  | beta
  | fetch
  | application
  | definition
  | carrier
  deriving DecidableEq

def rootMetas : Bool → List (MetaArity sourceBinding)
  | false => NamePassing.AuthoredOperationalProfile.betaMetas
  | true => []

def rootContext : Bool → Ctx sourceBinding
  | false => NamePassing.AuthoredOperationalProfile.beta.conclusion.ctx
  | true => NamePassing.AuthoredOperationalProfile.fetch.conclusion.ctx

def rootBefore : (fetch : Bool) → Term (withMetas sourceBinding (rootMetas fetch)) (rootContext fetch) .tm
  | false => NamePassing.AuthoredOperationalProfile.beta.conclusion.lhs
  | true => NamePassing.AuthoredOperationalProfile.fetch.conclusion.lhs

def rootAfter : (fetch : Bool) → Term (withMetas sourceBinding (rootMetas fetch)) (rootContext fetch) .tm
  | false => NamePassing.AuthoredOperationalProfile.beta.conclusion.rhs
  | true => NamePassing.AuthoredOperationalProfile.fetch.conclusion.rhs

def rootStage (fetch : Bool) : Static.{k} := staticInclusion.functor.obj
  (ClosedPresentation.SchemaExpressions.genericStage sourceBinding (rootMetas fetch) (rootContext fetch))

def rootDeclaration (fetch : Bool) : RelativeClosedInternalCategory.RulePresentation.Declaration vertex.{k} categoryMap :=
  ⟨baseObject categorySignature (rootStage fetch),
    ⟨.base (staticInclusion.functor.map (classOf
      (ClosedPresentation.SchemaExpressions.expression sourceBinding (rootBefore fetch)))),
      ⟨.baseArrow _⟩⟩,
    ⟨.base (staticInclusion.functor.map (classOf
      (ClosedPresentation.SchemaExpressions.expression sourceBinding (rootAfter fetch)))),
      ⟨.baseArrow _⟩⟩⟩

def applicationEndpoint (side : Bool) : edges.{k} ⊗ names ⟶ programs :=
  lift (fst edges names ≫ if side then edgeTarget else edgeSource) (snd edges names) ≫ application

def definitionEndpoint (side : Bool) : programs.{k} ⊗ (names ⟶[CategoryGuest] edges) ⟶ programs :=
  lift (fst programs (names ⟶[CategoryGuest] edges))
    (snd programs (names ⟶[CategoryGuest] edges) ≫
      (ihom names).map (if side then edgeTarget else edgeSource)) ≫ definition

def carrierEndpoint (side : Bool) : names.{k} ⊗ (programs ⊗ edges) ⟶ programs :=
  lift (fst names (programs ⊗ edges))
    (lift (snd names (programs ⊗ edges) ≫ fst programs edges)
      (snd names (programs ⊗ edges) ≫ snd programs edges ≫
        if side then edgeTarget else edgeSource)) ≫ carrier

def declaration : ULift.{k} Origin → RelativeClosedInternalCategory.RulePresentation.Declaration vertex.{k} categoryMap
  | ⟨.beta⟩ => rootDeclaration false
  | ⟨.fetch⟩ => rootDeclaration true
  | ⟨.application⟩ => ⟨edges ⊗ names,representative (applicationEndpoint false),representative (applicationEndpoint true)⟩
  | ⟨.definition⟩ => ⟨programs ⊗ (names ⟶[CategoryGuest] edges),
      representative (definitionEndpoint false),representative (definitionEndpoint true)⟩
  | ⟨.carrier⟩ => ⟨names ⊗ (programs ⊗ edges),
      representative (carrierEndpoint false),representative (carrierEndpoint true)⟩

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

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalPresentation
