import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredOperationalProfile
import Mettapedia.OSLF.Syntax.BindingClosedAuthoredPresentation
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRulePresentation

/-!
# Independent beta and environment-fetch evidence declarations

The original authored root schemas supply the complete function metadata,
ordinary context and both program expressions. Those expressions are encoded
in the static binding-equation theory before adjoining operational evidence.
Fresh evidence generators have exactly these independently formed endpoints.
This construction does not consult a process model or a semantic firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalPresentation

open _root_.CategoryTheory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus

abbrev binding := NamePassing.Presentation.signature
abbrev staticSignature := ClosedPresentation.AuthoredPresentation.signature.{0}
  NamePassing.AuthoredEquations.equations
abbrev Static := Object staticSignature
abbrev staticInclusion := ClosedPresentation.AuthoredPresentation.inclusion.{0}
  NamePassing.AuthoredEquations.equations

def vertex : Static := staticInclusion.functor.obj (ClosedPresentation.sortObject.{0} binding .tm)
abbrev categorySignature := RelativeClosedInternalCategory.Presentation.nativeSignature vertex
abbrev categoryMap := RelativeClosedInternalCategory.Presentation.nativeInclusion vertex

inductive Origin where
  | beta
  | fetch
  deriving DecidableEq

def metas : Origin → List (MetaArity binding)
  | .beta => NamePassing.AuthoredOperationalProfile.betaMetas
  | .fetch => []

def context : Origin → Ctx binding
  | .beta => NamePassing.AuthoredOperationalProfile.beta.conclusion.ctx
  | .fetch => NamePassing.AuthoredOperationalProfile.fetch.conclusion.ctx

def beforeTerm : (origin : Origin) → Term (withMetas binding (metas origin)) (context origin) .tm
  | .beta => NamePassing.AuthoredOperationalProfile.beta.conclusion.lhs
  | .fetch => NamePassing.AuthoredOperationalProfile.fetch.conclusion.lhs

def afterTerm : (origin : Origin) → Term (withMetas binding (metas origin)) (context origin) .tm
  | .beta => NamePassing.AuthoredOperationalProfile.beta.conclusion.rhs
  | .fetch => NamePassing.AuthoredOperationalProfile.fetch.conclusion.rhs

def staticStage (origin : Origin) : Static := staticInclusion.functor.obj
  (ClosedPresentation.SchemaExpressions.genericStage.{0} binding (metas origin) (context origin))

def staticBefore (origin : Origin) : staticStage origin ⟶ vertex :=
  staticInclusion.functor.map (classOf (ClosedPresentation.SchemaExpressions.expression.{0}
    binding (beforeTerm origin)))

def staticAfter (origin : Origin) : staticStage origin ⟶ vertex :=
  staticInclusion.functor.map (classOf (ClosedPresentation.SchemaExpressions.expression.{0}
    binding (afterTerm origin)))

def premise (origin : Origin) : Object categorySignature := baseObject categorySignature (staticStage origin)

def before (origin : Origin) : RawHom (premise origin)
    (RelativeClosedInternalCategory.NativeCategory.vertexObject vertex categoryMap) :=
  ⟨.base (staticBefore origin),⟨.baseArrow (staticBefore origin)⟩⟩

def after (origin : Origin) : RawHom (premise origin)
    (RelativeClosedInternalCategory.NativeCategory.vertexObject vertex categoryMap) :=
  ⟨.base (staticAfter origin),⟨.baseArrow (staticAfter origin)⟩⟩

def declarations (origin : Origin) : RelativeClosedInternalCategory.RulePresentation.Declaration
    vertex categoryMap := ⟨premise origin,before origin,after origin⟩

abbrev signature := RelativeClosedInternalCategory.RulePresentation.signature vertex categoryMap declarations

def headers : HeaderFormation signature := RelativeClosedInternalCategory.RulePresentation.headers
  vertex categoryMap declarations (RelativeClosedInternalCategory.Presentation.nativeHeaders vertex)

abbrev category := RelativeClosedInternalCategory.RulePresentation.category vertex categoryMap declarations
abbrev fire := RelativeClosedInternalCategory.RulePresentation.fire vertex categoryMap declarations

theorem authored_source (origin : Origin) :
    classOf ((fire origin).compose
      (RelativeClosedInternalCategory.RulePresentation.edgeSource vertex categoryMap declarations)) =
    classOf (RelativeClosedInternalCategory.RulePresentation.before vertex categoryMap declarations origin) :=
  RelativeClosedInternalCategory.RulePresentation.fire_source vertex categoryMap declarations origin

theorem authored_target (origin : Origin) :
    classOf ((fire origin).compose
      (RelativeClosedInternalCategory.RulePresentation.edgeTarget vertex categoryMap declarations)) =
    classOf (RelativeClosedInternalCategory.RulePresentation.after vertex categoryMap declarations origin) :=
  RelativeClosedInternalCategory.RulePresentation.fire_target vertex categoryMap declarations origin

theorem complete_ordered_domains :
    (metas .beta,context .beta,metas .fetch,context .fetch) =
      ([([NamePassing.Presentation.Srt.nm],NamePassing.Presentation.Srt.tm)],
        [NamePassing.Presentation.Srt.nm],[],[NamePassing.Presentation.Srt.nm,NamePassing.Presentation.Srt.tm]) := rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalPresentation
