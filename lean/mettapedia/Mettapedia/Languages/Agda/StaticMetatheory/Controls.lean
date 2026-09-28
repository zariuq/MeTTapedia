import Mettapedia.Languages.Agda.StaticMetatheory.Regularity
import Mettapedia.Languages.Agda.StaticSpecification.Examples

/-!
Dependent endpoint and context-conversion controls for the frozen source rules.
The positive examples require conversion between syntactically different types.
The negative examples use endpoint regularity to reject malformed annotations;
regularity extraction is explicitly not claimed to identify equality histories.
-/

namespace Mettapedia.Languages.Agda.StaticMetatheory.Controls
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticSpecification.Examples

/-- The declared function's result is its type argument, not a constant type. -/
def dependentFunctionType : Ty 0 :=
  Ty.pi (Ty.universe 1) (.bind (.el 1 (.var 0)))

def dependentFunctionTypeFormed : FormTy .nil dependentFunctionType :=
  .pi (.universe .nil 1) (.ofTyping (.var 0 oneUniverseFormed))

def dependentContext : RawContext 1 := .snoc .nil dependentFunctionType
def dependentContextFormed : FormCtx dependentContext :=
  .snoc .nil dependentFunctionTypeFormed

def dependentFunctionTyped : Typing dependentContext (.var 0)
    (Ty.pi (Ty.universe 1) (.bind (.el 1 (.var 0)))) :=
  .var 0 dependentContextFormed

def redexArgument : Term 1 := closedIdentity.weaken.app (.sort 0)
def equalArguments :
    TermEq dependentContext redexArgument (.sort 0) (Ty.universe 1) :=
  closedBeta.weaken dependentFunctionTypeFormed

/-- App congruence states the right endpoint at the unreduced left result code. -/
def dependentApplicationEquality :
    TermEq dependentContext ((Term.var 0).app redexArgument)
      ((Term.var 0).app (.sort 0)) (.el 1 redexArgument) :=
  .appCong (.refl dependentFunctionTyped) equalArguments

def dependentRightEndpoint :
    Typing dependentContext ((Term.var 0).app (.sort 0)) (.el 1 redexArgument) :=
  (termEndpoints dependentApplicationEquality).right

def dependentRightNaturalType :
    Typing dependentContext ((Term.var 0).app (.sort 0)) (Ty.universe 0) :=
  .app dependentFunctionTyped (.sort 0 dependentContextFormed)

theorem dependent_result_types_raw_distinct :
    (.el 1 redexArgument : Ty 1) ≠ Ty.universe 0 := by
  intro h
  cases h

/-- A beta-expanded universe is a formed domain convertible to Set zero. -/
def expandedDomain : Ty 0 := .el 1 (closedIdentity.app (.sort 0))
def domainConversion : TypeEq .nil expandedDomain (Ty.universe 0) := .atSort closedBeta
def expandedDomainFormed : FormTy .nil expandedDomain := (typeEndpoints domainConversion).left
def expandedContext : RawContext 1 := .snoc .nil expandedDomain
def expandedContextFormed : FormCtx expandedContext := .snoc .nil expandedDomainFormed

/-- Forming the dependent codomain genuinely uses conversion of the declaration. -/
def expandedCodomainFormed : FormTy expandedContext (.el 0 (.var 0)) :=
  .ofTyping (.conv (.var 0 expandedContextFormed) (domainConversion.weaken expandedDomainFormed))

def changedDomainPiEquality :
    TermEq .nil (.pi expandedDomain (.bind (.el 0 (.var 0))))
      (.pi (Ty.universe 0) (.bind (.el 0 (.var 0)))) (Ty.universe 1) :=
  .piCong expandedDomainFormed domainConversion (.refl expandedCodomainFormed)

def changedDomainRightEndpoint :
    Typing .nil (.pi (Ty.universe 0) (.bind (.el 0 (.var 0)))) (Ty.universe 1) :=
  (termEndpoints changedDomainPiEquality).right

theorem changed_domains_raw_distinct : expandedDomain ≠ Ty.universe 0 := by
  intro h
  cases h

def twoDeclarationConversion :
    ContextConversion (expandedContext.snoc (.el 0 (.var 0)))
      (typeContext.snoc (.el 0 (.var 0))) :=
  .snoc (.snoc .nil domainConversion) (.refl expandedCodomainFormed)

/-- The older type variable stays at index one after changing the first declaration. -/
def convertedNewestVariable :
    Typing (typeContext.snoc (.el 0 (.var 0))) (.var 0) (.el 0 (.var 1)) :=
  twoDeclarationConversion.typing (.var 0 twoDeclarationConversion.identitySub.source)

def reverseTwoDeclarationConversion := twoDeclarationConversion.symm
def roundtripTwoDeclarationConversion :=
  twoDeclarationConversion.trans reverseTwoDeclarationConversion

def bindingVersusNonbinding :
    TermEq .nil (.lam (.bind (.sort 0))) (.lam (.noBind (.sort 0)))
      (Ty.pi (Ty.universe 1) (.noBind (Ty.universe 1))) :=
  lambdaCong (.universe .nil 1) (.universe oneUniverseFormed 1)
    (.sort 0 oneUniverseFormed) (.sort 0 oneUniverseFormed)
    (.refl (.sort 0 oneUniverseFormed))

theorem abstraction_forms_raw_distinct :
    (Term.lam (.bind (.sort 0)) : Term 0) ≠ .lam (.noBind (.sort 0)) := by
  intro h
  cases h

/-- Formation is recovered from either endpoint even when levels alone agree. -/
theorem malformed_type_equality_rejected {Γ : RawContext n} {B : Ty n} :
    ¬ Nonempty (TypeEq Γ (.el 0 (.sort 0)) B) := by
  rintro ⟨d⟩
  exact wrong_annotation_rejected ⟨(typeEndpoints d).left⟩

theorem malformed_term_equality_rejected {Γ : RawContext n} {t u : Term n} :
    ¬ Nonempty (TermEq Γ t u (.el 0 (.sort 0))) := by
  rintro ⟨d⟩
  exact wrong_annotation_rejected ⟨(termEndpoints d).formed⟩

theorem malformed_context_conversion_rejected {Γ : RawContext 1} :
    ¬ Nonempty (ContextConversion Γ malformedTelescope) := by
  rintro ⟨d⟩
  exact malformed_telescope_rejected ⟨d.identitySub.target⟩

/-- Regularity returns derivations but does not retain every equality-rule event. -/
def directEquality : TermEq .nil (.sort 0) (.sort 0) (Ty.universe 1) :=
  .refl directSortTyping
def reversedTwiceEquality : TermEq .nil (.sort 0) (.sort 0) (Ty.universe 1) :=
  .symm (.symm directEquality)

theorem equality_receipts_distinct : directEquality ≠ reversedTwiceEquality := by
  intro h
  cases h

theorem extracted_endpoint_receipts_agree :
    termEndpoints directEquality = termEndpoints reversedTwiceEquality := rfl


end Mettapedia.Languages.Agda.StaticMetatheory.Controls
