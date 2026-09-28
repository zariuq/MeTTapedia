import Mettapedia.Languages.Agda.Structural.StaticContextConversion
import Mettapedia.Languages.Agda.Structural.SpineEvidenceOperations

/-!
# Dependent controls for structural regularity and context conversion

A beta-expanded universe is equal to its contraction but is different raw
syntax. Substitution into the type family `X ↦ X` therefore changes the raw
result code. The endpoint and context-conversion constructions must transport
real typing evidence across this difference. Negative controls exclude a
closed-level mismatch and a Prop annotation in this finite-Set fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics.RegularityControls

open Mettapedia.OSLF.Binding

def empty : RawContext 0 := .nil
def domain : TypeParameter 0 := universeType 0 1
def extended : RawContext 1 := empty.snoc domain.code
def codomain : TypeBody 0 := .noBind domain
def identityBody : TermBody 0 := .bind (.var .zero)

def domainFormed : Derivation (formed empty domain.code) := Derivation.formation (Derivation.sort 1 Derivation.empty)
def extendedFormed : Derivation (context extended) := Derivation.extend Derivation.empty domainFormed
def codomainFormed : Derivation (formed extended codomain.open.code) :=
  Derivation.formation (Derivation.sort 1 extendedFormed)
def bodyTyped : Derivation (typed extended identityBody.open codomain.open.code) :=
  Derivation.variableTerm (Γ := extended) .zero extendedFormed
def universeTyped : Derivation (typed empty (universeTerm 0) domain.code) := Derivation.sort 0 Derivation.empty

def expanded : RawTm 0 := app identityBody.lambda (universeTerm 0)
def contracted : RawTm 0 := universeTerm 0
def betaEquality : Derivation (termEqual empty expanded contracted domain.code) :=
  Derivation.beta domainFormed codomainFormed bodyTyped universeTyped

def family : TypeBody 0 := .bind ⟨1, .var .zero⟩
def familyFormed : Derivation (formed extended family.open.code) :=
  Derivation.formation (Derivation.variableTerm (Γ := extended) .zero extendedFormed)

def leftType : TypeParameter 0 := family.instantiate expanded
def rightType : TypeParameter 0 := family.instantiate contracted

noncomputable def equalDependentResults : Derivation (typeEqual empty leftType.code rightType.code) :=
  Derivation.instantiateCongruence domainFormed familyFormed
    betaEquality.termEndpoints.left betaEquality.termEndpoints.right betaEquality

theorem result_codes_are_distinct : leftType.code ≠ rightType.code := by
  intro same
  cases same

noncomputable def leftResultFormed : Derivation (formed empty leftType.code) :=
  equalDependentResults.typeEndpoints.left
noncomputable def rightResultFormed : Derivation (formed empty rightType.code) :=
  equalDependentResults.typeEndpoints.right

def leftContext : RawContext 1 := empty.snoc leftType.code
def rightContext : RawContext 1 := empty.snoc rightType.code
noncomputable def leftContextFormed : Derivation (context leftContext) := Derivation.extend Derivation.empty leftResultFormed
noncomputable def rightContextFormed : Derivation (context rightContext) := Derivation.extend Derivation.empty rightResultFormed

noncomputable def changedDeclaration : ContextConversion Derivation leftContext rightContext :=
  .snoc .nil equalDependentResults

noncomputable def contextIdentity : TypedSubstitution Derivation leftContext rightContext
    (Telescope.identity (S := sig) .term 1) :=
  changedDeclaration.identitySubstitution canonicalOperations Derivation.typeEndpoints

noncomputable def variableAfterContextConversion :
    Derivation (typed rightContext (.var .zero) (ContextGeometry.lookup leftContext .zero)) :=
  changedDeclaration.typing canonicalOperations Derivation.typeEndpoints
    (Derivation.variableTerm (Γ := leftContext) .zero leftContextFormed)

theorem context_codes_are_distinct : leftContext ≠ rightContext := by
  intro same
  cases same

/-- The second declaration depends on the first variable's converted type. -/
def dependentMember : RawTy 1 := (TypeParameter.mk 0 (.var .zero : RawTm 1)).code

noncomputable def memberFormedOnLeft : Derivation (formed leftContext dependentMember) := by
  have equal := canonicalOperations.weakenTypeEquality leftResultFormed equalDependentResults
  have variableTree := Derivation.variableTerm (Γ := leftContext) .zero leftContextFormed
  exact Derivation.formation (Derivation.conversion variableTree equal)

noncomputable def twoDeclarationConversion : ContextConversion Derivation
    (leftContext.snoc dependentMember) (rightContext.snoc dependentMember) :=
  .snoc changedDeclaration memberFormedOnLeft.typeReflexivity

noncomputable def twoDeclarationIdentity : TypedSubstitution Derivation
    (leftContext.snoc dependentMember) (rightContext.snoc dependentMember)
    (Telescope.identity (S := sig) .term 2) :=
  twoDeclarationConversion.identitySubstitution canonicalOperations Derivation.typeEndpoints

noncomputable def olderVariableAfterConversion : Derivation (typed (rightContext.snoc dependentMember)
    (.var (.succ .zero)) (ContextGeometry.lookup (leftContext.snoc dependentMember) (.succ .zero))) := by
  exact (congrArg (fun T => Derivation (typed (rightContext.snoc dependentMember) (.var (.succ .zero)) T))
    (Telescope.bind_identity (ContextGeometry.lookup (leftContext.snoc dependentMember) (.succ .zero)))).mp
    (twoDeclarationIdentity.image (.succ .zero))

noncomputable def conversionRoundTrip : ContextConversion Derivation leftContext leftContext :=
  changedDeclaration.transitivity canonicalOperations Derivation.typeEndpoints
    (changedDeclaration.symmetry canonicalOperations Derivation.typeEndpoints)

def bindingConstant : TermBody 0 := .bind (universeTerm 0)
def nonbindingConstant : TermBody 0 := .noBind (universeTerm 0)
def constantTyped : Derivation (typed extended (universeTerm 0) codomain.open.code) :=
  Derivation.sort 0 extendedFormed

noncomputable def bindingAndNonbindingEqual : Derivation
    (termEqual empty bindingConstant.lambda nonbindingConstant.lambda (piType domain codomain).code) :=
  canonicalOperations.lambdaCongruence domainFormed codomainFormed constantTyped constantTyped
    (Derivation.reflexivity constantTyped)

theorem binding_forms_remain_distinct : bindingConstant.lambda ≠ nonbindingConstant.lambda := by
  intro same
  cases same

theorem different_levels_rejected
    (tree : Derivation (typeEqual empty (universeType 0 0).code (universeType 0 1).code)) : False := by
  have levels := tree.typeEquality_levels
  cases levels

theorem prop_formation_rejected (tree : Derivation
    (formed empty (el (prop (levelClosed 1)) (universeTerm 0)))) : False := by
  have view := tree.formationView
  have boundary := view.boundary
  cases boundary

/-- The same derived lambda operation accepts genuine combined body trees. -/
noncomputable def combinedBody : SpineStatics.CoreDerivation
    (typed extended (eliminate (universeTerm 0) nil) codomain.open.code) :=
  SpineStatics.Derivation.elimination (SpineStatics.includeCanonical constantTyped)
    (SpineStatics.Derivation.nil extended codomain.open.code)

def administrativeConstant : TermBody 0 := .bind (eliminate (universeTerm 0) nil)

noncomputable def combinedLambdaEquality : SpineStatics.CoreDerivation
    (termEqual empty administrativeConstant.lambda administrativeConstant.lambda (piType domain codomain).code) :=
  SpineStatics.spineOperations.lambdaCongruence
    (SpineStatics.includeCanonical domainFormed) (SpineStatics.includeCanonical codomainFormed)
    combinedBody combinedBody
    (SpineStatics.Derivation.core (.reflexivity extended administrativeConstant.open codomain.open.code)
      (FiniteRulePremiseLists.consEvidence _ combinedBody (FiniteRulePremiseLists.noEvidence _)))

end Mettapedia.Languages.Agda.Structural.Statics.RegularityControls
