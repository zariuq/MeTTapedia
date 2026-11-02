import Mettapedia.Languages.HOLLight.SourceSelectionProfile
import Mettapedia.Languages.HOLLight.AdmittedPrimitiveProfiles
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Logic.HOL.RepresentedConstructorReflection
import Mettapedia.Logic.HOL.ConstructorPredicateRepresentation

/-!
# Field recovery compiled against the exact source provider statements

The constructor, marker and branches are explicit source terms. The three
premises are the actual source selection instances and full constructor law.
Retained recovery derives field injectivity from that full law and uses the
constructed decoder. Applying the compiled theorems to cache entries remains
an explicit primitive discharge operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.SourceFieldRepresentationCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory HOL
open HOL.ConstructorFieldRepresentation HOL.MixedConstructorPayloadMaps

structure Inputs where
  number : Ty
  element : Ty
  space : Ty
  raw : HOL.ClosedTerm Symbol (Raw number.toHOL element.toHOL (number.toHOL ⇒ space.toHOL) space.toHOL)
  marker : HOL.ClosedTerm Symbol number.toHOL
  branches : HOL.ClosedTerm Symbol (number.toHOL ⇒ space.toHOL)

def fields (given : Inputs) := [[given.number.toHOL,given.element.toHOL,given.number.toHOL]]
def payload (given : Inputs) := AdmittedSourcePayloads.payload (fields given)

private def castSelection {first second : HOL.Ty AtomicTy} (same : first = second)
    (operation : HOL.ClosedTerm Symbol (SelectionProofs.Selection first)) :
    HOL.ClosedTerm Symbol (SelectionProofs.Selection second) := same ▸ operation

private theorem castSelection_principle {first second : HOL.Ty AtomicTy} (same : first = second)
    (operation : HOL.ClosedTerm Symbol (SelectionProofs.Selection first)) :
    SelectionProofs.principle (castSelection same operation) = SelectionProofs.principle operation := by
  cases same
  rfl

def selectPayload (given : Inputs) : HOL.ClosedTerm Symbol (SelectionProofs.Selection (Payload given.number.toHOL given.element.toHOL)) :=
  castSelection (AdmittedSourcePayloads.payload_toHOL (fields given)) (SourceSelectionProfile.selection (payload given))
def selectField (given : Inputs) := SourceSelectionProfile.selection given.element
def encode (given : Inputs) := embedding given.raw given.marker given.branches
def decode (given : Inputs) := decoder given.raw (selectPayload given) (selectField given)

theorem payload_selection_statement (given : Inputs) :
    SelectionProofs.principle (selectPayload given) = SourceSelectionProfile.native (payload given) :=
  (castSelection_principle _ _).trans (SourceSelectionProfile.native_is_principle _).symm

def premises (given : Inputs) : List (HOL.ClosedFormula Symbol) := [
  SourceSelectionProfile.native (payload given),SourceSelectionProfile.native given.element,
  ConstructorInjectivity.statement given.raw]

def payloadProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given) (SelectionProofs.principle (selectPayload given)) :=
  .castIndices rfl (payload_selection_statement given).symm (.hyp ⟨0,by simp [premises]⟩)
def fieldProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given) (SelectionProofs.principle (selectField given)) :=
  .castIndices rfl (SourceSelectionProfile.native_is_principle given.element) (.hyp ⟨1,by simp [premises]⟩)
def constructorProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given) (ConstructorProjections.fieldInjective given.raw) :=
  .impE (ConstructorInjectivity.fields given.raw) (.hyp ⟨2,by simp [premises]⟩)

theorem payloadProof_free (given : Inputs) : (payloadProof given).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro
theorem fieldProof_free (given : Inputs) : (fieldProof given).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro
theorem constructorProof_free (given : Inputs) : (constructorProof given).FunctionExtensionalityFree :=
  ⟨ConstructorInjectivity.fields_free _,True.intro⟩

def roundtripProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given) (leftInverse (encode given) (decode given)) :=
  roundtrip_law given.raw given.marker given.branches (selectPayload given) (selectField given)
    (payloadProof given) (fieldProof given) (constructorProof given)
theorem roundtripProof_free (given : Inputs) : (roundtripProof given).FunctionExtensionalityFree :=
  roundtrip_law_free _ _ _ _ _ _ _ _ (payloadProof_free given) (fieldProof_free given) (constructorProof_free given)

def retractionProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given)
    (GuardedRetraction.law (decode given) (encode given) (image (encode given))) :=
  RepresentedConstructorReflection.fieldLaw given.raw given.marker given.branches (selectPayload given) (selectField given)
    (payloadProof given) (fieldProof given) (constructorProof given)
theorem retractionProof_free (given : Inputs) : (retractionProof given).FunctionExtensionalityFree :=
  RepresentedConstructorReflection.fieldLaw_free _ _ _ _ _ _ _ _
    (payloadProof_free given) (fieldProof_free given) (constructorProof_free given)

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id
@[irreducible,noinline] def compileRoundtrip (given : Inputs) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy (roundtripProof given)
    (roundtripProof_free given) ReverseTranslation.Naming.empty ("source-field-roundtrip",0)
@[irreducible,noinline] def compileRetraction (given : Inputs) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy (retractionProof given)
    (retractionProof_free given) ReverseTranslation.Naming.empty ("source-field-retraction",0)

theorem compileRoundtrip_accepted (given : Inputs) :
    (ProofSystem.checker emptyAxiomPolicy).check (compileRoundtrip given).proof.result
      (compileRoundtrip given).proof.certificate = true := (compileRoundtrip given).proof.accepted
theorem compileRetraction_accepted (given : Inputs) :
    (ProofSystem.checker emptyAxiomPolicy).check (compileRetraction given).proof.result
      (compileRetraction given).proof.certificate = true := (compileRetraction given).proof.accepted

/-- Transport the caller's predicate together with its field values. -/
def representedPredicate (given : Inputs)
    (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :=
  ConstructorPredicateRepresentation.lift (encode given) predicate

def predicateAt (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop))
    (field : HOL.ClosedTerm Symbol given.element.toHOL) :
    HOL.ProofSyntax Symbol (premises given)
      (.eq (.app (representedPredicate given predicate) (.app (encode given) field)) (.app predicate field)) :=
  ConstructorPredicateRepresentation.atEncoded (encode given) (decode given) predicate field (roundtripProof given)

theorem predicateAt_free (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop))
    (field : HOL.ClosedTerm Symbol given.element.toHOL) : (predicateAt given predicate field).FunctionExtensionalityFree :=
  ConstructorPredicateRepresentation.atEncoded_free _ _ _ _ _ (roundtripProof_free given)

def representedRetraction (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :
    HOL.ProofSyntax Symbol (premises given)
      (GuardedRetraction.law (decode given) (encode given) (representedPredicate given predicate)) :=
  ConstructorPredicateRepresentation.retraction (encode given) (decode given) predicate (roundtripProof given)

theorem representedRetraction_free (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :
    (representedRetraction given predicate).FunctionExtensionalityFree :=
  ConstructorPredicateRepresentation.retraction_free _ _ _ _ (roundtripProof_free given)

@[irreducible,noinline] def compilePredicateAt (given : Inputs)
    (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) (field : HOL.ClosedTerm Symbol given.element.toHOL) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy (predicateAt given predicate field)
    (predicateAt_free given predicate field) ReverseTranslation.Naming.empty ("source-predicate-at-encoded",0)

@[irreducible,noinline] def compileRepresentedRetraction (given : Inputs)
    (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy (representedRetraction given predicate)
    (representedRetraction_free given predicate) ReverseTranslation.Naming.empty ("source-represented-predicate-retraction",0)

private def castNumber {first second payload space : HOL.Ty AtomicTy} (same : first = second)
    (raw : HOL.ClosedTerm Symbol (first ⇒ payload ⇒ (first ⇒ space) ⇒ space)) :
    HOL.ClosedTerm Symbol (second ⇒ payload ⇒ (second ⇒ space) ⇒ space) := same ▸ raw

private theorem castNumber_statement {first second payload space : HOL.Ty AtomicTy} (same : first = second)
    (raw : HOL.ClosedTerm Symbol (first ⇒ payload ⇒ (first ⇒ space) ⇒ space)) :
    ConstructorInjectivity.statement (castNumber same raw) = ConstructorInjectivity.statement raw := by
  cases same
  rfl

section Admitted
variable {policy : AxiomPolicy} [DecidablePred policy]
    {before : ProofExecution.Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
    {parameter : Name} (element : Ty)
    (admitted : AdmittedSourcePayloads.Instance policy before operations parameter
      [[operations.number.toHOL,element.toHOL,operations.number.toHOL]])
    (numberSame : (AdmittedSourcePayloads.targetOperations operations parameter
      [[operations.number.toHOL,element.toHOL,operations.number.toHOL]]).number = operations.number)

/-- The constructor is the exact admitted source instance, the marker retains
the source numeral wrapper, and branches use the actual source bottom. The
number agreement is a checked equality of source types, not a logical law. -/
def fromAdmitted : Inputs where
  number := operations.number
  element := element
  space := (AdmittedSourcePayloads.targetOperations operations parameter
    [[operations.number.toHOL,element.toHOL,operations.number.toHOL]]).space
  raw := castNumber (congrArg Ty.toHOL numberSame)
    (AdmittedPrimitiveProfiles.constructor admitted)
  marker := operations.natural.zero
  branches := .lam (weaken (AdmittedSourcePayloads.targetOperations operations parameter
    [[operations.number.toHOL,element.toHOL,operations.number.toHOL]]).recursive.bottom)

theorem fromAdmitted_constructor_statement :
    ConstructorInjectivity.statement (fromAdmitted element admitted numberSame).raw =
      ConstructorInjectivityProfile.native (AdmittedSourcePayloads.targetOperations operations parameter
        [[operations.number.toHOL,element.toHOL,operations.number.toHOL]]).recursive :=
  (castNumber_statement _ _).trans (AdmittedPrimitiveProfiles.constructor_statement admitted)

theorem fromAdmitted_payload : payload (fromAdmitted element admitted numberSame) =
    AdmittedSourcePayloads.payload [[operations.number.toHOL,element.toHOL,operations.number.toHOL]] := rfl
end Admitted

#print axioms retractionProof
#print axioms retractionProof_free
#print axioms compileRetraction_accepted
#print axioms fromAdmitted_constructor_statement
end Mettapedia.Languages.HOLLight.SourceFieldRepresentationCompilation
