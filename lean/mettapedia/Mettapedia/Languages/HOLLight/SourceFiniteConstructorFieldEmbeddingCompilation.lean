import Mettapedia.Languages.HOLLight.SourceSelectionProfile
import Mettapedia.Languages.HOLLight.AdmittedPrimitiveProfiles
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Logic.HOL.VectorTreeFieldEmbedding

/-!
# Source-backed field embeddings at a complete constructor signature

The constructor and payload selection share one finite payload signature.
The chosen field and its other-field fillers are typed explicitly. The
compiled statements retain both source selection premises and the source
constructor law. Predicate transport retains the caller's source predicate.

The admitted solved/branch adapter uses one source payload instance for the
constructor, payload selection and bottom children. These checked certificate
constructions do not establish an external native replay result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SourceFiniteConstructorFieldEmbeddingCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory HOL
open HOL.FiniteConstructorEncoding HOL.FiniteConstructorFieldEmbedding

structure Inputs where
  number : Ty
  element : Ty
  space : Ty
  fields : List (List (HOL.Ty AtomicTy))
  occurrence : Fin fields.length
  selected : HOL.Var (fields.get occurrence) element.toHOL
  raw : HOL.ClosedTerm Symbol (number.toHOL ⇒ payloadType fields ⇒ (number.toHOL ⇒ space.toHOL) ⇒ space.toHOL)
  marker : HOL.ClosedTerm Symbol number.toHOL
  children : HOL.ClosedTerm Symbol (number.toHOL ⇒ space.toHOL)
  fillers : Arguments Symbol [] (remainingFields selected)

def payload (given : Inputs) : Ty := AdmittedSourcePayloads.payload given.fields

private def castSelection {first second : HOL.Ty AtomicTy} (same : first = second)
    (selection : HOL.ClosedTerm Symbol (HOL.SelectionProofs.Selection first)) :
    HOL.ClosedTerm Symbol (HOL.SelectionProofs.Selection second) := same ▸ selection

private theorem castSelection_principle {first second : HOL.Ty AtomicTy} (same : first = second)
    (selection : HOL.ClosedTerm Symbol (HOL.SelectionProofs.Selection first)) :
    HOL.SelectionProofs.principle (castSelection same selection) = HOL.SelectionProofs.principle selection := by
  cases same
  rfl

def selectPayload (given : Inputs) : HOL.ClosedTerm Symbol (HOL.SelectionProofs.Selection (payloadType given.fields)) :=
  castSelection (AdmittedSourcePayloads.payload_toHOL given.fields) (SourceSelectionProfile.selection (payload given))
def selectField (given : Inputs) := SourceSelectionProfile.selection given.element
def encode (given : Inputs) := embedding given.fields given.occurrence given.selected given.raw given.marker given.children given.fillers
def decode (given : Inputs) := decoder given.fields given.occurrence given.selected given.raw (selectPayload given) (selectField given)

theorem payload_selection_statement (given : Inputs) :
    HOL.SelectionProofs.principle (selectPayload given) = SourceSelectionProfile.native (payload given) :=
  (castSelection_principle _ _).trans (SourceSelectionProfile.native_is_principle _).symm

def premises (given : Inputs) : List (HOL.ClosedFormula Symbol) := [
  SourceSelectionProfile.native (payload given), SourceSelectionProfile.native given.element,
  HOL.ConstructorInjectivity.statement given.raw]

def payloadProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given) (HOL.SelectionProofs.principle (selectPayload given)) :=
  .castIndices rfl (payload_selection_statement given).symm (.hyp ⟨0,by simp [premises]⟩)
def fieldProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given) (HOL.SelectionProofs.principle (selectField given)) :=
  .castIndices rfl (SourceSelectionProfile.native_is_principle given.element) (.hyp ⟨1,by simp [premises]⟩)
def constructorProof (given : Inputs) : HOL.ProofSyntax Symbol (premises given) (HOL.ConstructorProjections.fieldInjective given.raw) :=
  .impE (HOL.ConstructorInjectivity.fields given.raw) (.hyp ⟨2,by simp [premises]⟩)

theorem payloadProof_free (given : Inputs) : (payloadProof given).FunctionExtensionalityFree :=
  (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro
theorem fieldProof_free (given : Inputs) : (fieldProof given).FunctionExtensionalityFree :=
  (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro
theorem constructorProof_free (given : Inputs) : (constructorProof given).FunctionExtensionalityFree :=
  ⟨HOL.ConstructorInjectivity.fields_free _,True.intro⟩

def roundtripProof (given : Inputs) :
    HOL.ProofSyntax Symbol (premises given) (HOL.ConstructorFieldRepresentation.leftInverse (encode given) (decode given)) :=
  roundtripLaw given.fields given.occurrence given.selected given.raw given.marker given.children given.fillers
    (selectPayload given) (selectField given) (payloadProof given) (fieldProof given) (constructorProof given)

theorem roundtripProof_free (given : Inputs) : (roundtripProof given).FunctionExtensionalityFree :=
  roundtripLaw_free _ _ _ _ _ _ _ _ _ _ _ _ (payloadProof_free given) (fieldProof_free given) (constructorProof_free given)

def representedPredicate (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :=
  HOL.ConstructorPredicateRepresentation.lift (encode given) predicate

def predicateAt (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop))
    (field : HOL.ClosedTerm Symbol given.element.toHOL) :
    HOL.ProofSyntax Symbol (premises given)
      (.eq (.app (representedPredicate given predicate) (.app (encode given) field)) (.app predicate field)) :=
  HOL.ConstructorPredicateRepresentation.atEncoded (encode given) (decode given) predicate field (roundtripProof given)

theorem predicateAt_free (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop))
    (field : HOL.ClosedTerm Symbol given.element.toHOL) : (predicateAt given predicate field).FunctionExtensionalityFree :=
  HOL.ConstructorPredicateRepresentation.atEncoded_free _ _ _ _ _ (roundtripProof_free given)

def representedRetraction (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :
    HOL.ProofSyntax Symbol (premises given)
      (HOL.GuardedRetraction.law (decode given) (encode given) (representedPredicate given predicate)) :=
  HOL.ConstructorPredicateRepresentation.retraction (encode given) (decode given) predicate (roundtripProof given)

theorem representedRetraction_free (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :
    (representedRetraction given predicate).FunctionExtensionalityFree :=
  HOL.ConstructorPredicateRepresentation.retraction_free _ _ _ _ (roundtripProof_free given)

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

@[irreducible,noinline] def compileRoundtrip (given : Inputs) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy (roundtripProof given)
    (roundtripProof_free given) ReverseTranslation.Naming.empty ("source-inventory-field-roundtrip",0)

@[irreducible,noinline] def compileRepresentedRetraction (given : Inputs)
    (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy (representedRetraction given predicate)
    (representedRetraction_free given predicate) ReverseTranslation.Naming.empty ("source-inventory-predicate-retraction",0)

theorem compileRoundtrip_accepted (given : Inputs) :
    (ProofSystem.checker emptyAxiomPolicy).check (compileRoundtrip given).proof.result
      (compileRoundtrip given).proof.certificate = true := (compileRoundtrip given).proof.accepted

theorem compileRoundtrip_hypotheses (given : Inputs) :
    (compileRoundtrip given).proof.result.sequent.hyp =
      ReverseTranslation.reverseHypotheses ReverseTranslation.Naming.empty
        ((premises given).map HOL.ImpredicativeConnectives.expand) := (compileRoundtrip given).hypotheses_exact

theorem compileRoundtrip_conclusion (given : Inputs) :
    (compileRoundtrip given).proof.result.sequent.concl =
      ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
        (HOL.ImpredicativeConnectives.expand (HOL.ConstructorFieldRepresentation.leftInverse (encode given) (decode given))) :=
  (compileRoundtrip given).conclusion_exact

theorem compileRepresentedRetraction_accepted (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :
    (ProofSystem.checker emptyAxiomPolicy).check (compileRepresentedRetraction given predicate).proof.result
      (compileRepresentedRetraction given predicate).proof.certificate = true :=
  (compileRepresentedRetraction given predicate).proof.accepted

theorem compileRepresentedRetraction_hypotheses (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :
    (compileRepresentedRetraction given predicate).proof.result.sequent.hyp =
      ReverseTranslation.reverseHypotheses ReverseTranslation.Naming.empty
        ((premises given).map HOL.ImpredicativeConnectives.expand) := (compileRepresentedRetraction given predicate).hypotheses_exact

theorem compileRepresentedRetraction_conclusion (given : Inputs) (predicate : HOL.ClosedTerm Symbol (given.element.toHOL ⇒ .prop)) :
    (compileRepresentedRetraction given predicate).proof.result.sequent.concl =
      ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
        (HOL.ImpredicativeConnectives.expand (HOL.GuardedRetraction.law (decode given) (encode given)
          (representedPredicate given predicate))) := (compileRepresentedRetraction given predicate).conclusion_exact

private def castNumber {first second payload space : HOL.Ty AtomicTy} (same : first = second)
    (raw : HOL.ClosedTerm Symbol (first ⇒ payload ⇒ (first ⇒ space) ⇒ space)) :
    HOL.ClosedTerm Symbol (second ⇒ payload ⇒ (second ⇒ space) ⇒ space) := same ▸ raw

private theorem castNumber_statement {first second payload space : HOL.Ty AtomicTy} (same : first = second)
    (raw : HOL.ClosedTerm Symbol (first ⇒ payload ⇒ (first ⇒ space) ⇒ space)) :
    HOL.ConstructorInjectivity.statement (castNumber same raw) = HOL.ConstructorInjectivity.statement raw := by
  cases same
  rfl

def vectorFields (operations : RecursiveSpaceSourceReadback.Operations) (element : Ty) : List (List (HOL.Ty AtomicTy)) :=
  HOL.VectorTreeFieldEmbedding.rawSignature operations.number.toHOL element.toHOL

section Admitted
variable {policy : AxiomPolicy} [DecidablePred policy] {before : ProofExecution.Registered.State}
  {operations : RecursiveSpaceSourceReadback.Operations} {parameter : Name}
  (element : Ty)
  (admitted : AdmittedSourcePayloads.Instance policy before operations parameter (vectorFields operations element))
  (numberSame : (AdmittedSourcePayloads.targetOperations operations parameter (vectorFields operations element)).number = operations.number)

def fromAdmitted : Inputs where
  number := operations.number
  element := element
  space := (AdmittedSourcePayloads.targetOperations operations parameter (vectorFields operations element)).space
  fields := vectorFields operations element
  occurrence := HOL.VectorTreeFieldEmbedding.solvedOccurrence
  selected := .vz
  raw := castNumber (congrArg Ty.toHOL numberSame) (AdmittedPrimitiveProfiles.constructor admitted)
  marker := operations.natural.zero
  children := .lam (HOL.weaken (AdmittedSourcePayloads.targetOperations operations parameter (vectorFields operations element)).recursive.bottom)
  fillers := PUnit.unit

theorem fromAdmitted_constructor_statement :
    HOL.ConstructorInjectivity.statement (fromAdmitted element admitted numberSame).raw =
      ConstructorInjectivityProfile.native (AdmittedSourcePayloads.targetOperations operations parameter
        (vectorFields operations element)).recursive :=
  (castNumber_statement _ _).trans (AdmittedPrimitiveProfiles.constructor_statement admitted)

theorem fromAdmitted_payload : payload (fromAdmitted element admitted numberSame) =
    AdmittedSourcePayloads.payload (vectorFields operations element) := rfl

theorem fromAdmitted_premises : premises (fromAdmitted element admitted numberSame) =
    [SourceSelectionProfile.native (AdmittedSourcePayloads.payload (vectorFields operations element)),
      SourceSelectionProfile.native element,
      ConstructorInjectivityProfile.native
        (AdmittedSourcePayloads.targetOperations operations parameter (vectorFields operations element)).recursive] := by
  unfold premises
  rw [fromAdmitted_constructor_statement]
  rfl

def nativeInputs : HOL.VectorTreeFieldEmbedding.Inputs Symbol [] operations.number.toHOL element.toHOL
    (AdmittedSourcePayloads.targetOperations operations parameter (vectorFields operations element)).space.toHOL where
  raw := (fromAdmitted element admitted numberSame).raw
  zero := (fromAdmitted element admitted numberSame).marker
  children := (fromAdmitted element admitted numberSame).children
  payloadSelection := selectPayload (fromAdmitted element admitted numberSame)
  fieldSelection := selectField (fromAdmitted element admitted numberSame)

theorem fromAdmitted_encode : encode (fromAdmitted element admitted numberSame) =
    (nativeInputs element admitted numberSame).encode := rfl
theorem fromAdmitted_decode : decode (fromAdmitted element admitted numberSame) =
    (nativeInputs element admitted numberSame).decode := rfl

end Admitted
#print axioms roundtripProof
#print axioms roundtripProof_free
#print axioms compileRoundtrip_accepted
#print axioms compileRepresentedRetraction_conclusion
#print axioms fromAdmitted_constructor_statement
end Mettapedia.Languages.HOLLight.SourceFiniteConstructorFieldEmbeddingCompilation
