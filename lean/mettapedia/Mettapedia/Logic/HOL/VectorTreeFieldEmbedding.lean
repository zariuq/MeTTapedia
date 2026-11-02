import Mettapedia.Logic.HOL.FiniteConstructorFieldEmbedding

/-!
# Answer fields in the complete solved/branch payload signature

The two constructor rows are a unary answer row and the branch's two
numeric fields. Storage and readback use that same complete raw signature.
The supplied source predicate is transported with its original membership.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorTreeFieldEmbedding
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {number element carrier : Ty Base} {Δ : List (Formula Const Γ)}

def rawSignature (number element : Ty Base) : List (List (Ty Base)) := [[element],[number,number]]
def storedSignature (number carrier : Ty Base) : List (List (Ty Base)) := [[carrier],[number,number]]

def solvedOccurrence : Fin (rawSignature number element).length := ⟨0,by change 0 < 2; decide⟩
def branchOccurrence : Fin (rawSignature number element).length := ⟨1,by change 1 < 2; decide⟩

structure Inputs (Const : Ty Base → Type v) (Γ : Ctx Base) (number element carrier : Ty Base) where
  raw : Term Const Γ (ConstructorProjections.Constructor number (payloadType (rawSignature number element)) (number ⇒ carrier) carrier)
  zero : Term Const Γ number
  children : Term Const Γ (number ⇒ carrier)
  payloadSelection : Term Const Γ (SelectionProofs.Selection (payloadType (rawSignature number element)))
  fieldSelection : Term Const Γ (SelectionProofs.Selection element)

namespace Inputs
variable (given : Inputs Const Γ number element carrier)

def encode : Term Const Γ (element ⇒ carrier) :=
  FiniteConstructorFieldEmbedding.embedding (rawSignature number element) solvedOccurrence .vz
    given.raw given.zero given.children PUnit.unit

def decode : Term Const Γ (carrier ⇒ element) :=
  FiniteConstructorFieldEmbedding.decoder (rawSignature number element) solvedOccurrence .vz
    given.raw given.payloadSelection given.fieldSelection

def predicate (source : Term Const Γ (element ⇒ .prop)) : Term Const Γ (carrier ⇒ .prop) :=
  ConstructorPredicateRepresentation.lift given.encode source

def substitute (images : Subst Const Γ Ξ) : Inputs Const Ξ number element carrier where
  raw := subst images given.raw
  zero := subst images given.zero
  children := subst images given.children
  payloadSelection := subst images given.payloadSelection
  fieldSelection := subst images given.fieldSelection

theorem encode_subst (images : Subst Const Γ Ξ) : subst images given.encode = (given.substitute images).encode :=
  FiniteConstructorFieldEmbedding.embedding_subst (rawSignature number element) solvedOccurrence .vz
    given.raw given.zero given.children PUnit.unit images

theorem decode_subst (images : Subst Const Γ Ξ) : subst images given.decode = (given.substitute images).decode :=
  FiniteConstructorFieldEmbedding.decoder_subst (rawSignature number element) solvedOccurrence .vz
    given.raw given.payloadSelection given.fieldSelection images

theorem predicate_subst (images : Subst Const Γ Ξ) (source : Term Const Γ (element ⇒ .prop)) :
    subst images (given.predicate source) = (given.substitute images).predicate (subst images source) := by
  rw [predicate,ConstructorPredicateRepresentation.lift_subst,encode_subst]
  rfl

variable (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
  (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
  (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))

def roundtrip (field : Term Const Γ element) :
    ProofSyntax Const Δ (.eq (.app given.decode (.app given.encode field)) field) :=
  FiniteConstructorFieldEmbedding.roundtrip (rawSignature number element) solvedOccurrence .vz
    given.raw given.zero given.children PUnit.unit given.payloadSelection given.fieldSelection
    payloadChoice fieldChoice injectivity field

def roundtripLaw : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode) :=
  FiniteConstructorFieldEmbedding.roundtripLaw (rawSignature number element) solvedOccurrence .vz
    given.raw given.zero given.children PUnit.unit given.payloadSelection given.fieldSelection
    payloadChoice fieldChoice injectivity

theorem roundtripLaw_free
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (constructorFree : injectivity.FunctionExtensionalityFree) :
    (given.roundtripLaw payloadChoice fieldChoice injectivity).FunctionExtensionalityFree :=
  FiniteConstructorFieldEmbedding.roundtripLaw_free (rawSignature number element) solvedOccurrence .vz
    given.raw given.zero given.children PUnit.unit given.payloadSelection given.fieldSelection
    payloadChoice fieldChoice injectivity payloadFree fieldFree constructorFree

def predicateRecovery (source : Term Const Γ (element ⇒ .prop)) (stored : Term Const Γ carrier)
    (member : ProofSyntax Const Δ (.app (given.predicate source) stored)) :
    ProofSyntax Const Δ (.eq (.app given.encode (.app given.decode stored)) stored) :=
  FiniteConstructorFieldEmbedding.predicateRecovery (rawSignature number element) solvedOccurrence .vz
    given.raw given.zero given.children PUnit.unit given.payloadSelection given.fieldSelection
    payloadChoice fieldChoice injectivity source stored member

theorem predicateRecovery_free
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (constructorFree : injectivity.FunctionExtensionalityFree)
    (source : Term Const Γ (element ⇒ .prop)) (stored : Term Const Γ carrier)
    (member : ProofSyntax Const Δ (.app (given.predicate source) stored)) (memberFree : member.FunctionExtensionalityFree) :
    (given.predicateRecovery payloadChoice fieldChoice injectivity source stored member).FunctionExtensionalityFree :=
  FiniteConstructorFieldEmbedding.predicateRecovery_free (rawSignature number element) solvedOccurrence .vz
    given.raw given.zero given.children PUnit.unit given.payloadSelection given.fieldSelection
    payloadChoice fieldChoice injectivity payloadFree fieldFree constructorFree source stored member memberFree

end Inputs
#print axioms Inputs.roundtripLaw
#print axioms Inputs.roundtripLaw_free
#print axioms Inputs.predicateRecovery
end Mettapedia.Logic.HOL.VectorTreeFieldEmbedding
