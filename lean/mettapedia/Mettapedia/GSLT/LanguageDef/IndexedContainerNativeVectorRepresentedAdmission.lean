import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorProgram
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorAdmission
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorSourceGuards
import Mettapedia.Logic.HOL.ConstructorPredicateRepresentation
import Mettapedia.Logic.HOL.ConstructorPayloadTransport

/-!
# Original constructor admission with a represented payload predicate

The independent payload type is encoded in the existing recursive carrier.
Its predicate is transported by direct image, retaining the source witness
and its membership. The original five constructor ports, generated shape,
root index and complete child conditions remain unchanged.

The field roundtrip is constructed from the two source selection principles
and the source constructor law. No image condition on an arbitrary predicate
is assumed. Whole-domain guarded uniqueness still requires elimination of
the actual generated admission guard; it is not asserted by this adapter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorRepresentedAdmission

open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original constructorCarrier)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorChildGuard
open IndexedContainerNativeVectorChildConditions
open FiniteConstructorEncoding MixedConstructorPayloadMaps

variable {Γ Ξ : Ctx Base} {A : Ty Base} {Δ : List (Formula Const Γ)}

structure Inputs (Γ : Ctx Base) (A : Ty Base) where
  raw : Term Const Γ (ConstructorFieldRepresentation.Raw N A (N ⇒ E) E)
  marker : Term Const Γ N
  branches : Term Const Γ (N ⇒ E)
  payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload N A))
  fieldSelection : Term Const Γ (SelectionProofs.Selection A)

namespace Inputs

def encode (given : Inputs Γ A) : Term Const Γ (A ⇒ E) :=
  ConstructorFieldRepresentation.embedding given.raw given.marker given.branches

def decode (given : Inputs Γ A) : Term Const Γ (E ⇒ A) :=
  ConstructorFieldRepresentation.decoder given.raw given.payloadSelection given.fieldSelection

def payload (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) : Term Const Γ (E ⇒ .prop) :=
  ConstructorPredicateRepresentation.lift given.encode source

def construct (given : Inputs Γ A) : Term Const Γ IndexedContainerNativeVectorConstructorProgram.RawConstructor :=
  ConstructorPayloadTransport.constructor given.raw given.decode

def substitute (given : Inputs Γ A) (images : Subst Const Γ Ξ) : Inputs Ξ A where
  raw := HOL.subst images given.raw
  marker := HOL.subst images given.marker
  branches := HOL.subst images given.branches
  payloadSelection := HOL.subst images given.payloadSelection
  fieldSelection := HOL.subst images given.fieldSelection

@[simp] theorem encode_subst (given : Inputs Γ A) (images : Subst Const Γ Ξ) :
    HOL.subst images given.encode = (given.substitute images).encode :=
  ConstructorFieldRepresentation.embedding_subst images given.raw given.marker given.branches

@[simp] theorem decode_subst (given : Inputs Γ A) (images : Subst Const Γ Ξ) :
    HOL.subst images given.decode = (given.substitute images).decode :=
  ConstructorFieldRepresentation.decoder_subst images given.raw given.payloadSelection given.fieldSelection

@[simp] theorem payload_subst (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (images : Subst Const Γ Ξ) :
    HOL.subst images (given.payload source) = (given.substitute images).payload (HOL.subst images source) := by
  rw [payload, ConstructorPredicateRepresentation.lift_subst, encode_subst]
  rfl

@[simp] theorem construct_subst (given : Inputs Γ A) (images : Subst Const Γ Ξ) :
    HOL.subst images given.construct = (given.substitute images).construct := by
  rw [construct, ConstructorPayloadTransport.constructor,
    CurriedPredicates.abstractFields_subst _ _ _ (ConstructorPayloadTransport.body_natural given.raw given.decode)]
  change CurriedPredicates.abstractFields [N,Payload N E,N ⇒ E] _ =
    CurriedPredicates.abstractFields [N,Payload N E,N ⇒ E] _
  apply congrArg (CurriedPredicates.abstractFields [N,Payload N E,N ⇒ E])
  funext laterContext later arguments
  simp only [ConstructorPayloadTransport.body, ConstructorPayloadTransport.value,
    ConstructorProjections.apply, substitute, decode, ConstructorFieldRepresentation.decoder_subst,
    HOL.subst_comp]
  rfl

def fieldInjectivity (given : Inputs Γ A)
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw)) :
    ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw) :=
  .impE (ConstructorInjectivity.fields given.raw) sourceLaw

theorem fieldInjectivity_free (given : Inputs Γ A)
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw))
    (free : sourceLaw.FunctionExtensionalityFree) : (given.fieldInjectivity sourceLaw).FunctionExtensionalityFree :=
  ⟨ConstructorInjectivity.fields_free _,free⟩

def roundtrip (given : Inputs Γ A)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw)) :
    ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode) :=
  ConstructorFieldRepresentation.roundtrip_law given.raw given.marker given.branches
    given.payloadSelection given.fieldSelection payloadChoice fieldChoice (given.fieldInjectivity sourceLaw)

theorem roundtrip_free (given : Inputs Γ A)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw))
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (sourceFree : sourceLaw.FunctionExtensionalityFree) :
    (given.roundtrip payloadChoice fieldChoice sourceLaw).FunctionExtensionalityFree :=
  ConstructorFieldRepresentation.roundtrip_law_free _ _ _ _ _ _ _ _ payloadFree fieldFree
    (given.fieldInjectivity_free sourceLaw sourceFree)

def retraction (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw)) :
    ProofSyntax Const Δ (GuardedRetraction.law given.decode given.encode (given.payload source)) :=
  ConstructorPredicateRepresentation.retraction given.encode given.decode source
    (given.roundtrip payloadChoice fieldChoice sourceLaw)

theorem retraction_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (sourceLaw : ProofSyntax Const Δ (ConstructorInjectivity.statement given.raw))
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (sourceFree : sourceLaw.FunctionExtensionalityFree) :
    (given.retraction source payloadChoice fieldChoice sourceLaw).FunctionExtensionalityFree :=
  ConstructorPredicateRepresentation.retraction_free _ _ _ _
    (given.roundtrip_free payloadChoice fieldChoice sourceLaw payloadFree fieldFree sourceFree)

def sourceImage (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (stored : Term Const Γ E)
    (member : ProofSyntax Const Δ (.app (given.payload source) stored)) :
    ProofSyntax Const Δ (.app (ConstructorFieldRepresentation.image given.encode) stored) :=
  ConstructorPredicateRepresentation.forget given.encode source stored member

theorem sourceImage_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (stored : Term Const Γ E)
    (member : ProofSyntax Const Δ (.app (given.payload source) stored)) (free : member.FunctionExtensionalityFree) :
    (given.sourceImage source stored member).FunctionExtensionalityFree :=
  ConstructorPredicateRepresentation.forget_free _ _ _ _ free

def allowed (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (length : Term Const Γ N) (field : Term Const Γ A)
    (member : ProofSyntax Const Δ (.app source field)) :
    ProofSyntax Const Δ (sourceAllowed (given.payload source) length (.app given.encode field)
      (weakenCtx Γ original.zero)) :=
  IndexedContainerNativeVectorSourceGuards.allowedOfTag (given.payload source) length (.app given.encode field)
    (ConstructorPredicateRepresentation.introduce given.encode source field member)

theorem allowed_free (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop))
    (length : Term Const Γ N) (field : Term Const Γ A)
    (member : ProofSyntax Const Δ (.app source field)) (free : member.FunctionExtensionalityFree) :
    (given.allowed source length field member).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorSourceGuards.allowedOfTag_free _ _ _ _
    (ConstructorPredicateRepresentation.introduce_free _ _ _ _ free)

end Inputs

variable (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (given : Inputs Γ A) (source : Term Const Γ (A ⇒ .prop)) (bottom : Term Const Γ E)

def program : Term Const Γ constructorCarrier :=
  IndexedContainerNativeVectorConstructorProgram.program elementSelection arraySelection
    (given.payload source) given.construct bottom

theorem program_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (program elementSelection arraySelection given source bottom) =
      program elementSelection arraySelection (given.substitute images) (HOL.subst images source)
        (HOL.subst images bottom) := by
  rw [program, IndexedContainerNativeVectorConstructorProgram.program_subst,
    Inputs.payload_subst, Inputs.construct_subst]
  rfl

variable (length : Term Const Γ N) (before : Term Const Γ E) (field : Term Const Γ A)
    (vector : Term Const Γ V) (after : Term Const Γ E)

def computation : ProofSyntax Const Δ (.eq
    (IndexedContainerNativeVectorConstructorProgram.applySource
      (program elementSelection arraySelection given source bottom) length before (.app given.encode field) vector after)
    (IndexedContainerNativeVectorConstructorProgram.constructed elementSelection arraySelection
      (given.payload source) given.construct bottom length before (.app given.encode field) vector after)) :=
  IndexedContainerNativeVectorConstructorProgram.computation elementSelection arraySelection
    (given.payload source) given.construct bottom length before (.app given.encode field) vector after

theorem computation_free :
    (computation (Δ := Δ) elementSelection arraySelection given source bottom length before field vector after).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorConstructorProgram.computation_free _ _ _ _ _ _ _ _ _ _

def rootIndex (member : ProofSyntax Const Δ (.app source field)) :
    ProofSyntax Const Δ ((constructors (given.payload source)).rootIndex given.construct
      (IndexedContainerNativeVectorConstructorProgram.constructed elementSelection arraySelection
        (given.payload source) given.construct bottom length before (.app given.encode field) vector after) .top) :=
  IndexedContainerNativeVectorConstructorProgram.rootIndex elementSelection arraySelection
    (given.payload source) given.construct bottom length before (.app given.encode field) vector after
    (given.allowed source length field member)

theorem rootIndex_free (member : ProofSyntax Const Δ (.app source field))
    (free : member.FunctionExtensionalityFree) :
    (rootIndex elementSelection arraySelection given source bottom length before field vector after member).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorConstructorProgram.rootIndex_free _ _ _ _ _ _ _ _ _ _ _
    (given.allowed_free source length field member free)

def programRootIndex (member : ProofSyntax Const Δ (.app source field)) :
    ProofSyntax Const Δ ((constructors (given.payload source)).rootIndex given.construct
      (IndexedContainerNativeVectorConstructorProgram.applySource
        (program elementSelection arraySelection given source bottom)
        length before (.app given.encode field) vector after) .top) := by
  let inventory := constructors (given.payload source)
  let point := IndexedContainerNativeVectorConstructorProgram.applySource
    (program elementSelection arraySelection given source bottom)
    length before (.app given.encode field) vector after
  let constructed := IndexedContainerNativeVectorConstructorProgram.constructed elementSelection arraySelection
    (given.payload source) given.construct bottom length before (.app given.encode field) vector after
  have body : ProofSyntax Const Δ (.app (inventory.rootAt given.construct .top) constructed) :=
    inventory.rootAt_intro given.construct .top constructed
      (rootIndex elementSelection arraySelection given source bottom length before field vector after member)
  have moved : ProofSyntax Const Δ (.app (inventory.rootAt given.construct .top) point) :=
    .impE (.eqPropER (.eqAppArg (inventory.rootAt given.construct .top)
      (computation elementSelection arraySelection given source bottom length before field vector after))) body
  exact inventory.rootAt_elim given.construct .top point moved

theorem programRootIndex_free (member : ProofSyntax Const Δ (.app source field))
    (free : member.FunctionExtensionalityFree) :
    (programRootIndex elementSelection arraySelection given source bottom length before field vector after member).FunctionExtensionalityFree := by
  unfold programRootIndex
  apply IndexedConstructorGuards.ConstructorPrograms.rootAt_elim_free
  constructor
  · exact computation_free _ _ _ _ _ _ _ _ _ _
  · apply IndexedConstructorGuards.ConstructorPrograms.rootAt_intro_free
    exact rootIndex_free _ _ _ _ _ _ _ _ _ _ _ free

variable (elements : Term Const Γ (E ⇒ .prop))

def admission (member : ProofSyntax Const Δ (.app source field))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint (given.payload source) elements given.construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint (given.payload source) elements given.construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint (given.payload source) elements given.construct) after)) :
    ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (IndexedContainerNativeVectorConstructorAdmission.domain (given.payload source) given.construct bottom)
      (numeral Γ 0) (encoded (given.payload source) length (.app given.encode field) (weakenCtx Γ original.zero))
      ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom)) :=
  IndexedContainerNativeVectorConstructorAdmission.sourceAdmission (given.payload source) given.construct bottom elements
    length (.app given.encode field) (weakenCtx Γ original.zero)
    ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom)
    (given.allowed source length field member)
    (sourceChildConditions elementSelection arraySelection (given.payload source) elements given.construct
      length (.app given.encode field) before vector after bottom (weakenCtx Γ original.zero)
      (given.allowed source length field member) premises arithmetic beforeMember vectorMember afterMember)

theorem admission_free (member : ProofSyntax Const Δ (.app source field))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint (given.payload source) elements given.construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint (given.payload source) elements given.construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint (given.payload source) elements given.construct) after))
    (memberFree : member.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (beforeFree : beforeMember.FunctionExtensionalityFree)
    (vectorFree : vectorMember.FunctionExtensionalityFree) (afterFree : afterMember.FunctionExtensionalityFree) :
    (admission elementSelection arraySelection given source bottom length before field vector after elements
      member premises arithmetic beforeMember vectorMember afterMember).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorConstructorAdmission.sourceAdmission_free
    (given.payload source) given.construct bottom elements length (.app given.encode field)
    (weakenCtx Γ original.zero) ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom)
    (given.allowed source length field member)
    (sourceChildConditions elementSelection arraySelection (given.payload source) elements given.construct
      length (.app given.encode field) before vector after bottom (weakenCtx Γ original.zero)
      (given.allowed source length field member) premises arithmetic beforeMember vectorMember afterMember)
    (given.allowed_free source length field member memberFree)
    (sourceChildConditions_free elementSelection arraySelection (given.payload source) elements given.construct
      length (.app given.encode field) before vector after bottom (weakenCtx Γ original.zero)
      (given.allowed source length field member) premises arithmetic beforeMember vectorMember afterMember
      (given.allowed_free source length field member memberFree) premisesFree arithmeticFree
      beforeFree vectorFree afterFree)

#print axioms Inputs.roundtrip
#print axioms Inputs.retraction
#print axioms Inputs.allowed
#print axioms program_subst
#print axioms rootIndex
#print axioms programRootIndex
#print axioms admission
#print axioms admission_free

namespace Controls

def padding : ClosedTerm Const E := IndexedContainerNativeVectorMethodReading.parameter 53 E

def inputs : Inputs [] N where
  raw := IndexedContainerNativeVectorMethodReading.parameter 50 _
  marker := original.zero
  branches := .lam (weaken padding)
  payloadSelection := IndexedContainerNativeVectorMethodReading.parameter 51 _
  fieldSelection := IndexedContainerNativeVectorMethodReading.parameter 52 _

def sourceZero : ClosedTerm Const (N ⇒ .prop) := .lam (.eq (.var .vz) (weaken original.zero))

def sourceZeroMember : ProofSyntax Const [] (.app sourceZero original.zero) := by
  apply ProofSyntax.impE (.eqPropER (.beta original.zero (.eq (.var .vz) (weaken original.zero))))
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl original.zero)
  simp only [instantiate, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]

theorem sourceZeroMember_free : sourceZeroMember.FunctionExtensionalityFree := by
  unfold sourceZeroMember
  exact ⟨True.intro,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩

def sourceAllowed := inputs.allowed sourceZero original.zero original.zero sourceZeroMember

theorem sourceAllowed_free : sourceAllowed.FunctionExtensionalityFree :=
  inputs.allowed_free sourceZero original.zero original.zero sourceZeroMember sourceZeroMember_free

def elementChoice : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)) :=
  IndexedContainerNativeVectorMethodReading.parameter 54 _
def arrayChoice : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)) :=
  IndexedContainerNativeVectorMethodReading.parameter 55 _

def originalProgramRoot := programRootIndex elementChoice arrayChoice inputs sourceZero padding
  original.zero padding original.zero original.nil padding sourceZeroMember

theorem originalProgramRoot_free : originalProgramRoot.FunctionExtensionalityFree :=
  programRootIndex_free _ _ _ _ _ _ _ _ _ _ _ sourceZeroMember_free

def providerPremises : List (ClosedFormula Const) := [
  SelectionProofs.principle inputs.payloadSelection,
  SelectionProofs.principle inputs.fieldSelection,
  ConstructorInjectivity.statement inputs.raw]

def representedRetraction : ProofSyntax Const providerPremises
    (GuardedRetraction.law inputs.decode inputs.encode (inputs.payload sourceZero)) :=
  inputs.retraction sourceZero (.hyp ⟨0,by decide⟩) (.hyp ⟨1,by decide⟩) (.hyp ⟨2,by decide⟩)

theorem representedRetraction_free : representedRetraction.FunctionExtensionalityFree :=
  inputs.retraction_free sourceZero _ _ _ True.intro True.intro True.intro

#print axioms sourceAllowed
#print axioms originalProgramRoot
#print axioms representedRetraction
#print axioms representedRetraction_free

end Controls

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorRepresentedAdmission
