import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorAdmission
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorSourceGuards
import Mettapedia.Logic.HOL.ConstructorFieldRepresentationControls
import Mettapedia.Logic.HOL.ConstructorPayloadTransport
import Mettapedia.Logic.HOL.MixedConstructorPayloadMapSemantics

/-!
# The original arbitrary field guard does not imply the storage image

The actual mixed-vector admission program permits both bottom and the stored
version of its decoded field when the caller predicate is full. Their payloads
are distinct, but lowering their fields through the constructed decoder gives
the same payload and hence the same lifted-constructor output.

The source-signature interpretation below reuses the existing recursive-space
field model's carriers and lifted operation. Unrelated source parameters have
explicit defaults; this is a counterexample to the original admission-domain
uniqueness statement, not a model of the complete active-child or method packet.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorRepresentedAdmissionControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V W parameter original)
open MixedConstructorPayloadMaps
open Mettapedia.Languages.HOLLight
open ConstructorFieldRepresentationControls (Number Space)

noncomputable def nativeModel := ConstructorFieldRepresentationControls.model
def nativeValues : nativeModel.Valuation [] := ConstructorFieldRepresentationControls.values
def nativeBottom : Space := RecursiveSpaceSemantics.bottom ConstructorFieldRepresentationControls.filler
noncomputable def decodedBottom := nativeModel.denote ConstructorFieldRepresentationControls.decode nativeValues nativeBottom
noncomputable def storedDecodedBottom : Space :=
  nativeModel.denote ConstructorFieldRepresentationControls.encode nativeValues decodedBottom
def nativeLifted := ConstructorPayloadTransport.constructor ConstructorFieldRepresentationControls.raw
  ConstructorFieldRepresentationControls.decode
def nativePayloadBottom := pack ConstructorFieldRepresentationControls.marker
  (.const ConstructorFieldRepresentationControls.Const.bottom) ConstructorFieldRepresentationControls.marker
def nativePayloadStored := pack ConstructorFieldRepresentationControls.marker
  (.app ConstructorFieldRepresentationControls.encode
    (.app ConstructorFieldRepresentationControls.decode (.const ConstructorFieldRepresentationControls.Const.bottom)))
  ConstructorFieldRepresentationControls.marker

def carrier : Base → Type 1
  | .number => Number
  | .element => Space
  | .vector => List Space
  | .evidence => Space
def inhabitant : (sort : Base) → carrier sort
  | .number => ULift.up 0
  | .element | .evidence => nativeBottom
  | .vector => []
def defaultValue : (type : Ty Base) → Ty.denote.{0,0} carrier type
  | .base sort => inhabitant sort
  | .prop => ULift.up False
  | .arr _ result => fun _ => defaultValue result
abbrev Assignment := {type : Ty Base} → Const type → Ty.denote.{0,0} carrier type
def assign {type : Ty Base} (name : Nat) (value : Ty.denote.{0,0} carrier type) (previous : Assignment) : Assignment :=
  fun {other} symbol => match symbol with
    | .parameter actual _ => if actual = name then
        if same : other = type then same.symm ▸ value else previous symbol
      else previous symbol

abbrev SourceConstructor := N ⇒ FiniteConstructorEncoding.payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E
@[irreducible] noncomputable def meaning : Assignment :=
  assign 0 (type := N) (ULift.up 0)
    (assign 1 (type := N ⇒ N) (fun value => ULift.up (value.down + 1))
      (assign 25 (type := SourceConstructor) (nativeModel.denote nativeLifted nativeValues)
        (assign 26 (type := E) nativeBottom
          (assign 1000 (type := E) nativeBottom
            (assign 1001 (type := E) storedDecodedBottom (fun {_} _ => defaultValue _))))))
noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carrier meaning
def values : model.Valuation [] := fun index => nomatch index
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def sourceConstructor : ClosedTerm Const SourceConstructor := parameter 25 _
def sourceBottom : ClosedTerm Const E := parameter 26 _
def bottomTag : ClosedTerm Const E := parameter 1000 _
def storedTag : ClosedTerm Const E := parameter 1001 _
def payload : ClosedTerm Const (E ⇒ .prop) := .lam .top
def children : ClosedTerm Const (N ⇒ E) := .lam (.const (.parameter 26 E))
def sourceSignature := IndexedContainerNativeVectorConstructorAdmission.signature payload sourceConstructor sourceBottom
def sourceDomain := IndexedContainerNativeVectorConstructorAdmission.domain payload sourceConstructor sourceBottom
def encoded (tag : ClosedTerm Const E) := IndexedContainerNativeVectorChildGuard.encoded payload original.zero tag original.zero

def topMember (tag : ClosedTerm Const E) : ProofSyntax Const [] (.app payload tag) :=
  .impE (.eqPropER (.beta tag .top)) .topI
def sourceAllowed (tag : ClosedTerm Const E) : ProofSyntax Const []
    (IndexedContainerNativeVectorPositionReading.sourceAllowed payload original.zero tag original.zero) :=
  IndexedContainerNativeVectorSourceGuards.allowedOfTag payload original.zero tag (topMember tag)

def sourcePadding (tag : ClosedTerm Const E) : ProofSyntax Const [] (sourceSignature.paddingConditions (encoded tag) children) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  exact ProofSyntax.beta (Const := Const) (Γ := [N]) (σ := N) (τ := E)
    (.var .vz) (.const (Const.parameter 26 E))

def sourceAdmission (tag : ClosedTerm Const E) : ProofSyntax Const []
    (GuardedConstructorProjections.admitted sourceDomain original.zero (encoded tag) children) :=
  .impE (.eqPropER (sourceSignature.constructorAdmission_at original.zero (encoded tag) children))
    (.andI (IndexedContainerNativeVectorConstructorAdmission.sourceShape payload sourceConstructor sourceBottom
      original.zero tag original.zero (sourceAllowed tag)) (sourcePadding tag))

theorem sourceAdmission_holds (tag : ClosedTerm Const E) :
    (model.denote (GuardedConstructorProjections.admitted sourceDomain original.zero (encoded tag) children) values).down :=
  Soundness.extDerivation_sound (sourceAdmission tag).erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) (fun _ absent => nomatch absent)

theorem zero_denote : model.denote original.zero values = ULift.up 0 := by unfold model meaning; rfl
theorem bottom_denote : model.denote sourceBottom values = nativeBottom := by unfold model meaning; rfl
theorem bottomTag_denote : model.denote bottomTag values = nativeBottom := by unfold model meaning; rfl
theorem storedTag_denote : model.denote storedTag values = storedDecodedBottom := by unfold model meaning; rfl
theorem constructor_denote : model.denote sourceConstructor values = nativeModel.denote nativeLifted nativeValues := by
  unfold model meaning
  rfl
theorem children_denote : model.denote children values = fun _ => nativeBottom := by
  unfold model meaning
  rfl

theorem encoded_bottom_denote : model.denote (encoded bottomTag) values = nativeModel.denote nativePayloadBottom nativeValues := by
  funext handler
  change handler (model.denote original.zero values) (model.denote bottomTag values) (model.denote original.zero values) = _
  rw [zero_denote,bottomTag_denote]
  rfl
theorem encoded_stored_denote : model.denote (encoded storedTag) values = nativeModel.denote nativePayloadStored nativeValues := by
  funext handler
  change handler (model.denote original.zero values) (model.denote storedTag values) (model.denote original.zero values) = _
  rw [zero_denote,storedTag_denote]
  rfl

theorem stored_bottom_different : storedDecodedBottom ≠ nativeBottom :=
  ConstructorFieldRepresentationControls.encoded_not_bottom decodedBottom

theorem original_payloads_distinct : model.denote (encoded storedTag) values ≠ model.denote (encoded bottomTag) values := by
  rw [encoded_stored_denote,encoded_bottom_denote]
  intro equal
  have observed := congrFun equal (fun _ field _ => ULift.up (field = nativeBottom))
  change ULift.up (storedDecodedBottom = nativeBottom) = ULift.up (nativeBottom = nativeBottom) at observed
  exact stored_bottom_different (Eq.mpr (congrArg ULift.down observed) rfl)

theorem lowered_payloads_equal :
    nativeModel.denote (mapPayload ConstructorFieldRepresentationControls.decode nativePayloadStored) nativeValues =
      nativeModel.denote (mapPayload ConstructorFieldRepresentationControls.decode nativePayloadBottom) nativeValues := by
  rw [mapPayload_denote,mapPayload_denote]
  funext handler
  change handler (ULift.up 0) (nativeModel.denote ConstructorFieldRepresentationControls.decode nativeValues storedDecodedBottom) (ULift.up 0) =
    handler (ULift.up 0) decodedBottom (ULift.up 0)
  exact congrArg (fun field => handler (ULift.up 0) field (ULift.up 0))
    (ConstructorFieldRepresentationControls.field_roundtrip decodedBottom)

theorem nativeComputation (input : ClosedTerm ConstructorFieldRepresentationControls.Const
    (Payload ConstructorFieldRepresentationControls.N ConstructorFieldRepresentationControls.E)) :
    nativeModel.denote (ConstructorProjections.apply nativeLifted ConstructorFieldRepresentationControls.marker input
      ConstructorFieldRepresentationControls.branches) nativeValues =
    nativeModel.denote (ConstructorPayloadTransport.value ConstructorFieldRepresentationControls.raw
      ConstructorFieldRepresentationControls.decode ConstructorFieldRepresentationControls.marker input
      ConstructorFieldRepresentationControls.branches) nativeValues :=
  Soundness.extDerivation_sound (ConstructorPayloadTransport.computation (Δ := []) ConstructorFieldRepresentationControls.raw
    ConstructorFieldRepresentationControls.decode ConstructorFieldRepresentationControls.marker input
    ConstructorFieldRepresentationControls.branches).erase
    (nativeModel.functionsRespectEqv_of_fullDomains ConstructorFieldRepresentationControls.full)
    (fun _ => trivial) (fun _ absent => nomatch absent)

theorem native_constructor_collision :
    nativeModel.denote (ConstructorProjections.apply nativeLifted ConstructorFieldRepresentationControls.marker nativePayloadStored
      ConstructorFieldRepresentationControls.branches) nativeValues =
    nativeModel.denote (ConstructorProjections.apply nativeLifted ConstructorFieldRepresentationControls.marker nativePayloadBottom
      ConstructorFieldRepresentationControls.branches) nativeValues := by
  rw [nativeComputation,nativeComputation]
  change nativeModel.denote ConstructorFieldRepresentationControls.raw nativeValues (ULift.up 0)
      (nativeModel.denote (mapPayload ConstructorFieldRepresentationControls.decode nativePayloadStored) nativeValues)
      (nativeModel.denote ConstructorFieldRepresentationControls.branches nativeValues) = _
  rw [lowered_payloads_equal]
  rfl

theorem original_constructor_collision :
    model.denote (ConstructorProjections.apply sourceConstructor original.zero (encoded storedTag) children) values =
      model.denote (ConstructorProjections.apply sourceConstructor original.zero (encoded bottomTag) children) values := by
  change model.denote sourceConstructor values (model.denote original.zero values) (model.denote (encoded storedTag) values)
      (model.denote children values) =
    model.denote sourceConstructor values (model.denote original.zero values) (model.denote (encoded bottomTag) values)
      (model.denote children values)
  rw [constructor_denote,zero_denote,encoded_stored_denote,encoded_bottom_denote,children_denote]
  exact native_constructor_collision

theorem original_guarded_uniqueness_refuted :
    ¬ model.models (GuardedConstructorProjections.fieldInjective sourceConstructor sourceDomain) := by
  intro claimed
  have reflects := (GuardedConstructorProjections.fieldInjective_models_full model full sourceConstructor sourceDomain values).mp claimed
  have bottomAdmitted := sourceAdmission_holds bottomTag
  have storedAdmitted := sourceAdmission_holds storedTag
  have collision := original_constructor_collision
  change model.denote sourceConstructor values (model.denote original.zero values) (model.denote (encoded storedTag) values)
      (model.denote children values) =
    model.denote sourceConstructor values (model.denote original.zero values) (model.denote (encoded bottomTag) values)
      (model.denote children values) at collision
  exact original_payloads_distinct (reflects _ _ _ bottomAdmitted _ _ _ storedAdmitted collision).1

#print axioms sourceAdmission_holds
#print axioms original_payloads_distinct
#print axioms original_constructor_collision
#print axioms original_guarded_uniqueness_refuted
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorRepresentedAdmissionControls
