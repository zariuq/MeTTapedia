import Mettapedia.Logic.HOL.VectorTreeFieldEmbedding
import Mettapedia.Logic.HOL.ConstructorPredicateRepresentationSemantics
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionSemantics
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics

/-!
# Full-signature field storage with distinct answers and guarded recovery

The raw carrier model uses the complete solved/branch payload type. Its
retained selection and constructor premises hold. Two Boolean answers are
stored distinctly, the original source predicate remains restrictive, and
bottom has no represented source witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorFieldEmbeddingControls
open Mettapedia.Languages.HOLLight
open VectorTreeFieldEmbedding ConstructorPredicateRepresentation

inductive Base where | number | answer | space
abbrev N : Ty Base := .base .number
abbrev A : Ty Base := .base .answer
abbrev E : Ty Base := .base .space
abbrev Signature := rawSignature N A
abbrev P : Ty Base := FiniteConstructorEncoding.payloadType Signature
abbrev Number := ULift.{1} Nat
abbrev Element := ULift.{1} Bool
abbrev PayloadValue := (Element → ULift.{1,0} Prop) →
  (Number → Number → ULift.{1,0} Prop) → ULift.{1,0} Prop
def filler : RecursiveSpaceSemantics.Relation PayloadValue := fun _ _ => False
abbrev Space := RecursiveSpaceSemantics.Carrier filler

def carriers : Base → Type 1
  | .number => Number
  | .answer => Element
  | .space => Space
def inhabitants : (type : Base) → carriers type
  | .number => .up 0
  | .answer => .up false
  | .space => RecursiveSpaceSemantics.bottom filler

inductive Const : Ty Base → Type where
  | construct : Const (N ⇒ P ⇒ (N ⇒ E) ⇒ E)
  | zero : Const N
  | bottom : Const E
  | answer (value : Bool) : Const A
  | payloadSelection : Const (SelectionProofs.Selection P)
  | fieldSelection : Const (SelectionProofs.Selection A)

noncomputable def meaning : {type : Ty Base} → Const type → Ty.denote.{0,0} carriers type
  | _, .construct => fun tag payload children => RecursiveSpaceSemantics.construct filler tag.down payload (fun n => children (.up n))
  | _, .zero => .up 0
  | _, .bottom => RecursiveSpaceSemantics.bottom filler
  | _, .answer value => .up value
  | _, .payloadSelection => HOLLightStandardTheory.selectionOperation carriers inhabitants P
  | _, .fieldSelection => HOLLightStandardTheory.selectionOperation carriers inhabitants A
noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carriers meaning
def values : model.Valuation [] := fun impossible => nomatch impossible
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def given : Inputs Const [] N A E where
  raw := .const .construct
  zero := .const .zero
  children := .lam (.const .bottom)
  payloadSelection := .const .payloadSelection
  fieldSelection := .const .fieldSelection
def encode := given.encode
def decode := given.decode
def premises : List (ClosedFormula Const) := [SelectionProofs.principle given.payloadSelection,
  SelectionProofs.principle given.fieldSelection,ConstructorProjections.fieldInjective given.raw]

theorem payload_selection_holds : model.models (SelectionProofs.principle given.payloadSelection) := by
  intro question _ field _ present
  exact HOLLightStandardTheory.selectionOperation_specified carriers inhabitants P question ⟨field,present⟩
theorem field_selection_holds : model.models (SelectionProofs.principle given.fieldSelection) := by
  intro question _ field _ present
  exact HOLLightStandardTheory.selectionOperation_specified carriers inhabitants A question ⟨field,present⟩
theorem constructor_injective_holds : model.models (ConstructorProjections.fieldInjective given.raw) := by
  intro tag _ payload _ children _ otherTag _ otherPayload _ otherChildren _ same
  obtain ⟨_, data, child⟩ := (RecursiveSpaceSemantics.construct_injective filler otherTag.down otherPayload (fun n => otherChildren (.up n))
    tag.down payload (fun n => children (.up n))).mp same
  change model.Eqv P otherPayload payload ∧ model.Eqv (N ⇒ E) otherChildren children
  constructor
  · cases data
    exact model.eqv_refl (full _ _)
  · intro n _
    rcases n with ⟨n⟩
    exact congrFun child n

theorem assumptions_realizable : Soundness.SatisfiesHyps model values premises := by
  intro formula member
  simp only [premises,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (model.models_iff_denote_closed _ values).mp payload_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp field_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp constructor_injective_holds

def recoveryProof : ProofSyntax Const premises (ConstructorFieldRepresentation.leftInverse encode decode) :=
  given.roundtripLaw (.hyp ⟨0,by simp [premises]⟩) (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)
theorem recoveryProof_free : recoveryProof.FunctionExtensionalityFree := by
  apply Inputs.roundtripLaw_free
  all_goals trivial
theorem recovery_holds : (model.denote (ConstructorFieldRepresentation.leftInverse encode decode) values).down :=
  Soundness.extDerivation_sound recoveryProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem field_roundtrip (field : Element) :
    model.denote decode values (model.denote encode values field) = field := recovery_holds field trivial

theorem distinct_fields : model.denote encode values (.up true) ≠ model.denote encode values (.up false) := by
  intro same
  have collision : (ULift.up true : Element) = .up false :=
    (field_roundtrip (.up true)).symm.trans ((congrArg (model.denote decode values) same).trans (field_roundtrip (.up false)))
  exact Bool.noConfusion (congrArg ULift.down collision)

theorem encoded_not_bottom (field : Element) : model.denote encode values field ≠ RecursiveSpaceSemantics.bottom filler :=
  RecursiveSpaceSemantics.construct_ne_bottom filler 0 (fun solved _branch => solved field) (fun _ => RecursiveSpaceSemantics.bottom filler)

def onlyTrue : ClosedTerm Const (A ⇒ .prop) := .lam (.eq (.var .vz) (.const (.answer true)))
def noFields : ClosedTerm Const (A ⇒ .prop) := .lam .bot

theorem accepted_true :
    (model.denote (given.predicate onlyTrue) values (model.denote encode values (.up true))).down :=
  (lift_denote_full model full encode onlyTrue values _).mpr ⟨.up true,rfl,rfl⟩

theorem rejected_false :
    ¬ (model.denote (given.predicate onlyTrue) values (model.denote encode values (.up false))).down := by
  intro present
  obtain ⟨field,valid,same⟩ := (lift_denote_full model full encode onlyTrue values _).mp present
  have fields := (field_roundtrip field).symm.trans ((congrArg (model.denote decode values) same).trans (field_roundtrip (.up false)))
  change field = ULift.up true at valid
  exact Bool.noConfusion (congrArg ULift.down (valid.symm.trans fields))

theorem bottom_refused (source : ClosedTerm Const (A ⇒ .prop)) :
    ¬ (model.denote (given.predicate source) values (RecursiveSpaceSemantics.bottom filler)).down := by
  intro present
  obtain ⟨field,_,same⟩ := (lift_denote_full model full encode source values _).mp present
  exact encoded_not_bottom field same

theorem empty_predicate_refuses (stored : Space) :
    ¬ (model.denote (given.predicate noFields) values stored).down :=
  empty_guard model encode noFields values (fun _ impossible => impossible) stored

def wrongDecoder : ClosedTerm Const (E ⇒ A) := .lam (.const (.answer false))
theorem wrong_decoder_refused : ¬ ∀ field : Element,
    model.denote wrongDecoder values (model.denote encode values field) = field := by
  intro claimed
  exact Bool.noConfusion (congrArg ULift.down (claimed (.up true)))

theorem explicit_other_fields (first last : ClosedTerm Const N) (field : ClosedTerm Const A) :
    FiniteConstructorFieldEmbedding.insertField (fields := [N,A,N]) (.vs .vz) field (first,last,PUnit.unit) =
      (first,field,last,PUnit.unit) := rfl

theorem selected_field_recovered (first last : ClosedTerm Const N) (field : ClosedTerm Const A) :
    FiniteConstructorEncoding.argumentAt (fields := [N,A,N]) (.vs .vz)
      (FiniteConstructorFieldEmbedding.insertField (.vs .vz) field (first,last,PUnit.unit)) = field :=
  FiniteConstructorFieldEmbedding.insertedField _ _ _

theorem empty_inventory_has_no_embedding_port : ¬ Nonempty (Fin (0 : Nat)) := by
  rintro ⟨impossible⟩
  exact Fin.elim0 impossible

#print axioms assumptions_realizable
#print axioms recoveryProof_free
#print axioms distinct_fields
#print axioms rejected_false
#print axioms bottom_refused
#print axioms wrong_decoder_refused
end Mettapedia.Logic.HOL.FiniteConstructorFieldEmbeddingControls
