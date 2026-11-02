import Mettapedia.Logic.HOL.RepresentedConstructorReflection
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionSemantics
import Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics

/-!
# An inhabited recursive-space model for field representation

The constructor and both selections have their intended interpretations in
one model. Two Boolean fields remain distinct after storage and recovery.
Bottom is outside the represented field image, refuting a decoder roundtrip
on the entire recursive carrier. These are semantic controls, not a source
cache reading or a native executable comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorFieldRepresentationControls
open ConstructorFieldRepresentation MixedConstructorPayloadMaps
open Mettapedia.Languages.HOLLight

inductive Base where | number | element | space
  deriving DecidableEq
abbrev N : Ty Base := .base .number
abbrev A : Ty Base := .base .element
abbrev E : Ty Base := .base .space
abbrev P := Payload N A
abbrev Number := ULift.{1} Nat
abbrev Element := ULift.{1} Bool
abbrev PayloadValue := (Number → Element → Number → ULift.{1,0} Prop) → ULift.{1,0} Prop
def filler : RecursiveSpaceSemantics.Relation PayloadValue := fun _ _ => False
abbrev Space := RecursiveSpaceSemantics.Carrier filler

def carriers : Base → Type 1
  | .number => Number
  | .element => Element
  | .space => Space
def inhabitants : (type : Base) → carriers type
  | .number => .up 0
  | .element => .up false
  | .space => RecursiveSpaceSemantics.bottom filler

inductive Const : Ty Base → Type where
  | construct : Const (N ⇒ P ⇒ (N ⇒ E) ⇒ E)
  | zero : Const N
  | bottom : Const E
  | payloadSelection : Const (SelectionProofs.Selection P)
  | fieldSelection : Const (SelectionProofs.Selection A)

noncomputable def meaning : {type : Ty Base} → Const type → Ty.denote.{0,0} carriers type
  | _, .construct => fun tag payload children => RecursiveSpaceSemantics.construct filler tag.down payload (fun n => children (.up n))
  | _, .zero => .up 0
  | _, .bottom => RecursiveSpaceSemantics.bottom filler
  | _, .payloadSelection => HOLLightStandardTheory.selectionOperation carriers inhabitants P
  | _, .fieldSelection => HOLLightStandardTheory.selectionOperation carriers inhabitants A
noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carriers meaning
def values : model.Valuation [] := fun entry => nomatch entry
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def raw : ClosedTerm Const (Raw N A (N ⇒ E) E) := .const .construct
def marker : ClosedTerm Const N := .const .zero
def branches : ClosedTerm Const (N ⇒ E) := .lam (.const .bottom)
def selectPayload : ClosedTerm Const (SelectionProofs.Selection P) := .const .payloadSelection
def selectField : ClosedTerm Const (SelectionProofs.Selection A) := .const .fieldSelection
def encode : ClosedTerm Const (A ⇒ E) := embedding raw marker branches
def decode : ClosedTerm Const (E ⇒ A) := decoder raw selectPayload selectField
def premises : List (ClosedFormula Const) := [SelectionProofs.principle selectPayload,
  SelectionProofs.principle selectField, ConstructorProjections.fieldInjective raw]

theorem payload_selection_holds : model.models (SelectionProofs.principle selectPayload) := by
  intro question _ field _ present
  exact HOLLightStandardTheory.selectionOperation_specified carriers inhabitants P question ⟨field,present⟩
theorem field_selection_holds : model.models (SelectionProofs.principle selectField) := by
  intro question _ field _ present
  exact HOLLightStandardTheory.selectionOperation_specified carriers inhabitants A question ⟨field,present⟩
theorem constructor_injective_holds : model.models (ConstructorProjections.fieldInjective raw) := by
  intro tag _ payload _ children _ otherTag _ otherPayload _ otherChildren _ same
  obtain ⟨_, data, child⟩ := (RecursiveSpaceSemantics.construct_injective filler otherTag.down otherPayload (fun n => otherChildren (.up n))
    tag.down payload (fun n => children (.up n))).mp same
  change model.Eqv P otherPayload payload ∧ model.Eqv (N ⇒ E) otherChildren children
  constructor
  · cases data; exact model.eqv_refl (full _ _)
  intro n _
  rcases n with ⟨n⟩
  exact congrFun child n

theorem assumptions_realizable : Soundness.SatisfiesHyps model values premises := by
  intro formula member
  simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (model.models_iff_denote_closed _ values).mp payload_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp field_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp constructor_injective_holds

def recoveryProof : ProofSyntax Const premises (leftInverse encode decode) :=
  roundtrip_law raw marker branches selectPayload selectField (.hyp ⟨0,by simp [premises]⟩)
    (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)
theorem recoveryProof_free : recoveryProof.FunctionExtensionalityFree := by
  apply roundtrip_law_free
  all_goals trivial
theorem recovery_holds : (model.denote (leftInverse encode decode) values).down :=
  Soundness.extDerivation_sound recoveryProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

def representedProof : ProofSyntax Const premises (GuardedRetraction.law decode encode (image encode)) :=
  RepresentedConstructorReflection.fieldLaw raw marker branches selectPayload selectField
    (.hyp ⟨0,by simp [premises]⟩) (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)
theorem representedProof_free : representedProof.FunctionExtensionalityFree := by
  apply RepresentedConstructorReflection.fieldLaw_free
  all_goals trivial
theorem represented_recovery_holds : (model.denote (GuardedRetraction.law decode encode (image encode)) values).down :=
  Soundness.extDerivation_sound representedProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem field_roundtrip (field : Element) :
    model.denote decode values (model.denote encode values field) = field := recovery_holds field trivial

theorem distinct_fields_remain_distinct :
    model.denote encode values (.up true) ≠ model.denote encode values (.up false) := by
  intro same
  have collision : (ULift.up true : Element) = .up false :=
    (field_roundtrip (.up true)).symm.trans ((congrArg (model.denote decode values) same).trans (field_roundtrip (.up false)))
  exact Bool.noConfusion (congrArg ULift.down collision)

theorem encoded_not_bottom (field : Element) : model.denote encode values field ≠ RecursiveSpaceSemantics.bottom filler :=
  RecursiveSpaceSemantics.construct_ne_bottom filler 0 (fun handler => handler (.up 0) field (.up 0)) (fun _ => RecursiveSpaceSemantics.bottom filler)
theorem bottom_not_in_image : ¬ (model.denote (.app (image encode) (.const .bottom)) values).down := by
  rintro ⟨field,_,same⟩
  exact encoded_not_bottom field same
theorem global_reverse_roundtrip_refused : ¬ ∀ stored : Space,
    model.denote encode values (model.denote decode values stored) = stored := by
  intro claimed
  exact encoded_not_bottom (model.denote decode values (RecursiveSpaceSemantics.bottom filler)) (claimed (RecursiveSpaceSemantics.bottom filler))

#print axioms assumptions_realizable
#print axioms field_roundtrip
#print axioms distinct_fields_remain_distinct
#print axioms global_reverse_roundtrip_refused
end Mettapedia.Logic.HOL.ConstructorFieldRepresentationControls
