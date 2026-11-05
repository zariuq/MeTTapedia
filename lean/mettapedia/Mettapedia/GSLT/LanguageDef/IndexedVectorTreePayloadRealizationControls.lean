import Mettapedia.GSLT.LanguageDef.IndexedVectorTreePayloadRealization
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionSemantics
import Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics

/-!
# Finite and infinite represented-payload profiles

The existing recursive-space interpretation and standard selection operations
are instantiated at an arbitrary inhabited element carrier. All three source
provider principles hold in that model. Finite and infinite restrictive
predicates then exercise the model-relative payload subtype and its actual
constructor-based encoding. A nonempty restricted numeric guard is refused.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreePayloadRealizationControls

open Mettapedia.Logic.HOL Mettapedia.Languages.HOLLight
open Mettapedia.TypeTheory.IndexedPositiveContainer

noncomputable section

inductive Base where | number | answer | space
abbrev N : Ty Base := .base .number
abbrev A : Ty Base := .base .answer
abbrev E : Ty Base := .base .space
abbrev P : Ty Base := FiniteConstructorEncoding.payloadType (VectorTreeFieldEmbedding.rawSignature N A)
abbrev Number := ULift.{1} Nat
abbrev ElementValue (Element : Type) := ULift.{1} Element
abbrev PayloadValue (Element : Type) :=
  (ElementValue Element → ULift.{1,0} Prop) →
    (Number → Number → ULift.{1,0} Prop) → ULift.{1,0} Prop
def filler (Element : Type) : RecursiveSpaceSemantics.Relation (PayloadValue Element) := fun _ _ => False
abbrev Space (Element : Type) := RecursiveSpaceSemantics.Carrier (filler Element)

def carriers (Element : Type) : Base → Type 1
  | .number => Number
  | .answer => ElementValue Element
  | .space => Space Element

def inhabitants (Element : Type) (initial : Element) : (type : Base) → carriers Element type
  | .number => .up 0
  | .answer => .up initial
  | .space => RecursiveSpaceSemantics.bottom (filler Element)

inductive Const (Element : Type) : Ty Base → Type where
  | construct : Const Element (N ⇒ P ⇒ (N ⇒ E) ⇒ E)
  | zero : Const Element N
  | successor : Const Element (N ⇒ N)
  | bottom : Const Element E
  | payloadSelection : Const Element (SelectionProofs.Selection P)
  | fieldSelection : Const Element (SelectionProofs.Selection A)
  | predicate (question : Element → Prop) : Const Element (A ⇒ .prop)

def meaning (Element : Type) (initial : Element) :
    {type : Ty Base} → Const Element type → Ty.denote.{0,0} (carriers Element) type
  | _,.construct => fun tag payload children =>
      RecursiveSpaceSemantics.construct (filler Element) tag.down payload (fun n => children (.up n))
  | _,.zero => .up 0
  | _,.successor => fun n => .up (n.down+1)
  | _,.bottom => RecursiveSpaceSemantics.bottom (filler Element)
  | _,.payloadSelection => HOLLightStandardTheory.selectionOperation (carriers Element) (inhabitants Element initial) P
  | _,.fieldSelection => HOLLightStandardTheory.selectionOperation (carriers Element) (inhabitants Element initial) A
  | _,.predicate question => fun value => .up (question value.down)

def model (Element : Type) (initial : Element) : HenkinModel.{0,0,0} Base (Const Element) :=
  .standard (carriers Element) (meaning Element initial)
def values (Element : Type) (initial : Element) : (model Element initial).Valuation [] :=
  fun impossible => nomatch impossible
theorem full (Element : Type) (initial : Element) : (model Element initial).FullDomains :=
  HenkinModel.fullDomains_standard _ _

def zero (Element : Type) : ClosedTerm (Const Element) N := .const .zero
def successor (Element : Type) : ClosedTerm (Const Element) (N ⇒ N) := .const .successor
def source (Element : Type) (question : Element → Prop) : ClosedTerm (Const Element) (A ⇒ .prop) :=
  .const (.predicate question)
def numberGuard (Element : Type) : ClosedTerm (Const Element) (N ⇒ .prop) := .lam .top

def numbers (Element : Type) (initial : Element) :
    IndexedVectorTreePayloadRealization.Numbers (model Element initial) (zero Element) (successor Element) where
  equivalence := Equiv.ulift.symm
  zero_correct := rfl
  successor_correct := fun _ => rfl

def given (Element : Type) : VectorTreeFieldEmbedding.Inputs (Const Element) [] N A E where
  raw := .const .construct
  zero := zero Element
  children := .lam (.const .bottom)
  payloadSelection := .const .payloadSelection
  fieldSelection := .const .fieldSelection

def premises (Element : Type) : List (ClosedFormula (Const Element)) :=
  [SelectionProofs.principle (given Element).payloadSelection,
   SelectionProofs.principle (given Element).fieldSelection,
   ConstructorProjections.fieldInjective (given Element).raw]

theorem payload_selection_holds (Element : Type) (initial : Element) :
    (model Element initial).models (SelectionProofs.principle (given Element).payloadSelection) := by
  intro question _ field _ present
  exact HOLLightStandardTheory.selectionOperation_specified (carriers Element) (inhabitants Element initial) P question ⟨field,present⟩

theorem field_selection_holds (Element : Type) (initial : Element) :
    (model Element initial).models (SelectionProofs.principle (given Element).fieldSelection) := by
  intro question _ field _ present
  exact HOLLightStandardTheory.selectionOperation_specified (carriers Element) (inhabitants Element initial) A question ⟨field,present⟩

theorem constructor_injective_holds (Element : Type) (initial : Element) :
    (model Element initial).models (ConstructorProjections.fieldInjective (given Element).raw) := by
  intro tag _ payload _ children _ otherTag _ otherPayload _ otherChildren _ same
  obtain ⟨_,data,child⟩ := (RecursiveSpaceSemantics.construct_injective (filler Element)
    otherTag.down otherPayload (fun n => otherChildren (.up n)) tag.down payload (fun n => children (.up n))).mp same
  change (model Element initial).Eqv P otherPayload payload ∧
    (model Element initial).Eqv (N ⇒ E) otherChildren children
  constructor
  · cases data
    exact (model Element initial).eqv_refl (full Element initial _ _)
  · intro n _
    rcases n with ⟨n⟩
    exact congrFun child n

theorem assumptions_realizable (Element : Type) (initial : Element) :
    Soundness.SatisfiesHyps (model Element initial) (values Element initial) (premises Element) := by
  intro formula member
  simp only [premises,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ((model Element initial).models_iff_denote_closed _ (values Element initial)).mp (payload_selection_holds Element initial)
  · exact ((model Element initial).models_iff_denote_closed _ (values Element initial)).mp (field_selection_holds Element initial)
  · exact ((model Element initial).models_iff_denote_closed _ (values Element initial)).mp (constructor_injective_holds Element initial)

def recoveryProof (Element : Type) : ProofSyntax (Const Element) (premises Element)
    (ConstructorFieldRepresentation.leftInverse (given Element).encode (given Element).decode) :=
  (given Element).roundtripLaw (.hyp ⟨0,by simp [premises]⟩) (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)

theorem field_roundtrip (Element : Type) (initial : Element) (field : ElementValue Element) :
    (model Element initial).denote (given Element).decode (values Element initial)
      ((model Element initial).denote (given Element).encode (values Element initial) field) = field := by
  have sound := Soundness.extDerivation_sound (recoveryProof Element).erase
    ((model Element initial).functionsRespectEqv_of_fullDomains (full Element initial))
    (fun _ => trivial) (assumptions_realizable Element initial)
  exact sound field trivial

theorem encode_injective (Element : Type) (initial : Element) :
    Function.Injective ((model Element initial).denote (given Element).encode (values Element initial)) := by
  intro first second same
  exact (field_roundtrip Element initial first).symm.trans
    ((congrArg ((model Element initial).denote (given Element).decode (values Element initial)) same).trans
      (field_roundtrip Element initial second))

theorem encoded_not_bottom (Element : Type) (initial : Element) (field : ElementValue Element) :
    (model Element initial).denote (given Element).encode (values Element initial) field ≠
      RecursiveSpaceSemantics.bottom (filler Element) :=
  RecursiveSpaceSemantics.construct_ne_bottom (filler Element) 0
    (fun solved _branch => solved field) (fun _ => RecursiveSpaceSemantics.bottom (filler Element))

def interpreted (Element : Type) (initial : Element) (question : Element → Prop) :=
  IndexedVectorTreePayloadRealization.realization (model Element initial) (given Element)
    (source Element question) (values Element initial) (zero Element) (successor Element) (numbers Element initial)

theorem images (Element : Type) (initial : Element) (question : Element → Prop) :
    IndexedContainerPositionTerms.FieldImages (interpreted Element initial question)
      (IndexedVectorTreePayloadRealization.guards
        (IndexedVectorTreePayloadRealization.Payload (model Element initial) (source Element question) (values Element initial))
        (given Element) (source Element question) (numberGuard Element) (zero Element) (successor Element)) :=
  IndexedVectorTreePayloadRealization.fieldImages (model Element initial) (full Element initial) (given Element)
    (source Element question) (numberGuard Element) (values Element initial) (zero Element) (successor Element)
    (numbers Element initial) (fun _ => True.intro)

theorem injections (Element : Type) (initial : Element) (question : Element → Prop) :
    IndexedContainerPositionTerms.FieldInjective (interpreted Element initial question) :=
  IndexedVectorTreePayloadRealization.injections (model Element initial) (full Element initial) (given Element)
    (source Element question) (values Element initial) (zero Element) (successor Element) (numbers Element initial)
    (.hyp ⟨0,by simp [premises]⟩) (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)
    (assumptions_realizable Element initial)

theorem predicate_at_encoded (Element : Type) (initial : Element) (question : Element → Prop) (field : Element) :
    ((model Element initial).denote ((given Element).predicate (source Element question)) (values Element initial)
      ((model Element initial).denote (given Element).encode (values Element initial) (.up field))).down ↔ question field := by
  have image := ConstructorPredicateRepresentation.lift_denote_full (model Element initial) (full Element initial)
    (given Element).encode (source Element question) (values Element initial)
    ((model Element initial).denote (given Element).encode (values Element initial) (.up field))
  constructor
  · intro present
    obtain ⟨witness,valid,same⟩ := image.mp present
    have original := encode_injective Element initial same
    cases original
    exact valid
  · intro valid
    exact image.mpr ⟨.up field,valid,rfl⟩

def finiteQuestion (field : Fin 4) : Prop := field.val ≠ 0
theorem finite_accepts_one :
    ((model (Fin 4) 0).denote ((given (Fin 4)).predicate (source (Fin 4) finiteQuestion)) (values (Fin 4) 0)
      ((model (Fin 4) 0).denote (given (Fin 4)).encode (values (Fin 4) 0) (.up 1))).down :=
  (predicate_at_encoded (Fin 4) 0 finiteQuestion 1).mpr (by change (1 : Nat) ≠ 0; decide)
theorem finite_refuses_zero :
    ¬ ((model (Fin 4) 0).denote ((given (Fin 4)).predicate (source (Fin 4) finiteQuestion)) (values (Fin 4) 0)
      ((model (Fin 4) 0).denote (given (Fin 4)).encode (values (Fin 4) 0) (.up 0))).down :=
  fun member => (predicate_at_encoded (Fin 4) 0 finiteQuestion 0).mp member rfl

def finiteField (n : Fin 3) : IndexedVectorTreePayloadRealization.Payload
    (model (Fin 4) 0) (source (Fin 4) finiteQuestion) (values (Fin 4) 0) :=
  ⟨.up ⟨n.val+1,Nat.succ_lt_succ n.isLt⟩,Nat.succ_ne_zero n.val⟩
theorem three_distinct_finite_represented_fields {first second : Fin 3}
    (same : (interpreted (Fin 4) 0 finiteQuestion).value .payload (finiteField first) =
      (interpreted (Fin 4) 0 finiteQuestion).value .payload (finiteField second)) : first = second := by
  have fields := (injections (Fin 4) 0 finiteQuestion).value .payload same
  have naturals := congrArg (fun field => field.val.down.val) fields
  exact Fin.ext (Nat.succ.inj naturals)

def infiniteQuestion (field : Nat) : Prop := 0 < field
def positiveField (n : Nat) : IndexedVectorTreePayloadRealization.Payload
    (model Nat 0) (source Nat infiniteQuestion) (values Nat 0) := ⟨.up (n+1),Nat.zero_lt_succ n⟩
theorem infinitely_many_represented_fields {first second : Nat}
    (same : (interpreted Nat 0 infiniteQuestion).value .payload (positiveField first) =
      (interpreted Nat 0 infiniteQuestion).value .payload (positiveField second)) : first = second := by
  have fields := (injections Nat 0 infiniteQuestion).value .payload same
  have naturals := congrArg (fun field => field.val.down) fields
  exact Nat.succ.inj naturals

def restrictedNumbers (Element : Type) : ClosedTerm (Const Element) (N ⇒ .prop) :=
  .lam (.eq (.var .vz) (weakenCtx [N] (zero Element)))
theorem nonempty_restricted_numbers_accepts_zero :
    ((model Nat 0).denote (restrictedNumbers Nat) (values Nat 0) (.up 0)).down := rfl
theorem restricted_numbers_cannot_supply_images :
    ¬ Nonempty (IndexedContainerPositionTerms.FieldImages (interpreted Nat 0 infiniteQuestion)
      (IndexedVectorTreePayloadRealization.guards
        (IndexedVectorTreePayloadRealization.Payload (model Nat 0) (source Nat infiniteQuestion) (values Nat 0))
        (given Nat) (source Nat infiniteQuestion) (restrictedNumbers Nat) (zero Nat) (successor Nat))) := by
  rintro ⟨claimed⟩
  have one := IndexedVectorTreePayloadRealization.guard_on_numbers_of_images (model Nat 0) (given Nat)
    (source Nat infiniteQuestion) (restrictedNumbers Nat) (values Nat 0) (zero Nat) (successor Nat) (numbers Nat 0) claimed 1
  change (ULift.up 1 : Number) = .up 0 at one
  have impossible := congrArg ULift.down one
  cases impossible

#print axioms assumptions_realizable
#print axioms images
#print axioms injections
#print axioms finite_accepts_one
#print axioms finite_refuses_zero
#print axioms three_distinct_finite_represented_fields
#print axioms infinitely_many_represented_fields
#print axioms restricted_numbers_cannot_supply_images

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreePayloadRealizationControls
