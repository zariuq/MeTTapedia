import Mettapedia.Logic.HOL.FiniteConstructorFieldEmbeddingControls

/-!
# Recursive-space fixture with genuine successor arithmetic

The original typed constants embed unchanged, including its raw constructor
and two choice operations. The extension adds natural-number successor on
the same scalar and recursive-space carriers. Arithmetic values and provider
laws are verified in this standard model; no general source-context or native
consumer adequacy is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.VectorTreeSuccessorFixture
open FiniteConstructorFieldEmbeddingControls (Base N A E P Number Element Space carriers)
open VectorTreeFieldEmbedding ConstructorPredicateRepresentation

inductive Const : Ty Base → Type where
  | old {type : Ty Base} : FiniteConstructorFieldEmbeddingControls.Const type → Const type
  | successor : Const (N ⇒ N)

noncomputable def meaning : {type : Ty Base} → Const type → Ty.denote.{0,0} carriers type
  | _,.old constant => FiniteConstructorFieldEmbeddingControls.meaning constant
  | _,.successor => fun n => ULift.up (n.down+1)
noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carriers meaning

def values : model.Valuation [] := fun index => nomatch index
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def embed {Γ : Ctx Base} {type : Ty Base} (term : Term FiniteConstructorFieldEmbeddingControls.Const Γ type) :
    Term Const Γ type := mapConst Const.old term

def given : Inputs Const [] N A E where
  raw := embed FiniteConstructorFieldEmbeddingControls.given.raw
  zero := embed FiniteConstructorFieldEmbeddingControls.given.zero
  children := embed FiniteConstructorFieldEmbeddingControls.given.children
  payloadSelection := embed FiniteConstructorFieldEmbeddingControls.given.payloadSelection
  fieldSelection := embed FiniteConstructorFieldEmbeddingControls.given.fieldSelection

def encode := given.encode
def decode := given.decode
def zero : ClosedTerm Const N := given.zero
def successor : ClosedTerm Const (N ⇒ N) := .const .successor
def one : ClosedTerm Const N := .app successor zero

def numeral : Nat → ClosedTerm Const N
  | 0 => zero
  | n+1 => .app successor (numeral n)

theorem zero_meaning : model.denote zero values = ULift.up 0 := rfl
theorem successor_meaning (n : Number) : model.denote successor values n = ULift.up (n.down+1) := rfl
theorem one_meaning : model.denote one values = ULift.up 1 := rfl
theorem one_ne_zero : model.denote one values ≠ model.denote zero values := by
  intro same
  exact Nat.noConfusion (congrArg ULift.down same)
theorem numeral_meaning (n : Nat) : model.denote (numeral n) values = ULift.up n := by
  induction n with
  | zero => rfl
  | succ n previous =>
    change ULift.up ((model.denote (numeral n) values).down+1) = ULift.up (n+1)
    rw [previous]

theorem payload_selection_holds : model.models (SelectionProofs.principle given.payloadSelection) := by
  exact FiniteConstructorFieldEmbeddingControls.payload_selection_holds

theorem field_selection_holds : model.models (SelectionProofs.principle given.fieldSelection) := by
  exact FiniteConstructorFieldEmbeddingControls.field_selection_holds

theorem constructor_injective_holds : model.models (ConstructorProjections.fieldInjective given.raw) := by
  exact FiniteConstructorFieldEmbeddingControls.constructor_injective_holds


def premises : List (ClosedFormula Const) := [SelectionProofs.principle given.payloadSelection,
  SelectionProofs.principle given.fieldSelection,ConstructorProjections.fieldInjective given.raw]

theorem assumptions_realizable : Soundness.SatisfiesHyps model values premises := by
  intro formula present
  simp only [premises,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  · exact (model.models_iff_denote_closed _ values).mp payload_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp field_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp constructor_injective_holds

def recoveryProof : ProofSyntax Const premises (ConstructorFieldRepresentation.leftInverse encode decode) :=
  given.roundtripLaw (.hyp ⟨0,by simp [premises]⟩) (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)
theorem recoveryProof_free : recoveryProof.FunctionExtensionalityFree := by
  apply Inputs.roundtripLaw_free
  all_goals trivial

theorem field_roundtrip (field : Element) : model.denote decode values (model.denote encode values field) = field :=
  FiniteConstructorFieldEmbeddingControls.field_roundtrip field

theorem distinct_fields : model.denote encode values (ULift.up true) ≠ model.denote encode values (ULift.up false) :=
  FiniteConstructorFieldEmbeddingControls.distinct_fields

def onlyTrue : ClosedTerm Const (A ⇒ .prop) := embed FiniteConstructorFieldEmbeddingControls.onlyTrue
def noFields : ClosedTerm Const (A ⇒ .prop) := embed FiniteConstructorFieldEmbeddingControls.noFields

theorem accepted_true :
    (model.denote (given.predicate onlyTrue) values (model.denote encode values (ULift.up true))).down :=
  FiniteConstructorFieldEmbeddingControls.accepted_true

theorem rejected_false :
    ¬ (model.denote (given.predicate onlyTrue) values (model.denote encode values (ULift.up false))).down :=
  FiniteConstructorFieldEmbeddingControls.rejected_false

theorem empty_predicate_refuses (stored : Space) :
    ¬ (model.denote (given.predicate noFields) values stored).down :=
  FiniteConstructorFieldEmbeddingControls.empty_predicate_refuses stored

theorem successor_injective : Function.Injective (model.denote successor values) := by
  intro first second same
  apply ULift.ext
  exact Nat.succ.inj (congrArg ULift.down same)

theorem zero_not_successor (n : Number) : model.denote zero values ≠ model.denote successor values n := by
  intro same
  exact Nat.noConfusion (congrArg ULift.down same)

theorem numeral_injective : Function.Injective (fun n => model.denote (numeral n) values) := by
  intro first second same
  have numbers := congrArg ULift.down same
  simpa only [numeral_meaning] using numbers

#print axioms full
#print axioms numeral_meaning
#print axioms assumptions_realizable
#print axioms recoveryProof_free
#print axioms distinct_fields
#print axioms accepted_true
#print axioms rejected_false
#print axioms empty_predicate_refuses
#print axioms successor_injective
#print axioms zero_not_successor
end Mettapedia.Logic.HOL.VectorTreeSuccessorFixture
