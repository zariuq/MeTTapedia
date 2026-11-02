import Mettapedia.Logic.HOL.ConstructorPredicateRepresentationSemantics
import Mettapedia.Logic.HOL.ConstructorFieldRepresentationControls

/-!
# Distinct represented fields and empty predicates

The actual recursive-space constructor and both source selections satisfy
the retained roundtrip premises. The subtype equivalence uses those programs
to encode and recover two different fields. Bottom remains outside the image,
and an empty source predicate admits no target values.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ConstructorPredicateRepresentationControls
open ConstructorFieldRepresentationControls
open ConstructorPredicateRepresentation

def allFields : ClosedTerm Const (A ⇒ .prop) := .lam .top
def represented : ClosedTerm Const (E ⇒ .prop) := lift encode allFields

noncomputable def comparison := subtypeEquivOfProof model full encode decode allFields values
  recoveryProof assumptions_realizable

def trueField : {field : Element // (model.denote allFields values field).down} := ⟨.up true,True.intro⟩
def falseField : {field : Element // (model.denote allFields values field).down} := ⟨.up false,True.intro⟩

theorem true_encoded : (comparison trueField).val = model.denote encode values (.up true) := rfl
theorem false_encoded : (comparison falseField).val = model.denote encode values (.up false) := rfl

theorem true_recovered : (comparison.symm (comparison trueField)).val = ULift.up true :=
  congrArg Subtype.val (comparison.left_inv trueField)
theorem false_recovered : (comparison.symm (comparison falseField)).val = ULift.up false :=
  congrArg Subtype.val (comparison.left_inv falseField)

theorem distinct_encoded_values : (comparison trueField).val ≠ (comparison falseField).val :=
  distinct_fields_remain_distinct

theorem bottom_refused :
    ¬ (model.denote represented values (Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.bottom filler)).down := by
  intro present
  obtain ⟨field,_,same⟩ := (lift_denote_full model full encode allFields values _).mp present
  exact encoded_not_bottom field same

def noFields : ClosedTerm Const (A ⇒ .prop) := .lam .bot

theorem empty_predicate_refuses (stored : Space) :
    ¬ (model.denote (lift encode noFields) values stored).down :=
  empty_guard model encode noFields values (fun _ impossible => impossible) stored

#print axioms comparison
#print axioms true_recovered
#print axioms false_recovered
#print axioms distinct_encoded_values
#print axioms bottom_refused
#print axioms empty_predicate_refuses
end Mettapedia.Logic.HOL.ConstructorPredicateRepresentationControls
