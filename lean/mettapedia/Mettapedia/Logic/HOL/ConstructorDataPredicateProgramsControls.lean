import Mettapedia.Logic.HOL.ConstructorDataPredicatePrograms
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Retained admission at a payload identified by beta conversion

The two constructor occurrences have the same field types but distinct data
conditions. Admission of a beta-wrapped payload retains the original payload,
its field proof, and its explicit equation to the selected encoding. The
standard Boolean model separates wrong occurrences, changed fields, and a
payload outside the constructor image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorDataPredicates.ProgramControls

open FiniteConstructorEncoding
open FiniteConstructorEncoding.Controls

theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def first : Fin signature.length := ⟨0, by decide⟩
def second : Fin signature.length := ⟨1, by decide⟩

def conditions : Conditions Constants [] signature
  | ⟨0, _⟩ => .lam (.lam (.var (.vs .vz)))
  | ⟨1, _⟩ => .lam (.lam .bot)

def packed : ClosedTerm Constants (payloadType signature) :=
  encode signature first fields

def payload : ClosedTerm Constants (payloadType signature) :=
  .app (.lam (.var .vz)) packed

def payloadEquation : ProofSyntax Constants [] (.eq payload packed) :=
  .beta packed (.var .vz)

def conditionEquation : ProofSyntax Constants []
    (.eq (applyArguments _ (conditions first) fields) .top) :=
  .eqTrans
    (.eqApp .bot (.beta .top (.lam (.var (.vs .vz)))))
    (.beta .bot .top)

def fieldProof : ProofSyntax Constants []
    (applyArguments _ (conditions first) fields) :=
  .impE (.eqPropER conditionEquation) .topI

def introduced : ProofSyntax Constants [] (guard signature conditions payload) :=
  introduceAt conditions payload first fields fieldProof payloadEquation

theorem payloadEquation_free : payloadEquation.FunctionExtensionalityFree := by
  trivial

theorem fieldProof_free : fieldProof.FunctionExtensionalityFree := by
  trivial

theorem introduced_free : introduced.FunctionExtensionalityFree :=
  introduceAt_free conditions payload first fields fieldProof payloadEquation
    fieldProof_free payloadEquation_free

theorem payload_is_not_the_encoding : payload ≠ packed := by
  intro same
  cases same

theorem payload_admitted :
    (model.denote (guard signature conditions payload) values).down := by
  apply Soundness.extDerivation_sound introduced.erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => full _ _)
  intro formula member
  cases member

def wrongOccurrence : ClosedTerm Constants (payloadType signature) :=
  encode signature second fields

def changedField : ClosedTerm Constants (payloadType signature) :=
  encode signature first changedFields

theorem wrong_occurrence_refused :
    ¬ (model.denote (guard signature conditions wrongOccurrence) values).down := by
  intro admitted
  exact (guard_on_encoded model full signature conditions second fields values).mp admitted

theorem changed_field_refused :
    ¬ (model.denote (guard signature conditions changedField) values).down := by
  intro admitted
  exact (guard_on_encoded model full signature conditions first changedFields values).mp admitted

theorem wrong_occurrence_equation_refused :
    ¬ (model.denote (.eq payload wrongOccurrence) values).down := by
  intro same
  exact constructor_distinguished (model.eq_of_eqv_of_fullDomains full same)

theorem changed_field_equation_refused :
    ¬ (model.denote (.eq payload changedField) values).down := by
  intro same
  exact field_distinguished (model.eq_of_eqv_of_fullDomains full same)

theorem unused_payload_refused :
    ¬ (model.denote (guard signature conditions unused) values).down :=
  guard_refuses_outside_image model full signature conditions unused values unused_refused

#print axioms introduced
#print axioms introduced_free
#print axioms payload_is_not_the_encoding
#print axioms payload_admitted
#print axioms wrong_occurrence_refused
#print axioms changed_field_refused
#print axioms wrong_occurrence_equation_refused
#print axioms changed_field_equation_refused
#print axioms unused_payload_refused

end Mettapedia.Logic.HOL.ConstructorDataPredicates.ProgramControls
