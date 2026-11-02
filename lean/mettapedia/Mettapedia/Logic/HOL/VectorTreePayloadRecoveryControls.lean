import Mettapedia.Logic.HOL.VectorTreePayloadRecovery
import Mettapedia.Logic.HOL.FiniteConstructorFieldEmbeddingControls

/-!
# Whole-inventory recovery with restrictive source guards

The same nontrivial recursive-space model realizes the three primitive
provider laws. The complete payload guard accepts the represented true
answer and the equal-length branch, refuses the false answer and an unused
payload, and supports retained recovery through the actual function programs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.VectorTreePayloadRecoveryControls
open FiniteConstructorEncoding
open FiniteConstructorFieldEmbeddingControls
open VectorTreePayloadMaps

abbrev Stored := VectorTreeFieldEmbedding.storedSignature N E
def branchCondition : ClosedTerm Const (handlerType [N,N]) :=
  .lam (.lam (.eq (.var (.vs .vz)) (.var .vz)))
def originalConditions := conditions given onlyTrue branchCondition
def solved (answer : Bool) : ClosedTerm Const (payloadType Stored) :=
  encode Stored ⟨0,by decide⟩ (.app given.encode (.const (.answer answer)),PUnit.unit)
def branch : ClosedTerm Const (payloadType Stored) :=
  encode Stored ⟨1,by decide⟩ (.const .zero,.const .zero,PUnit.unit)
def unused : ClosedTerm Const (payloadType Stored) := .lam (.lam .bot)
def admitted (payload : ClosedTerm Const (payloadType Stored)) : ClosedFormula Const :=
  ConstructorDataPredicates.guard Stored originalConditions payload

theorem true_answer_admitted : (model.denote (admitted (solved true)) values).down := by
  apply (ConstructorDataPredicates.guard_on_encoded model full Stored originalConditions
    ⟨0,by decide⟩ _ values).mpr
  exact accepted_true

theorem false_answer_refused : ¬ (model.denote (admitted (solved false)) values).down := by
  intro present
  apply rejected_false
  exact (ConstructorDataPredicates.guard_on_encoded model full Stored originalConditions
    ⟨0,by decide⟩ _ values).mp present

theorem branch_admitted : (model.denote (admitted branch) values).down := by
  apply (ConstructorDataPredicates.guard_on_encoded model full Stored originalConditions
    ⟨1,by decide⟩ _ values).mpr
  rfl

theorem unused_refused : ¬ (model.denote (admitted unused) values).down :=
  ConstructorDataPredicates.guard_refuses_outside_image model full Stored originalConditions unused values
    (TypeTheory.FiniteConstructorEncoding.unused_not_valid _ _)

def recoveryProof (payload : ClosedTerm Const (payloadType Stored)) :
    ProofSyntax Const (admitted payload :: premises)
      (.eq (.app (raiseProgram given) (.app (lowerProgram given) payload)) payload) :=
  recover given onlyTrue branchCondition
    (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩) (.hyp ⟨3,by simp [premises]⟩)
    payload (.hyp 0)

theorem recoveryProof_free (payload : ClosedTerm Const (payloadType Stored)) :
    (recoveryProof payload).FunctionExtensionalityFree := by
  apply recover_free
  all_goals trivial

theorem program_roundtrip (payload : ClosedTerm Const (payloadType Stored))
    (present : (model.denote (admitted payload) values).down) :
    model.denote (raiseProgram given) values (model.denote (lowerProgram given) values
      (model.denote payload values)) = model.denote payload values := by
  have holds : Soundness.SatisfiesHyps model values (admitted payload :: premises) := by
    intro formula member
    rcases List.mem_cons.mp member with rfl | member
    · exact present
    · exact assumptions_realizable formula member
  exact model.eq_of_eqv_of_fullDomains full (Soundness.extDerivation_sound
    (recoveryProof payload).erase (model.functionsRespectEqv_of_fullDomains full) (fun _ => full _ _) holds)

theorem true_answer_program_roundtrip :
    model.denote (raiseProgram given) values (model.denote (lowerProgram given) values
      (model.denote (solved true) values)) = model.denote (solved true) values :=
  program_roundtrip _ true_answer_admitted

theorem branch_program_roundtrip :
    model.denote (raiseProgram given) values (model.denote (lowerProgram given) values
      (model.denote branch values)) = model.denote branch values :=
  program_roundtrip _ branch_admitted

theorem original_predicate_matters : ¬ ∀ answer : Bool,
    (model.denote (admitted (solved answer)) values).down := by
  intro allAnswers
  exact false_answer_refused (allAnswers false)

def numericValues (first second : Nat) : model.Valuation [N,N] := fun index =>
  match index with
  | .vz => .up second
  | .vs .vz => .up first
  | .vs (.vs impossible) => nomatch impossible

def branchFields : Arguments Const [N,N] [N,N] :=
  (.var (.vs .vz),.var .vz,PUnit.unit)
def openBranch : Term Const [N,N] (payloadType Stored) :=
  encode Stored ⟨1,by decide⟩ branchFields
def openConditions : ConstructorDataPredicates.Conditions Const [N,N] Stored :=
  fun index => HOL.weaken (HOL.weaken (originalConditions index))

theorem branch_fields_checked_separately (first second : Nat) :
    (model.denote (ConstructorDataPredicates.guard Stored openConditions openBranch)
      (numericValues first second)).down ↔ first = second := by
  constructor
  · intro present
    have fields := (ConstructorDataPredicates.guard_on_encoded model full Stored openConditions
      ⟨1,by decide⟩ branchFields (numericValues first second)).mp present
    change (ULift.up first : Number) = ULift.up second at fields
    exact congrArg ULift.down fields
  · intro same
    apply (ConstructorDataPredicates.guard_on_encoded model full Stored openConditions
      ⟨1,by decide⟩ branchFields (numericValues first second)).mpr
    change (ULift.up first : Number) = ULift.up second
    exact congrArg ULift.up same

theorem unequal_branch_fields_refused :
    ¬ (model.denote (ConstructorDataPredicates.guard Stored openConditions openBranch)
      (numericValues 2 3)).down := by
  rw [branch_fields_checked_separately]
  decide

def reversedBranch : Term Const [N,N] (payloadType Stored) :=
  encode Stored ⟨1,by decide⟩ (.var .vz,.var (.vs .vz),PUnit.unit)

theorem branch_field_order_matters (first second : Nat) (different : first ≠ second) :
    model.denote openBranch (numericValues first second) ≠
      model.denote reversedBranch (numericValues first second) := by
  intro same
  have images := (encode_denote model Stored ⟨1,by decide⟩ branchFields (numericValues first second)).symm.trans
    ((congrArg (payloadEquivalence model Stored) same).trans
      (encode_denote model Stored ⟨1,by decide⟩ _ (numericValues first second)))
  have inputs := TypeTheory.FiniteConstructorEncoding.encode_injective _ _ images
  have fields := eq_of_heq (Sigma.mk.inj inputs).2
  exact different (congrArg ULift.down (congrArg Prod.fst fields))

#print axioms true_answer_admitted
#print axioms false_answer_refused
#print axioms branch_admitted
#print axioms unused_refused
#print axioms recoveryProof_free
#print axioms program_roundtrip
#print axioms branch_fields_checked_separately
#print axioms unequal_branch_fields_refused
#print axioms branch_field_order_matters
end Mettapedia.Logic.HOL.VectorTreePayloadRecoveryControls
