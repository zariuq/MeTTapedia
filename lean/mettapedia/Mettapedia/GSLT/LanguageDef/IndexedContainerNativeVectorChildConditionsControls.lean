import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditions
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveMembershipControls

/-!
# Full child-array controls and the constructor-installation boundary

A deliberately field-erasing operation witnesses the local child-array
contract but fails constructor injectivity. It is a counterexample to
inferring datatype installation from this contract. The child predicate
distinguishes the selected value from padding in the independent Boolean
model, for every vector length.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditionsControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorPositionModel
open IndexedContainerNativeVectorChildGuard
open IndexedContainerNativeVectorChildConditions
open FiniteConstructorEncoding PredicateFixedPoint

abbrev background := IndexedContainerNativeVectorActiveMembershipControls.assumptions
def seedAllowed := sourceAllowed payload (numeral [] 0) tag (numeral [] 0)
def parentAllowed (n : Nat) := sourceAllowed payload (numeral [] n) tag (numeral [] 0)
def assumptions (n : Nat) : List (ClosedFormula Const) := parentAllowed n :: seedAllowed :: background

def projectionOperation : ClosedTerm Const (N ⇒ payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E) :=
  .lam (.lam (.lam (.app (.var .vz) (.var (.vs (.vs .vz))))))
def seedChildren : ClosedTerm Const (N ⇒ E) := .lam (weaken tag)
def selectedValue := (constructors payload).constructorValue projectionOperation (occurrence payload)
  (sourceArguments payload (numeral [] 0) tag (numeral [] 0)) seedChildren
def elements : ClosedTerm Const (E ⇒ .prop) := .lam (.eq (.var .vz) (weaken selectedValue))
def jointElements := joint payload elements projectionOperation
def padding : ClosedTerm Const E := IndexedContainerNativeVectorActiveMembershipControls.trueElement

def selectedMember {Δ : List (ClosedFormula Const)} : ProofSyntax Const Δ (.app elements selectedValue) := by
  apply ProofSyntax.impE (.eqPropER (.beta selectedValue (.eq (.var .vz) (weaken selectedValue))))
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl selectedValue)
  simp only [instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem selectedMember_free {Δ : List (ClosedFormula Const)} : (selectedMember (Δ := Δ)).FunctionExtensionalityFree := by
  unfold selectedMember
  exact ⟨True.intro,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩

@[irreducible] def selectedRoot {Δ : List (ClosedFormula Const)} (allowed : ProofSyntax Const Δ seedAllowed) :
    ProofSyntax Const Δ ((constructors payload).rootIndex projectionOperation selectedValue .top) :=
  (constructors payload).rootIndex_intro projectionOperation (occurrence payload)
    (sourceArguments payload (numeral [] 0) tag (numeral [] 0)) seedChildren .top allowed
    (reading.resultProof code (parameterMap payload) (arguments (numeral [] 0) tag (numeral [] 0)))

set_option backward.isDefEq.respectTransparency true in
theorem selectedRoot_free {Δ : List (ClosedFormula Const)} (allowed : ProofSyntax Const Δ seedAllowed)
    (free : allowed.FunctionExtensionalityFree) : (selectedRoot allowed).FunctionExtensionalityFree := by
  unfold selectedRoot
  exact (constructors payload).rootIndex_intro_free _ _ _ _ _ allowed _ free
    (reading.resultProof_free code (parameterMap payload) (arguments (numeral [] 0) tag (numeral [] 0)))

def jointMember {Δ : List (ClosedFormula Const)} (allowed : ProofSyntax Const Δ seedAllowed)
    (free : allowed.FunctionExtensionalityFree) : ProofSyntax Const Δ (.app jointElements selectedValue) :=
  (certifiedJointMember payload elements projectionOperation selectedValue selectedMember (selectedRoot allowed)
    selectedMember_free (selectedRoot_free allowed free)).val

theorem jointMember_free {Δ : List (ClosedFormula Const)} (allowed : ProofSyntax Const Δ seedAllowed)
    (free : allowed.FunctionExtensionalityFree) : (jointMember allowed free).FunctionExtensionalityFree :=
  (certifiedJointMember payload elements projectionOperation selectedValue selectedMember (selectedRoot allowed)
    selectedMember_free (selectedRoot_free allowed free)).property

def vector : Nat → ClosedTerm Const V
  | 0 => original.nil
  | n+1 => ops.toSignature.consValue (numeral [] n) selectedValue (vector n)

def vectorMember {Δ : List (ClosedFormula Const)} (allowed : ProofSyntax Const Δ seedAllowed)
    (free : allowed.FunctionExtensionalityFree) : (n : Nat) →
    ProofSyntax Const Δ (ops.toSignature.member jointElements (numeral [] n) (vector n))
  | 0 => ops.toSignature.nil_member jointElements
  | n+1 => ops.toSignature.cons_member jointElements (numeral [] n) selectedValue (vector n)
      (jointMember allowed free) (vectorMember allowed free n)

theorem vectorMember_free {Δ : List (ClosedFormula Const)} (allowed : ProofSyntax Const Δ seedAllowed)
    (free : allowed.FunctionExtensionalityFree) (n : Nat) : (vectorMember allowed free n).FunctionExtensionalityFree := by
  induction n with
  | zero => exact ops.toSignature.nil_member_free jointElements
  | succ n previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ (jointMember_free allowed free) previous

def children (n : Nat) := ops.mixed (numeral [] n) selectedValue (vector n) selectedValue padding
def contract (n : Nat) := ((positions payload).contextual padding projectionOperation).childConditions
  elements (encoded payload (numeral [] n) tag (numeral [] 0)) (children n)

def seedProof (n : Nat) : ProofSyntax Const (assumptions n) seedAllowed := .hyp ⟨1, by change 1 < 11; decide⟩
theorem seedProof_free (n : Nat) : (seedProof n).FunctionExtensionalityFree := by trivial
def parentProof (n : Nat) : ProofSyntax Const (assumptions n) (parentAllowed n) := .hyp ⟨0, by change 0 < 11; decide⟩
theorem parentProof_free (n : Nat) : (parentProof n).FunctionExtensionalityFree := by trivial

@[irreducible] def contractCertificate (n : Nat) :
    { proof : ProofSyntax Const (assumptions n) (contract n) // proof.FunctionExtensionalityFree } :=
  certifiedChildConditions elementSelection arraySelection payload elements projectionOperation
    (numeral [] n) tag selectedValue (vector n) selectedValue padding (numeral [] 0) (parentProof n)
    ((IndexedContainerNativeVectorActiveMembershipControls.premises.prepend seedAllowed).prepend (parentAllowed n))
    ((IndexedContainerNativeVectorActiveMembershipControls.arithmetic.prepend seedAllowed).prepend (parentAllowed n))
    (jointMember (seedProof n) (seedProof_free n)) (vectorMember (seedProof n) (seedProof_free n) n)
    (jointMember (seedProof n) (seedProof_free n)) (parentProof_free n)
    ((IndexedContainerNativeVectorActiveMembershipControls.premises.prepend seedAllowed).prepend_free _
      (IndexedContainerNativeVectorActiveMembershipControls.premises.prepend_free _
        IndexedContainerNativeVectorActiveMembershipControls.premises_free))
    ((IndexedContainerNativeVectorActiveMembershipControls.arithmetic.prepend seedAllowed).prepend_free _
      (IndexedContainerNativeVectorActiveMembershipControls.arithmetic.prepend_free _
        IndexedContainerNativeVectorActiveMembershipControls.arithmetic_free))
    (jointMember_free (seedProof n) (seedProof_free n)) (vectorMember_free (seedProof n) (seedProof_free n) n)
    (jointMember_free (seedProof n) (seedProof_free n))

def contractProof (n : Nat) : ProofSyntax Const (assumptions n) (contract n) := (contractCertificate n).val
theorem contractProof_free (n : Nat) : (contractProof n).FunctionExtensionalityFree := (contractCertificate n).property

theorem assumptions_realizable (n : Nat) : Soundness.SatisfiesHyps model values (assumptions n) := by
  intro formula present
  simp only [assumptions, List.mem_cons] at present
  rcases present with rfl | rfl | present
  · exact (sourceAllowed_iff n 0).mpr rfl
  · exact (sourceAllowed_iff 0 0).mpr rfl
  · exact IndexedContainerNativeVectorActiveMembershipControls.assumptions_realizable _ present

theorem contract_valid (n : Nat) : (model.denote (contract n) values).down :=
  Soundness.extDerivation_sound (contractProof n).erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial)
    (assumptions_realizable n)

theorem padding_excluded : ¬ (model.denote (.app elements padding) values).down := by
  change ¬ (ULift.up true : ULift.{1} Bool) = ULift.up false
  intro same
  exact Bool.noConfusion (congrArg ULift.down same)

def wrongChildren (n : Nat) := ops.mixed (numeral [] n) padding (vector n) selectedValue padding
def wrongContract (n : Nat) := ((positions payload).contextual padding projectionOperation).childConditions
  elements (encoded payload (numeral [] n) tag (numeral [] 0)) (wrongChildren n)

def leadingActive (n : Nat) : ClosedFormula Const :=
  .app (sourceActivity payload (numeral [] n) tag (numeral [] 0)) (numeral [] 0)

def wrongPoint (n : Nat) : ProofSyntax Const [wrongContract n, leadingActive n]
    (.app elements (.app (wrongChildren n) (numeral [] 0))) :=
  .andER (.impE (.andEL (((positions payload).contextual padding projectionOperation).childConditions_at
    elements (encoded payload (numeral [] n) tag (numeral [] 0)) (wrongChildren n) (numeral [] 0) (.hyp 0))) (.hyp 1))

theorem wrong_leading_member_refused (n : Nat) : ¬ (model.denote (wrongContract n) values).down := by
  intro accepted
  have active := (sourceActivity_iff n 0 0).mpr ⟨rfl,by omega⟩
  have member := Soundness.extDerivation_sound (wrongPoint n).erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial)
    (by
      intro formula present
      simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl | rfl
      · exact accepted
      · exact active)
  have leading := IndexedContainerNativeVectorActiveMembershipControls.sound
    (ops.mixedLeading (numeral [] n) padding (vector n) selectedValue padding
      IndexedContainerNativeVectorActiveMembershipControls.premises)
  change model.denote (wrongChildren n) values (ULift.up 0) = model.denote padding values at leading
  change model.denote (wrongChildren n) values (ULift.up 0) = model.denote selectedValue values at member
  apply padding_excluded
  exact leading.symm.trans member

theorem no_proof_of_wrong_leading_member (n : Nat) :
    ¬ Nonempty (ProofSyntax Const (assumptions n) (wrongContract n)) := by
  rintro ⟨claimed⟩
  exact wrong_leading_member_refused n (Soundness.extDerivation_sound claimed.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial)
    (assumptions_realizable n))

theorem projection_is_not_constructor_injective : ¬ model.models (ConstructorInjectivity.statement projectionOperation) := by
  intro injective
  let data := model.denote (encoded payload (numeral [] 0) tag (numeral [] 0)) values
  let child : ULift.{1} Nat → ULift.{1} Bool := fun _ => ULift.up false
  have compared := injective (ULift.up 0) trivial data trivial child trivial
    (ULift.up 1) trivial data trivial child trivial
  have same : (ULift.up 0 : ULift.{1} Nat) = ULift.up 1 := (compared.mp rfl).1
  have impossible : (0 : Nat) = 1 := congrArg ULift.down same
  exact Nat.noConfusion impossible

theorem complete_child_contract_does_not_install_constructor (n : Nat) :
    (model.denote (contract n) values).down ∧ ¬ model.models (ConstructorInjectivity.statement projectionOperation) :=
  ⟨contract_valid n, projection_is_not_constructor_injective⟩

#print axioms assumptions_realizable
#print axioms contractProof_free
#print axioms contract_valid
#print axioms no_proof_of_wrong_leading_member
#print axioms complete_child_contract_does_not_install_constructor
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditionsControls
