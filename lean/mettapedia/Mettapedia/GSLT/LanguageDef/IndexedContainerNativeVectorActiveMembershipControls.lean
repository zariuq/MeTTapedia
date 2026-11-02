import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveMembership
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionModel

/-!
# Actual active-array membership with a nontrivial element predicate

The predicate admits true and excludes false. Every vector element and both
direct children are true; padding is false. The source activity guard covers
exactly the real children. The independent model therefore distinguishes
active membership from unguarded membership and from a missing scalar guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveMembershipControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original parameter)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorPositionModel
open IndexedContainerNativeVectorActiveMembership

def trueElement : ClosedTerm Const E := parameter 20 _
def falseElement : ClosedTerm Const E := tag
def elements : ClosedTerm Const (E ⇒ .prop) := .lam (.eq (.var .vz) (weaken trueElement))
def separationLaw := NaturalNumeralProofs.separation original.zero original.successor
def injectivityLaw := NaturalNumeralProofs.injectivity original.successor
def inductionLaw := NaturalRecursionProofs.inductionPrinciple original.zero original.successor
def assumptions : List (ClosedFormula Const) := separationLaw :: injectivityLaw :: inductionLaw :: ops.assumptions []
def arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero assumptions :=
  ⟨.hyp (Δ := assumptions) ⟨0,by decide⟩,.hyp (Δ := assumptions) ⟨1,by decide⟩,.hyp (Δ := assumptions) ⟨2,by decide⟩⟩
def premises : ops.ComputationPremises assumptions :=
  ((ops.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend separationLaw
theorem arithmetic_free : arithmetic.Free := by trivial
theorem premises_free : premises.FunctionExtensionalityFree :=
  ((ops.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend_free separationLaw
    ((ops.assumptionPremises.prepend inductionLaw).prepend_free injectivityLaw
      (ops.assumptionPremises.prepend_free inductionLaw ops.assumptionPremises_free))

theorem injectivity_holds : model.models injectivityLaw := by
  intro n _ m _
  constructor
  · intro same
    apply ULift.ext
    exact Nat.succ.inj (congrArg ULift.down same)
  · intro same
    cases same
    rfl

theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := by
  intro formula present
  simp only [assumptions,List.mem_cons] at present
  rcases present with rfl | rfl | rfl | present
  · exact separation_holds
  · exact injectivity_holds
  · exact induction_holds
  · exact primitive_assumptions_realizable _ present

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial) assumptions_realizable

def trueMember {Δ : List (ClosedFormula Const)} : ProofSyntax Const Δ (.app elements trueElement) := by
  apply ProofSyntax.impE (.eqPropER (.beta trueElement (.eq (.var .vz) (weaken trueElement))))
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl trueElement)
  simp only [instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem trueMember_free {Δ : List (ClosedFormula Const)} : (trueMember (Δ := Δ)).FunctionExtensionalityFree := by
  unfold trueMember
  exact ⟨True.intro,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩

def trueVector : Nat → ClosedTerm Const V
  | 0 => original.nil
  | n+1 => ops.toSignature.consValue (numeral [] n) trueElement (trueVector n)

def vectorMember {Δ : List (ClosedFormula Const)} : (n : Nat) →
    ProofSyntax Const Δ (ops.toSignature.member elements (numeral [] n) (trueVector n))
  | 0 => ops.toSignature.nil_member elements
  | n+1 => ops.toSignature.cons_member elements (numeral [] n) trueElement (trueVector n) trueMember (vectorMember n)

theorem vectorMember_free {Δ : List (ClosedFormula Const)} (n : Nat) : (vectorMember (Δ := Δ) n).FunctionExtensionalityFree := by
  induction n with
  | zero => exact ops.toSignature.nil_member_free elements
  | succ n previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ trueMember_free previous

def children (n : Nat) := ops.mixed (numeral [] n) trueElement (trueVector n) trueElement falseElement
def active (n slot : Nat) : ClosedFormula Const :=
  .app (sourceActivity payload (numeral [] n) tag (numeral [] 0)) (numeral [] slot)
def memberConclusion (n slot : Nat) : ClosedFormula Const := .app elements (.app (children n) (numeral [] slot))

@[irreducible] def membership (n slot : Nat) : ProofSyntax Const (active n slot :: assumptions) (memberConclusion n slot) :=
  sourceActiveMember elementSelection arraySelection payload elements (numeral [] n) tag trueElement (trueVector n)
    trueElement falseElement (numeral [] 0) (numeral [] slot) (premises.prepend (active n slot))
    (arithmetic.prepend (active n slot)) trueMember (vectorMember n) trueMember (.hyp 0)

set_option backward.isDefEq.respectTransparency true in
theorem membership_free (n slot : Nat) : (membership n slot).FunctionExtensionalityFree := by
  unfold membership
  exact sourceActiveMember_free elementSelection arraySelection payload elements (numeral [] n) tag trueElement (trueVector n)
    trueElement falseElement (numeral [] 0) (numeral [] slot) (premises.prepend (active n slot))
    (arithmetic.prepend (active n slot)) trueMember (vectorMember n) trueMember (.hyp 0)
    (premises.prepend_free _ premises_free) (arithmetic.prepend_free _ arithmetic_free)
    trueMember_free (vectorMember_free n) trueMember_free trivial

theorem active_holds_iff (n slot : Nat) : (model.denote (active n slot) values).down ↔ slot < n+2 := by
  change (model.denote (sourceActivity payload (numeral [] n) tag (numeral [] 0)) values
    (model.denote (numeral [] slot) values)).down ↔ _
  rw [numeral_denote,sourceActivity_iff]
  simp

theorem active_membership_holds (n slot : Nat) (bounded : slot < n+2) :
    (model.denote (memberConclusion n slot) values).down := by
  apply Soundness.extDerivation_sound (membership n slot).erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial)
  intro formula present
  simp only [List.mem_cons] at present
  rcases present with same | present
  · subst formula
    exact (active_holds_iff n slot).mpr bounded
  · exact assumptions_realizable _ present

def paddingProof (n : Nat) : ProofSyntax Const assumptions
    (.eq (.app (children n) (numeral [] (n+2))) falseElement) :=
  ops.mixedPadding elements (numeral [] n) trueElement (trueVector n) trueElement falseElement
    (numeral [] 0) (numeral [] (n+1)) premises (vectorMember n)
    (SuccessorOrder.sumStep original.successor original.zero (numeral [] n) (numeral [] 0) (numeral [] n)
      (SuccessorOrder.sumZero original.successor original.zero (numeral [] n)))

theorem padding_is_not_member (n : Nat) : ¬ (model.denote (memberConclusion n (n+2)) values).down := by
  intro member
  have padding := sound (paddingProof n)
  change model.denote (.app (children n) (numeral [] (n+2))) values = model.denote falseElement values at padding
  change model.denote (.app (children n) (numeral [] (n+2))) values = model.denote trueElement values at member
  have impossible : (false : Bool) = true := congrArg ULift.down (padding.symm.trans member)
  exact Bool.noConfusion impossible

theorem source_activity_cannot_be_dropped (n : Nat) :
    ¬ Nonempty (ProofSyntax Const assumptions (memberConclusion n (n+2))) := by
  rintro ⟨claimed⟩
  exact padding_is_not_member n (sound claimed)

theorem zero_vector_has_two_active_children :
    (model.denote (memberConclusion 0 0) values).down ∧ (model.denote (memberConclusion 0 1) values).down :=
  ⟨active_membership_holds 0 0 (by decide),active_membership_holds 0 1 (by decide)⟩

theorem nonempty_vector_covers_interior_and_tail :
    (model.denote (memberConclusion 2 1) values).down ∧ (model.denote (memberConclusion 2 2) values).down ∧
    (model.denote (memberConclusion 2 3) values).down :=
  ⟨active_membership_holds 2 1 (by decide),active_membership_holds 2 2 (by decide),active_membership_holds 2 3 (by decide)⟩

#print axioms assumptions_realizable
#print axioms active_membership_holds
#print axioms source_activity_cannot_be_dropped
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveMembershipControls
