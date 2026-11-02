import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionModel

/-!
# Source-inactive padding: realized premises and independent countermodels

The original generated activity predicate is interpreted in the natural/
Boolean/list model. Every concrete vector has a retained membership proof.
All eleven premises of the source-to-array theorem are jointly realizable.
Dropping source well-formedness is refuted by a malformed shape: every position
is then inactive, including the non-padding leading child. Dropping inactivity
is separately refuted at the well-formed source's leading child.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorInactivePaddingControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original parameter)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorPositionModel

def assumptions : List (ClosedFormula Const) := ops.assumptions []
def premises : ops.ComputationPremises assumptions := ops.assumptionPremises
theorem premises_free : premises.FunctionExtensionalityFree := ops.assumptionPremises_free

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) primitive_assumptions_realizable

def element : Bool → ClosedTerm Const E
  | false => tag
  | true => parameter 20 _

def vector : List Bool → ClosedTerm Const V
  | [] => original.nil
  | head :: tail => ops.toSignature.consValue (numeral [] tail.length) (element head) (vector tail)

def member : (xs : List Bool) → ProofSyntax Const assumptions
    (ops.toSignature.member payload (numeral [] xs.length) (vector xs))
  | [] => ops.toSignature.nil_member payload
  | head :: tail => ops.toSignature.cons_member payload (numeral [] tail.length) (element head) (vector tail)
      (.impE (.eqPropER (.beta (element head) .top)) .topI) (member tail)

theorem member_free (xs : List Bool) : (member xs).FunctionExtensionalityFree := by
  induction xs with
  | nil => exact ops.toSignature.nil_member_free payload
  | cons head tail previous =>
      exact ops.toSignature.cons_member_free _ _ _ _ _ _ (by trivial) previous

def children (xs : List Bool) :=
  ops.mixed (numeral [] xs.length) (element true) (vector xs) (element true) (element false)

def paddingEquation (xs : List Bool) (slot : Nat) : ClosedFormula Const :=
  .eq (.app (children xs) (numeral [] slot)) (element false)

def allowed (xs : List Bool) (shape : Nat) := sourceAllowed payload (numeral [] xs.length) tag (numeral [] shape)
def inactive (xs : List Bool) (shape slot : Nat) : ClosedFormula Const :=
  .not (.app (sourceActivity payload (numeral [] xs.length) tag (numeral [] shape)) (numeral [] slot))
def induction := NaturalRecursionProofs.inductionPrinciple original.zero original.successor
def separation := NaturalNumeralProofs.separation original.zero original.successor
def membership (xs : List Bool) := ops.toSignature.member payload (numeral [] xs.length) (vector xs)

def remaining (xs : List Bool) (shape slot : Nat) : List (ClosedFormula Const) :=
  induction :: separation :: inactive xs shape slot :: membership xs :: assumptions
def complete (xs : List Bool) (shape slot : Nat) : List (ClosedFormula Const) :=
  allowed xs shape :: remaining xs shape slot

def liftedPremises (xs : List Bool) (shape slot : Nat) : ops.ComputationPremises (complete xs shape slot) :=
  ((((premises.prepend (membership xs)).prepend (inactive xs shape slot)).prepend separation).prepend induction).prepend (allowed xs shape)

theorem liftedPremises_free (xs : List Bool) (shape slot : Nat) :
    (liftedPremises xs shape slot).FunctionExtensionalityFree := by
  unfold liftedPremises
  iterate 5 apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  exact premises_free

@[irreducible] def sourceProof (xs : List Bool) (shape slot : Nat) :
    ProofSyntax Const (complete xs shape slot) (paddingEquation xs slot) :=
  sourceInactivePadding elementSelection arraySelection payload payload (numeral [] xs.length) tag
    (element true) (vector xs) (element true) (element false) (numeral [] shape) (numeral [] slot)
    (.hyp ⟨0,by change 0 < 11; decide⟩) (.hyp ⟨1,by change 1 < 11; decide⟩)
    (.hyp ⟨2,by change 2 < 11; decide⟩) (liftedPremises xs shape slot)
    (.hyp ⟨4,by change 4 < 11; decide⟩) (.hyp ⟨3,by change 3 < 11; decide⟩)

set_option backward.isDefEq.respectTransparency true in
theorem sourceProof_free (xs : List Bool) (shape slot : Nat) :
    (sourceProof xs shape slot).FunctionExtensionalityFree := by
  unfold sourceProof
  exact sourceInactivePadding_free elementSelection arraySelection payload payload (numeral [] xs.length) tag
    (element true) (vector xs) (element true) (element false) (numeral [] shape) (numeral [] slot)
    _ _ _ (liftedPremises xs shape slot) _ _ trivial trivial trivial (liftedPremises_free xs shape slot) trivial trivial

theorem inactive_holds_iff (xs : List Bool) (shape slot : Nat) :
    (model.denote (inactive xs shape slot) values).down ↔ ¬ (shape = 0 ∧ slot < xs.length + 2) := by
  change (¬ (model.denote (sourceActivity payload (numeral [] xs.length) tag (numeral [] shape)) values
    (model.denote (numeral [] slot) values)).down) ↔ _
  rw [numeral_denote,sourceActivity_iff]

theorem remaining_realizable (xs : List Bool) (shape slot : Nat)
    (off : ¬ (shape = 0 ∧ slot < xs.length + 2)) :
    Soundness.SatisfiesHyps model values (remaining xs shape slot) := by
  intro formula present
  simp only [remaining,List.mem_cons] at present
  rcases present with rfl | rfl | rfl | rfl | present
  · exact induction_holds
  · exact separation_holds
  · exact (inactive_holds_iff xs shape slot).mpr off
  · exact sound (member xs)
  · exact primitive_assumptions_realizable _ present

theorem complete_realizable (xs : List Bool) (slot : Nat) (outside : xs.length + 2 ≤ slot) :
    Soundness.SatisfiesHyps model values (complete xs 0 slot) := by
  intro formula present
  simp only [complete,List.mem_cons] at present
  rcases present with same | present
  · subst formula
    exact (sourceAllowed_iff xs.length 0).mpr rfl
  · exact remaining_realizable xs 0 slot (by omega) _ present

theorem source_padding_holds (xs : List Bool) (slot : Nat) (outside : xs.length + 2 ≤ slot) :
    (model.denote (paddingEquation xs slot) values).down :=
  Soundness.extDerivation_sound (sourceProof xs 0 slot).erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (complete_realizable xs slot outside)

def leadingProof (xs : List Bool) : ProofSyntax Const assumptions
    (.eq (.app (children xs) (numeral [] 0)) (element true)) :=
  ops.mixedLeading (numeral [] xs.length) (element true) (vector xs) (element true) (element false) premises

theorem leading_is_not_padding (xs : List Bool) : ¬ (model.denote (paddingEquation xs 0) values).down := by
  intro wrong
  have leading := sound (leadingProof xs)
  have impossible : ULift.up true = (ULift.up false : ULift.{1} Bool) := leading.symm.trans wrong
  exact Bool.noConfusion (congrArg ULift.down impossible)

theorem dropping_source_allowed_refused (xs : List Bool) :
    ¬ Nonempty (ProofSyntax Const (remaining xs 9 0) (paddingEquation xs 0)) := by
  rintro ⟨claimed⟩
  apply leading_is_not_padding xs
  exact Soundness.extDerivation_sound claimed.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (remaining_realizable xs 9 0 (by simp))

theorem dropping_inactivity_refused (xs : List Bool) :
    ¬ Nonempty (ProofSyntax Const
      (allowed xs 0 :: induction :: separation :: membership xs :: assumptions) (paddingEquation xs 0)) := by
  rintro ⟨claimed⟩
  apply leading_is_not_padding xs
  apply Soundness.extDerivation_sound claimed.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial)
  intro formula present
  simp only [List.mem_cons] at present
  rcases present with rfl | rfl | rfl | rfl | present
  · exact (sourceAllowed_iff xs.length 0).mpr rfl
  · exact induction_holds
  · exact separation_holds
  · exact sound (member xs)
  · exact primitive_assumptions_realizable _ present

theorem nonempty_padding : (model.denote (paddingEquation [true,false] 4) values).down :=
  source_padding_holds [true,false] 4 (by decide)

theorem empty_padding : (model.denote (paddingEquation [] 2) values).down :=
  source_padding_holds [] 2 (by decide)

theorem same_position_plan_different_activity (length : Nat) :
    OrderedPositionPrograms.evaluateFields model Equiv.ulift.symm _ values (encodedFields length 0).2
      (plans payload (encodedFields length 0).1) =
    OrderedPositionPrograms.evaluateFields model Equiv.ulift.symm _ values (encodedFields length 9).2
      (plans payload (encodedFields length 9).1) ∧
    (model.denote (sourceActivity payload (numeral [] length) tag (numeral [] 0)) values (ULift.up 0)).down ∧
    ¬ (model.denote (sourceActivity payload (numeral [] length) tag (numeral [] 9)) values (ULift.up 0)).down := by
  refine ⟨(fields_evaluate length 0).trans (fields_evaluate length 9).symm,?_,?_⟩
  · rw [sourceActivity_iff]
    exact ⟨rfl,by omega⟩
  · rw [sourceActivity_iff]
    simp

#print axioms sourceProof_free
#print axioms complete_realizable
#print axioms source_padding_holds
#print axioms dropping_source_allowed_refused
#print axioms dropping_inactivity_refused
#print axioms same_position_plan_different_activity
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorInactivePaddingControls
