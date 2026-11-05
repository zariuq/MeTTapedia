import Mettapedia.Logic.HOL.Embedding.ZFSetPairingProofInterpretation
import Mettapedia.Logic.HOL.SetPairingSchemas
import Mettapedia.Logic.HOL.SetPairingOperationProofs

/-!
# Pairing controls with an independently interpreted selection failure

The retained programs have a real two-element set interpretation. Replacing
only the selector by the constant-empty function keeps the core set operations
but drops the second member of the proposed pair. The selection law is thus
material to this functional-image presentation; no claim that all pairing
constructions need choice follows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetPairingProofControls
open SetPairingProofs SetComprehensionProofs SetMembershipProofs
open Mettapedia.Logic.HOL.Embedding
open ZFSetHenkinInterpretation
open ZFSetPairingProofInterpretation (core epsilon basis laws laws_free)

def zero : ClosedTerm ChoiceSymbol SetPairingProofs.object := .const (.core .empty)
def one : ClosedTerm ChoiceSymbol SetPairingProofs.object := power core zero

def leftProof : ProofSyntax ChoiceSymbol (basis []) (member core zero (unordered core epsilon zero one)) :=
  leftMem core epsilon zero one (laws [])

def rightProof : ProofSyntax ChoiceSymbol (basis []) (member core one (unordered core epsilon zero one)) :=
  rightMem core epsilon zero one (laws [])

def membershipProof : ProofSyntax ChoiceSymbol (basis []) (.and
    (.imp (member core zero (unordered core epsilon zero one)) (.or (.eq zero zero) (.eq zero one)))
    (.imp (.or (.eq zero zero) (.eq zero one)) (member core zero (unordered core epsilon zero one)))) :=
  membership core epsilon zero one zero (laws [])

def injectivityClaim : ClosedFormula ChoiceSymbol :=
  .imp (.eq (ordered core epsilon zero one) (ordered core epsilon one zero))
    (.and (.eq zero one) (.eq one zero))

def injectivityProof : ProofSyntax ChoiceSymbol (basis []) injectivityClaim :=
  .impI (orderedInjective core epsilon zero one one zero ((laws []).prepend _) (.hyp 0))

theorem leftProof_free : leftProof.FunctionExtensionalityFree :=
  leftMem_free core epsilon zero one (laws []) (laws_free [])

theorem rightProof_free : rightProof.FunctionExtensionalityFree :=
  rightMem_free core epsilon zero one (laws []) (laws_free [])

theorem membershipProof_free : membershipProof.FunctionExtensionalityFree :=
  membership_free core epsilon zero one zero (laws []) (laws_free [])

theorem injectivityProof_free : injectivityProof.FunctionExtensionalityFree :=
  orderedInjective_free core epsilon zero one one zero _ _ ((laws []).prepend_free _ (laws_free [])) trivial

def secondSeparationProof : ProofSyntax ChoiceSymbol (basis [])
    (.not (.eq (ordered core epsilon zero zero) (ordered core epsilon zero one))) :=
  orderedApartSecond core epsilon zero zero zero one (laws [])
    (emptyNePower core (laws []).empty (laws []).power)

theorem secondSeparationProof_free : secondSeparationProof.FunctionExtensionalityFree :=
  orderedApartSecond_free core epsilon zero zero zero one (laws []) _ (laws_free [])
    (emptyNePower_free core (laws []).empty (laws []).power trivial trivial)

/-- The premise is a theorem to be supplied and discharged by the caller. -/
abbrev membershipSchema : ClosedFormula ChoiceSymbol :=
  SetPairingSchemas.membershipStatement core epsilon

private def schemaRules {assumptions : List (ClosedFormula ChoiceSymbol)}
    (proof : ProofSyntax ChoiceSymbol assumptions membershipSchema) :
    MembershipRules core epsilon assumptions :=
  SetPairingSchemas.rulesFromSchema core epsilon
    (proof.castIndices rfl (weakenCtx_nil membershipSchema).symm)

private theorem schemaRules_free {assumptions : List (ClosedFormula ChoiceSymbol)}
    (proof : ProofSyntax ChoiceSymbol assumptions membershipSchema)
    (free : proof.FunctionExtensionalityFree) : (schemaRules proof).Free :=
  SetPairingSchemas.rulesFromSchema_free core epsilon _ free

def injectivityUsingSchema : ProofSyntax ChoiceSymbol [membershipSchema] injectivityClaim :=
  .impI (MembershipRules.orderedInjective core epsilon zero one one zero
    ((schemaRules (.hyp 0)).prepend _) (.hyp 0))

theorem injectivityUsingSchema_free : injectivityUsingSchema.FunctionExtensionalityFree :=
  MembershipRules.orderedInjective_free core epsilon zero one one zero _ _
    (MembershipRules.prepend_free _ _
      (schemaRules_free (assumptions := [membershipSchema]) (.hyp 0) trivial)) trivial

abbrev separationSchemaBasis : List (ClosedFormula ChoiceSymbol) :=
  [membershipSchema, lawAt core emptyLaw, lawAt core powerLaw]

def secondSeparationUsingSchema : ProofSyntax ChoiceSymbol separationSchemaBasis
    (.not (.eq (ordered core epsilon zero zero) (ordered core epsilon zero one))) :=
  .notI (.notE ((emptyNePower core (.hyp 1) (.hyp 2)).prepend _)
    (.andER (MembershipRules.orderedInjective core epsilon zero zero zero one
      ((schemaRules (.hyp 0)).prepend _) (.hyp 0))))

theorem secondSeparationUsingSchema_free : secondSeparationUsingSchema.FunctionExtensionalityFree :=
  ⟨emptyNePower_free core (Δ := separationSchemaBasis) (.hyp 1) (.hyp 2) trivial trivial,
    MembershipRules.orderedInjective_free core epsilon zero zero zero one _ _
      (MembershipRules.prepend_free _ _
        (schemaRules_free (assumptions := separationSchemaBasis) (.hyp 0) trivial)) trivial⟩

namespace Operation

def membershipProof := SetPairingOperationProofs.schemaProof core epsilon (laws [])
theorem membershipProof_free : membershipProof.FunctionExtensionalityFree :=
  SetPairingOperationProofs.schemaProof_free core epsilon (laws []) (laws_free [])

abbrev firstApplication := SetPairingOperationProofs.applicationClaim core epsilon zero one one zero
abbrev secondApplication := SetPairingOperationProofs.applicationClaim core epsilon zero zero zero one
abbrev secondInjection := SetPairingOperationProofs.rawClaim core epsilon zero zero zero one

def firstConversion : ProofSyntax ChoiceSymbol [firstApplication] injectivityClaim :=
  SetPairingOperationProofs.convert core epsilon zero one one zero (.hyp 0)
theorem firstConversion_free : firstConversion.FunctionExtensionalityFree :=
  SetPairingOperationProofs.convert_free core epsilon zero one one zero
    (Δ := [firstApplication]) (.hyp 0) trivial

def secondConversion : ProofSyntax ChoiceSymbol [secondApplication] secondInjection :=
  SetPairingOperationProofs.convert core epsilon zero zero zero one (.hyp 0)
theorem secondConversion_free : secondConversion.FunctionExtensionalityFree :=
  SetPairingOperationProofs.convert_free core epsilon zero zero zero one
    (Δ := [secondApplication]) (.hyp 0) trivial

abbrev secondTailBasis : List (ClosedFormula ChoiceSymbol) :=
  [secondInjection,lawAt core emptyLaw,lawAt core powerLaw]
def secondTail : ProofSyntax ChoiceSymbol secondTailBasis
    (.not (.eq (ordered core epsilon zero zero) (ordered core epsilon zero one))) :=
  SetPairingOperationProofs.separateSecond core epsilon zero zero zero one (.hyp 0)
    (emptyNePower core (.hyp 1) (.hyp 2))
theorem secondTail_free : secondTail.FunctionExtensionalityFree :=
  SetPairingOperationProofs.separateSecond_free core epsilon zero zero zero one
    (Δ := secondTailBasis) (.hyp 0) _ trivial
    (emptyNePower_free core (Δ := secondTailBasis) (.hyp 1) (.hyp 2) trivial trivial)

end Operation

private theorem empty_ne_power : (∅ : ZFSet.{0}) ≠ ZFSet.powerset ∅ := by
  intro same
  have member : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← same] at member
  exact ZFSet.notMem_empty _ member

noncomputable def badDenote : {type : Ty Unit} → ChoiceSymbol type →
    Ty.denote.{0,1} ZFSetHenkinInterpretation.carrier.{0} type
  | _, .core symbol => ZFSetHenkinInterpretation.denoteSymbol symbol
  | _, .epsilon => fun _ => (∅ : ZFSet.{0})

noncomputable abbrev badModel : HenkinModel.{0,0,1} Unit ChoiceSymbol :=
  HenkinModel.standard ZFSetHenkinInterpretation.carrier badDenote

theorem bad_core_valid (formula : ClosedFormula ZFSetHenkinInterpretation.Symbol)
    (valid : ZFSetHenkinInterpretation.model.{0}.models formula) :
    badModel.models (mapConst core formula) := by
  have preserved := HenkinModel.models_substConst_of_agreement (fun symbol => .const (.core symbol))
    ZFSetHenkinInterpretation.model.{0} badModel rfl HEq.rfl (fun _ => HEq.rfl) formula
  simpa only [HOL.substConst_constant_images] using preserved.mpr valid

theorem bad_all_four_core_laws : ∀ formula ∈
    ([emptyLaw,powerLaw,separationLaw,replacementLaw] : List (ClosedFormula ZFSetHenkinInterpretation.Symbol)),
    badModel.models (mapConst core formula) := by
  intro formula present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact bad_core_valid _ emptyLaw_valid
  · exact bad_core_valid _ powerLaw_valid
  · exact bad_core_valid _ separationLaw_valid
  · exact bad_core_valid _ replacementLaw_valid

theorem bad_selection_refused : ¬ badModel.models choiceLaw := by
  intro valid
  have result := valid (fun x : ZFSet.{0} => ULift.up (x = ZFSet.powerset ∅)) trivial
    (ZFSet.powerset ∅) trivial rfl
  exact empty_ne_power result

theorem bad_pair_drops_right :
    ¬ (badModel.denote (member core one (unordered core epsilon zero one)) (fun index => nomatch index)).down := by
  change ¬ (ZFSet.powerset (∅ : ZFSet.{0}) ∈
    replacement (badModel.denote (index (Γ := []) core) (fun index => nomatch index))
      (fun _ => (∅ : ZFSet.{0})))
  rw [mem_replacement]
  rintro ⟨_,_,same⟩
  exact empty_ne_power same

def coreOnlyBasis : List (ClosedFormula ChoiceSymbol) :=
  [emptyLaw,powerLaw,separationLaw,replacementLaw].map (mapConst core)

theorem no_right_proof_without_selection : ¬ Nonempty
    (ProofSyntax ChoiceSymbol coreOnlyBasis (member core one (unordered core epsilon zero one))) := by
  rintro ⟨proof⟩
  apply bad_pair_drops_right
  apply Soundness.extDerivation_sound (ρ := fun index => nomatch index) proof.erase
    (badModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index)
  intro formula present
  obtain ⟨source, sourcePresent, rfl⟩ := List.mem_map.mp present
  exact (congrArg ULift.down
    (HenkinModel.denote_closed_valuation_eq badModel (mapConst core source) _ _)).mpr
      (bad_all_four_core_laws source sourcePresent)

theorem actual_pair_has_both :
    ZFSetPairingProofInterpretation.value (unordered core epsilon zero one) (fun index => nomatch index) =
      ({∅, ZFSet.powerset ∅} : ZFSet.{0}) :=
  ZFSetPairingProofInterpretation.unordered_value zero one _

theorem actual_ordered_swap_refused :
    ZFSetPairingProofInterpretation.value.{0} (ordered core epsilon zero one) (fun index => nomatch index) ≠
      ZFSetPairingProofInterpretation.value.{0} (ordered core epsilon one zero) (fun index => nomatch index) := by
  rw [ZFSetPairingProofInterpretation.ordered_value, ZFSetPairingProofInterpretation.ordered_value]
  intro equal
  exact empty_ne_power (ZFSet.pair_inj.mp equal).1

def operatorBetaProof : ProofSyntax ChoiceSymbol []
    (.eq (.app (.app (SetPairingProofs.operator core epsilon) zero) one)
      (ordered core epsilon zero one)) := operatorBeta core epsilon zero one

theorem operatorBetaProof_free : operatorBetaProof.FunctionExtensionalityFree :=
  operatorBeta_free core epsilon zero one

end Mettapedia.Logic.HOL.SetPairingProofControls
