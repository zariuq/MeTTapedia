import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredParentApplication
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeTabulationControls
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplicationInputs

/-!
# An actual stored-parent application in the common Native4 world

The input is the original length-two child array. The Vector argument is the
actual Shifted.tabulate program. Its retained equality, guard, All query and
pointwise reconstruction are assembled before the original stored parent is
passed to the eta-licensed case rule. The conclusion is not a premise.

The displayed context retains all four tabulation-route premises and the
seventeen source-input premises, including their three explicit previously
checked child/vector cuts. All hold in the same genuine Native4 model. This
finite application neither discharges an arbitrary induction contract nor
asserts an arbitrary executable inverse or eta-free parent transport.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredParentApplicationControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedVectorTreeNativeWitnessModel
namespace Witness
export IndexedVectorTreeNativeWitnessControls
  (family motive suppliedBranchCase branchFunction sourceVector solvedValue delta)
end Witness
namespace Tab
export IndexedVectorTreeNativeTabulationControls
  (additional hypotheses sourceArray shiftedValue shiftedExact shiftedGuard arrayPadding hypotheses_realizable)
end Tab
namespace Cases
export IndexedVectorTreeSourceCaseApplicationInputs
  (additional hypotheses branchCaseInput allQuery hypotheses_realizable)
end Cases
namespace Parent
export IndexedVectorTreeStoredParentApplication (vector rebuilt parent parentViaEta parentViaEta_not_free)
end Parent

noncomputable section

def hypotheses : List (ClosedFormula Native.Const) := Tab.additional ++ Cases.hypotheses

private def insertAfter {α : Type} (extra tail : List α) : (front : List α) →
    ProofSyntax.OccurrenceMap (front ++ tail) (front ++ extra ++ tail)
  | [] => ProofSyntax.OccurrenceMap.appendLeft extra tail
  | first :: rest => (insertAfter extra tail rest).lift first

@[irreducible] def fromCases {formula : ClosedFormula Native.Const}
    (proof : ProofSyntax Native.Const Cases.hypotheses formula) : ProofSyntax Native.Const hypotheses formula :=
  proof.mono (ProofSyntax.OccurrenceMap.appendLeft Tab.additional Cases.hypotheses)

@[irreducible] def fromTab {formula : ClosedFormula Native.Const}
    (proof : ProofSyntax Native.Const Tab.hypotheses formula) : ProofSyntax Native.Const hypotheses formula :=
  proof.mono (insertAfter Cases.additional Witness.delta Tab.additional)

theorem hypotheses_count : hypotheses.length = 21 := by decide +kernel

theorem hypotheses_realizable : Soundness.SatisfiesHyps model values hypotheses := by
  intro formula present
  rcases List.mem_append.mp present with route | source
  · exact Tab.hypotheses_realizable formula (List.mem_append_left _ route)
  · exact Cases.hypotheses_realizable formula source

theorem sound {formula : ClosedFormula Native.Const} (proof : ProofSyntax Native.Const hypotheses formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) hypotheses_realizable

def vector : ClosedTerm Native.Const Native.V :=
  Parent.vector elementSelection arraySelection shiftedSelection (numeral 2) Tab.sourceArray
def rebuilt : ClosedTerm Native.Const (Native.N ⇒ Native.E) :=
  Parent.rebuilt elementSelection arraySelection bottom shiftedSelection (numeral 2) Tab.sourceArray
def parent : ClosedTerm Native.Const Native.E :=
  Parent.parent input originalPredicate numbers one numeral bottom (numeral 2) Native.original.zero Tab.sourceArray

@[irreducible] def vectorGuard : ProofSyntax Native.Const hypotheses
    (.app (NativeVectorAll.Reading.vectorCode Native.original Native.selection Witness.family (numeral 2)) vector) :=
  fromTab Tab.shiftedGuard

@[irreducible] def reconstructed : ProofSyntax Native.Const hypotheses (.eq rebuilt Tab.sourceArray) := by
  apply ProofSyntax.castIndices rfl ?_ (ContextualTrinity.holeCongr
    (arrays.single (weaken (numeral 2)) (.var .vz) (weaken bottom)) (fromTab Tab.shiftedExact))
  simp only [instantiate,VectorChildArrays.Operations.single_subst,HOL.subst,Subst.single,
    PredicateFixedPoint.subst_single_weaken]
  rfl

@[irreducible] def pointwise : ProofSyntax Native.Const hypotheses
    (VectorTabulation.Shifted.pointwiseFormula rebuilt Tab.sourceArray) :=
  .allI (.eqApp (.var .vz) (reconstructed.renameShared Rename.weaken))

def query : ClosedFormula Native.Const := NativeVectorAll.Existence.query Native.original Native.pairs Native.witness
  Native.selection Witness.family Witness.motive (numeral 2) vector

@[irreducible] def actualAll : ProofSyntax Native.Const hypotheses query := by
  have code := NativeVectorAll.Reading.arguments_equal Native.original Native.pairs Native.witness Native.selection
    (assumptions := hypotheses) Witness.family Witness.motive (numeral 2) (numeral 2) vector Witness.sourceVector
    (.eqRefl _) (fromTab Tab.shiftedExact)
  exact .impE (.eqPropER (CurriedPredicates.existsValue_nil_congr _ _ code)) (fromCases Cases.allQuery)

@[irreducible] def originalShape : ProofSyntax Native.Const hypotheses
    (IndexedVectorTreeBranchActivity.allowed input originalPredicate numbers Native.original.zero one numeral
      (numeral 2) Native.original.zero) :=
  IndexedVectorTreeNativeChildConditions.numericAllowed arrays input originalPredicate numbers one numeral (numeral 2)
    (fromTab (IndexedVectorTreeNativeTabulationControls.liftProof (IndexedVectorTreeNativeWitnessControls.numberMember _)))

def goal : ClosedFormula Native.Const := CurriedPredicates.existsValue [] (.app Witness.motive parent)

@[irreducible] def actualParent : ProofSyntax Native.Const hypotheses goal :=
  Parent.parentViaEta elementSelection arraySelection input originalPredicate numbers one numeral bottom shiftedSelection
    Witness.motive Witness.suppliedBranchCase (numeral 2) Native.original.zero Tab.sourceArray
    (fromCases Cases.branchCaseInput) vectorGuard actualAll originalShape pointwise

theorem actualParent_not_free : ¬ actualParent.FunctionExtensionalityFree := by
  unfold actualParent
  exact Parent.parentViaEta_not_free elementSelection arraySelection input originalPredicate numbers one numeral bottom
    shiftedSelection Witness.motive Witness.suppliedBranchCase (numeral 2) Native.original.zero Tab.sourceArray
    (fromCases Cases.branchCaseInput) vectorGuard actualAll originalShape pointwise

theorem actual_original_parent_holds : (model.denote goal values).down := sound actualParent

private def existentialRoot {Γ : Ctx Native.Base} (formula : Formula Native.Const Γ) : Bool :=
  match formula with | .ex _ => true | _ => false
theorem no_existential_input : hypotheses.all (fun formula => !existentialRoot formula) = true := by decide +kernel

private theorem not_input (formula : ClosedFormula Native.Const) (root : existentialRoot formula = true) : formula ∉ hypotheses := by
  intro present
  have forbidden := (List.all_eq_true.mp no_existential_input) formula present
  simp only [root,Bool.not_true,Bool.false_eq_true] at forbidden

theorem all_query_not_a_premise : query ∉ hypotheses := not_input query rfl
theorem final_parent_not_a_premise : goal ∉ hypotheses := not_input goal rfl

theorem wrong_shape_refused : ¬ Nonempty (ProofSyntax Native.Const hypotheses
    (IndexedVectorTreeBranchActivity.allowed input originalPredicate numbers Native.original.zero one numeral (numeral 2) one)) := by
  rintro ⟨claimed⟩
  have same := sound (IndexedVectorTreeBranchShapeNormalization.shape input originalPredicate numbers
    Native.original.zero one numeral (numeral 2) one claimed)
  have impossible : (1 : Nat) = 0 := congrArg ULift.down same
  cases impossible

theorem forged_inactive_value_refused : ¬ Nonempty (ProofSyntax Native.Const hypotheses
    (.eq (.app Tab.sourceArray (numeral 2)) Witness.solvedValue)) := by
  rintro ⟨claimed⟩
  have padded := model.eq_of_eqv_of_fullDomains full (sound (fromTab Tab.arrayPadding))
  have forged := model.eq_of_eqv_of_fullDomains full (sound claimed)
  exact IndexedVectorTreeNativeWitnessControls.solved_not_bottom (forged.symm.trans padded)

#print axioms pointwise
#print axioms actualAll
#print axioms actualParent
#print axioms actualParent_not_free
#print axioms actual_original_parent_holds
#print axioms wrong_shape_refused
#print axioms forged_inactive_value_refused

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredParentApplicationControls
