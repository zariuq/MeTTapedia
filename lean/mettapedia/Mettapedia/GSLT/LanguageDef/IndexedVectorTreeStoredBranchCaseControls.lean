import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchCase
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredParentApplicationControls

/-!
# Deriving the original strengthened branch contract in the Native4 world

The selected motive asks for the actual derived-family membership of its
element. At each active slot the original Vector supplies that membership;
the old complete child condition supplies the same edge and least membership.
An explicit W witness then supplies the lifted motive. No whole induction
contract, All query or final parent observation is introduced as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchCaseControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedVectorTreeNativeWitnessModel
namespace Witness
export IndexedVectorTreeNativeWitnessControls (family motive sourceVector suppliedBranchCase)
end Witness
namespace ParentControl
export IndexedVectorTreeStoredParentApplicationControls (hypotheses fromCases fromTab originalShape hypotheses_realizable)
end ParentControl
namespace Inputs
export IndexedVectorTreeSourceCaseApplicationInputs (vectorInput arrayPremises branchCaseInput choice recursion)
end Inputs
namespace All
export IndexedVectorTreeNativeAllFromChildren (inductionPredicate indexedMotive indexedMotive_subst indexedMotive_beta)
end All
namespace Family
export IndexedVectorTreeStoredFamily (family root signature construct)
end Family

noncomputable section

namespace SelectedMotive
variable {Γ Ξ : Ctx Native.Base} {Δ : List (Formula Native.Const Γ)}

def code (family : Term Native.Const Γ (Native.E ⇒ .prop)) : Term Native.Const Γ (Native.E ⇒ Native.W ⇒ .prop) :=
  .lam (.lam (.app (weaken (weaken family)) (.var (.vs .vz))))

theorem code_subst (images : Subst Native.Const Γ Ξ) (family : Term Native.Const Γ (Native.E ⇒ .prop)) :
    HOL.subst images (code family) = code (HOL.subst images family) := by
  simp only [code,HOL.subst,subst_weaken,Subst.lift]
  rfl
theorem code_rename (rho : Rename Native.Base Γ Ξ) (family : Term Native.Const Γ (Native.E ⇒ .prop)) :
    HOL.rename rho (code family) = code (HOL.rename rho family) := by
  simpa only [subst_ofRename] using code_subst (Subst.ofRename rho) family

@[irreducible] def beta (family : Term Native.Const Γ (Native.E ⇒ .prop))
    (point : Term Native.Const Γ Native.E) (witness : Term Native.Const Γ Native.W) :
    ProofSyntax Native.Const Δ (.eq (.app (.app (code family) point) witness) (.app family point)) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2 (.app (weaken (weaken family)) (.var (.vs .vz))) point witness)
  simp only [code,instantiate,HOL.subst,Subst.lift,Subst.single,subst_weaken,
    PredicateFixedPoint.subst_single_weaken]
  rw [← weaken,PredicateFixedPoint.subst_single_weaken]

@[irreducible] def existsAt (family : Term Native.Const Γ (Native.E ⇒ .prop)) (point : Term Native.Const Γ Native.E)
    (member : ProofSyntax Native.Const Δ (.app family point)) :
    ProofSyntax Native.Const Δ (CurriedPredicates.existsValue [] (.app (code family) point)) :=
  CurriedPredicates.existsValue_intro [] (.app (code family) point) PUnit.unit (weakenCtx Γ Native.witness)
    (.impE (.eqPropER (beta family point (weakenCtx Γ Native.witness))) member)

def property (family : Term Native.Const Γ (Native.E ⇒ .prop)) := All.indexedMotive (code family)
theorem property_rename (rho : Rename Native.Base Γ Ξ) (family : Term Native.Const Γ (Native.E ⇒ .prop)) :
    HOL.rename rho (property family) = property (HOL.rename rho family) := by
  rw [property,← subst_ofRename,All.indexedMotive_subst,code_subst]
  exact congrArg (fun shifted => All.indexedMotive (code shifted)) (subst_ofRename rho family)

@[irreducible] def propertyAt (family : Term Native.Const Γ (Native.E ⇒ .prop))
    (point : Term Native.Const Γ Native.E) (index : Formula Native.Const Γ)
    (member : ProofSyntax Native.Const Δ (.app family point)) :
    ProofSyntax Native.Const Δ (.app (.app (property family) point) index) :=
  .impE (.eqPropER (All.indexedMotive_beta (code family) point index)) (existsAt family point member)

@[irreducible] def liftAt (family : Term Native.Const Γ (Native.E ⇒ .prop))
    (root : Term Native.Const Γ (Native.E ⇒ .prop ⇒ .prop)) (point : Term Native.Const Γ Native.E)
    (member : ProofSyntax Native.Const Δ (.app family point)) :
    ProofSyntax Native.Const Δ (.app (IndexedPredicateInduction.lift root (property family)) point) := by
  apply ProofSyntax.impE (.eqPropER (IndexedPredicateInduction.lift_beta root (property family) point))
  refine .allI (.impI ?_)
  apply ProofSyntax.castIndices rfl ?_
    (propertyAt (weaken family) (weaken point) (.var .vz) ((member.renameShared Rename.weaken).prepend _))
  simp only [weaken,property_rename]

@[irreducible] def strengthen (least family : Term Native.Const Γ (Native.E ⇒ .prop))
    (root : Term Native.Const Γ (Native.E ⇒ .prop ⇒ .prop)) (point : Term Native.Const Γ Native.E)
    (leastMember : ProofSyntax Native.Const Δ (.app least point))
    (member : ProofSyntax Native.Const Δ (.app family point)) :
    ProofSyntax Native.Const Δ (.app (PredicateFixedPoint.intersection least
      (IndexedPredicateInduction.lift root (property family))) point) :=
  .impE (.eqPropER (PredicateFixedPoint.intersection_beta least (IndexedPredicateInduction.lift root (property family)) point))
    (.andI leastMember (liftAt family root point member))

end SelectedMotive

def arithmetic : SuccessorOrder.PeanoEvidence Native.original.successor Native.original.zero ParentControl.hypotheses where
  separation := ParentControl.fromTab (IndexedVectorTreeNativeTabulationControls.liftProof
    (IndexedVectorTreeNativeWitnessModel.arithmetic.separation.prepend IndexedVectorTreeNativeWitnessControls.fieldHyp))
  injectivity := ParentControl.fromTab (IndexedVectorTreeNativeTabulationControls.liftProof
    (IndexedVectorTreeNativeWitnessModel.arithmetic.injectivity.prepend IndexedVectorTreeNativeWitnessControls.fieldHyp))
  induction := ParentControl.fromTab (IndexedVectorTreeNativeTabulationControls.liftProof
    (IndexedVectorTreeNativeWitnessModel.arithmetic.induction.prepend IndexedVectorTreeNativeWitnessControls.fieldHyp))

def premises : arrays.ComputationPremises ParentControl.hypotheses where
  elementChoice := ParentControl.fromCases Inputs.arrayPremises.elementChoice
  elementRecursion := ParentControl.fromCases Inputs.arrayPremises.elementRecursion
  arrayChoice := ParentControl.fromCases Inputs.arrayPremises.arrayChoice
  arrayRecursion := ParentControl.fromCases Inputs.arrayPremises.arrayRecursion
  head := ParentControl.fromCases Inputs.arrayPremises.head
  tail := ParentControl.fromCases Inputs.arrayPremises.tail

def vectorMember : ProofSyntax Native.Const ParentControl.hypotheses
    (arrays.toSignature.member Witness.family (numeral 2) Witness.sourceVector) :=
  IndexedVectorTreeNativeChildConditions.ReaderGuard.memberOfGuard Native.original Native.selection Witness.family
    (numeral 2) Witness.sourceVector (ParentControl.fromCases Inputs.vectorInput)

abbrev slotContext : Ctx Native.Base := [Native.N]
def movedInput := input.substitute (Subst.ofRename (Rename.weaken (σ := Native.N)))
def movedSource : Term Native.Const slotContext (Native.N ⇒ .prop) := weaken originalPredicate
def movedNumbers : Term Native.Const slotContext (Native.N ⇒ .prop) := weaken numbers
def movedTags (i : Nat) : Term Native.Const slotContext Native.N := weaken (numeral i)
def movedBottom : Term Native.Const slotContext Native.E := weaken bottom
def movedLength : Term Native.Const slotContext Native.N := weaken (numeral 2)
def movedShape : Term Native.Const slotContext Native.N := weaken Native.original.zero
def movedVector : Term Native.Const slotContext Native.V := weaken Witness.sourceVector
def movedFamily := Family.family movedInput movedSource movedNumbers Native.original.zero one Native.original.successor movedTags movedBottom
def movedSignature := Family.signature movedInput movedSource movedNumbers Native.original.zero one Native.original.successor movedTags movedBottom
def movedRoot := Family.root movedInput movedSource movedNumbers Native.original.zero one movedTags
def movedPayload := IndexedVectorTreeBranchActivity.payload movedInput movedSource movedNumbers Native.original.zero one movedTags movedLength movedShape
def movedChildren := arrays.single movedLength movedVector movedBottom
def movedMotive : Term Native.Const slotContext (Native.E ⇒ Native.W ⇒ .prop) := weaken Witness.motive
def movedPredicate := All.inductionPredicate Native.original movedInput movedSource movedNumbers one movedTags movedBottom movedMotive
def slot : Term Native.Const slotContext Native.N := .var .vz
def active : Formula Native.Const slotContext :=
  IndexedVectorTreeBranchActivity.activity movedInput movedSource movedNumbers Native.original.zero one Native.original.successor
    movedTags movedLength movedShape slot

theorem motive_coherence : movedMotive = SelectedMotive.code movedFamily := by
  change HOL.rename Rename.weaken (SelectedMotive.code Witness.family) = _
  rw [SelectedMotive.code_rename]
  exact congrArg SelectedMotive.code (IndexedVectorTreeStoredFamilyTransport.family_rename input originalPredicate numbers
    Native.original.zero one Native.original.successor numeral bottom Rename.weaken)

def movedAdmitted := IndexedVectorTreeNativeChildConditions.weakenAllowed arrays input originalPredicate numbers one numeral
  (numeral 2) Native.original.zero ParentControl.originalShape
def movedMember := IndexedVectorTreeNativeChildConditions.weakenVector arrays input originalPredicate numbers one numeral bottom
  (numeral 2) Witness.sourceVector vectorMember

@[irreducible] def oldSlot := IndexedVectorTreeNativeChildConditions.sourceSlotConditions arrays movedInput movedSource movedNumbers one
  movedTags movedBottom movedLength movedShape movedVector slot movedAdmitted (premises.weaken Native.N)
  (arithmetic.rename Rename.weaken) movedMember

@[irreducible] def strongSlot : ProofSyntax Native.Const (weakenHyps (σ := Native.N) ParentControl.hypotheses)
    (movedSignature.slotConditions movedPredicate movedPayload movedChildren slot) := by
  let memberHypotheses := active :: weakenHyps (σ := Native.N) ParentControl.hypotheses
  have present : ProofSyntax Native.Const memberHypotheses
      (.and (.app (.app (.app movedSignature.validEdge movedPayload) slot) (.app movedChildren slot))
        (.app movedSignature.least (.app movedChildren slot))) :=
    .impE (.andEL (oldSlot.prepend active)) (.hyp 0)
  have bounded := ProofSyntax.andER (IndexedVectorTreeBranchActivity.activityReadback movedInput movedSource movedNumbers
    Native.original.zero one Native.original.successor movedTags movedLength movedShape slot (.hyp (Δ := memberHypotheses) 0))
  have childMember := arrays.singleMemberAtBound movedFamily movedLength movedVector movedBottom slot
    ((premises.weaken Native.N).prepend active) ((arithmetic.rename Rename.weaken).prepend active)
    (movedMember.prepend active) bounded
  have strengthened : ProofSyntax Native.Const memberHypotheses (.app movedPredicate (.app movedChildren slot)) := by
    unfold movedPredicate
    rw [motive_coherence]
    exact SelectedMotive.strengthen movedSignature.least movedFamily movedRoot (.app movedChildren slot) (.andER present) childMember
  exact .andI (.impI (.andI (.andEL present) strengthened)) (.andER oldSlot)

def signature := Family.signature input originalPredicate numbers Native.original.zero one Native.original.successor numeral bottom
def payload := IndexedVectorTreeBranchActivity.payload input originalPredicate numbers Native.original.zero one numeral
  (numeral 2) Native.original.zero
def predicate := All.inductionPredicate Native.original input originalPredicate numbers one numeral bottom Witness.motive
def originalStrongContract : ClosedFormula Native.Const := signature.childConditions predicate payload
  IndexedVectorTreeNativeTabulationControls.sourceArray

private theorem strong_body : originalStrongContract = .all
    (movedSignature.slotConditions movedPredicate movedPayload movedChildren slot) := by
  have activeMoved := IndexedVectorTreeStoredFamilyTransport.active_rename input originalPredicate numbers
    Native.original.zero one Native.original.successor numeral (Rename.weaken (σ := Native.N))
  have edgeMoved := IndexedVectorTreeStoredFamilyTransport.edge_rename input originalPredicate numbers
    Native.original.zero one Native.original.successor numeral (Rename.weaken (σ := Native.N))
  have predicateMoved : HOL.rename (Rename.weaken (σ := Native.N)) predicate = movedPredicate := by
    change HOL.rename (Rename.weaken (σ := Native.N)) predicate =
      All.inductionPredicate Native.original movedInput movedSource movedNumbers one movedTags movedBottom movedMotive
    rw [show movedTags = (fun i => weaken (numeral i)) from funext (fun _ => rfl)]
    simpa only [predicate,movedInput,movedSource,movedNumbers,movedBottom,movedMotive,
      subst_ofRename,weaken] using
      (IndexedVectorTreeNativeAllFromChildren.inductionPredicate_subst Native.original input originalPredicate numbers
        one numeral bottom Witness.motive (Subst.ofRename (Rename.weaken (σ := Native.N))))
  have activeCode : signature.active = (IndexedVectorTreeStoredConstructorRecovery.positions input originalPredicate numbers
      Native.original.zero one Native.original.successor numeral).activeProgram := rfl
  have edgeCode : signature.validEdge = (IndexedVectorTreeStoredConstructorRecovery.positions input originalPredicate numbers
      Native.original.zero one Native.original.successor numeral).edgeProgram (Family.construct input) := rfl
  have bottomCode : signature.bottom = bottom := rfl
  unfold originalStrongContract RecursiveSpacePredicate.Contextual.childConditions RecursiveSpacePredicate.Contextual.slotConditions
  change Term.all _ = _
  simp only [weaken,activeCode,edgeCode,bottomCode,activeMoved,edgeMoved,payload,
    predicateMoved,IndexedVectorTreeNativeTabulationControls.sourceArray,VectorChildArrays.Operations.single_rename]
  rfl

@[irreducible] def originalStrongProof : ProofSyntax Native.Const ParentControl.hypotheses originalStrongContract :=
  .castIndices rfl strong_body.symm (.allI strongSlot)

theorem original_strong_contract_realized : (model.denote originalStrongContract values).down :=
  IndexedVectorTreeStoredParentApplicationControls.sound originalStrongProof

def tabulation : VectorTabulation.Shifted.ComputationPremises arrays shiftedSelection ParentControl.hypotheses where
  choice := ParentControl.fromTab IndexedVectorTreeNativeTabulationControls.shiftedChoice
  recursion := ParentControl.fromTab IndexedVectorTreeNativeTabulationControls.shiftedRecursion

def allPremises : NativeVectorAll.Existence.ComputationPremises Native.original Native.selection ParentControl.hypotheses where
  choice := ParentControl.fromCases Inputs.choice
  recursion := ParentControl.fromCases Inputs.recursion
  head := premises.head
  tail := premises.tail

@[irreducible] def actualBranch : ProofSyntax Native.Const ParentControl.hypotheses
    IndexedVectorTreeStoredParentApplicationControls.goal :=
  IndexedVectorTreeStoredBranchCase.applyViaEta elementSelection arraySelection input originalPredicate numbers one numeral bottom
    shiftedSelection Witness.motive Witness.suppliedBranchCase (numeral 2) Native.original.zero
    IndexedVectorTreeNativeTabulationControls.sourceArray ParentControl.originalShape originalStrongProof
    tabulation arithmetic premises allPremises (ParentControl.fromCases Inputs.branchCaseInput)

theorem actualBranch_not_free : ¬ actualBranch.FunctionExtensionalityFree := by
  unfold actualBranch
  exact IndexedVectorTreeStoredBranchCase.applyViaEta_not_free elementSelection arraySelection input originalPredicate numbers
    one numeral bottom shiftedSelection Witness.motive Witness.suppliedBranchCase (numeral 2) Native.original.zero
    IndexedVectorTreeNativeTabulationControls.sourceArray ParentControl.originalShape originalStrongProof
    tabulation arithmetic premises allPremises (ParentControl.fromCases Inputs.branchCaseInput)

theorem actual_original_branch_holds :
    (model.denote IndexedVectorTreeStoredParentApplicationControls.goal values).down :=
  IndexedVectorTreeStoredParentApplicationControls.sound actualBranch

private def wholeChildContractRoot {Γ : Ctx Native.Base} (formula : Formula Native.Const Γ) : Bool :=
  match formula with | .all (.and _ _) => true | _ => false
theorem no_child_contract_input :
    ParentControl.hypotheses.all (fun formula => !wholeChildContractRoot formula) = true := by decide +kernel
theorem original_strong_contract_not_a_premise : originalStrongContract ∉ ParentControl.hypotheses := by
  intro present
  have refused := (List.all_eq_true.mp no_child_contract_input) originalStrongContract present
  change (!true) = true at refused
  cases refused

#print axioms SelectedMotive.strengthen
#print axioms motive_coherence
#print axioms strongSlot
#print axioms originalStrongProof
#print axioms actualBranch
#print axioms actualBranch_not_free
#print axioms actual_original_branch_holds
#print axioms original_strong_contract_not_a_premise

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchCaseControls
