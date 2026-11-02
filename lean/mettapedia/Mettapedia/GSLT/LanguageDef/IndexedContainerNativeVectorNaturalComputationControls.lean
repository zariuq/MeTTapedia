import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalComputationModel
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorAllFromChildren
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorProgram
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorBoundary
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllInterpretation

/-!
# Complete child and All evidence at the natural constructor

The nontrivial payload predicate selects zero. A represented natural
constructor point supplies the root-index section; actual lists of that
point provide vectors of every finite length. The complete child contract
and original All evidence are produced under a jointly realizable profile.
Root-index membership is not least membership of the outer recursive family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalComputationControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original pairs witness selection parameter)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorChildGuard
open IndexedContainerNativeVectorEvidenceModel (elementSelection arraySelection ops)
open FiniteConstructorEncoding CurriedPredicates

def predicate (n : Nat) := n = 0
noncomputable def model := IndexedContainerNativeVectorNaturalComputationModel.model predicate
def values : model.Valuation [] := fun entry => nomatch entry
theorem full : model.FullDomains := IndexedContainerNativeVectorNaturalComputationModel.full predicate
def payload := IndexedContainerNativeVectorNaturalComputationModel.payloadPredicate
def construct := IndexedContainerNativeVectorNaturalComputationModel.constructor
def bottom := IndexedContainerNativeVectorNaturalComputationModel.bottom
def tag : ClosedTerm Const E := parameter 21 _
def family : ClosedTerm Const (E ⇒ .prop) := .lam .top
def motive : ClosedTerm Const (E ⇒ W ⇒ .prop) := .lam (.lam .top)
def childPredicate := NativeVectorAll.Existence.lifted original family motive
def joint := IndexedContainerNativeVectorChildConditions.joint payload childPredicate construct
def zeroChildren : ClosedTerm Const (N ⇒ E) := .lam (weaken bottom)
def point : ClosedTerm Const E := ConstructorProjections.apply construct original.zero
  (encoded payload original.zero tag original.zero) zeroChildren

def separationLaw := NaturalNumeralProofs.separation original.zero original.successor
def injectivityLaw := NaturalNumeralProofs.injectivity original.successor
def payloadFact : ClosedFormula Const := .app payload tag
def assumptions := payloadFact :: separationLaw :: injectivityLaw :: IndexedContainerNativeVectorEvidenceModel.assumptions
def payloadMember : ProofSyntax Const assumptions payloadFact := .hyp ⟨0,by decide⟩
theorem payloadMember_free : payloadMember.FunctionExtensionalityFree := by trivial
def arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero assumptions :=
  ⟨.hyp ⟨1,by decide⟩,.hyp ⟨2,by decide⟩,.hyp ⟨3,by decide⟩⟩
theorem arithmetic_free : arithmetic.Free := by trivial
def arrayPremises : ops.ComputationPremises assumptions :=
  ((IndexedContainerNativeVectorEvidenceModel.arrayPremises.prepend injectivityLaw).prepend separationLaw).prepend payloadFact
def allPremises : NativeVectorAll.Existence.ComputationPremises original selection assumptions :=
  ((IndexedContainerNativeVectorEvidenceModel.allPremises.prepend injectivityLaw).prepend separationLaw).prepend payloadFact
theorem arrayPremises_free : arrayPremises.FunctionExtensionalityFree :=
  ((IndexedContainerNativeVectorEvidenceModel.arrayPremises.prepend injectivityLaw).prepend separationLaw).prepend_free _
    ((IndexedContainerNativeVectorEvidenceModel.arrayPremises.prepend injectivityLaw).prepend_free _
      (IndexedContainerNativeVectorEvidenceModel.arrayPremises.prepend_free _ IndexedContainerNativeVectorEvidenceModel.arrayPremises_free))
theorem allPremises_free : allPremises.FunctionExtensionalityFree :=
  ((IndexedContainerNativeVectorEvidenceModel.allPremises.prepend injectivityLaw).prepend separationLaw).prepend_free _
    ((IndexedContainerNativeVectorEvidenceModel.allPremises.prepend injectivityLaw).prepend_free _
      (IndexedContainerNativeVectorEvidenceModel.allPremises.prepend_free _ IndexedContainerNativeVectorEvidenceModel.allPremises_free))

def allowed (n : Nat) := IndexedContainerNativeVectorSourceGuards.allowedOfTag payload (numeral [] n) tag payloadMember
theorem allowed_free (n : Nat) : (allowed n).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorSourceGuards.allowedOfTag_free _ _ _ payloadMember payloadMember_free

attribute [local irreducible] IndexedConstructorGuards.ConstructorPrograms.rootIndex_intro
@[irreducible] def pointRootIndex : ProofSyntax Const assumptions ((constructors payload).rootIndex construct point .top) :=
  (constructors payload).rootIndex_intro construct (occurrence payload)
    (sourceArguments payload original.zero tag original.zero) zeroChildren .top (allowed 0)
    (IndexedContainerNativeVectorConstructorProgram.resultIndex payload original.zero tag)
set_option backward.isDefEq.respectTransparency true in
theorem pointRootIndex_free : pointRootIndex.FunctionExtensionalityFree := by
  unfold pointRootIndex
  exact (constructors payload).rootIndex_intro_free _ _ _ _ _ (allowed 0) _ (allowed_free 0)
    (IndexedContainerNativeVectorConstructorProgram.resultIndex_free payload original.zero tag)
def pointRoot : ProofSyntax Const assumptions
    (.app (IndexedContainerNativeVectorActiveEdge.rootPredicate payload construct) point) :=
  (constructors payload).rootAt_intro construct .top point pointRootIndex
theorem pointRoot_free : pointRoot.FunctionExtensionalityFree :=
  (constructors payload).rootAt_intro_free construct .top point pointRootIndex pointRootIndex_free

def pointMember : ProofSyntax Const assumptions (.app family point) := .impE (.eqPropER (.beta point .top)) .topI
theorem pointMember_free : pointMember.FunctionExtensionalityFree := by trivial
def pointMotive : ProofSyntax Const assumptions (.app (.app motive point) witness) :=
  .impE (.eqPropER (CurriedGuardProgramProofs.beta2 .top point witness)) .topI
theorem pointMotive_free : pointMotive.FunctionExtensionalityFree :=
  ⟨CurriedGuardProgramProofs.beta2_free _ _ _,True.intro⟩
def pointExists : ProofSyntax Const assumptions (existsValue [] (.app motive point)) :=
  existsValue_intro [] (.app motive point) PUnit.unit witness pointMotive
theorem pointExists_free : pointExists.FunctionExtensionalityFree :=
  existsValue_intro_free [] (.app motive point) PUnit.unit witness pointMotive pointMotive_free
def liftedPoint : ProofSyntax Const assumptions (.app childPredicate point) :=
  .impE (.eqPropER (NativeVectorAll.Existence.lifted_apply original family motive point))
    (.andI pointMember pointExists)
theorem liftedPoint_free : liftedPoint.FunctionExtensionalityFree :=
  ⟨NativeVectorAll.Existence.lifted_apply_free _ _ _ _,pointMember_free,pointExists_free⟩
def jointPoint := (IndexedContainerNativeVectorChildConditions.certifiedJointMember payload childPredicate construct point
  liftedPoint pointRootIndex liftedPoint_free pointRootIndex_free).val
theorem jointPoint_free : jointPoint.FunctionExtensionalityFree :=
  (IndexedContainerNativeVectorChildConditions.certifiedJointMember payload childPredicate construct point
    liftedPoint pointRootIndex liftedPoint_free pointRootIndex_free).property

def vector : Nat → ClosedTerm Const V
  | 0 => original.nil
  | n+1 => ops.toSignature.consValue (numeral [] n) point (vector n)
def vectorMember : (n : Nat) → ProofSyntax Const assumptions (ops.toSignature.member family (numeral [] n) (vector n))
  | 0 => ops.toSignature.nil_member family
  | n+1 => ops.toSignature.cons_member family (numeral [] n) point (vector n) pointMember (vectorMember n)
def jointVectorMember : (n : Nat) → ProofSyntax Const assumptions (ops.toSignature.member joint (numeral [] n) (vector n))
  | 0 => ops.toSignature.nil_member joint
  | n+1 => ops.toSignature.cons_member joint (numeral [] n) point (vector n) jointPoint (jointVectorMember n)
theorem vectorMember_free (n : Nat) : (vectorMember n).FunctionExtensionalityFree := by
  induction n with
  | zero => exact ops.toSignature.nil_member_free family
  | succ n previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ pointMember_free previous
theorem jointVectorMember_free (n : Nat) : (jointVectorMember n).FunctionExtensionalityFree := by
  induction n with
  | zero => exact ops.toSignature.nil_member_free joint
  | succ n previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ jointPoint_free previous

def conditions (n : Nat) := (IndexedContainerNativeVectorChildConditions.certifiedChildConditions elementSelection arraySelection
  payload childPredicate construct (numeral [] n) tag point (vector n) point bottom (numeral [] 0)
  (allowed n) arrayPremises arithmetic jointPoint (jointVectorMember n) jointPoint
  (allowed_free n) arrayPremises_free arithmetic_free jointPoint_free (jointVectorMember_free n) jointPoint_free).val
theorem conditions_free (n : Nat) : (conditions n).FunctionExtensionalityFree :=
  (IndexedContainerNativeVectorChildConditions.certifiedChildConditions elementSelection arraySelection
    payload childPredicate construct (numeral [] n) tag point (vector n) point bottom (numeral [] 0)
    (allowed n) arrayPremises arithmetic jointPoint (jointVectorMember n) jointPoint
    (allowed_free n) arrayPremises_free arithmetic_free jointPoint_free (jointVectorMember_free n) jointPoint_free).property
def sourceIHs (n : Nat) := IndexedContainerNativeVectorAllFromChildren.sourceHypotheses elementSelection arraySelection
  payload family motive construct (numeral [] n) tag point (vector n) point bottom (numeral [] 0)
  (allowed n) arrayPremises arithmetic.induction (vectorMember n) (conditions n) allPremises
theorem sourceIHs_free (n : Nat) : (sourceIHs n).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorAllFromChildren.sourceHypotheses_free elementSelection arraySelection
    payload family motive construct (numeral [] n) tag point (vector n) point bottom (numeral [] 0)
    (allowed n) arrayPremises arithmetic.induction (vectorMember n) (conditions n) allPremises
    (allowed_free n) arrayPremises_free arithmetic_free.2.2 (vectorMember_free n) (conditions_free n) allPremises_free

theorem payloadFact_holds : model.models payloadFact := by
  unfold model payloadFact payload tag IndexedContainerNativeVectorNaturalComputationModel.model
    IndexedContainerNativeVectorNaturalComputationModel.extra
  rfl

theorem tag_denote : model.denote tag values = ULift.up 0 := by
  unfold model tag IndexedContainerNativeVectorNaturalComputationModel.model
    IndexedContainerNativeVectorNaturalComputationModel.extra
  rfl
theorem zeroChildren_denote : model.denote zeroChildren values = fun _ => ULift.up 0 := by
  funext slot
  change model.denote (weaken bottom) (model.extend values slot) = ULift.up 0
  rw [Soundness.denote_weaken]
  exact IndexedContainerNativeVectorNaturalComputationModel.bottom_denote predicate
def pointData : IndexedContainerNativeVectorNaturalComputationModel.SourceData :=
  ⟨⟨0,by decide⟩,ULift.up 0,ULift.up 0,ULift.up 0,PUnit.unit⟩
theorem point_payload_matching : payloadEquivalence model [[N,E,N]]
    (model.denote (encoded payload original.zero tag original.zero) values) =
    Mettapedia.TypeTheory.FiniteConstructorEncoding.encode
      (Ty.denote.{0,0} IndexedContainerNativeVectorNaturalComputationModel.carrier) [[N,E,N]] pointData := by
  change payloadEquivalence model [[N,E,N]] (model.denote (encode [[N,E,N]] ⟨0,by decide⟩
    (original.zero,tag,original.zero,PUnit.unit)) values) = _
  rw [encode_denote]
  apply congrArg (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode
    (Ty.denote.{0,0} IndexedContainerNativeVectorNaturalComputationModel.carrier) [[N,E,N]])
  change (⟨⟨0,by decide⟩,model.denote original.zero values,model.denote tag values,
    model.denote original.zero values,PUnit.unit⟩ : IndexedContainerNativeVectorNaturalComputationModel.SourceData) = _
  erw [IndexedContainerNativeVectorNaturalComputationModel.zero_denote predicate,tag_denote]
  rfl
theorem point_nonzero : (model.denote point values).down ≠ 0 := by
  change ((model.denote construct values) (model.denote original.zero values)
    (model.denote (encoded payload original.zero tag original.zero) values) (model.denote zeroChildren values)).down ≠ 0
  erw [IndexedContainerNativeVectorNaturalComputationModel.constructor_denote predicate,
    IndexedContainerNativeVectorNaturalComputationModel.zero_denote predicate,zeroChildren_denote]
  unfold IndexedContainerNativeVectorNaturalComputationModel.constructorMeaning FiniteConstructorEncoding.NaturalRealization.construct
  erw [point_payload_matching]
  erw [Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.construct_encode]
  exact Nat.succ_ne_zero _
theorem vector_denote (n : Nat) : model.denote (vector n) values =
    ULift.up (List.replicate n (model.denote point values).down) := by
  induction n with
  | zero => rfl
  | succ n previous =>
      change ULift.up ((model.denote point values).down :: (model.denote (vector n) values).down) = _
      rw [previous]
      rfl
theorem payload_rejects_one : ¬ (model.denote payload values (ULift.up 1)).down := by
  unfold model payload IndexedContainerNativeVectorNaturalComputationModel.model
    IndexedContainerNativeVectorNaturalComputationModel.extra
  exact Nat.noConfusion
theorem evidence_retains_pair_shape :
    (ULift.up PredicateSigma.Controls.Evidence.refl : ULift.{1} PredicateSigma.Controls.Evidence) ≠
      ULift.up (.pair .refl .refl) := by
  intro same
  have impossible := congrArg ULift.down same
  cases impossible

theorem raw_injectivity_refused : ¬ model.models (ConstructorInjectivity.statement construct) := by
  intro claimed
  exact IndexedContainerNativeVectorConstructorBoundary.original_reading_refuses_full_injectivity
    model full payload construct bottom values ((model.models_iff_denote_closed _ values).mp claimed)
theorem separation_holds : model.models separationLaw := by
  intro n _ same
  exact Nat.noConfusion (show n.down+1 = (0:Nat) from congrArg ULift.down same)
theorem injectivity_holds : model.models injectivityLaw := by
  intro n _ m _
  constructor
  · intro same; apply ULift.ext; exact Nat.succ.inj (congrArg ULift.down same)
  · intro same; cases same; rfl
theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := by
  intro formula present
  simp only [assumptions,List.mem_cons] at present
  rcases present with rfl | rfl | rfl | present
  · exact payloadFact_holds
  · exact separation_holds
  · exact injectivity_holds
  · exact IndexedContainerNativeVectorNaturalComputationModel.computationAssumptions_realizable predicate _ present
theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realizable
theorem complete_child_contract_holds (n : Nat) : (model.denote
    (IndexedContainerNativeVectorAllFromChildren.contract elementSelection arraySelection payload family motive construct
      (numeral [] n) tag point (vector n) point bottom (numeral [] 0)) values).down := sound (conditions n)
theorem source_IHs_hold (n : Nat) : (model.denote
    (IndexedContainerNativeVectorAllFromChildren.hypotheses family motive (numeral [] n) point (vector n) point) values).down :=
  sound (sourceIHs n)

def emptyMotive : ClosedTerm Const (E ⇒ W ⇒ .prop) := .lam (.lam .bot)
def emptyQuery := NativeVectorAll.Existence.query original pairs witness selection family emptyMotive (numeral [] 1) (vector 1)
theorem empty_nonempty_bundle_refused : ¬ (model.denote emptyQuery values).down := by
  rw [emptyQuery,NativeVectorAll.Existence.query,existsValue_nil_denote]
  rintro ⟨evidence,_,present⟩
  have interpreted := NativeVectorAll.Interpretation.cons_denote original pairs witness selection family emptyMotive
    allPremises.choice allPremises.recursion model values (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable (numeral [] 0) point (vector 0) allPremises.head allPremises.tail evidence
    (model.base_mem .evidence evidence)
  obtain ⟨_,_,_,_,_,impossible,_⟩ := interpreted.mp present
  exact impossible

#print axioms assumptions_realizable
#print axioms point_nonzero
#print axioms vector_denote
#print axioms complete_child_contract_holds
#print axioms source_IHs_hold
#print axioms empty_nonempty_bundle_refused
#print axioms raw_injectivity_refused
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalComputationControls
