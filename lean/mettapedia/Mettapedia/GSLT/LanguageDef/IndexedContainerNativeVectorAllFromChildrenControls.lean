import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorAllFromChildren
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorEvidenceModel
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditionsControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllInterpretation

/-!
# Independent controls for producing original All bundles from children

The nontrivial element predicate excludes padding. Tree evidence realizes
the original All profile together with both array profiles. For every vector
length, field proofs construct the child contract and the new route derives
all three source IH premises. An empty motive refuses a nonempty bundle.
The field-erasing outer operation remains a deliberate conditional fixture,
not an installed datatype constructor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorAllFromChildrenControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original pairs witness selection)
open IndexedContainerNativeVectorPositionReading (numeral)
open IndexedContainerNativeVectorEvidenceModel (model values full ops elementSelection arraySelection)
open IndexedContainerNativeVectorChildConditionsControls (projectionOperation selectedValue selectedMember selectedMember_free selectedRoot selectedRoot_free)
open FiniteConstructorEncoding CurriedPredicates

def payload := IndexedContainerNativeVectorPositionModel.payload
def tag := IndexedContainerNativeVectorPositionModel.tag
def family := IndexedContainerNativeVectorChildConditionsControls.elements
def bottom := IndexedContainerNativeVectorChildConditionsControls.padding
def motive : ClosedTerm Const (E ⇒ W ⇒ .prop) :=
  .lam (.lam (.app (weaken (weaken family)) (.var (.vs .vz))))
def childPredicate := NativeVectorAll.Existence.lifted original family motive
def joint := IndexedContainerNativeVectorChildConditions.joint payload childPredicate projectionOperation
def separationLaw := NaturalNumeralProofs.separation original.zero original.successor
def injectivityLaw := NaturalNumeralProofs.injectivity original.successor
def assumptions : List (ClosedFormula Const) := separationLaw :: injectivityLaw :: IndexedContainerNativeVectorEvidenceModel.assumptions
def arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero assumptions :=
  ⟨.hyp ⟨0,by decide⟩,.hyp ⟨1,by decide⟩,.hyp ⟨2,by decide⟩⟩
def arrayPremises : ops.ComputationPremises assumptions :=
  (IndexedContainerNativeVectorEvidenceModel.arrayPremises.prepend injectivityLaw).prepend separationLaw
def allPremises : NativeVectorAll.Existence.ComputationPremises original selection assumptions :=
  (IndexedContainerNativeVectorEvidenceModel.allPremises.prepend injectivityLaw).prepend separationLaw
theorem arithmetic_free : arithmetic.Free := by trivial
theorem arrayPremises_free : arrayPremises.FunctionExtensionalityFree :=
  (IndexedContainerNativeVectorEvidenceModel.arrayPremises.prepend injectivityLaw).prepend_free _
    (IndexedContainerNativeVectorEvidenceModel.arrayPremises.prepend_free _ IndexedContainerNativeVectorEvidenceModel.arrayPremises_free)
theorem allPremises_free : allPremises.FunctionExtensionalityFree :=
  (IndexedContainerNativeVectorEvidenceModel.allPremises.prepend injectivityLaw).prepend_free _
    (IndexedContainerNativeVectorEvidenceModel.allPremises.prepend_free _ IndexedContainerNativeVectorEvidenceModel.allPremises_free)

def payloadMember : ProofSyntax Const assumptions (.app payload tag) := .impE (.eqPropER (.beta tag .top)) .topI
theorem payloadMember_free : payloadMember.FunctionExtensionalityFree := by trivial
def allowed (n : Nat) := IndexedContainerNativeVectorSourceGuards.allowedOfTag payload (numeral [] n) tag payloadMember
theorem allowed_free (n : Nat) : (allowed n).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorSourceGuards.allowedOfTag_free _ _ _ payloadMember payloadMember_free

def motiveBeta : ProofSyntax Const assumptions (.eq (.app (.app motive selectedValue) witness) (.app family selectedValue)) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2 (.app (weaken (weaken family)) (.var (.vs .vz))) selectedValue witness)
  simp only [instantiate,HOL.subst,Subst.lift,Subst.single,subst_weaken,PredicateFixedPoint.subst_single_weaken]
  rfl
theorem motiveBeta_free : motiveBeta.FunctionExtensionalityFree := by
  unfold motiveBeta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _
def pointEvidence : ProofSyntax Const assumptions (.app (.app motive selectedValue) witness) :=
  .impE (.eqPropER motiveBeta) selectedMember
theorem pointEvidence_free : pointEvidence.FunctionExtensionalityFree := ⟨motiveBeta_free,selectedMember_free⟩
def pointExists : ProofSyntax Const assumptions (existsValue [] (.app motive selectedValue)) :=
  existsValue_intro [] (.app motive selectedValue) PUnit.unit witness pointEvidence
theorem pointExists_free : pointExists.FunctionExtensionalityFree :=
  existsValue_intro_free [] (.app motive selectedValue) PUnit.unit witness pointEvidence pointEvidence_free

@[irreducible] def liftedPoint : ProofSyntax Const assumptions (.app childPredicate selectedValue) :=
  .impE (.eqPropER (NativeVectorAll.Existence.lifted_apply original family motive selectedValue))
    (.andI selectedMember pointExists)
theorem liftedPoint_free : liftedPoint.FunctionExtensionalityFree := by
  unfold liftedPoint
  exact ⟨NativeVectorAll.Existence.lifted_apply_free _ _ _ _, selectedMember_free, pointExists_free⟩

def jointPoint : ProofSyntax Const assumptions (.app joint selectedValue) :=
  (IndexedContainerNativeVectorChildConditions.certifiedJointMember payload childPredicate projectionOperation selectedValue
    liftedPoint (selectedRoot (allowed 0)) liftedPoint_free (selectedRoot_free (allowed 0) (allowed_free 0))).val
theorem jointPoint_free : jointPoint.FunctionExtensionalityFree :=
  (IndexedContainerNativeVectorChildConditions.certifiedJointMember payload childPredicate projectionOperation selectedValue
    liftedPoint (selectedRoot (allowed 0)) liftedPoint_free (selectedRoot_free (allowed 0) (allowed_free 0))).property

def vector : Nat → ClosedTerm Const V
  | 0 => original.nil
  | n+1 => ops.toSignature.consValue (numeral [] n) selectedValue (vector n)
def vectorMember : (n : Nat) → ProofSyntax Const assumptions (ops.toSignature.member family (numeral [] n) (vector n))
  | 0 => ops.toSignature.nil_member family
  | n+1 => ops.toSignature.cons_member family (numeral [] n) selectedValue (vector n) selectedMember (vectorMember n)
def jointVectorMember : (n : Nat) → ProofSyntax Const assumptions (ops.toSignature.member joint (numeral [] n) (vector n))
  | 0 => ops.toSignature.nil_member joint
  | n+1 => ops.toSignature.cons_member joint (numeral [] n) selectedValue (vector n) jointPoint (jointVectorMember n)
theorem vectorMember_free (n : Nat) : (vectorMember n).FunctionExtensionalityFree := by
  induction n with
  | zero => exact ops.toSignature.nil_member_free family
  | succ n previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ selectedMember_free previous
theorem jointVectorMember_free (n : Nat) : (jointVectorMember n).FunctionExtensionalityFree := by
  induction n with
  | zero => exact ops.toSignature.nil_member_free joint
  | succ n previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ jointPoint_free previous

def conditions (n : Nat) := (IndexedContainerNativeVectorChildConditions.certifiedChildConditions elementSelection arraySelection
  payload childPredicate projectionOperation (numeral [] n) tag selectedValue (vector n) selectedValue bottom (numeral [] 0)
  (allowed n) arrayPremises arithmetic jointPoint (jointVectorMember n) jointPoint
  (allowed_free n) arrayPremises_free arithmetic_free jointPoint_free (jointVectorMember_free n) jointPoint_free).val
theorem conditions_free (n : Nat) : (conditions n).FunctionExtensionalityFree :=
  (IndexedContainerNativeVectorChildConditions.certifiedChildConditions elementSelection arraySelection
    payload childPredicate projectionOperation (numeral [] n) tag selectedValue (vector n) selectedValue bottom (numeral [] 0)
    (allowed n) arrayPremises arithmetic jointPoint (jointVectorMember n) jointPoint
    (allowed_free n) arrayPremises_free arithmetic_free jointPoint_free (jointVectorMember_free n) jointPoint_free).property

def sourceIHs (n : Nat) : ProofSyntax Const assumptions
    (IndexedContainerNativeVectorAllFromChildren.hypotheses family motive (numeral [] n) selectedValue (vector n) selectedValue) :=
  IndexedContainerNativeVectorAllFromChildren.sourceHypotheses elementSelection arraySelection payload family motive projectionOperation
    (numeral [] n) tag selectedValue (vector n) selectedValue bottom (numeral [] 0) (allowed n) arrayPremises arithmetic.induction
    (vectorMember n) (conditions n) allPremises
theorem sourceIHs_free (n : Nat) : (sourceIHs n).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorAllFromChildren.sourceHypotheses_free elementSelection arraySelection payload family motive projectionOperation
    (numeral [] n) tag selectedValue (vector n) selectedValue bottom (numeral [] 0) (allowed n) arrayPremises arithmetic.induction
    (vectorMember n) (conditions n) allPremises (allowed_free n) arrayPremises_free arithmetic_free.2.2
    (vectorMember_free n) (conditions_free n) allPremises_free

theorem separation_holds : model.models separationLaw := by
  intro n _ same
  have impossible : n.down+1 = (0:Nat) := congrArg ULift.down same
  exact Nat.noConfusion impossible
theorem injectivity_holds : model.models injectivityLaw := by
  intro n _ m _
  constructor
  · intro same; apply ULift.ext; exact Nat.succ.inj (congrArg ULift.down same)
  · intro same; cases same; rfl
theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := by
  intro formula present
  simp only [assumptions,List.mem_cons] at present
  rcases present with rfl | rfl | present
  · exact separation_holds
  · exact injectivity_holds
  · exact IndexedContainerNativeVectorEvidenceModel.assumptions_realizable _ present
theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) : (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realizable
theorem source_IHs_hold (n : Nat) :
    (model.denote (IndexedContainerNativeVectorAllFromChildren.hypotheses family motive (numeral [] n)
      selectedValue (vector n) selectedValue) values).down := sound (sourceIHs n)

def emptyMotive : ClosedTerm Const (E ⇒ W ⇒ .prop) := .lam (.lam .bot)
def emptyQuery := NativeVectorAll.Existence.query original pairs witness selection family emptyMotive (numeral [] 1) (vector 1)
theorem empty_nonempty_bundle_refused : ¬ (model.denote emptyQuery values).down := by
  rw [emptyQuery, NativeVectorAll.Existence.query, existsValue_nil_denote]
  rintro ⟨point, _, present⟩
  have interpretation := NativeVectorAll.Interpretation.cons_denote original pairs witness selection family emptyMotive
    allPremises.choice allPremises.recursion model values (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable (numeral [] 0) selectedValue (vector 0) allPremises.head allPremises.tail point
    (model.base_mem .evidence point)
  obtain ⟨_,_,_,_,_,impossible,_⟩ := interpretation.mp present
  exact impossible
theorem cannot_invent_missing_IHs : ¬ Nonempty (ProofSyntax Const assumptions emptyQuery) := by
  rintro ⟨proof⟩
  exact empty_nonempty_bundle_refused (sound proof)

#print axioms sourceIHs_free
#print axioms source_IHs_hold
#print axioms cannot_invent_missing_IHs
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorAllFromChildrenControls
