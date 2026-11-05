import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeFunctionPairs
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllInductionControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllInterpretation

/-!
# Actual All witnesses from the original nonempty Vector and induction contract

The evidence carrier is the same recursive space as the stored constructors.
Pairs use its independently checked two-child constructor representation. The
two additional assumptions select and recurse at the actual predicate-valued
All result type; head and tail retain their existing computation premises.
All twelve assumptions hold in the original function-vector model. No global
bundle witness is selected from the existential conclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllProductionControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open CurriedPredicates
open FiniteConstructorFieldEmbeddingControls (Base N E Number Space carriers)
open IndexedVectorTreeFunctionVectorFixture
open IndexedVectorTreeNativeChildConditionsControls (family solvedValue branchValue sourceVector tailVector)
open IndexedVectorTreeNativeAllInductionControls (diagonal diagonalContract)

def choiceLaw : ClosedFormula Const := SelectionProofs.principle readerSelection
def recursionLaw : ClosedFormula Const := NaturalRecursionProofs.statement zero successor (V ⇒ E ⇒ .prop)
def assumptions : List (ClosedFormula Const) :=
  choiceLaw :: recursionLaw :: IndexedVectorTreeFunctionPairs.assumptions

def lift {formula : ClosedFormula Const}
    (proof : ProofSyntax Const IndexedVectorTreeFunctionVectorFixture.assumptions formula) :
    ProofSyntax Const assumptions formula :=
  ((proof.prepend IndexedVectorTreeFunctionPairs.rawLaw).prepend recursionLaw).prepend choiceLaw

theorem lift_free {formula : ClosedFormula Const}
    (proof : ProofSyntax Const IndexedVectorTreeFunctionVectorFixture.assumptions formula)
    (free : proof.FunctionExtensionalityFree) : (lift proof).FunctionExtensionalityFree := by
  simpa only [lift, ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using free

def arrayPremises : ops.ComputationPremises assumptions :=
  (IndexedVectorTreeFunctionPairs.arrayPremises.prepend recursionLaw).prepend choiceLaw

theorem arrayPremises_free : arrayPremises.FunctionExtensionalityFree :=
  (IndexedVectorTreeFunctionPairs.arrayPremises.prepend recursionLaw).prepend_free choiceLaw
    (IndexedVectorTreeFunctionPairs.arrayPremises.prepend_free recursionLaw
      IndexedVectorTreeFunctionPairs.arrayPremises_free)

def arithmetic : SuccessorOrder.PeanoEvidence successor zero assumptions :=
  ((IndexedVectorTreeFunctionVectorFixture.arithmetic.prepend IndexedVectorTreeFunctionPairs.rawLaw).prepend recursionLaw).prepend choiceLaw

theorem arithmetic_free : arithmetic.Free :=
  ((IndexedVectorTreeFunctionVectorFixture.arithmetic.prepend IndexedVectorTreeFunctionPairs.rawLaw).prepend recursionLaw).prepend_free choiceLaw
    ((IndexedVectorTreeFunctionVectorFixture.arithmetic.prepend IndexedVectorTreeFunctionPairs.rawLaw).prepend_free recursionLaw
      (IndexedVectorTreeFunctionVectorFixture.arithmetic.prepend_free IndexedVectorTreeFunctionPairs.rawLaw
        IndexedVectorTreeFunctionVectorFixture.arithmetic_free))

def computation : NativeVectorAll.Existence.ComputationPremises original readerSelection assumptions where
  choice := .hyp ⟨0, by simp [assumptions]⟩
  recursion := .hyp ⟨1, by simp [assumptions]⟩
  head := arrayPremises.head
  tail := arrayPremises.tail

theorem computation_free : computation.FunctionExtensionalityFree :=
  ⟨True.intro, True.intro, arrayPremises_free.2.2.2.2.1, arrayPremises_free.2.2.2.2.2⟩

theorem recursion_holds : model.models recursionLaw := by
  intro initial _ step _
  let sequence : Number → Ty.denote carriers (V ⇒ E ⇒ .prop) :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨sequence, trivial, ?_, ?_⟩
  · intro vector _ point _
    rfl
  · intro n _ vector _ point _
    rfl

theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := by
  intro formula present
  rcases List.mem_cons.mp present with rfl | present
  · exact (model.models_iff_denote_closed _ values).mp (choice_holds _)
  · rcases List.mem_cons.mp present with rfl | inherited
    · exact (model.models_iff_denote_closed _ values).mp recursion_holds
    · exact IndexedVectorTreeFunctionPairs.assumptions_realizable _ inherited

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

def query : ClosedFormula Const := NativeVectorAll.Existence.query original
  IndexedVectorTreeFunctionPairs.pairs bottom readerSelection family diagonal (numeral 2) sourceVector

@[irreducible] def bundle : ProofSyntax Const assumptions query :=
  IndexedVectorTreeNativeAllFromChildren.ReaderGuard.produce original elementSelection arraySelection
    given onlyTrue numbers one numeral bottom diagonal IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
    (numeral 2) sourceVector (lift (IndexedVectorTreeNativeChildConditionsControls.numberMember _))
    arrayPremises arithmetic (lift IndexedVectorTreeNativeChildConditionsControls.originalVectorProof)
    (lift IndexedVectorTreeNativeAllInductionControls.inductionProof) computation

theorem bundle_free : bundle.FunctionExtensionalityFree := by
  unfold bundle
  exact IndexedVectorTreeNativeAllFromChildren.ReaderGuard.produce_free original elementSelection arraySelection
    given onlyTrue numbers one numeral bottom diagonal IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
    (numeral 2) sourceVector (lift (IndexedVectorTreeNativeChildConditionsControls.numberMember _))
    arrayPremises arithmetic (lift IndexedVectorTreeNativeChildConditionsControls.originalVectorProof)
    (lift IndexedVectorTreeNativeAllInductionControls.inductionProof) computation
    (lift_free _ (IndexedVectorTreeNativeChildConditionsControls.numberMember_free _))
    arrayPremises_free arithmetic_free
    (lift_free _ IndexedVectorTreeNativeChildConditionsControls.originalVectorProof_free)
    (lift_free _ IndexedVectorTreeNativeAllInductionControls.inductionProof_free) computation_free

theorem actual_nonempty_bundle_holds : (model.denote query values).down := sound bundle

theorem cons_denote (motive : ClosedTerm Const (E ⇒ E ⇒ .prop))
    (index : ClosedTerm Const N) (head : ClosedTerm Const E) (tail : ClosedTerm Const V)
    (point : Space) :
    (model.denote (NativeVectorAll.Reading.allCode original IndexedVectorTreeFunctionPairs.pairs
      bottom readerSelection family motive (.app successor index) (ops.toSignature.consValue index head tail))
      values point).down ↔
    ∃ first, model.adm E first ∧ ∃ second, model.adm E second ∧
      model.Eqv E (PredicateSigma.pairValue model IndexedVectorTreeFunctionPairs.pairs first second) point ∧
      (model.denote (.app motive head) values first).down ∧
      (model.denote (NativeVectorAll.Reading.allCode original IndexedVectorTreeFunctionPairs.pairs
        bottom readerSelection family motive index tail) values second).down := by
  have coded := NativeVectorAll.Interpretation.cons_denote original
    IndexedVectorTreeFunctionPairs.pairs bottom readerSelection family motive computation.choice computation.recursion
    model values (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    assumptions_realizable index head tail computation.head computation.tail point (by trivial)
  have constructor := (NativeVectorAll.Reading.operations original readerSelection).cons_apply
    (Δ := assumptions) family index head tail
  have same := NativeVectorAll.Reading.arguments_equal original IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
    (assumptions := assumptions) family motive (.app successor index) (.app successor index)
    _ (ops.toSignature.consValue index head tail) (.eqRefl _) constructor
  exact (model.eqv_arr_apply (sound same) (by trivial : model.adm E point)).symm.trans coded

theorem diagonal_cons_observation (index : ClosedTerm Const N)
    (head : ClosedTerm Const E) (tail : ClosedTerm Const V) (point : Space)
    (present : (model.denote (NativeVectorAll.Reading.allCode original IndexedVectorTreeFunctionPairs.pairs
      bottom readerSelection family diagonal (.app successor index) (ops.toSignature.consValue index head tail))
      values point).down) :
    PredicateSigma.firstValue model IndexedVectorTreeFunctionPairs.pairs point = model.denote head values ∧
    (model.denote (NativeVectorAll.Reading.allCode original IndexedVectorTreeFunctionPairs.pairs
      bottom readerSelection family diagonal index tail)
      values (PredicateSigma.secondValue model IndexedVectorTreeFunctionPairs.pairs point)).down := by
  obtain ⟨first, firstAdmitted, second, secondAdmitted, same, firstGuard, tailGuard⟩ :=
    (cons_denote diagonal index head tail point).mp present
  have equal := model.eq_of_eqv_of_fullDomains full same
  have firstEqual := model.eq_of_eqv_of_fullDomains full
    ((PredicateSigma.firstLaw_denote model IndexedVectorTreeFunctionPairs.pairs).mp
      IndexedVectorTreeFunctionPairs.pair_laws_realized.1 first firstAdmitted second secondAdmitted)
  have secondEqual := model.eq_of_eqv_of_fullDomains full
    ((PredicateSigma.secondLaw_denote model IndexedVectorTreeFunctionPairs.pairs).mp
      IndexedVectorTreeFunctionPairs.pair_laws_realized.2 first firstAdmitted second secondAdmitted)
  have firstObserved : PredicateSigma.firstValue model IndexedVectorTreeFunctionPairs.pairs point = first := by
    rw [← equal]
    exact firstEqual
  have secondObserved : PredicateSigma.secondValue model IndexedVectorTreeFunctionPairs.pairs point = second := by
    rw [← equal]
    exact secondEqual
  change model.Eqv E (model.denote head values) first at firstGuard
  refine ⟨firstObserved.trans (model.eq_of_eqv_of_fullDomains full firstGuard).symm, ?_⟩
  rw [secondObserved]
  exact tailGuard

theorem every_bundle_preserves_order (point : Space)
    (present : (model.denote (NativeVectorAll.Reading.allCode original IndexedVectorTreeFunctionPairs.pairs
      bottom readerSelection family diagonal (numeral 2) sourceVector) values point).down) :
    PredicateSigma.firstValue model IndexedVectorTreeFunctionPairs.pairs point = model.denote solvedValue values ∧
    PredicateSigma.firstValue model IndexedVectorTreeFunctionPairs.pairs
      (PredicateSigma.secondValue model IndexedVectorTreeFunctionPairs.pairs point) = model.denote branchValue values := by
  have first := diagonal_cons_observation one solvedValue tailVector point present
  have second := diagonal_cons_observation zero branchValue ops.nil
    (PredicateSigma.secondValue model IndexedVectorTreeFunctionPairs.pairs point) first.2
  exact ⟨first.1, second.1⟩

def falseQuery : ClosedFormula Const := NativeVectorAll.Existence.query original
  IndexedVectorTreeFunctionPairs.pairs bottom readerSelection family
    IndexedVectorTreeNativeAllInductionControls.falseMotive (numeral 2) sourceVector

theorem false_nonempty_bundle_refused : ¬ (model.denote falseQuery values).down := by
  rw [falseQuery, NativeVectorAll.Existence.query, existsValue_nil_denote]
  rintro ⟨point, _, member⟩
  have interpreted := NativeVectorAll.Interpretation.cons_denote original
    IndexedVectorTreeFunctionPairs.pairs bottom readerSelection family
    IndexedVectorTreeNativeAllInductionControls.falseMotive computation.choice computation.recursion
    model values (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    assumptions_realizable one solvedValue tailVector computation.head computation.tail
    point (by trivial)
  have constructor := NativeVectorAll.Reading.operations original readerSelection |>.cons_apply
    (Δ := assumptions) family one solvedValue tailVector
  have same := NativeVectorAll.Reading.arguments_equal original IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
    (assumptions := assumptions) family IndexedVectorTreeNativeAllInductionControls.falseMotive
    (numeral 2) (numeral 2) _ sourceVector (.eqRefl _) constructor
  have equal := model.eqv_arr_apply (sound same) (by trivial : model.adm E point)
  obtain ⟨_, _, _, _, _, impossible, _⟩ := interpreted.mp (equal.mpr member)
  exact impossible

theorem false_nonempty_bundle_unprovable : ¬ Nonempty (ProofSyntax Const assumptions falseQuery) := by
  rintro ⟨proof⟩
  exact false_nonempty_bundle_refused (sound proof)

@[irreducible] def emptyFalseBundle : ProofSyntax Const assumptions
    (NativeVectorAll.Existence.query original IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
      family IndexedVectorTreeNativeAllInductionControls.falseMotive zero original.nil) :=
  NativeVectorAll.Existence.nil_query original IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
    family IndexedVectorTreeNativeAllInductionControls.falseMotive computation.choice computation.recursion

theorem empty_false_bundle_holds : (model.denote
    (NativeVectorAll.Existence.query original IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
      family IndexedVectorTreeNativeAllInductionControls.falseMotive zero original.nil) values).down := sound emptyFalseBundle

theorem emptyFalseBundle_free : emptyFalseBundle.FunctionExtensionalityFree := by
  unfold emptyFalseBundle
  exact NativeVectorAll.Existence.nil_query_free original IndexedVectorTreeFunctionPairs.pairs bottom readerSelection
    family IndexedVectorTreeNativeAllInductionControls.falseMotive computation.choice computation.recursion
    computation_free.1 computation_free.2.1

#print axioms bundle_free
#print axioms assumptions_realizable
#print axioms actual_nonempty_bundle_holds
#print axioms every_bundle_preserves_order
#print axioms false_nonempty_bundle_unprovable
#print axioms empty_false_bundle_holds
#print axioms emptyFalseBundle_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllProductionControls
