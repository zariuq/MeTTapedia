import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditionsControls
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeReflexiveAllMotive
import Mettapedia.Logic.HOL.ContextualChildPredicateMonotonicity

/-!
# Actual nonempty induction contracts for value-dependent All evidence

The original length-two Vector contains distinct members of the same derived
family. Its independently proved child contract is strengthened for the
motive e = w, using the actual element as witness. A false motive cannot
supply the induction contract for that Vector. Distinct evidence values
cannot be substituted merely because their source indices agree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllInductionControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FiniteConstructorEncoding CurriedPredicates PredicateFixedPoint
open FiniteConstructorFieldEmbeddingControls (Base N A E)
open IndexedVectorTreeFunctionVectorFixture
open IndexedVectorTreeNativeChildConditionsControls

def diagonal : ClosedTerm Const (E ⇒ E ⇒ .prop) := IndexedVectorTreeReflexiveAllMotive.motive
def root := IndexedVectorTreeStoredFamily.root given onlyTrue numbers zero one numeral
def diagonalPredicate := IndexedVectorTreeNativeAllFromChildren.inductionPredicate
  original given onlyTrue numbers one numeral bottom diagonal
def diagonalContract := IndexedVectorTreeNativeAllFromChildren.contract original elementSelection arraySelection
  given onlyTrue numbers one numeral bottom diagonal (numeral 2) zero sourceVector

@[irreducible] def inclusionProof : ProofSyntax Const assumptions (included signature.least diagonalPredicate) :=
  IndexedVectorTreeReflexiveAllMotive.inclusion signature.least root
theorem inclusionProof_free : inclusionProof.FunctionExtensionalityFree := by
  unfold inclusionProof
  exact IndexedVectorTreeReflexiveAllMotive.inclusion_free _ _

@[irreducible] def inductionProof : ProofSyntax Const assumptions diagonalContract :=
  signature.childConditions_mono signature.least diagonalPredicate payload children inclusionProof childProof
theorem inductionProof_free : inductionProof.FunctionExtensionalityFree := by
  unfold inductionProof
  exact signature.childConditions_mono_free _ _ _ _ inclusionProof childProof inclusionProof_free childProof_free

theorem diagonal_contract_realized : (model.denote diagonalContract values).down := sound inductionProof

@[irreducible] def firstEvidence : ProofSyntax Const assumptions (existsValue [] (.app diagonal solvedValue)) :=
  IndexedVectorTreeNativeAllFromChildren.pointEvidence original elementSelection arraySelection
    given onlyTrue numbers one numeral bottom diagonal (numeral 2) zero sourceVector zero solvedValue
    (IndexedVectorTreeNativeChildConditions.numericAllowed ops given onlyTrue numbers one numeral (numeral 2) (numberMember _))
    premises arithmetic vectorProof inductionProof firstLookup

theorem firstLookup_free : firstLookup.FunctionExtensionalityFree := by
  unfold firstLookup
  exact IndexedVectorPositions.here_free _ _ _ _

theorem firstEvidence_free : firstEvidence.FunctionExtensionalityFree := by
  unfold firstEvidence
  exact IndexedVectorTreeNativeAllFromChildren.pointEvidence_free original elementSelection arraySelection
    given onlyTrue numbers one numeral bottom diagonal (numeral 2) zero sourceVector zero solvedValue
    (IndexedVectorTreeNativeChildConditions.numericAllowed ops given onlyTrue numbers one numeral (numeral 2) (numberMember _))
    premises arithmetic vectorProof inductionProof firstLookup
    (IndexedVectorTreeNativeChildConditions.numericAllowed_free _ _ _ _ _ _ _ _ (numberMember_free _))
    premises_free arithmetic_free vectorProof_free inductionProof_free firstLookup_free

theorem first_evidence_realized : (model.denote (existsValue [] (.app diagonal solvedValue)) values).down := sound firstEvidence

def wrongWitness : ClosedFormula Const := .app (.app diagonal solvedValue) branchValue
theorem wrong_witness_refused : ¬ (model.denote wrongWitness values).down := by
  intro present
  have beta : ProofSyntax Const assumptions (.eq wrongWitness (.eq solvedValue branchValue)) :=
    IndexedVectorTreeReflexiveAllMotive.motive_beta solvedValue branchValue
  have equation := (sound beta).mp present
  exact constructor_values_distinct (model.eq_of_eqv_of_fullDomains full equation)

def falseMotive {Γ : Ctx Base} : Term Const Γ (E ⇒ E ⇒ .prop) := .lam (.lam .bot)

@[irreducible] def false_beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (point witness : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (.app (.app falseMotive point) witness) .bot) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2 .bot point witness)
  rfl

def falseWitnessRefute {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (point : Term Const Γ E)
    (present : ProofSyntax Const Δ (existsValue [] (.app falseMotive point))) : ProofSyntax Const Δ .bot := by
  have unfolded := ProofSyntax.impE (.eqPropEL (existsValue_beta [] (.app falseMotive point) PUnit.unit)) present
  apply ProofSyntax.exE unfolded
  apply ProofSyntax.impE (.eqPropEL (false_beta (weaken point) (.var .vz)))
  exact .hyp 0

def falseContract := IndexedVectorTreeNativeAllFromChildren.contract original elementSelection arraySelection
  given onlyTrue numbers one numeral bottom falseMotive (numeral 2) zero sourceVector

@[irreducible] def falseContractRefute : ProofSyntax Const assumptions (.not falseContract) :=
  .notI (falseWitnessRefute solvedValue
    (IndexedVectorTreeNativeAllFromChildren.pointEvidence original elementSelection arraySelection
      given onlyTrue numbers one numeral bottom falseMotive (numeral 2) zero sourceVector zero solvedValue
      ((IndexedVectorTreeNativeChildConditions.numericAllowed ops given onlyTrue numbers one numeral (numeral 2) (numberMember _)).prepend falseContract)
      (premises.prepend falseContract) (arithmetic.prepend falseContract) (vectorProof.prepend falseContract)
      (.hyp (Δ := falseContract :: assumptions) 0) (firstLookup.prepend falseContract)))

theorem false_nonempty_induction_contract_refused : ¬ (model.denote falseContract values).down := sound falseContractRefute

theorem false_nonempty_induction_contract_unprovable : ¬ Nonempty (ProofSyntax Const assumptions falseContract) := by
  rintro ⟨proof⟩
  exact false_nonempty_induction_contract_refused (sound proof)

#print axioms inductionProof_free
#print axioms firstEvidence_free
#print axioms diagonal_contract_realized
#print axioms wrong_witness_refused
#print axioms false_nonempty_induction_contract_unprovable
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllInductionControls
