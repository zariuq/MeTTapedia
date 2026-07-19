import Mettapedia.Languages.Metamath.InferenceActiveHypothesisLeaf
import Mettapedia.Languages.Metamath.InferenceAssertionApplication

/-!
# Static source-pinned views of generated Metamath derivations

A `GeneratedProvesTree` is a canonical view of an existing generic generated
`Derivation`: its root is pinned to either a projected active hypothesis or a
projected assertion, and every leading `Proves` premise has an ordered
recursive view.  Assertion side evidence remains the native derivation data
already stored by `GeneratedAssertionNode`.

This is not a second proof calculus.  `toDerivation` assembles the generic
native derivation, `canonicalRawProof` states its exact structural erasure, and
`leadingPremisePostfixLabels` recovers the authored source labels while
deliberately skipping assertion side-premise derivations.  No runtime proof
state or checker execution is imported here.

An arbitrary generic `Derivation` is not assumed to possess this view.  Its
normalization requires separate source-rule classification and premise
decoding theorems.
-/

namespace Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement

/-! ## Source-pinned recursive view -/

mutual

/-- A source-pinned recursive view of a generated derivation of one encoded
Metamath formula. -/
inductive GeneratedProvesTree (projection : PrefixProjection)
    (target : ValidatedPresentation) : ConstantHeadedFormula → Type where
  | active (hypothesis : HypothesisView)
      (hmember : hypothesis ∈ projection.activeHypotheses) :
      GeneratedProvesTree projection target hypothesis.formula
  | assertion {assertion : AssertionView}
      {actuals : List ConstantHeadedFormula}
      {result : ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      (hmember : assertion ∈ projection.assertions)
      (node : GeneratedAssertionNode projection target assertion actuals
        result substitution)
      (children : GeneratedProvesForest projection target actuals) :
      GeneratedProvesTree projection target result

/-- Ordered source-pinned views for an exact list of assertion premises. -/
inductive GeneratedProvesForest (projection : PrefixProjection)
    (target : ValidatedPresentation) :
    List ConstantHeadedFormula → Type where
  | nil : GeneratedProvesForest projection target []
  | cons {formula : ConstantHeadedFormula}
      {formulas : List ConstantHeadedFormula}
      (head : GeneratedProvesTree projection target formula)
      (tail : GeneratedProvesForest projection target formulas) :
      GeneratedProvesForest projection target (formula :: formulas)

end

/-! ## Assembly into generic native derivations -/

mutual

/-- Assemble the existing generic native derivation represented by a
source-pinned tree. -/
def GeneratedProvesTree.toDerivation {projection : PrefixProjection}
    {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula) :
    Derivation target (proves (encodeFormula formula)) :=
  match tree with
  | .active _ hmember =>
      activeHypothesisDerivation projection target hprojection hmember
  | .assertion _ node children =>
      node.assemble (children.toDerivationList hprojection)

/-- Assemble the exact ordered list of generic `Proves` derivations. -/
def GeneratedProvesForest.toDerivationList {projection : PrefixProjection}
    {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas) :
    DerivationList target (assertionProvesPremises formulas) :=
  match forest with
  | .nil => .nil
  | .cons head tail =>
      .cons (head.toDerivation hprojection)
        (tail.toDerivationList hprojection)

end

/-! ## Authored postfix labels -/

mutual

/-- Authored normal-proof labels in postfix order.  Natively checked side
derivations are not emitted as source labels. -/
def GeneratedProvesTree.labels {projection : PrefixProjection}
    {target : ValidatedPresentation} {formula : ConstantHeadedFormula} :
    GeneratedProvesTree projection target formula → List String
  | .active hypothesis _ => [hypothesis.label]
  | .assertion (assertion := assertion) _ _ children =>
      children.labels ++ [assertion.label]

/-- Concatenate each tree's postfix labels in premise order. -/
def GeneratedProvesForest.labels {projection : PrefixProjection}
    {target : ValidatedPresentation} {formulas : List ConstantHeadedFormula} :
    GeneratedProvesForest projection target formulas → List String
  | .nil => []
  | .cons head tail => head.labels ++ tail.labels

end

/-! ## Exact structural raw erasure -/

mutual

/-- The canonical raw proof structurally represented by a source-pinned tree.
For an assertion, the recursive `Proves` children precede the exact stored
native side-evidence children. -/
def GeneratedProvesTree.canonicalRawProof
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula} :
    GeneratedProvesTree projection target formula → RawProof
  | .active hypothesis _ =>
      .node (activeHypothesisRuleInstance hypothesis) []
  | .assertion (assertion := assertion) (actuals := actuals)
      _ node children =>
      .node (assertionRuleInstance assertion actuals formula)
        (children.canonicalRawProofs ++
          node.sideEvidence.toDerivationList.erase)

/-- Canonical raw proofs for an ordered source-pinned forest. -/
def GeneratedProvesForest.canonicalRawProofs
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula} :
    GeneratedProvesForest projection target formulas → List RawProof
  | .nil => []
  | .cons head tail =>
      head.canonicalRawProof :: tail.canonicalRawProofs

end


@[simp] theorem GeneratedProvesForest.canonicalRawProofs_length
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas) :
    forest.canonicalRawProofs.length = formulas.length :=
  match forest with
  | .nil => rfl
  | .cons _ tail => by
      simp [GeneratedProvesForest.canonicalRawProofs,
        tail.canonicalRawProofs_length]
termination_by sizeOf forest

/-- Erasure commutes with the exact ordered append used to assemble assertion
children. -/
theorem erase_appendDerivationLists
    {presentation : ValidatedPresentation}
    {left right : List Pattern}
    (leftDerivations : DerivationList presentation left)
    (rightDerivations : DerivationList presentation right) :
    (appendDerivationLists leftDerivations rightDerivations).erase =
      leftDerivations.erase ++ rightDerivations.erase :=
  match leftDerivations with
  | .nil => rfl
  | .cons head tail => by
      simp [appendDerivationLists, DerivationList.erase,
        erase_appendDerivationLists tail rightDerivations]
termination_by sizeOf leftDerivations

/-- Assembling one local assertion node has the exact raw root and ordered
child split advertised by `GeneratedAssertionNode`. -/
theorem generatedAssertionNode_erase_assemble
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (provesEvidence : DerivationList target
      (assertionProvesPremises actuals)) :
    (node.assemble provesEvidence).erase =
      .node (assertionRuleInstance assertion actuals result)
        (provesEvidence.erase ++
          node.sideEvidence.toDerivationList.erase) := by
  simp [GeneratedAssertionNode.assemble, Derivation.erase,
    assertionPremises, erase_appendDerivationLists]

mutual

/-- The assembled generic derivation erases to the independently defined
canonical raw structure, not merely to some proof with the same conclusion. -/
theorem GeneratedProvesTree.erase_toDerivation
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula) :
    (tree.toDerivation hprojection).erase = tree.canonicalRawProof := by
  cases tree with
  | active hypothesis hmember =>
      simp [GeneratedProvesTree.toDerivation,
        GeneratedProvesTree.canonicalRawProof,
        activeHypothesisDerivation]
  | assertion hmember node children =>
      rw [GeneratedProvesTree.toDerivation,
        generatedAssertionNode_erase_assemble,
        children.erase_toDerivationList hprojection]
      rfl

/-- The assembled generic derivation list erases to the exact canonical raw
forest in the same premise order. -/
theorem GeneratedProvesForest.erase_toDerivationList
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas) :
    (forest.toDerivationList hprojection).erase =
      forest.canonicalRawProofs := by
  cases forest with
  | nil => rfl
  | cons head tail =>
      change (head.toDerivation hprojection).erase ::
          (tail.toDerivationList hprojection).erase =
        head.canonicalRawProof :: tail.canonicalRawProofs
      rw [GeneratedProvesTree.erase_toDerivation hprojection head,
        GeneratedProvesForest.erase_toDerivationList hprojection tail]

end

/-! ## Exact postfix recovery from raw erasure -/

mutual

/-- Read the generated-source postfix convention from a raw proof.  A
generated assertion instance has one argument per leading `Proves` child plus
one result argument, so `arguments.length - 1` selects exactly the authored
children and skips native side-evidence children.  This function is not
claimed to decode arbitrary raw proofs outside that generated convention. -/
def rawProofLeadingPremisePostfixLabels : RawProof → List String
  | .node ruleInstance children =>
      rawProofLeadingPremisePostfixLabelsFrom
          (ruleInstance.arguments.length - 1) children ++
        [ruleInstance.ruleId.value]

/-- Process at most the requested leading raw children. -/
def rawProofLeadingPremisePostfixLabelsFrom :
    Nat → List RawProof → List String
  | 0, _ => []
  | _ + 1, [] => []
  | count + 1, proof :: proofs =>
      rawProofLeadingPremisePostfixLabels proof ++
        rawProofLeadingPremisePostfixLabelsFrom count proofs

end

theorem rawProofLeadingPremisePostfixLabelsFrom_eq_take_flatMap
    (count : Nat) (proofs : List RawProof) :
    rawProofLeadingPremisePostfixLabelsFrom count proofs =
      (proofs.take count).flatMap rawProofLeadingPremisePostfixLabels := by
  induction count generalizing proofs with
  | zero => simp [rawProofLeadingPremisePostfixLabelsFrom]
  | succ count ih =>
      cases proofs with
      | nil => simp [rawProofLeadingPremisePostfixLabelsFrom]
      | cons proof proofs =>
          simp [rawProofLeadingPremisePostfixLabelsFrom, ih]

mutual

/-- The canonical raw proof recovers every authored source label in exact
postfix order, while omitting all native assertion side evidence. -/
theorem GeneratedProvesTree.canonicalRawProof_postfixLabels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula) :
    rawProofLeadingPremisePostfixLabels tree.canonicalRawProof =
      tree.labels := by
  cases tree with
  | active hypothesis hmember =>
      simp [GeneratedProvesTree.canonicalRawProof,
        rawProofLeadingPremisePostfixLabels,
        rawProofLeadingPremisePostfixLabelsFrom,
        activeHypothesisRuleInstance, GeneratedProvesTree.labels]
  | @assertion assertion actuals result substitution hmember node children =>
      have hcount :
          (assertionRuleInstance assertion actuals formula).arguments.length -
              1 =
            actuals.length := by
        simp [assertionRuleInstance, assertionRuleArguments]
      rw [GeneratedProvesTree.canonicalRawProof,
        rawProofLeadingPremisePostfixLabels,
        rawProofLeadingPremisePostfixLabelsFrom_eq_take_flatMap, hcount,
        ← children.canonicalRawProofs_length, List.take_left,
        GeneratedProvesForest.canonicalRawProofs_postfixLabels children]
      rfl

/-- Postfix recovery distributes over a canonical raw forest exactly as the
authored forest-label concatenation does. -/
theorem GeneratedProvesForest.canonicalRawProofs_postfixLabels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas) :
    forest.canonicalRawProofs.flatMap
        rawProofLeadingPremisePostfixLabels = forest.labels := by
  cases forest with
  | nil => rfl
  | cons head tail =>
      change rawProofLeadingPremisePostfixLabels head.canonicalRawProof ++
          tail.canonicalRawProofs.flatMap
            rawProofLeadingPremisePostfixLabels =
        head.labels ++ tail.labels
      rw [GeneratedProvesTree.canonicalRawProof_postfixLabels head,
        GeneratedProvesForest.canonicalRawProofs_postfixLabels tail]

end


/-- Combined exact endpoint: erasing the assembled generic derivation and
then reading its generated leading-premise convention returns precisely the
authored postfix labels. -/
theorem GeneratedProvesTree.erase_toDerivation_postfixLabels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula) :
    rawProofLeadingPremisePostfixLabels
        (tree.toDerivation hprojection).erase = tree.labels := by
  rw [tree.erase_toDerivation hprojection]
  exact tree.canonicalRawProof_postfixLabels

/-! ## Positive and negative boundaries -/

/-- Positive: every source-pinned view assembles the corresponding generic
native derivation. -/
example {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula) :
    Derivation target (proves (encodeFormula formula)) :=
  tree.toDerivation hprojection

/-- Negative: a source-pinned proof tree never emits an empty authored proof.
This does not assert the converse for arbitrary generic derivations. -/
theorem GeneratedProvesTree.labels_ne_nil
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula) :
    tree.labels ≠ [] := by
  cases tree <;> simp [GeneratedProvesTree.labels]

end Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
