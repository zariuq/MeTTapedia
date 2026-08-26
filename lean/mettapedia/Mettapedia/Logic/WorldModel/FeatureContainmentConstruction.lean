import Mettapedia.Logic.WorldModel.FeatureContainment
import Mettapedia.Logic.WorldModel.ContainmentEncoding

/-!
# Executable feature-containment construction

This file isolates the operational content of a repaired feature-containment
construction.  A reconstruction program may require an exact complexity index
as auxiliary input.  The residual therefore transports three fields—the
index, the reconstruction program, and the original residual—rather than
silently assuming that the index can be recovered from the base feature.

The construction is deliberately stated for an arbitrary conditional
algorithm.  It proves exact execution and an explicit additive-slack transfer.
Embedding the wrapper in a particular universal prefix machine, and deriving
the quantitative description-transfer premise from prefix-complexity chain
rules, are separate obligations.
-/

namespace Mettapedia.Logic.WorldModel.FeatureContainmentConstruction

open KolmogorovComplexity
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.FeatureContainment
open Mettapedia.Logic.WorldModel.ContainmentEncoding

/-- A feature implication whose premise and consequent execute in different
conditional algorithms.  This is useful for proving a wrapper correct before
compiling it into a chosen universal reference algorithm. -/
def CrossAlgorithmFeatureImplicationWithBudget
    (premiseAlgorithm consequentAlgorithm : ConditionalAlgorithm)
    (budget : BinString → Nat) (premise consequent : BinString) : Prop :=
  ∀ certificate source,
    (strictFeatureSemantics premiseAlgorithm).realizes premise certificate source →
    SlackFeatureOf consequentAlgorithm (budget source) consequent source

/-- The fixed head carried by the corrected residual. -/
def containmentHeader
    (complexityIndex : Nat) (reconstructionProgram : BinString) : BinString :=
  e2pair (binaryBits complexityIndex) reconstructionProgram

/-- The outer self-delimiting cost paid when `containmentHeader` is placed in
front of the original residual. -/
def containmentOuterOverhead
    (complexityIndex : Nat) (reconstructionProgram : BinString) : Nat :=
  2 * (binaryBits
    (containmentHeader complexityIndex reconstructionProgram).length).length + 1

/-- The tag and inner self-delimiting costs separating a base feature and a
reconstruction program. -/
def containmentInnerOverhead (complexityIndex : Nat) : Nat :=
  (binaryBits complexityIndex).length +
    2 * (binaryBits (binaryBits complexityIndex).length).length + 2

/-- A generator in the wrapper namespace.  The leading tag separates it from
descriptive programs. -/
def containmentGenerator (baseFeature : BinString) : BinString :=
  false :: baseFeature

/-- A descriptive program in the wrapper namespace.  It carries the same
index and reconstruction program as the corrected residual, followed by the
old descriptive program. -/
def containmentDescriptor
    (complexityIndex : Nat) (reconstructionProgram descriptiveProgram : BinString) :
    BinString :=
  true :: e2triple (binaryBits complexityIndex) reconstructionProgram
    descriptiveProgram

/-- Execute corrected feature containment over `U`.

* A generator decodes `(index, reconstructionProgram, residual)`, reconstructs
  the premise feature from `(baseFeature,index)`, then runs that premise on the
  residual.
* A descriptive program extracts the old residual from the source and packages
  it with the exact index and reconstruction program.
-/
def containmentWrapperAlgorithm (U : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun program condition =>
    match program with
    | false :: baseFeature =>
        match decodeIndexedResidual condition with
        | none => Part.none
        | some (complexityIndex, reconstructionProgram, residual) =>
            (U reconstructionProgram
              (pairCondition baseFeature (binaryBits complexityIndex))).bind
                fun premiseFeature => U premiseFeature residual
    | true :: payload =>
        match e2decodeTriple payload with
        | none => Part.none
        | some (complexityBits, reconstructionProgram, descriptiveProgram) =>
            (U descriptiveProgram condition).bind fun residual =>
              Part.some (indexedResidual (ofBinaryBits complexityBits)
                reconstructionProgram residual)
    | [] => Part.none

theorem containmentGenerator_length (baseFeature : BinString) :
    (containmentGenerator baseFeature).length = baseFeature.length + 1 := by
  simp [containmentGenerator]

theorem containmentDescriptor_extracts
    {U : ConditionalAlgorithm}
    {complexityIndex : Nat} {reconstructionProgram descriptiveProgram residual source :
      BinString}
    (extracts : residual ∈ U descriptiveProgram source) :
    indexedResidual complexityIndex reconstructionProgram residual ∈
      containmentWrapperAlgorithm U
        (containmentDescriptor complexityIndex reconstructionProgram
          descriptiveProgram) source := by
  unfold containmentDescriptor containmentWrapperAlgorithm
  simp only [e2decodeTriple_e2triple, ofBinaryBits_binaryBits]
  exact Part.mem_bind extracts (Part.mem_some _)

theorem containmentGenerator_reconstructs
    {U : ConditionalAlgorithm}
    {complexityIndex : Nat}
    {baseFeature reconstructionProgram premiseFeature residual source : BinString}
    (reconstructsPremise :
      premiseFeature ∈ U reconstructionProgram
        (pairCondition baseFeature (binaryBits complexityIndex)))
    (reconstructsSource : source ∈ U premiseFeature residual) :
    source ∈
      containmentWrapperAlgorithm U (containmentGenerator baseFeature)
        (indexedResidual complexityIndex reconstructionProgram residual) := by
  unfold containmentGenerator containmentWrapperAlgorithm
  simp only [decodeIndexedResidual_indexedResidual]
  exact Part.mem_bind reconstructsPremise reconstructsSource

/-- A core description bound on the base feature plus reconstruction program
implies the exact description-transfer inequality used by the wrapper theorem.
All coding costs are displayed rather than hidden in asymptotic notation. -/
theorem descriptionTransfer_of_coreDescriptionBound
    {complexityIndex coreSlack : Nat}
    {baseFeature reconstructionProgram premiseFeature : BinString}
    (coreBound :
      baseFeature.length + reconstructionProgram.length ≤
        premiseFeature.length + coreSlack) :
    (containmentGenerator baseFeature).length +
        (containmentHeader complexityIndex reconstructionProgram).length ≤
      premiseFeature.length +
        (coreSlack + containmentInnerOverhead complexityIndex) := by
  rw [containmentGenerator_length]
  unfold containmentHeader containmentInnerOverhead
  rw [e2pair_length]
  omega

/-- Corrected operational containment theorem.

The `descriptionTransfer` inequality is the exact finite obligation hidden by
asymptotic notation in a complexity-level proof: the new generator together
with the transported `(index,reconstructionProgram)` header must not exceed the
old premise description by more than `transferSlack`.  Only the *outer*
self-delimiting header is then added to the conclusion's slack.
-/
theorem containmentWrapper_implication_of_descriptionTransfer
    {U : ConditionalAlgorithm}
    {complexityIndex transferSlack : Nat}
    {baseFeature reconstructionProgram premiseFeature : BinString}
    (reconstructsPremise :
      premiseFeature ∈ U reconstructionProgram
        (pairCondition baseFeature (binaryBits complexityIndex)))
    (descriptionTransfer :
      (containmentGenerator baseFeature).length +
          (containmentHeader complexityIndex reconstructionProgram).length ≤
        premiseFeature.length + transferSlack) :
    CrossAlgorithmFeatureImplicationWithBudget U (containmentWrapperAlgorithm U)
      (fun _ => transferSlack +
        containmentOuterOverhead complexityIndex reconstructionProgram)
      premiseFeature (containmentGenerator baseFeature) := by
  intro certificate source realizesPremise
  rcases realizesPremise with ⟨extracts, reconstructs, compresses⟩
  refine ⟨
    { descriptiveProgram := containmentDescriptor complexityIndex
        reconstructionProgram certificate.descriptiveProgram,
      residual := indexedResidual complexityIndex reconstructionProgram
        certificate.residual }, ?_⟩
  refine ⟨containmentDescriptor_extracts extracts,
    containmentGenerator_reconstructs reconstructsPremise reconstructs, ?_⟩
  change (containmentGenerator baseFeature).length +
      (indexedResidual complexityIndex reconstructionProgram
        certificate.residual).length <
    source.length +
      (transferSlack +
        containmentOuterOverhead complexityIndex reconstructionProgram)
  rw [indexedResidual_length]
  change (containmentGenerator baseFeature).length +
      ((e2pair (binaryBits complexityIndex) reconstructionProgram).length +
        2 * (binaryBits
          (e2pair (binaryBits complexityIndex) reconstructionProgram).length).length +
        1 + certificate.residual.length) <
    source.length +
      (transferSlack +
        (2 * (binaryBits
          (e2pair (binaryBits complexityIndex) reconstructionProgram).length).length +
        1))
  unfold containmentHeader at descriptionTransfer
  omega

/-- Source-shaped form of the corrected construction.  The AIT ledger only
needs to establish a bound for `baseFeature ++ reconstructionProgram`; the
self-delimiting costs are then added by proved coding equations. -/
theorem containmentWrapper_implication_of_coreDescriptionBound
    {U : ConditionalAlgorithm}
    {complexityIndex coreSlack : Nat}
    {baseFeature reconstructionProgram premiseFeature : BinString}
    (reconstructsPremise :
      premiseFeature ∈ U reconstructionProgram
        (pairCondition baseFeature (binaryBits complexityIndex)))
    (coreBound :
      baseFeature.length + reconstructionProgram.length ≤
        premiseFeature.length + coreSlack) :
    CrossAlgorithmFeatureImplicationWithBudget U (containmentWrapperAlgorithm U)
      (fun _ => coreSlack + containmentInnerOverhead complexityIndex +
        containmentOuterOverhead complexityIndex reconstructionProgram)
      premiseFeature (containmentGenerator baseFeature) := by
  have h := containmentWrapper_implication_of_descriptionTransfer
    reconstructsPremise
    (descriptionTransfer_of_coreDescriptionBound coreBound)
  simpa [Nat.add_assoc] using h

/-- Nonvacuous version of the corrected construction, retaining a witness that
the premise is a genuine strict feature. -/
theorem witnessed_containmentWrapper_implication_of_descriptionTransfer
    {U : ConditionalAlgorithm}
    {complexityIndex transferSlack : Nat}
    {baseFeature reconstructionProgram premiseFeature witness : BinString}
    (witnessed : StrictFeatureOf U premiseFeature witness)
    (reconstructsPremise :
      premiseFeature ∈ U reconstructionProgram
        (pairCondition baseFeature (binaryBits complexityIndex)))
    (descriptionTransfer :
      (containmentGenerator baseFeature).length +
          (containmentHeader complexityIndex reconstructionProgram).length ≤
        premiseFeature.length + transferSlack) :
    StrictFeatureOf U premiseFeature witness ∧
      CrossAlgorithmFeatureImplicationWithBudget U (containmentWrapperAlgorithm U)
        (fun _ => transferSlack +
          containmentOuterOverhead complexityIndex reconstructionProgram)
        premiseFeature (containmentGenerator baseFeature) := by
  exact ⟨witnessed,
    containmentWrapper_implication_of_descriptionTransfer reconstructsPremise
      descriptionTransfer⟩

/-! ## Executable positive control -/

/-- A finite source algorithm with a strict feature and a separate program
that reconstructs the premise feature from a base feature plus exact index. -/
def containmentCanaryAlgorithm : ConditionalAlgorithm :=
  fun program condition =>
    if program = [false] ∧ condition = [] then Part.some fourTrue
    else if program = [true] ∧ condition = fourTrue then Part.some []
    else if program = [false, false] ∧
        condition = pairCondition [true] (binaryBits 0) then Part.some [false]
    else Part.none

theorem containmentCanary_strictFeature :
    StrictFeatureOf containmentCanaryAlgorithm [false] fourTrue := by
  refine ⟨{ descriptiveProgram := [true], residual := [] }, ?_⟩
  exact ⟨by simp [containmentCanaryAlgorithm, fourTrue],
    by simp [containmentCanaryAlgorithm, fourTrue], by simp [fourTrue]⟩

theorem containmentCanary_reconstructsPremise :
    [false] ∈ containmentCanaryAlgorithm [false, false]
      (pairCondition [true] (binaryBits 0)) := by
  simp [containmentCanaryAlgorithm]

theorem containmentCanary_correctedConstruction :
    StrictFeatureOf containmentCanaryAlgorithm [false] fourTrue ∧
      CrossAlgorithmFeatureImplicationWithBudget containmentCanaryAlgorithm
        (containmentWrapperAlgorithm containmentCanaryAlgorithm)
        (fun _ => 2 + containmentInnerOverhead 0 +
          containmentOuterOverhead 0 [false, false])
        [false] (containmentGenerator [true]) := by
  refine ⟨containmentCanary_strictFeature, ?_⟩
  apply containmentWrapper_implication_of_coreDescriptionBound
    containmentCanary_reconstructsPremise
  decide

/-! The negative representation control is
`ContainmentEncoding.unindexedResidual_not_injective`: deleting the index makes
the payload non-injective as an encoding of triples. -/

#print axioms containmentWrapper_implication_of_descriptionTransfer
#print axioms containmentWrapper_implication_of_coreDescriptionBound
#print axioms witnessed_containmentWrapper_implication_of_descriptionTransfer
#print axioms containmentCanary_correctedConstruction
#print axioms unindexedResidual_not_injective

end Mettapedia.Logic.WorldModel.FeatureContainmentConstruction
