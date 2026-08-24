import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentNaturality

/-!
# Higher-coherence candidates for dependent conversion receipts

Dependent second-Sigma beta supplies two proof-relevant type-conversion
receipts around one commuting substitution boundary.  Endpoint equality is
too weak to retain either receipt, while literal equality of receipt trees is
too strong to assume: substitution may expand one variable into compound
syntax and thereby reshape a pointwise conversion derivation.

This module compares those choices before a bicategorical interface is
selected.  It proves that:

* an endpoint-only shadow cannot reconstruct even the constructor count of a
  conversion receipt;
* same-endpoint receipts need not be equal;
* a free generated-cell syntax can relate unequal receipts without collapsing
  them, but does not yet satisfy unit coherence definitionally;
* every dependent-step naturality boundary determines two aligned conversion
  receipts with exactly common endpoints.

The final section packages a proposed generator for that aligned pair.  This
is candidate two-dimensional syntax, not a semantic adequacy theorem and not
the selected Prime bicategory.  Selection still requires reviewed unit,
associativity, interchange, substitution, and observation laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceCandidates

open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentNaturality
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.ProofRelevantStructuralComputation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticContextual
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalPi
open Mettapedia.TypeTheory.JudgmentalEquality

universe uEvidence

variable {Head : Type} {n : Nat}

/-! ## Receipt observations and the endpoint-only obstruction -/

/-- Constructor count is one deliberately simple proof-tree observation.  It
counts administrative reflexivity, symmetry, and transitivity nodes as well as
computational steps, so it detects information erased by endpoint support. -/
def receiptNodeCount
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n} :
    StructuralConversionReceipt computation headEq left right → Nat
  | .step _ => 1
  | .refl _ => 1
  | .symm receipt => receiptNodeCount receipt + 1
  | .trans first second =>
      receiptNodeCount first + receiptNodeCount second + 1

/-- Two conversion receipts with exactly the same raw endpoints.  No equality
or comparison between the receipts is included. -/
structure StructuralReceiptBoundary
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) (left right : Tm Head n) where
  first : StructuralConversionReceipt computation headEq left right
  second : StructuralConversionReceipt computation headEq left right

def StructuralReceiptBoundary.Strict
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n}
    (boundary : StructuralReceiptBoundary computation headEq left right) : Prop :=
  boundary.first = boundary.second

/-! ## A raw free-cell candidate over complete receipt trees -/

/-- Free two-dimensional syntax generated directly over retained conversion
trees.  Whiskering uses conversion composition and therefore preserves every
prefix, suffix, intermediate term, and nested receipt.

No bicategorical quotient is imposed.  In particular, unit and associativity
coherences remain data that a selected completion must add. -/
inductive GeneratedStructuralReceiptCell
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (Generator : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uEvidence) :
    {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type (uEvidence + 1) where
  | refl {left right} (receipt :
      StructuralConversionReceipt computation headEq left right) :
      GeneratedStructuralReceiptCell Generator receipt receipt
  | generator {left right} {first second :
      StructuralConversionReceipt computation headEq left right} :
      Generator first second →
      GeneratedStructuralReceiptCell Generator first second
  | vertical {left right} {first middle last :
      StructuralConversionReceipt computation headEq left right} :
      GeneratedStructuralReceiptCell Generator first middle →
      GeneratedStructuralReceiptCell Generator middle last →
      GeneratedStructuralReceiptCell Generator first last
  | whiskerLeft {left middle right}
      (prior : StructuralConversionReceipt computation headEq left middle)
      {first second :
        StructuralConversionReceipt computation headEq middle right} :
      GeneratedStructuralReceiptCell Generator first second →
      GeneratedStructuralReceiptCell Generator
        (.trans prior first) (.trans prior second)
  | whiskerRight {left middle right}
      {first second :
        StructuralConversionReceipt computation headEq left middle}
      (suffix : StructuralConversionReceipt computation headEq middle right) :
      GeneratedStructuralReceiptCell Generator first second →
      GeneratedStructuralReceiptCell Generator
        (.trans first suffix) (.trans second suffix)

/-! ## Non-collapse canaries for the three candidate shapes -/

namespace Canaries

open SyntacticContextual.TowerExamples

abbrev retainedTower : RetainedRoot Tower.rules :=
  SyntacticJudgmentalPi.TowerExamples.retainedTower

abbrev state : Tower.Tm 0 := universeZero.code

def oneReflexivity :
    StructuralConversionReceipt retainedTower.computation
      Tower.rules.headEq state state :=
  @ConversionEvidence.refl Unit
    (rawStructuralComputation retainedTower.computation Tower.rules.headEq 0)
    () state

def doubledReflexivity :
    StructuralConversionReceipt retainedTower.computation
      Tower.rules.headEq state state :=
  ConversionEvidence.trans oneReflexivity oneReflexivity

@[simp] theorem oneReflexivity_nodeCount :
    receiptNodeCount oneReflexivity = 1 :=
  rfl

@[simp] theorem doubledReflexivity_nodeCount :
    receiptNodeCount doubledReflexivity = 3 :=
  rfl

/-- Strict receipt equality cannot be the universal coherence notion: two
legal same-endpoint receipts retain different construction histories. -/
theorem oneReflexivity_ne_doubledReflexivity :
    oneReflexivity ≠ doubledReflexivity := by
  intro equality
  cases equality

def administrativeBoundary :
    StructuralReceiptBoundary retainedTower.computation Tower.rules.headEq
      state state :=
  { first := oneReflexivity
    second := doubledReflexivity }

theorem administrativeBoundary_not_strict :
    ¬ administrativeBoundary.Strict :=
  oneReflexivity_ne_doubledReflexivity

/-- No readout from the endpoint-only key can recover receipt-node count for
all receipts.  Both canaries have the sole endpoint key but require different
answers. -/
theorem no_endpoint_only_nodeCount_decoder :
    ¬ ∃ decode : PUnit → Nat,
      ∀ receipt : StructuralConversionReceipt retainedTower.computation
          Tower.rules.headEq state state,
        decode PUnit.unit = receiptNodeCount receipt := by
  rintro ⟨decode, complete⟩
  have first := complete oneReflexivity
  have second := complete doubledReflexivity
  simp only [oneReflexivity_nodeCount] at first
  simp only [doubledReflexivity_nodeCount] at second
  omega

/-- One authored generator may compare the two administrative presentations
without asserting their equality. -/
inductive AdministrativeGenerator :
    {left right : Tower.Tm 0} →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right → Type where
  | contractUnits :
      AdministrativeGenerator doubledReflexivity oneReflexivity

def administrativeCell :
    GeneratedStructuralReceiptCell AdministrativeGenerator
      doubledReflexivity oneReflexivity :=
  .generator .contractUnits

/-- Generated cells are genuinely weaker than receipt equality. -/
theorem generatedCell_does_not_imply_receipt_equality :
    ¬ ∀ {left right : Tower.Tm 0}
        {first second : StructuralConversionReceipt retainedTower.computation
          Tower.rules.headEq left right},
      GeneratedStructuralReceiptCell AdministrativeGenerator first second →
        first = second := by
  intro collapse
  exact oneReflexivity_ne_doubledReflexivity
    (collapse administrativeCell).symm

/-- The free syntax has not silently earned the left-unit law.  This is the
precise coherence obligation that separates a raw candidate from a selected
bicategory. -/
theorem generatedCell_not_yet_left_unital :
    GeneratedStructuralReceiptCell.vertical
        (GeneratedStructuralReceiptCell.refl doubledReflexivity)
        administrativeCell ≠
      administrativeCell := by
  intro equality
  cases equality

/-- The three candidate shapes are separated by one theorem-sized audit:
endpoint-only observation loses receipt structure, strict equality refuses a
valid generated comparison, and the free comparison syntax has not yet earned
bicategorical unit coherence. -/
theorem coherenceCandidateComparison :
    (¬ ∃ decode : PUnit → Nat,
      ∀ receipt : StructuralConversionReceipt retainedTower.computation
          Tower.rules.headEq state state,
        decode PUnit.unit = receiptNodeCount receipt) ∧
    (¬ administrativeBoundary.Strict) ∧
    Nonempty (GeneratedStructuralReceiptCell AdministrativeGenerator
      doubledReflexivity oneReflexivity) ∧
    GeneratedStructuralReceiptCell.vertical
        (GeneratedStructuralReceiptCell.refl doubledReflexivity)
        administrativeCell ≠
      administrativeCell :=
  ⟨no_endpoint_only_nodeCount_decoder,
    administrativeBoundary_not_strict,
    ⟨administrativeCell⟩,
    generatedCell_not_yet_left_unital⟩

end Canaries

/-! ## The exact dependent-Sigma comparison boundary -/

/-- A dependent-step naturality boundary aligns its right-hand type receipt
to the left raw candidate.  The result has literally common endpoints while
retaining both derivation trees. -/
def alignedTypeReceiptBoundary
    {rules : Rules Head} {retained : RetainedRoot rules}
    {context : FormedContext rules}
    {leftCandidate rightCandidate : RawDependentStep context}
    {left : DependentStepEvidence retained context leftCandidate}
    {right : DependentStepEvidence retained context rightCandidate}
    (boundary : DependentStepNaturalityBoundary left right) :
    StructuralReceiptBoundary retained.computation rules.headEq
      leftCandidate.sourceType leftCandidate.targetType where
  first := left.typeReceipt
  second := by
    cases boundary.raw_commutes
    exact right.typeReceipt

/-- Proposed generator syntax for the missing dependent type-receipt cell.
The constructor retains the complete proved raw/term naturality boundary.  It
does not assert that a semantic model has already interpreted this generator. -/
inductive SigmaSecondBoundaryGenerator
    {rules : Rules Head} {retained : RetainedRoot rules}
    {context : FormedContext rules}
    {leftCandidate rightCandidate : RawDependentStep context}
    {left : DependentStepEvidence retained context leftCandidate}
    {right : DependentStepEvidence retained context rightCandidate}
    (boundary : DependentStepNaturalityBoundary left right) :
    {source target : Tm Head context.arity} →
      StructuralConversionReceipt retained.computation rules.headEq
        source target →
      StructuralConversionReceipt retained.computation rules.headEq
        source target → Type where
  | substitutionExpansion :
      SigmaSecondBoundaryGenerator boundary
        (alignedTypeReceiptBoundary boundary).first
        (alignedTypeReceiptBoundary boundary).second

/-- The free-cell candidate can express exactly the currently missing Sigma
comparison without identifying its receipts.  Adequacy and coherence of this
generator remain the review-gated design question. -/
def sigmaSecondGeneratedCellCandidate
    {rules : Rules Head} {retained : RetainedRoot rules}
    {context : FormedContext rules}
    {leftCandidate rightCandidate : RawDependentStep context}
    {left : DependentStepEvidence retained context leftCandidate}
    {right : DependentStepEvidence retained context rightCandidate}
    (boundary : DependentStepNaturalityBoundary left right) :
    GeneratedStructuralReceiptCell (SigmaSecondBoundaryGenerator boundary)
      (alignedTypeReceiptBoundary boundary).first
      (alignedTypeReceiptBoundary boundary).second :=
  .generator .substitutionExpansion

/-! ## Axiom audit -/

#print axioms Canaries.oneReflexivity_ne_doubledReflexivity
#print axioms Canaries.no_endpoint_only_nodeCount_decoder
#print axioms Canaries.generatedCell_does_not_imply_receipt_equality
#print axioms Canaries.generatedCell_not_yet_left_unital
#print axioms Canaries.coherenceCandidateComparison
#print axioms alignedTypeReceiptBoundary
#print axioms sigmaSecondGeneratedCellCandidate

end Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceCandidates
