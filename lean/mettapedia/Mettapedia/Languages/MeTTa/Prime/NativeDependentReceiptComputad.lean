import Mettapedia.GSLT.Core.GeneratedTwoCellUniversal
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceCandidates

/-!
# Dependent conversion receipts as a raw two-computad boundary

The generated comparison cells for dependent Prime conversion receipts are
an exact instance of the representation-independent free-whiskered-cell
syntax.  Raw structural conversion receipts provide the one-cells,
reflexivity and transitivity provide their identity/composition operations,
and authored dependent boundaries provide parallel two-generators.

This identifies the common theorem beneath operational GSLT cells and Prime
conversion-receipt cells without selecting a strict, bicategorical, or
homotopical completion.  Every target interpretation of the five raw cell
constructors extends uniquely.  Unit, associativity, interchange,
substitution, observation, and all higher coherences remain explicit
additional obligations of a later completion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeDependentReceiptComputad

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.FreeWhiskeredCell
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceCandidates
open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentNaturality
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.ProofRelevantStructuralComputation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.SyntacticContextual
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.SyntacticJudgmentalPi

universe uEvidence uTarget

/-- Structural conversion receipts supply the raw retained one-cells.  Their
constructor-level reflexivity and transitivity are not quotiented by category
laws here. -/
@[reducible] def receiptBase
    {Head : Type}
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) (n : Nat) : Base where
  Object := Tm Head n
  Hom := StructuralConversionReceipt computation headEq
  compose := fun first second => ConversionEvidence.trans first second

variable {Head : Type} {n : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {Generator : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uEvidence}

/-- The earlier receipt-specific syntax embeds constructor-for-constructor in
the common raw-cell language. -/
def toCommon :
    {left right : Tm Head n} →
      {first second : StructuralConversionReceipt computation headEq
        left right} →
      GeneratedStructuralReceiptCell Generator first second →
        Cell (receiptBase computation headEq n) Generator first second
  | _, _, _, _, .refl receipt =>
      Cell.refl (base := receiptBase computation headEq n)
        (Generator := Generator) receipt
  | _, _, _, _, .generator evidence =>
      Cell.generator (base := receiptBase computation headEq n) evidence
  | _, _, _, _, .vertical earlier later =>
      Cell.vertical (toCommon earlier) (toCommon later)
  | _, _, _, _, .whiskerLeft prior cell =>
      Cell.whiskerLeft (base := receiptBase computation headEq n)
        prior (toCommon cell)
  | _, _, _, _, .whiskerRight suffix cell =>
      Cell.whiskerRight (base := receiptBase computation headEq n)
        suffix (toCommon cell)

/-- The common syntax reconstructs the receipt-specific tree exactly. -/
def fromCommon :
    {left right : Tm Head n} →
      {first second : StructuralConversionReceipt computation headEq
        left right} →
      Cell (receiptBase computation headEq n) Generator first second →
        GeneratedStructuralReceiptCell Generator first second
  | _, _, _, _, .refl receipt =>
      GeneratedStructuralReceiptCell.refl receipt
  | _, _, _, _, .generator evidence =>
      GeneratedStructuralReceiptCell.generator evidence
  | _, _, _, _, .vertical earlier later =>
      GeneratedStructuralReceiptCell.vertical
        (fromCommon earlier) (fromCommon later)
  | _, _, _, _, .whiskerLeft prior cell =>
      GeneratedStructuralReceiptCell.whiskerLeft prior (fromCommon cell)
  | _, _, _, _, .whiskerRight suffix cell =>
      GeneratedStructuralReceiptCell.whiskerRight suffix (fromCommon cell)

@[simp] theorem fromCommon_toCommon
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt computation headEq left right}
    (cell : GeneratedStructuralReceiptCell Generator first second) :
    fromCommon (toCommon cell) = cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      simp [toCommon, fromCommon, earlierIH, laterIH]
  | whiskerLeft prior cell cellIH =>
      simp [toCommon, fromCommon, cellIH]
  | whiskerRight suffix cell cellIH =>
      simp [toCommon, fromCommon, cellIH]

def identityAlgebra :
    Algebra (receiptBase computation headEq n) Generator
      (Cell (receiptBase computation headEq n) Generator) :=
  generatedAlgebra (fun evidence => evidence)

def commonRoundTripExtension : Extension
    (identityAlgebra (computation := computation) (headEq := headEq)
      (Generator := Generator)) where
  onCell := fun cell => toCommon (fromCommon cell)
  onRefl := by intros; rfl
  onGenerator := by intros; rfl
  onVertical := by intros; rfl
  onWhiskerLeft := by intros; rfl
  onWhiskerRight := by intros; rfl

def commonIdentityExtension : Extension
    (identityAlgebra (computation := computation) (headEq := headEq)
      (Generator := Generator)) where
  onCell := fun cell => cell
  onRefl := by intros; rfl
  onGenerator := by intros; rfl
  onVertical := by intros; rfl
  onWhiskerLeft := by intros; rfl
  onWhiskerRight := by intros; rfl

@[simp] theorem toCommon_fromCommon
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt computation headEq left right}
    (cell : Cell (receiptBase computation headEq n) Generator first second) :
    toCommon (fromCommon cell) = cell := by
  have extensionsEqual :
      commonRoundTripExtension (computation := computation)
          (headEq := headEq) (Generator := Generator) =
        commonIdentityExtension (computation := computation)
          (headEq := headEq) (Generator := Generator) :=
    Subsingleton.elim _ _
  have valuesEqual := congrArg
    (fun extension => extension.onCell cell) extensionsEqual
  exact valuesEqual

/-- The candidate receipt cells and the common raw two-computad syntax are
equivalent with their entire constructor histories intact. -/
def equivalence
    {left right : Tm Head n}
    (first second : StructuralConversionReceipt computation headEq left right) :
    GeneratedStructuralReceiptCell Generator first second ≃
      Cell (receiptBase computation headEq n) Generator first second where
  toFun := toCommon
  invFun := fromCommon
  left_inv := fromCommon_toCommon
  right_inv := toCommon_fromCommon

/-- Every proposed semantic completion receives one unique structural map
from the retained receipt computad once it interprets the five constructors. -/
theorem commonExtensions_contractible
    {Target : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uTarget}
    (algebra : Algebra (receiptBase computation headEq n) Generator Target) :
    Nonempty (Extension algebra) ∧ Subsingleton (Extension algebra) :=
  Extension.contractible algebra

/-! ## Concrete dependent-receipt controls -/

namespace Canaries

open NativeDependentReceiptCoherenceCandidates.Canaries

/-- The administrative comparison remains exactly one authored generator in
the common syntax; it is not converted into receipt equality. -/
theorem administrativeCell_toCommon :
    toCommon administrativeCell =
      Cell.generator
        (base := receiptBase retainedTower.computation Tower.rules.headEq 0)
        AdministrativeGenerator.contractUnits :=
  rfl

/-- Common-cell presentation preserves both the comparison and the fact that
its parallel one-cell histories are distinct. -/
theorem administrative_common_noncollapse :
    doubledReflexivity ≠ oneReflexivity ∧
      Nonempty
        (Cell
          (receiptBase retainedTower.computation Tower.rules.headEq 0)
          AdministrativeGenerator doubledReflexivity oneReflexivity) :=
  ⟨oneReflexivity_ne_doubledReflexivity.symm,
    ⟨toCommon administrativeCell⟩⟩

end Canaries

/-! ## The dependent second-Sigma boundary in the common language -/

/-- The existing second-Sigma naturality boundary is a genuine attached
two-generator in the common raw computad.  This is a shared input to any later
strict, weak, or higher completion. -/
def sigmaSecondCommonCell
    {rules : Rules Head} {retained : RetainedRoot rules}
    {context : FormedContext rules}
    {leftCandidate rightCandidate : RawDependentStep context}
    {left : NativeGradualDependentNaturality.DependentStepEvidence
      retained context leftCandidate}
    {right : NativeGradualDependentNaturality.DependentStepEvidence
      retained context rightCandidate}
    (boundary : NativeGradualDependentNaturality.DependentStepNaturalityBoundary
      left right) :
    Cell
      (receiptBase retained.computation rules.headEq context.arity)
      (SigmaSecondBoundaryGenerator boundary)
      (alignedTypeReceiptBoundary boundary).first
      (alignedTypeReceiptBoundary boundary).second :=
  toCommon (sigmaSecondGeneratedCellCandidate boundary)

@[simp] theorem sigmaSecondCommonCell_is_generator
    {rules : Rules Head} {retained : RetainedRoot rules}
    {context : FormedContext rules}
    {leftCandidate rightCandidate : RawDependentStep context}
    {left : NativeGradualDependentNaturality.DependentStepEvidence
      retained context leftCandidate}
    {right : NativeGradualDependentNaturality.DependentStepEvidence
      retained context rightCandidate}
    (boundary : NativeGradualDependentNaturality.DependentStepNaturalityBoundary
      left right) :
    sigmaSecondCommonCell boundary =
      Cell.generator
        (base := receiptBase retained.computation rules.headEq context.arity)
        SigmaSecondBoundaryGenerator.substitutionExpansion :=
  rfl

/-! ## Axiom audit -/

#print axioms fromCommon_toCommon
#print axioms toCommon_fromCommon
#print axioms equivalence
#print axioms commonExtensions_contractible
#print axioms Canaries.administrativeCell_toCommon
#print axioms Canaries.administrative_common_noncollapse
#print axioms sigmaSecondCommonCell_is_generator

end NativeDependentReceiptComputad
end Mettapedia.Languages.MeTTa.Prime
