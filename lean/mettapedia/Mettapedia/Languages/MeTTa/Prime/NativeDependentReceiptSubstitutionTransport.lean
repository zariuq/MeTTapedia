import Mettapedia.TypeTheory.FreeWhiskeredCellTransport
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptComputad

/-!
# Strict substitution transport for dependent Prime receipt cells

Substitution is a strict map of the one-dimensional base of retained
structural-conversion receipts: it maps terms, maps complete receipt trees,
and preserves receipt composition.  It becomes a strict map of generated
two-cells exactly when the hosted generator family supplies its own
substitution action.

This separates two capabilities that a native-calculus host must not
conflate.  Structural substitution alone preserves every raw conversion
path, but it cannot invent a target comparison generator.  With generator
naturality, the complete free cell transports and retains its authored-
generator count, constructor count, and raw construction shape.  Without
that evidence, a higher comparison or ordinary fallback remains necessary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeDependentReceiptSubstitutionTransport

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.FreeWhiskeredCell
open Mettapedia.TypeTheory.FreeWhiskeredCell.CoherenceObservation
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptComputad
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceCandidates
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.ProofRelevantStructuralComputation

universe uEvidence uSourceGenerator uTargetGenerator

/-! ## The strict one-dimensional substitution map -/

/-- Simultaneous substitution maps raw terms and their complete retained
conversion receipts, preserving receipt transitivity constructor-for-
constructor. -/
def receiptSubstitutionBaseMap
    {Head : Type} {n m : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (substitution : Sub Head n m) :
    BaseMap (receiptBase computation headEq n)
      (receiptBase computation headEq m) where
  onObject := subst substitution
  onHom := fun receipt => receipt.substitute substitution
  map_compose := by
    intros
    rfl

/-- Generator naturality is the additional capability required above raw
receipt substitution.  Its result stays in the exact parallel fibre selected
by the substituted source and target receipts. -/
abbrev ReceiptGeneratorNaturality
    {Head : Type} {n m : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (substitution : Sub Head n m)
    (SourceGenerator : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uSourceGenerator)
    (TargetGenerator : {left right : Tm Head m} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uTargetGenerator) :=
  GeneratorMap (receiptSubstitutionBaseMap substitution)
    SourceGenerator TargetGenerator

/-- A structural substitution plus generator naturality transports the full
generated receipt cell. -/
def substituteCell
    {Head : Type} {n m : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (substitution : Sub Head n m)
    {SourceGenerator : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uSourceGenerator}
    {TargetGenerator : {left right : Tm Head m} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uTargetGenerator}
    (naturality : ReceiptGeneratorNaturality substitution
      SourceGenerator TargetGenerator)
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt computation headEq left right}
    (cell : Cell (receiptBase computation headEq n)
      SourceGenerator first second) :
    Cell (receiptBase computation headEq m) TargetGenerator
      (first.substitute substitution) (second.substitute substitution) :=
  mapCell (receiptSubstitutionBaseMap substitution) naturality cell

theorem generatorCount_substituteCell
    {Head : Type} {n m : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (substitution : Sub Head n m)
    {SourceGenerator : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uSourceGenerator}
    {TargetGenerator : {left right : Tm Head m} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uTargetGenerator}
    (naturality : ReceiptGeneratorNaturality substitution
      SourceGenerator TargetGenerator)
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt computation headEq left right}
    (cell : Cell (receiptBase computation headEq n)
      SourceGenerator first second) :
    generatorCount (substituteCell substitution naturality cell) =
      generatorCount cell :=
  generatorCount_mapCell (receiptSubstitutionBaseMap substitution)
    naturality cell

theorem constructorCount_substituteCell
    {Head : Type} {n m : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (substitution : Sub Head n m)
    {SourceGenerator : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uSourceGenerator}
    {TargetGenerator : {left right : Tm Head m} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uTargetGenerator}
    (naturality : ReceiptGeneratorNaturality substitution
      SourceGenerator TargetGenerator)
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt computation headEq left right}
    (cell : Cell (receiptBase computation headEq n)
      SourceGenerator first second) :
    constructorCount (substituteCell substitution naturality cell) =
      constructorCount cell :=
  constructorCount_mapCell (receiptSubstitutionBaseMap substitution)
    naturality cell

theorem rawShape_substituteCell
    {Head : Type} {n m : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (substitution : Sub Head n m)
    {SourceGenerator : {left right : Tm Head n} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uSourceGenerator}
    {TargetGenerator : {left right : Tm Head m} →
      StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq left right →
        Type uTargetGenerator}
    (naturality : ReceiptGeneratorNaturality substitution
      SourceGenerator TargetGenerator)
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt computation headEq left right}
    (cell : Cell (receiptBase computation headEq n)
      SourceGenerator first second) :
    rawShape (substituteCell substitution naturality cell) = rawShape cell :=
  rawShape_mapCell (receiptSubstitutionBaseMap substitution) naturality cell

/-! ## A nonidentity Prime substitution and its refusing control -/

namespace Canaries

open NativeDependentReceiptCoherenceCandidates.Canaries

abbrev variableState : Tower.Tm 1 := .var 0

/-- Closing the sole variable with the universe-zero code is a genuine
nonidentity substitution from an open term fibre to a closed one. -/
def closeVariable : Sub Tower.Head 1 0 := fun _ => state

@[simp] theorem closeVariable_variableState :
    subst closeVariable variableState = state :=
  rfl

def variableOneReflexivity :
    StructuralConversionReceipt retainedTower.computation
      Tower.rules.headEq variableState variableState :=
  @ConversionEvidence.refl Unit
    (rawStructuralComputation retainedTower.computation Tower.rules.headEq 1)
    () variableState

def variableDoubledReflexivity :
    StructuralConversionReceipt retainedTower.computation
      Tower.rules.headEq variableState variableState :=
  ConversionEvidence.trans variableOneReflexivity variableOneReflexivity

@[simp] theorem substitute_variableOneReflexivity :
    variableOneReflexivity.substitute closeVariable = oneReflexivity :=
  rfl

@[simp] theorem substitute_variableDoubledReflexivity :
    variableDoubledReflexivity.substitute closeVariable =
      doubledReflexivity :=
  rfl

abbrev TaggedGenerator (n : Nat) :
    {left right : Tower.Tm n} →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right → Type :=
  fun _ _ => Nat

abbrev EmptyGenerator (n : Nat) :
    {left right : Tower.Tm n} →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right → Type :=
  fun _ _ => Empty

/-- The tag is authored provenance attached to a comparison between two
distinct open receipt histories. -/
def taggedCell :
    Cell (receiptBase retainedTower.computation Tower.rules.headEq 1)
      (TaggedGenerator 1) variableDoubledReflexivity
        variableOneReflexivity :=
  .generator 7

/-- Whiskering exercises preservation of receipt composition in addition to
the generator fibre itself. -/
def whiskeredTaggedCell :
    Cell (receiptBase retainedTower.computation Tower.rules.headEq 1)
      (TaggedGenerator 1)
      (.trans variableOneReflexivity variableDoubledReflexivity)
      (.trans variableOneReflexivity variableOneReflexivity) :=
  .whiskerLeft variableOneReflexivity taggedCell

def taggedNaturality :
    ReceiptGeneratorNaturality closeVariable
      (TaggedGenerator 1) (TaggedGenerator 0) where
  onGenerator := fun tag => tag

/-- The same comparison becomes a closed Prime cell; no post-hoc comparison
of the substituted receipts is needed. -/
def substitutedTaggedCell :
    Cell (receiptBase retainedTower.computation Tower.rules.headEq 0)
      (TaggedGenerator 0) doubledReflexivity oneReflexivity :=
  substituteCell closeVariable taggedNaturality taggedCell

@[simp] theorem substitutedTaggedCell_is_generator :
    substitutedTaggedCell =
      Cell.generator
        (base := receiptBase retainedTower.computation Tower.rules.headEq 0)
        (Generator := TaggedGenerator 0) (7 : Nat) :=
  rfl

def substitutedWhiskeredTaggedCell :=
  substituteCell closeVariable taggedNaturality whiskeredTaggedCell

/-- Strict substitution retains the complete raw cell shape, including the
whisker recording where the authored comparison occurred. -/
theorem substitutedWhiskeredTaggedCell_retains_shape :
    rawShape substitutedWhiskeredTaggedCell =
      rawShape whiskeredTaggedCell :=
  rawShape_substituteCell closeVariable taggedNaturality whiskeredTaggedCell

theorem substitutedWhiskeredTaggedCell_retains_counts :
    generatorCount substitutedWhiskeredTaggedCell =
        generatorCount whiskeredTaggedCell ∧
      constructorCount substitutedWhiskeredTaggedCell =
        constructorCount whiskeredTaggedCell :=
  ⟨generatorCount_substituteCell closeVariable taggedNaturality
      whiskeredTaggedCell,
    constructorCount_substituteCell closeVariable taggedNaturality
      whiskeredTaggedCell⟩

/-- The same raw substitution cannot manufacture a target generator when the
target parallel fibre is empty.  This is the native-capability boundary that
a host must inspect before selecting strict transport. -/
theorem no_empty_generator_naturality :
    IsEmpty
      (ReceiptGeneratorNaturality closeVariable
        (TaggedGenerator 1) (EmptyGenerator 0)) :=
  ⟨fun naturality =>
    Empty.elim
      (naturality.onGenerator
        (first := variableDoubledReflexivity)
        (second := variableOneReflexivity) (7 : Nat))⟩

/-- The positive and negative controls jointly characterize the scoped
result: strict Prime substitution preserves complete generated structure
when generator naturality is supplied, while raw substitution alone does not
entitle that realization. -/
theorem strictSubstitutionTransportBoundary :
    rawShape substitutedWhiskeredTaggedCell =
        rawShape whiskeredTaggedCell ∧
      generatorCount substitutedWhiskeredTaggedCell =
        generatorCount whiskeredTaggedCell ∧
      constructorCount substitutedWhiskeredTaggedCell =
        constructorCount whiskeredTaggedCell ∧
      IsEmpty
        (ReceiptGeneratorNaturality closeVariable
          (TaggedGenerator 1) (EmptyGenerator 0)) :=
  ⟨substitutedWhiskeredTaggedCell_retains_shape,
    substitutedWhiskeredTaggedCell_retains_counts.1,
    substitutedWhiskeredTaggedCell_retains_counts.2,
    no_empty_generator_naturality⟩

end Canaries

/-! ## Axiom audit -/

#print axioms receiptSubstitutionBaseMap
#print axioms substituteCell
#print axioms generatorCount_substituteCell
#print axioms constructorCount_substituteCell
#print axioms rawShape_substituteCell
#print axioms Canaries.substitutedWhiskeredTaggedCell_retains_shape
#print axioms Canaries.no_empty_generator_naturality
#print axioms Canaries.strictSubstitutionTransportBoundary

end NativeDependentReceiptSubstitutionTransport
end Mettapedia.Languages.MeTTa.Prime
