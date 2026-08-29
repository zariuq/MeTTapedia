import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.TypeTheory.FreeWhiskeredCellCoherenceObservation
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptComputad

/-!
# Observation-relative coherence for dependent Prime receipts

Prime's dependent conversion receipts form a raw two-computad.  A later
bicategorical or higher completion may identify administrative cell trees,
but no such identification is sound independently of what a consumer asks to
observe.

This module proves that boundary on the concrete administrative comparison
already used by the dependent second-Sigma analysis.  Counting only authored
comparison generators identifies a left vertical unit and safely serves the
corresponding one-policy request.  Counting the complete raw constructor tree
distinguishes the same cells.  Consequently every readout that identifies the
unit pair is refused for the combined history-sensitive policy family, while
the retained cell itself supports both policies.

The raw computad therefore remains the common semantic carrier.  Strict,
weak, or higher coherence may be exposed as a capability-specific readout; it
is not imposed as one global quotient.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeDependentReceiptCoherenceObservation

open Mettapedia.GSLT.Core
open Mettapedia.TypeTheory.FreeWhiskeredCell
open Mettapedia.TypeTheory.FreeWhiskeredCell.CoherenceObservation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.SyntacticContextual
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.SyntacticContextual.TowerExamples
open NativeDependentReceiptCoherenceCandidates
open NativeDependentReceiptCoherenceCandidates.Canaries
open NativeDependentReceiptComputad

/-! ## The concrete dependent-receipt unit pair -/

/-- The raw one-cell base containing the administrative comparison. -/
abbrev administrativeBase :=
  receiptBase retainedTower.computation Tower.rules.headEq 0

/-- The complete raw-cell fibre containing the administrative comparison. -/
abbrev AdministrativeCell :=
  Cell administrativeBase AdministrativeGenerator
    doubledReflexivity oneReflexivity

/-- The original authored administrative comparison in the common computad. -/
def retainedAdministrativeCell : AdministrativeCell :=
  toCommon administrativeCell

/-- The same comparison with an explicit reflexive cell vertically composed
on the left.  A bicategorical unit law would relate or identify this with the
un-padded comparison. -/
def leftUnitPaddedAdministrativeCell : AdministrativeCell :=
  Cell.vertical
    (Cell.refl (base := administrativeBase)
      (Generator := AdministrativeGenerator) doubledReflexivity)
    retainedAdministrativeCell

/-- Authored-generator count cannot observe the inserted unit. -/
theorem generatorCount_identifies_leftUnit :
    generatorCount leftUnitPaddedAdministrativeCell =
      generatorCount retainedAdministrativeCell :=
  generatorCount_leftUnit retainedAdministrativeCell

/-- Complete raw-constructor count does observe the inserted unit. -/
theorem constructorCount_separates_leftUnit :
    constructorCount leftUnitPaddedAdministrativeCell ≠
      constructorCount retainedAdministrativeCell :=
  constructorCount_leftUnit_ne retainedAdministrativeCell

/-- The unit-padded and retained cells are not silently equal in the raw
computad. -/
theorem leftUnitPadded_ne_retained :
    leftUnitPaddedAdministrativeCell ≠ retainedAdministrativeCell := by
  intro equality
  exact constructorCount_separates_leftUnit
    (congrArg constructorCount equality)

/-! ## A concrete reassociation pair -/

/-- The administrative comparison with both endpoint identities associated
to the left. -/
def leftAssociatedAdministrativeCell : AdministrativeCell :=
  Cell.vertical
    (Cell.vertical
      (Cell.refl (base := administrativeBase)
        (Generator := AdministrativeGenerator) doubledReflexivity)
      retainedAdministrativeCell)
    (Cell.refl (base := administrativeBase)
      (Generator := AdministrativeGenerator) oneReflexivity)

/-- The same three cells associated to the right. -/
def rightAssociatedAdministrativeCell : AdministrativeCell :=
  Cell.vertical
    (Cell.refl (base := administrativeBase)
      (Generator := AdministrativeGenerator) doubledReflexivity)
    (Cell.vertical retainedAdministrativeCell
      (Cell.refl (base := administrativeBase)
        (Generator := AdministrativeGenerator) oneReflexivity))

/-- Authored-generator count is invariant under this reassociation. -/
theorem generatorCount_identifies_reassociation :
    generatorCount leftAssociatedAdministrativeCell =
      generatorCount rightAssociatedAdministrativeCell := by
  exact generatorCount_vertical_assoc
    (Cell.refl (base := administrativeBase)
      (Generator := AdministrativeGenerator) doubledReflexivity)
    retainedAdministrativeCell
    (Cell.refl (base := administrativeBase)
      (Generator := AdministrativeGenerator) oneReflexivity)

/-- Total node count also misses reassociation. -/
theorem constructorCount_identifies_reassociation :
    constructorCount leftAssociatedAdministrativeCell =
      constructorCount rightAssociatedAdministrativeCell := by
  simp [leftAssociatedAdministrativeCell,
    rightAssociatedAdministrativeCell]
  omega

/-- The full raw tree shape retains the association choice. -/
theorem rawShape_separates_reassociation :
    rawShape leftAssociatedAdministrativeCell ≠
      rawShape rightAssociatedAdministrativeCell := by
  simp [leftAssociatedAdministrativeCell,
    rightAssociatedAdministrativeCell]

/-- Reassociated cells remain distinct in the retained computad. -/
theorem leftAssociated_ne_rightAssociated :
    leftAssociatedAdministrativeCell ≠
      rightAssociatedAdministrativeCell := by
  intro equality
  exact rawShape_separates_reassociation (congrArg rawShape equality)

/-! ## A concrete interchange pair -/

/-- The cell fibre obtained by composing two copies of the administrative
comparison horizontally. -/
abbrev AdministrativeHorizontalCell :=
  Cell administrativeBase AdministrativeGenerator
    (administrativeBase.compose doubledReflexivity doubledReflexivity)
    (administrativeBase.compose oneReflexivity oneReflexivity)

/-- Compose the two administrative comparisons by transporting the left
comparison first. -/
def horizontalRightThenLeftAdministrativeCell :
    AdministrativeHorizontalCell :=
  Cell.horizontalRightThenLeft
    retainedAdministrativeCell retainedAdministrativeCell

/-- Compose the same comparisons by transporting the right comparison
first. -/
def horizontalLeftThenRightAdministrativeCell :
    AdministrativeHorizontalCell :=
  Cell.horizontalLeftThenRight
    retainedAdministrativeCell retainedAdministrativeCell

/-- Authored-generator count identifies the two horizontal histories. -/
theorem generatorCount_identifies_administrative_interchange :
    generatorCount horizontalRightThenLeftAdministrativeCell =
      generatorCount horizontalLeftThenRightAdministrativeCell :=
  generatorCount_identifies_interchange
    retainedAdministrativeCell retainedAdministrativeCell

/-- Total constructor count also identifies the two horizontal histories. -/
theorem constructorCount_identifies_administrative_interchange :
    constructorCount horizontalRightThenLeftAdministrativeCell =
      constructorCount horizontalLeftThenRightAdministrativeCell :=
  constructorCount_identifies_interchange
    retainedAdministrativeCell retainedAdministrativeCell

/-- Full construction shape retains which comparison was transported first. -/
theorem rawShape_separates_administrative_interchange :
    rawShape horizontalRightThenLeftAdministrativeCell ≠
      rawShape horizontalLeftThenRightAdministrativeCell :=
  rawShape_separates_interchange
    retainedAdministrativeCell retainedAdministrativeCell

/-- Prime therefore retains the two raw horizontal construction histories as
distinct cells before a consumer earns strict interchange. -/
theorem horizontalAdministrativeCells_ne :
    horizontalRightThenLeftAdministrativeCell ≠
      horizontalLeftThenRightAdministrativeCell :=
  horizontalRightThenLeft_ne_horizontalLeftThenRight
    retainedAdministrativeCell retainedAdministrativeCell

/-! ## A capability-indexed observation family -/

inductive Policy where
  | authoredGenerators
  | rawConstructors
  | constructionShape
deriving DecidableEq

/-- The same observation vocabulary applies to every parallel cell fibre of
the dependent receipt computad. -/
def cellPolicies
    {source target : administrativeBase.Object}
    {first second : administrativeBase.Hom source target} :
    PolicyFamily (Cell administrativeBase AdministrativeGenerator first second) where
  Policy := Policy
  Result := fun
    | .authoredGenerators => Nat
    | .rawConstructors => Nat
    | .constructionShape => RawShape
  decide := fun
    | .authoredGenerators => generatorCount
    | .rawConstructors => constructorCount
    | .constructionShape => rawShape

/-- One family exposes both a unit-insensitive semantic statistic and the
complete raw construction-history statistic for the original administrative
comparison. -/
def policies : PolicyFamily AdministrativeCell :=
  cellPolicies

/-- The same complete family for the horizontal-composite fibre. -/
def interchangePolicies : PolicyFamily AdministrativeHorizontalCell :=
  cellPolicies

inductive GeneratorOnlyRequest where
  | authoredGenerators
deriving DecidableEq

/-- The smaller request asks only for the observation invariant under the
proposed unit equation. -/
def generatorOnlyFamily : PolicyFamily AdministrativeCell :=
  policies.reindex (fun _ : GeneratorOnlyRequest => Policy.authoredGenerators)

/-- The generator-only request on the horizontal-composite fibre. -/
def interchangeGeneratorOnlyFamily :
    PolicyFamily AdministrativeHorizontalCell :=
  interchangePolicies.reindex
    (fun _ : GeneratorOnlyRequest => Policy.authoredGenerators)

/-- Generator count itself is an executable sufficient readout for the
unit-insensitive request. -/
theorem generatorCount_supports_generatorOnly :
    generatorOnlyFamily.SupportsReadout
      (generatorCount : AdministrativeCell → Nat) := by
  refine ⟨{
    run := fun _ count => count
    agrees := ?_ }⟩
  intro policy cell
  cases policy
  rfl

/-- Authored-generator count is likewise sufficient for the small
horizontal-composite request. -/
theorem generatorCount_supports_interchangeGeneratorOnly :
    interchangeGeneratorOnlyFamily.SupportsReadout
      (generatorCount : AdministrativeHorizontalCell → Nat) := by
  refine ⟨{
    run := fun _ count => count
    agrees := ?_ }⟩
  intro policy cell
  cases policy
  rfl

/-- Any proposed key that identifies the left-unit pair is insufficient for
the complete policy family, because the raw-history policy separates them. -/
theorem any_leftUnit_identifying_key_refuses_fullFamily
    {Key : Type} (key : AdministrativeCell → Key)
    (identifies :
      key leftUnitPaddedAdministrativeCell =
        key retainedAdministrativeCell) :
    ¬ policies.SupportsReadout key :=
  policies.not_supportsReadout_of_policy_collision key identifies
    Policy.rawConstructors constructorCount_separates_leftUnit

/-- The concrete unit-insensitive generator-count key is therefore useful for
the small request and correctly refused for the history-sensitive request. -/
theorem generatorCount_refuses_fullFamily :
    ¬ policies.SupportsReadout
      (generatorCount : AdministrativeCell → Nat) :=
  any_leftUnit_identifying_key_refuses_fullFamily generatorCount
    generatorCount_identifies_leftUnit

/-- Any key that identifies the reassociated pair is likewise insufficient
for the complete family, even when it retains both scalar counts. -/
theorem any_reassociation_identifying_key_refuses_fullFamily
    {Key : Type} (key : AdministrativeCell → Key)
    (identifies :
      key leftAssociatedAdministrativeCell =
        key rightAssociatedAdministrativeCell) :
    ¬ policies.SupportsReadout key :=
  policies.not_supportsReadout_of_policy_collision key identifies
    Policy.constructionShape rawShape_separates_reassociation

/-- The generator-count key is refused independently by reassociation. -/
theorem generatorCount_refuses_fullFamily_by_reassociation :
    ¬ policies.SupportsReadout
      (generatorCount : AdministrativeCell → Nat) :=
  any_reassociation_identifying_key_refuses_fullFamily generatorCount
    generatorCount_identifies_reassociation

/-- Any proposed horizontal-cell key that identifies the two interchange
histories is insufficient for the full receipt policy family. -/
theorem any_interchange_identifying_key_refuses_fullFamily
    {Key : Type} (key : AdministrativeHorizontalCell → Key)
    (identifies :
      key horizontalRightThenLeftAdministrativeCell =
        key horizontalLeftThenRightAdministrativeCell) :
    ¬ interchangePolicies.SupportsReadout key :=
  interchangePolicies.not_supportsReadout_of_policy_collision key identifies
    Policy.constructionShape rawShape_separates_administrative_interchange

/-- Generator count is admitted for its declared small request and refused
for the full horizontal receipt request. -/
theorem generatorCount_refuses_interchangeFullFamily :
    ¬ interchangePolicies.SupportsReadout
      (generatorCount : AdministrativeHorizontalCell → Nat) :=
  any_interchange_identifying_key_refuses_fullFamily generatorCount
    generatorCount_identifies_administrative_interchange

/-- The exact extensional admission condition for every proposed receipt
key: all requested observations must agree on every key collision. -/
theorem supports_fullFamily_iff_preserves_every_policy
    {Key : Type} (key : AdministrativeCell → Key) :
    policies.SupportsReadout key ↔ policies.CompatibleReadout key := by
  letI : Nonempty AdministrativeCell := ⟨retainedAdministrativeCell⟩
  exact policies.supportsReadout_iff_compatible key

/-- Retaining the raw cell supports both observations without reconstruction. -/
theorem retainedCell_supports_fullFamily :
    policies.SupportsReadout (id : AdministrativeCell → AdministrativeCell) := by
  refine ⟨{
    run := fun policy cell => policies.decide policy cell
    agrees := ?_ }⟩
  intro policy cell
  rfl

/-- Retaining the horizontal cell itself supports every declared observation
without reconstructing its construction history. -/
theorem retainedHorizontalCell_supports_fullFamily :
    interchangePolicies.SupportsReadout
      (id : AdministrativeHorizontalCell → AdministrativeHorizontalCell) := by
  refine ⟨{
    run := fun policy cell => interchangePolicies.decide policy cell
    agrees := ?_ }⟩
  intro policy cell
  rfl

/-- The checked coherence boundary in one statement: the unit-insensitive
face is accepted for its exact request, refused for a stronger history
request, and the retained face supports both. -/
theorem leftUnit_coherence_is_capability_relative :
    generatorCount leftUnitPaddedAdministrativeCell =
        generatorCount retainedAdministrativeCell ∧
      generatorOnlyFamily.SupportsReadout
        (generatorCount : AdministrativeCell → Nat) ∧
      ¬ policies.SupportsReadout
        (generatorCount : AdministrativeCell → Nat) ∧
      policies.SupportsReadout
        (id : AdministrativeCell → AdministrativeCell) :=
  ⟨generatorCount_identifies_leftUnit,
    generatorCount_supports_generatorOnly,
    generatorCount_refuses_fullFamily,
    retainedCell_supports_fullFamily⟩

/-- Reassociation obeys the same capability-relative boundary while also
showing that retaining two scalar receipt statistics is not enough to retain
construction shape. -/
theorem reassociation_coherence_is_capability_relative :
    generatorCount leftAssociatedAdministrativeCell =
        generatorCount rightAssociatedAdministrativeCell ∧
      constructorCount leftAssociatedAdministrativeCell =
        constructorCount rightAssociatedAdministrativeCell ∧
      rawShape leftAssociatedAdministrativeCell ≠
        rawShape rightAssociatedAdministrativeCell ∧
      generatorOnlyFamily.SupportsReadout
        (generatorCount : AdministrativeCell → Nat) ∧
      ¬ policies.SupportsReadout
        (generatorCount : AdministrativeCell → Nat) :=
  ⟨generatorCount_identifies_reassociation,
    constructorCount_identifies_reassociation,
    rawShape_separates_reassociation,
    generatorCount_supports_generatorOnly,
    generatorCount_refuses_fullFamily_by_reassociation⟩

/-- Prime's concrete interchange boundary: the two scalar observations admit
the equation, the complete construction observation refuses it, and retaining
the proof-relevant cell supports every request. -/
theorem interchange_coherence_is_capability_relative :
    generatorCount horizontalRightThenLeftAdministrativeCell =
        generatorCount horizontalLeftThenRightAdministrativeCell ∧
      constructorCount horizontalRightThenLeftAdministrativeCell =
        constructorCount horizontalLeftThenRightAdministrativeCell ∧
      rawShape horizontalRightThenLeftAdministrativeCell ≠
        rawShape horizontalLeftThenRightAdministrativeCell ∧
      interchangeGeneratorOnlyFamily.SupportsReadout
        (generatorCount : AdministrativeHorizontalCell → Nat) ∧
      ¬ interchangePolicies.SupportsReadout
        (generatorCount : AdministrativeHorizontalCell → Nat) ∧
      interchangePolicies.SupportsReadout
        (id : AdministrativeHorizontalCell → AdministrativeHorizontalCell) :=
  ⟨generatorCount_identifies_administrative_interchange,
    constructorCount_identifies_administrative_interchange,
    rawShape_separates_administrative_interchange,
    generatorCount_supports_interchangeGeneratorOnly,
    generatorCount_refuses_interchangeFullFamily,
    retainedHorizontalCell_supports_fullFamily⟩

#print axioms generatorCount_identifies_leftUnit
#print axioms constructorCount_separates_leftUnit
#print axioms leftUnitPadded_ne_retained
#print axioms generatorCount_identifies_reassociation
#print axioms constructorCount_identifies_reassociation
#print axioms rawShape_separates_reassociation
#print axioms leftAssociated_ne_rightAssociated
#print axioms generatorCount_identifies_administrative_interchange
#print axioms constructorCount_identifies_administrative_interchange
#print axioms rawShape_separates_administrative_interchange
#print axioms horizontalAdministrativeCells_ne
#print axioms generatorCount_supports_generatorOnly
#print axioms generatorCount_supports_interchangeGeneratorOnly
#print axioms any_leftUnit_identifying_key_refuses_fullFamily
#print axioms generatorCount_refuses_fullFamily
#print axioms any_reassociation_identifying_key_refuses_fullFamily
#print axioms generatorCount_refuses_fullFamily_by_reassociation
#print axioms any_interchange_identifying_key_refuses_fullFamily
#print axioms generatorCount_refuses_interchangeFullFamily
#print axioms supports_fullFamily_iff_preserves_every_policy
#print axioms retainedCell_supports_fullFamily
#print axioms retainedHorizontalCell_supports_fullFamily
#print axioms leftUnit_coherence_is_capability_relative
#print axioms reassociation_coherence_is_capability_relative
#print axioms interchange_coherence_is_capability_relative

end NativeDependentReceiptCoherenceObservation
end Mettapedia.Languages.MeTTa.Prime
