import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalClassifyingUniversalProperty
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalCanonicalMapControls
import Mettapedia.TypeTheory.ContextualPrimitiveCellControls

/-!
# Classifying controls with independent native families and witnesses

The independently sized marked family model has a function-indexed finite
family and a full dependent primitive branch. The actual generated model
interpretation retains both supplied witness positions. Each coherent cell
must commute with the independent complete declaration square; that local
condition earns uniqueness on every generated and raw context.

The separate free structural interpretation has an actual nonidentity natural
cartesian cell. Its changed primitive witness fails declaration-fixed admission,
showing why unrestricted cell uniqueness is not the asserted property.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ClassifyingCells
open CanonicalMapControls

noncomputable abbrev nativeModel := markedQualified.commonUniverseLift.{0,1,0,1,0,0}
noncomputable abbrev canonical := Classifying.interpretation Controls.headers markedQualified

/-- The earned canonical interpreter meets the independent primitive
display square at the actually declared function-indexed family. -/
theorem fibre_admission :
    (LiftedModelMapComparison.correctedIso Controls.headers canonical canonical).hom.base.app
      ⟨ULift.up ((QuotientCwf.cwf Controls.signature).ext
        ((SyntacticModel.data Controls.headers).typeParameters .fibre).1
        ((SyntacticModel.data Controls.headers).typeFamily .fibre))⟩ ≫
        eqToHom (primitiveImage Controls.headers nativeModel canonical .fibre) =
      eqToHom (primitiveImage Controls.headers nativeModel canonical .fibre) :=
  canonical_admitted Controls.headers nativeModel canonical canonical .fibre

/-- An independently supplied logical and primitive-preserving
interpretation has exactly one complete declaration-admitted isomorphism. -/
@[instance_reducible] noncomputable def comparison
    (other : ModelMap sourceData nativeModel.data) : Unique (canonical ≅ other) :=
  Classifying.comparisonUnique Controls.headers markedQualified other

/-- Uniqueness consumes the local independent primitive square, rather
than assuming agreement at all generated contexts or at their components. -/
theorem complete_cell_unique (other : ModelMap sourceData nativeModel.data)
    (candidate : CorrectedTransformationData canonical.morphism.toPseudo other.morphism.toPseudo)
    (admitted : PrimitiveAdmission Controls.headers nativeModel canonical other candidate) :
    candidate = (comparisonCell Controls.headers nativeModel canonical other).val :=
  cell_unique Controls.headers nativeModel canonical other candidate admitted

theorem coherent_composition
    (first second : ModelMap sourceData nativeModel.data) :
    comparisonCell Controls.headers nativeModel canonical first ≫
      comparisonCell Controls.headers nativeModel first second =
        comparisonCell Controls.headers nativeModel canonical second :=
  comparison_composition Controls.headers nativeModel canonical first second

/-- Both genuinely different dependent witnesses survive the universal
interpreter and cannot be collapsed to existence alone. -/
theorem exact_dependent_readouts :
    (interpretedBranch ModelControls.trueZero).val = 0 ∧
      (interpretedBranch ModelControls.trueOne).val = 1 ∧
        (interpretedBranch ModelControls.trueZero).val ≠
          (interpretedBranch ModelControls.trueOne).val :=
  ⟨supplied_positions_retained.1, supplied_positions_retained.2,
    collapsing_the_second_witness_fails⟩

theorem actual_substitution_changes_positions :
    plainMapping.morphism.toFamilyMorphism.base.map sourceExchange ≠
      plainMapping.morphism.toFamilyMorphism.base.map sourceIdentity :=
  mapped_exchange_is_nonidentity

/-- Cartesian naturality and a fixed empty context permit a nonidentity
cell if the primitive complete display reading is omitted. -/
theorem dropping_primitive_reading_allows_extra_cell :
    let F := Mettapedia.TypeTheory.ContextualPrimitiveCellControls.valuations
    let cell := Mettapedia.TypeTheory.ContextualPrimitiveCellControls.negate
    cell.app ⟨(0 : Nat)⟩ = 𝟙 (F.obj ⟨(0 : Nat)⟩) ∧
      cell.app ⟨(1 : Nat)⟩ ≠ 𝟙 (F.obj ⟨(1 : Nat)⟩) ∧ cell ≠ 𝟙 F :=
  ⟨Mettapedia.TypeTheory.ContextualPrimitiveCellControls.empty_fixed,
    Mettapedia.TypeTheory.ContextualPrimitiveCellControls.primitive_display_not_fixed,
    Mettapedia.TypeTheory.ContextualPrimitiveCellControls.unrestricted_cell_not_identity⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingControls
