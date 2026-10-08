import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalCanonicalModelMap
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapLiftedCorrectedComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalModelMapControls
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalContextualInterpretationControls

/-!
# Canonical logical maps retaining declared native evidence

The source syntax is small, while the native dependent family model has
independently sized carriers. The canonical map retains an actual chosen mark,
a function-indexed finite family, both supplied witness positions and a
nonidentity assumption exchange. Comparison is available on all retained raw
contexts through the complete common-carrier corrected isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.CanonicalMapControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Interpretation
open ModelMapControls

noncomputable def markedQualified : QualifiedModel Controls.signature markedModel where
  data := markedData true
  realization := marked_realization true
  products_substitution := marked_product_substitution
  products_beta := marked_product_beta
  products_eta := marked_product_eta

noncomputable abbrev mapping := canonicalModelMap markedQualified Controls.headers
noncomputable abbrev sourceData :=
  (SyntacticModel.data Controls.headers).commonUniverseLift.{0,0,0,0,0,1}

/-- A genuinely declared family maps to the supplied marked family. -/
theorem supplied_fibre_preserved :
    HEq (mapping.morphism.toFamilyMorphism.mapType (sourceData.typeFamily .fibre))
      (ULift.up (ModelControls.declarations.fibre, true) :
        (TargetModel.{0,1,0,1,0} markedModel).toCwf.Ty
          (ULift.up (markContext true (ModelControls.model.typeParameters .fibre)).1)) :=
  mapping.typeFamily .fibre

noncomputable def interpretedBranch :=
  (cast (type_eq_of_heq (mapping.termValue .fullBranch))
    (mapping.morphism.toFamilyMorphism.mapTerm (sourceData.termValue .fullBranch))).down

theorem exact_supplied_branch : interpretedBranch = suppliedBranch := by
  exact congrArg ULift.down (eq_of_heq ((cast_heq _ _).trans (mapping.termValue .fullBranch)))

theorem supplied_positions_retained :
    (interpretedBranch ModelControls.trueZero).val = 0 ∧
      (interpretedBranch ModelControls.trueOne).val = 1 := by
  rw [exact_supplied_branch]
  exact ⟨rfl,rfl⟩

theorem function_index_changes_fibre :
    Fintype.card (ModelControls.declarations.fibre ⟨PUnit.unit, ModelControls.falseFunction⟩) = 1 ∧
      Fintype.card (ModelControls.declarations.fibre ⟨PUnit.unit, ModelControls.trueFunction⟩) = 2 :=
  ModelControls.function_changes_domain

theorem collapsing_the_second_witness_fails :
    (interpretedBranch ModelControls.trueZero).val ≠
      (interpretedBranch ModelControls.trueOne).val := by
  rw [supplied_positions_retained.1, supplied_positions_retained.2]
  decide

noncomputable abbrev plainMapping :=
  canonicalModelMap InterpretationControls.qualified Controls.headers

noncomputable def sourceExchange :=
  (ULift.up ((quotientProjection Controls.signature).map InterpretationControls.exchange) :
    (SourceModel.{0,1} Controls.signature).toCwf.Sub
      (ULift.up ((quotientProjection Controls.signature).obj InterpretationControls.assumptionContext))
      (ULift.up ((quotientProjection Controls.signature).obj InterpretationControls.assumptionContext)))

noncomputable def sourceIdentity :=
  (ULift.up ((quotientProjection Controls.signature).map
    (𝟙 InterpretationControls.assumptionContext)) :
    (SourceModel.{0,1} Controls.signature).toCwf.Sub
      (ULift.up ((quotientProjection Controls.signature).obj InterpretationControls.assumptionContext))
      (ULift.up ((quotientProjection Controls.signature).obj InterpretationControls.assumptionContext)))

theorem mapped_exchange_is_nonidentity :
    plainMapping.morphism.toFamilyMorphism.base.map sourceExchange ≠
      plainMapping.morphism.toFamilyMorphism.base.map sourceIdentity := by
  intro same
  exact InterpretationControls.mapped_exchange_is_nonidentity (congrArg ULift.down same)

/-- Any independently supplied local model map has a complete displayed
comparison with the canonical map, including the retained raw objects. -/
noncomputable def comparison
    (other : ModelMap sourceData (markedQualified.data.commonUniverseLift.{0,1,0,1,0,0})) :
    other.morphism.toPseudo ≅ mapping.morphism.toPseudo :=
  LiftedModelMapComparison.correctedIso Controls.headers other mapping

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.CanonicalMapControls
