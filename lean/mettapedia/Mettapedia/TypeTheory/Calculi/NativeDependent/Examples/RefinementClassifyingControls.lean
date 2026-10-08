import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingUniversalProperty
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualAssumptionComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementAbstractModelMapControls
import Mettapedia.TypeTheory.ContextualPrimitiveCellControls

/-!
# Coherent classification with retained guarded presentations

The actual native model interprets conditional natural-number refinements and
input-dependent finite families. Its declaration-admitted comparison is unique
as a complete corrected cell. Two different authored assumption contexts are
connected by generated guarded substitutions and retained through the natural
comparison; their raw objects are never identified.

A separate structural one-sort model has a genuine natural cartesian cell
which changes the full primitive witness. Its independently fixed declaration
square fails. This negative concerns structural cell admission; no dependent
products or sums are attributed to that auxiliary model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Refinement.Abstract ClassifyingCells

noncomputable section

abbrev nativeModel := AbstractModelMapControls.targetQualified
abbrev source := AbstractModelMapControls.source
abbrev canonical := Classifying.interpretation Controls.headerFormation
  AbstractModelMapControls.nativeQualified

/-- Primitive admission compares the actual complete family display with
the independently declared target family. -/
theorem dependent_fibre_admitted :
    (ModelMapComparison.correctedIso Controls.headerFormation canonical canonical).hom.base.app
      ⟨(Interpretation.SourceModel.{0,1} Controls.signature).toCwf.ext
        ((sourceModel.{0,1} Controls.headerFormation).data.typeParameters .fibre).1
        ((sourceModel.{0,1} Controls.headerFormation).data.typeFamily .fibre)⟩ ≫
          eqToHom (primitiveFamilyImage Controls.headerFormation nativeModel canonical .fibre) =
        eqToHom (primitiveFamilyImage Controls.headerFormation nativeModel canonical .fibre) :=
  (canonical_admitted Controls.headerFormation nativeModel canonical canonical).families .fibre

/-- The primitive predicate also retains its satisfying parameter context,
rather than reducing the declaration to its truth value at one input. -/
theorem positive_assumption_admitted :
    (ModelMapComparison.correctedIso Controls.headerFormation canonical canonical).hom.base.app
      ⟨(sourceModel.{0,1} Controls.headerFormation).localModel.assumptions.assumed
        ((sourceModel.{0,1} Controls.headerFormation).data.predicateParameters .positive).1
        ((sourceModel.{0,1} Controls.headerFormation).data.predicateValue .positive)⟩ ≫
          eqToHom (primitivePredicateImage Controls.headerFormation nativeModel canonical .positive) =
        eqToHom (primitivePredicateImage Controls.headerFormation nativeModel canonical .positive) :=
  (canonical_admitted Controls.headerFormation nativeModel canonical canonical).predicates .positive

@[instance_reducible] def comparison (other : ModelMap source nativeModel.data) :
    Unique (canonical ≅ other) :=
  Classifying.comparisonUnique Controls.headerFormation AbstractModelMapControls.nativeQualified other

theorem complete_cell_unique (other : ModelMap source nativeModel.data)
    (candidate : CorrectedTransformationData canonical.morphism.toPseudo other.morphism.toPseudo)
    (admitted : PrimitiveAdmission Controls.headerFormation nativeModel canonical other candidate) :
    candidate = (comparisonCell Controls.headerFormation nativeModel canonical other).val :=
  cell_unique Controls.headerFormation nativeModel canonical other candidate admitted

/-- The local admission forces predicate compatibility on every source
class, including conditional predicates over retained raw contexts. -/
theorem complete_predicate_square (other : ModelMap source nativeModel.data)
    (candidate : CorrectedTransformationData canonical.morphism.toPseudo other.morphism.toPseudo)
    (admitted : PrimitiveAdmission Controls.headerFormation nativeModel canonical other candidate)
    (Γ : (Interpretation.SourceModel.{0,1} Controls.signature).toCwf.Ctx)
    (predicate : (sourceModel.{0,1} Controls.headerFormation).localModel.doctrine.Predicate Γ) :
    nativeModel.localModel.doctrine.reindex (candidate.base.app ⟨Γ⟩)
      (other.predicates.doctrine.hom Γ predicate) = canonical.predicates.doctrine.hom Γ predicate :=
  admitted_predicate_coherence Controls.headerFormation nativeModel canonical other candidate
    admitted Γ predicate

def scalarContext : Context Controls.signature :=
  ⟨1, .snoc .nil (Controls.scalar 0), derivationContextFormation Controls.scalarContext⟩

def positivity : PredicateOver scalarContext := ⟨Controls.positive 0, ⟨Controls.positiveVariable⟩⟩

def redundantPositivity : PredicateOver scalarContext :=
  Logic.conjunction positivity (Logic.truth scalarContext)

theorem positivity_equation :
    Holds Controls.signature (.predicateEq scalarContext.raw positivity.code redundantPositivity.code) :=
  Logic.order_antisymm
    (Logic.raw_le_meet (Logic.order_refl positivity) (Logic.raw_le_truth positivity))
    (Logic.raw_meet_left positivity (Logic.truth scalarContext))

abbrev firstContext := assumed scalarContext positivity
abbrev secondContext := assumed scalarContext redundantPositivity

theorem raw_contexts_differ : firstContext.raw ≠ secondContext.raw := by
  intro same
  cases same

private def assumptionShape {n : Nat} (context : ContextExpr Controls.symbols n) : Bool :=
  match context with
  | .assume _ (.and _ _) => true
  | _ => false

theorem context_objects_differ : firstContext ≠ secondContext := by
  intro same
  have shape := congrArg (fun context : Context Controls.signature => assumptionShape context.raw) same
  exact (by decide : false ≠ true) shape

def guardedComparison : firstContext ≅ secondContext :=
  assumptionComparison positivity redundantPositivity positivity_equation

theorem guarded_comparison_retains_every_input :
    guardedComparison.hom.substitution = TermExpr.var :=
  assumptionArrow_tuple positivity redundantPositivity positivity_equation

theorem guarded_comparison_preserves_projection :
    guardedComparison.hom ≫ assumptionInclusion scalarContext redundantPositivity =
      assumptionInclusion scalarContext positivity :=
  assumptionArrow_projection positivity redundantPositivity positivity_equation

abbrev firstObject := (quotientProjection Controls.signature).obj firstContext
abbrev secondObject := (quotientProjection Controls.signature).obj secondContext

def quotientGuardedComparison : firstObject ≅ secondObject :=
  (quotientProjection Controls.signature).mapIso guardedComparison

/-- The derived unique corrected cell is natural on an actual guarded
isomorphism between different retained raw objects. -/
theorem comparison_on_distinct_raw_contexts (other : ModelMap source nativeModel.data) :
    (ModelMapComparison.contextFunctor canonical).map quotientGuardedComparison.hom ≫
      (comparisonCell Controls.headerFormation nativeModel canonical other).val.base.app
        ⟨ULift.up secondObject⟩ =
      (comparisonCell Controls.headerFormation nativeModel canonical other).val.base.app
        ⟨ULift.up firstObject⟩ ≫
          (ModelMapComparison.contextFunctor other).map quotientGuardedComparison.hom :=
  by
    let raised : (⟨ULift.up firstObject⟩ :
        (Interpretation.SourceModel.{0,1} Controls.signature).toCwf.base.Context) ⟶
      ⟨ULift.up secondObject⟩ := ULift.up quotientGuardedComparison.hom
    change canonical.morphism.toFamilyMorphism.base.map raised ≫
        (comparisonCell Controls.headerFormation nativeModel canonical other).val.base.app
          ⟨ULift.up secondObject⟩ =
      (comparisonCell Controls.headerFormation nativeModel canonical other).val.base.app
        ⟨ULift.up firstObject⟩ ≫ other.morphism.toFamilyMorphism.base.map raised
    exact (comparisonCell Controls.headerFormation nativeModel canonical other).val.base.naturality raised

/-- Compose the unique coherent interpretation comparison with the
independently generated guarded context isomorphism. -/
def interpretedGuardedComparison (other : ModelMap source nativeModel.data) :
    (ModelMapComparison.contextFunctor canonical).obj firstObject ≅
      (ModelMapComparison.contextFunctor other).obj secondObject :=
  (ModelMapComparison.contextIso Controls.headerFormation canonical other).app firstObject ≪≫
    (ModelMapComparison.contextFunctor other).mapIso quotientGuardedComparison

theorem canonical_map_retains_complete_conditional_value :
    HEq (canonical.morphism.toFamilyMorphism.mapTerm
      AbstractModelMapControls.sourceConditionalCertificate)
      (ULift.up InterpretationControls.conditionalRefined) :=
  AbstractModelMapControls.exact_supplied_certificate_image

theorem dependent_inputs_survive_classification (world : InterpretationControls.Worldᵒᵖ)
    (number : Nat) :
    InterpretationControls.fibreType.decoded.obj
      ⟨world, (⟨PUnit.unit, number⟩ : AbstractInterpretationControls.scalarScope.1.obj world)⟩ =
        Fin (Nat.succ number) :=
  AbstractModelMapControls.actual_fibre_depends_on_input world number

/-- This actual structural cell fixes the empty context and commutes with
the complete cartesian tuple reading while changing the newest witness. -/
theorem unrestricted_cartesian_candidate_changes_witness :
    let F := Mettapedia.TypeTheory.ContextualPrimitiveCellControls.valuations
    let candidate := Mettapedia.TypeTheory.ContextualPrimitiveCellControls.negate
    candidate.app ⟨(0 : Nat)⟩ = 𝟙 (F.obj ⟨(0 : Nat)⟩) ∧
      (∀ context valuation,
        Mettapedia.TypeTheory.ContextualPrimitiveCellControls.comprehensionReading context
          (candidate.app ⟨context + 1⟩ valuation) =
            ((fun position => !((Mettapedia.TypeTheory.ContextualPrimitiveCellControls.comprehensionReading
              context valuation).1 position)),
              !((Mettapedia.TypeTheory.ContextualPrimitiveCellControls.comprehensionReading
                context valuation).2))) ∧
      (candidate.app ⟨(1 : Nat)⟩ (fun _ => false)) 0 = true :=
  ⟨Mettapedia.TypeTheory.ContextualPrimitiveCellControls.empty_fixed,
    Mettapedia.TypeTheory.ContextualPrimitiveCellControls.complete_cartesian_reading,
    Mettapedia.TypeTheory.ContextualPrimitiveCellControls.newest_witness_changed⟩

/-- Its independently fixed complete declaration square fails. This is a
control of structural admission, not a claimed qualified logical model. -/
theorem unrestricted_candidate_fails_declaration_square :
    let F := Mettapedia.TypeTheory.ContextualPrimitiveCellControls.valuations
    let candidate := Mettapedia.TypeTheory.ContextualPrimitiveCellControls.negate
    candidate.app ⟨(1 : Nat)⟩ ≫ eqToHom (rfl : F.obj ⟨(1 : Nat)⟩ = F.obj ⟨(1 : Nat)⟩) ≠
      eqToHom (rfl : F.obj ⟨(1 : Nat)⟩ = F.obj ⟨(1 : Nat)⟩) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    Mettapedia.TypeTheory.ContextualPrimitiveCellControls.primitive_display_not_fixed

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingControls
