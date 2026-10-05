import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerClassifier
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamiliesControls

/-!
# Infinite, varying parameter controls for the contextual power classifier

The parameter object is the actual free receipt presheaf on the infinite
observed path context. Restriction retains the receipt generator and appends
the authored history. A later fibre contains infinitely many distinct
receipts, and new generator receipts are outside the restriction image.

A stable product predicate tests the first history label of its parameter.
Its constructed natural classifier recovers the previously local history
predicates at the initial parameter. This does not turn those local values
into a compatible global section: the parameter itself changes along each
history. Their present material subsets agree while their full future
material values differ.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerClassifierControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open FuturePowerFamilies FuturePowerClassifier
open ContextualGeneratedUniverse
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open ContextualPowerFamiliesControls

abbrev parameters := free (E := actualContext.base.Elements)

def initialParameter : parameters.obj initialPoint := seed initialPoint

def historyPredicate (label : Nat) : StablePredicate (product parameters domain.family) where
  holds point := ∃ rest, point.2.1.2.val.unop.unop.val = label :: rest
  closed {first second} step available := by
    obtain ⟨rest, starts⟩ := available
    have parameterEq : parameters.map step.1 first.2.1 = second.2.1 := congrArg Prod.fst step.2
    have triangle := congrArg
      (fun receipt : parameters.obj second.1 => receipt.2.val.unop.unop.val) parameterEq
    change first.2.1.2.val.unop.unop.val ++ step.1.val.unop.unop.val =
      second.2.1.2.val.unop.unop.val at triangle
    refine ⟨rest ++ step.1.val.unop.unop.val, ?_⟩
    rw [← triangle, starts]
    rfl

def historyClassifier (label : Nat) : NaturalHom parameters (family domain.family) :=
  classifier parameters domain.family (historyPredicate label)

/-- The history-sensitive local power value is now realized by a natural
map from an independently constructed, nonconstant parameter object. -/
theorem initial_history_predicate (label : Nat) :
    (historyClassifier label).app initialPoint initialParameter = startsWith label := by
  apply Predicate.ext
  intro argument
  change (∃ rest, (𝟙 initialPoint ≫ argument.1.2).val.unop.unop.val = label :: rest) ↔
    ∃ rest, argument.1.2.val.unop.unop.val = label :: rest
  rw [Category.id_comp]

theorem initial_future_truth (label other : Nat) :
    ((historyClassifier label).app initialPoint initialParameter).holds (futureArgument other) ↔ label = other := by
  rw [initial_history_predicate]
  exact startsWith_future_iff label other

theorem initial_no_present_truth (label : Nat) (argument : domain.family.obj initialPoint) :
    ¬ ((historyClassifier label).app initialPoint initialParameter).holds (current domain.family initialPoint argument) := by
  rw [initial_history_predicate]
  exact startsWith_has_no_present_truth label argument

theorem actual_naturality (label other : Nat) :
    (family domain.family).map (extensionArrow other)
        ((historyClassifier label).app initialPoint initialParameter) =
      (historyClassifier label).app (nextPoint other) (parameters.map (extensionArrow other) initialParameter) :=
  (historyClassifier label).naturality (extensionArrow other) initialParameter

/-- The operational base action identifies the labels; the actual context
arrows still retain them, so they can be used at one common later object. -/
def commonArrow (label : Nat) : initialPoint ⟶ nextPoint 0 :=
  ⟨extension label, by
    have first := PowerClassPresheafDescent.classFace_map_class
      model.sourceFace model.classFace model.observation (extension label) oldRaw.2
    have second := PowerClassPresheafDescent.classFace_map_class
      model.sourceFace model.classFace model.observation (extension 0) oldRaw.2
    exact first.trans ((congrArg (PowerClassFamilyDescent.classOf (model.observation.app next))
      (parallel_actions_equal label 0 oldRaw.2)).trans second.symm)⟩

def laterParameter (label : Nat) : parameters.obj (nextPoint 0) :=
  parameters.map (commonArrow label) initialParameter

theorem laterParameter_injective : Function.Injective laterParameter := by
  intro first second same
  have paths := congrArg (fun receipt : parameters.obj (nextPoint 0) => receipt.2.val.unop.unop.val) same
  change [first] = [second] at paths
  exact List.singleton_injective paths

/-- New receipts generated at the later object cannot come from an earlier
receipt: restriction preserves the generator, and no arrow goes back to
the initial length-zero world. -/
theorem parameter_restriction_not_surjective (label : Nat) :
    ¬ Function.Surjective (parameters.map (extensionArrow label)) := by
  intro onto
  obtain ⟨receipt, same⟩ := onto (seed (nextPoint label))
  have generators := congrArg Sigma.fst same
  change receipt.1 = nextPoint label at generators
  have generatorLength := congrArg (fun point : actualContext.base.Elements => point.1.unop.unop.length) generators
  change receipt.1.1.unop.unop.length = 1 at generatorLength
  have bound := receipt.2.val.unop.unop.property
  change receipt.1.1.unop.unop.length + receipt.2.val.unop.unop.val.length = 0 at bound
  omega

def materialHistory (label : Nat) : HSet :=
  (powers.model initialPoint).value ((historyClassifier label).app initialPoint initialParameter)

theorem materialHistory_eq (label : Nat) : materialHistory label = materialPredicate label := by
  exact congrArg (powers.model initialPoint).value (initial_history_predicate label)

theorem materialHistory_injective : Function.Injective materialHistory := by
  intro first second same
  exact materialPredicate_injective ((materialHistory_eq first).symm.trans (same.trans (materialHistory_eq second)))

theorem actual_material_future_truth (label other : Nat) :
    (domain.futureCoding arrowCoding initialPoint).reading (futureArgument other) ∈ materialHistory label ↔
      label = other := by
  rw [materialHistory_eq]
  exact material_future_truth label other

theorem materialHistory_present_empty (label : Nat) :
    ContextualPowerFamilies.presentPart domain arrowCoding initialPoint
      ((historyClassifier label).app initialPoint initialParameter) = ∅ := by
  rw [initial_history_predicate]
  exact present_part_empty label

/-- Even with one retained parameter, its present subset at one point cannot
recover the full material value of every natural classifier. -/
theorem no_present_only_parameter_classifier :
    ¬ ∃ recovery : HSet → HSet, ∀ operation : NaturalHom parameters powers.family,
      recovery (ContextualPowerFamilies.presentPart domain arrowCoding initialPoint
          (operation.app initialPoint initialParameter)) =
        (powers.model initialPoint).value (operation.app initialPoint initialParameter) := by
  rintro ⟨recovery, inverse⟩
  have first := inverse (historyClassifier 0)
  have second := inverse (historyClassifier 1)
  rw [materialHistory_present_empty] at first second
  have same : materialHistory 0 = materialHistory 1 := first.symm.trans second
  exact Nat.zero_ne_one (materialHistory_injective same)

def selectFirstParameter : NaturalHom (product parameters parameters) parameters :=
  firstProjection parameters parameters

theorem selectFirstParameter_not_injective :
    ¬ Function.Injective (selectFirstParameter.app (nextPoint 0)) := by
  intro injective
  have pairs := injective (a₁ := (laterParameter 0, laterParameter 0))
    (a₂ := (laterParameter 0, laterParameter 1)) rfl
  exact Nat.zero_ne_one (laterParameter_injective (congrArg Prod.snd pairs))

theorem actual_parameter_substitution (label : Nat) :
    classifier (product parameters parameters) domain.family
        (parameterSubstitution parameters domain.family selectFirstParameter (historyPredicate label)) =
      selectFirstParameter.comp (historyClassifier label) :=
  classifier_parameter_substitution parameters domain.family selectFirstParameter (historyPredicate label)

/-- A second interpretation uses actual material parameters and arguments;
the diagonal stable relation becomes a natural classifier with exact future
membership in the constructed contextual power carrier. -/
def diagonalPredicate : StablePredicate (product domain.family domain.family) where
  holds point := point.2.1 = point.2.2
  closed {first second} step equal := by
    have left := congrArg Prod.fst step.2
    have right := congrArg Prod.snd step.2
    exact left.symm.trans ((congrArg (domain.family.map step.1) equal).trans right)

theorem diagonal_material_future (point : actualContext.base.Elements)
    (member : {value : HSet // value ∈ (domain.model point).carrier})
    (argument : Arguments domain.family point) :
    (domain.futureCoding arrowCoding point).reading argument ∈
        (powers.model point).value ((classifier domain.family domain.family diagonalPredicate).app point
          ((domain.model point).decode member)) ↔
      domain.family.map argument.1.2 ((domain.model point).decode member) = argument.2 :=
  material_member_parameter_future domain arrowCoding domain diagonalPredicate point member argument

theorem actual_domain_varies :
    (domain.model (observedPoint model worldCoding oldRaw)).value
        (positiveSection.val (observedPoint model worldCoding oldRaw)) ≠
      (domain.model (observedPoint model worldCoding newRaw)).value
        (positiveSection.val (observedPoint model worldCoding newRaw)) := section_values_differ

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerClassifierControls
