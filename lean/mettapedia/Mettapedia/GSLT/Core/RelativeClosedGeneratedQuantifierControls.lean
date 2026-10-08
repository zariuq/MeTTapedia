import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierNativeMeaning
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageControls

/-!
# Actual quantification along a generated structural operator

The route is the independently generated constructor-image name, an arrow
between predicate function objects. The new quantifiers therefore act on
predicates of complete functions. Their actual quotient images retain the
whole supplied function and changing parameter. Both quantifier readouts
and an independently constant-truth separator are checked here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open ElementaryTypePredicateReadout
open PositionedRewritePredicatePower (name family_name)

abbrev source := RelativeClosedStructuralImageControls.source
abbrev selection := RelativeClosedStructuralImageControls.selected
abbrev constructors := RelativeClosedStructuralImageControls.constructors
abbrev base := RelativeClosedStructuralImageControls.base
abbrev original := RelativeClosedStructuralImagePresentation.signature source selection constructors
abbrev meanings := RelativeClosedStructuralImageNativeMeaning.meanings doctrine source selection constructors base
abbrev old := RelativeClosedStructuralImageNativeMeaning.realized doctrine source selection constructors base

def retainedLogical := (RelativeClosedStructuralImagePresentation.logicalInclusion source selection).compose
  (RelativeClosedStructuralImagePresentation.inclusion source selection constructors)

def language : RelativeClosedGeneratedQuantifier.PredicateSyntax original where
  proposition := retainedLogical.object RelativeClosedPredicateLogic.omega
  conjunction := retainedLogical.rawArrow RelativeClosedPredicateLogic.conjunctionRaw

theorem proposition_read : RawInterpretation.ObjectReads meanings language.proposition (operations doctrine).proposition :=
  (retainedLogical.evaluateObject_precompose meanings RelativeClosedPredicateLogic.omega.code).trans rfl

theorem conjunction_read : RawInterpretation.Reads meanings language.conjunction (operations doctrine).conjunction :=
  (retainedLogical.evaluateArrow_precompose meanings RelativeClosedPredicateLogic.conjunctionRaw.code).trans rfl

def structuralRoute : RelativeClosedGeneratedQuantifier.Route original where
  source := RelativeClosedStructuralImageNativeMeaning.rawSource source selection constructors (ULift.up false)
  target := RelativeClosedStructuralImageNativeMeaning.rawTarget source selection constructors (ULift.up false)
  arrow := RelativeClosedStructuralImagePresentation.namedRaw source selection constructors (ULift.up false)

abbrev inputSpace := power doctrine (Nat × Nat)
abbrev outputSpace := power doctrine Nat
abbrev originalImage : inputSpace ⟶ outputSpace := RelativeClosedStructuralImageControls.image

theorem structural_route_read : RawInterpretation.Reads meanings structuralRoute.arrow originalImage :=
  (RelativeClosedStructuralImageNativeMeaning.named_read doctrine source selection constructors base (ULift.up false)).trans
    (congrArg (fun arrow : inputSpace ⟶ outputSpace => some (⟨inputSpace, outputSpace, arrow⟩ :
      RelativeClosedSyntax.Interpretation.ArrowValue Type))
      (RelativeClosedStructuralImageNativeMeaning.imageAt_complete doctrine source selection constructors base (ULift.up false)).symm)

def existentialImage : power doctrine inputSpace ⟶ power doctrine outputSpace :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead original language meanings old doctrine
    proposition_read conjunction_read .existential structuralRoute originalImage structural_route_read

def universalImage : power doctrine inputSpace ⟶ power doctrine outputSpace :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead original language meanings old doctrine
    proposition_read conjunction_read .universal structuralRoute originalImage structural_route_read

theorem existential_image_complete : existentialImage = existsOperation doctrine originalImage :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead_complete original language meanings old doctrine
    proposition_read conjunction_read .existential structuralRoute originalImage structural_route_read

theorem universal_image_complete : universalImage = forallOperation doctrine originalImage :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead_complete original language meanings old doctrine
    proposition_read conjunction_read .universal structuralRoute originalImage structural_route_read

theorem the_quantified_route_is_an_authored_generated_name :
    structuralRoute.arrow.code = .name (Sum.inr (ULift.up false)) := rfl

theorem the_quantified_route_is_not_a_raw_base_arrow
    {before after : source.closed.Obj} (arrow : before ⟶ after) :
    structuralRoute.arrow.code ≠ .base arrow := by
  intro impossible
  cases impossible

def supplied (first second : Nat → Nat) : Nat ⟶ inputSpace :=
  RelativeClosedStructuralImageControls.inputs first second

def completeInput (first second : Nat → Nat) : Subobject (inputSpace ⊗ Nat) :=
  fromSet {whole | whole.1 = supplied first second whole.2}

def completeInputName (first second : Nat → Nat) : Nat ⟶ power doctrine inputSpace :=
  name doctrine (completeInput first second)

def existsOutput (first second : Nat → Nat) : Subobject (outputSpace ⊗ Nat) :=
  family doctrine (completeInputName first second ≫ existentialImage)

def forallOutput (first second : Nat → Nat) : Subobject (outputSpace ⊗ Nat) :=
  family doctrine (completeInputName first second ≫ universalImage)

theorem exists_output_read (first second : Nat → Nat) (result : outputSpace) (parameter : Nat) :
    Contains (existsOutput first second) (result, parameter) ↔
      result = originalImage (supplied first second parameter) := by
  have full : existsOutput first second =
      doctrine.existsAlong (originalImage ▷ Nat) (completeInput first second) := by
    exact (congrArg (fun operation => family doctrine (completeInputName first second ≫ operation))
      existential_image_complete).trans
      ((exists_supplied doctrine originalImage (completeInputName first second)).trans
        (congrArg (doctrine.existsAlong (originalImage ▷ Nat)) (family_name doctrine (completeInput first second))))
  rw [full, contains_exists]
  constructor
  · rintro ⟨⟨candidate, oldParameter⟩, admitted, reaches⟩
    change (originalImage candidate, oldParameter) = (result, parameter) at reaches
    obtain ⟨answer, unchanged⟩ := Prod.mk.inj reaches
    subst oldParameter
    have candidateRead := (contains_fromSet _ _).mp admitted
    exact answer.symm.trans (congrArg originalImage candidateRead)
  · intro answer
    refine ⟨(supplied first second parameter, parameter), (contains_fromSet _ _).mpr rfl, ?_⟩
    change (originalImage (supplied first second parameter), parameter) = (result, parameter)
    exact congrArg (fun value => (value, parameter)) answer.symm

theorem forall_output_read (first second : Nat → Nat) (result : outputSpace) (parameter : Nat) :
    Contains (forallOutput first second) (result, parameter) ↔
      ∀ candidate : inputSpace, originalImage candidate = result →
        candidate = supplied first second parameter := by
  have full : forallOutput first second =
      doctrine.forallAlong (originalImage ▷ Nat) (completeInput first second) := by
    exact (congrArg (fun operation => family doctrine (completeInputName first second ≫ operation))
      universal_image_complete).trans
      ((forall_supplied doctrine originalImage (completeInputName first second)).trans
        (congrArg (doctrine.forallAlong (originalImage ▷ Nat)) (family_name doctrine (completeInput first second))))
  rw [full, contains_forall]
  constructor
  · intro held candidate reaches
    have admitted := held (candidate, parameter) (congrArg (fun value => (value, parameter)) reaches)
    exact (contains_fromSet {whole : inputSpace ⊗ Nat | whole.1 = supplied first second whole.2}
      (candidate, parameter)).mp admitted
  · intro held ⟨candidate, oldParameter⟩ reaches
    change (originalImage candidate, oldParameter) = (result, parameter) at reaches
    obtain ⟨answer, unchanged⟩ := Prod.mk.inj reaches
    subst oldParameter
    exact (contains_fromSet _ _).mpr (held candidate answer)

theorem the_actual_generated_existential_retains_the_whole_function (first second : Nat → Nat) (parameter : Nat) :
    Contains (existsOutput first second) (originalImage (supplied first second parameter), parameter) :=
  (exists_output_read first second _ parameter).mpr rfl

theorem point_input_read (first second : Nat → Nat) (left right parameter : Nat) :
    Contains (family doctrine (point parameter ≫ supplied first second)) ((left, right), PUnit.unit) ↔
      left = first parameter ∧ right = second parameter := by
  rw [family_substitution, contains_reindex]
  exact RelativeClosedStructuralImageControls.complete_input_read first second left right parameter

theorem two_complete_inputs_are_distinct :
    supplied (fun _ => 2) (fun _ => 0) 0 ≠ supplied (fun _ => 0) (fun _ => 1) 0 := by
  intro same
  have arrowsEqual : point 0 ≫ supplied (fun _ => 2) (fun _ => 0) =
      point 0 ≫ supplied (fun _ => 0) (fun _ => 1) := by
    ext suppliedUnit
    exact same
  have firstRead := (point_input_read (fun _ => 2) (fun _ => 0) 2 0 0).mpr ⟨rfl, rfl⟩
  have transported := (congrArg (fun arrow : PUnit ⟶ inputSpace =>
    Contains (family doctrine arrow) ((2, 0), PUnit.unit)) arrowsEqual).mp firstRead
  have impossible := (point_input_read (fun _ => 0) (fun _ => 1) 2 0 0).mp transported
  omega

theorem the_structural_image_has_a_complete_input_collision :
    originalImage (supplied (fun _ => 2) (fun _ => 0) 0) =
      originalImage (supplied (fun _ => 0) (fun _ => 1) 0) := by
  have familiesEqual : family doctrine (supplied (fun _ => 2) (fun _ => 0) ≫ originalImage) =
      family doctrine (supplied (fun _ => 0) (fun _ => 1) ≫ originalImage) := by
    apply le_antisymm
    · apply (le_iff_contains _ _).mpr
      intro ⟨result, parameter⟩ held
      exact (RelativeClosedStructuralImageControls.output_read (fun _ => 0) (fun _ => 1) result parameter).mpr
        ((RelativeClosedStructuralImageControls.output_read (fun _ => 2) (fun _ => 0) result parameter).mp held)
    · apply (le_iff_contains _ _).mpr
      intro ⟨result, parameter⟩ held
      exact (RelativeClosedStructuralImageControls.output_read (fun _ => 2) (fun _ => 0) result parameter).mpr
        ((RelativeClosedStructuralImageControls.output_read (fun _ => 0) (fun _ => 1) result parameter).mp held)
  have arrowsEqual := family_injective doctrine familiesEqual
  exact congrArg (fun arrow : Nat ⟶ outputSpace => arrow 0) arrowsEqual

theorem actual_existential_and_universal_differ_on_the_collision :
    Contains (existsOutput (fun _ => 2) (fun _ => 0))
        (originalImage (supplied (fun _ => 2) (fun _ => 0) 0), 0) ∧
      ¬ Contains (forallOutput (fun _ => 2) (fun _ => 0))
        (originalImage (supplied (fun _ => 2) (fun _ => 0) 0), 0) := by
  refine ⟨the_actual_generated_existential_retains_the_whole_function _ _ 0, ?_⟩
  intro held
  have allCandidates := (forall_output_read (fun _ => 2) (fun _ => 0) _ 0).mp held
  exact two_complete_inputs_are_distinct
    (allCandidates (supplied (fun _ => 0) (fun _ => 1) 0)
      the_structural_image_has_a_complete_input_collision.symm).symm

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem future_retains_the_complete_chosen_input (first second : Nat → Nat)
    (result : outputSpace) (parameter : Nat) :
    Contains (family doctrine ((future ≫ completeInputName first second) ≫ existentialImage)) (result, parameter) ↔
      result = originalImage (supplied first second (parameter + 1)) := by
  have complete := (congrArg (family doctrine) (Category.assoc future (completeInputName first second) existentialImage)).trans
    (family_substitution doctrine future (completeInputName first second ≫ existentialImage))
  rw [complete, contains_reindex]
  exact exists_output_read first second result (parameter + 1)

def emptyInput : Subobject (inputSpace ⊗ Nat) := fromSet ∅
def emptyInputName : Nat ⟶ power doctrine inputSpace := name doctrine emptyInput

theorem actual_generated_existential_rejects_every_empty_input (result : outputSpace) (parameter : Nat) :
    ¬ Contains (family doctrine (emptyInputName ≫ existentialImage)) (result, parameter) := by
  intro held
  have complete := (congrArg (fun operation => family doctrine (emptyInputName ≫ operation)) existential_image_complete).trans
    ((exists_supplied doctrine originalImage emptyInputName).trans
      (congrArg (doctrine.existsAlong (originalImage ▷ Nat)) (family_name doctrine emptyInput)))
  have admitted := (congrArg (fun predicate : Subobject (outputSpace ⊗ Nat) =>
    Contains predicate (result, parameter)) complete).mp held
  obtain ⟨candidate, impossible, _⟩ := (contains_exists _ _ _).mp admitted
  exact (contains_fromSet ∅ candidate).mp impossible

def wrongConstantTruth : power doctrine inputSpace ⟶ power doctrine outputSpace :=
  name doctrine (⊤ : Subobject (outputSpace ⊗ power doctrine inputSpace))

theorem wrong_constant_truth_accepts_the_independently_empty_input (result : outputSpace) (parameter : Nat) :
    Contains (family doctrine (emptyInputName ≫ wrongConstantTruth)) (result, parameter) := by
  have complete : family doctrine (emptyInputName ≫ wrongConstantTruth) = ⊤ :=
    (family_substitution doctrine emptyInputName wrongConstantTruth).trans
      ((congrArg (doctrine.reindex (outputSpace ◁ emptyInputName))
        (family_name doctrine (⊤ : Subobject (outputSpace ⊗ power doctrine inputSpace)))).trans (doctrine.reindex_top _))
  exact (congrArg (fun predicate : Subobject (outputSpace ⊗ Nat) => Contains predicate (result, parameter)) complete).mpr
    (contains_top _)

theorem a_constant_truth_arrow_cannot_be_the_actual_generated_quantifier : wrongConstantTruth ≠ existentialImage := by
  intro same
  let suppliedResult : outputSpace := originalImage (supplied (fun _ => 2) (fun _ => 3) 0)
  exact actual_generated_existential_rejects_every_empty_input suppliedResult 0
    ((congrArg (fun operation : power doctrine inputSpace ⟶ power doctrine outputSpace =>
      Contains (family doctrine (emptyInputName ≫ operation)) (suppliedResult, 0)) same).mp
      (wrong_constant_truth_accepts_the_independently_empty_input suppliedResult 0))

end Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierControls
