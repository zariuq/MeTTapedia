import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerClassifierControls

/-!
# Larger, varying controls for covered parameterized classification

The argument family is the actual cyclic material input, raised to a larger
host universe. Parameters retain both an actual free contextual receipt and
an arbitrary ambient hyperset. Thus the parameter object is genuinely larger,
and its receipt component varies on the infinite path context. Authored
original-bound enumerations construct its history-sensitive classifiers.

The full ambient hyperset relation cannot satisfy the cover condition:
one present parameter would supply a forbidden small surjection onto all
hypersets. Nevertheless the ambient diagonal has constructed singleton
covers. Duplicate singleton receipts also prove that a cover does not
supply an inverse for its enumeration. Present-only recovery fails for the
actual natural, covered history classifiers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifierControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open CoveredFuturePowerFamilies CoveredFuturePowerClassifier
open ContextualPowerFamiliesControls
open FuturePowerClassifierControls
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

def raised (F : actualContext.base.Elements ⥤ Type) : actualContext.base.Elements ⥤ Type 1 where
  obj point := ULift.{1} (F.obj point)
  map step := TypeCat.ofHom (fun value => ⟨F.map step value.down⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (F.map_id_apply point value.down)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (F.map_comp_apply earlier later value.down)

def ambient : actualContext.base.Elements ⥤ Type 1 where
  obj _ := HSet.{0}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev wideParameters := product (raised parameters) ambient
abbrev wideArguments := raised domain.family

def wideInitialParameter : wideParameters.obj initialPoint :=
  (⟨initialParameter⟩, HSet.quineAtom)

def historyPredicate (label : Nat) : StablePredicate (product wideParameters wideArguments) where
  holds point := ∃ rest, point.2.1.1.down.2.val.unop.unop.val = label :: rest
  closed {first second} step available := by
    obtain ⟨rest, starts⟩ := available
    have parameterEq : wideParameters.map step.1 first.2.1 = second.2.1 := congrArg Prod.fst step.2
    have triangle := congrArg
      (fun parameter : wideParameters.obj second.1 => parameter.1.down.2.val.unop.unop.val) parameterEq
    change first.2.1.1.down.2.val.unop.unop.val ++ step.1.val.unop.unop.val =
      second.2.1.1.down.2.val.unop.unop.val at triangle
    refine ⟨rest ++ step.1.val.unop.unop.val, ?_⟩
    rw [← triangle, starts]
    rfl

/-- Every admitted raised argument has an actual small receipt. The
history condition restricts the original small argument carrier; no
enumeration is selected from existence. -/
def historyEnumeration (label : Nat) (point : actualContext.base.Elements)
    (parameter : wideParameters.obj point) :
    RelationEnumeration wideParameters wideArguments (historyPredicate label) point parameter where
  Carrier future := {argument : domain.family.obj future.1 //
    ∃ rest, (parameter.1.down.2 ≫ future.2).val.unop.unop.val = label :: rest}
  value _ code := ⟨code.val⟩
  covered _ argument := by
    constructor
    · intro holds
      exact ⟨⟨argument.down, holds⟩, ULift.up_down argument⟩
    · rintro ⟨code, _same⟩
      exact code.property

def historyRelation (label : Nat) : CoveredRelation wideParameters wideArguments where
  predicate := historyPredicate label
  covered point parameter := ⟨historyEnumeration label point parameter⟩

def historyClassifier (label : Nat) : NaturalHom wideParameters (family wideArguments) :=
  classifier wideParameters wideArguments (historyRelation label)

def wideFuture (label : Nat) : Arguments wideArguments initialPoint :=
  ⟨(futureArgument label).1, ⟨(futureArgument label).2⟩⟩

theorem history_future_truth (label other : Nat) :
    ((historyClassifier label).app initialPoint wideInitialParameter).val.holds (wideFuture other) ↔
      label = other := by
  change (∃ rest, (𝟙 initialPoint ≫ (futureArgument other).1.2).val.unop.unop.val = label :: rest) ↔ _
  rw [Category.id_comp]
  exact startsWith_future_iff label other

theorem history_has_no_present_truth (label : Nat) (argument : wideArguments.obj initialPoint) :
    ¬ ((historyClassifier label).app initialPoint wideInitialParameter).val.holds
      (current wideArguments initialPoint argument) := by
  change ¬ ∃ rest, (𝟙 initialPoint ≫ 𝟙 initialPoint).val.unop.unop.val = label :: rest
  rintro ⟨rest, impossible⟩
  change [] = label :: rest at impossible
  cases impossible

theorem actual_wide_naturality (label other : Nat) :
    (family wideArguments).map (extensionArrow other)
        ((historyClassifier label).app initialPoint wideInitialParameter) =
      (historyClassifier label).app (nextPoint other)
        (wideParameters.map (extensionArrow other) wideInitialParameter) :=
  (historyClassifier label).naturality (extensionArrow other) wideInitialParameter

def wideLaterParameter (label : Nat) : wideParameters.obj (nextPoint 0) :=
  (⟨laterParameter label⟩, HSet.quineAtom)

theorem wideLaterParameter_injective : Function.Injective wideLaterParameter := by
  intro first second same
  exact laterParameter_injective (congrArg (fun parameter : wideParameters.obj (nextPoint 0) =>
    parameter.1.down) same)

theorem wide_parameter_restriction_not_surjective (label : Nat) :
    ¬ Function.Surjective (wideParameters.map (extensionArrow label)) := by
  intro onto
  apply parameter_restriction_not_surjective label
  intro receipt
  obtain ⟨parameter, same⟩ := onto (⟨receipt⟩, HSet.quineAtom)
  exact ⟨parameter.1.down, congrArg (fun value : wideParameters.obj (nextPoint label) => value.1.down) same⟩

/-- The widened parameter fibre itself has no original-bound cover: its
second coordinate ranges over every actual bare hyperset. -/
theorem wideParameters_has_no_small_cover {I : Type} (reading : I → wideParameters.obj initialPoint) :
    ¬ Function.Surjective reading := by
  intro onto
  apply CoveredFuturePowerControls.hset_has_no_small_cover (fun index => (reading index).2)
  intro value
  obtain ⟨index, same⟩ := onto (⟨initialParameter⟩, value)
  exact ⟨index, congrArg Prod.snd same⟩

def cyclicParameterPredicate (label : Nat) : StablePredicate (product wideParameters wideArguments) where
  holds point := (historyPredicate label).holds point ∧ point.2.1.2 = HSet.quineAtom
  closed {first second} step available := by
    have parameterEq := congrArg Prod.fst step.2
    have ambientEq : first.2.1.2 = second.2.1.2 := congrArg Prod.snd parameterEq
    exact ⟨(historyPredicate label).closed step available.1, ambientEq.symm.trans available.2⟩

/-- The cover may depend propositionally on the arbitrary larger parameter
while its actual receipt carrier stays in the original small universe. -/
def cyclicParameterEnumeration (label : Nat) (point : actualContext.base.Elements)
    (parameter : wideParameters.obj point) :
    RelationEnumeration wideParameters wideArguments (cyclicParameterPredicate label) point parameter where
  Carrier future := {argument : domain.family.obj future.1 //
    (∃ rest, (parameter.1.down.2 ≫ future.2).val.unop.unop.val = label :: rest) ∧
      parameter.2 = HSet.quineAtom}
  value _ code := ⟨code.val⟩
  covered _ argument := by
    constructor
    · intro holds
      exact ⟨⟨argument.down, holds⟩, ULift.up_down argument⟩
    · rintro ⟨code, _same⟩
      exact code.property

def cyclicParameterRelation (label : Nat) : CoveredRelation wideParameters wideArguments where
  predicate := cyclicParameterPredicate label
  covered point parameter := ⟨cyclicParameterEnumeration label point parameter⟩

def cyclicParameterClassifier (label : Nat) : NaturalHom wideParameters (family wideArguments) :=
  classifier wideParameters wideArguments (cyclicParameterRelation label)

def emptyInitialParameter : wideParameters.obj initialPoint := (⟨initialParameter⟩, (∅ : HSet.{0}))

/-- The larger parameter coordinate affects the natural classifier: its
empty and cyclic values produce different future truth. -/
theorem actual_ambient_parameter_distinguished :
    ((cyclicParameterClassifier 0).app initialPoint wideInitialParameter).val.holds (wideFuture 0) ∧
      ¬ ((cyclicParameterClassifier 0).app initialPoint emptyInitialParameter).val.holds (wideFuture 0) := by
  constructor
  · exact ⟨(history_future_truth 0 0).mpr rfl, rfl⟩
  · intro available
    exact HSet.empty_ne_quineAtom available.2

theorem historyClassifier_injective : Function.Injective historyClassifier := by
  intro first second same
  have firstTruth := (history_future_truth first first).mpr rfl
  rw [same] at firstTruth
  exact ((history_future_truth second first).mp firstTruth).symm

/-- These are compatible natural maps into the covered power family.
Their equal empty present predicates still do not recover their distinct
full future values. -/
theorem no_present_only_covered_classifier :
    ¬ ∃ recovery : (wideArguments.obj initialPoint → Prop) → Power wideArguments initialPoint,
      ∀ operation : NaturalHom wideParameters (family wideArguments),
        recovery (fun argument => (operation.app initialPoint wideInitialParameter).val.holds
          (current wideArguments initialPoint argument)) = operation.app initialPoint wideInitialParameter := by
  rintro ⟨recovery, inverse⟩
  have currentZero : (fun argument => ((historyClassifier 0).app initialPoint wideInitialParameter).val.holds
      (current wideArguments initialPoint argument)) = fun _ => False := by
    funext argument
    exact propext ⟨history_has_no_present_truth 0 argument, False.elim⟩
  have currentOne : (fun argument => ((historyClassifier 1).app initialPoint wideInitialParameter).val.holds
      (current wideArguments initialPoint argument)) = fun _ => False := by
    funext argument
    exact propext ⟨history_has_no_present_truth 1 argument, False.elim⟩
  have first := inverse (historyClassifier 0)
  have second := inverse (historyClassifier 1)
  rw [currentZero] at first
  rw [currentOne] at second
  have same := first.symm.trans second
  have truth := (history_future_truth 0 0).mpr rfl
  rw [same] at truth
  exact Nat.zero_ne_one ((history_future_truth 1 0).mp truth).symm

def selectFirstParameter : NaturalHom (product wideParameters wideParameters) wideParameters :=
  firstProjection wideParameters wideParameters

theorem selectFirstParameter_not_injective :
    ¬ Function.Injective (selectFirstParameter.app (nextPoint 0)) := by
  intro injective
  have pairs := injective (a₁ := (wideLaterParameter 0, wideLaterParameter 0))
    (a₂ := (wideLaterParameter 0, wideLaterParameter 1)) rfl
  exact Nat.zero_ne_one (wideLaterParameter_injective (congrArg Prod.snd pairs))

theorem actual_parameter_substitution (label : Nat) :
    classifier (product wideParameters wideParameters) wideArguments
        (parameterSubstitution wideParameters wideArguments selectFirstParameter (historyRelation label)) =
      selectFirstParameter.comp (historyClassifier label) :=
  classifier_parameter_substitution wideParameters wideArguments selectFirstParameter (historyRelation label)

def fullAmbient : StablePredicate (product wideParameters ambient) where
  holds _ := True
  closed _ _ := trivial

/-- A genuine larger argument object prevents dropping the fixed-bound
cover condition from the parameterized universal correspondence. -/
theorem forget_not_surjective : ¬ Function.Surjective (CoveredFuturePowerClassifier.forget wideParameters ambient) := by
  intro onto
  obtain ⟨relation, same⟩ := onto fullAmbient
  have full : ∀ argument : ambient.obj initialPoint,
      relation.predicate.holds ⟨initialPoint, (wideInitialParameter, argument)⟩ := by
    intro argument
    change (CoveredFuturePowerClassifier.forget wideParameters ambient relation).holds ⟨initialPoint, (wideInitialParameter, argument)⟩
    rw [same]
    trivial
  obtain ⟨Carrier, value, covers⟩ :=
    small_surjection_of_full_relation wideParameters ambient relation initialPoint wideInitialParameter full
  exact CoveredFuturePowerControls.hset_has_no_small_cover value covers

theorem no_full_ambient_classifier :
    ¬ ∃ operation : NaturalHom wideParameters (family ambient), ∀ argument : ambient.obj initialPoint,
      (operation.app initialPoint wideInitialParameter).val.holds (current ambient initialPoint argument) := by
  rintro ⟨operation, full⟩
  obtain ⟨Carrier, value, covers⟩ := small_surjection_of_full_relation wideParameters ambient
    (classifiedRelation wideParameters ambient operation) initialPoint wideInitialParameter full
  exact CoveredFuturePowerControls.hset_has_no_small_cover value covers

/-- The ambient diagonal is nevertheless small-covered, with one receipt
at every future for each retained ambient hyperset. -/
def ambientDiagonal : CoveredRelation ambient ambient :=
  classifiedRelation ambient ambient (CoveredFuturePowerFunctor.unitHom ambient)

theorem ambient_diagonal_truth (point : actualContext.base.Elements) (first second : HSet.{0}) :
    ambientDiagonal.predicate.holds ⟨point, (first, second)⟩ ↔ first = second :=
  CoveredFuturePowerFunctor.singleton_current ambient point first second

theorem ambient_membership_classifier :
    classifier (family ambient) ambient (membershipRelation ambient) = identityHom (family ambient) :=
  membership_classifier ambient

def duplicateEnumeration (point : actualContext.base.Elements) :
    Enumeration (CoveredFuturePowerFunctor.singletonPower ambient point HSet.quineAtom).val where
  Carrier _ := Bool
  value _ _ := HSet.quineAtom
  covered _ _ := ⟨fun same => ⟨false, same⟩, fun ⟨_, same⟩ => same⟩

theorem duplicate_cover_has_no_left_inverse (point : actualContext.base.Elements) :
    ¬ ∃ inverse : HSet.{0} → Bool,
      Function.LeftInverse inverse ((duplicateEnumeration point).value ⟨point, 𝟙 point⟩) := by
  rintro ⟨inverse, leftInverse⟩
  have first := leftInverse false
  have second := leftInverse true
  exact Bool.false_ne_true (first.symm.trans second)

/-- The power value retains the predicate and cover existence, not the
number or identity of the authored receipts. -/
theorem duplicate_cover_same_power (point : actualContext.base.Elements) :
    (⟨(CoveredFuturePowerFunctor.singletonPower ambient point HSet.quineAtom).val,
      ⟨duplicateEnumeration point⟩⟩ : Power ambient point) =
        CoveredFuturePowerFunctor.singletonPower ambient point HSet.quineAtom :=
  Subtype.ext rfl

theorem actual_argument_material_variation :
    (domain.model (Mettapedia.GSLT.ObservedGeneratedModel.observedPoint model worldCoding oldRaw)).value
        (positiveSection.val (Mettapedia.GSLT.ObservedGeneratedModel.observedPoint model worldCoding oldRaw)) ≠
      (domain.model (Mettapedia.GSLT.ObservedGeneratedModel.observedPoint model worldCoding newRaw)).value
        (positiveSection.val (Mettapedia.GSLT.ObservedGeneratedModel.observedPoint model worldCoding newRaw)) :=
  actual_domain_varies

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifierControls
