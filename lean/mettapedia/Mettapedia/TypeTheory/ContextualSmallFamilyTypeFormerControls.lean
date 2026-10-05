import Mettapedia.TypeTheory.ContextualSmallFamilyConeComparison
import Mettapedia.TypeTheory.ContextualSmallFamilyComprehension
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverseControls

/-!
# Infinite nonconstant controls for small contextual type formers

The parameters include arbitrary bare hypersets, while arguments grow as
finite initial segments at every natural-number stage. Result fibres
depend on the argument position. Two actual compatible functions agree
on all present arguments and differ on newly available future arguments.

A second result family is inhabited on every present argument and empty
on a genuine future argument, so its contextual dependent product is
empty. Noninjective parameter substitution retains the original parameter
coordinates and the selected result values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerControls

open CategoryTheory ContextualWitnessCover
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence
open ContextualSmallFamilyUniverseControls
open MaterialSets.Hypersets
open PowerClassPresheafBaseChange

def smallUnit {E : Type 1} [Category.{0} E] : E ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def positionResults : cyclicSmall.Elements ⥤ Type where
  obj argument := {result : Nat // result ≤ argument.2.1.val}
  map {first second} step := TypeCat.ofHom fun result => ⟨result.val, by
    have position : first.2.1.val = second.2.1.val :=
      congrArg (fun member : cyclicSmall.obj second.1 => member.1.val) step.2
    rw [← position]
    exact result.property⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro result
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro result
    exact Subtype.ext rfl

def greatestResult : NatTrans (overArguments cyclicSmall smallUnit) positionResults where
  app argument := TypeCat.ofHom fun _ => ⟨argument.2.1.val, Nat.le_refl _⟩
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro _
    exact Subtype.ext (congrArg (fun member : cyclicSmall.obj second.1 => member.1.val) step.2).symm

def zeroResult : NatTrans (overArguments cyclicSmall smallUnit) positionResults where
  app _ := TypeCat.ofHom fun _ => ⟨0, Nat.zero_le _⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    exact Subtype.ext rfl

def greatestFunctions : NatTrans smallUnit (pi cyclicSmall positionResults) :=
  piCurry cyclicSmall positionResults greatestResult

def zeroFunctions : NatTrans smallUnit (pi cyclicSmall positionResults) :=
  piCurry cyclicSmall positionResults zeroResult

def greatestSection : (pi cyclicSmall positionResults).sections :=
  ⟨fun point => greatestFunctions.app point PUnit.unit, by
    intro first second step
    exact (congrArg (fun map => map PUnit.unit) (greatestFunctions.naturality step)).symm⟩

def zeroSection : (pi cyclicSmall positionResults).sections :=
  ⟨fun point => zeroFunctions.app point PUnit.unit, by
    intro first second step
    exact (congrArg (fun map => map PUnit.unit) (zeroFunctions.naturality step)).symm⟩

theorem greatest_evaluation (point : parameters.Elements) (argument : cyclicSmall.obj point) :
    (evaluateValue cyclicSmall positionResults point (greatestSection.val point) argument).val = argument.1.val := by
  exact congrArg Subtype.val (congrArg (fun operation : NatTrans (overArguments cyclicSmall smallUnit) positionResults =>
    operation.app ⟨point, argument⟩ PUnit.unit) (pi_uncurry_curry cyclicSmall positionResults greatestResult))

theorem zero_evaluation (point : parameters.Elements) (argument : cyclicSmall.obj point) :
    (evaluateValue cyclicSmall positionResults point (zeroSection.val point) argument).val = 0 := by
  exact congrArg Subtype.val (congrArg (fun operation : NatTrans (overArguments cyclicSmall smallUnit) positionResults =>
    operation.app ⟨point, argument⟩ PUnit.unit) (pi_uncurry_curry cyclicSmall positionResults zeroResult))

def laterArgument (stage : Nat) :
    (futureDomain cyclicSmall (parameter 0 HSet.quineAtom)).Elements :=
  ⟨⟨stage + 1, homOfLE (Nat.zero_le _)⟩, newCyclicMember stage⟩

theorem greatest_future_value (stage : Nat) :
    ((greatestSection.val (parameter 0 HSet.quineAtom)).val (laterArgument stage)).val = stage + 1 := rfl

theorem zero_future_value (stage : Nat) :
    ((zeroSection.val (parameter 0 HSet.quineAtom)).val (laterArgument stage)).val = 0 := rfl

theorem same_present_all_arguments (material : HSet.{0}) (argument : cyclicSmall.obj (parameter 0 material)) :
    evaluateValue cyclicSmall positionResults (parameter 0 material)
        (greatestSection.val (parameter 0 material)) argument =
      evaluateValue cyclicSmall positionResults (parameter 0 material)
        (zeroSection.val (parameter 0 material)) argument := by
  apply Subtype.ext
  rw [greatest_evaluation, zero_evaluation]
  exact congrArg Fin.val (Fin.eq_zero argument.1)

theorem different_whole_future_functions :
    greatestSection.val (parameter 0 HSet.quineAtom) ≠ zeroSection.val (parameter 0 HSet.quineAtom) := by
  intro same
  have results := congrArg (fun function : ProductAt cyclicSmall positionResults (parameter 0 HSet.quineAtom) =>
    (function.val (laterArgument 0)).val) same
  exact Nat.one_ne_zero results

theorem infinitely_many_selected_future_results : Function.Injective
    (fun stage => ((greatestSection.val (parameter 0 HSet.quineAtom)).val (laterArgument stage)).val) := by
  intro first second same
  exact Nat.succ.inj same

theorem parameter_object_remains_wider {I : Type} (reading : I → parameters.obj 0) :
    ¬ Function.Surjective reading := parameter_object_has_no_small_cover reading

def zeroOnlyResults : cyclicSmall.Elements ⥤ Type where
  obj argument := PLift (argument.2.1.val = 0)
  map {first second} step := TypeCat.ofHom fun result => ⟨by
    have position : first.2.1.val = second.2.1.val :=
      congrArg (fun member : cyclicSmall.obj second.1 => member.1.val) step.2
    exact position.symm.trans result.down⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro result
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro result
    exact Subsingleton.elim _ _

def presentFunction (material : HSet.{0}) :
    (argument : cyclicSmall.obj (parameter 0 material)) → zeroOnlyResults.obj ⟨parameter 0 material, argument⟩ :=
  fun argument => ⟨congrArg Fin.val (Fin.eq_zero argument.1)⟩

theorem present_function_does_not_extend (material : HSet.{0}) :
    Nonempty ((argument : cyclicSmall.obj (parameter 0 material)) →
      zeroOnlyResults.obj ⟨parameter 0 material, argument⟩) ∧
    ¬ Nonempty (ProductAt cyclicSmall zeroOnlyResults (parameter 0 material)) := by
  refine ⟨⟨presentFunction material⟩, ?_⟩
  rintro ⟨function⟩
  let future : (futureDomain cyclicSmall (parameter 0 material)).Elements :=
    ⟨⟨1, homOfLE (Nat.zero_le 1)⟩,
      ⟨⟨1, Nat.lt_succ_self 1⟩, ⟨false, Or.inl rfl⟩⟩⟩
  exact Nat.one_ne_zero (function.val future).down

theorem sums_still_inhabited (stage : Nat) (material : HSet.{0}) :
    Nonempty ((sigma cyclicSmall zeroOnlyResults).obj (parameter stage material)) :=
  ⟨⟨falseMember stage material, ⟨rfl⟩⟩⟩

def pairedPoint (saved : HSet.{0}) : pairedParameters.Elements := ⟨0, (HSet.quineAtom, saved)⟩

def changedGreatest (saved : HSet.{0}) :
    ProductAt (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall positionResults)
      (pairedPoint saved) :=
  productComparison selectFirst cyclicSmall positionResults (pairedPoint saved)
    (greatestSection.val (parameter 0 HSet.quineAtom))

theorem noninjective_change_preserves_result (saved : HSet.{0})
    (argument : (domainUnder selectFirst cyclicSmall).obj (pairedPoint saved)) :
    (evaluateValue (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall positionResults)
      (pairedPoint saved) (changedGreatest saved) argument).val = argument.1.val := by
  have value := evaluate_substitution selectFirst cyclicSmall positionResults (pairedPoint saved)
    (greatestSection.val (parameter 0 HSet.quineAtom)) argument
  exact (congrArg Subtype.val value).trans (greatest_evaluation (parameter 0 HSet.quineAtom) argument)

def changedTotal (saved : HSet.{0}) :
    ContextualSmallFamilyUniverse.TotalAt
      (pi (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall positionResults)) 0 :=
  ⟨(HSet.quineAtom, saved), changedGreatest saved⟩

theorem classified_change_retains_saved_parameter :
    (ContextualSmallFamilyUniverse.classificationForward
      (pi (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall positionResults))).app 0
        (changedTotal ∅) ≠
    (ContextualSmallFamilyUniverse.classificationForward
      (pi (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall positionResults))).app 0
        (changedTotal HSet.quineAtom) := by
  intro same
  have parameters := congrArg (fun receipt :
    (ContextualSmallFamilyUniverse.ClassificationPullback
      (pi (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall positionResults))).obj 0 =>
        receipt.val.2.2) same
  exact HSet.empty_ne_quineAtom parameters

def greatestSum : (sigma cyclicSmall positionResults).obj (parameter 1 HSet.quineAtom) :=
  ⟨newCyclicMember 0, ⟨1, Nat.le_refl 1⟩⟩

def zeroSum : (sigma cyclicSmall positionResults).obj (parameter 1 HSet.quineAtom) :=
  ⟨newCyclicMember 0, ⟨0, Nat.zero_le 1⟩⟩

theorem sigma_retains_selected_result : greatestSum ≠ zeroSum := by
  intro same
  exact Nat.one_ne_zero (congrArg (fun term : SumAt cyclicSmall positionResults (parameter 1 HSet.quineAtom) =>
    term.2.val) same)

def displayedResults : (ContextualSmallFamilyUniverse.total cyclicSmall).Elements ⥤ Type :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyComprehension.unflatten cyclicSmall) positionResults

theorem displayed_results_regroup :
    ContextualSmallFamilyComprehension.indexedBody cyclicSmall displayedResults = positionResults := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem actual_wider_comprehension_square :
    ContextualSmallFamilyComprehension.contextCompose (ContextualSmallFamilyComprehension.flatten
      (domainUnder selectFirst cyclicSmall))
      (ContextualSmallFamilyUniverse.elementMap
        (ContextualSmallFamilyComprehension.totalChange cyclicSmall selectFirst)) =
    ContextualSmallFamilyComprehension.contextCompose (argumentsUnder selectFirst cyclicSmall)
      (ContextualSmallFamilyComprehension.flatten cyclicSmall) :=
  ContextualSmallFamilyComprehension.comprehension_substitution cyclicSmall selectFirst

theorem independently_formed_code_decodes :
    ContextualSmallFamilyUniverse.decodedFamily
      (ContextualSmallFamilyUniverse.classifier (pi cyclicSmall positionResults)) =
        pi cyclicSmall positionResults := pi_decoder cyclicSmall positionResults

namespace Histories

open LabelledContextPaths

def historyParameters : World ⥤ Type := terminal

def historyDomain : historyParameters.Elements ⥤ Type :=
  ContextualSmallFamilyUniverse.restrict (CategoryOfElements.π historyParameters) arguments

def historyPoint : historyParameters.Elements := ⟨initial, PUnit.unit⟩

def historyArgument (label : Nat) : (futureDomain historyDomain historyPoint).Elements :=
  ⟨⟨next, extension label⟩, newlyAvailable⟩

theorem retained_future_arguments_injective : Function.Injective historyArgument := by
  intro first second same
  have paths := congrArg (fun argument : (futureDomain historyDomain historyPoint).Elements => argument.1.2.val) same
  exact List.singleton_injective paths

theorem compressed_parallel_histories_injective : Function.Injective
    (fun label => (ContextualSmallFamilyConeComparison.compression historyPoint).obj (historyArgument label).1) := by
  intro first second same
  have paths := congrArg (fun future : Future.Objects historyPoint => future.2.1.val) same
  exact List.singleton_injective paths

theorem same_endpoint_argument_different_actual_history :
    (futureArguments historyDomain historyPoint).obj (historyArgument 0) =
        (futureArguments historyDomain historyPoint).obj (historyArgument 1) ∧
      historyArgument 0 ≠ historyArgument 1 :=
  ⟨rfl, fun same => Nat.zero_ne_one (retained_future_arguments_injective same)⟩

end Histories

end Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerControls
