import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosure
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModelControls

/-!
# Argument-dependent contextual member closure controls

An infinite material family acquires a cyclic member at a later world.
The positive body returns the singleton of the selected member, so its
literal result depends on the argument. The negative body has an answer
at every present argument and no answer at the new cyclic argument.
Its complete contextual product is therefore empty. The positive body's
everywhere-inhabited positions also forbid a well-founded W tree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosureControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetFamilyClosure HostChoiceContextualHypersetModel
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualSetInterpretationControls
open HostChoiceContextualHypersetModelControls.Infinite
open PowerClassPresheafDescent.Controls
open ContextualSmallFamilyTypeFormers

abbrev parameters := terminal (E := Stagesᵒᵖ)
abbrev point (world : Stagesᵒᵖ) : parameters.Elements := ⟨world, PUnit.unit⟩

noncomputable abbrev input := domain growingParent

noncomputable def singletonBody : NaturalHom (comprehension growingParent) values :=
  (argumentReading growingParent).comp singletonSet

noncomputable def singletonChild (argument : input.Elements) :
    (body growingParent singletonBody).obj argument :=
  (bodyDecoder growingParent singletonBody argument).symm
    ⟨(argumentReading growingParent).app argument.1.1 ⟨argument.1.2, argument.2⟩,
      (member_singleton _ _ _).mpr rfl⟩

theorem singletonChild_value (argument : input.Elements) :
    (bodyDecoder growingParent singletonBody argument (singletonChild argument)).val =
      (argumentReading growingParent).app argument.1.1 ⟨argument.1.2, argument.2⟩ :=
  congrArg Subtype.val ((bodyDecoder growingParent singletonBody argument).apply_symm_apply _)

theorem singletonChild_natural {first second : input.Elements} (step : first ⟶ second) :
    (body growingParent singletonBody).map step (singletonChild first) = singletonChild second := by
  apply (bodyDecoder growingParent singletonBody second).injective
  apply Subtype.ext
  exact (bodyDecoder_value_natural growingParent singletonBody step (singletonChild first)).symm.trans
    ((congrArg (values.map step.1.1) (singletonChild_value first)).trans
      (((argumentReading growingParent).naturality step.1.1 ⟨first.1.2, first.2⟩).trans
        ((congrArg ((argumentReading growingParent).app second.1.1)
          (congrArg (fun receipt : (comprehension growingParent).obj second.1.1 => receipt)
            ((ContextualSmallFamilyComprehension.flatten input).map step).2)).trans
              (singletonChild_value second).symm)))

noncomputable def singletonProduct (parameter : parameters.Elements) :
    (piFamily growingParent singletonBody).obj parameter :=
  ⟨fun argument => singletonChild ((futureArguments input parameter).obj argument),
    fun step => singletonChild_natural ((futureArguments input parameter).map step)⟩

theorem singletonProduct_future_value (parameter : parameters.Elements)
    (argument : (futureDomain input parameter).Elements) :
    ((piDecoder growingParent singletonBody parameter (singletonProduct parameter)).val argument).val =
      (argumentReading growingParent).app argument.1.1 ⟨parameter.2, argument.2⟩ :=
  singletonChild_value ((futureArguments input parameter).obj argument)

noncomputable def loopArgument : input.obj (point (world 1)) :=
  (memberDecoder _).symm ⟨loopSet.val (world 1),
    (growing_future _ _ (𝟙 _) _).mpr (Or.inr ⟨Nat.le_refl 1, rfl⟩)⟩

theorem loopArgument_value :
    (argumentReading growingParent).app (world 1) ⟨PUnit.unit, loopArgument⟩ = loopSet.val (world 1) :=
  congrArg Subtype.val ((memberDecoder _).apply_symm_apply _)

noncomputable def futureLoopArgument : (futureDomain input (point (world 0))).Elements :=
  ⟨⟨world 1, advance⟩, loopArgument⟩

theorem singletonProduct_later_cyclic_value :
    ((piDecoder growingParent singletonBody (point (world 0)) (singletonProduct _)).val
      futureLoopArgument).val = loopSet.val (world 1) :=
  (singletonProduct_future_value _ futureLoopArgument).trans loopArgument_value

theorem singletonProduct_present_empty_value :
    ((piDecoder growingParent singletonBody (point (world 0)) (singletonProduct _)).val
      (currentArgument input _ (emptyCode (world 0)))).val = emptySet.val (world 0) :=
  (singletonProduct_future_value _ _).trans (emptyCode_value _)

theorem dependent_body_sets_distinct :
    singletonBody.app (world 1) ⟨PUnit.unit, emptyCode (world 1)⟩ ≠
      singletonBody.app (world 1) ⟨PUnit.unit, loopArgument⟩ := by
  intro same
  have available : Member (world 1) (emptySet.val (world 1))
      (singletonBody.app (world 1) ⟨PUnit.unit, emptyCode (world 1)⟩) :=
    (member_singleton _ _ _).mpr (emptyCode_value _)
  rw [same] at available
  exact loop_ne_empty _ (loopArgument_value.symm.trans ((member_singleton _ _ _).mp available))

def selectedEmptyTest : CoveredFuturePowerClassifier.StablePredicate
    (CoveredFuturePowerClassifier.product (comprehension growingParent) values) where
  holds receipt := (argumentReading growingParent).app receipt.1 receipt.2.1 = emptySet.val receipt.1
  closed {first second} step available := by
    have receipts : (comprehension growingParent).map step.1 first.2.1 = second.2.1 :=
      congrArg Prod.fst step.2
    exact (congrArg ((argumentReading growingParent).app second.1) receipts).symm.trans
      (((argumentReading growingParent).naturality step.1 first.2.1).symm.trans
        ((congrArg (values.map step.1) available).trans (emptySet.property step.1)))

noncomputable def boundedInput : NaturalHom (comprehension growingParent)
    (CoveredFuturePowerClassifier.product (comprehension growingParent) values) where
  app stage receipt := (receipt, singletonSet.app stage (emptySet.val stage))
  naturality step _receipt := Prod.ext rfl
    (((singletonSet (D := Stagesᵒᵖ)).naturality step (emptySet.val _)).trans
      (congrArg (singletonSet.app _) (emptySet.property step)))

noncomputable def selectedEmptyBody : NaturalHom (comprehension growingParent) values :=
  boundedInput.comp (separationSet (comprehension growingParent) selectedEmptyTest)

theorem member_selectedEmptyBody (stage : Stagesᵒᵖ)
    (receipt : (comprehension growingParent).obj stage) (child : values.obj stage) :
    Member stage child (selectedEmptyBody.app stage receipt) ↔
      emptySet.val stage = child ∧ (argumentReading growingParent).app stage receipt = emptySet.val stage := by
  exact (member_separation (comprehension growingParent) selectedEmptyTest stage receipt
    (singletonSet.app stage (emptySet.val stage)) child).trans
      (and_congr_left fun _ => member_singleton stage child (emptySet.val stage))

noncomputable def presentAnswer (argument : input.obj (point (world 0))) :
    (body growingParent selectedEmptyBody).obj ⟨point (world 0), argument⟩ :=
  (bodyDecoder growingParent selectedEmptyBody _).symm ⟨emptySet.val (world 0),
    (member_selectedEmptyBody _ _ _).mpr ⟨rfl, by
      change (memberDecoder _ argument).val = emptySet.val (world 0)
      rw [current_code_unique argument]
      exact emptyCode_value _⟩⟩

theorem every_present_argument_has_answer :
    ∀ argument : input.obj (point (world 0)),
      Nonempty ((body growingParent selectedEmptyBody).obj ⟨point (world 0), argument⟩) :=
  fun argument => ⟨presentAnswer argument⟩

theorem future_cyclic_body_empty :
    ¬ Nonempty ((body growingParent selectedEmptyBody).obj
      ((futureArguments input (point (world 0))).obj futureLoopArgument)) := by
  rintro ⟨answer⟩
  have available := (bodyDecoder growingParent selectedEmptyBody _ answer).property
  have impossible := ((member_selectedEmptyBody _ _ _).mp available).2
  exact loop_ne_empty _ (loopArgument_value.symm.trans impossible)

theorem complete_product_empty :
    ¬ Nonempty ((piFamily growingParent selectedEmptyBody).obj (point (world 0))) := by
  rintro ⟨term⟩
  exact future_cyclic_body_empty ⟨term.val futureLoopArgument⟩

theorem selected_body_really_depends_on_argument :
    Nonempty ((body growingParent selectedEmptyBody).obj
      ⟨point (world 1), emptyCode (world 1)⟩) ∧
    ¬ Nonempty ((body growingParent selectedEmptyBody).obj ⟨point (world 1), loopArgument⟩) := by
  refine ⟨⟨(bodyDecoder growingParent selectedEmptyBody _).symm ⟨emptySet.val (world 1),
    (member_selectedEmptyBody _ _ _).mpr ⟨rfl, emptyCode_value _⟩⟩⟩, ?_⟩
  exact future_cyclic_body_empty

theorem singleton_positions_admit_no_W (parameter : parameters.Elements) :
    ¬ Nonempty ((wFamily growingParent singletonBody).obj parameter) := by
  rintro ⟨tree⟩
  have impossible : ∀ (future : PowerClassPresheafBaseChange.Future.Objects parameter.1)
      (raw : ContextualWReindexing.Raw
        (ContextualSmallFamilyWTypes.signature input (body growingParent singletonBody) parameter) future), False := by
    intro future raw
    induction raw with
    | @sup future label _children ih =>
      exact ih future (𝟙 future)
        (singletonChild ((futureArguments input parameter).obj
          ⟨future, (futureDomain input parameter).map (𝟙 future) label⟩))
  exact impossible _ tree.val

theorem empty_shape_has_no_future_position (parameter : parameters.Elements)
    (future : PowerClassPresheafBaseChange.Future.Objects parameter.1)
    (arrow : ContextualSmallFamilyUniverse.root parameter.1 ⟶ future) :
    ¬ Nonempty ((ContextualSmallFamilyTypeFormers.futureBody input
      (body growingParent (argumentReading growingParent)) parameter).obj
        ⟨future, (futureDomain input parameter).map arrow (emptyCode parameter.1)⟩) := by
  rintro ⟨position⟩
  have moved := memberDecoder_restriction_value
    ((ContextualSmallFamilyUniverse.elementMap growingParent).map
      ((ContextualSmallFamilyUniverse.futureElement parameter.1 parameter.2).map arrow))
    (emptyCode parameter.1)
  have emptyParent : (argumentReading growingParent).app future.1
      ⟨parameter.2, (futureDomain input parameter).map arrow (emptyCode parameter.1)⟩ =
        emptySet.val future.1 :=
    moved.symm.trans ((congrArg (values.map arrow.1) (emptyCode_value parameter.1)).trans
      (emptySet.property arrow.1))
  have available := (bodyDecoder growingParent (argumentReading growingParent)
    ((futureArguments input parameter).obj
      ⟨future, (futureDomain input parameter).map arrow (emptyCode parameter.1)⟩) position).property
  change Member future.1 _ ((argumentReading growingParent).app future.1
    ⟨parameter.2, (futureDomain input parameter).map arrow (emptyCode parameter.1)⟩) at available
  rw [emptyParent] at available
  exact member_empty _ _ available

noncomputable def emptyPositionLeaf (parameter : parameters.Elements) :
    (wFamily growingParent (argumentReading growingParent)).obj parameter :=
  ContextualWTypes.sup (futureDomain input parameter)
    (futureBody input (body growingParent (argumentReading growingParent)) parameter)
    (emptyCode parameter.1)
    (fun future arrow position => (empty_shape_has_no_future_position parameter future arrow ⟨position⟩).elim)
    (fun future _second arrow _later position =>
      (empty_shape_has_no_future_position parameter future arrow ⟨position⟩).elim)

theorem actual_argument_dependent_W_inhabited (parameter : parameters.Elements) :
    Nonempty ((wFamily growingParent (argumentReading growingParent)).obj parameter) :=
  ⟨emptyPositionLeaf parameter⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosureControls
