import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModel
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretationControls

/-!
# Actual member type-former controls

The member decoder represents empty and cyclic fibres, and its dependent
pair, function and identity operations preserve the cyclic material child.
An infinitely advancing material set initially contains only the empty set
and later also contains the cyclic set. Two genuine compatible future
functions agree at every present argument and disagree at a later argument.
Thus the member model's dependent product cannot be recovered from present
evaluation alone.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModelControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetModel
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualSetInterpretationControls
open CoveredFuturePowerFamilies
open PowerClassPresheafDescent.Controls

universe u
variable {D : Type u} [Category.{u} D]

theorem empty_member_fibre (point : D) :
    ¬ Nonempty (memberFamily.obj ⟨point, emptySet.val point⟩) := by
  rintro ⟨code⟩
  exact member_empty point _ (memberDecoder _ code).property

noncomputable def cyclicCode (point : D) :
    memberFamily.obj ⟨point, loopSet.val point⟩ :=
  (memberDecoder _).symm ⟨loopSet.val point, loop_self_member point⟩

theorem cyclicCode_value (point : D) :
    (memberDecoder _ (cyclicCode point)).val = loopSet.val point :=
  congrArg Subtype.val ((memberDecoder _).apply_symm_apply _)

theorem cyclic_pair_value (point : D) :
    let pair : memberPairFamily.obj ⟨point, loopSet.val point⟩ := ⟨cyclicCode point, cyclicCode point⟩
    ((memberPairDecoder _ pair).1.val, (memberPairDecoder _ pair).2.val) =
      (loopSet.val point, loopSet.val point) :=
  Prod.ext (cyclicCode_value point) (cyclicCode_value point)

theorem cyclic_function_application (point : D) :
    (memberDecoder _ (ContextualSmallFamilyTypeFormers.evaluateValue memberFamily memberBody
      ⟨point, loopSet.val point⟩ (memberIdentity.val _) (cyclicCode point))).val = loopSet.val point :=
  (memberIdentity_apply_material _ _).trans (cyclicCode_value point)

noncomputable def cyclicIdentityInput (point : D) :
    (ContextualSmallFamilyIdentity.identityContext (memberFamily (D := D))).Elements :=
  ⟨point, (ContextualSmallFamilyIdentity.diagonal (memberFamily (D := D))).app point
    ⟨loopSet.val point, cyclicCode point⟩⟩

theorem cyclic_identity_elimination (point : D) :
    (memberDecoder ⟨point, loopSet.val point⟩
      ((ContextualSmallFamilyIdentity.J (memberFamily (D := D))
        (ContextualSmallFamilyIdentity.endpointMotive (memberFamily (D := D)))
        (ContextualSmallFamilyIdentity.endpointMethod (memberFamily (D := D)))).val
          (cyclicIdentityInput point))).val = loopSet.val point :=
  (memberJ_material (cyclicIdentityInput point)).trans (cyclicCode_value point)

noncomputable def pairEmptyCode (point : D) :
    memberFamily.obj ⟨point, pairSet.app point (emptySet.val point, loopSet.val point)⟩ :=
  (memberDecoder _).symm ⟨emptySet.val point, (member_pair point _ _ _).mpr (Or.inl rfl)⟩

noncomputable def pairCyclicCode (point : D) :
    memberFamily.obj ⟨point, pairSet.app point (emptySet.val point, loopSet.val point)⟩ :=
  (memberDecoder _).symm ⟨loopSet.val point, pair_cyclic_member point⟩

theorem unequal_member_identity_empty (point : D) :
    ¬ Nonempty (memberIdentityFamily.obj
      ⟨point, ⟨⟨pairSet.app point (emptySet.val point, loopSet.val point), pairEmptyCode point⟩,
        pairCyclicCode point⟩⟩) := by
  intro witness
  have same := (memberIdentity_value_iff _).mp witness
  have leftValue : (memberDecoder _ (pairEmptyCode point)).val = emptySet.val point :=
    congrArg Subtype.val ((memberDecoder _).apply_symm_apply
      (⟨emptySet.val point, (member_pair point _ _ _).mpr (Or.inl rfl)⟩ :
        ActualMember ⟨point, pairSet.app point (emptySet.val point, loopSet.val point)⟩))
  have rightValue : (memberDecoder _ (pairCyclicCode point)).val = loopSet.val point :=
    congrArg Subtype.val ((memberDecoder _).apply_symm_apply
      (⟨loopSet.val point, pair_cyclic_member point⟩ :
        ActualMember ⟨point, pairSet.app point (emptySet.val point, loopSet.val point)⟩))
  exact loop_ne_empty point (rightValue.symm.trans (same.symm.trans leftValue))

namespace Infinite

abbrev values := sets (D := Stagesᵒᵖ)

def growingPredicate (point : Stagesᵒᵖ) : Predicate values point where
  holds argument := argument.2 = emptySet.val argument.1.1 ∨
    (1 ≤ stageIndex argument.1.1 ∧ argument.2 = loopSet.val argument.1.1)
  closed {first second} move available := by
    have valueEq : values.map move.1.1 first.2 = second.2 := move.2
    rcases available with empty | ⟨later, cyclic⟩
    · exact Or.inl (valueEq.symm.trans
        ((congrArg (values.map move.1.1) empty).trans (emptySet.property move.1.1)))
    · exact Or.inr ⟨later.trans (growthLe move.1.1), valueEq.symm.trans
        ((congrArg (values.map move.1.1) cyclic).trans (loopSet.property move.1.1))⟩

noncomputable def growingEnumeration (point : Stagesᵒᵖ) : Enumeration (growingPredicate point) where
  Carrier future := PUnit.{1} ⊕ {_receipt : PUnit.{1} // 1 ≤ stageIndex future.1}
  value future receipt := match receipt with
    | Sum.inl _ => emptySet.val future.1
    | Sum.inr _ => loopSet.val future.1
  covered _ _ := by
    constructor
    · rintro (empty | ⟨later, cyclic⟩)
      · exact ⟨Sum.inl PUnit.unit, empty.symm⟩
      · exact ⟨Sum.inr ⟨PUnit.unit, later⟩, cyclic.symm⟩
    · rintro ⟨receipt, same⟩
      cases receipt with
      | inl _ => exact Or.inl same.symm
      | inr receipt => exact Or.inr ⟨receipt.property, same.symm⟩

noncomputable def growingPower (point : Stagesᵒᵖ) : Power values point :=
  ⟨growingPredicate point, ⟨growingEnumeration point⟩⟩

theorem growingPower_restrict {first second : Stagesᵒᵖ} (arrow : first ⟶ second) :
    restrictPower values arrow (growingPower first) = growingPower second := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

noncomputable def growingSet : values.sections :=
  assemble.mapSection ⟨growingPower, fun arrow => growingPower_restrict arrow⟩

theorem growing_future (point target : Stagesᵒᵖ) (arrow : point ⟶ target) (child : values.obj target) :
    FutureMember arrow child (growingSet.val point) ↔
      child = emptySet.val target ∨ (1 ≤ stageIndex target ∧ child = loopSet.val target) := by
  change (unfold.app point (assemble.app point (growingPower point))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

noncomputable def parentPoint (point : Stagesᵒᵖ) : values.Elements := ⟨point, growingSet.val point⟩

noncomputable def emptyCode (point : Stagesᵒᵖ) : memberFamily.obj (parentPoint point) :=
  (memberDecoder _).symm ⟨emptySet.val point, (growing_future point point (𝟙 _) _).mpr (Or.inl rfl)⟩

theorem emptyCode_value (point : Stagesᵒᵖ) :
    (memberDecoder _ (emptyCode point)).val = emptySet.val point :=
  congrArg Subtype.val ((memberDecoder _).apply_symm_apply _)

theorem current_code_unique (code : memberFamily.obj (parentPoint (world 0))) :
    code = emptyCode (world 0) := by
  apply (memberDecoder _).injective
  apply Subtype.ext
  have reading := (memberDecoder _ code).property
  rcases (growing_future _ _ (𝟙 _) _).mp reading with empty | ⟨later, _⟩
  · exact empty.trans (emptyCode_value (world 0)).symm
  · exact (Nat.not_succ_le_zero 0 later).elim

noncomputable def growingParent : NaturalHom (terminal (E := Stagesᵒᵖ)) values where
  app point _ := growingSet.val point
  naturality arrow _ := growingSet.property arrow

noncomputable def actualEmptySection : (actualMemberFamilyUnder growingParent).sections :=
  ⟨fun point => ⟨emptySet.val point.1,
    (growing_future point.1 point.1 (𝟙 _) _).mpr (Or.inl rfl)⟩, by
    intro first second step
    apply Subtype.ext
    exact emptySet.property step.1⟩

noncomputable def growingMemberSection : (memberFamilyUnder growingParent).sections :=
  (memberSectionEquivUnder growingParent).symm actualEmptySection

theorem growingMemberSection_value (point : (terminal (E := Stagesᵒᵖ)).Elements) :
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap growingParent).obj point)
      (growingMemberSection.val point)).val = emptySet.val point.1 :=
  congrArg (fun term : (actualMemberFamilyUnder growingParent).sections => (term.val point).val)
    ((memberSectionEquivUnder growingParent).apply_symm_apply actualEmptySection)

theorem growingMemberSection_compatible
    {first second : (terminal (E := Stagesᵒᵖ)).Elements} (step : first ⟶ second) :
    (memberFamilyUnder growingParent).map step (growingMemberSection.val first) =
      growingMemberSection.val second :=
  growingMemberSection.property step

abbrev advance := ContextualMaterialCoalgebraControls.firstAdvance

noncomputable def futureCyclicCode :
    memberFamily.obj ⟨world 1, values.map advance (growingSet.val (world 0))⟩ :=
  (memberDecoder _).symm ⟨loopSet.val (world 1), (futureMember_iff _ _ _).mp
    ((growing_future _ _ advance _).mpr (Or.inr ⟨Nat.le_refl 1, rfl⟩))⟩

noncomputable def futureCyclicArgument :
    (ContextualSmallFamilyTypeFormers.futureDomain memberFamily (parentPoint (world 0))).Elements :=
  ⟨⟨world 1, advance⟩, futureCyclicCode⟩

theorem futureCyclicCode_value :
    (memberDecoder _ futureCyclicCode).val = loopSet.val (world 1) :=
  congrArg Subtype.val ((memberDecoder _).apply_symm_apply _)

noncomputable def constantEmpty : memberFunctionFamily.obj (parentPoint (world 0)) :=
  (ContextualSmallFamilyTypeFormers.piCurry memberFamily memberBody
    (parameters := memberFamily) (ContextualSmallFamilyTypeFormers.identityNat memberBody)).app
    (parentPoint (world 0)) (emptyCode (world 0))

theorem constantEmpty_apply (argument : memberFamily.obj (parentPoint (world 0))) :
    ContextualSmallFamilyTypeFormers.evaluateValue memberFamily memberBody (parentPoint (world 0))
      constantEmpty argument = emptyCode (world 0) :=
  congrArg (fun operation : NatTrans (ContextualSmallFamilyTypeFormers.overArguments memberFamily memberFamily) memberBody =>
    operation.app ⟨parentPoint (world 0), argument⟩ (emptyCode (world 0)))
    (ContextualSmallFamilyTypeFormers.pi_uncurry_curry memberFamily memberBody
      (ContextualSmallFamilyTypeFormers.identityNat memberBody))

theorem agree_on_all_present_arguments (argument : memberFamily.obj (parentPoint (world 0))) :
    ContextualSmallFamilyTypeFormers.evaluateValue memberFamily memberBody (parentPoint (world 0))
      (memberIdentity.val _) argument =
    ContextualSmallFamilyTypeFormers.evaluateValue memberFamily memberBody (parentPoint (world 0))
      constantEmpty argument :=
  (memberIdentity_apply _ argument).trans ((current_code_unique argument).trans (constantEmpty_apply argument).symm)

theorem constantEmpty_future_value :
    (memberDecoder _ (constantEmpty.val futureCyclicArgument)).val = emptySet.val (world 1) := by
  change (memberDecoder _ (memberFamily.map
    (ContextualSmallFamilyTypeFormers.futureRootArrow memberFamily (parentPoint (world 0)) futureCyclicArgument)
    (emptyCode (world 0)))).val = _
  exact (memberDecoder_restriction_value _ _).symm.trans
    ((congrArg (values.map advance) (emptyCode_value (world 0))).trans (emptySet.property advance))

theorem functions_differ_on_future_argument :
    (memberIdentity.val (parentPoint (world 0))).val futureCyclicArgument ≠
      constantEmpty.val futureCyclicArgument := by
  intro same
  have material := congrArg (fun code => (memberDecoder _ code).val) same
  have identityValue : (memberDecoder _
    ((memberIdentity.val (parentPoint (world 0))).val futureCyclicArgument)).val = loopSet.val (world 1) :=
    futureCyclicCode_value
  exact loop_ne_empty (world 1) (identityValue.symm.trans (material.trans constantEmpty_future_value))

theorem current_evaluation_not_injective :
    ¬ Function.Injective (fun term : memberFunctionFamily.obj (parentPoint (world 0)) =>
      fun argument => ContextualSmallFamilyTypeFormers.evaluateValue memberFamily memberBody
        (parentPoint (world 0)) term argument) := by
  intro injective
  have same := injective (funext agree_on_all_present_arguments)
  exact functions_differ_on_future_argument
    (congrArg (fun term => term.val futureCyclicArgument) same)

theorem future_code_has_no_present_preimage :
    ¬ ∃ code : memberFamily.obj (parentPoint (world 0)),
      memberFamily.map (ContextualSmallFamilyTypeFormers.futureRootArrow memberFamily
        (parentPoint (world 0)) futureCyclicArgument) code = futureCyclicCode := by
  rintro ⟨code, same⟩
  rw [current_code_unique code] at same
  have reading := congrArg (fun item => (memberDecoder _ item).val) same
  exact loop_ne_empty (world 1) (futureCyclicCode_value.symm.trans
    (reading.symm.trans constantEmpty_future_value))

end Infinite

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModelControls
