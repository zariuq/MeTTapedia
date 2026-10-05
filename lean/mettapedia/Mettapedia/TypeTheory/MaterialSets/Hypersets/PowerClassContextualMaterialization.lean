import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledDependentProducts
import Mettapedia.GSLT.Logic.ContextualObservedFamilyEnclosure
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Material representation of compatible contextual functions

The material function decoder receives its future context, its actual
restriction arrow and its argument externally. Faithful graph labels for
that entire index, together with actual result-fibre decoders, suffice to
construct the material carrier. A decoder for the context/index carrier is
not assumed. Separation retains exactly the natural future functions.

The growing-context model supplies those labels explicitly. Its context
category is thin, so a context arrow is determined by its endpoints. A
separate obstruction records why endpoint labels cannot erase a genuinely
distinct parallel arrow in an arbitrary context category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualMaterialization

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open PowerClassPresheafBaseChange

universe u
variable {D : Type u} [Category.{u} D]
variable (domain : D ⥤ Type u) (body : domain.Elements ⥤ Type u) (point : D)

abbrev FutureArguments := (Future.domain domain point).Elements

variable (arguments : ArgumentCoding (FutureArguments domain point))
variable (outputs : (argument : FutureArguments domain point) →
  PresentedType ((Future.result domain body point).obj argument))

def naturalSectionModel : PresentedType (Future.result domain body point).sections :=
  LabelledDependentProducts.compatibleProduct arguments outputs
    (fun values => values ∈ (Future.result domain body point).sections)

/-- An actual material carrier for the full contextual Π fibre. Its inputs
are graph labels and actual result decoders, not a supplied section carrier. -/
def piModel : PresentedType (DependentSection domain body point) :=
  PresentedType.relabel (naturalSectionModel domain body point arguments outputs)
    (Future.sectionEquiv domain body point).symm

theorem piModel_value (function : DependentSection domain body point) :
    (piModel domain body point arguments outputs).value function =
      HSet.mk (LabelledDependentProducts.functionGraph arguments outputs
        (fun argument => function.app argument.1.1 argument.1.2 argument.2)) := rfl

theorem piModel_entry (function : DependentSection domain body point)
    (argument : FutureArguments domain point) :
    HSet.kpair (arguments.reading argument)
        ((outputs argument).value (function.app argument.1.1 argument.1.2 argument.2)) ∈
      (piModel domain body point arguments outputs).value function :=
  LabelledDependentProducts.product_entry arguments outputs
    (fun argument => function.app argument.1.1 argument.1.2 argument.2) argument

theorem piModel_evaluation (function : DependentSection domain body point)
    (argument : FutureArguments domain point) :
    LabelledDependentProducts.evalValue arguments outputs
        ((piModel domain body point arguments outputs).value function) argument =
      (outputs argument).value (function.app argument.1.1 argument.1.2 argument.2) :=
  LabelledDependentProducts.evalValue_functionGraph arguments outputs _ argument

theorem piModel_decode_encode (function : DependentSection domain body point) :
    (piModel domain body point arguments outputs).decode
      ⟨(piModel domain body point arguments outputs).value function,
        (piModel domain body point arguments outputs).value_mem function⟩ = function :=
  PresentedType.decode_value _ function

theorem piModel_encode_decode
    (member : {value : HSet.{u} // value ∈ (piModel domain body point arguments outputs).carrier}) :
    (piModel domain body point arguments outputs).value
      ((piModel domain body point arguments outputs).decode member) = member.1 :=
  PresentedType.value_decode _ member

/-- Material membership records a natural function, not merely an arbitrary
pointwise table with the same currently visible support. -/
theorem mem_piModel_iff (value : HSet.{u}) :
    value ∈ (piModel domain body point arguments outputs).carrier ↔
      ∃ function : DependentSection domain body point,
        HSet.mk (LabelledDependentProducts.functionGraph arguments outputs
          (fun argument => function.app argument.1.1 argument.1.2 argument.2)) = value := by
  constructor
  · intro member
    let decoded := (piModel domain body point arguments outputs).decode ⟨value, member⟩
    exact ⟨decoded, (piModel_value _ _ _ _ _ decoded).symm.trans (PresentedType.value_decode _ ⟨value, member⟩)⟩
  · rintro ⟨function, same⟩
    have represented := (piModel domain body point arguments outputs).value_mem function
    rw [piModel_value, same] at represented
    exact represented

/-- A material Σ fibre requires a decoder for its first coordinate. The
external context is retained; it is not inferred from the material pair. -/
def sigmaModel (first : PresentedType (domain.obj point))
    (second : (argument : domain.obj point) → PresentedType (body.obj ⟨point, argument⟩)) :
    PresentedType ((PowerClassPresheafProducts.IndexedSigma.family domain body).obj point) :=
  PresentedType.sum first second

theorem sigmaModel_value (first : PresentedType (domain.obj point))
    (second : (argument : domain.obj point) → PresentedType (body.obj ⟨point, argument⟩))
    (term : (PowerClassPresheafProducts.IndexedSigma.family domain body).obj point) :
    (sigmaModel domain body point first second).value term =
      HSet.kpair (first.value term.1) ((second term.1).value term.2) :=
  PresentedType.sum_value first second term

theorem sigmaModel_first_value (first : PresentedType (domain.obj point))
    (second : (argument : domain.obj point) → PresentedType (body.obj ⟨point, argument⟩))
    (term : (PowerClassPresheafProducts.IndexedSigma.family domain body).obj point) :
    HSet.fst ((sigmaModel domain body point first second).value term) = first.value term.1 :=
  (congrArg HSet.fst (sigmaModel_value domain body point first second term)).trans (HSet.fst_kpair _ _)

theorem sigmaModel_second_value (first : PresentedType (domain.obj point))
    (second : (argument : domain.obj point) → PresentedType (body.obj ⟨point, argument⟩))
    (term : (PowerClassPresheafProducts.IndexedSigma.family domain body).obj point) :
    HSet.snd ((sigmaModel domain body point first second).value term) = (second term.1).value term.2 :=
  (congrArg HSet.snd (sigmaModel_value domain body point first second term)).trans (HSet.snd_kpair _ _)

private theorem future_arrow_heq {X : D} {first second : Future.Objects X} (same : first = second) :
    HEq first.2 second.2 := by
  cases same
  rfl

theorem parallel_arrows_require_index_faithfulness {X Y : D} (first second : X ⟶ Y)
    (different : first ≠ second) (argument : domain.obj Y) :
    ¬ Function.Injective (fun index : FutureArguments domain X =>
      (⟨index.1.1, index.2⟩ : domain.Elements)) := by
  intro injective
  have indices := injective (a₁ := (⟨⟨Y, first⟩, argument⟩ : FutureArguments domain X))
    (a₂ := (⟨⟨Y, second⟩, argument⟩ : FutureArguments domain X)) rfl
  have futures : (⟨Y, first⟩ : Future.Objects X) = ⟨Y, second⟩ := congrArg Sigma.fst indices
  exact different (eq_of_heq (future_arrow_heq futures))

theorem parallel_control_forgets_distinct_arrows :
    ¬ Function.Injective (fun index : FutureArguments
      (PowerClassPresheafProducts.CP.unitFamily : CategoryTheory.Limits.WalkingParallelPair ⥤ Type)
        CategoryTheory.Limits.WalkingParallelPair.zero =>
          (⟨index.1.1, index.2⟩ : PowerClassPresheafProducts.CP.unitFamily.Elements)) := by
  exact parallel_arrows_require_index_faithfulness PowerClassPresheafProducts.CP.unitFamily
    CategoryTheory.Limits.WalkingParallelPairHom.left CategoryTheory.Limits.WalkingParallelPairHom.right
      (by intro same; cases same) PUnit.unit

def powerClassModel (graph : AccessiblePointedGraph.{u}) :
    PresentedType (AccessiblePointedGraph.PowerMemberClass graph) where
  graph := graph
  decode := ({
    toFun member := ⟨member.1, (AccessiblePointedGraph.picture_eq_mk graph).symm ▸ member.2⟩
    invFun member := ⟨member.1, (AccessiblePointedGraph.picture_eq_mk graph) ▸ member.2⟩
    left_inv _ := rfl
    right_inv _ := rfl } :
      {value : HSet.{u} // value ∈ HSet.mk graph} ≃ AccessiblePointedGraph.PicturedMembers graph).trans
        (AccessiblePointedGraph.powerMemberEquiv graph).symm

theorem powerClassModel_value (graph : AccessiblePointedGraph.{u})
    (member : AccessiblePointedGraph.PowerMemberClass graph) :
    (powerClassModel graph).value member = AccessiblePointedGraph.classValue graph member.1 := rfl

namespace BaseChange

variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)
variable (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) (point : Q.Elements)

def argumentForward :
    FutureArguments (PowerClassPresheafProducts.reindex change domain) point ⥤
      FutureArguments domain ((PowerClassPresheafProducts.elementMap change).obj point) :=
  Cat.elementsMap (Future.map (PowerClassPresheafProducts.elementMap change) point)
    (Future.domain domain ((PowerClassPresheafProducts.elementMap change).obj point))

def argumentBackward :
    FutureArguments domain ((PowerClassPresheafProducts.elementMap change).obj point) ⥤
      FutureArguments (PowerClassPresheafProducts.reindex change domain) point :=
  Cat.elementsBack (Future.map (PowerClassPresheafProducts.elementMap change) point)
    (liftFuture change point) (future_right_inverse change point)
      (Future.domain domain ((PowerClassPresheafProducts.elementMap change).obj point))

theorem argumentForward_backward
    (argument : FutureArguments domain ((PowerClassPresheafProducts.elementMap change).obj point)) :
    (argumentForward change domain point).obj ((argumentBackward change domain point).obj argument) = argument :=
  Cat.elements_right_obj _ _ (future_right_inverse change point) _ argument

theorem argumentBackward_forward
    (argument : FutureArguments (PowerClassPresheafProducts.reindex change domain) point) :
    (argumentBackward change domain point).obj ((argumentForward change domain point).obj argument) = argument :=
  Cat.elements_left_obj (Future.map (PowerClassPresheafProducts.elementMap change) point)
    (liftFuture change point) (future_left_inverse change point) (future_right_inverse change point)
      (Future.domain domain ((PowerClassPresheafProducts.elementMap change).obj point)) argument

variable (coding : ArgumentCoding
  (FutureArguments domain ((PowerClassPresheafProducts.elementMap change).obj point)))
variable (resultModels :
  (argument : FutureArguments domain ((PowerClassPresheafProducts.elementMap change).obj point)) →
    PresentedType ((Future.result domain body ((PowerClassPresheafProducts.elementMap change).obj point)).obj argument))

/-- The genuinely constructed future isomorphism transports faithful labels
without introducing a new choice of context representatives. -/
def codingReindex : ArgumentCoding (FutureArguments (PowerClassPresheafProducts.reindex change domain) point) where
  graph argument := coding.graph ((argumentForward change domain point).obj argument)
  injective := by
    intro first second same
    have readings := coding.injective same
    have recovered := congrArg (argumentBackward change domain point).obj readings
    exact (argumentBackward_forward change domain point first).symm.trans
      (recovered.trans (argumentBackward_forward change domain point second))

def outputsReindex (argument : FutureArguments (PowerClassPresheafProducts.reindex change domain) point) :
    PresentedType ((Future.result (PowerClassPresheafProducts.reindex change domain)
      (bodyReindex change domain body) point).obj argument) :=
  resultModels ((argumentForward change domain point).obj argument)

/-- Full contextual Π materialization commutes with the constructed base
change when its entire future-index labels are transported along that map. -/
theorem materialPi_reindex_value
    (function : DependentSection domain body ((PowerClassPresheafProducts.elementMap change).obj point)) :
    (piModel (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body) point
      (codingReindex change domain point coding) (outputsReindex change domain body point resultModels)).value
        (piFibreEquiv change domain body point function) =
      (piModel domain body ((PowerClassPresheafProducts.elementMap change).obj point) coding resultModels).value function := by
  rw [piModel_value, piModel_value]
  apply HSet.ext
  intro row
  refine (LabelledDependentProducts.mem_functionGraph_iff
    (codingReindex change domain point coding) (outputsReindex change domain body point resultModels)
    (fun argument => (piFibreEquiv change domain body point function).app
      argument.1.1 argument.1.2 argument.2) row).trans ?_
  refine Iff.trans ?_ (LabelledDependentProducts.mem_functionGraph_iff coding resultModels
    (fun argument => function.app argument.1.1 argument.1.2 argument.2) row).symm
  constructor
  · rintro ⟨argument, same⟩
    exact ⟨(argumentForward change domain point).obj argument, same⟩
  · rintro ⟨argument, same⟩
    refine ⟨(argumentBackward change domain point).obj argument, ?_⟩
    have indexEq := argumentForward_backward change domain point argument
    change HSet.kpair (coding.reading ((argumentForward change domain point).obj
        ((argumentBackward change domain point).obj argument)))
      ((resultModels ((argumentForward change domain point).obj
        ((argumentBackward change domain point).obj argument))).value
        (function.app (((argumentForward change domain point).obj
          ((argumentBackward change domain point).obj argument)).1.1)
          (((argumentForward change domain point).obj
            ((argumentBackward change domain point).obj argument)).1.2)
          (((argumentForward change domain point).obj
            ((argumentBackward change domain point).obj argument)).2))) = row
    exact (congrArg (fun index => HSet.kpair (coding.reading index)
      ((resultModels index).value (function.app index.1.1 index.1.2 index.2))) indexEq).trans same

end BaseChange

namespace Growing

open PowerClassFamilyDescent
open PowerClassPresheafDescent

abbrev profile := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.profile
abbrev base := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.base
abbrev displayed := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.displayed
abbrev positiveGraphs := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveGraphs
abbrev positiveTransport := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTransport
abbrev old := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.old
abbrev later := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.later
abbrev futureArrow := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.futureArrow
abbrev futureArgument := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.futureArgument
abbrev identityFunction := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.identity
abbrev constantFunction := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.constantEmpty

def labelGraphs (X : PowerClassPresheafDescent.Controls.Stagesᵒᵖ)
    (source : profile.sourceFace.obj X) : AccessiblePointedGraph := OutcomeLabels.chainGraph source.1.val

theorem labelsInvariant (X : PowerClassPresheafDescent.Controls.Stagesᵒᵖ) :
    FamilyInvariant (profile.observation.app X) (labelGraphs X) := by
  intro left right same
  have positions :=
    (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.bisimilar_iff_position X left right).mp
      ((profile.observation_eq_iff X left right).mp same)
  exact congrArg (fun position => HSet.mk (OutcomeLabels.chainGraph position.val)) positions

/-- Whole source fibres receive faithful position labels without decoding
a natural number from a material membership proposition. -/
def classCoding (X : PowerClassPresheafDescent.Controls.Stagesᵒᵖ) : ArgumentCoding (base.obj X) where
  graph observed := familyGraph (labelGraphs X) observed
  injective := by
    intro first second same
    obtain ⟨left, leftEq⟩ := classOf_surjective (profile.observation.app X) first
    obtain ⟨right, rightEq⟩ := classOf_surjective (profile.observation.app X) second
    rw [← leftEq, ← rightEq] at same
    have firstValue := (familyGraph_decode (labelGraphs X) (classOf (profile.observation.app X) left)).trans
      (family_beta _ _ (labelsInvariant X) left)
    have secondValue := (familyGraph_decode (labelGraphs X) (classOf (profile.observation.app X) right)).trans
      (family_beta _ _ (labelsInvariant X) right)
    have readings := firstValue.symm.trans (same.trans secondValue)
    change HSet.mk (OutcomeLabels.chainGraph left.1.val) = HSet.mk (OutcomeLabels.chainGraph right.1.val) at readings
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at readings
    have positions : left.1 = right.1 := Fin.ext (OutcomeLabels.chainValue_injective readings)
    have observed := (profile.observation_eq_iff X left right).mpr
      ((Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.bisimilar_iff_position X left right).mpr positions)
    exact leftEq.symm.trans (((classOf_eq_iff _ left right).mpr observed).trans rightEq)

def pointCoding : ArgumentCoding base.Elements where
  graph point := AccessiblePointedGraph.kpairGraph
    (OutcomeLabels.chainGraph (PowerClassPresheafDescent.Controls.stageIndex point.1))
    ((classCoding point.1).graph point.2)
  injective := by
    rintro ⟨X, first⟩ ⟨Y, second⟩ same
    change HSet.mk (AccessiblePointedGraph.kpairGraph
        (OutcomeLabels.chainGraph (PowerClassPresheafDescent.Controls.stageIndex X)) ((classCoding X).graph first)) =
      HSet.mk (AccessiblePointedGraph.kpairGraph
        (OutcomeLabels.chainGraph (PowerClassPresheafDescent.Controls.stageIndex Y)) ((classCoding Y).graph second)) at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    have worlds := (HSet.kpair_inj.mp same).1
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at worlds
    have indices := OutcomeLabels.chainValue_injective worlds
    have contexts : X = Y := Opposite.unop_injective (Opposite.unop_injective indices)
    subst Y
    exact Sigma.ext rfl (heq_of_eq ((classCoding X).injective (HSet.kpair_inj.mp same).2))

def memberModel (point : base.Elements) : PresentedType (displayed.obj point) :=
  powerClassModel (familyGraph (fun source => positiveGraphs ⟨point.1, source⟩) point.2)

theorem memberModel_value (point : base.Elements) (member : displayed.obj point) :
    (memberModel point).value member =
      Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.valueAt point member :=
  (powerClassModel_value _ member).trans (familyMemberEquiv_value _ _ member).symm

/-- Contexts in this model are thin. Endpoint and actual argument labels
therefore preserve the entire future arrow/argument index. -/
def futureCoding (point : base.Elements) : ArgumentCoding (FutureArguments displayed point) where
  graph argument := AccessiblePointedGraph.kpairGraph (pointCoding.graph argument.1.1)
    ((memberModel argument.1.1).termGraph argument.2)
  injective := by
    rintro ⟨⟨X, earlier⟩, first⟩ ⟨⟨Y, later⟩, second⟩ same
    change displayed.obj X at first
    change displayed.obj Y at second
    change HSet.mk (AccessiblePointedGraph.kpairGraph (pointCoding.graph X) ((memberModel X).termGraph first)) =
      HSet.mk (AccessiblePointedGraph.kpairGraph (pointCoding.graph Y) ((memberModel Y).termGraph second)) at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    rw [PresentedType.mk_termGraph (memberModel X) first, PresentedType.mk_termGraph (memberModel Y) second] at same
    have endpoints : X = Y := pointCoding.injective (HSet.kpair_inj.mp same).1
    subst Y
    have arrows : earlier = later := by
      apply CategoryOfElements.ext base
      exact Subsingleton.elim _ _
    subst later
    exact Sigma.ext rfl (heq_of_eq ((memberModel X).value_injective (HSet.kpair_inj.mp same).2))

abbrev identityBody := PowerClassPresheafProducts.indexedBody displayed
  (PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.projection displayed) displayed)

def outputModels (point : base.Elements) (argument : FutureArguments displayed point) :
    PresentedType ((Future.result displayed identityBody point).obj argument) := memberModel argument.1.1

def materialPi (point : base.Elements) : PresentedType (DependentSection displayed identityBody point) :=
  piModel displayed identityBody point (futureCoding point) (outputModels point)

def materialSigma (point : base.Elements) :
    PresentedType ((PowerClassPresheafProducts.IndexedSigma.family displayed identityBody).obj point) :=
  sigmaModel displayed identityBody point (memberModel point) (fun _ => memberModel point)

def laterIndex : FutureArguments displayed old := ⟨⟨later, futureArrow⟩, futureArgument⟩

theorem material_functions_differ :
    (materialPi old).value (identityFunction.val old) ≠
      (materialPi old).value (constantFunction.val old) := by
  intro same
  exact Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.function_components_differ
    ((materialPi old).value_injective same)

/-- The constructed material decoder preserves a genuinely later cyclic
argument at an old observed base point. -/
theorem material_future_evaluation :
    LabelledDependentProducts.evalValue (futureCoding old) (outputModels old)
        ((materialPi old).value (identityFunction.val old)) laterIndex = HSet.quineAtom := by
  have evaluation := piModel_evaluation displayed identityBody old (futureCoding old) (outputModels old)
    (identityFunction.val old) laterIndex
  have application := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.ConstructiveFamilies.identityFunction_future
    profile positiveGraphs positiveTransport old later futureArrow futureArgument
  exact evaluation.trans ((congrArg (memberModel later).value application).trans
    ((memberModel_value later futureArgument).trans
      Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.futureArgument_value))

theorem material_constant_evaluation :
    LabelledDependentProducts.evalValue (futureCoding old) (outputModels old)
        ((materialPi old).value (constantFunction.val old)) laterIndex = ∅ := by
  have evaluation := piModel_evaluation displayed identityBody old (futureCoding old) (outputModels old)
    (constantFunction.val old) laterIndex
  have application := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.ConstructiveFamilies.constantFunction_future
    profile positiveGraphs positiveTransport
    Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.emptyDisplayed
      old later futureArrow futureArgument
  exact evaluation.trans ((congrArg (memberModel later).value application).trans
    ((memberModel_value later _).trans
      (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.emptyDisplayed_value
        Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.laterRaw)))

def laterPair : (PowerClassPresheafProducts.IndexedSigma.family displayed identityBody).obj later :=
  ⟨futureArgument,
    Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.emptyDisplayed.val later⟩

theorem materialSigma_later_pair :
    (materialSigma later).value laterPair = HSet.kpair HSet.quineAtom ∅ := by
  have pairValue := sigmaModel_value displayed identityBody later (memberModel later) (fun _ => memberModel later) laterPair
  have firstValue := (memberModel_value later futureArgument).trans
    Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.futureArgument_value
  have secondValue := (memberModel_value later
    (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.emptyDisplayed.val later)).trans
      (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.emptyDisplayed_value
        Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.laterRaw)
  exact pairValue.trans (congrArg₂ HSet.kpair firstValue secondValue)

theorem materialSigma_cyclic_first : HSet.fst ((materialSigma later).value laterPair) = HSet.quineAtom :=
  (congrArg HSet.fst materialSigma_later_pair).trans (HSet.fst_kpair _ _)

theorem materialSigma_empty_second : HSet.snd ((materialSigma later).value laterPair) = ∅ :=
  (congrArg HSet.snd materialSigma_later_pair).trans (HSet.snd_kpair _ _)

def currentEvaluation
    (member : {value : HSet // value ∈ (materialPi old).carrier}) :
    (argument : displayed.obj old) → displayed.obj old :=
  fun argument => ((materialPi old).decode member).app old (𝟙 old) argument

theorem material_current_evaluation_not_injective : ¬ Function.Injective currentEvaluation := by
  intro injective
  let identityMember := (materialPi old).decode.symm (identityFunction.val old)
  let constantMember := (materialPi old).decode.symm (constantFunction.val old)
  have sameCurrent : currentEvaluation identityMember = currentEvaluation constantMember := by
    funext argument
    change ((materialPi old).decode identityMember).app old (𝟙 old) argument =
      ((materialPi old).decode constantMember).app old (𝟙 old) argument
    have first := congrArg (fun function : DependentSection displayed identityBody old =>
      function.app old (𝟙 old) argument) ((materialPi old).decode.apply_symm_apply (identityFunction.val old))
    have second := congrArg (fun function : DependentSection displayed identityBody old =>
      function.app old (𝟙 old) argument) ((materialPi old).decode.apply_symm_apply (constantFunction.val old))
    exact first.trans
      ((Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.current_applications_agree argument).trans
        second.symm)
  exact material_functions_differ (congrArg Subtype.val (injective sameCurrent))

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualMaterialization
