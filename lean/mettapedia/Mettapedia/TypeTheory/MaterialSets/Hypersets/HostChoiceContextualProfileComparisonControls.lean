import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualAntiFoundationComparison
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotientControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretationControls

/-!
# Infinite and varying controls for contextual profile comparisons

Infinitely many actual root occurrences picture one member. Their genuine
symmetry changes dependent occurrence transport while leaving the actual
internal set reading unchanged. Infinite declared results are separated by
their complete future histories even though their present children agree.

A second construction has no present members before its declared threshold,
then acquires the embedded Quine atom. Present accessibility can therefore
fail after an actual context map. Persistent accessibility excludes that
value, and the original material natural ordinals give infinite positive
controls. The unfolding criterion example is a graph-level comparison,
not an alternative set-universe construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualProfileComparisonControls

open _root_.CategoryTheory AccessiblePointedGraph
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.GroupoidIdentityElimination
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualObserverComparison HostChoiceContextualAntiFoundationComparison

universe u
variable {D : Type u} [Category.{u} D]

namespace InfiniteOccurrences

def graph (child : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  sup fun _ : ULift.{u,0} Nat => child

def occurrence (child : AccessiblePointedGraph.{u}) (number : Nat) : Occurrence (graph child) :=
  ⟨some ⟨ULift.up number, child.point⟩, SupEdge.point (ULift.up number)⟩

theorem occurrence_injective (child : AccessiblePointedGraph.{u}) :
    Function.Injective (occurrence child) := by
  intro first second same
  have nodes := congrArg Subtype.val same
  have pairs := Option.some.inj nodes
  exact congrArg (fun pair : Σ _ : ULift.{u,0} Nat, child.Node => pair.1.down) pairs

theorem occurrence_picture (child : AccessiblePointedGraph.{u}) (number : Nat) :
    (occurrence child number).picture = HSet.mk child :=
  (HSet.mk_repoint _ _).symm.trans (HSet.sound (repoint_sup_equiv (ULift.up number)))

def interchange : ULift.{u,0} Nat ≃ ULift.{u,0} Nat where
  toFun value := ⟨match value.down with | 0 => 1 | 1 => 0 | n+2 => n+2⟩
  invFun value := ⟨match value.down with | 0 => 1 | 1 => 0 | n+2 => n+2⟩
  left_inv value := by
    rcases value with ⟨number⟩
    cases number with
    | zero => rfl
    | succ number => cases number <;> rfl
  right_inv value := by
    rcases value with ⟨number⟩
    cases number with
    | zero => rfl
    | succ number => cases number <;> rfl

def symmetry (child : AccessiblePointedGraph.{u}) : PresentationIso (graph child) (graph child) :=
  PresentationIdentityControls.constantSupIso child interchange

theorem symmetry_moves (child : AccessiblePointedGraph.{u}) :
    (symmetry child).occurrenceTransport (occurrence child 0) = occurrence child 1 := rfl

theorem symmetry_not_reflexivity (child : AccessiblePointedGraph.{u}) :
    symmetry child ≠ PresentationIso.refl (graph child) := by
  intro same
  have applied := congrArg (fun path : PresentationIso (graph child) (graph child) =>
    path.occurrenceTransport (occurrence child 0)) same
  exact Nat.zero_ne_one ((occurrence_injective child applied).symm)

theorem material_member_reading_constant (point : D) (child : AccessiblePointedGraph.{u}) (number : Nat) :
    (HostChoiceContextualObserverComparison.occurrenceMember point (graph child) (occurrence child number)).val =
      HostChoiceContextualSetInfinity.reading.app point (HSet.mk child) :=
  congrArg (HostChoiceContextualSetInfinity.reading.app point) (occurrence_picture child number)

theorem reading_not_injective (point : D) (child : AccessiblePointedGraph.{u}) :
    ¬ Function.Injective ((HostChoiceContextualObserverComparison.occurrenceReading point).app (graph child)) := by
  intro injective
  have same : (HostChoiceContextualObserverComparison.occurrenceReading point).app (graph child)
      (ULift.up (occurrence child 0)) =
      (HostChoiceContextualObserverComparison.occurrenceReading point).app (graph child)
        (ULift.up (occurrence child 1)) :=
    Subtype.ext ((material_member_reading_constant point child 0).trans
      (material_member_reading_constant point child 1).symm)
  exact Nat.zero_ne_one (occurrence_injective child (congrArg ULift.down (injective same)))

theorem no_natural_occurrence_descent (point : D) (child : AccessiblePointedGraph.{u}) :
    ¬ ∃ family : Discrete (sets.obj point) ⥤ Type (u+1),
      Nonempty (MaterialIdentityObservation.NaturalEquivalence MaterialIdentityObservation.liftedOccurrences
        (compose (graphReadout point) family)) :=
  no_occurrence_descent_of_moved point (symmetry child) (occurrence child 0)
    (fun same => Nat.zero_ne_one ((occurrence_injective child same).symm))

theorem basedJ_distinguishes_symmetry (child : AccessiblePointedGraph.{u}) :
    basedJ occurrenceMotive (occurrence child 0) (symmetry child) ≠
      basedJ occurrenceMotive (occurrence child 0) (PresentationIso.refl (graph child)) := by
  intro same
  exact Nat.zero_ne_one ((occurrence_injective child same).symm)

theorem actual_identity_comparison_not_faithful (point : D) :
    ¬ (identityComparison point).Faithful := by
  intro faithful
  exact symmetry_not_reflexivity empty
    (@faithful (graph empty) (graph empty) (symmetry empty) (PresentationIso.refl _)
      (Subsingleton.elim _ _))

end InfiniteOccurrences

namespace InfiniteResults

open ContextualCoalgebraQuotientControls.Results LabelledContextPaths

theorem actual_set_results_injective :
    Function.Injective (fun tag => (observe coalgebra).app initial (result tag)) := by
  intro first second same
  exact (result_bisimilar_iff first second).mp ((observe_kernel coalgebra initial _ _).mp same)

theorem same_present_distinct_actual_values :
    (∀ child, ¬ (coalgebra.app initial (result 0)).val.holds
      (CoveredFuturePowerFamilies.current states initial child)) ∧
    (∀ child, ¬ (coalgebra.app initial (result 1)).val.holds
      (CoveredFuturePowerFamilies.current states initial child)) ∧
    (observe coalgebra).app initial (result 0) ≠ (observe coalgebra).app initial (result 1) :=
  ⟨no_present_children 0, no_present_children 1,
    fun same => Nat.zero_ne_one (actual_set_results_injective same)⟩

theorem declared_result_consumer_exists :
    ∃ consumer : NaturalHom states (classes coalgebra), Behavioral coalgebra consumer ∧
      consumer.app initial (result 0) ≠ consumer.app initial (result 1) := by
  refine ⟨classProjection coalgebra, ?_, ?_⟩
  · intro point first second related
    exact Quotient.sound ((observe_kernel coalgebra point first second).mpr related)
  · intro same
    exact declared_results_not_bisimilar
      ((observe_kernel coalgebra initial _ _).mp
        ((Mettapedia.TypeTheory.ContextualKernelQuotients.projection_eq_iff
          (observe coalgebra) initial _ _).mp same))

end InfiniteResults

namespace WellFoundedBoundary

noncomputable def cyclic (point : D) : sets.obj point :=
  HostChoiceContextualSetInfinity.reading.app point HSet.quineAtom

theorem cyclic_self_member (point : D) : Member point (cyclic point) (cyclic point) :=
  (HostChoiceContextualSetInfinity.reading_material_member point _ _).mpr HSet.quineAtom_mem_self

theorem cyclic_not_wellFounded (point : D) : ¬ ContextualWF point (cyclic point) :=
  Mettapedia.TypeTheory.MaterialSets.not_acc_of_rel_self (cyclic_self_member point)

theorem embedded_ordinals_persistent (point : D) (number : Nat) :
    PersistentWF point (HostChoiceContextualSetInfinity.ordinal point number) :=
  (persistentWF_reading_iff point _).mpr (NaturalOrdinalModel.ordinal_wellFounded number)

theorem infinitely_many_persistent_values (point : D) :
    Function.Injective (fun number =>
      (⟨HostChoiceContextualSetInfinity.ordinal point number,
        embedded_ordinals_persistent point number⟩ : {value : sets.obj point // PersistentWF point value})) := by
  intro first second same
  exact HostChoiceContextualSetInfinity.ordinal_injective point (congrArg Subtype.val same)

theorem no_global_membership_induction (point : D) :
    ¬ (∀ predicate : sets.obj point → Prop,
      (∀ parent, (∀ child, Member point child parent → predicate child) → predicate parent) →
        ∀ value, predicate value) := by
  intro induction
  have allAccessible := induction (ContextualWF point) (fun parent children => Acc.intro parent children)
  exact cyclic_not_wellFounded point (allAccessible (cyclic point))

theorem no_distinct_natural_futureQuines (point : D)
    (first second : (sets (D := D)).sections) (firstLaw : FutureQuine first) (secondLaw : FutureQuine second) :
    first.val point = second.val point :=
  congrArg (fun value : (sets (D := D)).sections => value.val point)
    ((futureQuine_unique first firstLaw).trans (futureQuine_unique second secondLaw).symm)

end WellFoundedBoundary

namespace LaterCycles

open CoveredFuturePowerFamilies PowerClassPresheafDescent.Controls

abbrev values := sets (D := Stagesᵒᵖ)

noncomputable def predicate (threshold : Nat) (point : Stagesᵒᵖ) : Predicate values point where
  holds argument := threshold ≤ stageIndex argument.1.1 ∧ argument.2 = WellFoundedBoundary.cyclic argument.1.1
  closed {first second} move available := by
    have natural : values.map move.1.1 (WellFoundedBoundary.cyclic first.1.1) =
        WellFoundedBoundary.cyclic second.1.1 :=
      HostChoiceContextualSetInfinity.reading.naturality move.1.1 HSet.quineAtom
    exact ⟨available.1.trans (growthLe move.1.1),
      move.2.symm.trans ((congrArg (values.map move.1.1) available.2).trans natural)⟩

noncomputable def enumeration (threshold : Nat) (point : Stagesᵒᵖ) : Enumeration (predicate threshold point) where
  Carrier future := {_unit : PUnit.{1} // threshold ≤ stageIndex future.1}
  value future _ := WellFoundedBoundary.cyclic future.1
  covered _ _ := ⟨fun ⟨later, same⟩ => ⟨⟨PUnit.unit, later⟩, same.symm⟩,
    fun ⟨receipt, same⟩ => ⟨receipt.property, same.symm⟩⟩

noncomputable def power (threshold : Nat) (point : Stagesᵒᵖ) : Power values point :=
  ⟨predicate threshold point, ⟨enumeration threshold point⟩⟩

theorem power_restrict (threshold : Nat) {point target : Stagesᵒᵖ} (arrow : point ⟶ target) :
    restrictPower values arrow (power threshold point) = power threshold target := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

noncomputable def late (threshold : Nat) : values.sections :=
  assemble.mapSection ⟨power threshold, fun arrow => power_restrict threshold arrow⟩

theorem late_future (threshold : Nat) {point target : Stagesᵒᵖ} (arrow : point ⟶ target)
    (child : values.obj target) :
    FutureMember arrow child ((late threshold).val point) ↔
      threshold ≤ stageIndex target ∧ child = WellFoundedBoundary.cyclic target := by
  change (unfold.app point (assemble.app point (power threshold point))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem late_current (threshold : Nat) (point : Stagesᵒᵖ) (child : values.obj point) :
    Member point child ((late threshold).val point) ↔
      threshold ≤ stageIndex point ∧ child = WellFoundedBoundary.cyclic point :=
  late_future threshold (𝟙 point) child

theorem late_wellFounded_iff (threshold : Nat) (point : Stagesᵒᵖ) :
    ContextualWF point ((late threshold).val point) ↔ ¬ threshold ≤ stageIndex point := by
  constructor
  · intro accessible admitted
    exact WellFoundedBoundary.cyclic_not_wellFounded point
      (Acc.inv accessible ((late_current threshold point _).mpr ⟨admitted, rfl⟩))
  · intro absent
    exact Acc.intro _ fun child belongs =>
      (absent ((late_current threshold point child).mp belongs).1).elim

theorem accessible_present_inaccessible_future :
    ContextualWF (world 0) ((late 1).val (world 0)) ∧
      ¬ ContextualWF (world 1)
        (values.map ContextualMaterialCoalgebraControls.firstAdvance ((late 1).val (world 0))) := by
  constructor
  · exact (late_wellFounded_iff 1 (world 0)).mpr (Nat.not_succ_le_zero 0)
  · have natural := (late 1).property ContextualMaterialCoalgebraControls.firstAdvance
    rw [natural]
    exact fun accessible => (late_wellFounded_iff 1 (world 1)).mp accessible (Nat.le_refl 1)

theorem late_not_persistent : ¬ PersistentWF (world 0) ((late 1).val (world 0)) :=
  fun persistent => accessible_present_inaccessible_future.2
    (persistent (world 1) ContextualMaterialCoalgebraControls.firstAdvance)

theorem late_outside_bare_material_image :
    ¬ ∃ material : HSet, HostChoiceContextualSetInfinity.reading.app (world 0) material =
      (late 1).val (world 0) := by
  rintro ⟨material, same⟩
  have accessible := (wellFounded_reading_iff (world 0) material).mp
    (same.symm ▸ accessible_present_inaccessible_future.1)
  exact late_not_persistent (same ▸ (persistentWF_reading_iff (world 0) material).mpr accessible)

theorem late_ne_empty : (late 1).val (world 0) ≠ emptySet.val (world 0) := by
  intro same
  exact late_outside_bare_material_image
    ⟨∅, (HostChoiceContextualSetInfinity.reading_empty (world 0)).trans same.symm⟩

/-- Ordinary bisimulation of the present membership graph is too coarse
on the contextual carrier: both roots are childless now and differ later. -/
theorem present_bisimilar_but_values_distinct :
    Bisimilar (fun parent child => Member (world 0) child parent)
      (fun parent child => Member (world 0) child parent)
      ((late 1).val (world 0)) (emptySet.val (world 0)) ∧
      (late 1).val (world 0) ≠ emptySet.val (world 0) := by
  refine ⟨⟨fun first second => first = (late 1).val (world 0) ∧ second = emptySet.val (world 0),
    ?_, rfl, rfl⟩, late_ne_empty⟩
  rintro first second ⟨rfl, rfl⟩
  constructor
  · intro child available
    exact (Nat.not_succ_le_zero 0 ((late_current 1 (world 0) child).mp available).1).elim
  · intro child available
    exact (member_empty (world 0) child available).elim

theorem present_membership_not_strongly_extensional :
    ¬ Mettapedia.SetTheory.AntiFoundation.StronglyExtensional
      (fun parent child => Member (world 0) child parent) := by
  intro strong
  obtain ⟨relation, bisimulation, related⟩ := present_bisimilar_but_values_distinct.1
  exact late_ne_empty (strong relation bisimulation _ _ related)

def advanceTo (stage : Nat) : world 0 ⟶ world stage := (homOfLE (Nat.zero_le stage)).op.op

theorem late_values_injective : Function.Injective (fun threshold => (late threshold).val (world 0)) := by
  intro first second same
  have thresholds : ∀ stage : Nat, first ≤ stage ↔ second ≤ stage := by
    intro stage
    have firstNatural := (late first).property (advanceTo stage)
    have secondNatural := (late second).property (advanceTo stage)
    have futureSame := firstNatural.symm.trans ((congrArg (values.map (advanceTo stage)) same).trans secondNatural)
    have members : Member (world stage) (WellFoundedBoundary.cyclic (world stage))
        ((late first).val (world stage)) ↔
        Member (world stage) (WellFoundedBoundary.cyclic (world stage))
          ((late second).val (world stage)) := by rw [futureSame]
    exact ((late_current first (world stage) _).trans (and_iff_left rfl)).symm.trans
      (members.trans ((late_current second (world stage) _).trans (and_iff_left rfl)))
  exact Nat.le_antisymm ((thresholds second).mpr (Nat.le_refl second))
    ((thresholds first).mp (Nat.le_refl first))

end LaterCycles

namespace AlternativeIdentification

open UnfoldingIdentityComparison

theorem rooted_unfolding_criterion_does_not_supply_injective_actual_decoration (point : D) :
    ScottExtensional UnaryBinary.edge.{u} ∧
      ¬ Function.Injective ((decoration UnaryBinary.edge).app point) := by
  refine ⟨UnaryBinary.scottExtensional, ?_⟩
  intro injective
  exact Bool.noConfusion (congrArg ULift.down
    (injective ((decoration_kernel UnaryBinary.edge point (ULift.up true) (ULift.up false)).mpr
      (UnaryBinary.all_nodes_bisimilar _ _))))

end AlternativeIdentification

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualProfileComparisonControls
