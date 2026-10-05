import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialFamilies
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls

/-!
# Growing constructive observed continuations

The task at index zero gains a new declared continuation at every natural
stage. Index one loops; every higher index is terminal. Observations retain
the index, while an independent Boolean occurrence tag is forgotten. The
bare material interpretation identifies different terminal results, and
the structured interpretation distinguishes them.

The actual generated continuation family is initially empty and later
inhabited. Its dependent body has a member at the cyclic continuation and
none at a terminal continuation. All dictionaries and readouts are the
constructed choice-free ones at their stated universe bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.ConstructiveObservedMaterialControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ConstructiveObservedMaterialInterpretation ConstructiveObservedMaterialFamilies
open PowerClassPresheafDescent.Controls ContextualObservedCoalgebra

abbrev raw := growingSource
abbrev worlds := ContextualObservedCoalgebraControls.worlds
abbrev arrows := ContextualObservedCoalgebraControls.arrows
abbrev atomCoding := ContextualObservedCoalgebraControls.naturalAtoms

def admitted (parent child : Nat) : Prop :=
  (parent = 1 ∧ child = 1) ∨ (parent = 0 ∧ 0 < child)

def dynamics : NaturalHom raw (CoveredFuturePowerFamilies.family raw) where
  app _ argument := CoveredFuturePowerFamilies.ofFull {
    holds := fun future => admitted argument.1.val future.2.1.val
    closed := by
      intro first second step available
      have indexes := congrArg (fun value : raw.obj second.1.1 => value.1.val) step.2
      change first.2.1.val = second.2.1.val at indexes
      exact indexes ▸ available }
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

def atoms (reading : Nat) (state : ContextualCoalgebraLabelledGraph.State raw) : Prop :=
  reading = state.2.1.val

abbrev classes := observedClasses worlds arrows dynamics atoms atomCoding
abbrev projection := observedProjection worlds arrows dynamics atoms atomCoding
abbrev values := readout worlds arrows dynamics
abbrev interpreted := interpretation worlds arrows dynamics atoms atomCoding
abbrev params := parameters worlds arrows dynamics atoms atomCoding
abbrev domain := (continuationCode worlds arrows dynamics atoms atomCoding).decode
abbrev body := (continuationBodyCode worlds arrows dynamics atoms atomCoding).decode

theorem equal_indices_observed (point : Stagesᵒᵖ) (first second : raw.obj point)
    (same : first.1.val = second.1.val) : ObservedBisimilar dynamics atoms point first second := by
  refine ⟨fun _ left right => left.1.val = right.1.val, {
    underlying := {
      stable := fun {_ _} _ {_ _} same => same
      forth := ?_
      back := ?_ }
    atoms := ?_ }, same⟩
  · intro point left right same future child available
    refine ⟨child, ?_, rfl⟩
    change admitted right.1.val child.1.val
    change admitted left.1.val child.1.val at available
    exact same ▸ available
  · intro point left right same future child available
    refine ⟨child, ?_, rfl⟩
    change admitted left.1.val child.1.val
    change admitted right.1.val child.1.val at available
    exact same.symm ▸ available
  · intro point left right same atom
    change atom = left.1.val ↔ atom = right.1.val
    exact same ▸ Iff.rfl

theorem projection_equal_iff (point : Stagesᵒᵖ) (first second : raw.obj point) :
    projection.app point first = projection.app point second ↔ first.1.val = second.1.val := by
  rw [ContextualObservedMaterialFamily.classObservation_eq_iff]
  constructor
  · intro related
    exact (observed_bisimilar_atoms dynamics atoms related first.1.val).mp rfl
  · exact equal_indices_observed point first second

theorem terminal_values_equal (point : Stagesᵒᵖ) (first second : raw.obj point)
    (firstTerminal : 2 ≤ first.1.val) (secondTerminal : 2 ≤ second.1.val) :
    values.app point first = values.app point second := by
  apply (readout_kernel worlds arrows dynamics point first second).mpr
  refine ⟨fun _ left right => 2 ≤ left.1.val ∧ 2 ≤ right.1.val, {
    stable := fun {_ _} _ {_ _} related => related
    forth := ?_
    back := ?_ }, firstTerminal, secondTerminal⟩
  · intro point left right related future child available
    change (left.1.val = 1 ∧ child.1.val = 1) ∨ (left.1.val = 0 ∧ 0 < child.1.val) at available
    rcases available with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega
  · intro point left right related future child available
    change (right.1.val = 1 ∧ child.1.val = 1) ∨ (right.1.val = 0 ∧ 0 < child.1.val) at available
    rcases available with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega

theorem different_results_retained :
    values.app (world 3) (stageValue 3 2 (by omega) false) =
      values.app (world 3) (stageValue 3 3 (by omega) false) ∧
    interpreted.app (world 3) (stageValue 3 2 (by omega) false) ≠
      interpreted.app (world 3) (stageValue 3 3 (by omega) false) := by
  refine ⟨terminal_values_equal _ _ _ (by decide) (by decide), ?_⟩
  intro same
  have indexes := (projection_equal_iff _ _ _).mp (congrArg Prod.fst same)
  exact (by decide : ¬ (2 : Nat) = 3) indexes

theorem duplicate_occurrences_identified (stage index : Nat) (bound : index < stage + 1) :
    interpreted.app (world stage) (stageValue stage index bound false) =
      interpreted.app (world stage) (stageValue stage index bound true) ∧
    stageValue stage index bound false ≠ stageValue stage index bound true := by
  refine ⟨(interpretation_kernel worlds arrows dynamics atoms atomCoding _ _ _).mpr
    (equal_indices_observed _ _ _ rfl), ?_⟩
  exact fun same => Bool.false_ne_true (congrArg Prod.snd same)

def task (stage : Nat) : params.Elements :=
  ⟨⟨world stage⟩, interpreted.app (world stage) (stageValue stage 0 (by omega) false)⟩

def taskStep {first second : Nat} (order : first ≤ second) : task first ⟶ task second :=
  CategoryOfElements.homMk _ _ ⟨(homOfLE order).op.op⟩
    (interpreted.naturality ((homOfLE order).op.op) (stageValue first 0 (by omega) false))

def child (stage index : Nat) (positive : 0 < index) (bound : index < stage + 1) :
    domain.native.obj (task stage) :=
  ⟨⟨projection.app (world stage) (stageValue stage index bound false)⟩,
    (source_continuation_iff worlds arrows dynamics atoms atomCoding _ _ _).mpr
      ⟨stageValue stage index bound false, rfl, Or.inr ⟨rfl, positive⟩⟩⟩

theorem child_eq_iff (stage first second : Nat) (firstPos : 0 < first) (secondPos : 0 < second)
    (firstBound : first < stage + 1) (secondBound : second < stage + 1) :
    child stage first firstPos firstBound = child stage second secondPos secondBound ↔ first = second := by
  constructor
  · intro same
    exact (projection_equal_iff _ _ _).mp (congrArg (fun value => value.val.down) same)
  · intro same
    cases same
    rfl

theorem initial_continuations_empty : ¬ Nonempty (domain.native.obj (task 0)) := by
  rintro ⟨candidate⟩
  obtain ⟨original, _, available⟩ :=
    (source_class_continuation_iff worlds arrows dynamics atoms atomCoding _ _ _).mp candidate.property
  have bound := original.1.isLt
  change original.1.val < 1 at bound
  change (0 = 1 ∧ original.1.val = 1) ∨ (0 = 0 ∧ 0 < original.1.val) at available
  rcases available with ⟨impossible, _⟩ | ⟨_, positive⟩ <;> omega

theorem continuation_family_grows (stage : Nat) :
    ¬ ∃ original : domain.native.obj (task stage),
      domain.native.map (taskStep (Nat.le_succ stage)) original =
        child (stage + 1) (stage + 1) (Nat.succ_pos stage) (by omega) := by
  rintro ⟨original, same⟩
  obtain ⟨argument, reads, _⟩ :=
    (source_class_continuation_iff worlds arrows dynamics atoms atomCoding _ _ _).mp original.property
  have classSame := congrArg (fun value => value.val.down) same
  change classes.map ((homOfLE (Nat.le_succ stage)).op.op) original.val.down = _ at classSame
  rw [← reads] at classSame
  have sourceSame := (projection.naturality ((homOfLE (Nat.le_succ stage)).op.op) argument).symm.trans classSame
  have indexes := (projection_equal_iff _ _ _).mp sourceSame
  have bound := argument.1.isLt
  change argument.1.val = stage + 1 at indexes
  change argument.1.val < stage + 1 at bound
  omega

def cyclicChild : domain.native.obj (task 2) := child 2 1 (by omega) (by omega)
def terminalChild : domain.native.obj (task 2) := child 2 2 (by omega) (by omega)

def cyclicBodyMember : body.native.obj ⟨(task 2).1, ⟨(task 2).2, cyclicChild⟩⟩ :=
  ⟨⟨projection.app (world 2) (stageValue 2 1 (by omega) false)⟩,
    (source_continuation_iff worlds arrows dynamics atoms atomCoding _ _ _).mpr
      ⟨stageValue 2 1 (by omega) false, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem terminal_body_empty : ¬ Nonempty (body.native.obj ⟨(task 2).1, ⟨(task 2).2, terminalChild⟩⟩) := by
  rintro ⟨candidate⟩
  obtain ⟨original, _, available⟩ :=
    (source_class_continuation_iff worlds arrows dynamics atoms atomCoding _ _ _).mp candidate.property
  change (2 = 1 ∧ original.1.val = 1) ∨ (2 = 0 ∧ 0 < original.1.val) at available
  rcases available with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega

theorem dependent_body_varies :
    Nonempty (body.native.obj ⟨(task 2).1, ⟨(task 2).2, cyclicChild⟩⟩) ∧
      ¬ Nonempty (body.native.obj ⟨(task 2).1, ⟨(task 2).2, terminalChild⟩⟩) :=
  ⟨⟨cyclicBodyMember⟩, terminal_body_empty⟩

end Mettapedia.GSLT.ConstructiveObservedMaterialControls
