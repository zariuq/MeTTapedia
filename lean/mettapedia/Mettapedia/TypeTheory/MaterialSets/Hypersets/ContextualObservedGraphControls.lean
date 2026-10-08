import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphFamilies
import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialControls

/-!
# The actual growing observed execution in the joint graph universe

The existing authored dynamics has a task state, a cyclic continuation,
terminal results and retained duplicate source occurrences. Its actual
observed continuation family is decoded into contextual graph receipts.
The receipts grow at every stage, and the second continuation family
distinguishes cyclic and terminal children.

Declared result classes survive the literal readout. Successor-only
material matching can still equate distinct terminal results; these are
two different readout contracts, not an implicit identification.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphControls

open CategoryTheory Mettapedia.GSLT
open ContextualGraphDiagrams ContextualRealizedGraphs
open ConstructiveObservedMaterialControls
open PowerClassPresheafDescent.Controls

abbrev modelReadout := ContextualObservedGraphFamilies.readout worlds arrows dynamics atoms atomCoding
abbrev receiptFamily := ContextualObservedGraphFamilies.successors worlds arrows dynamics atoms atomCoding
abbrev comparison := ContextualObservedGraphFamilies.continuationEquiv worlds arrows dynamics atoms atomCoding
abbrev classSource := ConstructiveObservedMaterialInterpretation.observedCoalgebra worlds arrows dynamics atoms atomCoding

def childReceipt (stage index : Nat) (positive : 0 < index) (bound : index < stage+1) :
    receiptFamily.obj (task stage) := comparison (task stage) (child stage index positive bound)

theorem initial_receipts_empty : ¬ Nonempty (receiptFamily.obj (task 0)) := by
  rintro ⟨receipt⟩
  exact initial_continuations_empty ⟨(comparison (task 0)).symm receipt⟩

theorem receipts_grow (stage : Nat) :
    ¬ ∃ previous : receiptFamily.obj (task stage),
      receiptFamily.map (taskStep (Nat.le_succ stage)) previous =
        childReceipt (stage+1) (stage+1) (Nat.succ_pos stage) (by omega) := by
  rintro ⟨previous, same⟩
  apply continuation_family_grows stage
  refine ⟨(comparison (task stage)).symm previous, ?_⟩
  apply (comparison (task (stage+1))).injective
  exact (ContextualObservedGraphFamilies.continuation_transport worlds arrows dynamics atoms atomCoding
    (taskStep (Nat.le_succ stage)) ((comparison (task stage)).symm previous)).trans
      ((congrArg (receiptFamily.map (taskStep (Nat.le_succ stage)))
        ((comparison (task stage)).apply_symm_apply previous)).trans same)

def childMembership (stage index : Nat) (positive : 0 < index) (bound : index < stage+1) :
    Member ((ContextualObservedGraphDiagram.pointing classSource).app (world stage)
        (childReceipt stage index positive bound).val)
      ((ContextualObservedGraphDiagram.pointing classSource).app (world stage) (task stage).2.1) :=
  ContextualObservedGraphFamilies.member worlds arrows dynamics atoms atomCoding
    (task stage) (childReceipt stage index positive bound)

def childPoint (child : domain.native.obj (task 2)) : params.Elements :=
  ⟨(task 2).1,
    (ConstructiveObservedMaterialFamilies.childParameter worlds arrows dynamics atoms atomCoding).app
      (task 2).1 ⟨(task 2).2, child⟩⟩

def cyclicGrandchild : receiptFamily.obj (childPoint cyclicChild) :=
  comparison (childPoint cyclicChild) cyclicBodyMember

theorem terminal_grandchildren_empty : ¬ Nonempty (receiptFamily.obj (childPoint terminalChild)) := by
  rintro ⟨receipt⟩
  exact terminal_body_empty ⟨(comparison (childPoint terminalChild)).symm receipt⟩

theorem actual_dependent_body_varies :
    Nonempty (receiptFamily.obj (childPoint cyclicChild)) ∧
      ¬ Nonempty (receiptFamily.obj (childPoint terminalChild)) :=
  ⟨⟨cyclicGrandchild⟩, terminal_grandchildren_empty⟩

def wholeSections := ContextualObservedGraphFamilies.sections worlds arrows dynamics atoms atomCoding

theorem whole_sections_roundtrip (term : domain.native.sections) :
    wholeSections.symm (wholeSections term) = term := wholeSections.symm_apply_apply term

theorem no_terminal_member {point target : Stagesᵒᵖ} (arrival : point ⟶ target)
    (parent : raw.obj point) (terminal : 2 ≤ parent.1.val) (value : Value Stagesᵒᵖ target) :
    ¬ Nonempty (Member value (move Stagesᵒᵖ arrival (modelReadout.app point parent))) := by
  rintro ⟨member⟩
  have current := member.1.property
  change (classSource.app target (classes.map arrival (projection.app point parent))).val.holds
    (CoveredFuturePowerFamilies.current classes target member.1.val) at current
  rw [projection.naturality] at current
  obtain ⟨original, _, available⟩ :=
    (ConstructiveObservedMaterialFamilies.source_class_continuation_iff worlds arrows dynamics atoms atomCoding
      target (raw.map arrival parent) member.1.val).mp current
  change admitted parent.1.val original.1.val at available
  rcases available with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega

def terminalMatching {point : Stagesᵒᵖ} (first second : raw.obj point)
    (firstTerminal : 2 ≤ first.1.val) (secondTerminal : 2 ≤ second.1.val) :
    Equal (modelReadout.app point first) (modelReadout.app point second) :=
  extensionality
    (fun _ arrival value proof => False.elim (no_terminal_member arrival first firstTerminal value ⟨proof⟩))
    (fun _ arrival value proof => False.elim (no_terminal_member arrival second secondTerminal value ⟨proof⟩))

theorem terminal_results_literal_distinct :
    modelReadout.app (world 3) (stageValue 3 2 (by omega) false) ≠
      modelReadout.app (world 3) (stageValue 3 3 (by omega) false) := by
  intro same
  have related := (ContextualObservedGraphFamilies.literal_kernel worlds arrows dynamics atoms atomCoding
    (world 3) (stageValue 3 2 (by omega) false) (stageValue 3 3 (by omega) false)).mp same
  have impossible := (ContextualObservedCoalgebra.observed_bisimilar_atoms dynamics atoms related 2).mp rfl
  exact (by decide : ¬ (2 : Nat) = 3) impossible

theorem terminal_readouts_have_different_kernels :
    Nonempty (Equal (modelReadout.app (world 3) (stageValue 3 2 (by omega) false))
      (modelReadout.app (world 3) (stageValue 3 3 (by omega) false))) ∧
      modelReadout.app (world 3) (stageValue 3 2 (by omega) false) ≠
        modelReadout.app (world 3) (stageValue 3 3 (by omega) false) :=
  ⟨⟨terminalMatching _ _ (by decide) (by decide)⟩, terminal_results_literal_distinct⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphControls
