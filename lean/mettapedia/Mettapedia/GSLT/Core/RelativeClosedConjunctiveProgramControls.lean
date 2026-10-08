import Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgramAdjunction
import Mettapedia.GSLT.Core.RelativeClosedProgramReductionExtensionControls

/-!
# A nontrivial program construction monad and complete event folding

The program-theory construction strictly enlarges an independently supplied
Boolean-order theory and changes its actual constant-top map. This follows
from complete semantic separators, not from raw vocabulary alone.

For a separate nonconstant reduction graph, the actual multiplication and
unit event maps compose to the complete original event under their earned
comparison. Its independent Boolean interpretation retains false as source
and true as target. The second conjunction folds both supplied Boolean
inputs and is neither an argument projection nor constant truth.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedConjunctiveProgramControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory
open RelativeClosedConjunctiveProgram HomEquivalence FreeForgetful

def diagonal : (true : Bool) ⟶ true ⨯ true := prod.lift (𝟙 true) (𝟙 true)

instance diagonal_mono : Mono diagonal := by
  change Mono (prod.lift (𝟙 true) (𝟙 true))
  infer_instance

abbrev sourceTheory : ProgramReductionTheory.Theory.{0,0} where
  closed := LambdaTheoryStructuredControls.boolTheory
  program := true
  reduction := Subobject.mk diagonal

abbrev sourceClass := ProgramReductionTheoryIsoClasses.of sourceTheory
abbrev generated := freeObject sourceTheory

def topMap : ProgramReductionTheory.Map sourceTheory sourceTheory where
  closed := LambdaTheoryStructuredControls.topMap
  program := Iso.refl true
  reduction := (Subobject.underlyingIso diagonal).inv
  source := Subsingleton.elim _ _
  target := Subsingleton.elim _ _

def topExtension : ConjunctiveProgramTheory.Map generated generated :=
  extension sourceTheory generated (ProgramReductionTheory.Map.compose topMap (unitMap sourceTheory))

theorem actual_free_action_is_nonidentity :
    free.map (ProgramReductionTheoryIsoClasses.classOf topMap) ≠ 𝟙 generated := by
  change ConjunctiveProgramTheory.classOf topExtension ≠
    ConjunctiveProgramTheory.classOf (ConjunctiveProgramTheory.Map.identity generated)
  intro same
  obtain ⟨comparison⟩ := (ConjunctiveProgramTheory.classOf_equal_iff _ _).mp same
  exact RelativeClosedConjunctiveAdjunctionControls.top_extension_has_no_identity_comparison
    ⟨comparison.comparison⟩

theorem monad_object_is_not_isomorphic_to_the_old_program_theory :
    ¬ Nonempty (Construction.monad.obj sourceClass ≅ sourceClass) := by
  rintro ⟨comparison⟩
  exact RelativeClosedConjunctiveAdjunctionControls.monad_object_is_not_isomorphic_to_the_old_theory
    ⟨ProgramReductionTheoryIsoClasses.forget.mapIso comparison⟩

theorem program_construction_is_not_identity_up_to_natural_isomorphism :
    ¬ Nonempty (Construction.monad.toFunctor ≅ 𝟭 ProgramReductionTheoryIsoClasses.{0}) := by
  rintro ⟨comparison⟩
  exact monad_object_is_not_isomorphic_to_the_old_program_theory ⟨comparison.app sourceClass⟩

abbrev multiplication := Construction.multiplicationMap sourceClass
abbrev firstDiagram := RelativeClosedConjunctiveAdjunctionControls.firstDiagram
abbrev foldDiagram := multiplication.closed.functor ⋙ firstDiagram
abbrev second := freeObject generated.programTheory

theorem underlying_fold_functor : multiplication.closed.functor =
    RelativeClosedConjunctiveAdjunctionControls.multiplication.functor := rfl

def foldedConjunction : ULift.{0} Bool × ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom RelativeClosedConjunctiveAdjunctionControls.fold_product_read.symm ≫
    foldDiagram.map second.operations.conjunction ≫
      eqToHom RelativeClosedConjunctiveAdjunctionControls.fold_proposition_read

theorem complete_fold_read : foldedConjunction = RelativeClosedConjunctiveControls.boolean.conjunction :=
  RelativeClosedConjunctiveAdjunctionControls.complete_fold_conjunction

theorem fold_retains_both_supplied_inputs :
    (foldedConjunction (ULift.up true, ULift.up false)).down = false ∧
      (foldedConjunction (ULift.up false, ULift.up true)).down = false ∧
      (foldedConjunction (ULift.up true, ULift.up true)).down = true := by
  rw [complete_fold_read]
  exact ⟨rfl, rfl, rfl⟩

theorem fold_is_neither_first_projection_nor_constant_truth :
    foldedConjunction ≠ RelativeClosedConjunctiveControls.projecting.conjunction ∧
      foldedConjunction ≠ RelativeClosedConjunctiveControls.boolean.top (ULift.{0} Bool × ULift.{0} Bool) := by
  constructor
  · intro same
    have actual := congrArg (fun arrow : ULift.{0} Bool × ULift.{0} Bool ⟶ ULift.{0} Bool =>
      (arrow (ULift.up true, ULift.up false)).down) same
    exact Bool.false_ne_true (fold_retains_both_supplied_inputs.1.symm.trans actual)
  · intro same
    have actual := congrArg (fun arrow : ULift.{0} Bool × ULift.{0} Bool ⟶ ULift.{0} Bool =>
      (arrow (ULift.up true, ULift.up false)).down) same
    exact Bool.false_ne_true (fold_retains_both_supplied_inputs.1.symm.trans actual)

abbrev graphSource := RelativeClosedProgramReductionExtensionControls.sourceTheory
abbrev graphClass := ProgramReductionTheoryIsoClasses.of graphSource
abbrev graphGenerated := freeObject graphSource
abbrev graphMultiplication := Construction.multiplicationMap graphClass
abbrev graphBaseComparison := Construction.multiplication_base_comparison graphClass

def completeFoldedEvent : graphGenerated.programTheory.Event ⟶ graphGenerated.programTheory.Event :=
  graphBaseComparison.comparison.inv.app graphGenerated.programTheory.Event ≫
    graphMultiplication.closed.functor.map (unitMap graphGenerated.programTheory).reduction ≫
      graphMultiplication.reduction

theorem complete_event_roundtrip : completeFoldedEvent = 𝟙 graphGenerated.programTheory.Event := by
  have retained : graphBaseComparison.comparison.hom.app graphGenerated.programTheory.Event =
      graphMultiplication.closed.functor.map (unitMap graphGenerated.programTheory).reduction ≫
        graphMultiplication.reduction :=
    (Category.comp_id _).symm.trans (Construction.retains_complete_event graphClass)
  exact (congrArg
    (fun arrow => graphBaseComparison.comparison.inv.app graphGenerated.programTheory.Event ≫ arrow)
    retained.symm).trans
      (Iso.inv_hom_id_app graphBaseComparison.comparison graphGenerated.programTheory.Event)

abbrev graphDiagram := RelativeClosedProgramReductionExtensionControls.diagram

def foldedSource : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom RelativeClosedProgramReductionExtensionControls.program_read.symm ≫
    graphDiagram.map (RelativeClosedProgramReductionExtensionControls.retainedEvent ≫
      completeFoldedEvent ≫ graphGenerated.programTheory.source) ≫
        eqToHom RelativeClosedProgramReductionExtensionControls.program_read

def foldedTarget : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom RelativeClosedProgramReductionExtensionControls.program_read.symm ≫
    graphDiagram.map (RelativeClosedProgramReductionExtensionControls.retainedEvent ≫
      completeFoldedEvent ≫ graphGenerated.programTheory.target) ≫
        eqToHom RelativeClosedProgramReductionExtensionControls.program_read

theorem folded_source_read : foldedSource = RelativeClosedProgramReductionExtensionControls.decodedSource := by
  have reading : completeFoldedEvent ≫ graphGenerated.programTheory.source =
      graphGenerated.programTheory.source :=
    (congrArg (fun arrow : graphGenerated.programTheory.Event ⟶ graphGenerated.programTheory.Event =>
      arrow ≫ graphGenerated.programTheory.source) complete_event_roundtrip).trans
        (Category.id_comp graphGenerated.programTheory.source)
  exact congrArg
    (fun arrow : graphGenerated.programTheory.Event ⟶ graphGenerated.programTheory.program =>
      eqToHom RelativeClosedProgramReductionExtensionControls.program_read.symm ≫
        graphDiagram.map (RelativeClosedProgramReductionExtensionControls.retainedEvent ≫ arrow) ≫
          eqToHom RelativeClosedProgramReductionExtensionControls.program_read) reading

theorem folded_target_read : foldedTarget = RelativeClosedProgramReductionExtensionControls.decodedTarget := by
  have reading : completeFoldedEvent ≫ graphGenerated.programTheory.target =
      graphGenerated.programTheory.target :=
    (congrArg (fun arrow : graphGenerated.programTheory.Event ⟶ graphGenerated.programTheory.Event =>
      arrow ≫ graphGenerated.programTheory.target) complete_event_roundtrip).trans
        (Category.id_comp graphGenerated.programTheory.target)
  exact congrArg
    (fun arrow : graphGenerated.programTheory.Event ⟶ graphGenerated.programTheory.program =>
      eqToHom RelativeClosedProgramReductionExtensionControls.program_read.symm ≫
        graphDiagram.map (RelativeClosedProgramReductionExtensionControls.retainedEvent ≫ arrow) ≫
          eqToHom RelativeClosedProgramReductionExtensionControls.program_read) reading

theorem actual_monad_fold_retains_nonconstant_program_endpoints :
    (foldedSource (ULift.up false)).down = false ∧
      (foldedTarget (ULift.up false)).down = true ∧
      (foldedSource (ULift.up true)).down = true ∧
      (foldedTarget (ULift.up true)).down = true := by
  rw [folded_source_read, folded_target_read]
  exact RelativeClosedProgramReductionExtensionControls.complete_supplied_endpoints

theorem folded_target_cannot_be_replaced_by_its_source : foldedTarget ≠ foldedSource := by
  rw [folded_target_read, folded_source_read]
  exact RelativeClosedProgramReductionExtensionControls.complete_target_is_not_identity

end Mettapedia.GSLT.Core.RelativeClosedConjunctiveProgramControls
