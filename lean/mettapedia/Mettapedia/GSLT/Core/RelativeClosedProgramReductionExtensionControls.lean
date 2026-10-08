import Mettapedia.CategoryTheory.RelativeClosedProgramReductionExtension
import Mettapedia.GSLT.Core.RelativeClosedConjunctiveAdjunctionControls

/-!
# Complete reductions and selected positions through a generated extension

The source is a genuine generated closed theory with a nonconstant program
object. Its reduction relation is the graph of the independently interpreted
truth operation. The extension preserves the complete event, source and
target. An independent Boolean interpretation retains the supplied source
value and returns truth, excluding an identity target interpretation.

A selected position retains two independently supplied context readings.
Duplicate authored occurrences remain distinct even when their monic endpoint
readout agrees.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedProgramReductionExtensionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory
open ProgramReductionTheory
open RelativeClosedConjunctive
open RelativeClosedConjunctive.HomEquivalence
open RelativeClosedProgramReductionExtension

abbrev old := RelativeClosedConjunctiveAdjunctionControls.generated
abbrev program := old.operations.proposition
abbrev truthTarget := old.operations.top program

def graph : program ⟶ program ⨯ program := prod.lift (𝟙 program) truthTarget

instance graph_mono : Mono graph := by
  change Mono (prod.lift (𝟙 program) truthTarget)
  infer_instance

abbrev sourceTheory : Theory.{0,0} where
  closed := old.closed
  program := program
  reduction := Subobject.mk graph

def sourceEvent : sourceTheory.Event ≅ program := Subobject.underlyingIso graph

theorem source_event_read : sourceEvent.inv ≫ sourceTheory.source = 𝟙 program := by
  change (Subobject.underlyingIso graph).inv ≫ ((Subobject.mk graph).arrow ≫ prod.fst) = _
  rw [← Category.assoc, Subobject.underlyingIso_arrow]
  exact prod.lift_fst _ _

theorem target_event_read : sourceEvent.inv ≫ sourceTheory.target = truthTarget := by
  change (Subobject.underlyingIso graph).inv ≫ ((Subobject.mk graph).arrow ≫ prod.snd) = _
  rw [← Category.assoc, Subobject.underlyingIso_arrow]
  exact prod.lift_snd _ _

abbrev extended := generatedTheory sourceTheory
abbrev inclusion := generatedInclusion sourceTheory

def retainedEvent : extended.program ⟶ extended.Event :=
  inclusion.closed.functor.map sourceEvent.inv ≫ inclusion.reduction

theorem retained_source : retainedEvent ≫ extended.source = 𝟙 extended.program := by
  change (inclusion.closed.functor.map sourceEvent.inv ≫ inclusion.reduction) ≫ extended.source = _
  rw [Category.assoc, inclusion.source, ← Category.assoc,
    ← inclusion.closed.functor.map_comp, source_event_read]
  change inclusion.closed.functor.map (𝟙 program) ≫ 𝟙 _ = _
  rw [_root_.CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

theorem retained_target : retainedEvent ≫ extended.target = inclusion.closed.functor.map truthTarget := by
  change (inclusion.closed.functor.map sourceEvent.inv ≫ inclusion.reduction) ≫ extended.target = _
  rw [Category.assoc, inclusion.target, ← Category.assoc,
    ← inclusion.closed.functor.map_comp, target_event_read]
  exact Category.comp_id _

abbrev firstDiagram := RelativeClosedConjunctiveAdjunctionControls.firstDiagram
abbrev firstBase := RelativeClosedConjunctiveAdjunctionControls.firstBase
abbrev boolean := RelativeClosedConjunctiveControls.boolean
abbrev booleanLaws := RelativeClosedConjunctiveControls.boolean_laws
abbrev independentModel := ModelReadout.model firstDiagram boolean booleanLaws
abbrev diagram := independentModel.diagram

theorem program_read : diagram.obj extended.program = ULift.{0} Bool :=
  (RelativeClosedSyntax.Interpretation.functor_base_object
    independentModel.meanings independentModel.realization program).trans
    RelativeClosedConjunctiveAdjunctionControls.fresh_read

theorem old_target_read : diagram.map (inclusion.closed.functor.map truthTarget) =
    firstDiagram.map truthTarget :=
  RelativeClosedSyntax.Interpretation.functor_base_arrow
    independentModel.meanings independentModel.realization truthTarget

def decodedSource : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom program_read.symm ≫ diagram.map (retainedEvent ≫ extended.source) ≫ eqToHom program_read

def decodedTarget : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom program_read.symm ≫ diagram.map (retainedEvent ≫ extended.target) ≫ eqToHom program_read

theorem complete_source : decodedSource = 𝟙 (ULift.{0} Bool) := by
  have mapped : diagram.map (retainedEvent ≫ extended.source) = 𝟙 (diagram.obj extended.program) :=
    (congrArg diagram.map retained_source).trans (diagram.map_id extended.program)
  refine (congrArg (fun arrow => eqToHom program_read.symm ≫ arrow ≫ eqToHom program_read) mapped).trans ?_
  exact (congrArg (fun arrow => eqToHom program_read.symm ≫ arrow)
    (Category.id_comp (eqToHom program_read))).trans
    ((eqToHom_trans program_read.symm program_read).trans (eqToHom_refl _ _))

theorem complete_target : decodedTarget = boolean.top (ULift.{0} Bool) := by
  have mapped := (congrArg diagram.map retained_target).trans old_target_read
  have actual := (ModelReadout.mapping firstBase boolean booleanLaws).image_top program
  change firstDiagram.map truthTarget ≫ eqToHom RelativeClosedConjunctiveAdjunctionControls.fresh_read =
    boolean.top (firstDiagram.obj program) at actual
  refine (congrArg (fun arrow => eqToHom program_read.symm ≫ arrow ≫ eqToHom program_read) mapped).trans ?_
  exact (congrArg (fun arrow => eqToHom program_read.symm ≫ arrow) actual).trans
    (boolean.reindex_top (eqToHom program_read.symm))

theorem complete_supplied_endpoints :
    (decodedSource (ULift.up false)).down = false ∧
    (decodedTarget (ULift.up false)).down = true ∧
    (decodedSource (ULift.up true)).down = true ∧
    (decodedTarget (ULift.up true)).down = true := by
  rw [complete_source, complete_target]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem complete_target_is_not_identity : decodedTarget ≠ decodedSource := by
  intro collapsed
  have same := congrArg (fun arrow : ULift.{0} Bool ⟶ ULift.{0} Bool =>
    (arrow (ULift.up false)).down) collapsed
  exact Bool.false_ne_true (complete_supplied_endpoints.1.symm.trans
    (same.symm.trans complete_supplied_endpoints.2.1))

def rule : AuthoredClosedTheory.Rule sourceTheory where
  parameters := program ⨯ program
  left := prod.fst
  right := prod.fst ≫ truthTarget
  action := prod.fst ≫ sourceEvent.inv
  source := by rw [Category.assoc, source_event_read, Category.comp_id]
  target := by rw [Category.assoc, target_event_read]

def position : AuthoredClosedTheory.Position rule where
  environment := program
  carrier := program
  relies := prod.snd
  focus := prod.fst
  plug := prod.snd
  decomposition := prod.lift_snd _ _

theorem supplied_position_complete :
    (selectedPosition sourceTheory position).relies = inclusion.closed.functor.map prod.snd ∧
    (selectedPosition sourceTheory position).focus = inclusion.closed.functor.map prod.fst ∧
    (selectedPosition sourceTheory position).plug =
      inv (prodComparison inclusion.closed.functor program program) ≫ inclusion.closed.functor.map prod.snd :=
  ⟨selected_rely_input_readout sourceTheory position,
    selected_focus_readout sourceTheory position, selected_context_readout sourceTheory position⟩

theorem selected_focus_and_rely_are_distinct :
    (selectedPosition sourceTheory position).focus ≠ (selectedPosition sourceTheory position).relies := by
  intro collapsed
  have mapped := congrArg diagram.map collapsed
  have firstRead := RelativeClosedSyntax.Interpretation.functor_base_arrow
    independentModel.meanings independentModel.realization (prod.fst : program ⨯ program ⟶ program)
  have secondRead := RelativeClosedSyntax.Interpretation.functor_base_arrow
    independentModel.meanings independentModel.realization (prod.snd : program ⨯ program ⟶ program)
  have projected : firstDiagram.map (prod.fst : program ⨯ program ⟶ program) =
      firstDiagram.map (prod.snd : program ⨯ program ⟶ program) :=
    firstRead.symm.trans (mapped.trans secondRead)
  have distinct : (prod.fst : firstDiagram.obj program ⨯ firstDiagram.obj program ⟶ firstDiagram.obj program) =
      prod.snd := (cancel_epi (prodComparison firstDiagram program program)).mp
    ((prodComparison_fst firstDiagram program program).trans
      (projected.trans (prodComparison_snd firstDiagram program program).symm))
  let first : firstDiagram.obj program :=
    (eqToHom RelativeClosedConjunctiveAdjunctionControls.fresh_read.symm) (ULift.up false)
  let second : firstDiagram.obj program :=
    (eqToHom RelativeClosedConjunctiveAdjunctionControls.fresh_read.symm) (ULift.up true)
  have plain : (TypeCat.ofHom _root_.Prod.fst :
      firstDiagram.obj program × firstDiagram.obj program ⟶ firstDiagram.obj program) =
      TypeCat.ofHom _root_.Prod.snd :=
    (Types.binaryProductIso_inv_comp_fst _ _).symm.trans
      ((congrArg (fun arrow => (Types.binaryProductIso _ _).inv ≫ arrow) distinct).trans
        (Types.binaryProductIso_inv_comp_snd _ _))
  have supplied := congrArg (fun arrow : firstDiagram.obj program × firstDiagram.obj program ⟶ firstDiagram.obj program =>
    ((eqToHom RelativeClosedConjunctiveAdjunctionControls.fresh_read) (arrow (first, second))).down) plain
  change false = true at supplied
  exact Bool.false_ne_true supplied

def occurrences : AuthoredClosedTheory.Presentation.{0,0,0} sourceTheory where
  ConstructorOrigin := Bool
  constructor _ := ⟨program, 𝟙 program⟩
  RuleOrigin := Bool
  rule _ := rule
  PositionOrigin _ := Bool
  position _ _ := position

theorem duplicate_rule_origins_remain_distinct :
    (false : (authoredPresentation sourceTheory occurrences).RuleOrigin) ≠ true := Bool.false_ne_true

theorem duplicate_actions_agree :
    ((authoredPresentation sourceTheory occurrences).rule false).action =
      ((authoredPresentation sourceTheory occurrences).rule true).action := rfl

theorem complete_selected_decomposition :
    prod.lift (selectedPosition sourceTheory position).relies (selectedPosition sourceTheory position).focus ≫
      (selectedPosition sourceTheory position).plug = (authoredRule sourceTheory rule).left :=
  (selectedPosition sourceTheory position).decomposition

end Mettapedia.GSLT.Core.RelativeClosedProgramReductionExtensionControls
