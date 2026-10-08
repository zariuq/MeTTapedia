import Mettapedia.GSLT.Core.RelativeClosedPositionedModalNativeMeaning
import Mettapedia.GSLT.Core.PositionedRewriteModalPowerControls
import Mettapedia.CategoryTheory.AsSmallYoneda

/-!
# A genuine positioned rewrite for the generated modal interpretation

The source is the earned common-universe category of small sets. Its program
relation is the successor graph, and its selected rewrite adds both supplied
numbers before taking a successor. The position retains the first number as
its rely input and the second as its focus. Actual product comparisons earn
the full position decomposition and pullback square.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalControlData

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory AsSmallYoneda
open ProgramReductionTheory AuthoredClosedTheory

abbrev Base := AsSmallYoneda.Small Type
abbrev upward : Type ⥤ Base := up Type
abbrev base : Base ⥤ Type := down Type
abbrev closed : LambdaTheory.{1,1} where
  Obj := Base
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance
abbrev program : Base := upward.obj Nat
abbrev parameters : Base := upward.obj (Nat ⨯ Nat)

def successor : program ⟶ program := upward.map PositionedRewriteModalControls.successor
def graph : program ⟶ program ⨯ program := prod.lift (𝟙 program) successor

instance graph_mono : Mono graph := by
  unfold graph
  infer_instance

abbrev theory : Theory.{1,1} where
  closed := closed
  program := program
  reduction := Subobject.mk graph

def event : program ≅ theory.Event := (Subobject.underlyingIso graph).symm

theorem event_source : event.hom ≫ theory.source = 𝟙 program := by
  change (Subobject.underlyingIso graph).inv ≫ ((Subobject.mk graph).arrow ≫ prod.fst) = _
  rw [← Category.assoc, Subobject.underlyingIso_arrow]
  exact prod.lift_fst _ _

theorem event_target : event.hom ≫ theory.target = successor := by
  change (Subobject.underlyingIso graph).inv ≫ ((Subobject.mk graph).arrow ≫ prod.snd) = _
  rw [← Category.assoc, Subobject.underlyingIso_arrow]
  exact prod.lift_snd _ _

def before : parameters ⟶ program := upward.map
  ((Types.binaryProductIso Nat Nat).hom ≫ PositionedRewriteModalControls.before)

def rule : Rule theory where
  parameters := parameters
  left := before
  right := before ≫ successor
  action := before ≫ event.hom
  source := by rw [Category.assoc, event_source, Category.comp_id]
  target := by rw [Category.assoc, event_target]

def tuple : parameters ⟶ program ⨯ program := Limits.prodComparison upward Nat Nat

instance tuple_isIso : IsIso tuple := by
  unfold tuple
  infer_instance

def position : Position rule where
  environment := program
  carrier := program
  relies := upward.map (prod.fst : Nat ⨯ Nat ⟶ Nat)
  focus := upward.map (prod.snd : Nat ⨯ Nat ⟶ Nat)
  plug := inv tuple ≫ before
  decomposition := by
    change tuple ≫ (inv tuple ≫ before) = before
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

def selection : RelativeClosedPositionedModalPresentation.Selection theory where
  rule := rule
  position := position
  assignments := program
  forget := upward.map (prod.snd : Nat ⨯ Nat ⟶ Nat)
  focus := 𝟙 program
  square := by
    change IsPullback (upward.map (prod.snd : Nat ⨯ Nat ⟶ Nat)) tuple (𝟙 program) prod.snd
    exact IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id]
      exact (Limits.prodComparison_snd upward Nat Nat).symm⟩

abbrev Origin := ULift.{1} Bool
def selected (_ : Origin) := selection

abbrev frame := selection.frame
abbrev diagram := RelativeClosedPositionedModalNativeMeaning.diagram
  ElementaryTypePredicateReadout.doctrine theory selected base

theorem the_actual_rule_retains_both_numbers (pair : Nat × Nat) :
    base.map rule.left ((Types.binaryProductIso Nat Nat).inv pair) = pair.1 + pair.2 := by
  change ((Types.binaryProductIso Nat Nat).hom ≫ PositionedRewriteModalControls.before)
    ((Types.binaryProductIso Nat Nat).inv pair) = _
  have complete := congrArg (fun arrow : Nat × Nat ⟶ Nat => arrow pair)
    ((Iso.inv_hom_id_assoc (Types.binaryProductIso Nat Nat) PositionedRewriteModalControls.before))
  exact complete

theorem the_actual_reduct_retains_both_numbers (pair : Nat × Nat) :
    base.map rule.right ((Types.binaryProductIso Nat Nat).inv pair) = pair.1 + pair.2 + 1 := by
  change Nat.succ (base.map rule.left ((Types.binaryProductIso Nat Nat).inv pair)) = _
  rw [the_actual_rule_retains_both_numbers]

theorem neither_rule_input_can_be_dropped :
    base.map rule.left ((Types.binaryProductIso Nat Nat).inv (2, 3)) = (5 : Nat) ∧
    base.map rule.left ((Types.binaryProductIso Nat Nat).inv (2, 4)) = (6 : Nat) ∧
    base.map rule.left ((Types.binaryProductIso Nat Nat).inv (3, 3)) = (6 : Nat) := by
  exact ⟨(the_actual_rule_retains_both_numbers (2, 3)).trans (rfl : (2 : Nat) + 3 = 5),
    (the_actual_rule_retains_both_numbers (2, 4)).trans (rfl : (2 : Nat) + 4 = 6),
    (the_actual_rule_retains_both_numbers (3, 3)).trans (rfl : (3 : Nat) + 3 = 6)⟩

theorem independently_authored_origins_remain_distinct :
    (ULift.up false : Origin) ≠ ULift.up true := by
  intro same
  exact Bool.false_ne_true (congrArg ULift.down same)

theorem duplicate_selected_operator_readings_agree :
    RelativeClosedPositionedModalNativeMeaning.added ElementaryTypePredicateReadout.doctrine
      theory selected base (some (ULift.up false)) =
    RelativeClosedPositionedModalNativeMeaning.added ElementaryTypePredicateReadout.doctrine
      theory selected base (some (ULift.up true)) := rfl

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalControlData
