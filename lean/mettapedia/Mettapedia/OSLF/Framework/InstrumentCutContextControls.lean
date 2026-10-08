import Mettapedia.OSLF.Framework.InstrumentCutEquationRules
import Mettapedia.OSLF.Framework.InstrumentSourceRelativePushout
import Mettapedia.OSLF.Framework.InstrumentSourceTransitions
import Mettapedia.OSLF.Framework.InstrumentSourceEquationComparison
import Mettapedia.OSLF.Framework.InstrumentCutObservations
import Mettapedia.OSLF.Framework.InstrumentCutSourceReactions
import Mettapedia.CategoryTheory.GroundPathSingleFrameIPO

/-!
# Actual cut, hole-position, equation and occurrence controls

The source has two different closed leaves and a binary interaction. Distinct
hole positions fill to the same complete term but remain distinct typed
contexts and form an actual IPO. An extra common outer frame fails IPO
minimality. A unary-unit source equation changes the raw head while preserving
the actual quotient exposure. Duplicate authored origins stay distinct.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContextControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence
open InstrumentCutContexts

inductive Symbol where
  | leaf (color : Bool)
  | cut

def arity : Symbol → Nat
  | .leaf _ => 0
  | .cut => 2

abbrev sig := signature arity

local instance instrumentCutContextControlsQuiver : Quiver (Srt Symbol arity) := frameQuiver sig

def leaf (color : Bool) : Value arity .base := original arity (.leaf color) (fun position => Fin.elim0 position)

def sourceCut : OriginalCut Symbol arity := ⟨.cut, rfl⟩

def leftFrame : Frame sig (.base : Srt Symbol arity) .base :=
  Frame.slot (signature := sig) (Constructor.original Symbol.cut) (0 : Fin 2) (fun _ _ => leaf false)

def rightFrame : Frame sig (.base : Srt Symbol arity) .base :=
  Frame.slot (signature := sig) (Constructor.original Symbol.cut) (1 : Fin 2) (fun _ _ => leaf false)

def leftContext : Context sig (.base : Srt Symbol arity) .base :=
  @Quiver.Hom.toPath (Srt Symbol arity) (frameQuiver sig) _ _ leftFrame

def rightContext : Context sig (.base : Srt Symbol arity) .base :=
  @Quiver.Hom.toPath (Srt Symbol arity) (frameQuiver sig) _ _ rightFrame

theorem frames_differ : leftFrame ≠ rightFrame := by
  intro same
  have positions := congrArg (fun frame : Frame sig (.base : Srt Symbol arity) .base => frame.position.val) same
  change (0 : Nat) = 1 at positions
  omega

theorem contexts_differ : leftContext ≠ rightContext := by
  intro same
  exact frames_differ (eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons same))

theorem syntax_positions_differ : readContext sig leftContext ≠ readContext sig rightContext :=
  fun same => contexts_differ (readContext_injective leftContext rightContext same)

theorem both_have_one_hole : (readContext sig leftContext).holeCount = 1 ∧
    (readContext sig rightContext).holeCount = 1 :=
  ⟨readContext_holeCount sig leftContext, readContext_holeCount sig rightContext⟩

theorem same_complete_ground_value : (action sig).path leftContext (leaf false) =
    (action sig).path rightContext (leaf false) := by
  change Frame.fill leftFrame (leaf false) = Frame.fill rightFrame (leaf false)
  apply congrArg (Term.node (signature := sig) (Constructor.original Symbol.cut))
  funext position
  fin_cases position <;> rfl

theorem positionSquare : termArrow sig (leaf false) ≫ contextArrow sig leftContext =
    termArrow sig (leaf false) ≫ contextArrow sig rightContext :=
  congrArg (termArrow sig) same_complete_ground_value

/-- All competing candidates factor uniquely, although filling is not
injective in the hole position. -/
theorem distinct_positions_actualIPO : IsIdemPushout (termArrow sig (leaf false))
    (termArrow sig (leaf false)) (contextArrow sig leftContext) (contextArrow sig rightContext) positionSquare :=
  distinct_single_frames_ipo (action sig) leftFrame rightFrame frames_differ
    (leaf false) (leaf false) positionSquare

theorem extra_common_outer_frame_notIPO :
    ¬ IsIdemPushout (termArrow sig (leaf false)) (termArrow sig (leaf false))
      (contextArrow sig leftContext) (contextArrow sig leftContext) rfl := by
  intro ipo
  let candidate : PathCandidate (action sig) (leaf false) (leaf false) leftContext leftContext :=
    { apex := .base
      inl := .nil
      inr := .nil
      down := leftContext
      comm := rfl
      fac_left := rfl
      fac_right := rfl }
  have zero := ipo_no_context_descent (action sig) (leaf false) (leaf false)
    leftContext leftContext rfl ipo candidate
  change 1 = 0 at zero
  omega

def arguments : Fin 2 → Value arity .base := ![leaf false, leaf true]

def askInstance : AdministrativeInstance arity (.ask Symbol.cut) := .ask Symbol.cut arguments

def firstOccurrence : AdministrativeOccurrence arity Bool (.ask Symbol.cut) := ⟨false, askInstance⟩
def secondOccurrence : AdministrativeOccurrence arity Bool (.ask Symbol.cut) := ⟨true, askInstance⟩

def firstReceipt : FiringReceipt arity Bool (.ask Symbol.cut) askInstance.body askInstance.output :=
  ⟨firstOccurrence, rfl, rfl⟩

def secondReceipt : FiringReceipt arity Bool (.ask Symbol.cut) askInstance.body askInstance.output :=
  ⟨secondOccurrence, rfl, rfl⟩

theorem retained_receipts_differ : firstReceipt ≠ secondReceipt := by
  intro same
  have origins := congrArg (fun receipt => receipt.occurrence.origin) same
  cases origins

theorem ask_actualIPO_step : ActIPO (administrativeRules arity Bool)
    (contextArrow sig (probeContext arity (.ask Symbol.cut)))
    (termArrow sig askInstance.body) (termArrow sig askInstance.output) := firstReceipt.step

theorem ask_retains_both_children : firstReceipt.occurrence.instance_.body =
    originalCut arity sourceCut (leaf false) (leaf true) ∧
    firstReceipt.occurrence.instance_.output = bundle arity Symbol.cut arguments := ⟨rfl, rfl⟩

theorem no_receipt_with_empty_origins :
    ¬ ActIPO (administrativeRules arity PEmpty)
      (contextArrow sig (probeContext arity (.ask Symbol.cut)))
      (termArrow sig askInstance.body) (termArrow sig askInstance.output) := by
  intro step
  obtain ⟨occurrence, _, _⟩ := (administrative_step_iff arity PEmpty _ _ _).mp step
  exact occurrence.origin.elim

def properRule : SourceRule arity where
  redex := .node .cut ![.node (.leaf false) (fun position => Fin.elim0 position),
    .node (.leaf true) (fun position => Fin.elim0 position)]
  reactum := .node (.leaf false) (fun position => Fin.elim0 position)

theorem proper_rule_changes_complete_term : embedSource arity properRule.redex ≠
    embedSource arity properRule.reactum := by
  intro same
  have heads := Term.head_eq (signature := sig) _ _ same
  cases heads

theorem extended_ask_retains_readout : ActIPO (extendedRules arity Bool (fun rule => rule = properRule))
    (contextArrow sig (probeContext arity (.ask Symbol.cut)))
    (termArrow sig askInstance.body) (termArrow sig askInstance.output) :=
  (extended_administrative_step_iff arity Bool (fun rule => rule = properRule) _ _ _).mpr
    ⟨firstOccurrence, rfl, rfl⟩

theorem original_and_observer_share_cut_symbol :
    rootSymbol arity sourceCut askInstance.body.head = .interaction ∧
    rootSymbol arity sourceCut (cut arity (.ask Symbol.cut) (probe arity (.ask Symbol.cut)) askInstance.body).head =
      .interaction := ⟨original_cut_symbol arity sourceCut (leaf false) (leaf true), rfl⟩

def rawBody : RawTerm sig (.base : Srt Symbol arity) .base := embed sig .base askInstance.body
def paddedBody : RawTerm sig (.base : Srt Symbol arity) .base := pad sig .base rawBody
def rawOutput : RawTerm sig (.base : Srt Symbol arity) (.arguments Symbol.cut) := embed sig .base askInstance.output

theorem raw_padding_changes_root : paddedBody ≠ rawBody := by
  intro same
  have heads := Term.head_eq (signature := extended sig .base) _ _ same
  change Sum.inr (PUnit.unit) = Sum.inl (Constructor.original Symbol.cut) at heads
  cases heads

theorem padding_same_authored_class : classOf paddedBody = classOf rawBody :=
  Quotient.sound (Equation.unit rawBody)

/-- The source's raw root is padding, yet the actual equation-category IPO
exposes the original binary cut and retains its complete argument bundle. -/
theorem padded_source_actual_exposure :
    EquationProbeExposure arity (.ask Symbol.cut) (classOf paddedBody) (classOf rawBody)
      (classOf rawOutput) (classOf rawOutput) :=
  (equationProbeExposure_raw_iff arity (.ask Symbol.cut) paddedBody rawBody rawOutput rawOutput).mpr
    ⟨Equation.unit rawBody, Equation.refl rawOutput⟩

theorem original_positions_stay_distinct_in_quotient :
    contextClassOf (embedContext sig .base leftContext) ≠
      contextClassOf (embedContext sig .base rightContext) := by
  intro same
  have readouts := congrArg (contextValue sig .base) same
  change normalizeContext sig .base (embedContext sig .base leftContext) =
    normalizeContext sig .base (embedContext sig .base rightContext) at readouts
  rw [normalize_embedContext, normalize_embedContext] at readouts
  exact contexts_differ readouts

def sourceLeaf (color : Bool) : InstrumentObservations.Tree Symbol arity :=
  .node (.leaf color) (fun position => Fin.elim0 position)

def leftSourceFrame : SourceFrame arity := ⟨Symbol.cut, (0 : Fin 2), fun _ _ => sourceLeaf false⟩
def rightSourceFrame : SourceFrame arity := ⟨Symbol.cut, (1 : Fin 2), fun _ _ => sourceLeaf false⟩

theorem source_leaf_readout (color : Bool) : embedSource arity (sourceLeaf color) = leaf color := by
  apply congrArg (Term.node (signature := sig) (Constructor.original (Symbol.leaf color)))
  funext position
  exact position.elim0

theorem source_left_frame_readout : sourceFrameImage arity leftSourceFrame = leftFrame := by
  apply congrArg (Frame.slot (signature := sig) (Constructor.original Symbol.cut) (0 : Fin 2))
  funext other absent
  exact source_leaf_readout false

theorem source_right_frame_readout : sourceFrameImage arity rightSourceFrame = rightFrame := by
  apply congrArg (Frame.slot (signature := sig) (Constructor.original Symbol.cut) (1 : Fin 2))
  funext other absent
  exact source_leaf_readout false

theorem source_left_context_readout : sourceContextImage arity [leftSourceFrame] = leftContext :=
  congrArg (fun frame => @Quiver.Hom.toPath (Srt Symbol arity) (frameQuiver sig) _ _ frame) source_left_frame_readout

theorem source_right_context_readout : sourceContextImage arity [rightSourceFrame] = rightContext :=
  congrArg (fun frame => @Quiver.Hom.toPath (Srt Symbol arity) (frameQuiver sig) _ _ frame) source_right_frame_readout

theorem source_position_square : sourceValueArrow arity (sourceLeaf false) ≫ sourceContextArrow arity [leftSourceFrame] =
    sourceValueArrow arity (sourceLeaf false) ≫ sourceContextArrow arity [rightSourceFrame] := by
  apply congrArg SourceArrow.value
  apply congrArg (InstrumentObservations.Tree.node Symbol.cut)
  funext position
  fin_cases position <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem source_positions_actualIPO : IsIdemPushout (sourceValueArrow arity (sourceLeaf false))
    (sourceValueArrow arity (sourceLeaf false)) (sourceContextArrow arity [leftSourceFrame])
    (sourceContextArrow arity [rightSourceFrame]) source_position_square := by
  apply (source_idemPushout_iff arity (sourceLeaf false) (sourceLeaf false)
    [leftSourceFrame] [rightSourceFrame] source_position_square).mpr
  have different : sourceFrameImage arity leftSourceFrame ≠ sourceFrameImage arity rightSourceFrame := by
    intro same
    rw [source_left_frame_readout, source_right_frame_readout] at same
    exact frames_differ same
  exact distinct_single_frames_ipo (action sig) (sourceFrameImage arity leftSourceFrame)
    (sourceFrameImage arity rightSourceFrame) different (embedSource arity (sourceLeaf false))
    (embedSource arity (sourceLeaf false))
    (by
      have mapped := congrArg (sourceFunctor arity).map source_position_square
      rw [Functor.map_comp, Functor.map_comp] at mapped
      exact mapped)

theorem source_positions_quotientIPO :
    IsIdemPushout ((sourceEquationFunctor arity).map (sourceValueArrow arity (sourceLeaf false)))
      ((sourceEquationFunctor arity).map (sourceValueArrow arity (sourceLeaf false)))
      ((sourceEquationFunctor arity).map (sourceContextArrow arity [leftSourceFrame]))
      ((sourceEquationFunctor arity).map (sourceContextArrow arity [rightSourceFrame]))
      (by rw [← Functor.map_comp, source_position_square, Functor.map_comp]) :=
  (sourceEquation_idemPushout_iff arity _ _ _ _ source_position_square).mp source_positions_actualIPO

theorem proper_root_extended_step :
    ActIPO (extendedRules arity Bool (fun rule => rule = properRule))
      (contextArrow sig (sourceContextImage arity []))
      (termArrow sig (embedSource arity properRule.redex))
      (termArrow sig (embedSource arity properRule.reactum)) := by
  refine ⟨properRule.reaction, Or.inr ⟨properRule, rfl, rfl⟩,
    contextArrow sig (sourceContextImage arity []), rfl, ?_, rfl⟩
  exact ground_identityReactionIPO (action sig) (embedSource arity properRule.redex)
    (embedSource arity properRule.redex) (sourceContextImage arity []) rfl

theorem proper_root_step_reflected :
    ActIPO (properSourceRules arity (fun rule => rule = properRule)) (sourceContextArrow arity [])
      (sourceValueArrow arity properRule.redex) (sourceValueArrow arity properRule.reactum) :=
  (extended_source_step_iff arity Bool (fun rule => rule = properRule) [] _ _).mp proper_root_extended_step

def leafKit : InstrumentObservations.Policy Symbol :=
  fun constructor => ∃ color : Bool, constructor = .leaf color

def cutKit : InstrumentObservations.Policy Symbol := fun constructor => leafKit constructor ∨ constructor = .cut

theorem sampled_probe_actual_response :
    ProbeResponse arity Bool cutKit (.term properRule.redex) (.ask .cut) (.bundle properRule.redex) := by
  change ProbeResponse arity Bool cutKit (.term (.node Symbol.cut ![sourceLeaf false, sourceLeaf true]))
    (.ask Symbol.cut) (.bundle (.node Symbol.cut ![sourceLeaf false, sourceLeaf true]))
  exact event_probe_response arity false
    (@InstrumentObservations.Event.ask Symbol arity cutKit Symbol.cut ![sourceLeaf false, sourceLeaf true] (Or.inr rfl))

theorem response_keeps_actual_label_under_expansion :
    ProbeResponse arity Bool cutKit (.term (sourceLeaf false)) (.ask (Symbol.leaf false)) (.bundle (sourceLeaf false)) :=
  probe_response_monotone arity (fun _ permission => Or.inl permission)
    (event_probe_response arity false (.ask (Symbol.leaf false) (fun position => Fin.elim0 position) ⟨false, rfl⟩))

theorem different_leaves_not_probe_bisimilar :
    ¬ ProbeBisimilar arity Bool leafKit (.term (sourceLeaf false)) (.term (sourceLeaf true)) := by
  intro related
  have same := (probe_term_bisimilar_iff_view arity Bool leafKit _ _).mp related
  simp [InstrumentObservations.view, leafKit, sourceLeaf] at same

theorem every_empty_origin_response_fails (opened : InstrumentObservations.Policy Symbol)
    (source target : SourceState arity) (label : SourceLabel arity) :
    ¬ ProbeResponse arity PEmpty opened source label target := by
  rintro ⟨sourceSort, targetSort, _, step⟩
  obtain ⟨occurrence, _, _⟩ := (administrative_step_iff arity PEmpty _ _ _).mp step
  exact occurrence.origin.elim

theorem empty_origins_lose_structural_separation :
    ProbeBisimilar arity PEmpty leafKit (.term (sourceLeaf false)) (.term (sourceLeaf true)) := by
  let relation : SourceState arity → SourceState arity → Prop :=
    fun first second => InstrumentObservations.tag first = InstrumentObservations.tag second
  refine ⟨relation, ⟨fun same => same, ?_, ?_⟩, rfl⟩
  · intro first second _ label target response
    exact (every_empty_origin_response_fails leafKit first target label response).elim
  · intro first second _ label target response
    exact (every_empty_origin_response_fails leafKit second target label response).elim

def alternateRule : SourceRule arity where
  redex := .node .cut ![sourceLeaf true, sourceLeaf false]
  reactum := sourceLeaf true

def futureProper (rule : SourceRule arity) : Prop := rule = properRule ∨ rule = alternateRule

theorem future_root_step (rule : SourceRule arity) (admitted : futureProper rule) :
    ActIPO (extendedRules arity Bool futureProper) (contextArrow sig (sourceContextImage arity []))
      (termArrow sig (embedSource arity rule.redex)) (termArrow sig (embedSource arity rule.reactum)) := by
  refine ⟨rule.reaction, Or.inr ⟨rule, admitted, rfl⟩,
    contextArrow sig (sourceContextImage arity []), rfl, ?_, rfl⟩
  exact ground_identityReactionIPO (action sig) (embedSource arity rule.redex)
    (embedSource arity rule.redex) (sourceContextImage arity []) rfl

theorem root_probe_kernel_does_not_determine_future_leaf_readout :
    ProbeBisimilar arity Bool leafKit (.term properRule.redex) (.term alternateRule.redex) ∧
      ActIPO (extendedRules arity Bool futureProper) (contextArrow sig (sourceContextImage arity []))
        (termArrow sig (embedSource arity properRule.redex)) (termArrow sig (embedSource arity properRule.reactum)) ∧
      ActIPO (extendedRules arity Bool futureProper) (contextArrow sig (sourceContextImage arity []))
        (termArrow sig (embedSource arity alternateRule.redex)) (termArrow sig (embedSource arity alternateRule.reactum)) ∧
      ¬ ProbeBisimilar arity Bool leafKit (.term properRule.reactum) (.term alternateRule.reactum) := by
  refine ⟨?_, future_root_step properRule (Or.inl rfl), future_root_step alternateRule (Or.inr rfl), ?_⟩
  · apply (probe_term_bisimilar_iff_view arity Bool leafKit _ _).mpr
    simp [InstrumentObservations.view, leafKit, properRule, alternateRule]
  · exact different_leaves_not_probe_bisimilar

theorem swapped_children_fail_equation_bundle_match :
    ¬ Equation sig .base (rawBundle arity .cut ![embed sig .base (leaf false), embed sig .base (leaf true)])
      (rawBundle arity .cut ![embed sig .base (leaf true), embed sig .base (leaf false)]) := by
  intro equation
  have first := (rawBundle_equations_iff arity Symbol.cut _ _).mp equation (0 : Fin 2)
  have readout := equation_normalizes first
  change Padding.normalize sig .base (embed sig .base (leaf false)) =
    Padding.normalize sig .base (embed sig .base (leaf true)) at readout
  rw [normalize_embed, normalize_embed] at readout
  have heads := Term.head_eq (signature := sig) _ _ readout
  cases heads

def unitArguments : Fin 2 → RawBase arity :=
  ![pad sig .base (embed sig .base (leaf false)), embed sig .base (leaf true)]

theorem unit_get_retains_selected_child :
    EquationProbeExposure arity (.get Symbol.cut (0 : Fin 2)) (classOf (rawBundle arity Symbol.cut unitArguments))
      (classOf (rawBundle arity Symbol.cut unitArguments)) (classOf (unitArguments 0))
      (classOf (embed sig .base (leaf false))) :=
  (equation_get_iff arity Symbol.cut (0 : Fin 2) unitArguments _ _).mpr
    ⟨Equation.refl _, (Equation.unit _).symm⟩

theorem unit_get_rejects_wrong_child :
    ¬ EquationProbeExposure arity (.get Symbol.cut (0 : Fin 2)) (classOf (rawBundle arity Symbol.cut unitArguments))
      (classOf (rawBundle arity Symbol.cut unitArguments)) (classOf (unitArguments 0))
      (classOf (embed sig .base (leaf true))) := by
  intro exposure
  have equation := (equation_get_iff arity Symbol.cut (0 : Fin 2) unitArguments _ _).mp exposure
  have readout := equation_normalizes equation.2
  change Padding.normalize sig .base (embed sig .base (leaf true)) =
    Padding.normalize sig .base (pad sig .base (embed sig .base (leaf false))) at readout
  rw [normalize_pad, normalize_embed, normalize_embed] at readout
  have heads := Term.head_eq (signature := sig) _ _ readout
  cases heads

end Mettapedia.OSLF.Framework.InstrumentCutContextControls
