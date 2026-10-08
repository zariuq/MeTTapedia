import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentFiring
import Mettapedia.OSLF.Syntax.SortedCommutativeConstructorReadout

/-!
# Complete sorted AC1 frame and observer controls

Two different free-constructor hole positions can have the same ground
filling while remaining different context classes. The complete RPO still
exists. A proper Cut has equal source classes with two unequal ordered ask
targets; actual IPO steps retain both matches and origins. Get keeps its
selected coordinate and nullary ask keeps its genuine fresh bundle sort.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstrumentControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open SortedCommutativeInstruments

inductive Symbol where
  | low
  | high
  | pair

abbrev arity : Symbol → Nat
  | .low => 0
  | .high => 0
  | .pair => 2

def low : Value arity .base := sourceNode arity (.ordinary .low) (fun position => Fin.elim0 position)
def high : Value arity .base := sourceNode arity (.ordinary .high) (fun position => Fin.elim0 position)

theorem low_high_classes_distinct : classOf low ≠ classOf high := by
  intro same
  have inventories := congrArg inventoryQ same
  change inventory low = inventory high at inventories
  simp only [low, high, sourceNode, inventory] at inventories
  have heads := Multiset.singleton_inj.mp inventories
  cases heads

def firstHole : RawContext (signature arity) (Parallel arity) .base .base :=
  RawContext.frame (signature := signature arity) (Parallel := Parallel arity) (SortedCommutativeInstruments.Constructor.original Symbol.pair) 0
    (fun _ _ => low) .hole

def secondHole : RawContext (signature arity) (Parallel arity) .base .base :=
  RawContext.frame (signature := signature arity) (Parallel := Parallel arity) (SortedCommutativeInstruments.Constructor.original Symbol.pair) 1
    (fun _ _ => low) .hole

theorem position_collision : firstHole.fill low = secondHole.fill low := by
  apply congrArg (Term.node (signature := signature arity) (SortedCommutativeInstruments.Constructor.original Symbol.pair))
  funext position
  fin_cases position <;> rfl

private def framePosition {source target : Srt arity} : Frame (signature arity) (Parallel arity) source target → Nat
  | .slot _ position _ => position.val

private def rootPosition {source target : Srt arity} : MixedContext (signature arity) (Parallel arity) source target → Nat
  | .parallel _ => 0
  | .frame _ edge _ => framePosition edge

theorem same_ground_does_not_identify_contexts : ¬ContextEquation firstHole secondHole := by
  intro equation
  have positions := congrArg rootPosition equation.normalize
  change 0 = 1 at positions
  cases positions

theorem actual_context_classes_differ : contextClassOf firstHole ≠ contextClassOf secondHole :=
  fun same => same_ground_does_not_identify_contexts (Quotient.exact same)

theorem position_collision_square :
    RawArrow.comp (signature := signature arity) (Parallel := Parallel arity)
        (RawArrow.value (classOf low)) (RawArrow.context (contextClassOf firstHole)) =
      RawArrow.comp (signature := signature arity) (Parallel := Parallel arity)
        (RawArrow.value (classOf low)) (RawArrow.context (contextClassOf secondHole)) :=
  congrArg RawArrow.value (congrArg classOf position_collision)

theorem complete_rpo_at_position_collision :
    ∃ candidate : Mettapedia.GSLT.RelativePushout.Candidate (C := ContextCategory arity)
        (RawArrow.value (classOf low) : (.origin : ContextCategory arity) ⟶ .interface .base)
        (RawArrow.value (classOf low))
        (RawArrow.context (contextClassOf firstHole)) (RawArrow.context (contextClassOf secondHole)),
      Mettapedia.GSLT.RelativePushout.IsRelativePushout candidate :=
  raw_hasRelativePushouts (classOf low) (classOf low) (.interface .base)
    (RawArrow.context (contextClassOf firstHole)) (RawArrow.context (contextClassOf secondHole)) position_collision_square

def ordered : Fin 2 → Value arity .base := Fin.cases low (fun _ => high)
def reversed : Fin 2 → Value arity .base := Fin.cases high (fun _ => low)

def firstAsk : Occurrence arity Nat := .ask 7 .properCut ordered
def secondAsk : Occurrence arity Nat := .ask 8 .properCut reversed

theorem proper_cut_unit_equation :
    Equation (signature := signature arity) (Parallel := Parallel arity) (.cut rfl low (.zero rfl)) low :=
  Equation.unit (signature := signature arity) (Parallel := Parallel arity) rfl low

theorem same_cut_class : classOf (sourceNode arity .properCut ordered) = classOf (sourceNode arity .properCut reversed) :=
  Quotient.sound (Equation.comm (signature := signature arity) (Parallel := Parallel arity) rfl low high)

theorem same_ask_source : firstAsk.agent = secondAsk.agent := congrArg RawArrow.value same_cut_class
theorem same_ask_label : firstAsk.label = secondAsk.label := rfl

theorem different_ordered_ask_targets : firstAsk.target ≠ secondAsk.target := by
  intro same
  have bundled := RawArrow.value.inj same
  have picked := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
    (SortedCommutativeInstruments.Constructor.arguments (arity := arity) SourceSymbol.properCut)
    ordered reversed).mp bundled 0
  exact low_high_classes_distinct picked

theorem both_ordered_matches_fire :
    Mettapedia.GSLT.RedexRelativeCongruence.ActIPO (rules arity Nat) firstAsk.label firstAsk.agent firstAsk.target ∧
      Mettapedia.GSLT.RedexRelativeCongruence.ActIPO (rules arity Nat) secondAsk.label secondAsk.agent secondAsk.target :=
  ⟨firstAsk.direct_step, secondAsk.direct_step⟩

theorem deterministic_quotient_root_target_rejected :
    ¬∃ choose : ValueClass arity .base → ValueClass arity (.arguments SourceSymbol.properCut),
      choose (classOf firstAsk.body) = classOf firstAsk.output ∧
        choose (classOf secondAsk.body) = classOf secondAsk.output := by
  rintro ⟨choose, first, second⟩
  have outputs := first.symm.trans ((congrArg choose same_cut_class).trans second)
  exact different_ordered_ask_targets (congrArg RawArrow.value outputs)

theorem actual_firing_receipts_keep_origins :
    (directReceipt firstAsk).occurrence.origin = 7 ∧ (directReceipt secondAsk).occurrence.origin = 8 := ⟨rfl, rfl⟩

theorem actual_firing_receipts_are_distinct : directReceipt firstAsk ≠ directReceipt secondAsk := by
  intro same
  have origins := congrArg (fun receipt : FiringReceipt arity Nat => receipt.occurrence.origin) same
  change 7 = 8 at origins
  cases origins

def getFirst : Occurrence arity Nat := .get 9 .properCut ordered 0
def getSecond : Occurrence arity Nat := .get 10 .properCut ordered 1

theorem selected_targets_retained :
    getFirst.target = (RawArrow.value (classOf low) : (.origin : ContextCategory arity) ⟶ .interface .base) ∧
      getSecond.target = (RawArrow.value (classOf high) : (.origin : ContextCategory arity) ⟶ .interface .base) := ⟨rfl, rfl⟩

theorem selected_target_positions_differ : getFirst.target ≠ getSecond.target := by
  intro same
  rw [selected_targets_retained.1, selected_targets_retained.2] at same
  exact low_high_classes_distinct (RawArrow.value.inj same)

theorem both_selected_get_steps :
    Mettapedia.GSLT.RedexRelativeCongruence.ActIPO (rules arity Nat) getFirst.label getFirst.agent getFirst.target ∧
      Mettapedia.GSLT.RedexRelativeCongruence.ActIPO (rules arity Nat) getSecond.label getSecond.agent getSecond.target :=
  ⟨getFirst.direct_step, getSecond.direct_step⟩

def nullaryAsk : Occurrence arity Nat := .ask 11 .unit (fun position => Fin.elim0 position)

theorem nullary_ask_is_real_firing :
    Mettapedia.GSLT.RedexRelativeCongruence.ActIPO (rules arity Nat) nullaryAsk.label nullaryAsk.agent nullaryAsk.target :=
  nullaryAsk.direct_step

theorem no_parallel_residue_at_fresh_arguments
    (supplied : Multiset (ResiduePayload (signature := signature arity) (Parallel := Parallel arity)
      (.arguments SourceSymbol.properCut))) : supplied = 0 :=
  Multiset.eq_zero_of_forall_notMem (fun head _ => arguments_not_parallel arity .properCut head.property)

theorem empty_origins_admit_no_receipts (supplied : FiringReceipt arity Empty) : False :=
  Empty.elim supplied.occurrence.origin

end Mettapedia.OSLF.Framework.SortedCommutativeInstrumentControls
