import Mettapedia.OSLF.Framework.SortedCommutativeFullObserverSeparation
import Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionControls

/-!
# Full future assays versus current root names and empty receipts

A current equation-stable root-name observation ignores a changed child.
The actual full ask/get family separates those whole source classes. Source
commutativity and unit equations remain indistinguishable, even when raw
representatives differ. If receipt origins are empty, every actual firing
is impossible and two independently distinct source classes are bisimilar;
the inhabited-origin qualifier is necessary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeFullObserverControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high sourceCut swappedCut)
open SortedCommutativeProbeSourceControls (ordered pairValue)
open SortedCommutativeProbeReconstructionControls (lowTarget highTarget)

theorem full_observers_separate_independently_distinct_source_heads :
    ¬IPOBisimilar (rules arity Nat) lowTarget highTarget := by
  intro related
  exact SortedCommutativeSourceControls.source_values_are_distinct
    ((full_observer_bisimilar_iff_source_equal (arity := arity) (Origins := Nat) ⟨7⟩ _ _).mp related)

private def sourceHeadName
    (head : Head (signature := Source.signature arity) (Parallel := Source.Parallel arity) (ULift.up ())) : Symbol :=
  match head with
  | .node symbol _arguments => symbol

def currentRootNames (supplied : Source.ValueClass arity) : Multiset Symbol :=
  (inventoryQ supplied).map sourceHeadName

def changedArguments : Fin 2 → Source.Value arity := fun _ => high
def changedPair : Source.Value arity := Source.sourceNode (.ordinary Symbol.pair) changedArguments

theorem equal_current_roots_have_a_real_future_coordinate_separator :
    currentRootNames (classOf pairValue) = currentRootNames (classOf changedPair) ∧
      ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) lowTarget ∧
      ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) changedArguments)) highTarget ∧
      ¬IPOBisimilar (rules arity Nat)
        (RawArrow.value (Source.classEmbedding (classOf pairValue)))
        (RawArrow.value (Source.classEmbedding (classOf changedPair))) := by
  refine ⟨rfl, SortedCommutativeProbeReconstructionControls.both_positions_really_fire_in_the_full_family.1,
    (get_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair)
      changedArguments 0 highTarget).mpr ⟨⟨8⟩, rfl⟩, ?_⟩
  intro related
  have wholeRead := (full_observer_bisimilar_iff_source_equal (arity := arity) (Origins := Nat) ⟨7⟩
    (classOf pairValue) (classOf changedPair)).mp related
  have firstRead := (node_class_eq_iff (signature := Source.signature arity) (Parallel := Source.Parallel arity)
    Symbol.pair ordered changedArguments).mp wholeRead 0
  exact SortedCommutativeSourceControls.source_values_are_distinct firstRead

theorem actual_source_commutativity_is_indistinguishable_to_full_observers :
    sourceCut ≠ swappedCut ∧
      IPOBisimilar (rules arity Nat)
        (RawArrow.value (Source.classEmbedding (classOf sourceCut)))
        (RawArrow.value (Source.classEmbedding (classOf swappedCut))) := by
  constructor
  · intro same
    have firstRead : low = high := (Term.cut.inj same).1
    exact SortedCommutativeSourceControls.source_values_are_distinct (congrArg classOf firstRead)
  · exact (full_observer_bisimilar_iff_source_equal (arity := arity) (Origins := Nat) ⟨7⟩ _ _).mpr
      (Quotient.sound SortedCommutativeSourceControls.original_commutative_equation)

theorem actual_source_unit_padding_is_indistinguishable :
    IPOBisimilar (rules arity Nat)
      (RawArrow.value (Source.classEmbedding (classOf (.cut rfl low (.zero rfl) : Source.Value arity))))
      lowTarget :=
  (full_observer_bisimilar_iff_source_equal (arity := arity) (Origins := Nat) ⟨7⟩ _ _).mpr
    (Quotient.sound (Equation.unit (signature := Source.signature arity)
      (Parallel := Source.Parallel arity)
      (show Source.Parallel arity (ULift.up ()) from rfl) low))

private theorem no_actual_empty_origin_step {interface target : ContextCategory arity}
    (agent : (.origin : ContextCategory arity) ⟶ interface) (label : interface ⟶ target)
    (result : (.origin : ContextCategory arity) ⟶ target) :
    ¬ActIPO (rules arity Empty) label agent result := by
  rintro ⟨rule, ⟨occurrence, _originRead⟩, _reaction, _square, _minimal, _output⟩
  cases occurrence with
  | ask origin _ _ => exact Empty.elim origin
  | get origin _ _ _ => exact Empty.elim origin
  | build origin _ _ => exact Empty.elim origin

theorem no_origin_can_make_distinct_whole_source_classes_bisimilar :
    classOf low ≠ classOf high ∧ IPOBisimilar (rules arity Empty) lowTarget highTarget := by
  refine ⟨SortedCommutativeSourceControls.source_values_are_distinct,
    ⟨fun interface _left _right => interface = .interface .base, ?_, rfl⟩⟩
  intro interface left right _related
  constructor
  · intro target label result step
    exact (no_actual_empty_origin_step left label result step).elim
  · intro target label result step
    exact (no_actual_empty_origin_step right label result step).elim

end Mettapedia.OSLF.Framework.SortedCommutativeFullObserverControls
