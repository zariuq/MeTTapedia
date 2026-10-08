import Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionReadout
import Mettapedia.OSLF.Framework.SortedCommutativeProbeSourceControls

/-!
# Complete payload, all-family reconstruction and unit controls

Both pair positions fire and every full-family competitor retains the
selected source class. Build reconstructs the whole pair and original Cut,
including two different ordered bundles with the same AC1 result. Empty
origins and wrong targets exclude actual steps. A nontrivial raw unit padding
is an identity class, while equal ground fillings at different source hole
positions are retained as genuinely different context classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high sourceCut firstHole secondHole)
open SortedCommutativeProbeSourceControls (ordered reversed pairValue)

def lowTarget : (.origin : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.value (Source.classEmbedding (classOf low))

def highTarget : (.origin : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.value (Source.classEmbedding (classOf high))

def pairBuildTarget : (.origin : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.value (Source.classEmbedding (classOf pairValue))

theorem both_positions_really_fire_in_the_full_family :
    ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) lowTarget ∧
      ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 1)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) highTarget :=
  ⟨(get_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) ordered 0 lowTarget).mpr ⟨⟨7⟩, rfl⟩,
    (get_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) ordered 1 highTarget).mpr ⟨⟨8⟩, rfl⟩⟩

theorem every_competing_first_get_retains_the_supplied_coordinate
    (result : (.origin : ContextCategory arity) ⟶ .interface .base)
    (step : ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) result) : result = lowTarget :=
  ((get_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) ordered 0 result).mp step).2

theorem first_get_cannot_return_the_other_coordinate :
    ¬ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) highTarget := by
  intro step
  have wrong := every_competing_first_get_retains_the_supplied_coordinate highTarget step
  exact SortedCommutativeSourceControls.source_values_are_distinct
    (Source.classEmbedding_injective (RawArrow.value.inj wrong.symm))

theorem whole_pair_build_really_fires :
    ActIPO (rules arity Nat) (buildLabel (.ordinary Symbol.pair))
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) pairBuildTarget :=
  (build_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) ordered pairBuildTarget).mpr ⟨⟨37⟩, rfl⟩

theorem every_competing_build_retains_the_whole_pair
    (result : (.origin : ContextCategory arity) ⟶ .interface .base)
    (step : ActIPO (rules arity Nat) (buildLabel (.ordinary Symbol.pair))
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) result) : result = pairBuildTarget :=
  ((build_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) ordered result).mp step).2

theorem empty_origins_exclude_get_and_build
    (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ¬ActIPO (rules arity Empty) (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) result ∧
      ¬ActIPO (rules arity Empty) (buildLabel (.ordinary Symbol.pair))
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) result := by
  constructor
  · intro step
    obtain ⟨origin⟩ := ((get_source_step_iff (arity := arity) (Origins := Empty)
      (.ordinary Symbol.pair) ordered 0 result).mp step).1
    exact Empty.elim origin
  · intro step
    obtain ⟨origin⟩ := ((build_source_step_iff (arity := arity) (Origins := Empty)
      (.ordinary Symbol.pair) ordered result).mp step).1
    exact Empty.elim origin

def cutTarget : (.origin : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.value (Source.classEmbedding (classOf sourceCut))

theorem both_ordered_cut_bundles_rebuild_the_same_whole_class :
    ActIPO (rules arity Nat) (buildLabel SourceSymbol.properCut)
        (RawArrow.value (sourceBundle SourceSymbol.properCut ordered)) cutTarget ∧
      ActIPO (rules arity Nat) (buildLabel SourceSymbol.properCut)
        (RawArrow.value (sourceBundle SourceSymbol.properCut reversed)) cutTarget := by
  refine ⟨(build_source_step_iff (arity := arity) (Origins := Nat) .properCut ordered cutTarget).mpr ⟨⟨7⟩, rfl⟩,
    (build_source_step_iff (arity := arity) (Origins := Nat) .properCut reversed cutTarget).mpr ⟨⟨8⟩, ?_⟩⟩
  exact congrArg (fun value => (RawArrow.value (Source.classEmbedding value) :
    (.origin : ContextCategory arity) ⟶ .interface .base))
      (Quotient.sound SortedCommutativeSourceControls.original_commutative_equation)

theorem the_same_cut_get_label_reads_different_ordered_bundles :
    ActIPO (rules arity Nat) (getLabel SourceSymbol.properCut 0)
        (RawArrow.value (sourceBundle SourceSymbol.properCut ordered)) lowTarget ∧
      ActIPO (rules arity Nat) (getLabel SourceSymbol.properCut 0)
        (RawArrow.value (sourceBundle SourceSymbol.properCut reversed)) highTarget ∧ lowTarget ≠ highTarget := by
  refine ⟨(get_source_step_iff (arity := arity) (Origins := Nat) .properCut ordered 0 lowTarget).mpr ⟨⟨7⟩, rfl⟩,
    (get_source_step_iff (arity := arity) (Origins := Nat) .properCut reversed 0 highTarget).mpr ⟨⟨8⟩, rfl⟩, ?_⟩
  intro same
  exact SortedCommutativeSourceControls.source_values_are_distinct
    (Source.classEmbedding_injective (RawArrow.value.inj same))

def getOccurrence (origin : Nat) : Occurrence arity Nat :=
  .get origin (.ordinary Symbol.pair) (fun position => Source.embed (ordered position)) 1

theorem equal_full_selected_targets_keep_distinct_origins :
    (getOccurrence 7).target = highTarget ∧ (getOccurrence 8).target = highTarget ∧
      directReceipt (getOccurrence 7) ≠ directReceipt (getOccurrence 8) := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have originRead := congrArg (fun receipt : FiringReceipt arity Nat => receipt.occurrence.origin) same
  change 7 = 8 at originRead
  cases originRead

theorem nullary_build_really_returns_the_source_unit :
    ActIPO (rules arity Nat) (buildLabel SourceSymbol.unit)
      (RawArrow.value (sourceBundle SourceSymbol.unit (fun position => Fin.elim0 position)))
      (RawArrow.value (Source.classEmbedding (classOf (.zero rfl : Source.Value arity)))) :=
  (build_source_step_iff (arity := arity) (Origins := Nat) .unit (fun position => Fin.elim0 position) _).mpr ⟨⟨11⟩, rfl⟩

def paddedHole : Source.Context (arity := arity) := .left rfl .hole (.zero rfl)

theorem actual_unit_padding_is_an_identity_class :
    paddedHole ≠ (.hole : Source.Context (arity := arity)) ∧
      contextClassOf paddedHole = ContextClass.identity (signature := Source.signature arity)
        (Parallel := Source.Parallel arity) (ULift.up ()) := by
  constructor
  · intro same
    cases same
  · apply (ContextClass.fill_unit_iff_identity (signature := Source.signature arity)
      (Parallel := Source.Parallel arity) (show Source.Parallel arity (ULift.up ()) from rfl)
        (contextClassOf paddedHole)).mp
    exact Quotient.sound (Equation.unit rfl (.zero rfl))

theorem ground_collision_does_not_make_context_action_faithful :
    (contextClassOf firstHole).fill (classOf low) = (contextClassOf secondHole).fill (classOf low) ∧
      contextClassOf firstHole ≠ contextClassOf secondHole :=
  ⟨congrArg classOf SortedCommutativeSourceControls.source_position_collision,
    fun same => SortedCommutativeSourceControls.original_positions_remain_distinct (Quotient.exact same)⟩

theorem a_real_source_frame_cannot_preserve_the_unit :
    (contextClassOf firstHole).fill (classOf (.zero rfl : Source.Value arity)) ≠
      classOf (.zero rfl : Source.Value arity) := by
  intro same
  have inventories := congrArg inventoryQ same
  have counts := congrArg Multiset.card inventories
  change 1 = 0 at counts
  cases counts

end Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionControls
