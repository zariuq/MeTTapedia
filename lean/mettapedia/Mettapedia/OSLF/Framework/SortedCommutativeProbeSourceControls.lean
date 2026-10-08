import Mettapedia.OSLF.Framework.SortedCommutativeProbeSourceReadout
import Mettapedia.OSLF.Framework.SortedCommutativeSourceControls

/-!
# Actual source matching, complete payload and nondeterministic Cut controls

The full administrative rule family supplies an ordinary pair assay, and
every competing firing has its complete ordered target. A wrong source head
and empty origins reject actual steps. A proper Cut has two ordered source
matches at the same equation class; both complete targets really fire and
cannot be served by a deterministic decoder. Nullary ask retains its fresh
bundle sort, and separately supplied equal-target origins remain distinct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeProbeSourceControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments Support
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high sourceCut)

def ordered : Fin 2 → Source.Value arity := Fin.cases low (fun _ => high)
def reversed : Fin 2 → Source.Value arity := Fin.cases high (fun _ => low)

def pairValue : Source.Value arity := Source.sourceNode (.ordinary Symbol.pair) ordered

def pairTarget : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair)) :=
  RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair) (fun position => Source.embed (ordered position))))

theorem actual_pair_assay_fires :
    ActIPO (rules arity Nat) (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf pairValue))) pairTarget :=
  (ordinary_ask_step_iff (arity := arity) (Origins := Nat) Symbol.pair ordered pairTarget).mpr ⟨⟨7⟩, rfl⟩

theorem every_full_family_pair_competitor_keeps_the_whole_target
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair)))
    (step : ActIPO (rules arity Nat) (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf pairValue))) result) : result = pairTarget :=
  ((ordinary_ask_step_iff (arity := arity) (Origins := Nat) Symbol.pair ordered result).mp step).2

theorem pair_payload_keeps_both_coordinates :
    pairTarget = RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair)
      (Fin.cases (Source.embed low) (fun _ => Source.embed high)))) := by
  apply congrArg (fun arguments : Fin 2 → Value arity .base =>
    RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair) arguments)))
  funext position
  fin_cases position <;> rfl

theorem wrong_source_head_has_no_actual_pair_assay
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair))) :
    ¬ActIPO (rules arity Nat) (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf low))) result := by
  intro step
  obtain ⟨_origin, arguments, sourceRead, _targetRead⟩ :=
    (ask_source_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) _ result).mp step
  have inventories := congrArg inventoryQ sourceRead
  change inventory low = inventory (Source.sourceNode (.ordinary Symbol.pair) arguments) at inventories
  simp only [low, Source.sourceNode, inventory] at inventories
  have heads := Multiset.singleton_inj.mp inventories
  cases heads

theorem no_origins_means_no_real_assay
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair))) :
    ¬ActIPO (rules arity Empty) (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf pairValue))) result := by
  intro step
  obtain ⟨origin⟩ := ((ordinary_ask_step_iff (arity := arity) (Origins := Empty) Symbol.pair ordered result).mp step).1
  exact Empty.elim origin

def firstCutTarget : (.origin : ContextCategory arity) ⟶ .interface (.arguments SourceSymbol.properCut) :=
  RawArrow.value (classOf (bundle arity .properCut (fun position => Source.embed (ordered position))))

def secondCutTarget : (.origin : ContextCategory arity) ⟶ .interface (.arguments SourceSymbol.properCut) :=
  RawArrow.value (classOf (bundle arity .properCut (fun position => Source.embed (reversed position))))

theorem two_ordered_source_matches_really_fire :
    ActIPO (rules arity Nat) (askLabel SourceSymbol.properCut)
        (RawArrow.value (Source.classEmbedding (classOf sourceCut))) firstCutTarget ∧
      ActIPO (rules arity Nat) (askLabel SourceSymbol.properCut)
        (RawArrow.value (Source.classEmbedding (classOf sourceCut))) secondCutTarget := by
  refine ⟨(ask_source_step_iff (arity := arity) (Origins := Nat) .properCut _ firstCutTarget).mpr ⟨7, ordered, rfl, rfl⟩,
    (ask_source_step_iff (arity := arity) (Origins := Nat) .properCut _ secondCutTarget).mpr ⟨8, reversed, ?_, rfl⟩⟩
  exact Quotient.sound SortedCommutativeSourceControls.original_commutative_equation

theorem complete_ordered_cut_targets_are_distinct : firstCutTarget ≠ secondCutTarget := by
  intro same
  have bundled := RawArrow.value.inj same
  have firstCoordinate := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
    (SortedCommutativeInstruments.Constructor.arguments (arity := arity) SourceSymbol.properCut)
    (fun position => Source.embed (ordered position)) (fun position => Source.embed (reversed position))).mp bundled 0
  change Source.classEmbedding (classOf low) = Source.classEmbedding (classOf high) at firstCoordinate
  exact SortedCommutativeSourceControls.source_values_are_distinct
    (Source.classEmbedding_injective firstCoordinate)

theorem no_deterministic_cut_decoder_covers_all_actual_firings :
    ¬∃ decode : Source.ValueClass arity →
        ((.origin : ContextCategory arity) ⟶ .interface (.arguments SourceSymbol.properCut)),
      ∀ supplied result, ActIPO (rules arity Nat) (askLabel SourceSymbol.properCut)
        (RawArrow.value (Source.classEmbedding supplied)) result → decode supplied = result := by
  rintro ⟨decode, faithful⟩
  exact complete_ordered_cut_targets_are_distinct
    ((faithful _ _ two_ordered_source_matches_really_fire.1).symm.trans
      (faithful _ _ two_ordered_source_matches_really_fire.2))

def pairOccurrence (origin : Nat) : Occurrence arity Nat :=
  .ask origin (.ordinary Symbol.pair) (fun position => Source.embed (ordered position))

theorem same_target_does_not_merge_supplied_origins :
    (pairOccurrence 7).target = (pairOccurrence 8).target ∧
      directReceipt (pairOccurrence 7) ≠ directReceipt (pairOccurrence 8) := by
  refine ⟨rfl, ?_⟩
  intro same
  have origins := congrArg (fun receipt : FiringReceipt arity Nat => receipt.occurrence.origin) same
  change 7 = 8 at origins
  cases origins

def nullaryTarget : (.origin : ContextCategory arity) ⟶ .interface (.arguments SourceSymbol.unit) :=
  RawArrow.value (classOf (bundle arity .unit (fun position => Fin.elim0 position)))

theorem actual_nullary_unit_assay :
    ActIPO (rules arity Nat) (askLabel SourceSymbol.unit)
      (RawArrow.value (Source.classEmbedding (classOf (.zero rfl : Source.Value arity)))) nullaryTarget := by
  apply (ask_source_step_iff (arity := arity) (Origins := Nat) .unit _ nullaryTarget).mpr
  refine ⟨11, (fun position => Fin.elim0 position), rfl, ?_⟩
  apply congrArg (fun arguments : Fin 0 → Value arity .base =>
    RawArrow.value (classOf (bundle arity .unit arguments)))
  funext position
  exact Fin.elim0 position

theorem nonbase_zero_support_is_exactly_identity
    (context : ContextClass (signature arity) (Parallel arity) (.arguments SourceSymbol.properCut) (.arguments SourceSymbol.properCut))
    (pure : classContextObserverCount context = 0) :
    context = ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) (.arguments SourceSymbol.properCut) :=
  eq_of_heq (classContextObserverCount_zero_nonbase_identity
    (arguments_not_parallel arity .properCut) context pure).2

theorem nonbase_reaction_can_leave_its_sort_when_support_is_not_zero :
    contextObserverCount (probeContext arity (.build SourceSymbol.properCut)) = 2 ∧
      InstrumentCutContexts.result (sourceArity arity) (.build SourceSymbol.properCut) ≠
        InstrumentCutContexts.receiver (sourceArity arity) (.build SourceSymbol.properCut) :=
  ⟨contextObserverCount_probeContext _, by intro impossible; cases impossible⟩

end Mettapedia.OSLF.Framework.SortedCommutativeProbeSourceControls
