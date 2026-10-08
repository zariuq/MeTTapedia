import Mettapedia.OSLF.Framework.SortedCommutativeCombinedReconstruction
import Mettapedia.OSLF.Framework.SortedCommutativeUnitReactionControls

/-!
# Unit-rule competition and complete future reconstruction coexist

The independently authored source rule has a genuine binary Cut of two
units as redex. Its actual same-label get successor retains the entire
assay beside the supplied reactum. Complete future probes still separate
it from every pure source value and reconstruct both ordinary and AC1
source classes. Administrative inversion also retains a genuinely
observer-bearing child inside a free constructor, rather than erasing it.

Duplicate origins remain different firing evidence. Missing administrative
origins remove every ask even though the original unit rule can still
fire under get. No unique-get or nonunit-redex admission is inferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeCombinedReconstructionControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments Support
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high sourceCut swappedCut)
open SortedCommutativeProbeSourceControls (ordered)
open SortedCommutativeProbeReconstructionControls (lowTarget highTarget)

def sourceDeclarations (_ : Nat) := unitSourceRule low

def sourceRules (rule : ReactionRule (.origin : Source.SourceCategory (arity := arity))) : Prop :=
  ∃ origin : Nat, sourceDeclarations origin = rule

def combinedRules := combinedSourceRules sourceRules Nat

theorem same_independently_authored_unit_family :
    combinedRules = SortedCommutativeUnitReactionControls.combinedRules := by
  funext rule
  apply propext
  constructor
  · rintro (administrative | ⟨original, ⟨origin, rfl⟩, rfl⟩)
    · exact Or.inl administrative
    · exact Or.inr ⟨origin, rfl⟩
  · rintro (administrative | ⟨origin, rfl⟩)
    · exact Or.inl administrative
    · exact Or.inr ⟨unitSourceRule low, ⟨origin, rfl⟩, rfl⟩

theorem actual_get_results_remain_distinct :
    ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) lowTarget ∧
      ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered))
        SortedCommutativeUnitReactionControls.originalResult ∧
      lowTarget ≠ SortedCommutativeUnitReactionControls.originalResult := by
  rw [same_independently_authored_unit_family]
  exact SortedCommutativeUnitReactionControls.actual_get_result_is_not_unique

theorem arbitrary_original_rules_still_separate_source_heads :
    ¬IPOBisimilar combinedRules lowTarget highTarget := by
  intro related
  exact SortedCommutativeSourceControls.source_values_are_distinct
    ((combined_observer_bisimilar_iff_source_equal_all_rules sourceRules (Origins := Nat) ⟨7⟩ _ _).mp related)

theorem arbitrary_original_rules_respect_source_commutativity :
    IPOBisimilar combinedRules (RawArrow.value (Source.classEmbedding (classOf sourceCut)))
      (RawArrow.value (Source.classEmbedding (classOf swappedCut))) :=
  (combined_observer_raw_bisimilar_iff_source_equation_all_rules sourceRules (Origins := Nat) ⟨8⟩ _ _).mpr
    SortedCommutativeSourceControls.original_commutative_equation

theorem the_foreign_get_successor_cannot_match_any_pure_source (source : Source.ValueClass arity) :
    ¬IPOBisimilar combinedRules (RawArrow.value (Source.classEmbedding source))
      SortedCommutativeUnitReactionControls.originalResult := by
  intro related
  have read := (combined_observer_bisimilar_iff_embedded_equal sourceRules (Origins := Nat) ⟨7⟩ source
    (classOf (.cut (signature := signature arity) (Parallel := Parallel arity)
      rfl (Source.embed low) (getAssay (.ordinary Symbol.pair) ordered 0)))).mp related
  have support := congrArg (fun supplied => arrowObserverCount
    (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶ .interface .base)) read
  have leftPure : arrowObserverCount (RawArrow.value (Source.classEmbedding source) :
      (.origin : ContextCategory arity) ⟶ .interface .base) = 0 := classObserverCount_embedding source
  rw [leftPure] at support
  change 0 = arrowObserverCount SortedCommutativeUnitReactionControls.originalResult at support
  rw [SortedCommutativeUnitReactionControls.original_result_retains_three_fresh_heads] at support
  omega

def observedChild : Value arity .base :=
  .cut rfl (Source.embed low) (getAssay (.ordinary Symbol.pair) ordered 0)

def nativeArguments : Fin 2 → Value arity .base :=
  Fin.cases observedChild (fun _ => Source.embed high)

def nativePair : Value arity .base := sourceNode arity (.ordinary Symbol.pair) nativeArguments

theorem a_native_pair_ask_retains_the_entire_observer_bearing_child :
    ActIPO (rules arity Nat) (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (classOf nativePair))
      (RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair) nativeArguments))) :=
  (ask_native_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) _ _).mpr
    ⟨23, nativeArguments, rfl, rfl⟩

theorem native_get_reads_that_whole_child :
    ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair) nativeArguments)))
      (RawArrow.value (classOf observedChild)) :=
  (get_native_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) nativeArguments 0 _).mpr
    ⟨⟨24⟩, rfl⟩

theorem native_build_reconstructs_the_whole_observer_bearing_pair :
    ActIPO (rules arity Nat) (buildLabel (.ordinary Symbol.pair))
      (RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair) nativeArguments)))
      (RawArrow.value (classOf nativePair)) :=
  (build_native_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) nativeArguments _).mpr
    ⟨⟨25⟩, rfl⟩

theorem a_native_get_cannot_erase_the_retained_assay :
    ¬ActIPO (rules arity Nat) (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair) nativeArguments))) lowTarget := by
  intro step
  have read := ((get_native_step_iff (arity := arity) (Origins := Nat) (.ordinary Symbol.pair) nativeArguments 0
    (Source.classEmbedding (classOf low))).mp step).2
  have support := congrArg (fun supplied => arrowObserverCount
    (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶ .interface .base)) read
  change arrowObserverCount lowTarget = arrowObserverCount SortedCommutativeUnitReactionControls.originalResult at support
  rw [SortedCommutativeUnitReactionControls.administrative_result_has_no_fresh_head,
    SortedCommutativeUnitReactionControls.original_result_retains_three_fresh_heads] at support
  omega

theorem repeated_full_native_targets_keep_their_supplied_origins :
    (directReceipt (.get 24 (.ordinary Symbol.pair) nativeArguments 0 : Occurrence arity Nat)).occurrence.target =
        (directReceipt (.get 25 (.ordinary Symbol.pair) nativeArguments 0 : Occurrence arity Nat)).occurrence.target ∧
      directReceipt (.get 24 (.ordinary Symbol.pair) nativeArguments 0 : Occurrence arity Nat) ≠
        directReceipt (.get 25 (.ordinary Symbol.pair) nativeArguments 0 : Occurrence arity Nat) := by
  refine ⟨rfl, ?_⟩
  intro same
  have origins := congrArg (fun receipt => receipt.occurrence.origin) same
  change (24 : Nat) = 25 at origins
  omega

theorem repeated_original_targets_also_keep_their_supplied_origins :
    (SortedCommutativeUnitReactionControls.originalFiring 7).result =
        (SortedCommutativeUnitReactionControls.originalFiring 8).result ∧
      SortedCommutativeUnitReactionControls.originalFiring 7 ≠
        SortedCommutativeUnitReactionControls.originalFiring 8 :=
  SortedCommutativeUnitReactionControls.identical_result_does_not_merge_original_origins

theorem missing_origins_remove_ask_but_not_the_original_get
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair))) :
    ¬ActIPO (combinedSourceRules sourceRules Empty) (askLabel (.ordinary Symbol.pair)) lowTarget result ∧
      ActIPO (combinedSourceRules sourceRules Empty) (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered))
        SortedCommutativeUnitReactionControls.originalResult := by
  constructor
  · intro step
    have administrative := (combined_ask_step_iff_administrative (Origins := Empty)
      sourceRules (.ordinary Symbol.pair) _ result).mp step
    obtain ⟨origin, _before, _input, _output⟩ :=
      (ask_source_step_iff (Origins := Empty) (.ordinary Symbol.pair) (classOf low) result).mp administrative
    exact Empty.elim origin
  · obtain ⟨rule, ⟨origin, rfl⟩, reaction, square, minimal, output⟩ :=
      (SortedCommutativeUnitReactionControls.originalFiring 11).step
    refine ⟨Source.mapReactionRule (unitSourceRule low),
      Or.inr ⟨unitSourceRule low, ⟨origin, rfl⟩, rfl⟩, reaction, square, minimal, ?_⟩
    exact (SortedCommutativeUnitReactionControls.original_firing_keeps_the_full_result 11).symm.trans output

end Mettapedia.OSLF.Framework.SortedCommutativeCombinedReconstructionControls
