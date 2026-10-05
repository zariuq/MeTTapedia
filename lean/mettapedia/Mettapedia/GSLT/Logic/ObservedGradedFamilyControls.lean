import Mettapedia.GSLT.Logic.ObservedDepthBudgetSpan
import Mettapedia.GSLT.Distinction.Constructive.Controls

/-!
# Controls for finite-depth material descent and occurrence transport

A family of two alternatives descends through the coarse terminal observer,
but its occurrence-sensitive selected term does not. Adding the authored
Boolean reading makes the exact observer injective and permits both a
genuinely varying material family and its selected term to descend.

On the cell dynamics, decreasing-depth observation derives outgoing endpoint
lifting while incoming lifting fails. The self-loop and two-cycle agree at
every finite depth, but the retained original event cannot be lifted from
every state representative as that very same occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedGradedFamilyControls

open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.Distinction.Constructive.Controls
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassFamilyDescent ObservedGradedFamilyDescent ObservedMaterialization

theorem coarse_readout_equal (depth : Nat) :
    readout coarse depth false = readout coarse depth true :=
  (readout_eq_iff coarse coarseVocabulary depth false true).mpr
    (coarse.depthBound_eq_zero_of_gradedBisimilar coarseVocabulary coarse_gradedBisimilar depth)

theorem fine_readout_injective (depth : Nat) : Function.Injective (readout fine depth) := by
  intro left right same
  have atomic := congrFun same ⟨.atom none, Nat.zero_le depth⟩
  change fineReading none left = fineReading none right at atomic
  cases left <;> cases right
  · rfl
  · exact (show (0 : ℤ) ≠ 1 by decide) atomic |>.elim
  · exact (show (1 : ℤ) ≠ 0 by decide) atomic |>.elim
  · rfl

def alternativesGraph : AccessiblePointedGraph :=
  AccessiblePointedGraph.sup (fun tag : Bool => if tag then HSet.loop else AccessiblePointedGraph.empty)

def alternatives (_source : Bool) : AccessiblePointedGraph := alternativesGraph

def selectedAlternative (source : Bool) : El (· ∈ ·) (HSet.mk (alternatives source)) :=
  ⟨if source then HSet.quineAtom else ∅, by
    apply HSet.mem_range.mpr
    refine ⟨source, ?_⟩
    cases source
    · exact HSet.mk_empty
    · exact HSet.mk_loop⟩

theorem coarse_family_descends (depth : Nat) :
    FamilyInvariant (readout coarse depth) alternatives := fun _ _ _ => rfl

theorem coarse_selected_term_does_not_descend (depth : Nat) :
    ¬ TermCompatible (readout coarse depth) alternatives selectedAlternative := by
  intro compatible
  exact HSet.empty_ne_quineAtom (compatible (coarse_readout_equal depth))

theorem coarse_selected_decoder_not_exact (depth : Nat) :
    ¬ (∀ source, termValue alternatives selectedAlternative (classOf (readout coarse depth) source) =
      (selectedAlternative source).1) := by
  intro exactDecoder
  exact coarse_selected_term_does_not_descend depth
    ((termCompatible_iff_beta (readout coarse depth) alternatives selectedAlternative).mpr exactDecoder)

def varyingGraph (source : Bool) : AccessiblePointedGraph :=
  AccessiblePointedGraph.sup (fun _ : Unit => if source then HSet.loop else AccessiblePointedGraph.empty)

def varyingTerm (source : Bool) : El (· ∈ ·) (HSet.mk (varyingGraph source)) :=
  ⟨if source then HSet.quineAtom else ∅, by
    apply HSet.mem_range.mpr
    refine ⟨(), ?_⟩
    cases source
    · exact HSet.mk_empty
    · exact HSet.mk_loop⟩

theorem varying_graph_nonconstant : HSet.mk (varyingGraph false) ≠ HSet.mk (varyingGraph true) := by
  intro same
  have member : (∅ : HSet) ∈ HSet.mk (varyingGraph false) := (varyingTerm false).2
  rw [same] at member
  obtain ⟨_, value⟩ := HSet.mem_range.mp member
  exact HSet.empty_ne_quineAtom (HSet.mk_loop.symm.trans value).symm

theorem fine_family_descends (depth : Nat) : FamilyInvariant (readout fine depth) varyingGraph := by
  intro left right same
  exact congrArg (fun source => HSet.mk (varyingGraph source)) (fine_readout_injective depth same)

theorem fine_selected_term_descends (depth : Nat) :
    TermCompatible (readout fine depth) varyingGraph varyingTerm := by
  intro left right same
  exact congrArg (fun source => (varyingTerm source).1) (fine_readout_injective depth same)

theorem varying_coarse_family_does_not_descend (depth : Nat) :
    ¬ FamilyInvariant (readout coarse depth) varyingGraph := by
  intro invariant
  exact varying_graph_nonconstant (invariant (coarse_readout_equal depth))

theorem fine_family_decoder_exact (depth : Nat) (source : Bool) :
    decodedFamily varyingGraph (classOf (readout fine depth) source) = HSet.mk (varyingGraph source) :=
  family_beta (readout fine depth) varyingGraph (fine_family_descends depth) source

theorem fine_selected_decoder_exact (depth : Nat) (source : Bool) :
    termValue varyingGraph varyingTerm (classOf (readout fine depth) source) = (varyingTerm source).1 :=
  termValue_beta (readout fine depth) varyingGraph varyingTerm (fine_selected_term_descends depth) source

def cellOccurrences : ActionOccurrences cells.dynamics where
  Occurrence _ source target := PLift (target ∈ source.next)
  erases _ _ _ := ⟨fun ⟨proof⟩ => proof.down, fun proof => ⟨⟨proof⟩⟩⟩

def restEvent (depth : Nat) : ObservedDepthBudgetSpan.Event cells cellOccurrences :=
  ⟨depth, ⟨(), .rest, .rest, ⟨List.mem_singleton_self _⟩⟩⟩

theorem budget_source_lifts : (ObservedDepthBudgetSpan.observation cells cellOccurrences).SourceLifts :=
  ObservedDepthBudgetSpan.sourceLifts cells cellVocabulary cellOccurrences halfScale_positive

theorem budget_target_does_not_lift :
    ¬ (ObservedDepthBudgetSpan.observation cells cellOccurrences).TargetLifts := by
  intro lifting
  have same : (ObservedDepthBudgetSpan.observedSpan cells cellOccurrences).target (restEvent 0) =
      ObservedDepthBudgetSpan.stateReading cells (0, Cell.dead) := by
    apply congrArg (fun observed => (⟨0, observed⟩ : ObservedDepthBudgetSpan.ObservedState cells))
    exact (classOf_eq_iff _ _ _).mpr
      ((readout_eq_iff cells cellVocabulary 0 .rest .dead).mpr cells_rest_dead_separated.1)
  obtain ⟨lifted, target, _⟩ := lifting (0, Cell.dead) (restEvent 0) same
  have targetCell : lifted.occurrence.target = .dead := congrArg Prod.snd target
  have step := (cellOccurrences.erases _ _ _).mp ⟨lifted.occurrence.occurrence⟩
  rw [targetCell] at step
  change Cell.dead ∈ lifted.occurrence.source.next at step
  cases sourceIs : lifted.occurrence.source <;> simp [Cell.next, sourceIs] at step

theorem budget_source_occurrence_does_not_lift :
    ¬ (ObservedDepthBudgetSpan.observation cells cellOccurrences).SourceOccurrenceLifts := by
  intro lifting
  have same : (ObservedDepthBudgetSpan.observedSpan cells cellOccurrences).source (restEvent 0) =
      ObservedDepthBudgetSpan.stateReading cells (1, Cell.ping) := by
    apply congrArg (fun observed => (⟨1, observed⟩ : ObservedDepthBudgetSpan.ObservedState cells))
    exact (classOf_eq_iff _ _ _).mpr
      ((readout_eq_iff cells cellVocabulary 1 .rest .ping).mpr
        (cells.depthBound_eq_zero_of_gradedBisimilar cellVocabulary cells_rest_ping_bisimilar 1))
  obtain ⟨lifted, source, observedEvent⟩ := lifting (1, Cell.ping) (restEvent 0) same
  change lifted = restEvent 0 at observedEvent
  rw [observedEvent] at source
  have falseEquality : Cell.rest = Cell.ping := congrArg Prod.snd source
  cases falseEquality

end Mettapedia.GSLT.ObservedGradedFamilyControls
