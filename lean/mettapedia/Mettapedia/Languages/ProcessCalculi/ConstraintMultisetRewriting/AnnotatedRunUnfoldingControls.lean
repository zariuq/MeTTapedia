import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfoldingWorlds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAbsence

/-! # Competing alternatives, finite completeness and causal history controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding.Controls

open AnnotatedRuns
open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label start taker reader)

def catalogue := [taker, reader]

theorem both_orders_enumerated :
    [taker, reader] ∈ frontier A label catalogue 2 start ∧
      [reader, taker] ∈ frontier A label catalogue 2 start := by
  constructor
  · exact (mem_frontier A label catalogue 2 start _).mpr
      ⟨rfl, AnnotatedRuns.Controls.taker_then_reader, by simp [catalogue]⟩
  · exact (mem_frontier A label catalogue 2 start _).mpr
      ⟨rfl, AnnotatedRuns.Controls.shared_variables_swap.1, by simp [catalogue]⟩

/-- Two scheduling histories are present, but the causal class is one. -/
theorem independent_orders_share_causal_class :
    (Quot.mk (RoundEquiv A label start) [taker, reader]) =
      Quot.mk (RoundEquiv A label start) [reader, taker] :=
  Quot.sound (traceEquiv_roundEquiv A label AnnotatedRuns.Controls.swapped_words
    start AnnotatedRuns.Controls.taker_then_reader)

theorem represented_causal_class :
    Quot.mk (RoundEquiv A label start) [taker, reader] ∈ causalFrontier A label catalogue 2 start := by
  apply (mem_causalFrontier A label catalogue 2 start _).mpr
  exact ⟨[taker, reader], rfl, AnnotatedRuns.Controls.taker_then_reader, by simp [catalogue], rfl⟩

/-- A depth-zero node is available although source work is enabled. -/
theorem zero_depth_is_not_completion :
    [] ∈ frontier A label catalogue 0 start ∧ [] ∉ completed A label catalogue 0 start := by
  constructor
  · exact (mem_frontier A label catalogue 0 start []).mpr
      ⟨rfl, ⟨AnnotatedRuns.Controls.zeros, by intro equation member; cases member⟩, by simp⟩
  · intro member
    have terminal := ((mem_completed A label catalogue 0 start []).mp member).2.2.2
    exact terminal taker (by simp [catalogue]) AnnotatedRuns.Controls.taker_valid

def weight (firing : AnnotatedRuns.Controls.Run) := firing.selection.taken.length

/-- An exhausted classifier has found no answer, but its pending candidate
and independently valid firing rule out a completion certificate. -/
theorem unresolved_is_not_absorbing :
    known [taker] (fun _ => none) = [] ∧
      pending [taker] (fun _ => none) = [taker] ∧
      ¬ Terminal A label [taker] start := by
  refine ⟨rfl, rfl, ?_⟩
  intro terminal
  exact terminal taker (by simp) AnnotatedRuns.Controls.taker_valid

/-- Observing only the chosen candidate would falsely certify maximality. -/
theorem competitor_changes_maximum :
    Maximal A label [reader] start weight reader ∧
      ¬ Maximal A label catalogue start weight reader := by
  have readReady := AnnotatedRuns.Controls.shared_variables_swap.1.1
  constructor
  · apply (maximal_iff A label [reader] start weight reader).mpr
    refine ⟨by simp, readReady, ?_⟩
    intro other member _
    have same := List.mem_singleton.mp member
    subst other
    exact Nat.le_refl _
  · intro maximal
    have greatest := ((maximal_iff A label catalogue start weight reader).mp maximal).2.2
      taker (by simp [catalogue]) AnnotatedRuns.Controls.taker_valid
    change 1 ≤ 0 at greatest
    omega

/-- Collection is over branches, not over distinct returned payloads. -/
theorem equal_answers_from_two_worlds_survive :
    collect label start (fun _ => [(7 : Nat)]) [[taker], [reader]] = [7, 7] := rfl

theorem noFlow_does_not_remove_read_take_precedence :
    ¬ Flow reader (⟨reader.rule, [], ⟨[1], [], []⟩⟩ : AnnotatedRuns.Controls.Run) ∧
      ReadBeforeTake reader (⟨reader.rule, [], ⟨[1], [], []⟩⟩ : AnnotatedRuns.Controls.Run) := by
  constructor
  · simp [Flow, AnnotatedRuns.Controls.reader]
  · exact ⟨1, by simp [AnnotatedRuns.Controls.reader], by simp⟩

open AnnotatedRuns.RoundControls (tellSame tellOne tellTwo)

/-- Pairwise constraint checks cannot replace joint consistency in an
unfolding node. The forbidden triple is absent in every order. -/
theorem inconsistent_triple_never_enumerated (word : List AnnotatedRuns.Controls.Run)
    (permuted : word.Perm [tellSame, tellOne, tellTwo]) :
    word ∉ frontier A label [tellSame, tellOne, tellTwo] 3 AnnotatedRuns.RoundControls.empty := by
  intro member
  exact AnnotatedRuns.RoundControls.pairwise_consistent_not_joint word permuted
    (frontier_sound A label member)

namespace RestoredAbsence

open AnnotatedRuns.AbsenceControls (maker empty restored_absence_two_traces)

local notation "absenceLabel" => AnnotatedRuns.AbsenceControls.label
local notation "absenceReader" => AnnotatedRuns.AbsenceControls.reader
local notation "absenceTaker" => AnnotatedRuns.AbsenceControls.taker

/-- The same bare firings and endpoint can carry distinct contextual causal
histories. An event-structure encoding must distinguish their contexts. -/
theorem both_histories_survive_unfolding :
    [absenceReader, maker, absenceTaker] ∈ frontier A absenceLabel [absenceReader, maker, absenceTaker] 3 empty ∧
      [maker, absenceTaker, absenceReader] ∈ frontier A absenceLabel [absenceReader, maker, absenceTaker] 3 empty ∧
      ¬ RoundEquiv A absenceLabel empty [absenceReader, maker, absenceTaker] [maker, absenceTaker, absenceReader] := by
  obtain ⟨first, second, _, _, different, _⟩ := restored_absence_two_traces
  exact ⟨(mem_frontier A absenceLabel _ 3 empty _).mpr ⟨rfl, first, by simp⟩,
    (mem_frontier A absenceLabel _ 3 empty _).mpr ⟨rfl, second, by simp⟩, different⟩

end RestoredAbsence

#print axioms mem_frontier
#print axioms mem_completed
#print axioms closed_frontier_bounds
#print axioms completed_exact_of_closed_frontier
#print axioms mem_causalFrontier
#print axioms closed_classifier_exact
#print axioms certified_empty_iff_terminal
#print axioms collectQueries_stable
#print axioms competitor_changes_maximum
#print axioms inconsistent_triple_never_enumerated
#print axioms RestoredAbsence.both_histories_survive_unfolding

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding.Controls
