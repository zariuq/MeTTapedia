import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.AtomicFusion
import Mettapedia.Languages.MeTTa.TransformComposition

/-! # Separating controls for overlap composition and transported conditions -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CompositionControls

open Mettapedia.Languages.MeTTa.TransformComposition

def maker : Span ℕ := ⟨0, 0, {0}⟩
def taker : Span ℕ := ⟨{0}, 0, 0⟩

/-- Two valid overlaps have different initial resource requirements. -/
theorem overlap_choice_matters :
    maker.IsOverlap taker 0 ∧ maker.IsOverlap taker {0} ∧
      ¬ (maker.composeAlong taker 0).Enables 0 ∧
      (maker.composeAlong taker {0}).Enables 0 := by
  decide

/-- With an extra original token both overlaps are possible and have equal
final bags, while retaining different consumption and production. -/
theorem same_bag_distinct_overlap :
    (maker.composeAlong taker 0).Enables {0} ∧
      (maker.composeAlong taker {0}).Enables {0} ∧
      (maker.composeAlong taker 0).fire {0} =
        (maker.composeAlong taker {0}).fire {0} ∧
      (maker.composeAlong taker 0).consume ≠
        (maker.composeAlong taker {0}).consume := by
  decide

/-- Net bag effects can cancel without erasing the allocation choice. -/
theorem counted_make_take_is_unit : maker.compose taker = Span.unit := by
  decide

def makeOccurrence : Commit ℕ ℕ := Commit.makeOne 1
def takeOccurrence : Commit ℕ ℕ := Commit.takeOne 1
def unchanged : Commit ℕ ℕ := ⟨∅, ∅, ∅, []⟩

/-- Cancelling final writes does not remove intermediate freshness. -/
theorem cancelled_writes_still_require_freshness :
    (CommitPrecondition.sequential id makeOccurrence takeOccurrence).Holds id ∅ ∧
      ¬ (CommitPrecondition.sequential id makeOccurrence takeOccurrence).Holds id {1} ∧
      Enabled id {1} unchanged ∧ fire (fire ∅ makeOccurrence) takeOccurrence = ∅ := by
  decide

/-- The composed update alone accepts a store rejected by the transported guard. -/
theorem net_update_is_not_the_admission_condition :
    Enabled id {1} (makeOccurrence.compose takeOccurrence) ∧
      ¬ (CommitPrecondition.sequential id makeOccurrence takeOccurrence).Holds id {1} := by
  decide

/-- The model permits reusing a consumed identifier; the final store observes
the original occurrence as retained. A native globally-fresh allocator is stricter. -/
theorem restored_input_is_retained :
    (takeOccurrence.compose makeOccurrence).taken = ∅ ∧
      (takeOccurrence.compose makeOccurrence).made = ∅ ∧
      (takeOccurrence.compose makeOccurrence).kept = {1} ∧
      (CommitPrecondition.sequential id takeOccurrence makeOccurrence).Holds id {1} := by
  decide

def emptyRegion : PredicateQuery ℕ ℕ := ⟨fun n => decide (n = 1), ∅⟩

/-- An absence condition can become true because the matching item was consumed. -/
theorem absence_after_consumption :
    ¬ emptyRegion.Holds id {1} ∧ emptyRegion.Holds id (fire {1} takeOccurrence) ∧
      (emptyRegion.pullback id takeOccurrence).seen = {1} ∧
      (emptyRegion.pullback id takeOccurrence).Holds id {1} := by
  decide

/-- An update that creates a member cannot satisfy absence of its region. -/
theorem incompatible_output_refused :
    ¬ emptyRegion.Compatible id makeOccurrence ∧
      ¬ emptyRegion.Holds id (fire ∅ makeOccurrence) := by
  decide

/-- A postcondition cannot still observe the occurrence just consumed. -/
theorem consumed_observation_refused :
    ¬ (⟨fun _ => true, {1}⟩ : PredicateQuery ℕ ℕ).Compatible id takeOccurrence := by
  decide

/-- Repeated observations retain their positions through the compiled precondition. -/
theorem repeated_queries_retained :
    let p : CommitPrecondition ℕ ℕ := ⟨∅, ∅, [emptyRegion, emptyRegion], true⟩
    (p.before id takeOccurrence).queries.length = 2 := by
  rfl

def readObserver : Commit ℕ ℕ := ⟨∅, {1}, {2}, []⟩
def absenceObserver : Commit ℕ ℕ := ⟨∅, ∅, {2}, [emptyRegion]⟩

/-- A positive reader can observe an intermediate output that net-effect
composition removes. It cannot run before or after the atomic composite. -/
theorem fusion_can_hide_readable_output :
    Enabled id ∅ makeOccurrence ∧
      Enabled id (fire ∅ makeOccurrence) readObserver ∧
      Enabled id (fire (fire ∅ makeOccurrence) readObserver) takeOccurrence ∧
      ¬ Enabled id ∅ readObserver ∧
      ¬ Enabled id (fire ∅ (makeOccurrence.compose takeOccurrence)) readObserver ∧
      fire (fire (fire ∅ makeOccurrence) readObserver) takeOccurrence = {2} := by
  decide

/-- Avoiding the first output alone is not sufficient for atomic fusion:
the first step makes nothing, yet an observer sees the removal window. -/
theorem fusion_can_hide_removal_window :
    takeOccurrence.made = ∅ ∧
      Enabled id {1} takeOccurrence ∧
      Enabled id (fire {1} takeOccurrence) absenceObserver ∧
      Enabled id (fire (fire {1} takeOccurrence) absenceObserver) makeOccurrence ∧
      ¬ Enabled id {1} absenceObserver ∧
      ¬ Enabled id (fire {1} (takeOccurrence.compose makeOccurrence)) absenceObserver ∧
      fire (fire (fire {1} takeOccurrence) absenceObserver) makeOccurrence = {1, 2} := by
  decide

def independentObserver : Commit ℕ ℕ := ⟨∅, {3}, {4}, []⟩

/-- A real intervening reader/writer can move past the second step when the
full dependency condition holds; its visible output is retained by fusion. -/
theorem independent_interleaving_can_fuse :
    (CommitPrecondition.sequential id makeOccurrence takeOccurrence).Holds id {3} ∧
      Executable id {3} [makeOccurrence.compose takeOccurrence, independentObserver] ∧
      fireList {3} [makeOccurrence.compose takeOccurrence, independentObserver] = {3, 4} := by
  have movable : ∀ observer ∈ [independentObserver], TraceIndependent id observer takeOccurrence := by
    intro observer member
    simp only [List.mem_singleton] at member
    subst member
    unfold TraceIndependent Independent Clash Spoils WritesInto Commit.uses
    decide
  have original : Executable id {3} [makeOccurrence, independentObserver, takeOccurrence] :=
    .cons (by decide) (.cons (by decide) (.cons (by decide) (.nil _)))
  have fused := (executable_fusion_iff makeOccurrence takeOccurrence [independentObserver] []
    movable).mp original
  exact ⟨fused.1, fused.2, by decide⟩

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CompositionControls
