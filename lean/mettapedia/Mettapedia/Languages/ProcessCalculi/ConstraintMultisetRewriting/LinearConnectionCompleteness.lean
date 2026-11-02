import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionLayout
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders

/-!
# Exact static connections for fresh pure occurrence schedules

With globally fresh, uniquely produced physical identities, actual pure
schedules yield static linear connection certificates. The converse is the
certificate's independent sequentialization theorem. The existing process
order theorem then characterizes every permitted reordering; no adjacent
swap theorem or second execution calculus is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionLayout

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConditionalComposite
open GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

theorem produced_distinct_of_executable :
    ∀ (events : List (Event T O)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before events → UniqueMakers events →
        (events.flatMap fun event => event.2.made).Nodup
  | [], _before, _executes, _unique => List.nodup_nil
  | event :: events, before, executes, unique => by
      obtain ⟨headUnique, tailUnique⟩ := List.pairwise_cons.mp unique
      apply List.nodup_append.mpr
      refine ⟨executes.1.output_distinct,
        produced_distinct_of_executable events (event.2.result label event.1 before) executes.2 tailUnique, ?_⟩
      intro o inHead other inTail same
      subst other
      obtain ⟨producer, member, produced⟩ := List.mem_flatMap.mp inTail
      exact headUnique producer member o inHead produced

/-- Once taken, a physical occurrence cannot be consumed again when no
future event is allowed to recreate its identity. -/
theorem consumed_distinct_of_executable :
    ∀ (events : List (Event T O)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before events → FreshFrom before events → UniqueMakers events →
        (events.flatMap fun event => event.2.taken).Nodup
  | [], _before, _executes, _fresh, _unique => List.nodup_nil
  | event :: events, before, executes, fresh, unique => by
      obtain ⟨headUnique, tailUnique⟩ := List.pairwise_cons.mp unique
      apply List.nodup_append.mpr
      refine ⟨executes.1.take_distinct,
        consumed_distinct_of_executable events (event.2.result label event.1 before) executes.2
          (fresh_after label fresh headUnique) tailUnique, ?_⟩
      intro o inHead other inTail same
      subst other
      obtain ⟨consumer, member, consumed⟩ := List.mem_flatMap.mp inTail
      have initial := executes.1.occurrences.taken_subset (by simpa [Selection.commit] using inHead)
      have gone := executes.1.consumed_removed inHead
      have neverMade : ∀ producer ∈ events, o ∉ producer.2.made :=
        fun producer member made => fresh producer (List.mem_cons_of_mem _ member) o made initial
      exact (absent_stays A label events _ o executes.2 gone neverMade consumer member).2 consumed

theorem fresh_boundary_of_fresh_from (events : List (Event T O)) (before : Configuration T O)
    (fresh : FreshFrom before events) : Disjoint (made events) before.present := by
  refine Finset.disjoint_left.mpr fun o produced initial => ?_
  have inList : o ∈ events.flatMap (fun event => event.2.made) := List.mem_toFinset.mp produced
  obtain ⟨producer, member, created⟩ := List.mem_flatMap.mp inList
  exact fresh producer member o created initial

/-- No source acceptance occurs in the target certificate's fields. Each
field is extracted from actual source evidence under the occurrence-net
freshness hypotheses, including the global equation model. -/
theorem certificate_of_executable {program : Set (RuleInstance T)} {assignment : S}
    (events : List (Event T O)) (before : Configuration T O)
    (executes : ConditionalSchedule.Executable A label before events)
    (fresh : FreshFrom before events) (unique : UniqueMakers events)
    (pure : LinearHornAdequacy.Pure events) (declared : LinearHornAdequacy.Declared program events)
    (solved : A.Models assignment (ConditionalSchedule.follow label before events).equations) :
    Certificate A program assignment label before events := by
  have models := (models_follow_iff A assignment label events before).mp solved
  exact ⟨shapes_of_executable A label events before executes, pure, declared,
    produced_distinct_of_executable A label events before executes unique,
    consumed_distinct_of_executable A label events before executes fresh unique,
    fresh_boundary_of_fresh_from events before fresh,
    supplied_of_executable A label events before executes, models.1, models.2⟩

theorem executable_iff_certificate {program : Set (RuleInstance T)} {assignment : S}
    (events : List (Event T O)) (before : Configuration T O)
    (fresh : FreshFrom before events) (unique : UniqueMakers events)
    (pure : LinearHornAdequacy.Pure events) (declared : LinearHornAdequacy.Declared program events) :
    (ConditionalSchedule.Executable A label before events ∧
      A.Models assignment (ConditionalSchedule.follow label before events).equations) ↔
        Certificate A program assignment label before events :=
  ⟨fun ⟨executes, solved⟩ => certificate_of_executable A label events before executes fresh unique pure declared solved,
    Certificate.executes⟩

namespace Certificate

variable {A : SubstitutionAction T S} {program : Set (RuleInstance T)} {assignment : S}
  {label : O → T} {before : Configuration T O} {events : List (Event T O)}

theorem fresh_from (layout : Certificate A program assignment label before events) : FreshFrom before events := by
  intro producer member o produced initial
  have inList : o ∈ events.flatMap (fun event => event.2.made) :=
    List.mem_flatMap.mpr ⟨producer, member, produced⟩
  exact Finset.disjoint_left.mp layout.fresh_boundary (List.mem_toFinset.mpr inList) initial

theorem unique_makers (layout : Certificate A program assignment label before events) : UniqueMakers events := by
  have distinct := layout.produced_distinct
  clear layout
  induction events with
  | nil => exact List.Pairwise.nil
  | cons event events ih =>
      obtain ⟨_, tailDistinct, headTail⟩ := List.nodup_append.mp distinct
      refine List.pairwise_cons.mpr ⟨?_, ih tailDistinct⟩
      intro producer member o inHead inTail
      exact headTail o inHead o (List.mem_flatMap.mpr ⟨producer, member, inTail⟩) rfl

theorem respects_causality (layout : Certificate A program assignment label before events) :
    events.Pairwise LaterIndependent :=
  runs_respect_order A label events before layout.executes.1 layout.fresh_from layout.unique_makers

/-- The already-proved process criterion applies to the static connection
certificate: permitted orders are exactly the source's actual executions.
The comparison retains the fixed selections and common equation constraints. -/
theorem reorderings (layout : Certificate A program assignment label before events)
    (order : List (Event T O)) (perm : events.Perm order) :
    (ConditionalSchedule.Executable A label before order ↔ order.Pairwise LaterIndependent) ∧
      (ConditionalSchedule.Executable A label before order →
        SameUpTo A (ConditionalSchedule.follow label before events)
          (ConditionalSchedule.follow label before order)) :=
  runs_are_exactly_linearizations A label events order before perm
    (fun event member => (layout.pure event member).2) layout.fresh_from layout.unique_makers layout.executes.1

/-- Every permitted order has an independent Horn proof over the same full
physical residual boundary and shared assignment. Its rule-use order is kept;
different sequentializations are not identified as equal proof objects. -/
theorem logical_proof_of_linearization [DecidableEq T] (structural : A.E = Eq)
    (layout : Certificate A program assignment label before events)
    (order : List (Event T O)) (perm : events.Perm order) (ordered : order.Pairwise LaterIndependent) :
    ∃ proof : LinearHornAdequacy.Proof A program assignment
        (labels (PositiveResourceProjection.realized A assignment label) before.present)
        (labels (PositiveResourceProjection.realized A assignment label) (residual before.present events)),
      proof.uses.map (LinearHornAdequacy.rawRule A program assignment) = order.map Prod.fst := by
  have comparison := layout.reorderings order perm
  have executable := comparison.1.mpr ordered
  have same := comparison.2 executable
  have solved : A.Models assignment (ConditionalSchedule.follow label before order).equations :=
    (same.1 assignment).mp layout.executes.2
  have boundary : (ConditionalSchedule.follow label before order).present = residual before.present events :=
    same.2.symm.trans layout.final_rows
  rw [← boundary]
  exact LinearHornAdequacy.proof_of_constraint_schedule A program assignment label structural order before
    executable (fun event member => layout.pure event (perm.mem_iff.mpr member))
    (fun event member => layout.declared event (perm.mem_iff.mpr member)) solved

end Certificate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionLayout
