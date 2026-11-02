import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionCompleteness

/-!
# Static physical layouts with retained, potentially aliased reads

These resource and equation conditions do not assert source executability.
They retain original rules, including their checks. The remaining guard
obligation is deliberately separate from the one common consistency model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SharedReadProcessLayouts

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open LinearConnectionLayout ConditionalComposite

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def Supplied (initial : Finset O) (events : List (Event T O)) : Prop :=
  ∀ earlier event suffix, events = earlier ++ event :: suffix →
    event.2.taken.toFinset ∪ event.2.read.toFinset ⊆ initial ∪ made earlier

structure Layout (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : List (Event T O)) : Prop where
  shapes : ∀ event ∈ events, (ShapeTest.ofSelection event.1 event.2).Holds label
  produced_distinct : (events.flatMap fun event => event.2.made).Nodup
  consumed_distinct : (events.flatMap fun event => event.2.taken).Nodup
  fresh_boundary : Disjoint (made events) before.present
  supplied : Supplied before.present events
  take_read_apart : ∀ event ∈ events, Disjoint event.2.taken.toFinset event.2.read.toFinset
  reads_before_takes : events.Pairwise fun first second => GuardFreeProcessOrders.NoAsym second first
  incoming : A.Models assignment before.equations
  connections : ∀ event ∈ events, A.Models assignment (addedEquations label event.1 event.2)

namespace Layout

variable {A : SubstitutionAction T S} {assignment : S} {label : O → T}
  {before : Configuration T O} {event : Event T O} {events : List (Event T O)}

theorem head_occurrences (layout : Layout A assignment label before (event :: events)) :
    Enabled label before.present (event.2.commit (T := T)) := by
  have supplied : event.2.taken.toFinset ∪ event.2.read.toFinset ⊆ before.present := by
    simpa using layout.supplied [] event events rfl
  refine ⟨fun o member => supplied (Finset.mem_union_left _ member),
    fun o member => supplied (Finset.mem_union_right _ member),
    layout.take_read_apart event List.mem_cons_self, ?_, ?_⟩
  · exact Finset.disjoint_of_subset_left (by
      intro o member
      have inside : o ∈ event.2.made.toFinset := by simpa [Selection.commit] using member
      simpa only [made_cons] using Finset.mem_union_left (made events) inside) layout.fresh_boundary
  · intro query member
    cases member

theorem head_consistent (layout : Layout A assignment label before (event :: events)) :
    A.Models assignment (event.2.problem label event.1 before) := by
  rw [problem_eq, A.models_append]
  exact ⟨layout.incoming, layout.connections event List.mem_cons_self⟩

theorem tail (layout : Layout A assignment label before (event :: events)) :
    Layout A assignment label (event.2.result label event.1 before) events := by
  have producerSplit := List.nodup_append.mp layout.produced_distinct
  have consumerSplit := List.nodup_append.mp layout.consumed_distinct
  have readSplit := List.pairwise_cons.mp layout.reads_before_takes
  refine ⟨fun selected member => layout.shapes selected (List.mem_cons_of_mem _ member),
    producerSplit.2.1, consumerSplit.2.1, ?_, ?_,
    fun selected member => layout.take_read_apart selected (List.mem_cons_of_mem _ member),
    readSplit.2, layout.head_consistent, fun selected member =>
      layout.connections selected (List.mem_cons_of_mem _ member)⟩
  · refine Finset.disjoint_left.mpr fun o inTail inResult => ?_
    rcases mem_fire.mp inResult with ⟨inBefore, _⟩ | inHead
    · exact Finset.disjoint_left.mp layout.fresh_boundary (by simp [inTail]) inBefore
    · exact producerSplit.2.2 o (by simpa [Selection.commit] using inHead) o
        (by simpa [made] using inTail) rfl
  · intro earlier selected suffix decomposition o selectedPort
    have oldSupply := layout.supplied (event :: earlier) selected suffix
      (by simp [decomposition]) selectedPort
    have selectedMember : selected ∈ events := by rw [decomposition]; simp
    have notHead : o ∉ event.2.taken.toFinset := by
      intro headTake
      rcases Finset.mem_union.mp selectedPort with selectedTake | selectedRead
      · exact consumerSplit.2.2 o (by simpa using headTake) o
          (List.mem_flatMap.mpr ⟨selected, selectedMember, by simpa using selectedTake⟩) rfl
      · exact readSplit.1 selected selectedMember o (by simpa using selectedRead)
          (by simpa using headTake)
    simp only [made_cons, Finset.mem_union] at oldSupply
    rcases oldSupply with inBefore | inHead | inPrefix
    · exact Finset.mem_union_left _ (mem_fire.mpr (Or.inl ⟨inBefore, notHead⟩))
    · exact Finset.mem_union_left _ (mem_fire.mpr (Or.inr inHead))
    · exact Finset.mem_union_right _ inPrefix

theorem residual_after_head (layout : Layout A assignment label before (event :: events)) :
    residual (event.2.result label event.1 before).present events =
      residual before.present (event :: events) := by
  have noProducedTake : Disjoint (made (event :: events)) event.2.taken.toFinset :=
    Finset.disjoint_of_subset_right layout.head_occurrences.taken_subset layout.fresh_boundary
  ext o
  have apart : o ∈ made (event :: events) → o ∉ event.2.taken.toFinset :=
    fun member => Finset.disjoint_left.mp noProducedTake member
  simp only [LinearConnectionLayout.residual, made_cons, taken_cons, Selection.result, fire,
    Selection.commit, Finset.mem_sdiff, Finset.mem_union]
  simp only [made_cons, Finset.mem_union] at apart
  tauto

theorem final_rows : ∀ {events : List (Event T O)} {before : Configuration T O},
    Layout A assignment label before events →
      (ConditionalSchedule.follow label before events).present = residual before.present events
  | [], _before, _layout => by simp [ConditionalSchedule.follow, LinearConnectionLayout.residual]
  | _ :: _, _before, layout => (final_rows layout.tail).trans layout.residual_after_head

theorem final_model (layout : Layout A assignment label before events) :
    A.Models assignment (ConditionalSchedule.follow label before events).equations :=
  (models_follow_iff A assignment label events before).mpr ⟨layout.incoming, layout.connections⟩

theorem initial_segment {earlier suffix : List (Event T O)}
    (layout : Layout A assignment label before (earlier ++ suffix)) :
    Layout A assignment label before earlier := by
  refine ⟨fun selected member => layout.shapes selected (List.mem_append_left _ member),
    ?_, ?_, ?_, ?_, fun selected member =>
      layout.take_read_apart selected (List.mem_append_left _ member),
    (List.pairwise_append.mp layout.reads_before_takes).1, layout.incoming,
    fun selected member => layout.connections selected (List.mem_append_left _ member)⟩
  · have distinct := layout.produced_distinct
    rw [List.flatMap_append] at distinct
    exact (List.nodup_append.mp distinct).1
  · have distinct := layout.consumed_distinct
    rw [List.flatMap_append] at distinct
    exact (List.nodup_append.mp distinct).1
  · refine Finset.disjoint_of_subset_left ?_ layout.fresh_boundary
    intro o member
    simp only [made, List.flatMap_append, List.mem_toFinset, List.mem_append] at member ⊢
    exact Or.inl member
  · intro front selected rest decomposition
    exact layout.supplied front selected (rest ++ suffix) (by simp [decomposition, List.append_assoc])

theorem drop_prefix : ∀ (earlier suffix : List (Event T O)) (before : Configuration T O),
    Layout A assignment label before (earlier ++ suffix) →
      Layout A assignment label (ConditionalSchedule.follow label before earlier) suffix
  | [], _suffix, _before, layout => layout
  | _ :: earlier, suffix, _before, layout => drop_prefix earlier suffix _ layout.tail

end Layout

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SharedReadProcessLayouts
