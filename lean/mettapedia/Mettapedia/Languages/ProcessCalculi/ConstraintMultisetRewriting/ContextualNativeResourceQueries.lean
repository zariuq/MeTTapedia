import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProducerAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSymbolicCountQueries

/-!
# Native queries check the whole source resource precondition

The finite compiled precondition retains required and forbidden entry
identities even when intermediate creations disappear from the net result.
Required and forbidden identities are checked against the actual inventory.
Only source port shapes and the store-independent possibility flag use a
point condition on the invocation control row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualPredicateQueryAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uA

private theorem condition_queries_empty {N : Type} [DecidableEq N] (label : N → Unit)
    (code : List (Commit N Unit)) (empty : ∀ commit ∈ code, commit.queries = []) :
    (CompiledSchedule.compile label code).condition.queries = [] := by
  induction code with
  | nil => rfl
  | cons first rest prior =>
      have initial := empty first (List.mem_cons_self ..)
      have later := prior (fun commit member => empty commit (List.mem_cons_of_mem _ member))
      change first.queries ++ ((CompiledSchedule.compile label rest).condition.queries.map _) = []
      rw [initial, later]
      rfl

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

abbrev ProducerQuery (schedule : Schedule S O Γ sort before after) :=
  DataQuery schedule.guardNativeFamily
    (GuardPhysical O × Row schedule.guardNativeBank schedule.guardNativeFamily Γ sort) (GuardPhysical O)

def sourceResourceCondition (schedule : Schedule S O Γ sort before after) : CommitPrecondition O Unit :=
  (CompiledSchedule.compile unitLabel schedule.commits).condition

theorem source_resource_queries_empty (schedule : Schedule S O Γ sort before after) :
    schedule.sourceResourceCondition.queries = [] := by
  apply condition_queries_empty
  intro commit member
  obtain ⟨selection, _selected, rfl⟩ := List.mem_map.mp member
  rfl

def entryIdentity (occurrence : O) : GuardPhysical O := some (.inl occurrence)

omit [DecidableEq O] in
theorem entry_identity_injective : Function.Injective (entryIdentity (O := O)) :=
  fun _ _ same => Sum.inl.inj (Option.some.inj same)

def producerPresentQuery (schedule : Schedule S O Γ sort before after) : schedule.ProducerQuery :=
  let required := schedule.sourceResourceCondition.present.image entryIdentity
  ⟨fun _ label => decide (label.1 ∈ required), required⟩

def producerAbsentQuery (schedule : Schedule S O Γ sort before after) : schedule.ProducerQuery :=
  let forbidden := schedule.sourceResourceCondition.absent.image entryIdentity
  ⟨fun _ label => decide (label.1 ∈ forbidden), ∅⟩

noncomputable def producerStaticQuery (schedule : Schedule S O Γ sort before after) : schedule.ProducerQuery :=
  liftPoint (ofCondition (fun _ => schedule.ShapesHold ∧ schedule.sourceResourceCondition.possible = true) none)

noncomputable def producerResourceQueries (schedule : Schedule S O Γ sort before after) : List schedule.ProducerQuery :=
  [schedule.producerStaticQuery, schedule.producerPresentQuery, schedule.producerAbsentQuery]

private theorem finite_presence {N Label : Type} {Candidate : Type uA} [DecidableEq N]
    (required world : Finset N) (rows : N → Label) (candidate : Candidate) :
    ((CensusAdmission.Query.mk (fun (_ : Candidate) (label : N × Label) => decide (label.1 ∈ required)) required).atSolution candidate).Holds
      (fun occurrence => (occurrence, rows occurrence)) world ↔ required ⊆ world := by
  change regionOf _ world (fun label : N × Label => decide (label.1 ∈ required)) = required ↔ _
  constructor
  · intro same occurrence member
    have selected : occurrence ∈ regionOf (fun occurrence => (occurrence, rows occurrence)) world
        (fun label => decide (label.1 ∈ required)) := by rw [same]; exact member
    exact (mem_regionOf.mp selected).1
  · intro present
    ext occurrence
    simp only [mem_regionOf, decide_eq_true_eq]
    exact ⟨And.right, fun member => ⟨present member, member⟩⟩

private theorem finite_absence {N Label : Type} {Candidate : Type uA} [DecidableEq N]
    (forbidden world : Finset N) (rows : N → Label) (candidate : Candidate) :
    ((CensusAdmission.Query.mk (fun (_ : Candidate) (label : N × Label) => decide (label.1 ∈ forbidden)) ∅).atSolution candidate).Holds
      (fun occurrence => (occurrence, rows occurrence)) world ↔ Disjoint forbidden world := by
  change regionOf _ world (fun label : N × Label => decide (label.1 ∈ forbidden)) = ∅ ↔ _
  constructor
  · intro empty
    apply Finset.disjoint_left.mpr
    intro occurrence excluded present
    have selected : occurrence ∈ regionOf (fun occurrence => (occurrence, rows occurrence)) world
        (fun label => decide (label.1 ∈ forbidden)) := mem_regionOf.mpr ⟨present, decide_eq_true excluded⟩
    rw [empty] at selected
    exact Finset.notMem_empty _ selected
  · intro apart
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro occurrence member
    obtain ⟨present, excluded⟩ := mem_regionOf.mp member
    exact Finset.disjoint_left.mp apart (of_decide_eq_true excluded) present

theorem entry_presence_iff (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) (required : Finset O) :
    required.image entryIdentity ⊆ (schedule.nativeBindingState occupied).present ↔ required ⊆ before.present := by
  constructor
  · intro checked occurrence member
    have inside := checked (Finset.mem_image_of_mem entryIdentity member)
    change entryIdentity occurrence ∈ insert none (before.present.image entryIdentity) at inside
    rcases Finset.mem_insert.mp inside with impossible | old
    · cases impossible
    · obtain ⟨original, present, same⟩ := Finset.mem_image.mp old
      have equal := entry_identity_injective same
      exact equal ▸ present
  · intro checked physical member
    obtain ⟨occurrence, original, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem entryIdentity (checked original))

theorem entry_absence_iff (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) (forbidden : Finset O) :
    Disjoint (forbidden.image entryIdentity) (schedule.nativeBindingState occupied).present ↔ Disjoint forbidden before.present := by
  constructor
  · intro apart
    apply Finset.disjoint_left.mpr
    intro occurrence excluded present
    exact Finset.disjoint_left.mp apart (Finset.mem_image_of_mem entryIdentity excluded)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem entryIdentity present))
  · intro apart
    apply Finset.disjoint_left.mpr
    intro physical excluded present
    obtain ⟨occurrence, original, rfl⟩ := Finset.mem_image.mp excluded
    change entryIdentity occurrence ∈ insert none (before.present.image entryIdentity) at present
    rcases Finset.mem_insert.mp present with impossible | old
    · cases impossible
    · obtain ⟨other, visible, same⟩ := Finset.mem_image.mp old
      have equal := entry_identity_injective same
      subst other
      exact Finset.disjoint_left.mp apart original visible

theorem producer_resource_queries_iff (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (consistent : ContextualConditionalExecution.Solvable (schedule.nativeBindingInformation occupied schedule.producerValues [])) :
    (∀ query ∈ schedule.producerResourceQueries,
      AskData (schedule.nativeBindingInformation occupied schedule.producerValues []) query
        (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present) ↔
      schedule.ShapesHold ∧ Executable unitLabel before.present schedule.commits := by
  have static : AskData (schedule.nativeBindingInformation occupied schedule.producerValues []) schedule.producerStaticQuery
      (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present ↔
      schedule.ShapesHold ∧ schedule.sourceResourceCondition.possible = true := by
    erw [producerStaticQuery, lift_point_ask_iff, ask_condition_iff _ _ _ (Finset.mem_insert_self _ _)]
    constructor
    · intro checked
      obtain ⟨Future, future, candidate, model⟩ := consistent
      exact checked Future future candidate model
    · intro holds Future future candidate _model
      exact holds
  have present : AskData (schedule.nativeBindingInformation occupied schedule.producerValues []) schedule.producerPresentQuery
      (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present ↔
      schedule.sourceResourceCondition.present ⊆ before.present := by
    constructor
    · intro checked
      obtain ⟨Future, future, candidate, model⟩ := consistent
      exact (schedule.entry_presence_iff occupied _).mp ((finite_presence _ _ _ (⟨Future, future, candidate⟩ : Candidate schedule.guardNativeFamily)).mp
        (checked Future future candidate model))
    · intro holds Future future candidate _model
      exact (finite_presence _ _ _ (⟨Future, future, candidate⟩ : Candidate schedule.guardNativeFamily)).mpr ((schedule.entry_presence_iff occupied _).mpr holds)
  have absent : AskData (schedule.nativeBindingInformation occupied schedule.producerValues []) schedule.producerAbsentQuery
      (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present ↔
      Disjoint schedule.sourceResourceCondition.absent before.present := by
    constructor
    · intro checked
      obtain ⟨Future, future, candidate, model⟩ := consistent
      exact (schedule.entry_absence_iff occupied _).mp ((finite_absence _ _ _ (⟨Future, future, candidate⟩ : Candidate schedule.guardNativeFamily)).mp
        (checked Future future candidate model))
    · intro holds Future future candidate _model
      exact (finite_absence _ _ _ (⟨Future, future, candidate⟩ : Candidate schedule.guardNativeFamily)).mpr ((schedule.entry_absence_iff occupied _).mpr holds)
  have resources : Executable unitLabel before.present schedule.commits ↔
      schedule.sourceResourceCondition.possible = true ∧ schedule.sourceResourceCondition.present ⊆ before.present ∧
        Disjoint schedule.sourceResourceCondition.absent before.present := by
    rw [← CompiledSchedule.compile_condition_iff]
    change schedule.sourceResourceCondition.Holds unitLabel before.present ↔ _
    rw [CommitPrecondition.Holds, schedule.source_resource_queries_empty]
    simp only [List.not_mem_nil, false_implies, implies_true, and_true]
  constructor
  · intro checked
    have one := static.mp (checked _ (List.mem_cons_self ..))
    have two := present.mp (checked _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have three := absent.mp (checked _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    exact ⟨one.1, resources.mpr ⟨one.2, two, three⟩⟩
  · rintro ⟨shapes, executable⟩ query member
    have parts := resources.mp executable
    simp only [producerResourceQueries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact static.mpr ⟨shapes, parts.1⟩
    · exact present.mpr parts.2.1
    · exact absent.mpr parts.2.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
