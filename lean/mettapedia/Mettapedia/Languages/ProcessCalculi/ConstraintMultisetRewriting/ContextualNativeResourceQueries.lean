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

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body

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

abbrev ProducerQuery (body : Body S O Γ sort before after) :=
  DataQuery body.guardNativeFamily
    (GuardPhysical O × Row body.guardNativeBank body.guardNativeFamily Γ sort) (GuardPhysical O)

def sourceResourceCondition (body : Body S O Γ sort before after) : CommitPrecondition O Unit :=
  (CompiledSchedule.compile ContextualSourceSchedules.Schedule.unitLabel body.commits).condition

theorem source_resource_queries_empty (body : Body S O Γ sort before after) :
    body.sourceResourceCondition.queries = [] := by
  apply condition_queries_empty
  intro commit member
  obtain ⟨selection, _selected, rfl⟩ := List.mem_map.mp member
  rfl

def entryIdentity (occurrence : O) : GuardPhysical O := some (.inl occurrence)

omit [DecidableEq O] in
theorem entry_identity_injective : Function.Injective (entryIdentity (O := O)) :=
  fun _ _ same => Sum.inl.inj (Option.some.inj same)

def producerPresentQuery (body : Body S O Γ sort before after) : body.ProducerQuery :=
  let required := body.sourceResourceCondition.present.image entryIdentity
  ⟨fun _ label => decide (label.1 ∈ required), required⟩

def producerAbsentQuery (body : Body S O Γ sort before after) : body.ProducerQuery :=
  let forbidden := body.sourceResourceCondition.absent.image entryIdentity
  ⟨fun _ label => decide (label.1 ∈ forbidden), ∅⟩

noncomputable def producerStaticQuery (body : Body S O Γ sort before after) : body.ProducerQuery :=
  liftPoint (ofCondition (fun _ => body.ShapesHold ∧ body.sourceResourceCondition.possible = true) none)

noncomputable def producerResourceQueries (body : Body S O Γ sort before after) : List body.ProducerQuery :=
  [body.producerStaticQuery, body.producerPresentQuery, body.producerAbsentQuery]

private theorem finite_presence {N Label : Type} {Candidate : Type uA} [DecidableEq N]
    (required world : Finset N) (rows : N → Label) (candidate : Candidate) :
    ((PredicateQueryAdmission.Query.mk (fun (_ : Candidate) (label : N × Label) => decide (label.1 ∈ required)) required).atSolution candidate).Holds
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
    ((PredicateQueryAdmission.Query.mk (fun (_ : Candidate) (label : N × Label) => decide (label.1 ∈ forbidden)) ∅).atSolution candidate).Holds
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

theorem entry_presence_iff (body : Body S O Γ sort before after) (occupied : Finset Nat) (required : Finset O) :
    required.image entryIdentity ⊆ (body.nativeBindingState occupied).present ↔ required ⊆ before.present := by
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

theorem entry_absence_iff (body : Body S O Γ sort before after) (occupied : Finset Nat) (forbidden : Finset O) :
    Disjoint (forbidden.image entryIdentity) (body.nativeBindingState occupied).present ↔ Disjoint forbidden before.present := by
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

theorem producer_resource_queries_iff (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (consistent : ContextualConditionalExecution.Solvable (body.nativeBindingInformation occupied produced [])) :
    (∀ query ∈ body.producerResourceQueries,
      AskData (body.nativeBindingInformation occupied produced []) query
        (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present) ↔
      body.ShapesHold ∧ Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits := by
  have static : AskData (body.nativeBindingInformation occupied produced []) body.producerStaticQuery
      (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present ↔
      body.ShapesHold ∧ body.sourceResourceCondition.possible = true := by
    erw [producerStaticQuery, lift_point_ask_iff, ask_condition_iff _ _ _ (Finset.mem_insert_self _ _)]
    constructor
    · intro checked
      obtain ⟨Future, future, candidate, model⟩ := consistent
      exact checked Future future candidate model
    · intro holds Future future candidate _model
      exact holds
  have present : AskData (body.nativeBindingInformation occupied produced []) body.producerPresentQuery
      (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present ↔
      body.sourceResourceCondition.present ⊆ before.present := by
    constructor
    · intro checked
      obtain ⟨Future, future, candidate, model⟩ := consistent
      exact (body.entry_presence_iff occupied _).mp ((finite_presence _ _ _ (⟨Future, future, candidate⟩ : Candidate body.guardNativeFamily)).mp
        (checked Future future candidate model))
    · intro holds Future future candidate _model
      exact (finite_presence _ _ _ (⟨Future, future, candidate⟩ : Candidate body.guardNativeFamily)).mpr ((body.entry_presence_iff occupied _).mpr holds)
  have absent : AskData (body.nativeBindingInformation occupied produced []) body.producerAbsentQuery
      (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present ↔
      Disjoint body.sourceResourceCondition.absent before.present := by
    constructor
    · intro checked
      obtain ⟨Future, future, candidate, model⟩ := consistent
      exact (body.entry_absence_iff occupied _).mp ((finite_absence _ _ _ (⟨Future, future, candidate⟩ : Candidate body.guardNativeFamily)).mp
        (checked Future future candidate model))
    · intro holds Future future candidate _model
      exact (finite_absence _ _ _ (⟨Future, future, candidate⟩ : Candidate body.guardNativeFamily)).mpr ((body.entry_absence_iff occupied _).mpr holds)
  have resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits ↔
      body.sourceResourceCondition.possible = true ∧ body.sourceResourceCondition.present ⊆ before.present ∧
        Disjoint body.sourceResourceCondition.absent before.present := by
    rw [← CompiledSchedule.compile_condition_iff]
    change body.sourceResourceCondition.Holds ContextualSourceSchedules.Schedule.unitLabel before.present ↔ _
    rw [CommitPrecondition.Holds, body.source_resource_queries_empty]
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

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
