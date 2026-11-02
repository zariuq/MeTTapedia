import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadSupportAllocation

/-!
# Read-support allocation retains ordinary physical reads

Support classes are allocated as distinct rows. Repeated ports use the same
allocated row, which remains present. Consumption and fresh production are
constructed separately; reads are never implemented by consume-and-republish.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PositiveResourceProjection (realized readFootprint)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {assignment : S} {label : O → T} {rule : RuleInstance T}

namespace ReadAllocation

variable {plan : ReadPlan A assignment label rule} {world : Finset O}

noncomputable def readList (allocation : ReadAllocation plan world) : List O :=
  List.ofFn (fun port => allocation.embedding (plan.portClass port))

theorem readList_support (allocation : ReadAllocation plan world) :
    allocation.readList.toFinset = allocation.slots.toFinset := by
  ext occurrence
  simp only [readList, List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨port, rfl⟩
    exact allocation.embedding_mem _
  · intro member
    obtain ⟨row, atRow⟩ := allocation.embedding_surjective_slots occurrence member
    obtain ⟨port, atPort⟩ := ReadPortPushouts.readQuotient_surjective plan.selection row
    refine ⟨port.down, ?_⟩
    change allocation.embedding (ReadPortPushouts.readQuotient plan.selection port) = occurrence
    rw [atPort]
    exact atRow

theorem readList_values (allocation : ReadAllocation plan world) :
    allocation.readList.map (realized A assignment label) =
      plan.prototype.map (realized A assignment label) := by
  calc
    _ = List.ofFn (fun port => realized A assignment label (allocation.embedding (plan.portClass port))) :=
      List.map_ofFn (f := fun port => allocation.embedding (plan.portClass port))
        (g := realized A assignment label)
    _ = List.ofFn (fun port => realized A assignment label (plan.prototype.get port)) :=
      congrArg List.ofFn (funext (fun port => allocation.embedding_values (plan.portClass port)))
    _ = _ := by
      simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map plan.prototype (realized A assignment label)

theorem readList_matches (allocation : ReadAllocation plan world) (structural : A.E = Eq) :
    List.Forall₂ (fun pattern occurrence =>
      A.E (A.apply assignment pattern) (A.apply assignment (label occurrence))) rule.read allocation.readList := by
  have prototypeValues : rule.read.map (A.apply assignment) =
      plan.prototype.map (realized A assignment label) := by
    have matching : List.Forall₂ Eq (rule.read.map (A.apply assignment))
        (plan.prototype.map (realized A assignment label)) := by
      simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using plan.compatible
    simpa only [List.forall₂_eq_eq_eq] using matching
  have matching : List.Forall₂ Eq (rule.read.map (A.apply assignment))
      (allocation.readList.map (realized A assignment label)) := by
    rw [List.forall₂_eq_eq_eq, allocation.readList_values]
    exact prototypeValues
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, realized, structural] using matching

noncomputable def realization (allocation : ReadAllocation plan world) (taken made : List O) :
    ReadRealization A assignment label plan (⟨taken, allocation.readList, made⟩ : Selection O) where
  embedding := allocation.embedding
  injective := allocation.embedding_injective
  ports := rfl
  values := allocation.embedding_values

end ReadAllocation

/-- Reuse the established no-read lift to allocate raw fresh outputs
against the whole original world. The temporary producer is only an
allocation witness; it does not render the reads as consumption. -/
theorem fresh_outputs [DecidableEq T] (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (values : List T) (world : Finset O) :
    ∃ made : List O, made.Nodup ∧ Disjoint made.toFinset world ∧ made.map label = values := by
  let producer : RuleInstance T := ⟨[], [], [], [], values⟩
  let before : Configuration T O := ⟨[], world⟩
  obtain ⟨selection, valid, _, _⟩ := PositiveResourceProjection.lift_no_read_frame A A.identity label structural
    supply producer rfl rfl before (A.models_nil A.identity) (A.models_nil A.identity)
    (labels (realized A A.identity label) world) (by simp [producer, before])
  exact ⟨selection.made, valid.output_distinct, valid.occurrences.fresh, valid.outputs⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning
