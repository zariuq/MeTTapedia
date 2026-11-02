import Mettapedia.Languages.CHR.Operational
import Mathlib.Data.List.Nodup

/-! Erasing occurrence identities from an authorized refined firing yields a
CHR multiset firing. Propagation history prevents replay of the same ordered
head occurrences, without identifying newly introduced equal constraints. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

theorem visitOrder_permutation (rule : Rule) : rule.visitOrder.Perm (List.range rule.heads.length) := by
  unfold Rule.visitOrder Rule.heads
  rw [List.length_append, List.range_add]
  have order : (List.range rule.removed.length).map (· + rule.kept.length) =
      (List.range rule.removed.length).map (rule.kept.length + ·) := by
    congr 1
    funext index
    exact Nat.add_comm _ _
  rw [order]
  exact List.perm_append_comm

theorem visitOrder_nodup (rule : Rule) : rule.visitOrder.Nodup :=
  (visitOrder_permutation rule).nodup_iff.mpr List.nodup_range

/-- Theoretical firing over constraint multisets, represented by lists up to
permutation. It has no occurrence IDs, active cursor or history. The ordered
body is returned to the controller, not executed atomically. -/
inductive TheoreticalFire (program : Program) :
    List Constraint → List Constraint → Environment → List Goal → Prop
  | apply (index : Nat) (rule : Rule) (environment : Environment)
      (kept removed rest before after : List Constraint)
      (atRule : program.rules[index]? = some rule)
      (keptInstance : rule.kept.mapM (Head.instantiate environment) = some kept)
      (removedInstance : rule.removed.mapM (Head.instantiate environment) = some removed)
      (guards : guardsEval environment rule.guards = .ok true)
      (beforePermutation : before.Perm (kept ++ removed ++ rest))
      (afterPermutation : after.Perm (kept ++ rest)) :
      TheoreticalFire program before after environment rule.body

theorem head_instances {environment : Environment} {heads : List Head} {selected : List Occurrence}
    (matched : List.Forall₂ (fun head occurrence => head.instantiate environment = some occurrence.constraint)
      heads selected) :
    heads.mapM (Head.instantiate environment) = some (selected.map Occurrence.constraint) := by
  induction matched with
  | nil => rfl
  | cons here _ rest => simp [List.mapM_cons, here, rest]

theorem commit_refines (program : Program) (state : State) (rule : Rule) (index : Nat)
    (environment : Environment) (selection : Selection) (active cursor : Nat) (tail : List Task)
    (atRule : program.rules[index]? = some rule)
    (matched : selection.Matches rule environment state.store)
    (guards : guardsEval environment rule.guards = .ok true) :
    TheoreticalFire program (state.store.map Occurrence.constraint)
      ((commit state rule index environment selection active cursor tail).store.map Occurrence.constraint)
      environment rule.body := by
  apply TheoreticalFire.apply index rule environment
    (selection.kept.map Occurrence.constraint) (selection.removed.map Occurrence.constraint)
    (selection.rest.map Occurrence.constraint)
    (atRule := atRule) (keptInstance := head_instances matched.2.2.1)
    (removedInstance := head_instances matched.2.2.2.1) (guards := guards)
  · simpa only [List.map_append] using matched.1.map Occurrence.constraint
  · simp only [commit, List.map_append]
    exact List.Perm.refl _

theorem commit_keeps_occurrence (state : State) (rule : Rule) (index : Nat)
    (environment : Environment) (selection : Selection) (active cursor : Nat) (tail : List Task)
    {occurrence : Occurrence} (kept : occurrence ∈ selection.kept) :
    occurrence ∈ (commit state rule index environment selection active cursor tail).store := by
  exact List.mem_append_left _ kept

theorem propagation_recorded (state : State) (rule : Rule) (index : Nat)
    (environment : Environment) (selection : Selection) (active cursor : Nat) (tail : List Task)
    (propagation : rule.removed = []) :
    selection.key index ∈ (commit state rule index environment selection active cursor tail).history := by
  simp [commit, propagation]

theorem propagation_cannot_replay (state : State) (rule : Rule) (index : Nat)
    (environment : Environment) (selection : Selection) (active cursor : Nat) (tail : List Task)
    (propagation : rule.removed = []) :
    ¬ selection.Fresh rule index (commit state rule index environment selection active cursor tail).history := by
  intro fresh
  exact fresh propagation (propagation_recorded state rule index environment selection active cursor tail propagation)

theorem fresh_occurrence_changes_key (index : Nat) (old new : Selection) (id : Nat)
    (absent : id ∉ old.heads.map Occurrence.id) (present : id ∈ new.heads.map Occurrence.id) :
    old.key index ≠ new.key index := by
  intro same
  have heads := congrArg Key.heads same
  change old.heads.map Occurrence.id = new.heads.map Occurrence.id at heads
  rw [← heads] at present
  exact absent present

theorem next_id_unused (state : State) (wellFormed : state.WellFormed) :
    ∀ occurrence ∈ state.store, occurrence.id ≠ state.nextId := by
  intro occurrence member
  exact Nat.ne_of_lt (wellFormed.2 occurrence member)

theorem commit_wellFormed (state : State) (rule : Rule) (index : Nat)
    (environment : Environment) (selection : Selection) (active cursor : Nat) (tail : List Task)
    (matched : selection.Matches rule environment state.store) (wellFormed : state.WellFormed) :
    (commit state rule index environment selection active cursor tail).WellFormed := by
  have sub : List.Sublist (selection.kept ++ selection.rest)
      (selection.kept ++ selection.removed ++ selection.rest) :=
    (List.sublist_append_left selection.kept selection.removed).append_right selection.rest
  constructor
  · exact List.Nodup.sublist (sub.map Occurrence.id) ((matched.1.map Occurrence.id).nodup_iff.mp wellFormed.1)
  · intro occurrence member
    exact wellFormed.2 occurrence (matched.1.mem_iff.mpr (sub.mem member))

theorem introduce_wellFormed (state : State) (constraint : Constraint) (wellFormed : state.WellFormed) :
    ({state with store := state.store ++ [⟨state.nextId, constraint⟩], nextId := state.nextId + 1} : State).WellFormed := by
  constructor
  · simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.Nodup.append wellFormed.1 (List.nodup_singleton _)
    intro id present new
    have same : id = state.nextId := List.mem_singleton.mp new
    obtain ⟨occurrence, member, rfl⟩ := List.mem_map.mp present
    exact (next_id_unused state wellFormed occurrence member) same
  · intro occurrence member
    rcases List.mem_append.mp member with old | new
    · exact Nat.lt_trans (wellFormed.2 occurrence old) (Nat.lt_succ_self _)
    · have same := List.mem_singleton.mp new
      subst occurrence
      exact Nat.lt_succ_self _

theorem initial_wellFormed (constraints : List Constraint) : (initial constraints).WellFormed := by
  simp [State.WellFormed, initial]

theorem Step.wellFormed {program : Program} {first second : State}
    (step : Step program first second) (formed : first.WellFormed) : second.WellFormed := by
  cases step <;> try exact formed
  · exact introduce_wellFormed _ _ formed
  · apply commit_wellFormed <;> assumption

theorem selection_no_reuse (rule : Rule) (environment : Environment) (store : List Occurrence)
    (selection : Selection) (matched : selection.Matches rule environment store)
    (first second : Fin selection.heads.length)
    (sameId : selection.heads[first].id = selection.heads[second].id) : first = second := by
  have unique := List.nodup_iff_injective_get.mp matched.2.1
  apply Fin.ext
  have positions := unique
    (a₁ := ⟨first.val, by rw [List.length_map]; exact first.isLt⟩)
    (a₂ := ⟨second.val, by rw [List.length_map]; exact second.isLt⟩)
    (by simpa using sameId)
  simpa only [Fin.mk.injEq] using positions

#print axioms commit_refines
#print axioms propagation_cannot_replay
#print axioms selection_no_reuse
#print axioms Step.wellFormed

end Mettapedia.Languages.CHR
