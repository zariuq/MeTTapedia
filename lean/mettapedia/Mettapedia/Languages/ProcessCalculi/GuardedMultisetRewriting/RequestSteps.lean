import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step

/-!
# Requests select ordinary guarded rewriting inference steps

A request supplies schematic arguments. The step consumes that request,
retains its selected premises and publishes its instantiated conclusion.
Repeated premise selections may share a single occurrence. These lemmas
construct the existing `Step` witnesses; they add no execution relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uV uT uP
variable {V : Type uV} {T : Type uT} {P : Type uP}

def requestRule (request : P) (premises : List P) (conclusion : P)
    (guard : Subst V T → Bool) : Rule V T P :=
  ⟨[request], premises, [⟨request, fun assignment _ => guard assignment = true⟩], [conclusion]⟩

/-- The selected list records read positions; its deduplicated bag records
the actual occurrences required to retain them. -/
theorem Reads.of_selection [DecidableEq T] {L : TermLayer V T P} {assignment : Subst V T}
    {patterns : List P} {selected : List T}
    (matched : List.Forall₂ (L.Solves assignment) patterns selected) :
    Reads L assignment patterns (selected : Multiset T).dedup :=
  ⟨selected, matched, Multiset.dedup_le _, fun _ member => Multiset.mem_dedup.mpr member⟩

theorem requestRule_step [DecidableEq T] {L : TermLayer V T P}
    {request conclusion : P} {premises : List P} {guard : Subst V T → Bool}
    {assignment : Subst V T} {requestValue result : T} {selected : List T} {state : Multiset T}
    (binds : BindsOnlyGathers L (requestRule request premises conclusion guard) assignment)
    (requestMatches : L.Solves assignment request requestValue)
    (premisesMatch : List.Forall₂ (L.Solves assignment) premises selected)
    (available : ∀ value ∈ selected, value ∈ state)
    (checked : guard assignment = true)
    (output : L.inst assignment conclusion = some result) :
    Step L (requestRule request premises conclusion guard) ({requestValue} + state) (state + {result}) := by
  let kept := (selected : Multiset T).dedup
  have contained : kept ≤ state := (Multiset.le_iff_subset (Multiset.nodup_dedup _)).mpr (by
    intro value member
    exact available value (Multiset.mem_dedup.mp member))
  have partition : state - kept + kept = state := tsub_add_cancel_of_le contained
  refine ⟨assignment, state - kept, {requestValue}, kept, [result], binds,
    ⟨[requestValue], .cons requestMatches .nil, rfl⟩,
    Reads.of_selection premisesMatch, ?_, ?_, ?_, ?_⟩
  · rw [add_right_comm, partition, add_comm]
  · intro check member
    have same : check = ⟨request, fun assignment _ => guard assignment = true⟩ := by
      simpa [requestRule] using member
    subst check
    exact checked
  · simp [instTemplate, requestRule, output]
  · rw [partition]
    rfl

/-- A local invariant proof for a request rule lifts to its actual store step.
The local proof must justify its output from the values selected by the reads. -/
theorem requestRule_preserves {L : TermLayer V T P}
    {request conclusion : P} {premises : List P} {guard : Subst V T → Bool}
    (validValue : T → Prop)
    (localSound : ∀ assignment selected result,
      guard assignment = true → List.Forall₂ (L.Solves assignment) premises selected →
      (∀ value ∈ selected, validValue value) →
      L.inst assignment conclusion = some result → validValue result)
    {before after : Multiset T}
    (validBefore : ∀ value ∈ before, validValue value)
    (step : Step L (requestRule request premises conclusion guard) before after) :
    ∀ value ∈ after, validValue value := by
  obtain ⟨assignment, frame, taken, kept, made, _, _, ⟨selected, matched, _, present⟩,
    source, checks, outputs, destination⟩ := step
  have checked : guard assignment = true := checks
    ⟨request, fun assignment _ => guard assignment = true⟩ (by simp [requestRule])
  have validSelected : ∀ value ∈ selected, validValue value := by
    intro value member
    apply validBefore value
    rw [source]
    exact Multiset.mem_add.mpr (Or.inr (present value member))
  have madeOne : ∃ result, L.inst assignment conclusion = some result ∧ made = [result] := by
    change [conclusion].mapM (L.inst assignment) = some made at outputs
    cases result : L.inst assignment conclusion with
    | none => simp [result] at outputs
    | some value =>
        have same : [value] = made := by simpa [result] using outputs
        exact ⟨value, rfl, same.symm⟩
  obtain ⟨result, produced, rfl⟩ := madeOne
  intro value member
  rw [destination] at member
  rcases Multiset.mem_add.mp member with retained | fresh
  · apply validBefore value
    rw [source]
    rcases Multiset.mem_add.mp retained with framed | keptMember
    · exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl framed)))
    · exact Multiset.mem_add.mpr (Or.inr keptMember)
  · have same : value = result := by simpa using fresh
    subst value
    exact localSound assignment selected result checked matched validSelected produced

/-- A data-only request guard is unaffected by an unrelated store frame.
This property is specific to these rules, not to arbitrary absence checks. -/
theorem requestRule_frame {L : TermLayer V T P}
    {request conclusion : P} {premises : List P} {guard : Subst V T → Bool}
    {before after : Multiset T}
    (step : Step L (requestRule request premises conclusion guard) before after) (extra : Multiset T) :
    Step L (requestRule request premises conclusion guard) (before + extra) (after + extra) := by
  obtain ⟨assignment, frame, taken, kept, made, binds, takes, reads, source, checks, outputs, destination⟩ := step
  refine ⟨assignment, frame + extra, taken, kept, made, binds, takes, reads, ?_, ?_, outputs, ?_⟩
  · rw [source]
    ac_rfl
  · intro check member
    have same : check = ⟨request, fun assignment _ => guard assignment = true⟩ := by
      simpa [requestRule] using member
    subst check
    exact checks _ member
  · rw [destination]
    ac_rfl

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
