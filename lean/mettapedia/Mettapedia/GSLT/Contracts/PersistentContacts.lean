import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# Persistent registrations with linear requests

A contact records a selected message and a selected registration. A
persistent contact keeps the registration's identity. It does not take
it and republish an equal registration. Matching a request or computing
the continuation is a separate concern of the rule that supplies the
contact; this file states the lifetime and interference laws afterward.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PersistentContacts

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O R : Type*} [DecidableEq O]

def contact (registration request : O) (result : Finset O) : Commit O R :=
  ⟨{request}, {registration}, result, []⟩

omit [DecidableEq O] in
theorem enabled_contact_iff {label : O → R} {store : Finset O} {registration request : O}
    {result : Finset O} :
    Enabled label store (contact registration request result) ↔
      request ∈ store ∧ registration ∈ store ∧ request ≠ registration ∧ Disjoint result store := by
  constructor
  · intro enabled
    exact ⟨enabled.taken_subset (by simp [contact]), enabled.kept_subset (by simp [contact]),
      by simpa [contact] using enabled.apart, enabled.fresh⟩
  · rintro ⟨requested, registered, different, fresh⟩
    exact ⟨by simp [contact, requested], by simp [contact, registered],
      by simpa [contact] using different, fresh, by simp [contact]⟩

theorem retains_registration {label : O → R} {store : Finset O} {registration request : O}
    {result : Finset O} (ready : Enabled label store (contact registration request result)) :
    registration ∈ fire store (contact (R := R) registration request result) := by
  obtain ⟨_, kept, apart, _⟩ := enabled_contact_iff.mp ready
  exact mem_fire.mpr (.inl ⟨kept, by simpa [contact] using apart.symm⟩)

/-- Contacts may share the registration even on one channel. With
distinct roles the only clashes are a shared request or a shared new
identity. No disjoint-channel hypothesis is needed. -/
theorem same_registration_independent_iff (label : O → R) {registration a b : O}
    {outA outB : Finset O} (differentA : a ≠ registration) (differentB : b ≠ registration) :
    Independent label (contact registration a outA) (contact registration b outB) ↔
      a ≠ b ∧ Disjoint outA outB := by
  simp [Independent, Clash, Spoils, WritesInto, contact, differentA, differentB, not_or]

def contacts (registration : O) (requests : List (O × Finset O)) : List (Commit O R) :=
  requests.map fun request => contact registration request.1 request.2

theorem takesOf_contacts (registration : O) (requests : List (O × Finset O)) :
    takenOf (contacts (R := R) registration requests) = (requests.map Prod.fst).toFinset := by
  ext o
  simp [contacts, mem_takenOf, contact]

/-- An outstanding batch can be served in any order using the very same
registration. This is one contact per request and no extra unfold or
registration-copying transition. -/
theorem contacts_serialize {label : O → R} {store : Finset O} {registration : O}
    {requests : List (O × Finset O)} {execution : List (Commit O R)}
    (registered : registration ∈ store)
    (ready : ∀ r ∈ requests, r.1 ∈ store ∧ r.1 ≠ registration ∧ Disjoint r.2 store)
    (apart : requests.Pairwise fun a b => a.1 ≠ b.1 ∧ Disjoint a.2 b.2)
    (order : (contacts (R := R) registration requests).Perm execution) :
    Executable label store execution ∧
      registration ∈ fireList store execution ∧
      execution.length = requests.length ∧
      takenOf execution = (requests.map Prod.fst).toFinset := by
  let wave : List (Commit O R) := contacts registration requests
  have each : ∀ c ∈ wave, Enabled label store c := by
    intro c member
    obtain ⟨r, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨inStore, notRegistration, fresh⟩ := ready r selected
    exact enabled_contact_iff.mpr ⟨inStore, registered, notRegistration, fresh⟩
  have localPairs : wave.Pairwise (Independent label) := by
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp_of_mem (fun ha hb pair =>
      (same_registration_independent_iff label (ready _ ha).2.1 (ready _ hb).2.1).mpr pair) apart
  have enabledNow : Executable label store execution :=
    executable_of_pairwise_independent (fun c member => each c (order.symm.subset member))
      ((order.pairwise_iff fun h => h.symm).mp localPairs)
  have taken : takenOf execution = (requests.map Prod.fst).toFinset :=
    (takenOf_perm order).symm.trans (takesOf_contacts registration requests)
  refine ⟨enabledNow, ?_, order.length_eq.symm.trans (List.length_map ..), taken⟩
  rw [fireList_eq_fire_effectOf (MatchedAt.of_enabled
    (fun c member => each c (order.symm.subset member)))]
  apply mem_fire.mpr
  refine .inl ⟨registered, ?_⟩
  change registration ∉ takenOf execution
  rw [taken]
  simp only [List.mem_toFinset, List.mem_map]
  rintro ⟨r, member, equal⟩
  exact (ready r member).2.1 equal

namespace Controls

private def listenerLabel (_ : Nat) : Unit := ()
private def serves (request : Nat) : Commit Nat Unit := contact 0 request ∅

theorem shared_server_is_not_a_serialization_point :
    Executable listenerLabel {0, 1, 2} [serves 2, serves 1] ∧
      fireList {0, 1, 2} [serves 2, serves 1] = {0} := by
  let requests : List (Nat × Finset Nat) := [(1, ∅), (2, ∅)]
  have order : (contacts (R := Unit) 0 requests).Perm [serves 2, serves 1] := List.Perm.swap ..
  have result := contacts_serialize (label := listenerLabel) (store := {0, 1, 2})
    (by decide) (requests := requests)
    (by simp [requests]) (by simp [requests]) order
  exact ⟨result.1, by decide⟩

/-- The same observer sees a difference if the rule models a persistent
registration by taking and reinstalling one at a different identity. -/
theorem reinstall_does_not_validate_a_second_contact :
    let before : Finset Nat := {0, 1, 2}
    let reinstall : Commit Nat Unit := ⟨{0, 1}, ∅, {3}, []⟩
    Enabled listenerLabel before reinstall ∧
      Enabled listenerLabel before (serves 2) ∧
      ¬ Enabled listenerLabel (fire before reinstall) (serves 2) := by
  decide

end Controls

#print axioms enabled_contact_iff
#print axioms same_registration_independent_iff
#print axioms contacts_serialize
#print axioms Controls.shared_server_is_not_a_serialization_point
#print axioms Controls.reinstall_does_not_validate_a_second_contact

end Mettapedia.GSLT.Contracts.PersistentContacts
