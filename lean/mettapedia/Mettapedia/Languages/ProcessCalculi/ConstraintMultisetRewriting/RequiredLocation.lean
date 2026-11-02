import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormation

/-!
# An ordinary located CMR firing needs each required physical location

The statement uses the existing two-way step and rigid location action. If a
location has no live occurrence, a take or read declared there has no valid
selection. Data copied elsewhere cannot satisfy that physical requirement.
There is no abstract fault semantics or new permit mechanism in this result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequiredLocation

universe uT uS uN uO
variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq O]

private theorem related_member {A B : Type*} {relation : A → B → Prop}
    {left : List A} {right : List B} (matched : List.Forall₂ relation left right)
    {value : A} (member : value ∈ left) :
    ∃ other ∈ right, relation value other := by
  induction matched with
  | nil => cases member
  | @cons first second left right pair rest ih =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨second, by simp, pair⟩
      · obtain ⟨other, present, related⟩ := ih tail
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

theorem selected_take_location_present (action : SubstitutionAction T S)
    (location : O → N) (payload : O → T) {picked : Selection O}
    {rule : RuleInstance (N × T)} {before : Configuration (N × T) O}
    (valid : picked.Valid (LocatedSubstitution.action action)
      (fun occurrence => (location occurrence, payload occurrence)) rule before)
    {pattern : N × T} (required : pattern ∈ rule.take) :
    ∃ occurrence ∈ before.present, location occurrence = pattern.1 := by
  obtain ⟨occurrence, taken, same⟩ :=
    related_member (LocatedSubstitution.take_locations action location payload valid) required
  exact ⟨occurrence, valid.occurrences.taken_subset (by simpa [Selection.commit] using taken), same.symm⟩

theorem selected_read_location_present (action : SubstitutionAction T S)
    (location : O → N) (payload : O → T) {picked : Selection O}
    {rule : RuleInstance (N × T)} {before : Configuration (N × T) O}
    (valid : picked.Valid (LocatedSubstitution.action action)
      (fun occurrence => (location occurrence, payload occurrence)) rule before)
    {pattern : N × T} (required : pattern ∈ rule.read) :
    ∃ occurrence ∈ before.present, location occurrence = pattern.1 := by
  obtain ⟨occurrence, read, same⟩ :=
    related_member (LocatedSubstitution.read_locations action location payload valid) required
  exact ⟨occurrence, valid.occurrences.kept_subset (by simpa [Selection.commit] using read), same.symm⟩

/-- Even unifiable payload copies in other regions cannot enable this take. -/
theorem no_step_of_missing_take_location (action : SubstitutionAction T S)
    (location : O → N) (payload : O → T) (rule : RuleInstance (N × T))
    (before after : Configuration (N × T) O) {pattern : N × T}
    (required : pattern ∈ rule.take)
    (missing : ∀ occurrence ∈ before.present, location occurrence ≠ pattern.1) :
    ¬ Step (LocatedSubstitution.action action)
      (fun occurrence => (location occurrence, payload occurrence)) rule before after := by
  rintro ⟨picked, valid, _⟩
  obtain ⟨occurrence, present, same⟩ := selected_take_location_present action location payload valid required
  exact missing occurrence present same

/-- This is an ordinary read requirement, not a new fault-state classifier. -/
theorem no_step_of_missing_read_location (action : SubstitutionAction T S)
    (location : O → N) (payload : O → T) (rule : RuleInstance (N × T))
    (before after : Configuration (N × T) O) {pattern : N × T}
    (required : pattern ∈ rule.read)
    (missing : ∀ occurrence ∈ before.present, location occurrence ≠ pattern.1) :
    ¬ Step (LocatedSubstitution.action action)
      (fun occurrence => (location occurrence, payload occurrence)) rule before after := by
  rintro ⟨picked, valid, _⟩
  obtain ⟨occurrence, present, same⟩ := selected_read_location_present action location payload valid required
  exact missing occurrence present same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequiredLocation
