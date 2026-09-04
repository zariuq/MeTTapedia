import Mettapedia.Languages.ProcessCalculi.MORK.ScheduledMinimum

/-!
# Least scheduling after four exact erasures

This module packages a recurring work-queue argument independently of any
particular language.  If four obsolete candidates are erased from a duplicate-
free finite inventory, the earlier of the two remaining candidates is selected
regardless of list order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

/-- Once four distinguished members are excluded from a six-member inventory,
the candidate is one of the two survivors. -/
theorem eq_survivor_or_minimum_of_mem_six
    {α : Type} {candidate first second third fourth survivor minimum : α}
    (member : candidate ∈ [first, third, second, fourth, survivor, minimum])
    (notFirst : candidate ≠ first) (notSecond : candidate ≠ second)
    (notThird : candidate ≠ third) (notFourth : candidate ≠ fourth) :
    candidate = survivor ∨ candidate = minimum := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    firstEqual | thirdEqual | secondEqual | fourthEqual | survivorEqual |
      minimumEqual
  · exact (notFirst firstEqual).elim
  · exact (notThird thirdEqual).elim
  · exact (notSecond secondEqual).elim
  · exact (notFourth fourthEqual).elim
  · exact Or.inl survivorEqual
  · exact Or.inr minimumEqual

/-- Membership after four erasures excludes each removed candidate when the
original inventory has no duplicates. -/
theorem ne_removed_of_mem_four_erases
    {α : Type} [DecidableEq α]
    {facts : List α} {candidate first second third fourth : α}
    (nodup : facts.Nodup)
    (member : candidate ∈
      ((((facts.erase first).erase second).erase third).erase fourth)) :
    candidate ≠ first ∧ candidate ≠ second ∧ candidate ≠ third ∧
      candidate ≠ fourth := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equal
    subst candidate
    have afterFirst : first ∈ facts.erase first :=
      List.mem_of_mem_erase (List.mem_of_mem_erase
        (List.mem_of_mem_erase member))
    exact nodup.not_mem_erase afterFirst
  · intro equal
    subst candidate
    have afterSecond : second ∈ (facts.erase first).erase second :=
      List.mem_of_mem_erase (List.mem_of_mem_erase member)
    exact (nodup.erase first).not_mem_erase afterSecond
  · intro equal
    subst candidate
    have afterThird : third ∈
        ((facts.erase first).erase second).erase third :=
      List.mem_of_mem_erase member
    exact ((nodup.erase first).erase second).not_mem_erase afterThird
  · intro equal
    subst candidate
    exact (((nodup.erase first).erase second).erase third).not_mem_erase member

/-- A duplicate-free six-candidate inventory reduces to the two surviving
candidates after the four distinguished erasures. -/
theorem candidatesWithin_pair_after_four_erasures
    {α : Type} [DecidableEq α]
    {facts final : List α} {first second third fourth survivor minimum : α}
    (nodup : facts.Nodup)
    (within : ∀ candidate ∈ facts,
      candidate ∈ [first, third, second, fourth, survivor, minimum])
    (finalExact : final =
      ((((facts.erase first).erase second).erase third).erase fourth)) :
    ∀ candidate ∈ final, candidate ∈ [survivor, minimum] := by
  intro candidate member
  rw [finalExact] at member
  have originalMember : candidate ∈ facts :=
    List.mem_of_mem_erase (List.mem_of_mem_erase
      (List.mem_of_mem_erase (List.mem_of_mem_erase member)))
  obtain ⟨notFirst, notSecond, notThird, notFourth⟩ :=
    ne_removed_of_mem_four_erases nodup member
  rcases eq_survivor_or_minimum_of_mem_six (within candidate originalMember)
      notFirst notSecond notThird notFourth with survivorEqual | minimumEqual
  · simp [survivorEqual]
  · simp [minimumEqual]

/-- A present strict minimum is selected from any list contained in a
two-candidate inventory. -/
theorem selectNextScheduled_of_within_pair
    {α : Type} [SchedulerKey α] [DecidableEq α]
    (facts : List α) (survivor minimum : α)
    (within : ∀ candidate ∈ facts, candidate ∈ [survivor, minimum])
    (present : minimum ∈ facts)
    (ordered : lexLt (SchedulerKey.key minimum)
      (SchedulerKey.key survivor) = true) :
    selectNextScheduled facts = some minimum := by
  apply selectNextScheduled_eq_some_of_mem_of_strict_minimum _ _ present
  intro candidate member different
  have allowed := within candidate member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
  rcases allowed with survivorEqual | minimumEqual
  · subst candidate
    exact ordered
  · exact (different minimumEqual).elim

/-- Four exact erasures leave the designated minimum as the scheduler result
when the original inventory contains only the four removed candidates, one
other survivor, and the minimum itself. -/
theorem selectNextScheduled_after_four_erases
    {α : Type} [SchedulerKey α] [DecidableEq α]
    (facts : List α) (first second third fourth survivor minimum : α)
    (nodup : facts.Nodup)
    (within : ∀ candidate ∈ facts,
      candidate ∈ [first, third, second, fourth, survivor, minimum])
    (present : minimum ∈
      ((((facts.erase first).erase second).erase third).erase fourth))
    (ordered : lexLt (SchedulerKey.key minimum)
      (SchedulerKey.key survivor) = true) :
    selectNextScheduled
        ((((facts.erase first).erase second).erase third).erase fourth) =
      some minimum := by
  apply selectNextScheduled_eq_some_of_mem_of_strict_minimum _ _ present
  intro candidate member different
  have originalMember : candidate ∈ facts :=
    List.mem_of_mem_erase (List.mem_of_mem_erase
      (List.mem_of_mem_erase (List.mem_of_mem_erase member)))
  have allowed := within candidate originalMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
  rcases allowed with
    firstEqual | thirdEqual | secondEqual | fourthEqual | survivorEqual |
      minimumEqual
  · subst candidate
    have afterFirst : first ∈ facts.erase first :=
      List.mem_of_mem_erase (List.mem_of_mem_erase
        (List.mem_of_mem_erase member))
    exact (nodup.not_mem_erase afterFirst).elim
  · subst candidate
    have afterThird : third ∈
        ((facts.erase first).erase second).erase third :=
      List.mem_of_mem_erase member
    exact (((nodup.erase first).erase second).not_mem_erase afterThird).elim
  · subst candidate
    have afterSecond : second ∈ (facts.erase first).erase second :=
      List.mem_of_mem_erase (List.mem_of_mem_erase member)
    exact ((nodup.erase first).not_mem_erase afterSecond).elim
  · subst candidate
    exact ((((nodup.erase first).erase second).erase third).not_mem_erase
      member).elim
  · subst candidate
    exact ordered
  · exact (different minimumEqual).elim

#print axioms selectNextScheduled_after_four_erases
#print axioms eq_survivor_or_minimum_of_mem_six
#print axioms ne_removed_of_mem_four_erases
#print axioms candidatesWithin_pair_after_four_erasures
#print axioms selectNextScheduled_of_within_pair

end Mettapedia.Languages.ProcessCalculi.MORK
