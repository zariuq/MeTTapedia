import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcess

/-!
# The resource-word criterion meets the existing process-order theorem

For a permutation of an admitted check-free source schedule, all port shapes,
local freshness conditions and joint equation models are already retained.
The independent resource word is therefore the remaining execution criterion.
Under the existing occurrence-net freshness and unique-maker hypotheses, its
per-identity words characterize exactly the producer/use and read/take orders.

This comparison retains physical identities and compares equation stores by
their models. It does not quotient proof histories, counts or scheduler weights.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcess

open ConditionalSchedule

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

theorem permuted_operator_defined_iff (action : SubstitutionAction T S) (label : O → T)
    {schedule order : List (Firing T O)} (perm : schedule.Perm order)
    (before : Configuration T O) (free : CheckFree schedule)
    (executes : Executable action label before schedule) :
    (∃ after, ResourceOccupation.runs (word order) before.present = some after) ↔
      Executable action label before order := by
  obtain ⟨shapes, fresh, _sourceOperator, consistent⟩ :=
    (executable_iff_operator action label schedule before free).mp executes
  have orderFree : CheckFree order := fun firing member => free firing (perm.symm.subset member)
  constructor
  · rintro ⟨after, resource⟩
    apply (executable_iff_operator action label order before orderFree).mpr
    refine ⟨fun firing member => shapes firing (perm.symm.subset member),
      fun firing member => fresh firing (perm.symm.subset member), ?_,
      (action.equivalent_consistent (equations_perm_equivalent action label perm before)).mp consistent⟩
    rw [← operator_result label order before after resource]
    exact resource
  · intro admitted
    exact ⟨_, ((executable_iff_operator action label order before orderFree).mp admitted).2.2.1⟩

/-- The graph order and every occurrence's resource word agree on the actual
source execution, including the exact terminal physical boundary. -/
theorem linearization_iff_modes (action : SubstitutionAction T S) (label : O → T)
    {schedule order : List (Firing T O)} (perm : schedule.Perm order)
    (before : Configuration T O) (free : CheckFree schedule)
    (fresh : GuardFreeProcessOrders.FreshFrom before schedule)
    (unique : GuardFreeProcessOrders.UniqueMakers schedule)
    (executes : Executable action label before schedule) :
    order.Pairwise GuardFreeProcessOrders.LaterIndependent ↔
      ∀ occurrence, ResourceOccupation.modeRun (word order) occurrence
        (decide (occurrence ∈ before.present)) =
          some (decide (occurrence ∈ (follow label before schedule).present)) := by
  have original := GuardFreeProcessOrders.runs_are_exactly_linearizations action label
    schedule order before perm free fresh unique executes
  constructor
  · intro ordered
    have admitted := original.1.mpr ordered
    have resource := ((executable_iff_operator action label order before
      (fun firing member => free firing (perm.symm.subset member))).mp admitted).2.2.1
    rw [← (original.2 admitted).2] at resource
    exact (ResourceOccupation.runs_eq_some_iff_modes _ _ _).mp resource
  · intro modes
    have resource := (ResourceOccupation.runs_eq_some_iff_modes _ _ _).mpr modes
    exact original.1.mp ((permuted_operator_defined_iff action label perm before free executes).mp
      ⟨_, resource⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcess
