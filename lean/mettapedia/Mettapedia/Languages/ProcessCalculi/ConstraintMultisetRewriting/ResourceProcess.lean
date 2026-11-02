import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionLayout
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders

/-!
# Resource operators compute the worlds of the existing firing schedules

The resource word erases a source schedule's terms but keeps every selected
physical occurrence and read-port repetition. For check-free source schedules,
execution is equivalent to the operator succeeding, local output freshness,
port-shape agreement and consistency of the complete final equation problem.

The executable relation and final configuration are the existing owners.
The operator is independently computed from the selection lists. In particular
the converse below reconstructs every source step from the operator's result;
it does not assume the requested source execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcess

open ConditionalSchedule

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def ports (selection : Selection O) : List O × List O × List O :=
  (selection.taken, selection.read, selection.made)

def word (schedule : List (Firing T O)) : List (List O × List O × List O) :=
  schedule.map fun firing => ports firing.2

def PortShape (label : O → T) (firing : Firing T O) : Prop :=
  firing.1.take.length = firing.2.taken.length ∧
    firing.1.read.length = firing.2.read.length ∧ firing.2.made.map label = firing.1.produce

def Shapes (label : O → T) (schedule : List (Firing T O)) : Prop :=
  ∀ firing ∈ schedule, PortShape label firing

def LocallyFresh (schedule : List (Firing T O)) : Prop :=
  ∀ firing ∈ schedule, Disjoint firing.2.made.toFinset firing.2.taken.toFinset

def CheckFree (schedule : List (Firing T O)) : Prop :=
  ∀ firing ∈ schedule, firing.1.checks = []

/-- A successful resource word computes the source's complete physical result,
even before shape or information admission has been established. -/
theorem operator_result (label : O → T) :
    ∀ (schedule : List (Firing T O)) (before : Configuration T O) (after : Finset O),
      ResourceOccupation.runs (word schedule) before.present = some after →
        after = (follow label before schedule).present
  | [], before, after, success => by
      simpa [word, ResourceOccupation.runs, ResourceOccupation.one, follow] using success.symm
  | firing :: rest, before, after, success => by
      change (ResourceOccupation.commit firing.2.taken firing.2.read firing.2.made before.present).bind
        (ResourceOccupation.runs (word rest)) = some after at success
      obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨_, _, _, _, _, middleEq⟩ :=
        (ResourceOccupation.commit_eq_some_iff _ _ _ _ _).mp first
      have same : middle = (firing.2.result label firing.1 before).present := middleEq
      apply operator_result label rest (firing.2.result label firing.1 before) after
      simpa only [same] using later

/-- The only resource side condition not computed by the operator is source
freshness between a firing's taken and made identities. Guard-free admission
then depends on the actual complete equation problem, not independent per-step
solutions. -/
theorem executable_iff_operator (action : SubstitutionAction T S) (label : O → T) :
    ∀ (schedule : List (Firing T O)) (before : Configuration T O), CheckFree schedule →
      (Executable action label before schedule ↔
        Shapes label schedule ∧ LocallyFresh schedule ∧
        ResourceOccupation.runs (word schedule) before.present =
          some (follow label before schedule).present ∧
        action.Consistent (follow label before schedule).equations)
  | [], before, _free => by
      simp [Executable, Shapes, LocallyFresh, word, ResourceOccupation.runs,
        ResourceOccupation.one, follow]
  | firing :: rest, before, free => by
      have restFree : CheckFree rest := fun later member => free later (List.mem_cons_of_mem _ member)
      constructor
      · rintro ⟨valid, continues⟩
        obtain ⟨shapes, fresh, resource, consistent⟩ :=
          (executable_iff_operator action label rest _ restFree).mp continues
        have sourceResource := (ResourceOccupation.enabled_iff_nonzero_and_fresh label firing.2
          before.present).mp ⟨valid.take_distinct, valid.output_distinct, valid.occurrences⟩
        refine ⟨?_, ?_, ?_, consistent⟩
        · intro selected member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨valid.take_length, valid.read_length, valid.outputs⟩
          · exact shapes selected member
        · intro selected member
          rcases List.mem_cons.mp member with rfl | member
          · exact sourceResource.2
          · exact fresh selected member
        · change (ResourceOccupation.commit firing.2.taken firing.2.read firing.2.made before.present).bind
            (ResourceOccupation.runs (word rest)) = _
          rw [ResourceOccupation.valid_result_world action firing.2 label firing.1 before valid,
            Option.bind_some]
          exact resource
      · rintro ⟨shapes, fresh, resource, consistent⟩
        change (ResourceOccupation.commit firing.2.taken firing.2.read firing.2.made before.present).bind
          (ResourceOccupation.runs (word rest)) = _ at resource
        obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp resource
        obtain ⟨_, _, _, _, _, middleEq⟩ :=
          (ResourceOccupation.commit_eq_some_iff _ _ _ _ _).mp first
        have same : middle = (firing.2.result label firing.1 before).present := middleEq
        have sourceResource := (ResourceOccupation.enabled_iff_nonzero_and_fresh label firing.2
          before.present).mpr ⟨⟨middle, first⟩, fresh firing List.mem_cons_self⟩
        have shape := shapes firing List.mem_cons_self
        have currentConsistent : action.Consistent (firing.2.result label firing.1 before).equations := by
          obtain ⟨assignment, solved⟩ := consistent
          exact ⟨assignment, ((LinearConnectionLayout.models_follow_iff action assignment label rest
            (firing.2.result label firing.1 before)).mp solved).1⟩
        have valid : firing.2.Valid action label firing.1 before := {
          take_distinct := sourceResource.1
          output_distinct := sourceResource.2.1
          take_length := shape.1
          read_length := shape.2.1
          outputs := shape.2.2
          occurrences := sourceResource.2.2
          consistent := currentConsistent
          checks := by
            intro check member
            rw [free firing List.mem_cons_self] at member
            cases member }
        refine ⟨valid, (executable_iff_operator action label rest _ restFree).mpr
          ⟨fun selected member => shapes selected (List.mem_cons_of_mem _ member),
            fun selected member => fresh selected (List.mem_cons_of_mem _ member), ?_, consistent⟩⟩
        simpa only [same, follow] using later

/-- The same characterization can be checked occurrence by occurrence. The
joint information condition stays global. -/
theorem executable_iff_modes (action : SubstitutionAction T S) (label : O → T)
    (schedule : List (Firing T O)) (before : Configuration T O) (free : CheckFree schedule) :
    Executable action label before schedule ↔
      Shapes label schedule ∧ LocallyFresh schedule ∧
      (∀ occurrence, ResourceOccupation.modeRun (word schedule) occurrence
        (decide (occurrence ∈ before.present)) =
          some (decide (occurrence ∈ (follow label before schedule).present))) ∧
      action.Consistent (follow label before schedule).equations := by
  rw [executable_iff_operator action label schedule before free,
    ResourceOccupation.runs_eq_some_iff_modes]

/-- Permuting events preserves the final equation models even when that
permutation does not execute physically. -/
theorem equations_perm_equivalent (action : SubstitutionAction T S) (label : O → T)
    {schedule order : List (Firing T O)} (perm : schedule.Perm order) (before : Configuration T O) :
    action.Equivalent (follow label before schedule).equations (follow label before order).equations := by
  intro assignment
  rw [LinearConnectionLayout.models_follow_iff, LinearConnectionLayout.models_follow_iff]
  constructor
  · rintro ⟨incoming, connections⟩
    exact ⟨incoming, fun firing member => connections firing (perm.symm.subset member)⟩
  · rintro ⟨incoming, connections⟩
    exact ⟨incoming, fun firing member => connections firing (perm.subset member)⟩

/-- An equality of independent resource operators lifts to the original
check-free source schedules. This proof uses operator admission in both
directions, rather than a second source swap implementation. -/
theorem executable_permutation_of_operator (action : SubstitutionAction T S) (label : O → T)
    {schedule order : List (Firing T O)} (perm : schedule.Perm order)
    (before : Configuration T O) (free : CheckFree schedule)
    (sameOperator : ResourceOccupation.runs (word schedule) = ResourceOccupation.runs (word order))
    (executes : Executable action label before schedule) :
    Executable action label before order ∧
      GuardFreeProcessOrders.SameUpTo action (follow label before schedule) (follow label before order) := by
  obtain ⟨shapes, fresh, resource, consistent⟩ :=
    (executable_iff_operator action label schedule before free).mp executes
  have orderResource : ResourceOccupation.runs (word order) before.present =
      some (follow label before schedule).present := by rw [← sameOperator]; exact resource
  have sameWorld := operator_result label order before _ orderResource
  have sameEquations := equations_perm_equivalent action label perm before
  refine ⟨(executable_iff_operator action label order before
    (fun firing member => free firing (perm.symm.subset member))).mpr ⟨
      fun firing member => shapes firing (perm.symm.subset member),
      fun firing member => fresh firing (perm.symm.subset member), ?_,
      (action.equivalent_consistent sameEquations).mp consistent⟩, sameEquations, sameWorld⟩
  rw [← sameWorld]
  exact orderResource

/-- At each identity, at least one selection is absent, or both selections
only read it. This is a sufficient commutation condition. -/
def SharedReadsOnly (first second : Selection O) : Prop :=
  ∀ occurrence,
    (first.taken.count occurrence = 0 ∧ first.read.count occurrence = 0 ∧ first.made.count occurrence = 0) ∨
    (second.taken.count occurrence = 0 ∧ second.read.count occurrence = 0 ∧ second.made.count occurrence = 0) ∨
    (first.taken.count occurrence = 0 ∧ first.made.count occurrence = 0 ∧
      second.taken.count occurrence = 0 ∧ second.made.count occurrence = 0)

theorem shared_reads_swap (action : SubstitutionAction T S) (label : O → T)
    (first second : Firing T O) (before : Configuration T O)
    (free : CheckFree [first, second]) (apart : SharedReadsOnly first.2 second.2)
    (executes : Executable action label before [first, second]) :
    Executable action label before [second, first] ∧
      GuardFreeProcessOrders.SameUpTo action (follow label before [first, second])
        (follow label before [second, first]) := by
  apply executable_permutation_of_operator action label (List.Perm.swap _ _ []) before free ?_ executes
  exact ResourceOccupation.commits_comm_of_shared_reads_only (ports first.2) (ports second.2) apart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcess
