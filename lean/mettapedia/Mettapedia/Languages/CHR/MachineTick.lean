import Mettapedia.Languages.CHR.MachineSearchSteps

/-! The machine refines the refined operational semantics. Every tick is a
finite, possibly empty, run of `Step` that keeps the simulation relation;
the start state simulates the initial state; so every bounded machine run is
an operational run, and the machine shows the operational outcome, with the
final store up to permutation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem tick_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
      Simulates program (tick (table program) state) abstract' := by
  cases running : state.status with
  | failed =>
    have same : tick (table program) state = state := by
      unfold tick
      rw [running]
    rw [same]
    exact ⟨abstract, .refl, simulates⟩
  | faulted reason =>
    have same : tick (table program) state = state := by
      unfold tick
      rw [running]
    rw [same]
    exact ⟨abstract, .refl, simulates⟩
  | running =>
    cases tasks : state.tasks with
    | nil =>
      have same : tick (table program) state = state := by
        unfold tick
        rw [running, tasks]
      rw [same]
      exact ⟨abstract, .refl, simulates⟩
    | cons task tail =>
      have related := simulates.tasks running
      rw [tasks] at related
      obtain ⟨abstractTask, tailAbstract, first, tailRel, abstractTasks⟩ :=
        List.forall₂_cons_left_iff.mp related
      cases first with
      | seeds heads ground =>
        cases heads with
        | nil =>
          have ticked : tick (table program) state = { state with tasks := tail } := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact endGoals_simulates program state abstract simulates running _ tail tasks [] tailAbstract
            abstractTasks tailRel
        | cons head heads =>
          have ticked : tick (table program) state =
              introduce (table program) head [] (.seeds heads) state.tasks tail state
                (state.next :: state.seeds) := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact seed_simulates program state abstract simulates running head heads tail tailAbstract tasks
            abstractTasks ground tailRel
      | goals environment other goals agree =>
        cases goals with
        | nil =>
          have ticked : tick (table program) state = { state with tasks := tail } := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          exact endGoals_simulates program state abstract simulates running _ tail tasks other tailAbstract
            abstractTasks tailRel
        | cons current goals =>
          have ticked : tick (table program) state = goal (table program) environment current goals tail state := by
            unfold tick
            rw [running, tasks]
          rw [ticked]
          cases current with
          | tell head =>
            exact tell_simulates program state abstract simulates running environment other agree head goals tail
              tailAbstract tasks abstractTasks tailRel
          | assign index expression =>
            exact assign_simulates program state abstract simulates running environment other agree index
              expression goals tail tailAbstract tasks abstractTasks tailRel
          | fail =>
            exact fail_simulates program state abstract simulates running environment other goals tail tailAbstract
              abstractTasks
      | scan active key values cursor below stored =>
        have ticked : tick (table program) state =
            scan active key values (keyAtsFrom program key cursor) tail state := by
          unfold tick
          rw [running, tasks]
        rw [ticked]
        exact scan_simulates program state abstract simulates running active key values cursor tail tailAbstract
          tasks abstractTasks below stored tailRel
      | search active key values cursor occurrence frames found atCursor matched below stored alive consumed
          enumerated rejected =>
        have ticked : tick (table program) state =
            search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state := by
          unfold tick
          rw [running, tasks]
        rw [ticked]
        exact search_simulates program state abstract simulates running active key values cursor occurrence frames
          found tail tailAbstract tasks abstractTasks atCursor matched below stored alive consumed enumerated
          rejected tailRel

theorem iterate_simulates (program : Program) :
    ∀ (ticks : Nat) (state : State) (abstract : CHR.State), Simulates program state abstract →
      ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
        Simulates program (iterate (table program) ticks state) abstract'
  | 0, _, abstract, simulates => ⟨abstract, .refl, simulates⟩
  | ticks + 1, state, abstract, simulates => by
    obtain ⟨middle, first, related⟩ := tick_simulates program state abstract simulates
    obtain ⟨final, rest, finalRelated⟩ := iterate_simulates program ticks _ middle related
    exact ⟨final, first.trans rest, finalRelated⟩

theorem advance_simulates (program : Program) :
    ∀ (budget : Nat) (state : State) (abstract : CHR.State), Simulates program state abstract →
      ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
        Simulates program (advance (table program) budget state) abstract'
  | 0, _, abstract, simulates => ⟨abstract, .refl, simulates⟩
  | budget + 1, state, abstract, simulates => by
    unfold advance
    split
    · obtain ⟨middle, first, related⟩ := tick_simulates program state abstract simulates
      obtain ⟨final, rest, finalRelated⟩ := advance_simulates program budget _ middle related
      exact ⟨final, first.trans rest, finalRelated⟩
    · exact ⟨abstract, .refl, simulates⟩

/-! ## Start and outcome -/

theorem instantiateTerms_values (environment : Environment) :
    ∀ (values : List Value), instantiateTerms environment (values.map Term.value) = some values
  | [] => rfl
  | value :: rest => by
    simp [instantiateTerms, instantiateTerm, instantiateTerms_values environment rest]

theorem start_simulates (program : Program) (constraints : List Constraint) :
    Simulates program (start (constraints.map Constraint.asHead)) (initial constraints) := by
  refine ⟨.refl _, ⟨List.nodup_nil, (fun _ impossible => by cases impossible), List.nodup_nil⟩,
    (fun _ impossible => by cases impossible), rfl, rfl, .running, fun _ => ?_, ?_⟩
  · have tells : (constraints.map Constraint.asHead).map Goal.tell =
        constraints.map (Goal.tell ∘ Constraint.asHead) := List.map_map
    show List.Forall₂ _ [Task.seeds (constraints.map Constraint.asHead)]
      [CHR.Task.goals [] (constraints.map (Goal.tell ∘ Constraint.asHead))]
    rw [← tells]
    refine .cons (.seeds _ fun head member => ?_) .nil
    obtain ⟨constraint, _, rfl⟩ := List.mem_map.mp member
    simp [Constraint.asHead, instantiateTerms_values]
  · intro task inside
    simp [start] at inside

/-- What a machine state shows, in the operational outcome vocabulary: the
final store lists the contents of the machine store. -/
def outcome (state : State) : Outcome :=
  match state.status with
  | .failed => .failed
  | .faulted reason => .fault reason
  | .running => if state.tasks.isEmpty then .completed ((contents state.store).map Occurrence.constraint)
    else .pending

/-- Outcomes agree, completed stores up to permutation. -/
inductive OutcomeRel : Outcome → Outcome → Prop where
  | pending : OutcomeRel .pending .pending
  | completed (machine abstract : List Constraint) (permuted : abstract.Perm machine) :
      OutcomeRel (.completed machine) (.completed abstract)
  | failed : OutcomeRel .failed .failed
  | fault (reason : ArithmeticFault) : OutcomeRel (.fault reason) (.fault reason)

theorem outcome_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) : OutcomeRel (outcome state) (observe abstract) := by
  rcases state with ⟨tasks, store, history, next, status, seeds⟩
  rcases abstract with ⟨abstractTasks, abstractStore, abstractHistory, nextId, abstractStatus⟩
  have related : StatusRel status abstractStatus := simulates.status
  cases related with
  | failed => exact .failed
  | faulted reason => exact .fault reason
  | running =>
    have lengths := forall₂_length (simulates.tasks rfl)
    simp only at lengths
    cases tasks with
    | nil =>
      cases abstractTasks with
      | nil => exact .completed _ _ (simulates.store.map Occurrence.constraint)
      | cons => simp at lengths
    | cons task tail =>
      cases abstractTasks with
      | nil => simp at lengths
      | cons => exact .pending

/-- A bounded machine run from the seeds of `constraints` is an operational
run from the initial state of `constraints`, and the machine's outcome is
the outcome of the state it reaches. -/
theorem advance_refines (program : Program) (constraints : List Constraint) (budget : Nat) :
    ∃ abstract, Relation.ReflTransGen (Step program) (initial constraints) abstract ∧
      Simulates program (advance (table program) budget (start (constraints.map Constraint.asHead))) abstract ∧
      OutcomeRel (outcome (advance (table program) budget (start (constraints.map Constraint.asHead))))
        (observe abstract) := by
  obtain ⟨abstract, run, related⟩ := advance_simulates program budget _ _ (start_simulates program constraints)
  exact ⟨abstract, run, related, outcome_simulates program _ abstract related⟩

#print axioms tick_simulates
#print axioms advance_simulates
#print axioms start_simulates
#print axioms outcome_simulates
#print axioms advance_refines

end Mettapedia.Languages.CHR.Machine
