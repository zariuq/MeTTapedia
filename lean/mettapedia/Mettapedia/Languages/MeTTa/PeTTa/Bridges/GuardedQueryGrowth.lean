import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource

/-!
# Fresh satisfaction support and completed packet growth

The measured support consists of distinct complete Atoms headed by `sat`,
at one fixed handle. It is not yet the typed node set of one formula. A missing
read is assigned zero only by this measurement, never by guard admission.
The second source payload is headed by `fr`, so it cannot change this support,
including when both writes use the same handle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedPresenceConditional (Input)
open NamedGuardedInsertionSource (Body Evidence)
open NamedGuardedCandidateExecution (Advance executeAdmitted execute)

def isSat : Atom → Bool
  | .expression (.symbol "sat" :: _) => true
  | _ => false

def support (atoms : List Atom) : Finset Atom := (atoms.filter isSat).toFinset

def measure (target : NamedSpaces.Handle) (state : Effects.State) : Nat :=
  (support ((state.read target).getD [])).card

theorem read_sat (environment : Environment) (formula node : Atom) :
    isSat (read environment (.expression [.symbol "sat", formula, node])) = true := by
  simp [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation, isSat]

theorem read_fr (environment : Environment) (fields : List Atom) :
    isSat (read environment (.expression (.symbol "fr" :: fields))) = false := by
  simp [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation, isSat]

theorem pair_growth (before middle after : Effects.State) (target secondTarget : NamedSpaces.Handle)
    (key second : Atom) (rows : List Atom)
    (snapshot : before.read target = some rows) (fresh : key ∉ rows)
    (keySat : isSat key = true) (secondNotSat : isSat second = false)
    (firstWrite : Effects.insert before target key = some middle)
    (secondWrite : Effects.insert middle secondTarget second = some after) :
    measure target after = measure target before + 1 := by
  have finalRead := ScopedInsertionSequence.pair_store_receipt before middle after target secondTarget key second
    firstWrite secondWrite target
  have notHeld : key ∉ support rows := by
    simpa only [support, List.mem_toFinset, List.mem_filter, keySat, and_true] using fresh
  have onlyKey : support (rows ++ [key] ++ if target = secondTarget then [second] else []) =
      insert key (support rows) := by
    by_cases same : target = secondTarget
    · simp [support, same, keySat, secondNotSat, List.filter_append]
    · simp [support, same, keySat, List.filter_append]
  unfold measure
  rw [finalRead, snapshot]
  simp only [ite_true, Option.map_some, Option.getD_some]
  rw [onlyKey, Finset.card_insert_of_notMem notHeld]

variable {Context : Type}

/-- A completed admitted candidate either copied a held witness without
writing, or published one genuinely fresh `sat` key and one non-`sat` row. -/
theorem admitted_growth (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (evidence : Evidence input guard body)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (fields : List Atom) (frontierCode : body.secondCode = .expression (.symbol "fr" :: fields))
    (after : Advance) (completed : (executeAdmitted input guard body evidence finished output).result = .advanced after) :
    measure input.request.handle after.state = measure input.request.handle input.world.state + after.answers.length := by
  have keySat : isSat input.request.pattern = true := by
    rw [← guard.reading]
    exact read_sat _ _ _
  have secondNotSat : isSat evidence.secondValue = false := by
    rw [← evidence.secondRead, frontierCode]
    exact read_fr _ _
  unfold executeAdmitted at completed
  split at completed
  · cases completed
  next rows snapshot =>
    split at completed
    next ready =>
      split at completed
      next present =>
        split at completed
        · cases completed
        next allocated copied =>
          cases NamedGuardedCandidateExecution.Result.advanced.inj completed
          simp
      next absent =>
        split at completed
        · cases completed
        next middle firstWrite =>
          split at completed
          · cases completed
          next final secondWrite =>
            cases NamedGuardedCandidateExecution.Result.advanced.inj completed
            exact pair_growth input.world.state middle final input.request.handle body.secondHandle
              input.request.pattern evidence.secondValue rows snapshot absent keySat secondNotSat firstWrite secondWrite
    · cases completed

theorem execute_growth (input : Input Context) (body : Body)
    (fields : List Atom) (frontierCode : body.secondCode = .expression (.symbol "fr" :: fields))
    (after : Advance) (completed : (execute input body).result = .advanced after) :
    measure input.request.handle after.state = measure input.request.handle input.world.state + after.answers.length := by
  unfold execute at completed
  split at completed
  next finished =>
    split at completed
    next output =>
      split at completed
      · cases completed
      next guard guardReady =>
        split at completed
        · cases completed
        next evidence bodyReady =>
          exact admitted_growth input guard body evidence finished output fields frontierCode after completed
    · cases completed
  · cases completed

/-- The concrete guarded leaf conserves raw satisfaction support against
local packet growth. A source `fr` payload remains non-`sat` under reading. -/
theorem leaf_balanced (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (fields : List Atom) (frontierCode : template.body.secondCode = .expression (.symbol "fr" :: fields)) :
    ScopedNestedQueryExecution.Balanced (measure template.satisfactionHandle)
      (GuardedNestedQuerySource.leaf program template Context).execute := by
  intro caller state context origins pending after completed
  change (GuardedNestedQuerySource.invoke program template caller state context origins pending).execution.stop =
    .complete after at completed
  unfold GuardedNestedQuerySource.invoke at completed
  dsimp only at completed
  split at completed
  · cases completed
  next principal resolved =>
    split at completed
    · cases completed
    next request requested =>
      have requestFields := CapturedQueryOperands.request_fields _ _ _ request requested
      dsimp only at completed
      split at completed
      · cases completed
      · cases completed
      next next advanced =>
        have growth := execute_growth
          ((template.candidate caller context origins request).input program state pending)
          template.body fields frontierCode next advanced
        have same : state.advance next = after := ScopedNestedQueryExecution.Stop.complete.inj completed
        subst after
        change measure request.handle next.state = measure request.handle state.world.state + next.answers.length at growth
        rw [requestFields.1] at growth
        change measure template.satisfactionHandle next.state + state.scope.collected.length =
          measure template.satisfactionHandle state.world.state + (state.scope.collected ++ next.answers).length
        rw [List.length_append]
        omega

theorem nested_packet_count (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (fields : List Atom) (frontierCode : template.body.secondCode = .expression (.symbol "fr" :: fields))
    (legs : List NestedQuerySource.Leg) (caller : Control) (state : NamedGuardedCandidateBatch.State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (after : NamedGuardedCandidateBatch.State Context) (initiallyEmpty : state.scope.collected = [])
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program template Context)
      legs caller state context origins pending).stop = .complete after) :
    measure template.satisfactionHandle after.world.state =
      measure template.satisfactionHandle state.world.state + after.scope.collected.length :=
  ScopedNestedQueryExecution.completed_packet_count program (GuardedNestedQuerySource.leaf program template Context)
    (measure template.satisfactionHandle) (leaf_balanced program template fields frontierCode)
    legs caller state context origins pending after initiallyEmpty completed

/-- The conservation law applies to the actual source prefix certified by
the worker. Finishing the enclosing collector is still a subsequent step. -/
theorem source_packet_count (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (fields : List Atom) (frontierCode : template.body.secondCode = .expression (.symbol "fr" :: fields))
    (legs : List NestedQuerySource.Leg) (caller : Control) (state : NamedGuardedCandidateBatch.State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (after : NamedGuardedCandidateBatch.State Context) (initiallyEmpty : state.scope.collected = [])
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program template Context)
      legs caller state context origins pending).stop = .complete after) :
    let execution := ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program template Context)
      legs caller state context origins pending
    (ScopedQuerySource.machine .relational program).run execution.budget
      (ScopedMatchEntry.entrance (ScopedNestedQueryExecution.source legs template.source) (.var template.body.result)
        caller state context origins pending) = (execution.events, .exhausted (after.cursor pending)) ∧
      measure template.satisfactionHandle after.world.state =
        measure template.satisfactionHandle state.world.state + after.scope.collected.length := by
  dsimp only
  constructor
  · have actual := GuardedNestedQuerySource.run_exact program template legs caller state context origins pending
    simpa only [ScopedNestedQueryExecution.Execution.observation, completed, ScopedNestedQueryExecution.Stop.outcome] using actual
  · exact nested_packet_count program template fields frontierCode legs caller state context origins pending after initiallyEmpty completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth
