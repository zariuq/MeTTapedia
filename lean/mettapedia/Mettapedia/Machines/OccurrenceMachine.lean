import Mettapedia.Machines.MachineRefinement
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.FinsetOps

/-!
# Occurrence-preserving finite-branching machines

`MachineCore` is deterministic. A MeTTa evaluator must additionally preserve
the multiplicity of nondeterministic answers: two rule occurrences may produce
equal values without becoming one answer occurrence.

This module derives a finite-search observation from an ordered transition
function. The order is operational data, while coercion to `Multiset` forgets
only order and retains multiplicity. Transition indices form executable trace
certificates, so duplicate edges to the same state remain distinguishable.

The existing deterministic answer machines embed by turning `Option State`
into a zero-or-one successor list. The embedding is proved equivalent to the
existing reachability-based `Produces` relation; no correspondence with the
native CeTTa evaluator is claimed here.
-/

namespace Mettapedia.Machines

/-- A finite-branching answer machine. Successor-list position is transition
occurrence identity; equal successor states at different positions are not
silently collapsed. -/
structure OccurrenceMachineCore (Term State Answer : Type) where
  load : Term → State
  next : State → List State
  answer : State → Option Answer
  answer_final : ∀ s a, answer s = some a → next s = []

namespace OccurrenceMachineCore

variable {Term State Answer : Type}

/-- Follow a transition-occurrence trace. Each natural number selects one
position in the current state's successor list. -/
def follow (M : OccurrenceMachineCore Term State Answer) :
    State → List Nat → Option State
  | state, [] => some state
  | state, edge :: rest =>
      (M.next state)[edge]? >>= fun target => M.follow target rest

private theorem getElem?_eq_some_of_mem_zipIdx {values : List State}
    {value : State} {index : Nat} (h : (value, index) ∈ values.zipIdx) :
    values[index]? = some value := by
  have key := List.exists_mem_zipIdx'.mp
    (show ∃ entry ∈ values.zipIdx, entry = (value, index) from
      ⟨_, h, rfl⟩)
  obtain ⟨foundIndex, foundBound, pairEquality⟩ := key
  have indexEquality : foundIndex = index :=
    (Prod.ext_iff.mp pairEquality).2
  subst indexEquality
  rw [List.getElem?_eq_getElem foundBound]
  exact congrArg some (Prod.ext_iff.mp pairEquality).1

private theorem mem_zipIdx_of_getElem?_eq_some {values : List State}
    {value : State} {index : Nat} (h : values[index]? = some value) :
    (value, index) ∈ values.zipIdx := by
  obtain ⟨indexBound, valueEquality⟩ :=
    List.getElem?_eq_some_iff.mp h
  have zippedBound : index < values.zipIdx.length := by
    simpa using indexBound
  have zippedEquality : values.zipIdx[index] = (value, index) := by
    simpa [List.getElem_zipIdx] using congrArg (fun x => (x, index)) valueEquality
  rw [← zippedEquality]
  exact List.getElem_mem zippedBound

/-- Fuel-bounded answer occurrences. `List.flatMap` preserves both duplicate
successors and duplicate answers; fuel limits transitions, not observations of
an already-final state. -/
def answerOccurrences (M : OccurrenceMachineCore Term State Answer) :
    Nat → State → List Answer
  | 0, state => M.answer state |>.toList
  | fuel + 1, state =>
      match M.answer state with
      | some answer => [answer]
      | none => (M.next state).flatMap (M.answerOccurrences fuel)

/-- Answer occurrences paired with their transition-index traces. -/
def answerTraces (M : OccurrenceMachineCore Term State Answer) :
    Nat → State → List (Answer × List Nat)
  | 0, state => M.answer state |>.toList.map fun answer => (answer, [])
  | fuel + 1, state =>
      match M.answer state with
      | some answer => [(answer, [])]
      | none =>
          (M.next state).zipIdx.flatMap fun (target, edge) =>
            (M.answerTraces fuel target).map fun (answer, trace) =>
              (answer, edge :: trace)

/-- The still-live frontier at a transition-depth cut. A non-answer state is
pending exactly when it has successors that the bound did not inspect; a
stuck state is not mislabeled as pending. -/
def pendingTraces (M : OccurrenceMachineCore Term State Answer) :
    Nat → State → List (State × List Nat)
  | 0, state =>
      match M.answer state with
      | some _ => []
      | none =>
          if (M.next state).isEmpty then [] else [(state, [])]
  | fuel + 1, state =>
      match M.answer state with
      | some _ => []
      | none =>
          (M.next state).zipIdx.flatMap fun (target, edge) =>
            (M.pendingTraces fuel target).map fun (pending, trace) =>
              (pending, edge :: trace)

/-- The complete observable slice of a depth-bounded exhaustive expansion.
This is not a global work budget or a scheduling policy: every successor at
each inspected depth is expanded. -/
structure ExpansionSlice (State Answer : Type) where
  answers : List (Answer × List Nat)
  pending : List (State × List Nat)

/-- Pair completed answer occurrences with the explicit unexpanded frontier. -/
def expand (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (state : State) : ExpansionSlice State Answer where
  answers := M.answerTraces fuel state
  pending := M.pendingTraces fuel state

/-- Every emitted trace is an executable path to a state exposing the paired
answer. This validates the trace as a certificate, rather than treating it as
an unverified annotation on the answer list. -/
theorem answerTraces_sound (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state : State} {answer : Answer} {trace : List Nat}
    (h : (answer, trace) ∈ M.answerTraces fuel state) :
    ∃ final,
      M.follow state trace = some final ∧ M.answer final = some answer := by
  induction fuel generalizing state answer trace with
  | zero =>
      cases hanswer : M.answer state with
      | none => simp [answerTraces, hanswer] at h
      | some value =>
          have pairEquality : (answer, trace) = (value, []) := by
            simpa [answerTraces, hanswer] using h
          cases pairEquality
          exact ⟨state, rfl, hanswer⟩
  | succ fuel ih =>
      cases hanswer : M.answer state with
      | some value =>
          have pairEquality : (answer, trace) = (value, []) := by
            simpa [answerTraces, hanswer] using h
          cases pairEquality
          exact ⟨state, rfl, hanswer⟩
      | none =>
          simp only [answerTraces, hanswer] at h
          obtain ⟨⟨target, edge⟩, edgeMember, pairMember⟩ :=
            List.mem_flatMap.mp h
          obtain ⟨⟨childAnswer, childTrace⟩, childMember,
              pairEquality⟩ := List.mem_map.mp pairMember
          cases pairEquality
          obtain ⟨final, childFollow, observed⟩ := ih childMember
          have edgeLookup : (M.next state)[edge]? = some target :=
            getElem?_eq_some_of_mem_zipIdx edgeMember
          exact ⟨final, by simp [follow, edgeLookup, childFollow], observed⟩

/-- Every pending certificate follows to the stated non-answer state, which
still has at least one successor. -/
theorem pendingTraces_sound (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state pending : State} {trace : List Nat}
    (h : (pending, trace) ∈ M.pendingTraces fuel state) :
    M.follow state trace = some pending ∧
      M.answer pending = none ∧ M.next pending ≠ [] := by
  induction fuel generalizing state pending trace with
  | zero =>
      cases hanswer : M.answer state with
      | some value => simp [pendingTraces, hanswer] at h
      | none =>
          cases hempty : (M.next state).isEmpty with
          | true => simp [pendingTraces, hanswer, hempty] at h
          | false =>
              have pairEquality : (pending, trace) = (state, []) := by
                simpa [pendingTraces, hanswer, hempty] using h
              cases pairEquality
              exact ⟨rfl, hanswer, by
                intro nextEmpty
                simp [nextEmpty] at hempty⟩
  | succ fuel ih =>
      cases hanswer : M.answer state with
      | some value => simp [pendingTraces, hanswer] at h
      | none =>
          simp only [pendingTraces, hanswer] at h
          obtain ⟨⟨target, edge⟩, edgeMember, pairMember⟩ :=
            List.mem_flatMap.mp h
          obtain ⟨⟨childPending, childTrace⟩, childMember,
              pairEquality⟩ := List.mem_map.mp pairMember
          cases pairEquality
          obtain ⟨childFollow, childAnswer, childLive⟩ := ih childMember
          have edgeLookup : (M.next state)[edge]? = some target :=
            getElem?_eq_some_of_mem_zipIdx edgeMember
          exact ⟨by simp [follow, edgeLookup, childFollow],
            childAnswer, childLive⟩

/-- A transition-occurrence trace cannot simultaneously certify a completed
answer and an unexpanded live state. This is the local non-conflation law for
the two halves of `ExpansionSlice`. -/
theorem answer_pending_trace_disjoint
    (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state pending : State} {answer : Answer}
    {trace : List Nat}
    (completed : (answer, trace) ∈ M.answerTraces fuel state)
    (live : (pending, trace) ∈ M.pendingTraces fuel state) : False := by
  obtain ⟨final, completedFollow, observed⟩ :=
    M.answerTraces_sound completed
  obtain ⟨liveFollow, unobserved, _⟩ := M.pendingTraces_sound live
  have final_eq_pending : final = pending :=
    Option.some.inj (completedFollow.symm.trans liveFollow)
  rw [← final_eq_pending, observed] at unobserved
  cases unobserved

/-- Pending traces lie exactly at the requested transition depth. -/
theorem pendingTraces_length_eq (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state pending : State} {trace : List Nat}
    (h : (pending, trace) ∈ M.pendingTraces fuel state) :
    trace.length = fuel := by
  induction fuel generalizing state pending trace with
  | zero =>
      cases hanswer : M.answer state with
      | some value => simp [pendingTraces, hanswer] at h
      | none =>
          cases hempty : (M.next state).isEmpty with
          | true => simp [pendingTraces, hanswer, hempty] at h
          | false =>
              have pairEquality : (pending, trace) = (state, []) := by
                simpa [pendingTraces, hanswer, hempty] using h
              cases pairEquality
              rfl
  | succ fuel ih =>
      cases hanswer : M.answer state with
      | some value => simp [pendingTraces, hanswer] at h
      | none =>
          simp only [pendingTraces, hanswer] at h
          obtain ⟨⟨target, edge⟩, _, pairMember⟩ :=
            List.mem_flatMap.mp h
          obtain ⟨⟨childPending, childTrace⟩, childMember,
              pairEquality⟩ := List.mem_map.mp pairMember
          cases pairEquality
          simpa using congrArg Nat.succ (ih childMember)

/-- Conversely, an executable trace of exactly the cut depth ending in a live
non-answer state is present in the pending frontier. -/
theorem pendingTraces_complete (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state pending : State} {trace : List Nat}
    (followed : M.follow state trace = some pending)
    (unobserved : M.answer pending = none)
    (live : M.next pending ≠ [])
    (exact : trace.length = fuel) :
    (pending, trace) ∈ M.pendingTraces fuel state := by
  induction fuel generalizing state pending trace with
  | zero =>
      have traceEmpty : trace = [] := List.length_eq_zero_iff.mp exact
      subst trace
      have statePending : state = pending := by
        simpa [follow] using Option.some.inj followed
      subst state
      have successorsNonempty : (M.next pending).isEmpty = false := by
        cases hnext : M.next pending with
        | nil => exact absurd hnext live
        | cons target rest => rfl
      simp [pendingTraces, unobserved, successorsNonempty]
  | succ fuel ih =>
      cases trace with
      | nil => simp at exact
      | cons edge rest =>
          cases edgeLookup : (M.next state)[edge]? with
          | none => simp [follow, edgeLookup] at followed
          | some target =>
              have childFollow : M.follow target rest = some pending := by
                simpa [follow, edgeLookup] using followed
              have childExact : rest.length = fuel := by
                simpa using Nat.succ.inj exact
              have childMember :
                  (pending, rest) ∈ M.pendingTraces fuel target :=
                ih childFollow unobserved live childExact
              have stateNotAnswer : M.answer state = none := by
                cases stateAnswer : M.answer state with
                | none => rfl
                | some value =>
                    have noSuccessors :=
                      M.answer_final state value stateAnswer
                    have impossible : (M.next state)[edge]? = none := by
                      simp [noSuccessors]
                    rw [impossible] at edgeLookup
                    contradiction
              have edgeMember : (target, edge) ∈ (M.next state).zipIdx :=
                mem_zipIdx_of_getElem?_eq_some edgeLookup
              simp only [pendingTraces, stateNotAnswer, List.mem_flatMap]
              exact ⟨(target, edge), edgeMember,
                List.mem_map.mpr ⟨(pending, rest), childMember, rfl⟩⟩

/-- Exact certificate characterization of the unexpanded live frontier. -/
theorem mem_pendingTraces_iff
    (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state pending : State} {trace : List Nat} :
    (pending, trace) ∈ M.pendingTraces fuel state ↔
      M.follow state trace = some pending ∧
      M.answer pending = none ∧ M.next pending ≠ [] ∧
      trace.length = fuel := by
  constructor
  · intro h
    obtain ⟨followed, unobserved, live⟩ := M.pendingTraces_sound h
    exact ⟨followed, unobserved, live, M.pendingTraces_length_eq h⟩
  · rintro ⟨followed, unobserved, live, exact⟩
    exact M.pendingTraces_complete followed unobserved live exact

/-- Conversely, every bounded executable trace ending in an observed answer is
enumerated. Together with `answerTraces_sound`, this makes the trace list exact
for its transition bound. -/
theorem answerTraces_complete (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state final : State} {answer : Answer} {trace : List Nat}
    (followed : M.follow state trace = some final)
    (observed : M.answer final = some answer)
    (bounded : trace.length ≤ fuel) :
    (answer, trace) ∈ M.answerTraces fuel state := by
  induction fuel generalizing state final answer trace with
  | zero =>
      have traceEmpty : trace = [] := by
        exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero bounded)
      subst trace
      have stateFinal : state = final := by
        simpa [follow] using Option.some.inj followed
      subst final
      simp [answerTraces, observed]
  | succ fuel ih =>
      cases trace with
      | nil =>
          have stateFinal : state = final := by
            simpa [follow] using Option.some.inj followed
          subst final
          simp [answerTraces, observed]
      | cons edge rest =>
          cases edgeLookup : (M.next state)[edge]? with
          | none => simp [follow, edgeLookup] at followed
          | some target =>
              have childFollow : M.follow target rest = some final := by
                simpa [follow, edgeLookup] using followed
              have childBound : rest.length ≤ fuel := by
                simpa using bounded
              have childMember :
                  (answer, rest) ∈ M.answerTraces fuel target :=
                ih childFollow observed childBound
              have stateNotAnswer : M.answer state = none := by
                cases stateAnswer : M.answer state with
                | none => rfl
                | some value =>
                    have noSuccessors :=
                      M.answer_final state value stateAnswer
                    have impossible : (M.next state)[edge]? = none := by
                      simp [noSuccessors]
                    rw [impossible] at edgeLookup
                    contradiction
              have edgeMember : (target, edge) ∈ (M.next state).zipIdx :=
                mem_zipIdx_of_getElem?_eq_some edgeLookup
              simp only [answerTraces, stateNotAnswer, List.mem_flatMap]
              exact ⟨(target, edge), edgeMember,
                List.mem_map.mpr ⟨(answer, rest), childMember, rfl⟩⟩

/-- Every emitted trace uses at most the available transition fuel. -/
theorem answerTraces_length_le (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state : State} {answer : Answer} {trace : List Nat}
    (h : (answer, trace) ∈ M.answerTraces fuel state) :
    trace.length ≤ fuel := by
  induction fuel generalizing state answer trace with
  | zero =>
      cases hanswer : M.answer state with
      | none => simp [answerTraces, hanswer] at h
      | some value =>
          have pairEquality : (answer, trace) = (value, []) := by
            simpa [answerTraces, hanswer] using h
          cases pairEquality
          rfl
  | succ fuel ih =>
      cases hanswer : M.answer state with
      | some value =>
          have pairEquality : (answer, trace) = (value, []) := by
            simpa [answerTraces, hanswer] using h
          cases pairEquality
          simp
      | none =>
          simp only [answerTraces, hanswer] at h
          obtain ⟨⟨target, edge⟩, _, pairMember⟩ :=
            List.mem_flatMap.mp h
          obtain ⟨⟨childAnswer, childTrace⟩, childMember,
              pairEquality⟩ := List.mem_map.mp pairMember
          cases pairEquality
          have childBound := ih childMember
          simpa using Nat.succ_le_succ childBound

/-- Exact fuel-bounded trace characterization. -/
theorem mem_answerTraces_iff (M : OccurrenceMachineCore Term State Answer)
    {fuel : Nat} {state : State} {answer : Answer} {trace : List Nat} :
    (answer, trace) ∈ M.answerTraces fuel state ↔
      ∃ final,
        M.follow state trace = some final ∧
        M.answer final = some answer ∧ trace.length ≤ fuel := by
  constructor
  · intro h
    obtain ⟨final, followed, observed⟩ := M.answerTraces_sound h
    exact ⟨final, followed, observed, M.answerTraces_length_le h⟩
  · rintro ⟨final, followed, observed, bounded⟩
    exact M.answerTraces_complete followed observed bounded

/-- Erasing trace certificates returns exactly the occurrence list. -/
theorem answerTraces_map_fst (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (state : State) :
    (M.answerTraces fuel state).map Prod.fst =
      M.answerOccurrences fuel state := by
  induction fuel generalizing state with
  | zero =>
      cases hanswer : M.answer state <;>
        simp [answerTraces, answerOccurrences, hanswer]
  | succ fuel ih =>
      simp only [answerTraces, answerOccurrences]
      cases hanswer : M.answer state with
      | some answer => rfl
      | none =>
          have children : ∀ (targets : List State) (offset : Nat),
              ((targets.zipIdx offset).flatMap fun (target, edge) =>
                (M.answerTraces fuel target).map fun (answer, trace) =>
                  (answer, edge :: trace)).map Prod.fst =
                targets.flatMap (M.answerOccurrences fuel) := by
            intro targets
            induction targets with
            | nil => simp
            | cons target rest rest_ih =>
                intro offset
                simp only [List.zipIdx_cons, List.flatMap_cons,
                  List.map_append, List.map_map]
                have head_eq :
                    List.map
                      (Prod.fst ∘ fun pair : Answer × List Nat =>
                        (pair.1, offset :: pair.2))
                      (M.answerTraces fuel target) =
                    M.answerOccurrences fuel target := by
                  calc
                    _ = List.map Prod.fst
                        (M.answerTraces fuel target) := by
                      apply List.map_congr_left
                      intro pair _
                      cases pair
                      rfl
                    _ = M.answerOccurrences fuel target := ih target
                rw [head_eq, rest_ih (offset + 1)]
          exact children (M.next state) 0

/-- Forget only enumeration order, retaining answer multiplicity. -/
def answerBag (M : OccurrenceMachineCore Term State Answer)
    (fuel : Nat) (state : State) : Multiset Answer :=
  M.answerOccurrences fuel state

/-- Two machines differ only by transition enumeration when loading and answer
observation agree and every successor list is a permutation. -/
structure Reorders (M N : OccurrenceMachineCore Term State Answer) : Prop where
  load_eq : M.load = N.load
  answer_eq : ∀ state, M.answer state = N.answer state
  next_perm : ∀ state, List.Perm (M.next state) (N.next state)

/-- Reordering transitions may reorder the occurrence list, but cannot add,
remove, or collapse answer occurrences at a fixed exhaustive depth bound.
This does not imply fairness or invariance under a global finite work budget. -/
theorem answerOccurrences_perm_of_reorders
    {M N : OccurrenceMachineCore Term State Answer}
    (h : Reorders M N) (fuel : Nat) (state : State) :
    List.Perm (M.answerOccurrences fuel state)
      (N.answerOccurrences fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simp [answerOccurrences, h.answer_eq state]
  | succ fuel ih =>
      simp only [answerOccurrences]
      rw [h.answer_eq state]
      cases N.answer state with
      | some answer => exact List.Perm.refl [answer]
      | none =>
          exact (h.next_perm state).flatMap fun target _ => ih target

/-- The semantic answer bag is invariant under transition reordering. -/
theorem answerBag_eq_of_reorders
    {M N : OccurrenceMachineCore Term State Answer}
    (h : Reorders M N) (fuel : Nat) (state : State) :
    M.answerBag fuel state = N.answerBag fuel state :=
  Quot.sound (answerOccurrences_perm_of_reorders h fuel state)

/-! ## Deterministic machines embed without inventing branching -/

/-- Lift a deterministic answer machine by exposing its optional successor as
a zero-or-one list. -/
def ofDeterministic (M : AnswerMachineCore Term Answer) :
    OccurrenceMachineCore Term M.State Answer where
  load := M.load
  next := fun state => (M.step state).toList
  answer := M.answer
  answer_final := by
    intro state answer hanswer
    rw [M.answer_final state answer hanswer]
    rfl

/-- A deterministic run to an observed answer appears in the finite
occurrence enumerator at some transition bound. -/
theorem deterministic_steps_to_mem (M : AnswerMachineCore Term Answer)
    {start final : M.State} {answer : Answer}
    (run : M.toMachineCore.Steps start final)
    (observed : M.answer final = some answer) :
    ∃ fuel, answer ∈
      (ofDeterministic M).answerOccurrences fuel start := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨0, by simp [answerOccurrences, ofDeterministic, observed]⟩
  | @head start next step _ ih =>
      obtain ⟨fuel, hmem⟩ := ih
      have hnotAnswer : M.answer start = none := by
        cases hstart : M.answer start with
        | none => rfl
        | some value =>
            have hfinal := M.answer_final start value hstart
            rw [MachineCore.StepRel, hfinal] at step
            exact absurd step.symm (Option.some_ne_none next)
      refine ⟨fuel + 1, ?_⟩
      rw [MachineCore.StepRel] at step
      simpa [answerOccurrences, ofDeterministic, hnotAnswer, step] using hmem

/-- Reachability-based production implies finite occurrence enumeration. -/
theorem deterministic_produces_to_mem (M : AnswerMachineCore Term Answer)
    {term : Term} {answer : Answer} (h : M.Produces term answer) :
    ∃ fuel, answer ∈
      (ofDeterministic M).answerOccurrences fuel (M.load term) := by
  obtain ⟨final, run, observed⟩ := h
  exact deterministic_steps_to_mem M run observed

/-- Every answer emitted by the deterministic embedding has a corresponding
reachable final state. -/
theorem deterministic_mem_to_steps (M : AnswerMachineCore Term Answer)
    {start : M.State} {answer : Answer} {fuel : Nat}
    (h : answer ∈
      (ofDeterministic M).answerOccurrences fuel start) :
    ∃ final, M.toMachineCore.Steps start final ∧
      M.answer final = some answer := by
  induction fuel generalizing start with
  | zero =>
      have observed : M.answer start = some answer := by
        simpa [answerOccurrences, ofDeterministic] using h
      exact ⟨start, Relation.ReflTransGen.refl, observed⟩
  | succ fuel ih =>
      simp only [answerOccurrences] at h
      cases hanswer : M.answer start with
      | some value =>
          have hanswerD : (ofDeterministic M).answer start = some value :=
            hanswer
          rw [hanswerD] at h
          have equal : answer = value := by simpa [hanswer] using h
          subst answer
          exact ⟨start, Relation.ReflTransGen.refl, hanswer⟩
      | none =>
          have hanswerD : (ofDeterministic M).answer start = none := hanswer
          rw [hanswerD] at h
          cases hstep : M.step start with
          | none =>
              have hnextD : (ofDeterministic M).next start = [] := by
                simp [ofDeterministic, hstep]
              simp [hnextD] at h
          | some next =>
              have hnextD : (ofDeterministic M).next start = [next] := by
                simp [ofDeterministic, hstep]
              have hnext : answer ∈
                  (ofDeterministic M).answerOccurrences fuel next := by
                simpa [hnextD] using h
              obtain ⟨final, tail, observed⟩ :=
                ih (start := next) hnext
              refine ⟨final, ?_, observed⟩
              have first : M.toMachineCore.StepRel start next := hstep
              exact Relation.ReflTransGen.head first tail

/-- Every answer emitted by the deterministic embedding corresponds to the
existing reachability-based `Produces` relation. -/
theorem deterministic_mem_to_produces (M : AnswerMachineCore Term Answer)
    {term : Term} {answer : Answer} {fuel : Nat}
    (h : answer ∈
      (ofDeterministic M).answerOccurrences fuel (M.load term)) :
    M.Produces term answer := by
  obtain ⟨final, run, observed⟩ := deterministic_mem_to_steps M h
  exact ⟨final, run, observed⟩

/-- The executable finite enumerator and the existing deterministic
reachability semantics agree exactly after existentially hiding fuel. -/
theorem deterministic_produces_iff_mem
    (M : AnswerMachineCore Term Answer) {term : Term} {answer : Answer} :
    M.Produces term answer ↔
      ∃ fuel, answer ∈
        (ofDeterministic M).answerOccurrences fuel (M.load term) :=
  ⟨deterministic_produces_to_mem M,
    fun ⟨_, h⟩ => deterministic_mem_to_produces M h⟩

/-! ## Existing evaluator correspondences pass through the embedding -/

/-- The occurrence-preserving view of the eager CEK machine. -/
def cekOccurrenceCore : OccurrenceMachineCore Tm CEK.St CEK.Val :=
  ofDeterministic cekAnswerCore

/-- CBV evaluator success appears in the exact occurrence enumerator. -/
theorem cek_eval_to_occurrence {n : Nat} {term : Tm} {value : CEK.Val}
    (h : CEK.evalV n [] term = some value) :
    ∃ fuel, value ∈
      cekOccurrenceCore.answerOccurrences fuel (cekOccurrenceCore.load term) :=
  deterministic_produces_to_mem cekAnswerCore (cek_eval_to_produces h)

/-- The occurrence-preserving view of the demand-driven Krivine machine. -/
def krivineOccurrenceCore :
    OccurrenceMachineCore Tm Krivine.KSt Krivine.NVal :=
  ofDeterministic krivineAnswerCore

/-- CBN evaluator success appears in the exact occurrence enumerator. -/
theorem krivine_eval_to_occurrence {n : Nat} {term : Tm}
    {value : Krivine.NVal} (h : Krivine.evalN n [] term = some value) :
    ∃ fuel, value ∈
      krivineOccurrenceCore.answerOccurrences fuel
        (krivineOccurrenceCore.load term) :=
  deterministic_produces_to_mem krivineAnswerCore
    (krivine_eval_to_produces h)

/-! ## Positive and negative occurrence examples -/

inductive DuplicateExampleState where
  | root
  | done
  deriving DecidableEq

/-- Two distinct transition occurrences deliberately reach the same final
state and equal answer. -/
def duplicateExample :
    OccurrenceMachineCore Unit DuplicateExampleState Nat where
  load := fun _ => .root
  next
    | .root => [.done, .done]
    | .done => []
  answer
    | .root => none
    | .done => some 7
  answer_final := by
    intro state answer h
    cases state <;> simp_all

/-- Duplicate edges remain two answer occurrences. -/
example : duplicateExample.answerOccurrences 1 .root = [7, 7] := rfl

/-- Their trace certificates remain distinct even though endpoint and answer
are equal. -/
example : duplicateExample.answerTraces 1 .root =
    [(7, [0]), (7, [1])] := rfl

/-- Before either outgoing occurrence is inspected, the root is explicit
pending work rather than failure. -/
example : duplicateExample.expand 0 .root =
    { answers := [], pending := [(.root, [])] } := rfl

/-- One transition layer exhausts both duplicate occurrences and leaves no
pending frontier. -/
example : duplicateExample.expand 1 .root =
    { answers := [(7, [0]), (7, [1])], pending := [] } := rfl

/-- A set-valued observation would lose information: the occurrence bag has
cardinality two while its support has cardinality one. -/
example : (duplicateExample.answerBag 1 .root).card = 2 ∧
    (duplicateExample.answerBag 1 .root).dedup.card = 1 := by
  decide

/-- A stuck state is distinct from a cut-off live state: it has neither an
answer nor pending successors. -/
def stuckExample : OccurrenceMachineCore Unit Unit Nat where
  load := id
  next := fun _ => []
  answer := fun _ => none
  answer_final := by simp

example : stuckExample.expand 0 () = { answers := [], pending := [] } := rfl

end OccurrenceMachineCore

end Mettapedia.Machines
