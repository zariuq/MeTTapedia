import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Scoped query answers through a read-only transform effect

Preparation retains each occurrence and its own computed source substitution.
The independent PeTTa queryBodies function specifies the resulting evaluation
requests. An admitted read-only effect preserves the store; it does not erase
those requests or turn their templates into data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open PeTTa.Unifying (unify rename Control queryBodies queryRows queryJoin queryLegs joinedBodies)
open PeTTaStoreSelection (atomFrames)

variable {O : Type} (label : O → Atom)

def scan (bindings : Subst) (pattern : Atom) : Nat → List O → Option (List (O × Subst)) :=
  queryRows label Prod.mk bindings pattern

theorem scan_cons (bindings : Subst) (pattern : Atom) (use : Nat) (row : O) (rest : List O) :
    scan label bindings pattern use (row :: rest) =
      (do
        let later ← scan label bindings pattern (use + 1) rest
        match unify bindings pattern (rename use (label row)) with
        | .ok bound => some ((row,bound) :: later)
        | .clash => some later
        | .exhausted => none) := rfl

def continuations (body : Atom) (packets : List (O × Subst)) : List Control :=
  packets.map fun row => .evaluate row.2 body

/-- Whole source computation, including exhaustion, equals the independently
prepared occurrence packets followed by continuation construction. -/
theorem scan_source (bindings : Subst) (pattern body : Atom) (use : Nat) (rows : List O) :
    queryBodies bindings pattern body use (rows.map label) =
      (scan label bindings pattern use rows).map (continuations body) := by
  exact PeTTa.Unifying.queryRows_natural id Prod.mk (fun _ bound => Control.evaluate bound body)
    label (fun packet : O × Subst => Control.evaluate packet.2 body) (fun _ _ => rfl)
    bindings pattern use rows

/-- Per-leg reads at an already resolved space. The authored nesting opens
each next query when that continuation is entered, not when the first
query was opened. This is distinct from capturing the entire conjunction.
Calling code remains responsible for location admission, including when
there are no legs. -/
def nestedAt (handle : PeTTa.NamedSpaces.Handle) : List Atom → Atom → Atom
  | [], body => body
  | pattern :: legs, body =>
      .expression [.symbol "match", PeTTa.Effects.handleValue handle, pattern, nestedAt handle legs body]

theorem scanned_occurrences_sublist (bindings : Subst) (pattern : Atom) (use : Nat)
    (rows : List O) (packets : List (O × Subst))
    (prepared : scan label bindings pattern use rows = some packets) :
    (packets.map Prod.fst).Sublist rows := by
  induction rows generalizing use packets with
  | nil =>
      simp only [scan, queryRows, Option.some.injEq] at prepared
      subst packets
      exact .slnil
  | cons occurrence rest ih =>
      unfold scan at prepared
      cases later : queryRows label Prod.mk bindings pattern (use + 1) rest with
      | none => simp [queryRows, later] at prepared
      | some remaining =>
          have inherited := ih _ _ later
          cases matched : unify bindings pattern (rename use (label occurrence)) with
          | ok bound =>
              simp [queryRows, later, matched] at prepared
              subst packets
              exact inherited.cons_cons _
          | clash =>
              simp [queryRows, later, matched] at prepared
              subst packets
              exact inherited.cons _
          | exhausted => simp [queryRows, later, matched] at prepared

def request (packets : List (O × Subst)) : OrderedStore.Publication Atom O :=
  ⟨⟨[], packets.map Prod.fst, []⟩, []⟩

/-- Read receipts for the selected paths retain repeated occurrences.
Candidate completeness uses the full captured view, not this list of hits. -/
def joinedRequest (packets : List (List O × Subst)) : OrderedStore.Publication Atom O :=
  ⟨⟨[], packets.flatMap Prod.fst, []⟩, []⟩

theorem joined_occurrences_in_view {bindings : Subst} {pattern : Atom} {use : Nat}
    {rows : List O} {packets : List (List O × Subst)} {used : Nat}
    (prepared : queryJoin label rows (queryLegs pattern) bindings use = some (packets,used)) :
    ∀ occurrence ∈ packets.flatMap Prod.fst, occurrence ∈ rows := by
  intro occurrence found
  obtain ⟨packet, member, chosen⟩ := List.mem_flatMap.mp found
  exact (PeTTa.Unifying.queryJoin_preserves label rows (fun _ => True) (use + used)
    (queryLegs pattern) bindings trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    use prepared le_rfl packet member).2.1 occurrence chosen

namespace JoinCursor

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open PeTTa.Unifying (queryBranches)

abbrev Packet (O : Type) := List O × Subst

/-- A branch opens a full leg's freshening range before probing any row.
The resumed sibling keeps its own slot in that range; children allocate
beyond it. The path is accumulated in reverse order. -/
inductive Work (O : Type) where
  | enter (legs : List Atom) (path : List O) (bindings : Subst)
  | scan (pattern : Atom) (legs : List Atom) (path : List O) (bindings : Subst)
      (slot : Nat) (unvisited : List O)

structure State (O : Type) where
  view : List O
  next : Nat
  work : List (Work O)

def start (rows : List O) (legs : List Atom) (bindings : Subst) (use : Nat) : State O :=
  ⟨rows, use, [.enter legs [] bindings]⟩

/-- One row probe, descent, or delivery. Pending work refers to the retained
view, not to the store at the time the cursor is next pulled. -/
def move (state : State O) : Transition (State O) (Packet O) Nat Empty :=
  match state.work with
  | [] => .finish state.next
  | .enter [] path bindings :: rest =>
      .publish [(path.reverse, bindings)] {state with work := rest}
  | .enter (pattern :: legs) path bindings :: rest => .silent
      {state with next := state.next + state.view.length
                  work := .scan pattern legs path bindings state.next state.view :: rest}
  | .scan _ _ _ _ _ [] :: rest => .silent {state with work := rest}
  | .scan pattern legs path bindings slot (row :: rows) :: rest =>
      let sibling := Work.scan pattern legs path bindings (slot + 1) rows
      match unify bindings pattern (rename slot (label row)) with
      | .ok bound => .silent {state with work := .enter legs (row :: path) bound :: sibling :: rest}
      | .clash => .silent {state with work := sibling :: rest}
      | .exhausted => .fail []

def machine : Machine (State O) (Packet O) Nat Empty := ⟨fun state => some (move label state)⟩

private def attachPath (path : List O) (packet : Packet O) : Packet O :=
  (path.reverse ++ packet.1, packet.2)

private def subtree (rows : List O) (legs : List Atom) (path : List O)
    (bindings : Subst) (use : Nat) : Option (List (Packet O) × Nat) :=
  (queryJoin label rows legs bindings use).map fun (packets, spent) =>
    (packets.map (attachPath path), spent)

private def workValue (rows : List O) (use : Nat) : Work O → Option (List (Packet O) × Nat)
  | .enter legs path bindings => subtree label rows legs path bindings use
  | .scan pattern legs path bindings slot unvisited => do
      let hits ← scan label bindings pattern slot unvisited
      queryBranches (fun next (row, bound) => subtree label rows legs (row :: path) bound next) use hits

/-- Independent complete reading of a residual, using the source's batch
scan and join. This is a proof specification, not how pulling runs. -/
def remaining (state : State O) : Option (List (Packet O) × Nat) :=
  (queryBranches (workValue label state.view) state.next state.work).map fun (packets, spent) =>
    (packets, state.next + spent)

@[simp] theorem remaining_start (rows : List O) (legs : List Atom) (bindings : Subst) (use : Nat) :
    remaining label (start rows legs bindings use) =
      (queryJoin label rows legs bindings use).map (fun (packets, spent) => (packets, use + spent)) := by
  simp only [remaining, start, queryBranches, workValue, subtree]
  have unitPath : attachPath ([] : List O) = id := by
    funext packet
    cases packet
    rfl
  cases queryJoin label rows legs bindings use <;> simp [unitPath]

private theorem enter_value (rows : List O) (pattern : Atom) (legs : List Atom)
    (path : List O) (bindings : Subst) (use : Nat) :
    workValue label rows use (.enter (pattern :: legs) path bindings) =
      (workValue label rows (use + rows.length) (.scan pattern legs path bindings use rows)).map
        (fun (packets, spent) => (packets, rows.length + spent)) := by
  simp only [workValue, subtree, queryJoin, scan]
  cases hits : queryRows label Prod.mk bindings pattern use rows with
  | none => rfl
  | some packets =>
      let child (atUse : Nat) (branch : O × Subst) :=
        (queryJoin label rows legs branch.2 atUse).map
          (fun (tails, spent) => (tails.map (fun tail : Packet O => (branch.1 :: tail.1, tail.2)), spent))
      let extended (atUse : Nat) (branch : O × Subst) :=
        subtree label rows legs (branch.1 :: path) branch.2 atUse
      have joins (atUse : Nat) (branch : O × Subst) :
          extended atUse (id branch) = (child atUse branch).map
            (fun (tails, spent) => (tails.map (attachPath path), spent)) := by
        dsimp only [extended, child, subtree, id_eq]
        cases read : queryJoin label rows legs branch.2 atUse <;>
          simp [attachPath, List.map_map, Function.comp_def, List.append_assoc]
      have related := PeTTa.Unifying.queryBranches_natural id (attachPath path) joins (use + rows.length) packets
      rw [List.map_id] at related
      change ((queryBranches child (use + rows.length) packets).bind _).map _ =
        (queryBranches extended (use + rows.length) packets).map _
      rw [related]
      cases queryBranches child (use + rows.length) packets <;> rfl

private theorem scan_cons_value (rows : List O) (pattern : Atom) (legs : List Atom)
    (path : List O) (bindings : Subst) (use slot : Nat) (row : O) (rest : List O) :
    workValue label rows use (.scan pattern legs path bindings slot (row :: rest)) =
      (match unify bindings pattern (rename slot (label row)) with
      | .exhausted => none
      | .clash => workValue label rows use (.scan pattern legs path bindings (slot + 1) rest)
      | .ok bound => do
          let (earlier, spent) ← workValue label rows use (.enter legs (row :: path) bound)
          let (later, more) ← workValue label rows (use + spent) (.scan pattern legs path bindings (slot + 1) rest)
          some (earlier ++ later, spent + more)) := by
  simp only [workValue, scan_cons]
  cases tail : scan label bindings pattern (slot + 1) rest <;>
    cases unified : unify bindings pattern (rename slot (label row)) <;>
    simp [queryBranches]

private def continuedValue : Transition (State O) (Packet O) Nat Empty → Option (List (Packet O) × Nat)
  | .silent next => remaining label next
  | .publish packets next => (remaining label next).map fun (later, last) => (packets ++ later, last)
  | .finish last => some ([], last)
  | .fail _ | .call _ _ => none

private theorem move_exact (state : State O) : continuedValue label (move label state) = remaining label state := by
  rcases state with ⟨rows, use, tasks⟩
  cases tasks with
  | nil => simp [move, continuedValue, remaining, queryBranches]
  | cons task rest =>
      cases task with
      | enter legs path bindings =>
          cases legs with
          | nil =>
            simp only [move, continuedValue, remaining, queryBranches, workValue, subtree, queryJoin]
            cases tail : queryBranches (workValue label rows) use rest <;> simp [attachPath, tail]
          | cons pattern legs =>
            simp only [move, continuedValue, remaining, queryBranches, enter_value]
            cases joined : workValue label rows (use + rows.length)
                (.scan pattern legs path bindings use rows) with
            | none => rfl
            | some batch =>
                rcases batch with ⟨packets, spent⟩
                simp only [Option.map_some, Option.bind_some, bind]
                rw [← Nat.add_assoc use rows.length spent]
                cases queryBranches (workValue label rows) (use + rows.length + spent) rest <;>
                  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      | scan pattern legs path bindings slot unvisited =>
          cases unvisited with
          | nil =>
            simp [move, continuedValue, remaining, queryBranches, workValue, scan, queryRows]
          | cons row unvisited =>
            cases matched : unify bindings pattern (rename slot (label row)) with
            | exhausted => simp [move, matched, continuedValue, remaining, queryBranches, scan_cons_value]
            | clash => simp [move, matched, continuedValue, remaining, queryBranches, scan_cons_value]
            | ok bound =>
              simp only [move, matched, continuedValue, remaining]
              conv_rhs => rw [queryBranches, scan_cons_value, matched]
              rw [queryBranches]
              cases head : workValue label rows use (.enter legs (row :: path) bound) with
              | none => simp [head]
              | some first =>
                rcases first with ⟨earlier, spent⟩
                simp only [head, bind, Option.bind_some]
                rw [queryBranches]
                cases workValue label rows (use + spent)
                    (.scan pattern legs path bindings (slot + 1) unvisited) with
                | none => simp
                | some second =>
                  rcases second with ⟨later, more⟩
                  simp only [bind, Option.bind_some]
                  rw [← Nat.add_assoc use spent more]
                  cases queryBranches (workValue label rows) (use + spent + more) rest <;>
                    simp [List.append_assoc, Nat.add_assoc]

private def includePackets (packets : List (Packet O)) (tail : Option (List (Packet O) × Nat)) :
    Option (List (Packet O) × Nat) :=
  tail.map fun (later, last) => (packets ++ later, last)

/-- Recover the completed source answer from a run, possibly by also reading
its not-yet-demanded suffix. A partial search without a completion receipt is
not a negative answer for the fully captured source profile. -/
def reconstruct (run : List (Packet O) × Outcome (State O) Nat Empty) :
    Option (List (Packet O) × Nat) :=
  match run.2 with
  | .finished last => some (run.1, last)
  | .exhausted saved => includePackets run.1 (remaining label saved)
  | .faulted | .stuck _ | .suspended _ _ => none

private theorem reconstruct_append (earlier : List (Packet O))
    (run : List (Packet O) × Outcome (State O) Nat Empty) :
    reconstruct label (earlier ++ run.1, run.2) = includePackets earlier (reconstruct label run) := by
  rcases run with ⟨observed, status⟩
  cases status <;> simp [reconstruct, includePackets, Option.map_map, Function.comp_def, List.append_assoc]

theorem run_exact (fuel : Nat) (state : State O) :
    reconstruct label ((machine label).run fuel state) = remaining label state := by
  induction fuel generalizing state with
  | zero =>
      change includePackets [] (remaining label state) = _
      cases remaining label state <;> rfl
  | succ fuel ih =>
      cases moved : move label state with
      | silent next =>
          rw [(machine label).run_succ_silent (congrArg some moved), ih]
          simpa only [moved, continuedValue] using move_exact label state
      | publish packets next =>
          rw [(machine label).run_succ_publish (congrArg some moved), reconstruct_append, ih]
          simpa only [moved, continuedValue, includePackets] using move_exact label state
      | finish last =>
          rw [(machine label).run_succ_finish (congrArg some moved)]
          simpa only [moved, continuedValue, reconstruct] using move_exact label state
      | fail faults =>
          rw [(machine label).run_succ_fail (congrArg some moved)]
          simpa only [moved, continuedValue, reconstruct] using move_exact label state
      | call request saved => cases request

theorem finished_start (rows : List O) (legs : List Atom) (bindings : Subst) (use fuel : Nat)
    {packets : List (Packet O)} {last : Nat}
    (finished : (machine label).run fuel (start rows legs bindings use) = (packets, .finished last)) :
    ∃ spent, queryJoin label rows legs bindings use = some (packets, spent) ∧ last = use + spent := by
  have exactRun := run_exact label fuel (start rows legs bindings use)
  rw [finished, remaining_start] at exactRun
  obtain ⟨⟨found, spent⟩, read, equal⟩ := Option.map_eq_some_iff.mp exactRun.symm
  obtain ⟨rfl, same⟩ := Prod.mk.inj equal
  exact ⟨spent, read, same.symm⟩

private def enterBudget (width : Nat) : Nat → Nat
  | 0 => 1
  | legs + 1 => 2 + width * (enterBudget width legs + 1)

private def workBudget (width : Nat) : Work O → Nat
  | .enter legs _ _ => enterBudget width legs.length
  | .scan _ legs _ _ _ rows => 1 + rows.length * (enterBudget width legs.length + 1)

/-- A finite bound on cursor transitions, not a work estimate for the
unifier or a budget the incremental reader has to compute. -/
def budget (state : State O) : Nat :=
  1 + (state.work.map (workBudget state.view.length)).sum

theorem next_retains_view {state reached : State O}
    (taken : move label state = .silent reached ∨
      ∃ packets, move label state = .publish packets reached) :
    reached.view = state.view ∧ budget reached < budget state := by
  rcases state with ⟨rows, use, tasks⟩
  cases tasks with
  | nil =>
      rcases taken with impossible | ⟨_, impossible⟩ <;> cases impossible
  | cons task rest =>
    cases task with
    | enter legs path bindings =>
      cases legs with
      | nil =>
          rcases taken with acted | ⟨_, acted⟩ <;> cases acted
          simp [budget, workBudget, enterBudget]
      | cons pattern legs =>
          rcases taken with acted | ⟨_, acted⟩ <;> cases acted
          simp [budget, workBudget, enterBudget]
    | scan pattern legs path bindings slot unvisited =>
      cases unvisited with
      | nil =>
          rcases taken with acted | ⟨_, acted⟩ <;> cases acted
          simp [budget, workBudget]
      | cons row restRows =>
          cases unified : unify bindings pattern (rename slot (label row)) <;>
            rcases taken with acted | ⟨_, acted⟩ <;>
            simp only [move, unified] at acted <;> cases acted <;>
            simp [budget, workBudget, Nat.succ_mul]
          all_goals omega

theorem paused_retains_view {fuel : Nat} {state saved : State O}
    (stopped : ((machine label).run fuel state).2 = .exhausted saved) : saved.view = state.view := by
  induction fuel generalizing state with
  | zero => exact congrArg State.view (Outcome.exhausted.inj stopped).symm
  | succ fuel ih =>
      cases moved : move label state with
      | silent reached =>
          rw [(machine label).run_succ_silent (congrArg some moved)] at stopped
          exact (ih stopped).trans (next_retains_view label (.inl moved)).1
      | publish packets reached =>
          rw [(machine label).run_succ_publish (congrArg some moved)] at stopped
          exact (ih stopped).trans (next_retains_view label (.inr ⟨packets,moved⟩)).1
      | finish last =>
          rw [(machine label).run_succ_finish (congrArg some moved)] at stopped
          cases stopped
      | fail packets =>
          rw [(machine label).run_succ_fail (congrArg some moved)] at stopped
          cases stopped
      | call request saved => cases request

theorem terminal_of_budget {fuel : Nat} {state : State O} (enough : budget state ≤ fuel) :
    ((machine label).run fuel state).2 = .faulted ∨
      ∃ last, ((machine label).run fuel state).2 = .finished last := by
  induction fuel generalizing state with
  | zero =>
      unfold budget at enough
      omega
  | succ fuel ih =>
      cases moved : move label state with
      | silent reached =>
          rw [(machine label).run_succ_silent (congrArg some moved)]
          apply ih
          have less := (next_retains_view label (.inl moved)).2
          omega
      | publish packets reached =>
          rw [(machine label).run_succ_publish (congrArg some moved)]
          apply ih
          have less := (next_retains_view label (.inr ⟨packets, moved⟩)).2
          omega
      | finish last =>
          rw [(machine label).run_succ_finish (congrArg some moved)]
          exact .inr ⟨last, rfl⟩
      | fail packets =>
          rw [(machine label).run_succ_fail (congrArg some moved)]
          exact .inl rfl
      | call request saved => cases request

theorem finish_iff (rows : List O) (legs : List Atom) (bindings : Subst) (use fuel : Nat)
    (enough : budget (start rows legs bindings use) ≤ fuel) (packets : List (Packet O)) (spent : Nat) :
    (machine label).run fuel (start rows legs bindings use) = (packets, .finished (use + spent)) ↔
      queryJoin label rows legs bindings use = some (packets,spent) := by
  constructor
  · intro finished
    obtain ⟨used, read, last⟩ := finished_start label rows legs bindings use fuel finished
    rwa [Nat.add_left_cancel last]
  · intro read
    have found := run_exact label fuel (start rows legs bindings use)
    rw [remaining_start, read] at found
    rcases terminal_of_budget label enough with faulted | ⟨last, finished⟩
    · simp [reconstruct, faulted] at found
    · rw [reconstruct, finished] at found
      obtain ⟨published, number⟩ := Prod.mk.inj (Option.some.inj found)
      exact Prod.ext published (finished.trans (congrArg Outcome.finished number))

/-- The completed cursor certifies the exact use charge without assuming a
particular bound or counting phase transitions as source instructions. -/
theorem finished_exact (rows : List O) (legs : List Atom) (bindings : Subst) (use fuel : Nat)
    {packets : List (Packet O)} {last : Nat}
    (finished : (machine label).run fuel (start rows legs bindings use) = (packets, .finished last)) :
    queryJoin label rows legs bindings use = some (packets, last - use) := by
  obtain ⟨spent, prepared, same⟩ := finished_start label rows legs bindings use fuel finished
  simpa only [same, Nat.add_sub_cancel_left] using prepared

/-- A certified complete capture and a paid cursor prefix determine one
common ordered continuation. Merely emitting some packets is not the
completion hypothesis: the unvisited work must still be licensed. -/
theorem paused_prefix_of_completed (rows : List O) (legs : List Atom) (bindings : Subst)
    (use fuel : Nat) {packets earlier : List (Packet O)} {spent : Nat} {saved : State O}
    (complete : queryJoin label rows legs bindings use = some (packets, spent))
    (paused : (machine label).run fuel (start rows legs bindings use) = (earlier, .exhausted saved)) :
    ∃ later, packets = earlier ++ later ∧ remaining label saved = some (later, use + spent) := by
  have exactRun := run_exact label fuel (start rows legs bindings use)
  rw [paused, remaining_start, complete] at exactRun
  change (remaining label saved).map (fun (later, last) => (earlier ++ later, last)) =
    some (packets, use + spent) at exactRun
  obtain ⟨⟨later, last⟩, read, equal⟩ := Option.map_eq_some_iff.mp exactRun
  obtain ⟨same, rfl⟩ := Prod.mk.inj equal
  exact ⟨later, same.symm, read⟩

end JoinCursor

variable [DecidableEq O]

theorem prepared_admitted (bindings : Subst) (pattern : Atom) (use : Nat)
    (rows : List O) (packets : List (O × Subst))
    (prepared : scan label bindings pattern use rows = some packets) (unique : rows.Nodup)
    (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, rows)) (request packets) := by
  refine ⟨⟨unique, List.nodup_nil, List.nodup_nil⟩, ?_, consistent⟩
  refine ⟨by simp [request, OrderedStore.Publication.commit, Selection.commit], ?_,
    by simp [request, OrderedStore.Publication.commit, Selection.commit],
    by simp [request, OrderedStore.Publication.commit, Selection.commit], ?_⟩
  · intro occurrence member
    exact List.mem_toFinset.mpr ((scanned_occurrences_sublist label bindings pattern use rows packets prepared).subset
      (List.mem_toFinset.mp member))
  · intro query member
    simp [request, OrderedStore.Publication.commit] at member

theorem read_preserves_store (knowledge : EquationStore Atom) (rows : List O)
    (packets : List (O × Subst))
    (admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, rows))
      (request packets)) :
    (OrderedStore.step atomFrames PUnit.unit label).result (request packets) admitted = (knowledge, rows) := by
  apply Prod.ext
  · exact OrderedStore.result_knowledge atomFrames PUnit.unit label admitted
  · rw [OrderedStore.result_rows]
    exact OrderedStore.reads_only _ _

/-- Preservation and reflection include the actual branch-local evaluation
requests and the target's unchanged world, not just its answer count. -/
theorem query_iff_target (bindings : Subst) (pattern body : Atom) (use : Nat)
    (rows : List O) (unique : rows.Nodup) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) (tasks : List Control) :
    queryBodies bindings pattern body use (rows.map label) = some tasks ↔
      ∃ packets, scan label bindings pattern use rows = some packets ∧
        continuations body packets = tasks ∧
        ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
            (s := (knowledge, rows)) (request packets),
          (OrderedStore.step atomFrames PUnit.unit label).result (request packets) admitted = (knowledge, rows) := by
  rw [scan_source]
  constructor
  · intro source
    obtain ⟨packets, prepared, same⟩ := Option.map_eq_some_iff.mp source
    have admitted := prepared_admitted label bindings pattern use rows packets prepared unique knowledge consistent
    exact ⟨packets, prepared, same, admitted, read_preserves_store label knowledge rows packets admitted⟩
  · rintro ⟨packets, prepared, same, _, _⟩
    simp [prepared, same]

omit [DecidableEq O] in
/-- The resulting requests enter the actual source continuation, retaining
all caller frames and advancing the source's renaming-use counter. -/
theorem source_query_transition (registry : PeTTa.SpaceSemantics.Program)
    (source : PeTTa.Unifying.Configuration) (answer : PeTTa.Unifying.Answer)
    (pattern body : Atom) (rest : List PeTTa.Unifying.Frame) (rows : List O)
    (packets : List (List O × Subst)) (used : Nat)
    (control : source.control = .returned [answer])
    (frames : source.frames = .query pattern body :: rest)
    (opened : (PeTTa.Effects.readHandle answer.value >>= source.state.read) = some (rows.map label))
    (prepared : queryJoin label rows (queryLegs pattern) answer.bindings source.uses = some (packets,used)) :
    PeTTa.Unifying.Transition registry source
      { source with
        control := .sequence (joinedBodies body packets) []
        frames := rest
        uses := source.uses + used } := by
  apply PeTTa.Unifying.Transition.query_return control frames
  simp [PeTTa.Unifying.queries, opened, PeTTa.Unifying.queryBatch_from_join, prepared]

/-- This joins the read effect to the real evaluator continuation. The
unchanged target store does not suppress body evaluation requests. -/
theorem query_effect_and_continuation (registry : PeTTa.SpaceSemantics.Program)
    (source : PeTTa.Unifying.Configuration) (answer : PeTTa.Unifying.Answer)
    (pattern body : Atom) (rest : List PeTTa.Unifying.Frame) (rows : List O)
    (packets : List (List O × Subst)) (used : Nat)
    (control : source.control = .returned [answer])
    (frames : source.frames = .query pattern body :: rest)
    (opened : (PeTTa.Effects.readHandle answer.value >>= source.state.read) = some (rows.map label))
    (prepared : queryJoin label rows (queryLegs pattern) answer.bindings source.uses = some (packets,used))
    (unique : rows.Nodup) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
        (s := (knowledge, rows)) (joinedRequest packets),
      (OrderedStore.step atomFrames PUnit.unit label).result (joinedRequest packets) admitted = (knowledge, rows) ∧
      PeTTa.Unifying.Transition registry source
        { source with
          control := .sequence (joinedBodies body packets) []
          frames := rest
          uses := source.uses + used } := by
  have admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
      (s := (knowledge,rows)) (joinedRequest packets) := by
    refine ⟨⟨unique, List.nodup_nil, List.nodup_nil⟩, ?_, consistent⟩
    refine ⟨by simp [joinedRequest, OrderedStore.Publication.commit, Selection.commit], ?_,
      by simp [joinedRequest, OrderedStore.Publication.commit, Selection.commit],
      by simp [joinedRequest, OrderedStore.Publication.commit, Selection.commit], ?_⟩
    · intro occurrence member
      exact List.mem_toFinset.mpr (joined_occurrences_in_view label prepared occurrence
        (List.mem_toFinset.mp member))
    · intro query member
      simp [joinedRequest, OrderedStore.Publication.commit] at member
  refine ⟨admitted, ?_, source_query_transition label registry source answer pattern body
    rest rows packets used control frames opened prepared⟩
  apply Prod.ext
  · exact OrderedStore.result_knowledge atomFrames PUnit.unit label admitted
  · rw [OrderedStore.result_rows]
    exact OrderedStore.reads_only _ _

omit [DecidableEq O] in
theorem exhaustion_is_not_empty (bindings : Subst) (pattern body : Atom) (use : Nat)
    (rows : List O) (exhausted : scan label bindings pattern use rows = none) :
    queryBodies bindings pattern body use (rows.map label) = none ∧
      queryBodies bindings pattern body use (rows.map label) ≠ some [] := by
  rw [scan_source, exhausted]
  simp

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation
