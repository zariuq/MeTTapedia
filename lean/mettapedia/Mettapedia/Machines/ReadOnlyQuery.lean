import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mettapedia.Logic.ArrayInvariants.UpdateTrace
import Mettapedia.Coalgebra.CoherentPrefixTower

/-!
# Read certificates for pure adaptive queries

A query's next read can depend on an earlier value. Its certificate therefore
records the reads actually executed, including negative lookups when the store
value is an `Option`. Agreement on those reads suffices to replay the same
control path and obtain the same result. Values may be ordered answer lists;
no quotient by answer support or multiplicity is taken.

This is a read-only computation interface, not a binding store or a cache
replacement. Query identity, owner identity, modes and source revisions must
still distinguish different programs. Effects cannot be hidden in `pure`.
Validation compares complete values, not hash fingerprints.

An observation stays at the snapshot world where the read was performed.
A residual that has already closed over that value returns it in the original
store and in a successor store. Revalidating the cached certificate against
the successor is a different policy: `checkReads` refuses the certificate when
the observed value no longer agrees. The successor's new answer comes from
running the original query again, not from running that closed residual.
A complete positive read depends on the whole ordered list. Replacing that
list can change candidates, count, and the first element while both answers
stay nonempty, so the none query versus presence does not classify the dependency.
A none read of the same key is not agreement. A suffix extension is called
an append example only under the ordering assumption stated on
`Controls.snapshot_advance_differs_from_validated_fresh`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQuery

universe u v w x

/-- A pure query whose continuation may depend on the observed store value. -/
inductive Program (Key : Type u) (Value : Type v) (Answer : Type w) where
  | pure (answer : Answer)
  | read (key : Key) (next : Value → Program Key Value Answer)

abbrev Reads (Key : Type u) (Value : Type v) := List (Key × Value)

/-- The result and the complete ordered read certificate. -/
structure Observation (Key : Type u) (Value : Type v) (Answer : Type w) where
  answer : Answer
  reads : Reads Key Value

variable {Key : Type u} {Value : Type v} {Answer : Type w} {Other : Type x}

def run (store : Key → Value) : Program Key Value Answer → Observation Key Value Answer
  | .pure answer => ⟨answer, []⟩
  | .read key next =>
      let observed := store key
      let rest := run store (next observed)
      ⟨rest.answer, (key, observed) :: rest.reads⟩

/-- Every read, including a missing lookup, must retain its observed value. -/
def Agrees (store : Key → Value) (reads : Reads Key Value) : Prop :=
  ∀ read ∈ reads, store read.1 = read.2

theorem run_agrees (store : Key → Value) (program : Program Key Value Answer) :
    Agrees store (run store program).reads := by
  induction program with
  | pure answer => simp [run, Agrees]
  | read key next ih =>
      intro observed member
      simp only [run, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih (store key) observed member

/-- Replaying an unchanged read certificate preserves both the result and
the read path; new dependencies cannot appear behind unchanged reads. -/
theorem run_eq_of_agrees (first second : Key → Value)
    (program : Program Key Value Answer)
    (agree : Agrees second (run first program).reads) :
    run second program = run first program := by
  induction program with
  | pure answer => rfl
  | read key next ih =>
      have here : second key = first key :=
        agree (key, first key) (by simp [run])
      have tail : Agrees second (run first (next (first key))).reads := by
        intro observed member
        exact agree observed (by simp [run, member])
      simp only [run, here, ih (first key) tail]

def checkReads [DecidableEq Value] (store : Key → Value) (reads : Reads Key Value) : Bool :=
  reads.all fun read => decide (store read.1 = read.2)

theorem checkReads_iff [DecidableEq Value] (store : Key → Value) (reads : Reads Key Value) :
    checkReads store reads = true ↔ Agrees store reads := by
  simp [checkReads, Agrees]

theorem agrees_append (store : Key → Value) (first second : Reads Key Value) :
    Agrees store (first ++ second) ↔ Agrees store first ∧ Agrees store second := by
  simp [Agrees, List.mem_append, or_imp, forall_and]

/-- Nested observations retain both read certificates, in execution order. -/
theorem checkReads_append [DecidableEq Value] (store : Key → Value)
    (first second : Reads Key Value) :
    checkReads store (first ++ second) = (checkReads store first && checkReads store second) := by
  simp [checkReads, List.all_append]

/-- A successful executable validation licenses reuse of the old result. -/
theorem validated_answer [DecidableEq Value] (first second : Key → Value)
    (program : Program Key Value Answer)
    (valid : checkReads second (run first program).reads = true) :
    (run second program).answer = (run first program).answer :=
  congrArg Observation.answer (run_eq_of_agrees first second program
    ((checkReads_iff _ _).mp valid))

/-- An unchanged coordinate may be read more than once; occurrence order is
retained in the certificate. -/
def samples (store : Key → Value) (keys : List Key) : Reads Key Value :=
  keys.map fun key => (key, store key)

theorem agrees_samples_iff (first second : Key → Value) (keys : List Key) :
    Agrees second (samples first keys) ↔ ∀ key ∈ keys, second key = first key := by
  simp [Agrees, samples]

/-- A trace that writes no sampled coordinate retains the certificate. -/
theorem trace_preserves_reads [DecidableEq Key]
    (initial : Key → Value)
    (writes : Nat → Option (Mettapedia.Logic.ArrayInvariants.UpdateTrace.Write Key Value))
    (start finish : Nat) (reads : Reads Key Value)
    (valid : Agrees (Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes start) reads)
    (ordered : start ≤ finish)
    (untouched : ∀ read ∈ reads, ∀ i, start ≤ i → i < finish →
      ¬ Mettapedia.Logic.ArrayInvariants.UpdateTrace.Updates writes i read.1) :
    Agrees (Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes finish) reads := by
  intro read member
  exact (Mettapedia.Logic.ArrayInvariants.UpdateTrace.stable_between initial writes
    start finish read.1 ordered (untouched read member)).trans (valid read member)

/-- Sequential query composition retains reads from the first computation
and every dependency selected by its answer. -/
def bind (program : Program Key Value Answer)
    (next : Answer → Program Key Value Other) : Program Key Value Other :=
  match program with
  | .pure answer => next answer
  | .read key more => .read key fun value => bind (more value) next

theorem run_bind (store : Key → Value) (program : Program Key Value Answer)
    (next : Answer → Program Key Value Other) :
    run store (bind program next) =
      let first := run store program
      let second := run store (next first.answer)
      ⟨second.answer, first.reads ++ second.reads⟩ := by
  induction program with
  | pure answer => rfl
  | read key more ih => simp [bind, run, ih]

/-- Checking a returned nested computation includes every read made by its
answer-selected continuation, including reads that produced no matches. -/
theorem checkReads_bind [DecidableEq Value] (first second : Key → Value)
    (program : Program Key Value Answer) (next : Answer → Program Key Value Other) :
    checkReads second (run first (bind program next)).reads =
      (checkReads second (run first program).reads &&
        checkReads second (run first (next (run first program).answer)).reads) := by
  rw [run_bind]
  exact checkReads_append _ _ _

/-- Validation of both certificates preserves the entire composed observation,
not only its returned answer. The continuation is selected by the first answer. -/
theorem validated_bind [DecidableEq Value] (first second : Key → Value)
    (program : Program Key Value Answer) (next : Answer → Program Key Value Other)
    (parentValid : checkReads second (run first program).reads = true)
    (childValid : checkReads second (run first (next (run first program).answer)).reads = true) :
    run second (bind program next) = run first (bind program next) := by
  apply run_eq_of_agrees first second (bind program next)
  apply (checkReads_iff _ _).mp
  rw [checkReads_bind, parentValid, childValid]
  rfl

/-- A stable caller cannot license publication after a child dependency changed. -/
theorem changed_child_rejects_bind [DecidableEq Value] (first second : Key → Value)
    (program : Program Key Value Answer) (next : Answer → Program Key Value Other)
    (childChanged : checkReads second
      (run first (next (run first program).answer)).reads = false) :
    checkReads second (run first (bind program next)).reads = false := by
  rw [checkReads_bind, childChanged]
  exact Bool.and_false _

/-- Continue from a previously obtained observation. Only the answer-selected
suffix runs; the old reads remain dependencies and are not sampled again.
This construction concerns read-only queries, not hidden effects in `pure`. -/
def Observation.extend (cached : Observation Key Value Answer)
    (store : Key → Value) (next : Answer → Program Key Value Other) :
    Observation Key Value Other :=
  let suffix := run store (next cached.answer)
  ⟨suffix.answer, cached.reads ++ suffix.reads⟩

/-- Reusing a validated cached prefix has the same complete observation as
the independently interpreted sequential query in the current store. -/
theorem extend_eq_run_bind_of_valid [DecidableEq Value]
    (before after : Key → Value) (program : Program Key Value Answer)
    (next : Answer → Program Key Value Other)
    (valid : checkReads after (run before program).reads = true) :
    (run before program).extend after next = run after (bind program next) := by
  have unchanged := run_eq_of_agrees before after program ((checkReads_iff _ _).mp valid)
  rw [← unchanged, run_bind]
  rfl

/-- New work cannot replace the old certificate by its own fresh reads. -/
theorem checkReads_extend [DecidableEq Value] (store : Key → Value)
    (cached : Observation Key Value Answer) (next : Answer → Program Key Value Other) :
    checkReads store (cached.extend store next).reads =
      (checkReads store cached.reads && checkReads store (run store (next cached.answer)).reads) :=
  checkReads_append store _ _

/-- A changed cached read refuses the combined result even when the suffix
has just read the new value. -/
theorem changed_cached_read_refuses_extend [DecidableEq Value]
    (store : Key → Value) (cached : Observation Key Value Answer)
    (next : Answer → Program Key Value Other)
    (changed : checkReads store cached.reads = false) :
    checkReads store (cached.extend store next).reads = false := by
  rw [checkReads_extend, changed]
  rfl

def map (f : Answer → Other) (program : Program Key Value Answer) :
    Program Key Value Other := bind program fun answer => .pure (f answer)

theorem run_map (store : Key → Value) (program : Program Key Value Answer)
    (f : Answer → Other) :
    run store (map f program) =
      ⟨f (run store program).answer, (run store program).reads⟩ := by
  simp [map, run_bind, run]

/-! ## Coverage of fuelled recursive queries

The store may itself be the preceding depth of a recursive computation. Checking
every dependency actually read distinguishes a completed negative answer from
an approximation that stopped at depth zero. The unfolding equation below is
an obligation of the concrete computation; coverage never infers convergence
from two equal successive answers.
-/

/-- All recursively requested results used by this answer have enough depth. -/
def depthCovered (body : Key → Program Key Value Value)
    (eval : Nat → Key → Value) : Nat → Key → Bool
  | 0, _ => false
  | depth + 1, key =>
      (run (eval depth) (body key)).reads.all fun read =>
        depthCovered body eval depth read.1

/-- A covered computation has the same answer at every greater depth. This
includes failed searches and branches selected by negative answers. -/
theorem depthCovered_stable (body : Key → Program Key Value Value)
    (eval : Nat → Key → Value)
    (unfold : ∀ depth key, eval (depth + 1) key =
      (run (eval depth) (body key)).answer)
    (depth extra : Nat) (key : Key)
    (covered : depthCovered body eval depth key = true) :
    eval (depth + extra) key = eval depth key := by
  induction depth generalizing key extra with
  | zero => simp [depthCovered] at covered
  | succ depth ih =>
      rw [Nat.succ_add, unfold, unfold]
      apply congrArg Observation.answer
      apply run_eq_of_agrees
      intro read member
      have child : depthCovered body eval depth read.1 = true :=
        List.all_eq_true.mp covered read member
      exact (ih extra read.1 child).trans
        (run_agrees (eval depth) (body key) read member)

/-- Once every reached dependency was covered, extra depth neither changes the
read path nor invalidates the completion certificate. -/
theorem depthCovered_mono (body : Key → Program Key Value Value)
    (eval : Nat → Key → Value)
    (unfold : ∀ depth key, eval (depth + 1) key =
      (run (eval depth) (body key)).answer)
    (depth extra : Nat) (key : Key)
    (covered : depthCovered body eval depth key = true) :
    depthCovered body eval (depth + extra) key = true := by
  induction depth generalizing key with
  | zero => simp [depthCovered] at covered
  | succ depth ih =>
      have same : run (eval (depth + extra)) (body key) = run (eval depth) (body key) := by
        apply run_eq_of_agrees
        intro read found
        have visit := List.all_eq_true.mp covered read found
        exact (depthCovered_stable body eval unfold depth extra read.1 visit).trans
          (run_agrees (eval depth) (body key) read found)
      rw [Nat.succ_add, depthCovered, same]
      exact List.all_eq_true.mpr fun read found =>
        ih read.1 (List.all_eq_true.mp covered read found)

/-- A concrete decreasing dependency rank supplies a sufficient query depth.
This checks the reads the actual adaptive body makes at each approximation. -/
theorem depthCovered_of_rank (body : Key → Program Key Value Value)
    (eval : Nat → Key → Value) (rank : Key → Nat)
    (decreases : ∀ depth key read,
      read ∈ (run (eval depth) (body key)).reads → rank read.1 < rank key)
    (depth : Nat) (key : Key) (enough : rank key < depth) :
    depthCovered body eval depth key = true := by
  induction depth generalizing key with
  | zero => omega
  | succ depth ih =>
      apply List.all_eq_true.mpr
      intro read member
      exact ih read.1 (by have smaller := decreases depth key read member; omega)

/-- Traverse a finite family of pure queries, concatenating their answers. -/
def flatTraverse {Item : Type x} (items : List Item)
    (query : Item → Program Key Value (List Answer)) :
    Program Key Value (List Answer) :=
  match items with
  | [] => .pure []
  | item :: rest => bind (query item) fun first =>
      map (first ++ ·) (flatTraverse rest query)

theorem run_flatTraverse {Item : Type x} (store : Key → Value)
    (items : List Item) (query : Item → Program Key Value (List Answer)) :
    (run store (flatTraverse items query)).answer =
      items.flatMap fun item => (run store (query item)).answer := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [flatTraverse, run_bind, run_map, ih]

/-- Traversal records every child query's reads in physical visit order,
including repeated equal reads and failed lookups. -/
theorem run_flatTraverse_reads {Item : Type x} (store : Key → Value)
    (items : List Item) (query : Item → Program Key Value (List Answer)) :
    (run store (flatTraverse items query)).reads =
      items.flatMap fun item => (run store (query item)).reads := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [flatTraverse, run_bind, run_map, ih]

/-- A left fold whose next query depends on the accumulator. -/
def foldQueries {Item : Type x} (items : List Item) (initial : Answer)
    (query : Answer → Item → Program Key Value Answer) : Program Key Value Answer :=
  match items with
  | [] => .pure initial
  | item :: rest => bind (query initial item) fun next => foldQueries rest next query

theorem run_foldQueries {Item : Type x} (store : Key → Value)
    (items : List Item) (initial : Answer)
    (query : Answer → Item → Program Key Value Answer) :
    (run store (foldQueries items initial query)).answer =
      items.foldl (fun acc item => (run store (query acc item)).answer) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => simp [foldQueries, run_bind, ih]

/-! ## Resuming after a performed read prefix

A paused query has performed some reads in the store where it ran, and its
residual program closes over the values it saw. Resumed in another store, the
residual's later reads see that store. The resumed result is the fresh result
there whenever every performed read still agrees, none checks included
(`resumed_eq_fresh_of_prefix_agrees`). A check confined to the reads the
residual has still to make does not establish this
(`Controls.pending_only_check_accepts_stale_none`), and agreement of the
performed reads does not require an unchanged store
(`Controls.prefix_check_accepts_unrelated_change`). A residual that has already
closed over its value returns that value in either store. The successor answer
of the original query is a new run of that query, not a run of the closed
residual (`Controls.snapshot_advance_differs_from_validated_fresh`). -/

/-- Perform at most `steps` reads in `store`; return them, oldest first, with
the residual program. -/
def pausePrefix (store : Key → Value) : Nat → Program Key Value Answer →
    Reads Key Value × Program Key Value Answer
  | 0, program => ([], program)
  | _ + 1, .pure answer => ([], .pure answer)
  | steps + 1, .read key next =>
      let rest := pausePrefix store steps (next (store key))
      ((key, store key) :: rest.1, rest.2)

/-- The performed reads are a valid certificate in the store where they ran. -/
theorem pausePrefix_agrees (store : Key → Value) :
    ∀ (steps : Nat) (program : Program Key Value Answer),
      Agrees store (pausePrefix store steps program).1
  | 0, _ => by simp [pausePrefix, Agrees]
  | _ + 1, .pure _ => by simp [pausePrefix, Agrees]
  | steps + 1, .read key next => by
      intro read member
      simp only [pausePrefix, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact pausePrefix_agrees store steps (next (store key)) read member

/-- **Resumption after a validated prefix is the fresh run.** If every read
performed before the pause agrees with the store of resumption, resuming the
residual there gives the fresh run's answer, and the performed reads followed by
the residual's reads are exactly the fresh run's certificate. -/
theorem resumed_eq_fresh_of_prefix_agrees (paused resumed : Key → Value) :
    ∀ (steps : Nat) (program : Program Key Value Answer),
      Agrees resumed (pausePrefix paused steps program).1 →
        (run resumed (pausePrefix paused steps program).2).answer =
            (run resumed program).answer ∧
          (pausePrefix paused steps program).1 ++
              (run resumed (pausePrefix paused steps program).2).reads =
            (run resumed program).reads
  | 0, _, _ => by simp [pausePrefix]
  | _ + 1, .pure _, _ => by simp [pausePrefix, run]
  | steps + 1, .read key next, agree => by
      have here : resumed key = paused key := agree (key, paused key) (by simp [pausePrefix])
      have tail : Agrees resumed (pausePrefix paused steps (next (paused key))).1 := by
        intro read member
        exact agree read (by simp [pausePrefix, member])
      obtain ⟨answer, reads⟩ :=
        resumed_eq_fresh_of_prefix_agrees paused resumed steps (next (paused key)) tail
      simp only [pausePrefix, run, here, List.cons_append]
      exact ⟨answer, by rw [reads]⟩

/-- Pausing and resuming in the same store repeats and loses no read. -/
theorem resumed_eq_run_same_store (store : Key → Value) (steps : Nat)
    (program : Program Key Value Answer) :
    (run store (pausePrefix store steps program).2).answer = (run store program).answer ∧
      (pausePrefix store steps program).1 ++ (run store (pausePrefix store steps program).2).reads =
        (run store program).reads :=
  resumed_eq_fresh_of_prefix_agrees store store steps program
    (pausePrefix_agrees store steps program)

/-! ### Retained adaptive reads

The existing prefix and residual form the retained state. A snapshot runner
uses one fixed store. Validated resumption is a separate operation: it checks
the entire performed prefix before reading any pending key in the new store.
Neither operation silently restarts the original query.
-/

theorem pausePrefix_add (store : Key → Value) (first extra : Nat)
    (program : Program Key Value Answer) :
    pausePrefix store (first + extra) program =
      let earlier := pausePrefix store first program
      let later := pausePrefix store extra earlier.2
      (earlier.1 ++ later.1, later.2) := by
  induction first generalizing program with
  | zero => simp [pausePrefix]
  | succ first ih =>
      cases program with
      | pure answer =>
          cases extra <;> simp [pausePrefix]
      | read key next =>
          simp [Nat.succ_add, pausePrefix, ih, List.cons_append]

namespace Retained

abbrev State (Key : Type u) (Value : Type v) (Answer : Type w) :=
  Reads Key Value × Program Key Value Answer

def begin (program : Program Key Value Answer) : State Key Value Answer := ([], program)

def resume (store : Key → Value) (fuel : Nat)
    (state : State Key Value Answer) : State Key Value Answer :=
  let next := pausePrefix store fuel state.2
  (state.1 ++ next.1, next.2)

theorem resume_zero (store : Key → Value) (state : State Key Value Answer) :
    resume store 0 state = state := by
  cases state
  simp [resume, pausePrefix]

theorem resume_add (store : Key → Value) (first extra : Nat)
    (state : State Key Value Answer) :
    resume store (first + extra) state = resume store extra (resume store first state) := by
  simp [resume, pausePrefix_add, List.append_assoc]

def trajectory (store : Key → Value) (state : State Key Value Answer) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory (resume store) state :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical _ state
    (resume_zero store) (fun first extra current => resume_add store first extra current)

theorem reads_prefix (store : Key → Value) (fuel : Nat) (state : State Key Value Answer) :
    state.1 <+: (resume store fuel state).1 := by
  exact ⟨_, rfl⟩

theorem trajectory_reads_prefix (store : Key → Value) (state : State Key Value Answer)
    (first extra : Nat) :
    ((trajectory store state).observation first).1 <+:
      ((trajectory store state).observation (first + extra)).1 :=
  (trajectory store state).observer_prefix_after_resume Prod.fst
    (fun fuel current => reads_prefix store fuel current) first extra

/-- Refusal executes no pending read and returns no replacement state. A
caller retains the original state on this branch. -/
def resumeValidated [DecidableEq Value] (store : Key → Value) (fuel : Nat)
    (state : State Key Value Answer) : Option (State Key Value Answer) :=
  if checkReads store state.1 then some (resume store fuel state) else none

theorem resumeValidated_refused [DecidableEq Value] (store : Key → Value) (fuel : Nat)
    (state : State Key Value Answer) (changed : checkReads store state.1 = false) :
    resumeValidated store fuel state = none := by
  simp [resumeValidated, changed]

theorem resumeValidated_accepted [DecidableEq Value] (store : Key → Value) (fuel : Nat)
    (state : State Key Value Answer) (valid : checkReads store state.1 = true) :
    resumeValidated store fuel state = some (resume store fuel state) := by
  simp [resumeValidated, valid]

/-- A state earned by pausing the original query gives the fresh answer and
complete read certificate after validating its performed prefix. This is a
read-only law; it does not license repeating effects or changing authorities. -/
theorem validated_fresh [DecidableEq Value] (paused current : Key → Value)
    (first : Nat) (program : Program Key Value Answer)
    (valid : checkReads current (pausePrefix paused first program).1 = true) :
    (run current (pausePrefix paused first program).2).answer = (run current program).answer ∧
      (pausePrefix paused first program).1 ++
        (run current (pausePrefix paused first program).2).reads = (run current program).reads :=
  resumed_eq_fresh_of_prefix_agrees paused current first program
    ((checkReads_iff current _).mp valid)

end Retained

namespace Controls

/-- A first read selects the next dependency. -/
def adaptive : Program Nat Nat (List Nat) :=
  .read 0 fun selected => .read selected fun value => .pure [value, value]

def original : Nat → Nat
  | 0 => 2
  | 2 => 7
  | _ => 0

theorem ordered_duplicate_answers : (run original adaptive).answer = [7, 7] := rfl

theorem transitive_reads_recorded :
    (run original adaptive).reads = [(0, 2), (2, 7)] := rfl

theorem unrelated_write_validates :
    checkReads (Function.update original 1 99) (run original adaptive).reads = true := by
  decide

theorem changed_dependency_rejected :
    checkReads (Function.update original 2 8) (run original adaptive).reads = false := by
  decide

/-- Reading only the initial selector omits the selected value dependency. -/
theorem root_only_certificate_is_insufficient :
    checkReads (Function.update original 2 8) [(0, 2)] = true ∧
      (run (Function.update original 2 8) adaptive).answer ≠
        (run original adaptive).answer := by
  decide

/-- A failed lookup is a dependency: a later successful write changes it. -/
def negativeLookupQuery : Program Nat (Option Nat) Bool :=
  .read 4 fun value => .pure value.isNone

theorem negative_lookup_must_be_recorded :
    (run (fun _ => none) negativeLookupQuery).reads = [(4, none)] ∧
      checkReads (Function.update (fun _ => none) 4 (some 9))
        (run (fun _ => none) negativeLookupQuery).reads = false := by
  decide

/-- The complete ordered answer list is one read value, including emptiness
and repeated physical answers. Merely recording a returned witness is weaker. -/
def matchesAt (key : Nat) : Program Nat (List Nat) (List Nat) :=
  .read key fun values => .pure values

def originalMatches : Nat → List Nat
  | 0 => [3]
  | 1 => [7, 7]
  | _ => []

theorem nested_complete_matches_recorded :
    (run originalMatches (bind (matchesAt 0) fun _ => matchesAt 1)).reads =
      [(0, [3]), (1, [7, 7])] ∧
    (run originalMatches (bind (matchesAt 0) fun _ => matchesAt 1)).answer = [7, 7] := by
  decide

theorem child_match_insertion_invalidates :
    let changed := Function.update originalMatches 1 [7, 7, 8]
    checkReads changed (run originalMatches (matchesAt 0)).reads = true ∧
    checkReads changed
      (run originalMatches (bind (matchesAt 0) fun _ => matchesAt 1)).reads = false ∧
    (run changed (bind (matchesAt 0) fun _ => matchesAt 1)).answer = [7, 7, 8] := by
  decide

theorem empty_child_match_insertion_invalidates :
    let changed := Function.update originalMatches 2 [8]
    checkReads changed (run originalMatches (matchesAt 0)).reads = true ∧
    (run originalMatches (matchesAt 2)).answer = [] ∧
    checkReads changed
      (run originalMatches (bind (matchesAt 0) fun _ => matchesAt 2)).reads = false := by
  decide

theorem unrelated_match_write_preserves_composition :
    let changed := Function.update originalMatches 2 [8]
    checkReads changed
      (run originalMatches (bind (matchesAt 0) fun _ => matchesAt 1)).reads = true ∧
    run changed (bind (matchesAt 0) fun _ => matchesAt 1) =
      run originalMatches (bind (matchesAt 0) fun _ => matchesAt 1) := by
  dsimp
  constructor
  · decide
  · apply validated_bind
    · decide
    · decide

/-- Read whether key 4 is not present, then read key 5; the answer uses both. -/
def guardedQuery : Program Nat (Option Nat) (Bool × Option Nat) :=
  .read 4 fun guard => .read 5 fun value => .pure (guard.isNone, value)

def guardStore : Nat → Option Nat := fun key => if key = 5 then some 1 else none

/-- Pause after the none query of key 4 was read, then let key 4 appear. The
reads the residual still makes agree, yet the resumed answer keeps the stale
none query and differs from the fresh run; the performed prefix is refused. -/
theorem pending_only_check_accepts_stale_none :
    let paused := pausePrefix guardStore 1 guardedQuery
    let changed := Function.update guardStore 4 (some 9)
    checkReads changed (run guardStore paused.2).reads = true ∧
      (run changed paused.2).answer = (true, some 1) ∧
      (run changed guardedQuery).answer = (false, some 1) ∧
      checkReads changed paused.1 = false := by
  decide

/-- A change outside the performed reads leaves them valid, and resuming gives
the fresh answer, although the store itself changed. -/
theorem prefix_check_accepts_unrelated_change :
    let paused := pausePrefix guardStore 1 guardedQuery
    let changed := Function.update guardStore 7 (some 3)
    changed 7 ≠ guardStore 7 ∧
      checkReads changed paused.1 = true ∧
      (run changed paused.2).answer = (run changed guardedQuery).answer := by
  decide

theorem retained_validation_refuses_stale_none :
    let paused := pausePrefix guardStore 1 guardedQuery
    Retained.resumeValidated (Function.update guardStore 4 (some 9)) 1 paused = none := by
  decide

theorem retained_validation_accepts_unrelated_change :
    let paused := pausePrefix guardStore 1 guardedQuery
    let changed := Function.update guardStore 7 (some 3)
    Retained.resumeValidated changed 1 paused =
      some ([(4, none), (5, some 1)], .pure (true, some 1)) := by
  rfl

/-! ### Snapshot world versus validated-fresh

`positiveQuery` returns the complete list stored at its key, in that list's
order. Agreement is equality of the list. `Function.update positiveBefore 0
[9, 2, 2]` replaces that list. Both answers are nonempty, and the candidates,
count, and first element change. That replacement is not a physical append.

An append example needs an ordering assumption: the stored list is the
candidate sequence in admission order, and an append extends it by a suffix.
Under that assumption only, `[2, 2]` extended to `[2, 2, 9]` is an append.
The old list is a prefix, the count changes, the first element stays `2`,
and the cached certificate still fails.

`seenQuery` reads key 0 and returns it. After one step the residual is
`.pure 0`. Running that residual returns 0 in `seenBefore` and in `seenAfter`.
The answer 1 is `(run seenAfter seenQuery)`, a new run of the original query.
-/

/-- Complete ordered answers at key 0, with a repeated positive candidate. -/
def positiveBefore : Nat → List Nat
  | 0 => [2, 2]
  | _ => []

/-- Every key is not present. -/
def emptyBefore : Nat → List Nat := fun _ => []

/-- Every key was read as zero. -/
def seenBefore : Nat → Nat := fun _ => 0

/-- Read the whole ordered answer list at key 0. -/
def positiveQuery : Program Nat (List Nat) (List Nat) :=
  .read 0 fun values => .pure values

/-- Read key 0 once and return the value already observed. -/
def seenQuery : Program Nat Nat Nat :=
  .read 0 fun seen => .pure seen

/-- The one-step residual of `seenQuery` has closed over the observed zero. -/
theorem snapshot_residual_closed_over_zero :
    (pausePrefix seenBefore 1 seenQuery).2 = (.pure 0 : Program Nat Nat Nat) := by
  rfl

/-- Replacing the stored list changes a nonempty positive answer's candidates,
count, and first element. Under the suffix-extension assumption above,
`[2, 2] ++ [9] = [2, 2, 9]` is the append-shaped successor. A none query at the
key is not agreement. The closed residual returns 0 in both stores; answer 1
is a new run of `seenQuery`, and the cached certificate fails on the successor. -/
theorem snapshot_advance_differs_from_validated_fresh :
    let positiveAfter := Function.update positiveBefore 0 [9, 2, 2]
    let suffixAfter := Function.update positiveBefore 0 [2, 2, 9]
    let emptyAfter := Function.update emptyBefore 0 [4]
    let seenAfter := Function.update seenBefore 0 1
    let paused := pausePrefix seenBefore 1 seenQuery
    (run positiveBefore positiveQuery).answer = [2, 2] ∧
      (run positiveAfter positiveQuery).answer = [9, 2, 2] ∧
      (run positiveBefore positiveQuery).reads = [(0, [2, 2])] ∧
      (run positiveBefore positiveQuery).answer ≠ [] ∧
      (run positiveAfter positiveQuery).answer ≠ [] ∧
      (run positiveBefore positiveQuery).answer ≠ (run positiveAfter positiveQuery).answer ∧
      (run positiveBefore positiveQuery).answer.length = 2 ∧
      (run positiveAfter positiveQuery).answer.length = 3 ∧
      (run positiveBefore positiveQuery).answer.head? = some 2 ∧
      (run positiveAfter positiveQuery).answer.head? = some 9 ∧
      checkReads positiveAfter (run positiveBefore positiveQuery).reads = false ∧
      (run positiveBefore positiveQuery).answer ++ [9] =
        (run suffixAfter positiveQuery).answer ∧
      (run suffixAfter positiveQuery).answer = [2, 2, 9] ∧
      (run suffixAfter positiveQuery).answer.length = 3 ∧
      (run suffixAfter positiveQuery).answer.head? = some 2 ∧
      checkReads suffixAfter (run positiveBefore positiveQuery).reads = false ∧
      (run emptyBefore positiveQuery).answer = [] ∧
      (run emptyBefore positiveQuery).reads = [(0, [])] ∧
      (run emptyAfter positiveQuery).answer = [4] ∧
      checkReads emptyAfter (run emptyBefore positiveQuery).reads = false ∧
      paused.1 = [(0, 0)] ∧
      (run seenBefore paused.2).answer = 0 ∧
      (run seenAfter paused.2).answer = 0 ∧
      checkReads seenAfter paused.1 = false ∧
      (run seenBefore seenQuery).answer = 0 ∧
      (run seenAfter seenQuery).answer = 1 ∧
      (run seenAfter paused.2).answer ≠ (run seenAfter seenQuery).answer := by
  decide

/-- A cached empty lookup remains a dependency when a later read sees the
new value. Keeping only that later read would fabricate validation. -/
theorem newer_read_does_not_rebase_cached :
    let current : Nat → List Nat := fun key => if key = 0 then [4] else []
    let cached := run emptyBefore positiveQuery
    let combined := cached.extend current fun _ => positiveQuery
    combined.answer = [4] ∧
      combined.reads = [(0, []), (0, [4])] ∧
      checkReads current combined.reads = false ∧
      checkReads current (run current positiveQuery).reads = true := by
  decide

/-- An unchanged cached prefix and the new suffix retain both complete
ordered readouts, including repeated payloads. -/
theorem cached_then_query_retains_both :
    let combined := (run originalMatches (matchesAt 0)).extend originalMatches
      fun _ => matchesAt 1
    combined.answer = [7, 7] ∧ combined.reads = [(0, [3]), (1, [7, 7])] ∧
      checkReads originalMatches combined.reads = true := by
  decide

end Controls

/-! ## Ordered candidate selection

`concatenate` is the ordered join of the lists stored at the candidate keys.
It does not run a program. `firstSuccessScan` reads until the first nonempty
list and returns that list's first occurrence. `completeScan` reads every
candidate. Occurrence identity and payload are separate fields, so two equal
payloads remain two occurrences. Candidate order is an input of the program,
not a stored value: a certificate of one order does not license another.
-/

namespace OrderedSelection

structure Occurrence (Id : Type u) (Payload : Type v) where
  id : Id
  payload : Payload
  deriving DecidableEq

variable {Id : Type v} {Payload : Type w}

/-- The ordered join of the candidate lists. Not the trace of a scanner. -/
def concatenate (store : Key → List (Occurrence Id Payload)) : List Key →
    List (Occurrence Id Payload)
  | [] => []
  | key :: rest => store key ++ concatenate store rest

/-- Skip empty candidate lists. Return the first occurrence of the first
nonempty list, and do not read candidates after that success. -/
def firstSuccessScan : List Key →
    Program Key (List (Occurrence Id Payload)) (Option (Occurrence Id Payload))
  | [] => .pure none
  | key :: rest =>
      .read key fun occurrences =>
        match occurrences with
        | [] => firstSuccessScan rest
        | hit :: _ => .pure (some hit)

/-- Read every candidate, including empty lists, and append their occurrences. -/
def completeScan : List Key →
    Program Key (List (Occurrence Id Payload)) (List (Occurrence Id Payload))
  | [] => .pure []
  | key :: rest =>
      .read key fun here =>
        bind (completeScan rest) fun tail => .pure (here ++ tail)

/-- Reads of a first success: every earlier empty list, then the selected
candidate's full list. Later candidates are not present. -/
def dependencyReads (store : Key → List (Occurrence Id Payload)) : List Key →
    Reads Key (List (Occurrence Id Payload))
  | [] => []
  | key :: rest =>
      match store key with
      | [] => (key, []) :: dependencyReads store rest
      | occurrences => [(key, occurrences)]

/-- Local cardinality of one complete stream. Two occurrences fail it even
when their payloads are equal. This is not a claim about later runs. -/
def atMostOne : List (Occurrence Id Payload) → Bool
  | [] => true
  | [_] => true
  | _ :: _ :: _ => false

theorem firstSuccessScan_eq_concatenate_head (store : Key → List (Occurrence Id Payload)) :
    ∀ candidates,
      (run store (firstSuccessScan candidates)).answer = (concatenate store candidates).head?
  | [] => by rfl
  | key :: rest => by
      cases h : store key with
      | nil =>
          rw [firstSuccessScan, concatenate, h, List.nil_append, run]
          simpa [h] using firstSuccessScan_eq_concatenate_head store rest
      | cons hit tail =>
          rw [firstSuccessScan, concatenate, h, run]
          simp [run, h, List.head?_cons]

theorem firstSuccessScan_reads_eq (store : Key → List (Occurrence Id Payload)) :
    ∀ candidates,
      (run store (firstSuccessScan candidates)).reads = dependencyReads store candidates
  | [] => by rfl
  | key :: rest => by
      cases h : store key with
      | nil =>
          rw [firstSuccessScan, dependencyReads, h, run]
          simpa [h] using firstSuccessScan_reads_eq store rest
      | cons hit tail =>
          rw [firstSuccessScan, dependencyReads, h, run]
          simp [run, h]

theorem dependencyReads_earlier_empties
    (store : Key → List (Occurrence Id Payload))
    (earlier : List Key) (selected : Key) (later : List Key)
    (empties : ∀ key ∈ earlier, store key = [])
    (selectedNonempty : store selected ≠ []) :
    dependencyReads store (earlier ++ selected :: later) =
      earlier.map (fun key => (key, ([] : List (Occurrence Id Payload)))) ++
        [(selected, store selected)] := by
  induction earlier with
  | nil =>
      cases h : store selected with
      | nil => exact (selectedNonempty h).elim
      | cons hit tail =>
          simp [dependencyReads, h, List.map_nil, List.nil_append]
  | cons key rest ih =>
      have emptyKey : store key = [] := empties key (by simp)
      have restEmpty : ∀ k ∈ rest, store k = [] :=
        fun k member => empties k (List.mem_cons_of_mem key member)
      simp [dependencyReads, List.cons_append, List.map_cons, emptyKey, ih restEmpty]

theorem completeScan_eq_concatenate (store : Key → List (Occurrence Id Payload)) :
    ∀ candidates,
      (run store (completeScan candidates)).answer = concatenate store candidates
  | [] => by rfl
  | key :: rest => by
      rw [completeScan, concatenate, run, run_bind]
      simp only [run]
      rw [completeScan_eq_concatenate store rest]

theorem completeScan_reads_eq (store : Key → List (Occurrence Id Payload)) :
    ∀ candidates,
      (run store (completeScan candidates)).reads =
        candidates.map fun key => (key, store key)
  | [] => by rfl
  | key :: rest => by
      rw [completeScan, run, run_bind]
      simp only [run, List.map_cons, List.append_nil]
      rw [completeScan_reads_eq store rest]

/-- Validating the recorded reads preserves the chosen occurrence and the read
path. Keys missing from that path, including candidates after the success, may
change without disturbing this run. -/
theorem validated_first_success
    [DecidableEq Id] [DecidableEq Payload]
    (first second : Key → List (Occurrence Id Payload)) (candidates : List Key)
    (valid : checkReads second (run first (firstSuccessScan candidates)).reads = true) :
    run second (firstSuccessScan candidates) = run first (firstSuccessScan candidates) :=
  run_eq_of_agrees first second (firstSuccessScan candidates)
    ((checkReads_iff second _).mp valid)

theorem unread_key_may_change
    [DecidableEq Key] [DecidableEq Id] [DecidableEq Payload]
    (store : Key → List (Occurrence Id Payload)) (candidates : List Key)
    (key : Key) (value : List (Occurrence Id Payload))
    (missing : ∀ read ∈ (run store (firstSuccessScan candidates)).reads, read.1 ≠ key) :
    run (Function.update store key value) (firstSuccessScan candidates) =
      run store (firstSuccessScan candidates) := by
  apply run_eq_of_agrees store (Function.update store key value)
  intro read member
  have different : read.1 ≠ key := missing read member
  rw [Function.update_apply, if_neg different]
  exact run_agrees store (firstSuccessScan candidates) read member

/-- A `Retained` state from the existing runner keeps the captured result when
resumed in the store where it paused. -/
theorem retained_resume_preserves_captured
    (store : Key → List (Occurrence Id Payload)) (fuel : Nat) (candidates : List Key) :
    let program := firstSuccessScan candidates
    let paused := Retained.resume store fuel (Retained.begin program)
    (run store paused.2).answer = (run store program).answer ∧
      paused.1 ++ (run store paused.2).reads = (run store program).reads := by
  simpa [Retained.begin, Retained.resume] using
    resumed_eq_run_same_store store fuel (firstSuccessScan candidates)

/-- Reuse in a new world is the existing validated-prefix policy, not the
resume of a residual that has already closed over old values. -/
theorem validated_reuse_is_separate
    [DecidableEq Id] [DecidableEq Payload]
    (paused current : Key → List (Occurrence Id Payload)) (fuel : Nat) (candidates : List Key)
    (valid : checkReads current
      (pausePrefix paused fuel (firstSuccessScan candidates)).1 = true) :
    Retained.resumeValidated current fuel (pausePrefix paused fuel (firstSuccessScan candidates)) =
      some (Retained.resume current fuel (pausePrefix paused fuel (firstSuccessScan candidates))) ∧
      (run current (pausePrefix paused fuel (firstSuccessScan candidates)).2).answer =
        (run current (firstSuccessScan candidates)).answer :=
  ⟨Retained.resumeValidated_accepted current fuel _ valid,
    (Retained.validated_fresh paused current fuel (firstSuccessScan candidates) valid).1⟩

/-- The certificate that licenses reuse of the cardinality check is the
complete stream. -/
theorem complete_stream_is_the_reuse_certificate
    [DecidableEq Id] [DecidableEq Payload]
    (first second : Key → List (Occurrence Id Payload)) (candidates : List Key)
    (valid : checkReads second (run first (completeScan candidates)).reads = true) :
    (run second (completeScan candidates)).answer = concatenate first candidates ∧
      (run second (map atMostOne (completeScan candidates))).answer =
        atMostOne (concatenate first candidates) := by
  have same := run_eq_of_agrees first second (completeScan candidates)
    ((checkReads_iff second _).mp valid)
  refine ⟨?_, ?_⟩
  · rw [same, completeScan_eq_concatenate]
  · rw [run_map, same, completeScan_eq_concatenate]

def orderWorld : Nat → List (Occurrence Nat Nat)
  | 0 => [⟨1, 7⟩]
  | 1 => [⟨2, 9⟩]
  | _ => []

def orderWorldLater : Nat → List (Occurrence Nat Nat) :=
  Function.update orderWorld 1 [⟨3, 7⟩]

def fallbackWorld : Nat → List (Occurrence Nat Nat)
  | 0 => []
  | 1 => [⟨4, 5⟩]
  | _ => []

def singletonWorld : Nat → List (Occurrence Nat Nat)
  | 0 => [⟨1, 7⟩]
  | _ => []

def equalPayloadWorld : Nat → List (Occurrence Nat Nat)
  | 0 => [⟨1, 7⟩]
  | 1 => [⟨2, 7⟩]
  | _ => []

/-- The dependency path is the earlier empty results plus the selected
candidate. Checking those values does not license a different candidate order:
the reversed program is a different query, and the old certificate can still
agree while that program returns another occurrence. -/
theorem firstSuccess_dependency_records_earlier_empties_and_forbids_reorder :
    dependencyReads fallbackWorld [0, 1] = [(0, []), (1, [⟨4, 5⟩])] ∧
      (run fallbackWorld (firstSuccessScan [0, 1])).reads =
        dependencyReads fallbackWorld [0, 1] ∧
      checkReads orderWorldLater (run orderWorld (firstSuccessScan [0, 1])).reads = true ∧
      (run orderWorldLater (firstSuccessScan [1, 0])).answer ≠
        (run orderWorld (firstSuccessScan [0, 1])).answer := by
  decide

theorem atMostOne_rejects_second_equal_payload :
    (run equalPayloadWorld (completeScan [0, 1])).answer = [⟨1, 7⟩, ⟨2, 7⟩] ∧
      (run equalPayloadWorld (completeScan [0, 1])).answer =
        concatenate equalPayloadWorld [0, 1] ∧
      (⟨1, 7⟩ : Occurrence Nat Nat).payload = (⟨2, 7⟩ : Occurrence Nat Nat).payload ∧
      (⟨1, 7⟩ : Occurrence Nat Nat).id ≠ (⟨2, 7⟩ : Occurrence Nat Nat).id ∧
      (run equalPayloadWorld (map atMostOne (completeScan [0, 1]))).answer = false := by
  decide

/-- A later success leaves the once selection in place and falsifies singleton
cardinality. The once prefix still validates; the complete stream does not.
The prefix is not the completeness certificate. -/
theorem once_prefix_is_not_the_completeness_certificate :
    let later := Function.update singletonWorld 1 [⟨2, 7⟩]
    (run singletonWorld (firstSuccessScan [0, 1])).answer =
        (run later (firstSuccessScan [0, 1])).answer ∧
      (run singletonWorld (map atMostOne (completeScan [0, 1]))).answer = true ∧
      (run later (map atMostOne (completeScan [0, 1]))).answer = false ∧
      checkReads later (run singletonWorld (firstSuccessScan [0, 1])).reads = true ∧
      checkReads later (run singletonWorld (completeScan [0, 1])).reads = false ∧
      (run singletonWorld (firstSuccessScan [0, 1])).reads ≠
        (run singletonWorld (completeScan [0, 1])).reads := by
  decide

theorem empty_completion :
    let store : Nat → List (Occurrence Nat Nat) := fun _ => []
    (run store (completeScan [0, 1])).answer = concatenate store [0, 1] ∧
      (run store (completeScan [0, 1])).answer = [] ∧
      (run store (firstSuccessScan [0, 1])).answer = none ∧
      atMostOne ([] : List (Occurrence Nat Nat)) = true ∧
      (run store (completeScan [0, 1])).reads = [(0, []), (1, [])] := by
  decide

theorem earlier_insertion_invalidates_fallback :
    let inserted := Function.update fallbackWorld 0 [⟨9, 1⟩]
    (run fallbackWorld (firstSuccessScan [0, 1])).answer = some ⟨4, 5⟩ ∧
      (run inserted (firstSuccessScan [0, 1])).answer = some ⟨9, 1⟩ ∧
      (run fallbackWorld (firstSuccessScan [0, 1])).reads = [(0, []), (1, [⟨4, 5⟩])] ∧
      checkReads inserted (run fallbackWorld (firstSuccessScan [0, 1])).reads = false := by
  decide

theorem unrelated_later_change_preserves_first :
    let later := Function.update singletonWorld 2 [⟨8, 3⟩]
    (run singletonWorld (firstSuccessScan [0, 1])).answer = some ⟨1, 7⟩ ∧
      (run later (firstSuccessScan [0, 1])).answer = some ⟨1, 7⟩ ∧
      checkReads later (run singletonWorld (firstSuccessScan [0, 1])).reads = true ∧
      (run later (firstSuccessScan [0, 1])).reads =
        (run singletonWorld (firstSuccessScan [0, 1])).reads := by
  decide

theorem retained_none_preserves_and_stale_plan_refuses :
    (pausePrefix fallbackWorld 1 (firstSuccessScan [0, 1])).1 = [(0, [])] ∧
      (run fallbackWorld (pausePrefix fallbackWorld 1 (firstSuccessScan [0, 1])).2).answer =
        (run fallbackWorld (firstSuccessScan [0, 1])).answer ∧
      Retained.resumeValidated fallbackWorld 1 (pausePrefix fallbackWorld 1 (firstSuccessScan [0, 1])) =
        some (Retained.resume fallbackWorld 1
          (pausePrefix fallbackWorld 1 (firstSuccessScan [0, 1]))) ∧
      Retained.resumeValidated (Function.update fallbackWorld 0 [⟨9, 1⟩]) 1
          (pausePrefix fallbackWorld 1 (firstSuccessScan [0, 1])) = none := by
  refine ⟨rfl, (resumed_eq_run_same_store fallbackWorld 1 (firstSuccessScan [0, 1])).1, rfl, rfl⟩

/-- One read of a nonempty candidate closes over that occurrence.
The residual is `pure`, so resumption does not consult the next candidate. -/
theorem retained_success_keeps_first_occurrence :
    (pausePrefix orderWorld 1 (firstSuccessScan [0, 1])).1 =
        [(0, [(⟨1, 7⟩ : Occurrence Nat Nat)])] ∧
      (run orderWorld (pausePrefix orderWorld 1 (firstSuccessScan [0, 1])).2).answer =
        some (⟨1, 7⟩ : Occurrence Nat Nat) ∧
      (run orderWorld (pausePrefix orderWorld 1 (firstSuccessScan [0, 1])).2).reads = [] ∧
      (run orderWorld (firstSuccessScan [1])).answer =
        some (⟨2, 9⟩ : Occurrence Nat Nat) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Equal payloads do not make the captured occurrence the next one. -/
theorem retained_success_keeps_first_identity :
    (run equalPayloadWorld (pausePrefix equalPayloadWorld 1 (firstSuccessScan [0, 1])).2).answer =
        some (⟨1, 7⟩ : Occurrence Nat Nat) ∧
      (run equalPayloadWorld (firstSuccessScan [1])).answer =
        some (⟨2, 7⟩ : Occurrence Nat Nat) ∧
      (⟨1, 7⟩ : Occurrence Nat Nat).payload = (⟨2, 7⟩ : Occurrence Nat Nat).payload ∧
      (⟨1, 7⟩ : Occurrence Nat Nat).id ≠ (⟨2, 7⟩ : Occurrence Nat Nat).id := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide

/-- An empty candidate list pauses as a finished `pure none`, with no reads. -/
theorem retained_empty_is_terminal :
    (pausePrefix (fun _ : Nat => ([] : List (Occurrence Nat Nat))) 1
        (firstSuccessScan ([] : List Nat))).1 = [] ∧
      (run (fun _ : Nat => ([] : List (Occurrence Nat Nat)))
          (pausePrefix (fun _ : Nat => ([] : List (Occurrence Nat Nat))) 1
            (firstSuccessScan ([] : List Nat))).2).answer =
        (none : Option (Occurrence Nat Nat)) ∧
      (run (fun _ : Nat => ([] : List (Occurrence Nat Nat)))
          (pausePrefix (fun _ : Nat => ([] : List (Occurrence Nat Nat))) 1
            (firstSuccessScan ([] : List Nat))).2).reads = [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Changing the selected row invalidates the captured prefix.
The closed residual still holds the original occurrence. -/
theorem changed_selected_row_refuses :
    checkReads (Function.update orderWorld 0 [(⟨9, 7⟩ : Occurrence Nat Nat)])
        (pausePrefix orderWorld 1 (firstSuccessScan [0, 1])).1 = false ∧
      Retained.resumeValidated
          (Function.update orderWorld 0 [(⟨9, 7⟩ : Occurrence Nat Nat)]) 1
          (pausePrefix orderWorld 1 (firstSuccessScan [0, 1])) = none ∧
      (run orderWorld (pausePrefix orderWorld 1 (firstSuccessScan [0, 1])).2).answer =
        some (⟨1, 7⟩ : Occurrence Nat Nat) := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms firstSuccessScan_eq_concatenate_head
#print axioms completeScan_eq_concatenate
#print axioms atMostOne_rejects_second_equal_payload
#print axioms firstSuccess_dependency_records_earlier_empties_and_forbids_reorder
#print axioms retained_success_keeps_first_occurrence
#print axioms retained_success_keeps_first_identity
#print axioms retained_empty_is_terminal
#print axioms changed_selected_row_refuses

end OrderedSelection

end Mettapedia.Machines.ReadOnlyQuery
