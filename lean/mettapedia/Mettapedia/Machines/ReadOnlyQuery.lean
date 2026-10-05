import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mettapedia.Logic.ArrayInvariants.UpdateTrace

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

/-- Every read, including an absent lookup, must retain its observed value. -/
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

def map (f : Answer → Other) (program : Program Key Value Answer) :
    Program Key Value Other := bind program fun answer => .pure (f answer)

theorem run_map (store : Key → Value) (program : Program Key Value Answer)
    (f : Answer → Other) :
    run store (map f program) =
      ⟨f (run store program).answer, (run store program).reads⟩ := by
  simp [map, run_bind, run]

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
def absenceQuery : Program Nat (Option Nat) Bool :=
  .read 4 fun value => .pure value.isNone

theorem negative_lookup_must_be_recorded :
    (run (fun _ => none) absenceQuery).reads = [(4, none)] ∧
      checkReads (Function.update (fun _ => none) 4 (some 9))
        (run (fun _ => none) absenceQuery).reads = false := by
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

end Controls

end Mettapedia.Machines.ReadOnlyQuery
