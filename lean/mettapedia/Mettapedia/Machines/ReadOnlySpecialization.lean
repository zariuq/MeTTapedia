import Mettapedia.Machines.RuntimePlumbing.DependencyStamps

/-!
# Driving known prefixes of adaptive reads

Only reads selected by the static policy are driven. The first dynamic read
and all its possible continuations remain in the original query language.
Driving records an ordered dependency prefix, including absent values. At
entry the full prefix must still agree, either by value or by a sound stamp
check. The theorem retains the semantic read trace as well as the answer.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlySpecialization

open ReadOnlyQuery

universe u v w

variable {Key : Type u} {Value : Type v} {Answer : Type w}

/-- Restore the dependencies discharged by driving before reporting the
remaining query's observation. -/
def observeSuffix (captured : Reads Key Value) (suffix : Program Key Value Answer)
    (memory : Key → Value) : Observation Key Value Answer :=
  let result := run memory suffix
  ⟨result.answer, captured ++ result.reads⟩

structure Residual (source : Program Key Value Answer) where
  reads : Reads Key Value
  suffix : Program Key Value Answer
  exactOn : ∀ memory, Agrees memory reads →
    observeSuffix reads suffix memory = run memory source

namespace Residual

def keep (source : Program Key Value Answer) : Residual source where
  reads := []
  suffix := source
  exactOn := by
    intro memory _
    cases h : run memory source
    simp [observeSuffix, h]

def pull {key : Key} {next : Value → Program Key Value Answer} {value : Value}
    (rest : Residual (next value)) : Residual (.read key next) where
  reads := (key, value) :: rest.reads
  suffix := rest.suffix
  exactOn := by
    intro memory agrees
    have here : memory key = value := agrees (key, value) (by simp)
    have tail : Agrees memory rest.reads :=
      fun observed member => agrees observed (List.mem_cons_of_mem _ member)
    have exactTail := rest.exactOn memory tail
    unfold observeSuffix at exactTail ⊢
    simp only [run, here, List.cons_append]
    rw [← exactTail]

/-- Validate the captured prefix before executing the suffix. -/
def tryRun [DecidableEq Value] {source : Program Key Value Answer}
    (plan : Residual source) (memory : Key → Value) : Option (Observation Key Value Answer) :=
  if checkReads memory plan.reads then some (observeSuffix plan.reads plan.suffix memory)
  else none

theorem tryRun_sound [DecidableEq Value] {source : Program Key Value Answer}
    (plan : Residual source) (memory : Key → Value) {result : Observation Key Value Answer}
    (accepted : plan.tryRun memory = some result) : result = run memory source := by
  unfold tryRun at accepted
  split at accepted
  · rename_i valid
    cases accepted
    exact plan.exactOn memory ((checkReads_iff _ _).mp valid)
  · cases accepted

end Residual

/-- Reconstruct a residual from an ordered capture. At each read the
capture must name the actual next key. Value agreement is checked at entry. -/
def restore [DecidableEq Key] :
    (captured : Reads Key Value) → (source : Program Key Value Answer) → Option (Residual source)
  | [], source => some (.keep source)
  | _ :: _, .pure _ => none
  | (key, value) :: rest, .read expected next =>
    if key = expected then (restore rest (next value)).map Residual.pull
    else none

theorem restore_records_reads [DecidableEq Key] (captured : Reads Key Value)
    (source : Program Key Value Answer) (plan : Residual source)
    (accepted : restore captured source = some plan) : plan.reads = captured := by
  induction captured generalizing source with
  | nil =>
    cases accepted
    rfl
  | cons observed rest ih =>
    obtain ⟨key, value⟩ := observed
    cases source with
    | pure answer => cases accepted
    | read expected next =>
      by_cases same : key = expected
      · subst expected
        cases replayed : restore rest (next value) with
        | none => simp [restore, replayed] at accepted
        | some actual =>
          simp [restore, replayed] at accepted
          subst plan
          exact congrArg ((key, value) :: ·) (ih _ _ replayed)
      · simp [restore, same] at accepted

/-- Drive at most the supplied number of static reads. Budget exhaustion
leaves a continuation with its exact arguments. -/
def drive (static : Key → Bool) (memory : Key → Value) :
    (fuel : Nat) → (source : Program Key Value Answer) → Residual source
  | 0, source => .keep source
  | _ + 1, .pure answer => .keep (.pure answer)
  | fuel + 1, .read key next =>
    if static key then (drive static memory fuel (next (memory key))).pull
    else .keep (.read key next)

theorem restore_drive [DecidableEq Key] (static : Key → Bool) (memory : Key → Value)
    (fuel : Nat) (source : Program Key Value Answer) :
    let plan := drive static memory fuel source
    restore plan.reads source = some plan := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases source with
    | pure answer => rfl
    | read key next =>
      by_cases known : static key = true
      · simp only [drive, known, if_true]
        change restore ((key, memory key) :: (drive static memory fuel (next (memory key))).reads)
          (.read key next) = _
        simp [restore, ih (next (memory key))]
      · simp [drive, known, Residual.keep, restore]

theorem drive_agrees (static : Key → Bool) (memory : Key → Value) (fuel : Nat)
    (source : Program Key Value Answer) : Agrees memory (drive static memory fuel source).reads := by
  induction fuel generalizing source with
  | zero => simp [drive, Residual.keep, Agrees]
  | succ fuel ih =>
    cases source with
    | pure answer => simp [drive, Residual.keep, Agrees]
    | read key next =>
      by_cases known : static key = true
      · simp only [drive, known, if_true, Residual.pull]
        intro observed member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · exact ih (next (memory key)) observed member
      · simp [drive, known, Residual.keep, Agrees]

/-- The footprint is a prefix of the reference read trace. The budget and
the first live read can each cut that prefix short. -/
theorem drive_reads_from_source (static : Key → Bool) (memory : Key → Value) (fuel : Nat)
    (source : Program Key Value Answer) :
    (drive static memory fuel source).reads =
      ((run memory source).reads.take fuel).takeWhile (fun read => static read.1) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases source with
    | pure answer => rfl
    | read key next =>
      by_cases known : static key = true
      · simp [drive, known, Residual.pull, run, ih]
      · simp [drive, known, Residual.keep, run]

theorem drive_reads_le (static : Key → Bool) (memory : Key → Value) (fuel : Nat)
    (source : Program Key Value Answer) : (drive static memory fuel source).reads.length ≤ fuel := by
  induction fuel generalizing source with
  | zero => simp [drive, Residual.keep]
  | succ fuel ih =>
    cases source with
    | pure answer => simp [drive, Residual.keep]
    | read key next =>
      by_cases known : static key = true
      · simpa [drive, known, Residual.pull] using ih (next (memory key))
      · simp [drive, known, Residual.keep]

section Stamps

open RuntimePlumbing.DependencyStamps

variable {K V A : Type}

/-- With a trusted advancing memory, a stamp check can discharge the same
prefix obligation without comparing the stored values. -/
theorem drive_sound_of_stamps (static : K → Bool) (before after : Memory K V)
    (fuel : Nat) (source : Program K V A) (advances : Advances before after)
    (valid : check before after (drive static before.value fuel source).reads = true) :
    observeSuffix (drive static before.value fuel source).reads
      (drive static before.value fuel source).suffix after.value = run after.value source := by
  apply (drive static before.value fuel source).exactOn
  intro observed member
  have same := (check_iff _ _ _).mp valid observed member
  exact ((advances observed.1).2 same).symm.trans
    (drive_agrees static before.value fuel source observed member)

end Stamps

end Mettapedia.Machines.ReadOnlySpecialization
