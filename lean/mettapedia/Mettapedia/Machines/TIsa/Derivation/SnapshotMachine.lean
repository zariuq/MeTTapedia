import Mettapedia.Machines.TIsa.Derivation.Instructions

/-!
# Shared control for a prepared firing

A schedule proposes a finite population at the current snapshot. Its
candidates can have different data and proof obligations, but the
control only needs two continuations: try the next candidate, or fund
and publish a completed one. Preparation and checks do not move the
world. This same evaluator, CPS form, and instruction loop can drive
one occurrence firing or any validated batch.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SnapshotMachine

universe u v t

/-- The data present at the three boundaries of selection. -/
structure Phases (World : Type u) where
  Candidate : World → Type v
  Pending : World → Type v
  Accepted : World → Type v

structure Schedule {World : Type u} (phases : Phases World) where
  options : (before : World) → List (phases.Candidate before)
  prepare : {before : World} → phases.Candidate before → Option (phases.Pending before)
  verify : {before : World} → phases.Pending before → Option (phases.Accepted before)
  publish : {before : World} → phases.Accepted before → World

variable {World : Type u} {phases : Phases World} (schedule : Schedule phases)

def candidateResult {before : World} (candidate : phases.Candidate before) : Option (phases.Accepted before) :=
  (schedule.prepare candidate).bind schedule.verify

def search (before : World) : Option (phases.Accepted before) :=
  (schedule.options before).findSome? (candidateResult schedule)

inductive Outcome (World : Type u) where
  | quiescent (world : World)
  | exhausted (world : World)

def run : ℕ → World → Outcome World
  | 0, before => match search schedule before with
    | none => .quiescent before
    | some _ => .exhausted before
  | fuel + 1, before => match search schedule before with
    | none => .quiescent before
    | some success => run fuel (schedule.publish success)

def afterSearch (before : World) (fuel : ℕ) :
    Option (phases.Accepted before) → Outcome World
  | none => .quiescent before
  | some success => match fuel with
    | 0 => .exhausted before
    | fuel + 1 => run schedule fuel (schedule.publish success)

theorem run_eq_afterSearch (fuel : ℕ) (before : World) :
    run schedule fuel before = afterSearch schedule before fuel (search schedule before) := by
  cases fuel <;> cases found : search schedule before <;> simp [run, afterSearch, found]

def searchK {R : Type*} {before : World}
    (win : phases.Accepted before → R) (lose : Unit → R) : List (phases.Candidate before) → R
  | [] => lose ()
  | attempt :: rest => match schedule.prepare attempt with
    | none => searchK win lose rest
    | some pending => match schedule.verify pending with
      | none => searchK win lose rest
      | some success => win success

theorem searchK_eq {R : Type*} {before : World}
    (win : phases.Accepted before → R) (lose : Unit → R) (candidates : List (phases.Candidate before)) :
    searchK schedule win lose candidates = (candidates.findSome? (candidateResult schedule)).elim (lose ()) win := by
  induction candidates with
  | nil => rfl
  | cons attempt rest ih =>
    cases resolved : schedule.prepare attempt with
    | none => simpa [searchK, List.findSome?_cons, candidateResult, resolved] using ih
    | some pending =>
      cases checked : schedule.verify pending with
      | none => simpa [searchK, List.findSome?_cons, candidateResult, resolved, checked] using ih
      | some success => simp [searchK, candidateResult, resolved, checked]

def runK {R : Type*} (finish : Outcome World → R) : ℕ → World → R
  | 0, before => searchK schedule (fun _ => finish (.exhausted before))
    (fun _ => finish (.quiescent before)) (schedule.options before)
  | fuel + 1, before => searchK schedule (fun success => runK finish fuel (schedule.publish success))
    (fun _ => finish (.quiescent before)) (schedule.options before)

theorem runK_eq {R : Type*} (finish : Outcome World → R) (fuel : ℕ)
    (before : World) : runK schedule finish fuel before = finish (run schedule fuel before) := by
  induction fuel generalizing before with
  | zero =>
    rw [runK, searchK_eq]
    change (search schedule before).elim _ _ = _
    cases found : search schedule before <;> simp [run, found]
  | succ fuel ih =>
    rw [runK, searchK_eq]
    change (search schedule before).elim _ _ = _
    cases found : search schedule before <;> simp [run, found, ih]

inductive Config (phases : Phases World) where
  | entry (fuel : ℕ) (world : World)
  | scan (fuel : ℕ) (world : World) (rest : List (phases.Candidate world))
  | check (fuel : ℕ) (world : World) (meaning : phases.Pending world)
      (rest : List (phases.Candidate world))
  | fund (fuel : ℕ) (world : World) (success : phases.Accepted world)
  | publication (fuel : ℕ) (world : World) (success : phases.Accepted world)
  | halt (outcome : Outcome World)

def current {T : Type t} : Config phases → Option (Instruction T)
  | .entry .. => some .search
  | .scan _ _ [] => some .quiesce
  | .scan _ _ (_ :: _) => some .candidate
  | .check .. => some .checkSolution
  | .fund .. => some .fund
  | .publication .. => some .publish
  | .halt .. => none

def execute {T : Type t} : Instruction T → Config phases → Option (Config phases)
  | .search, .entry fuel world => some (.scan fuel world (schedule.options world))
  | .quiesce, .scan _ world [] => some (.halt (.quiescent world))
  | .candidate, .scan fuel world (attempt :: rest) => some (match schedule.prepare attempt with
    | none => .scan fuel world rest
    | some pending => .check fuel world pending rest)
  | .checkSolution, .check fuel world pending rest => some (match schedule.verify pending with
    | none => .scan fuel world rest
    | some success => .fund fuel world success)
  | .fund, .fund 0 world _ => some (.halt (.exhausted world))
  | .fund, .fund (fuel + 1) world success => some (.publication fuel world success)
  | .publish, .publication fuel _ success => some (.entry fuel (schedule.publish success))
  | _, _ => none

def transition (config : Config phases) : Option (Config phases) :=
  (current (T := Unit) config).bind fun instruction => execute schedule instruction config

abbrev Runs := Relation.ReflTransGen fun first later => transition schedule first = some later

def scanResult (phases : Phases World) (fuel : ℕ) (before : World) :
    Option (phases.Accepted before) → Config phases
  | none => .halt (.quiescent before)
  | some success => .fund fuel before success

def meaning : Config phases → Outcome World
  | .entry fuel world => run schedule fuel world
  | .scan fuel world rest => afterSearch schedule world fuel (rest.findSome? (candidateResult schedule))
  | .check fuel world pending rest =>
    afterSearch schedule world fuel ((schedule.verify pending).or (rest.findSome? (candidateResult schedule)))
  | .fund fuel world success => afterSearch schedule world fuel (some success)
  | .publication fuel _ success => run schedule fuel (schedule.publish success)
  | .halt outcome => outcome

theorem transition_preserves {first later : Config phases}
    (moved : transition schedule first = some later) : meaning schedule first = meaning schedule later := by
  cases first with
  | entry fuel world =>
    cases moved
    exact run_eq_afterSearch schedule fuel world
  | scan fuel world rest =>
    cases rest with
    | nil => cases moved; rfl
    | cons attempt rest =>
      cases resolved : schedule.prepare attempt with
      | none =>
        obtain rfl := Option.some.inj (by simpa only [transition, current, execute, Option.bind_some, resolved] using moved)
        simp [meaning, candidateResult, resolved]
      | some pending =>
        obtain rfl := Option.some.inj (by simpa only [transition, current, execute, Option.bind_some, resolved] using moved)
        cases gate : schedule.verify pending <;> simp [meaning, candidateResult, resolved, gate]
  | check fuel world pending rest =>
    cases gate : schedule.verify pending with
    | none =>
      obtain rfl := Option.some.inj (by simpa only [transition, current, execute, Option.bind_some, gate] using moved)
      simp [meaning, gate]
    | some success =>
      obtain rfl := Option.some.inj (by simpa only [transition, current, execute, Option.bind_some, gate] using moved)
      simp [meaning, gate]
  | fund fuel world success =>
    cases fuel <;> cases moved <;> rfl
  | publication fuel _ success => cases moved; rfl
  | halt _ => cases moved

theorem scan_reaches (fuel : ℕ) (before : World) (queries : List (phases.Candidate before)) :
    Runs schedule (.scan fuel before queries) (scanResult phases fuel before (queries.findSome? (candidateResult schedule))) := by
  induction queries with
  | nil => exact .single rfl
  | cons attempt rest ih =>
    cases found : schedule.prepare attempt with
    | none =>
      rw [List.findSome?_cons_of_isNone (show (candidateResult schedule attempt).isNone by simp [candidateResult, found])]
      exact .head (by simp [transition, current, execute, found]) ih
    | some pending =>
      have gate : Runs schedule (.scan fuel before (attempt :: rest)) (.check fuel before pending rest) :=
        .single (by simp [transition, current, execute, found])
      cases checked : schedule.verify pending with
      | none =>
        rw [List.findSome?_cons_of_isNone (show (candidateResult schedule attempt).isNone by simp [candidateResult, found, checked])]
        exact gate.trans (.head (by simp [transition, current, execute, checked]) ih)
      | some success =>
        simp only [List.findSome?_cons, candidateResult, found, Option.bind_some, checked, scanResult]
        exact gate.tail (by simp [transition, current, execute, checked])

theorem complete_run (fuel : ℕ) (before : World) :
    Runs schedule (.entry fuel before) (.halt (run schedule fuel before)) := by
  have openSearch (n : ℕ) (world : World) :
      Runs schedule (.entry n world) (scanResult phases n world (search schedule world)) :=
    .head rfl (scan_reaches schedule n world (schedule.options world))
  induction fuel generalizing before with
  | zero =>
    cases found : search schedule before with
    | none => simpa [scanResult, run, found] using (openSearch 0 before)
    | some success =>
      exact (openSearch 0 before).trans (by
        simp only [found, scanResult, run]
        exact .single rfl)
  | succ fuel ih =>
    cases found : search schedule before with
    | none => simpa [scanResult, run, found] using (openSearch (fuel + 1) before)
    | some success =>
      apply (openSearch (fuel + 1) before).trans
      simp only [found, scanResult, run]
      exact .head rfl (.head rfl (ih (schedule.publish success)))

theorem machine_run_iff (fuel : ℕ) (before : World) (outcome : Outcome World) :
    Runs schedule (.entry fuel before) (.halt outcome) ↔ outcome = run schedule fuel before := by
  constructor
  · intro ran
    have invariant {first later : Config phases} (path : Runs schedule first later) :
        meaning schedule first = meaning schedule later := by
      induction path with
      | refl => rfl
      | tail _ edge ih => exact ih.trans (transition_preserves schedule edge)
    exact (invariant ran).symm
  · rintro rfl
    exact complete_run schedule fuel before

def Outcome.world : Outcome World → World
  | .quiescent world | .exhausted world => world

def Config.world : Config phases → World
  | .entry _ world | .scan _ world _ | .check _ world _ _ | .fund _ world _ |
      .publication _ world _ => world
  | .halt result => result.world

/-- Only publication can change the snapshot projected from control. -/
theorem world_changed {first later : Config phases}
    (moved : transition schedule first = some later) (changed : later.world ≠ first.world) :
    ∃ (fuel : ℕ) (before : World) (answer : phases.Accepted before),
      first = .publication fuel before answer ∧ later = .entry fuel (schedule.publish answer) := by
  cases first with
  | entry fuel world => cases moved; exact (changed rfl).elim
  | scan fuel world rest =>
    cases rest with
    | nil => cases moved; exact (changed rfl).elim
    | cons trial rest =>
      cases found : schedule.prepare trial <;>
        obtain rfl := Option.some.inj (by simpa only [transition, current, execute, Option.bind_some, found] using moved)
      all_goals exact (changed rfl).elim
  | check fuel world pending rest =>
    cases found : schedule.verify pending <;>
      obtain rfl := Option.some.inj (by simpa only [transition, current, execute, Option.bind_some, found] using moved)
    all_goals exact (changed rfl).elim
  | fund fuel world accepted =>
    cases fuel <;> cases moved <;> exact (changed rfl).elim
  | publication fuel world accepted => cases moved; exact ⟨fuel, world, accepted, rfl, rfl⟩
  | halt _ => cases moved

inductive LegalRun (possible : World → Prop) (step : World → World → Prop) : ℕ → World → Outcome World → Prop
  | quiet {fuel before} : ¬possible before → LegalRun possible step fuel before (.quiescent before)
  | budget {before} : possible before → LegalRun possible step 0 before (.exhausted before)
  | commit {fuel before after result} : step before after → LegalRun possible step fuel after result →
      LegalRun possible step (fuel + 1) before result

theorem run_legal {possible : World → Prop} {step : World → World → Prop}
    (absence : ∀ before, search schedule before = none → ¬possible before)
    (entry : ∀ {before} {accepted : phases.Accepted before},
      search schedule before = some accepted → possible before ∧ step before (schedule.publish accepted))
    (fuel : ℕ) (before : World) : LegalRun possible step fuel before (run schedule fuel before) := by
  induction fuel generalizing before with
  | zero =>
    cases found : search schedule before with
    | none => simpa [run, found] using LegalRun.quiet (fuel := 0) (step := step) (absence before found)
    | some result => simpa [run, found] using LegalRun.budget (step := step) (entry found).1
  | succ fuel ih =>
    cases found : search schedule before with
    | none => simpa [run, found] using LegalRun.quiet (fuel := fuel + 1) (step := step) (absence before found)
    | some result => simpa [run, found] using LegalRun.commit (entry found).2 (ih (schedule.publish result))
end Mettapedia.Machines.TIsa.Derivation.SnapshotMachine
