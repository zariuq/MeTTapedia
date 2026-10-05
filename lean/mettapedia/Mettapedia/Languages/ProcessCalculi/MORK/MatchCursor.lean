import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.GSLT.LanguageDef.NativeControlCursor

/-!
# Retained structural matching work

The finite MORK matcher is executed by an explicit stack of atom and list
meetings. A poll opens one expression, takes one pair from a list, or performs
one variable/rigid comparison. It does not finish a nested structural match
before returning its residual. The independent recursive `matchAtom` remains
the reference, including its substitution order and repeated-variable checks.

Variable lookup, captured-value equality and binding are atomic primitives of
this fragment. Their byte/CPU costs are not bounded by a stack-item grant.
This is one-way finite matching, not CeTTa's bidirectional, cyclic or
epoch-aware unifier. Arena ownership, source revisions and the implementations
of those primitives remain separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MatchCursor

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull collect)

inductive Job where
  | atom (pattern concrete : Atom)
  | atoms (patterns concretes : List Atom)
  deriving Repr

/-- `none` is an exhausted matcher; a present state retains both the refined
substitution and every unfinished structural meeting. -/
abbrev State := Option (Subst × List Job)

def start (substitution : Subst) (pattern concrete : Atom) : State :=
  some (substitution, [.atom pattern concrete])

def jobResult (substitution : Subst) : Job → Option Subst
  | .atom pattern concrete => matchAtom substitution pattern concrete
  | .atoms patterns concretes => matchAtom.matchAtomList substitution patterns concretes

/-- This reference composes the existing recursive matcher over unfinished
jobs. The running cursor does not compute it. -/
def jobsResult : List Job → Subst → Option Subst
  | [], substitution => some substitution
  | job :: rest, substitution =>
      (jobResult substitution job).bind (jobsResult rest)

theorem jobsResult_append (first later : List Job) (substitution : Subst) :
    jobsResult (first ++ later) substitution =
      (jobsResult first substitution).bind (jobsResult later) := by
  induction first generalizing substitution with
  | nil => rfl
  | cons job rest ih =>
      simp only [List.cons_append, jobsResult, ih, Option.bind_assoc]

/-- One local transition returns replacement jobs, rather than recursively
processing them. Non-expression cases reuse the canonical atomic primitive. -/
def advanceJob (substitution : Subst) : Job → Option (Subst × List Job)
  | .atom (.expression patterns) (.expression concretes) =>
      some (substitution, [.atoms patterns concretes])
  | .atom pattern concrete =>
      (matchAtom substitution pattern concrete).map (fun next => (next, []))
  | .atoms [] [] => some (substitution, [])
  | .atoms (pattern :: patterns) (concrete :: concretes) =>
      some (substitution, [.atom pattern concrete, .atoms patterns concretes])
  | .atoms _ _ => none

private theorem atomic_replacement (result : Option Subst) :
    (result.map (fun next => (next, ([] : List Job)))).bind
      (fun next => jobsResult next.2 next.1) = result := by
  cases result <;> rfl

/-- Decomposition agrees with the independently recursive matcher. -/
theorem advanceJob_result (substitution : Subst) (job : Job) :
    (advanceJob substitution job).bind (fun next => jobsResult next.2 next.1) =
      jobResult substitution job := by
  cases job with
  | atom pattern concrete =>
      cases pattern <;> cases concrete <;>
        first
        | exact atomic_replacement _
        | simp [advanceJob, jobsResult, jobResult, matchAtom]
  | atoms patterns concretes =>
      cases patterns with
      | nil => cases concretes <;> rfl
      | cons pattern patterns =>
          cases concretes with
          | nil => rfl
          | cons concrete concretes =>
              cases matched : matchAtom substitution pattern concrete <;>
                simp [advanceJob, jobsResult, jobResult, matchAtom.matchAtomList, matched]

theorem advanceJob_rest (substitution : Subst) (job : Job) (rest : List Job) :
    (advanceJob substitution job).bind
        (fun next => jobsResult (next.2 ++ rest) next.1) =
      jobsResult (job :: rest) substitution := by
  simp_rw [jobsResult_append]
  rw [← Option.bind_assoc, advanceJob_result]
  rfl

def pull : State → Pull State Subst
  | none => .done
  | some (substitution, []) => .yield substitution none
  | some (substitution, job :: rest) =>
      .suspend ((advanceJob substitution job).map
        (fun next => (next.1, next.2 ++ rest)))

def residualAnswers : State → List Subst
  | none => []
  | some (substitution, jobs) => (jobsResult jobs substitution).toList

/-- A structural atom match has at most one refinement. Its successful reply
contains an already exhausted local residual, unlike a general query stream. -/
theorem yield_residual (state : State) (substitution : Subst) (next : State)
    (emitted : pull state = .yield substitution next) : next = none := by
  cases state with
  | none => simp [pull] at emitted
  | some live =>
      rcases live with ⟨current, jobs⟩
      cases jobs with
      | nil => simpa [pull] using (congrArg (fun reply => match reply with
          | .yield _ rest => rest
          | _ => next) emitted).symm
      | cons job rest => simp [pull] at emitted

theorem pull_answers (state : State) :
    match pull state with
    | .done => residualAnswers state = []
    | .suspend next => residualAnswers state = residualAnswers next
    | .yield substitution next =>
        residualAnswers state = substitution :: residualAnswers next := by
  cases state with
  | none => rfl
  | some live =>
      rcases live with ⟨substitution, jobs⟩
      cases jobs with
      | nil => rfl
      | cons job rest =>
          have conserved := advanceJob_rest substitution job rest
          cases moved : advanceJob substitution job with
          | none =>
              simp only [moved, Option.bind_none] at conserved
              simp [pull, moved, residualAnswers, ← conserved]
          | some next =>
              simp only [moved, Option.bind_some] at conserved
              simp [pull, moved, residualAnswers, ← conserved]

/-- Structural stack work. Captured-value equality and substitution lookup
retain their separate primitive complexity. -/
noncomputable def jobCost : Job → Nat
  | .atom pattern concrete => 1 + sizeOf pattern + sizeOf concrete
  | .atoms patterns concretes => 1 + sizeOf patterns + sizeOf concretes

noncomputable def jobsCost (jobs : List Job) : Nat := (jobs.map jobCost).sum

noncomputable def remainingCost : State → Nat
  | none => 0
  | some (_, jobs) => 1 + jobsCost jobs

theorem advanceJob_cost (substitution : Subst) (job : Job)
    (next : Subst × List Job) (moved : advanceJob substitution job = some next) :
    jobsCost next.2 < jobCost job := by
  cases job with
  | atom pattern concrete =>
      cases pattern <;> cases concrete <;>
        simp [advanceJob] at moved
      all_goals first
        | (subst next; simp [jobsCost, jobCost]; all_goals omega)
        | (obtain ⟨nextSubstitution, _, rfl⟩ := moved
           simp [jobsCost, jobCost])
  | atoms patterns concretes =>
      cases patterns <;> cases concretes <;>
        simp [advanceJob] at moved <;>
        (subst next; simp [jobsCost, jobCost]; all_goals omega)

theorem pull_cost (state : State) :
    match pull state with
    | .done => remainingCost state = 0
    | .suspend next => remainingCost next < remainingCost state
    | .yield _ next => remainingCost next < remainingCost state := by
  cases state with
  | none => rfl
  | some live =>
      rcases live with ⟨substitution, jobs⟩
      cases jobs with
      | nil => simp [pull, remainingCost, jobsCost]
      | cons job rest =>
          cases moved : advanceJob substitution job with
          | none => simp [pull, moved, remainingCost]
          | some next =>
              have smaller := advanceJob_cost substitution job next moved
              simp only [pull, moved, Option.map_some, remainingCost, jobsCost,
                List.map_append, List.sum_append, List.map_cons, List.sum_cons]
              unfold jobsCost at smaller
              omega

theorem collect_sound (fuel : Nat) (state : State) (answers : List Subst)
    (completed : collect pull fuel state = some answers) :
    answers = residualAnswers state :=
  NativeControlCursor.collect_sound pull residualAnswers
    (fun state => by cases moved : pull state <;> simpa only [moved] using pull_answers state)
    fuel state answers completed

theorem collect_complete (fuel : Nat) (state : State)
    (enough : remainingCost state < fuel) :
    collect pull fuel state = some (residualAnswers state) :=
  NativeControlCursor.collect_complete pull residualAnswers
    (fun state => by cases moved : pull state <;> simpa only [moved] using pull_answers state)
    remainingCost
    (fun state => by cases moved : pull state <;> simpa only [moved] using pull_cost state)
    fuel state enough

/-- Exact completed binding list, preserving the substitution's own order. -/
theorem start_answers (substitution : Subst) (pattern concrete : Atom) :
    residualAnswers (start substitution pattern concrete) =
      (matchAtom substitution pattern concrete).toList := by
  simp [residualAnswers, start, jobsResult, jobResult]

theorem completed_match_iff (substitution : Subst) (pattern concrete : Atom)
    (fuel : Nat) (answers : List Subst)
    (completed : collect pull fuel (start substitution pattern concrete) = some answers)
    (next : Subst) :
    next ∈ answers ↔ MatchAtomRel substitution pattern concrete next := by
  rw [collect_sound fuel _ answers completed, start_answers, Option.mem_toList]
  exact matchAtom_iff

theorem finite_completion (substitution : Subst) (pattern concrete : Atom) :
    collect pull (remainingCost (start substitution pattern concrete) + 1)
      (start substitution pattern concrete) =
      some ((matchAtom substitution pattern concrete).toList) := by
  rw [collect_complete _ _ (Nat.lt_succ_self _), start_answers]

/-- The common cursor retains the actual matching stack and substitution
through every grant; it does not restart the reference matcher. -/
theorem pause_resume_exact (first later : Nat) (state : State) (reversed : List Subst) :
    Mettapedia.Machines.Cursor.advance (NativeControlCursor.provider pull)
      (NativeControlCursor.client Subst) (fun _ _ => 1) (first + later)
      (NativeControlCursor.packet pull state reversed) =
    Mettapedia.Machines.Cursor.resume (NativeControlCursor.provider pull)
      (NativeControlCursor.client Subst) (fun _ _ => 1) later
      (Mettapedia.Machines.Cursor.advance (NativeControlCursor.provider pull)
        (NativeControlCursor.client Subst) (fun _ _ => 1) first
        (NativeControlCursor.packet pull state reversed)) :=
  NativeControlCursor.chunk_exact _ _ _ _ _

namespace Controls

def repeated : Atom := .expression [.symbol "pair", .var "x", .var "x"]
def equalFields : Atom := .expression [.symbol "pair", .symbol "a", .symbol "a"]
def crossedFields : Atom := .expression [.symbol "pair", .symbol "a", .symbol "b"]

theorem expression_opening_retains_unfinished_match :
    pull (start [] repeated equalFields) =
      .suspend (some ([], [.atoms
        [.symbol "pair", .var "x", .var "x"]
        [.symbol "pair", .symbol "a", .symbol "a"]])) := rfl

theorem first_grant_cannot_publish_nested_result :
    collect pull 1 (start [] repeated equalFields) = none := rfl

theorem repeated_variable_keeps_one_binding :
    collect pull 32 (start [] repeated equalFields) =
      some [[("x", .symbol "a")]] := by decide

theorem crossed_fields_are_refuted :
    collect pull 32 (start [] repeated crossedFields) = some [] := by decide

theorem arity_mismatch_is_refuted :
    collect pull 32 (start [] (.expression [.var "x"])
      (.expression [.symbol "a", .symbol "b"])) = some [] := by decide

theorem zero_allowance_retains_every_job :
    Mettapedia.Machines.Cursor.advance (NativeControlCursor.provider pull)
      (NativeControlCursor.client Subst) (fun _ _ => 1) 0
      (NativeControlCursor.packet pull (start [] repeated equalFields) []) =
    (0, .paused (NativeControlCursor.packet pull (start [] repeated equalFields) [])) := rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.MORK.MatchCursor
