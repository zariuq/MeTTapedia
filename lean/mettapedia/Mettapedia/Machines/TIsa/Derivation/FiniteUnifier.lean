import Mettapedia.Logic.LP.TotalUnificationStructural

/-!
# A resumable finite-term unifier

The work list and the elimination trail make the continuation
of Martelli--Montanari explicit. The trail is newest first:
readback composes the solution of the remaining problem with
each saved elimination, in turn. Fuel limits only how much of
the machine is run. It is never evidence of inconsistency.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.FiniteUnifier

open Mettapedia.Logic.LP

universe u p
variable {σ : LPSignature.{u,u,p,u}}

abbrev Equations (σ : LPSignature) := List (Term σ × Term σ)
abbrev Trail (σ : LPSignature) := List (σ.vars × Term σ)

inductive Conflict where
  | heads
  | occurs
  deriving DecidableEq, Repr

inductive Action (σ : LPSignature) where
  | discard
  | eliminate (name : σ.vars) (term : Term σ)
  | decompose (children : Equations σ)
  | refuse (reason : Conflict)

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def action : Term σ → Term σ → Action σ
  | .var v, .var w => if v = w then .discard else .eliminate v (.var w)
  | .var v, .const atom => .eliminate v (.const atom)
  | .var v, .app key args =>
    if (Term.app key args).occursIn v then .refuse .occurs else .eliminate v (.app key args)
  | .const atom, .var v => .eliminate v (.const atom)
  | .const left, .const right => if left = right then .discard else .refuse .heads
  | .const _, .app _ _ => .refuse .heads
  | .app key args, .var v =>
    if (Term.app key args).occursIn v then .refuse .occurs else .eliminate v (.app key args)
  | .app _ _, .const _ => .refuse .heads
  | .app key args, .app other more =>
    if equal : key = other then .decompose (finPairsToList args (equal ▸ more)) else .refuse .heads

def interpretAction (rest : Equations σ) : Action σ → Option (Subst σ)
  | .discard => unifyTotal rest
  | .eliminate v term =>
    let binding := Subst.single v term
    (unifyTotal (binding.applyEqs rest)).map (· ∘ₛ binding)
  | .decompose more => unifyTotal (more ++ rest)
  | .refuse _ => none

theorem action_exact (left right : Term σ) (rest : Equations σ) :
    interpretAction rest (action left right) = unifyTotal ((left, right) :: rest) := by
  cases left <;> cases right <;> rw [unifyTotal] <;> (try simp only [action])
  all_goals try (intro _ impossible; cases impossible)
  case var.var v w =>
    by_cases same : v = w
    · simp [same, interpretAction]
    · rw [if_neg same, if_neg same, interpretAction]
      cases unifyTotal ((Subst.single v (.var w)).applyEqs rest) <;> rfl
  case var.const v c =>
    simp only [Term.occursIn, Bool.false_eq_true, if_false, interpretAction]
    cases unifyTotal ((Subst.single v (.const c)).applyEqs rest) <;> rfl
  case var.app v f args =>
    cases cyclic : (Term.app f args).occursIn v
    · simp only [Bool.false_eq_true, if_false, interpretAction]
      cases unifyTotal ((Subst.single v (.app f args)).applyEqs rest) <;> rfl
    · simp [interpretAction]
  case const.var c v =>
    simp only [interpretAction]
    cases unifyTotal ((Subst.single v (.const c)).applyEqs rest) <;> rfl
  case const.const left right =>
    by_cases same : left = right <;> simp [same, interpretAction]
  case const.app c f args => rfl
  case app.var f args v =>
    cases cyclic : (Term.app f args).occursIn v
    · simp only [Bool.false_eq_true, if_false, interpretAction]
      cases unifyTotal ((Subst.single v (.app f args)).applyEqs rest) <;> rfl
    · simp [interpretAction]
  case app.const f args c => rfl
  case app.app f args g more =>
    by_cases same : f = g <;> simp [same, interpretAction]

def readTrail (suffix : Subst σ) (trail : Trail σ) : Subst σ :=
  trail.foldl (fun solution binding => solution ∘ₛ Subst.single binding.1 binding.2) suffix

structure Work (σ : LPSignature) where
  pending : Equations σ
  trail : Trail σ

inductive Configuration (σ : LPSignature) where
  | working (work : Work σ)
  | solved (trail : Trail σ)
  | inconsistent (reason : Conflict)

def start (equations : Equations σ) : Configuration σ := .working ⟨equations, []⟩

def advance (work : Work σ) : Configuration σ :=
  match work.pending with
  | [] => .solved work.trail
  | (left, right) :: rest =>
    match action left right with
    | .discard => .working {work with pending := rest}
    | .eliminate v term => .working ⟨(Subst.single v term).applyEqs rest, (v, term) :: work.trail⟩
    | .decompose more => .working {work with pending := more ++ rest}
    | .refuse reason => .inconsistent reason

def step : Configuration σ → Configuration σ
  | .working work => advance work
  | endState => endState

def run : ℕ → Configuration σ → Configuration σ
  | 0, state => state
  | fuel + 1, state => run fuel (step state)

def terminal : Configuration σ → Bool
  | .working _ => false
  | _ => true

/-- This is a proof interpretation, not an operation executed by
the work-list machine. -/
def meaning : Configuration σ → Option (Subst σ)
  | .working work => (unifyTotal work.pending).map (fun solution => readTrail solution work.trail)
  | .solved trail => some (readTrail (Subst.id σ) trail)
  | .inconsistent _ => none

theorem advance_preserves (work : Work σ) :
    meaning (advance work) = meaning (.working work) := by
  obtain ⟨pending, trail⟩ := work
  cases pending with
  | nil => simp [advance, meaning, unifyTotal]
  | cons first rest =>
    obtain ⟨left, right⟩ := first
    rw [show meaning (.working ⟨(left, right) :: rest, trail⟩) =
      (interpretAction rest (action left right)).map (fun solution => readTrail solution trail) by
      simp only [meaning, action_exact]]
    cases next : action left right <;>
      simp [advance, next, meaning, interpretAction, readTrail, Option.map_map, Function.comp_def]

theorem step_preserves (state : Configuration σ) : meaning (step state) = meaning state := by
  cases state with
  | working work => exact advance_preserves work
  | solved trail => rfl
  | inconsistent reason => rfl

theorem run_preserves (fuel : ℕ) (state : Configuration σ) :
    meaning (run fuel state) = meaning state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [run, ih, step_preserves]

theorem start_exact (fuel : ℕ) (equations : Equations σ) :
    meaning (run fuel (start equations)) = unifyTotal equations := by
  rw [run_preserves]
  simp [start, meaning, readTrail]

theorem inconsistent_exact (fuel : ℕ) (equations : Equations σ) (reason : Conflict)
    (done : run fuel (start equations) = .inconsistent reason) :
    unifyTotal equations = none := by
  have exact := start_exact fuel equations
  rw [done] at exact
  exact exact.symm

theorem solved_exact (fuel : ℕ) (equations : Equations σ) (trail : Trail σ)
    (done : run fuel (start equations) = .solved trail) :
    unifyTotal equations = some (readTrail (Subst.id σ) trail) := by
  have exact := start_exact fuel equations
  rw [done] at exact
  exact exact.symm

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem smaller_size {new old : Equations σ} (bound : mmVarCount new ≤ mmVarCount old)
    (size : mmSize new < mmSize old) :
    Prod.Lex (· < ·) (· < ·) (mmMeasure new) (mmMeasure old) := by
  unfold mmMeasure
  by_cases same : mmVarCount new = mmVarCount old
  · rw [same]
    exact .right _ size
  · exact .left _ _ (Nat.lt_of_le_of_ne bound same)

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem eliminates_left (v : σ.vars) (term : Term σ) (rest : Equations σ)
    (acyclic : term.occursIn v = false) :
    Prod.Lex (· < ·) (· < ·) (mmMeasure ((Subst.single v term).applyEqs rest))
      (mmMeasure ((.var v, term) :: rest)) :=
  .left _ _ (mmVarCount_eliminate_lt v term rest acyclic)

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem eliminates_right (v : σ.vars) (term : Term σ) (rest : Equations σ)
    (acyclic : term.occursIn v = false) :
    Prod.Lex (· < ·) (· < ·) (mmMeasure ((Subst.single v term).applyEqs rest))
      (mmMeasure ((term, .var v) :: rest)) := by
  have swap : mmVarCount ((term, .var v) :: rest) = mmVarCount ((.var v, term) :: rest) := by
    simp only [mmVarCount, eqVars, Finset.union_comm term.freeVars]
  exact .left _ _ (swap ▸ mmVarCount_eliminate_lt v term rest acyclic)

theorem advances_decrease (work next : Work σ) (moves : advance work = .working next) :
    Prod.Lex (· < ·) (· < ·) (mmMeasure next.pending) (mmMeasure work.pending) := by
  obtain ⟨agenda, saved⟩ := work
  cases agenda with
  | nil => cases moves
  | cons first rest =>
    obtain ⟨left, right⟩ := first
    cases left <;> cases right
    case var.var v w =>
      by_cases same : v = w
      · subst w
        simp [advance, action] at moves
        subst next
        exact smaller_size (mmVarCount_cons_ge _ _ _) (mmSize_var_eq_lt v rest)
      · simp only [advance, action, if_neg same, Configuration.working.injEq] at moves
        subst next
        exact eliminates_left v (.var w) rest (by simp [Term.occursIn, same])
    case var.const v c =>
      cases moves
      exact eliminates_left v (.const c) rest rfl
    case var.app v f args =>
      cases occurs : (Term.app f args).occursIn v
      · simp [advance, action, occurs] at moves
        subst next
        exact eliminates_left v (.app f args) rest occurs
      · simp [advance, action, occurs] at moves
    case const.var c v =>
      cases moves
      exact eliminates_right v (.const c) rest rfl
    case const.const c d =>
      by_cases same : c = d
      · subst d
        simp [advance, action] at moves
        subst next
        exact smaller_size (mmVarCount_cons_ge _ _ _) (mmSize_const_eq_lt c rest)
      · simp [advance, action, same] at moves
    case const.app c f args => cases moves
    case app.var f args v =>
      cases occurs : (Term.app f args).occursIn v
      · simp [advance, action, occurs] at moves
        subst next
        exact eliminates_right v (.app f args) rest occurs
      · simp [advance, action, occurs] at moves
    case app.const f args c => cases moves
    case app.app f args g more =>
      by_cases same : f = g
      · subst g
        simp [advance, action] at moves
        subst next
        exact smaller_size (mmVarCount_app_eq_decompose_le f args more rest)
          (mmSize_app_eq_decompose_lt f args more rest)
      · simp [advance, action, same] at moves

def stepsToFinish (work : Work σ) : ℕ :=
  match moved : advance work with
  | .working next => stepsToFinish next + 1
  | .solved _ | .inconsistent _ => 1
termination_by mmMeasure work.pending
decreasing_by exact advances_decrease work next moved

theorem finishes_at (work : Work σ) : terminal (run (stepsToFinish work) (.working work)) = true := by
  rw [stepsToFinish]
  cases moved : advance work with
  | working next =>
    simpa only [run, step, moved] using finishes_at next
  | solved trail => simp only [run, step, moved, terminal]
  | inconsistent fault => simp only [run, step, moved, terminal]
termination_by mmMeasure work.pending
decreasing_by exact advances_decrease work next moved

theorem finishes (work : Work σ) : ∃ steps, terminal (run steps (.working work)) = true :=
  ⟨stepsToFinish work, finishes_at work⟩

theorem complete (equations : Equations σ) :
    ∃ steps, terminal (run steps (start equations)) = true ∧
      meaning (run steps (start equations)) = unifyTotal equations := by
  obtain ⟨steps, done⟩ := finishes ⟨equations, []⟩
  exact ⟨steps, done, start_exact _ _⟩

theorem resume (first second : ℕ) (state : Configuration σ) :
    run second (run first state) = run (first + second) state := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
    rw [run, ih]
    rw [show first + 1 + second = (first + second) + 1 by omega, run]

namespace Examples

private abbrev atoms : LPSignature where
  vars := ℕ
  constants := ℕ
  relationSymbols := Empty
  relationArity _ := 0
  functionSymbols := ℕ
  functionArity := id

private def cycle : Equations atoms :=
  [(.var 0, .app 1 (fun _ => .var 0))]

theorem exhaustion_does_not_reject_a_cycle :
    terminal (run 0 (start cycle)) = false := by decide +kernel

theorem cycle_detected_by_the_occurs_check :
    (match run 1 (start cycle) with
     | .inconsistent reason => some reason
     | _ => none) = some .occurs := by decide +kernel

private def chain : Equations atoms := [(.var 0, .var 1), (.var 1, .const 11)]

theorem composed_trail_resolves_both_aliases :
    (match run 3 (start chain) with
     | .solved trail => some ((readTrail (Subst.id atoms) trail) 0, (readTrail (Subst.id atoms) trail) 1)
     | _ => none) = some (.const 11, .const 11) := by rfl

end Examples

end Mettapedia.Machines.TIsa.Derivation.FiniteUnifier
