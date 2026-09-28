import Mathlib.Tactic

/-!
# Static admission for witness search with depth pruning

Deleting a search alternative preserves the support of its possible values.
That fact alone does not preserve observable writes or an ordered exception:
the deleted alternative may perform either before a later answer is selected.

The certificate below inspects every branch before execution. It rejects
effect and raise nodes, including those a bounded run would never encounter.
The model separates this property from support soundness and from preservation
of an ordered first answer. It is a finite syntax model, not a correspondence
proof for a native opcode scanner, recursion, or abstract numeric totality.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SearchPruningAdmission

universe u v

inductive Search (A : Type u) (E : Type v) where
  | answer (value : A)
  | fail
  | choice (left right : Search A E)
  | delay (body : Search A E)
  | effect (event : E) (body : Search A E)
  | raise
deriving Repr, DecidableEq

inductive Outcome (A : Type u) where
  | absent
  | found (value : A)
  | raised
deriving Repr, DecidableEq

structure Result (A : Type u) (E : Type v) where
  events : List E
  outcome : Outcome A
  cutoff : Bool
deriving Repr, DecidableEq

variable {A : Type u} {E : Type v}

/-- A syntactic, compositional certificate. In particular, it does not inspect
only the branch selected by a speculative execution. -/
def certified : Search A E → Bool
  | .answer _ | .fail => true
  | .choice left right => certified left && certified right
  | .delay body => certified body
  | .effect _ _ | .raise => false

/-- An ordered evaluator whose depth meter is charged at `delay`. A cutoff
acts as a missing answer to the surrounding choice, while remaining explicit
in the result. Events already performed remain observable. -/
def observe (depth : Nat) : Search A E → Result A E
  | .answer value => ⟨[], .found value, false⟩
  | .fail => ⟨[], .absent, false⟩
  | .raise => ⟨[], .raised, false⟩
  | .effect event body =>
      let result := observe depth body
      { result with events := event :: result.events }
  | .delay body =>
      match depth with
      | 0 => ⟨[], .absent, true⟩
      | depth + 1 => observe depth body
  | .choice left right =>
      let first := observe depth left
      match first.outcome with
      | .absent =>
          let second := observe depth right
          { second with
            events := first.events ++ second.events
            cutoff := first.cutoff || second.cutoff }
      | .found _ | .raised => first

/-- Possible-value support deliberately forgets ordering, events, and errors.
The negative controls explain why that observation cannot license an
effect-preserving portfolio by itself. -/
inductive HasAnswer : Search A E → A → Prop
  | answer (value : A) : HasAnswer (.answer value) value
  | left {left right : Search A E} {value : A} :
      HasAnswer left value → HasAnswer (.choice left right) value
  | right {left right : Search A E} {value : A} :
      HasAnswer right value → HasAnswer (.choice left right) value
  | delay {body : Search A E} {value : A} :
      HasAnswer body value → HasAnswer (.delay body) value
  | effect {body : Search A E} {value : A} (event : E) :
      HasAnswer body value → HasAnswer (.effect event body) value

theorem observe_support (search : Search A E) (depth : Nat) (value : A)
    (found : (observe depth search).outcome = .found value) :
    HasAnswer search value := by
  induction search generalizing depth with
  | answer answer =>
      simp only [observe, Outcome.found.injEq] at found
      subst answer
      exact .answer value
  | fail => simp [observe] at found
  | raise => simp [observe] at found
  | effect event body ih => exact .effect event (ih depth found)
  | delay body ih =>
      cases depth with
      | zero => simp [observe] at found
      | succ depth => exact .delay (ih depth found)
  | choice left right ihLeft ihRight =>
      simp only [observe] at found
      cases first : (observe depth left).outcome with
      | absent =>
          simp only [first] at found
          exact .right (ihRight depth found)
      | found answer =>
          simp only [first, Outcome.found.injEq] at found
          subst answer
          exact .left (ihLeft depth first)
      | raised => simp [first] at found

/-- Both obligations are discharged from the computed syntax certificate;
neither is assumed as a semantic premise about the selected execution. -/
theorem certified_observe (search : Search A E) (safe : certified search = true)
    (depth : Nat) :
    (observe depth search).events = [] ∧
      (observe depth search).outcome ≠ .raised := by
  induction search generalizing depth with
  | answer value => simp [observe]
  | fail => simp [observe]
  | raise => simp [certified] at safe
  | effect event body ih => simp [certified] at safe
  | delay body ih =>
      cases depth with
      | zero => simp [observe]
      | succ depth => exact ih safe depth
  | choice left right ihLeft ihRight =>
      simp only [certified, Bool.and_eq_true] at safe
      obtain ⟨leftEvents, leftRaise⟩ := ihLeft safe.1 depth
      obtain ⟨rightEvents, rightRaise⟩ := ihRight safe.2 depth
      simp only [observe]
      cases first : (observe depth left).outcome with
      | absent => simp [leftEvents, rightEvents, rightRaise]
      | found value => simp [first, leftEvents]
      | raised => exact False.elim (leftRaise first)

namespace Controls

def skippedWrite : Search Nat Nat :=
  .choice (.delay (.effect 42 .fail)) (.answer 7)

theorem same_supported_answer_but_different_effects :
    HasAnswer skippedWrite 7 ∧
      (observe 0 skippedWrite).outcome = .found 7 ∧
      (observe 1 skippedWrite).outcome = .found 7 ∧
      (observe 0 skippedWrite).events = [] ∧
      (observe 1 skippedWrite).events = [42] ∧
      certified skippedWrite = false := by
  exact ⟨.right (.answer 7), by decide⟩

def skippedRaise : Search Nat Nat :=
  .choice (.delay .raise) (.answer 7)

theorem supported_answer_bypasses_ordered_error :
    HasAnswer skippedRaise 7 ∧
      (observe 0 skippedRaise).outcome = .found 7 ∧
      (observe 1 skippedRaise).outcome = .raised ∧
      certified skippedRaise = false := by
  exact ⟨.right (.answer 7), by decide⟩

def pureChoice : Search Nat Nat :=
  .choice (.delay (.answer 1)) (.answer 2)

theorem certification_does_not_preserve_ordered_first :
    certified pureChoice = true ∧
      (observe 0 pureChoice).outcome = .found 2 ∧
      (observe 1 pureChoice).outcome = .found 1 ∧
      HasAnswer pureChoice 1 ∧ HasAnswer pureChoice 2 := by
  exact ⟨by decide, by decide, by decide,
    .left (.delay (.answer 1)), .right (.answer 2)⟩

end Controls

end Mettapedia.Machines.SearchPruningAdmission
