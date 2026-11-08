import Mettapedia.Machines.BoundaryCore
import Mathlib.Tactic

/-!
# Finite-answer protocols and typed region boundaries

A call separates entry, body, discharge, and selection of the complete answer
batch. Early answers include failed checks. Selection is deliberately not
required to distribute over alternatives: an evaluator may suppress errors
when another alternative succeeds.

The observation here is an exact finite multiset, not a set. Effects, order,
identity, and suspension must be represented in the observed values when a
client needs them; this module does not erase them by a runtime theorem.

An optional offer is a pure/pre-work admission decision: `none` retains its
incoming state. A partially executed attempt must export its residual state
instead; it cannot use `none` to erase effects or published answers. The
region budget counts graph transitions, not source evaluator fuel or C work.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TypedBoundary

universe u

variable {I F G V W O N A : Type u}

/-- A boundary over already specified argument demand. A frame contains all
state that the body and the return check share. -/
abbrev Boundary (I F V O : Type u) :=
  BoundaryCore.Protocol Multiset I F V O (· + ·)

def Boundary.run (b : Boundary I F V O) (body : F → Multiset V) (input : I) : Multiset O :=
  b.select (b.early input + (b.enter input).bind fun frame =>
    (body frame).bind (b.leave frame))

theorem Boundary.run_core (b : Boundary I F V O) (body : F → Multiset V) (input : I) :
    b.run body input = BoundaryCore.Protocol.run b body input := rfl

/-- The logical relation is lifted to occurrences, not merely membership. -/
theorem Boundary.run_eq_of_related
    (source : Boundary I F V O) (target : Boundary I G W O)
    (body : F → Multiset V) (compiled : G → Multiset W)
    (frames : F → G → Prop) (values : V → W → Prop)
    (early : ∀ input, source.early input = target.early input)
    (entry : ∀ input, Multiset.Rel frames (source.enter input) (target.enter input))
    (work : ∀ f g, frames f g → Multiset.Rel values (body f) (compiled g))
    (returns : ∀ f g, frames f g → ∀ v w, values v w →
      source.leave f v = target.leave g w)
    (selection : source.select = target.select) (input : I) :
    source.run body input = target.run compiled input := by
  have outputs : Multiset.Rel Eq
      ((source.enter input).bind fun f => (body f).bind (source.leave f))
      ((target.enter input).bind fun g => (compiled g).bind (target.leave g)) := by
    apply Multiset.rel_bind _ (entry input)
    intro f g related
    apply Multiset.rel_bind _ (work f g related)
    intro v w relatedValue
    exact Multiset.rel_eq.mpr (returns f g related v w relatedValue)
  simp only [Boundary.run, early input, selection, Multiset.rel_eq.mp outputs]

/-- Replacing a check requires equality of its entire continuation bag on
reachable results. Merely having a successful typing derivation is weaker. -/
theorem Boundary.run_eq_of_leave
    (source : Boundary I F V O) (replacement : F → V → Multiset O)
    (body : F → Multiset V) (input : I)
    (checked : ∀ f ∈ source.enter input, ∀ v ∈ body f,
      source.leave f v = replacement f v) :
    source.run body input =
      ({ source with leave := replacement } : Boundary I F V O).run body input := by
  unfold Boundary.run
  change source.select (source.early input + _) = source.select (source.early input + _)
  apply congrArg source.select
  apply congrArg (source.early input + ·)
  exact Multiset.bind_congr fun f hf =>
    Multiset.bind_congr fun v hv => checked f hf v hv

/-- An optional compiled result is not an optional language answer. Refusal
invokes the canonical operation on exactly the incoming boundary state. -/
def dispatch (canonical : I → Multiset O) (compiled : I → Option (Multiset O))
    (input : I) : Multiset O :=
  match compiled input with
  | none => canonical input
  | some answers => answers

theorem dispatch_eq (canonical : I → Multiset O) (compiled : I → Option (Multiset O))
    (sound : ∀ input answers, compiled input = some answers → answers = canonical input)
    (input : I) : dispatch canonical compiled input = canonical input := by
  cases accepted : compiled input with
  | none => simp [dispatch, accepted]
  | some answers => simpa [dispatch, accepted] using sound input answers accepted

/-- A batch policy that keeps successes if any exist, and failures otherwise. -/
def preferSuccess (success : O → Bool) (answers : Multiset O) : Multiset O :=
  let good := answers.filter fun answer => success answer = true
  if good.card = 0 then answers.filter (fun answer => success answer = false) else good

theorem preferSuccess_all (success : O → Bool) (answers : Multiset O)
    (good : ∀ answer ∈ answers, success answer = true) :
    preferSuccess success answers = answers := by
  have filtered : answers.filter (fun answer => success answer = true) = answers :=
    Multiset.filter_eq_self.mpr good
  unfold preferSuccess
  rw [filtered]
  dsimp only
  split_ifs with empty
  · simp [Multiset.card_eq_zero.mp empty]
  · rfl

theorem preferSuccess_list (success : O → Bool) (answers : List O) :
    preferSuccess success (answers : Multiset O) =
      ((if (answers.filter success).isEmpty then
        answers.filter (fun answer => !success answer) else answers.filter success) : List O) := by
  simp only [preferSuccess, Multiset.filter_coe, Multiset.coe_card]
  cases filtered : answers.filter success with
  | nil => simp [filtered]
  | cons first rest => simp [filtered]

/-- A graph edge can return an answer or expose another complete boundary
state. The state includes the continuation, not just its current value. -/
abbrev Graph (N A : Type u) := N → Multiset (Sum A N)

def run (graph : Graph N A) : Nat → Sum A N → Multiset (Sum A N)
  | _, .inl answer => {.inl answer}
  | 0, .inr state => {.inr state}
  | fuel + 1, .inr state => (graph state).bind (run graph fuel)

/-- Exact residual composition: a second region starts where the first one
stopped, even when some alternatives have already returned. -/
theorem run_add (graph : Graph N A) (first second : Nat) (state : Sum A N) :
    run graph (first + second) state =
      (run graph first state).bind (run graph second) := by
  induction first generalizing state with
  | zero => cases state <;> simp [run]
  | succ first ih =>
      cases state with
      | inl answer => simp [run]
      | inr state =>
          simp only [Nat.succ_add, run, Multiset.bind_assoc]
          exact Multiset.bind_congr fun next _ => ih next

/-- Returned values agree; retained states may have different representations. -/
def ExitRel (states : F → G → Prop) : Sum A F → Sum A G → Prop
  | .inl left, .inl right => left = right
  | .inr left, .inr right => states left right
  | _, _ => False

/-- Local two-sided occurrence correspondence composes through an arbitrary
finite region, including loops, without a deterministic-body assumption. -/
theorem run_related (source : Graph F A) (target : Graph G A)
    (states : F → G → Prop)
    (steps : ∀ left right, states left right →
      Multiset.Rel (ExitRel states) (source left) (target right))
    (fuel : Nat) (left : Sum A F) (right : Sum A G)
    (related : ExitRel states left right) :
    Multiset.Rel (ExitRel states) (run source fuel left) (run target fuel right) := by
  induction fuel generalizing left right with
  | zero =>
      have one : Multiset.Rel (ExitRel states) {left} {right} := .cons related .zero
      cases left <;> cases right <;> exact one
  | succ fuel ih =>
      cases left with
      | inl answer =>
          cases right with
          | inl answer' => exact .cons related .zero
          | inr _ => contradiction
      | inr state =>
          cases right with
          | inl _ => contradiction
          | inr state' =>
              exact Multiset.rel_bind (fun left right h => ih left right h)
                (steps state state' related)

/-- A fused region retains the precise frontier of several primitive steps.
This is not a claim that the fused region consumes one unit of source fuel. -/
def fuse (width : Nat) (graph : Graph N A) : Graph N A :=
  fun state => run graph width (.inr state)

theorem run_fuse (width regions : Nat) (graph : Graph N A) (state : Sum A N) :
    run (fuse width graph) regions state = run graph (width * regions) state := by
  induction regions generalizing state with
  | zero => cases state <;> rfl
  | succ regions ih =>
      cases state with
      | inl answer => simp [run]
      | inr state =>
          simp only [run, fuse, Nat.mul_succ, Nat.add_comm (width * regions) width]
          rw [run_add]
          exact Multiset.bind_congr fun next _ => ih next

/-- An admission type is a predicate of the full boundary state. Its typing
rule must preserve that predicate on continuing exits. -/
def Preserves (graph : Graph N A) (admitted : N → Prop) : Prop :=
  ∀ state, admitted state → ∀ next, Sum.inr next ∈ graph state → admitted next

def AtExit (admitted : N → Prop) : Sum A N → Prop
  | .inl _ => True
  | .inr state => admitted state

theorem run_preserves (graph : Graph N A) (admitted : N → Prop)
    (closed : Preserves graph admitted) (fuel : Nat) (state : Sum A N)
    (entry : AtExit admitted state) :
    ∀ answer ∈ run graph fuel state, AtExit admitted answer := by
  induction fuel generalizing state with
  | zero =>
      cases state <;> simpa [run] using entry
  | succ fuel ih =>
      cases state with
      | inl answer => simp [run, AtExit]
      | inr state =>
          intro answer member
          obtain ⟨next, hn, ha⟩ := Multiset.mem_bind.mp member
          apply ih next _ answer ha
          cases next with
          | inl value => trivial
          | inr next => exact closed state entry next hn

/-- Every graph region may independently offer a prepared implementation. -/
def tiered (graph : Graph N A) (compiled : N → Option (Multiset (Sum A N))) : Graph N A :=
  dispatch graph compiled

/-- Local admission and closure suffice for exact correspondence at every
finite frontier, including repeated answers and paused alternatives. -/
theorem tiered_run_eq (graph : Graph N A)
    (compiled : N → Option (Multiset (Sum A N))) (admitted : N → Prop)
    (closed : Preserves graph admitted)
    (sound : ∀ state, admitted state → ∀ answers,
      compiled state = some answers → answers = graph state)
    (fuel : Nat) (state : Sum A N) (entry : AtExit admitted state) :
    run (tiered graph compiled) fuel state = run graph fuel state := by
  induction fuel generalizing state with
  | zero => cases state <;> rfl
  | succ fuel ih =>
      cases state with
      | inl answer => rfl
      | inr state =>
          have step : tiered graph compiled state = graph state := by
            cases accepted : compiled state with
            | none => simp [tiered, dispatch, accepted]
            | some answers =>
                simpa [tiered, dispatch, accepted] using sound state entry answers accepted
          simp only [run, step]
          apply Multiset.bind_congr
          intro next member
          apply ih next
          cases next with
          | inl answer => trivial
          | inr next => exact closed state entry next member

namespace Controls

def succeeds : Sum Nat Nat → Bool
  | .inl _ => false
  | .inr _ => true

/-- Batch selection cannot be pushed independently into each alternative. -/
theorem selection_not_additive :
    preferSuccess succeeds ({Sum.inl 7, Sum.inr 2} : Multiset (Sum Nat Nat)) ≠
      preferSuccess succeeds {Sum.inl 7} + preferSuccess succeeds {Sum.inr 2} := by
  decide

def repeating : Boundary Unit Unit Nat Nat where
  early := fun _ => 0
  enter := fun _ => {()}
  leave := fun _ value => {value, value}
  select := id

/-- A successful check with two derivations cannot be replaced by a no-op. -/
theorem existence_does_not_elide :
    repeating.run (fun _ => {3}) () = {3, 3} ∧
      repeating.run (fun _ => {3}) () ≠ ({3} : Multiset Nat) := by
  constructor
  · simp [Boundary.run, repeating]
  · decide

def countdown : Graph Nat Nat
  | 0 => {.inl 7, .inl 7}
  | n + 1 => {.inr n}

def partialCountdown : Nat → Option (Multiset (Sum Nat Nat))
  | 0 => some {.inl 7, .inl 7}
  | 1 => none
  | n + 2 => some {.inr (n + 1)}

theorem partialCountdown_sound (n : Nat) (answers : Multiset (Sum Nat Nat))
    (accepted : partialCountdown n = some answers) : answers = countdown n := by
  cases n with
  | zero => simpa [partialCountdown, countdown] using accepted.symm
  | succ n => cases n <;> simp_all [partialCountdown, countdown]

/-- The middle step declines; the other regions still execute compiled and
the two producer occurrences remain two answers. -/
theorem local_decline_keeps_duplicates :
    run (tiered countdown partialCountdown) 3 (.inr 2) = {.inl 7, .inl 7} := by
  decide

/-- A bounded prefix is a live frontier, not a certificate of no answers. -/
theorem paused_is_not_empty :
    run countdown 1 (.inr 2) = {.inr 1} ∧
      run countdown 3 (.inr 2) = {.inl 7, .inl 7} := by
  decide

/-- A macro step and three primitive steps expose the same duplicate answers,
although their internal transition counts differ. -/
theorem fusion_keeps_frontier :
    run (fuse 3 countdown) 1 (.inr 2) = run countdown 3 (.inr 2) ∧
      run countdown 1 (.inr 2) ≠ run countdown 3 (.inr 2) := by
  decide

def losesDuplicate : Nat → Option (Multiset (Sum Nat Nat))
  | 0 => some {.inl 7}
  | _ => none

theorem set_preservation_is_insufficient :
    (∀ answer, answer ∈ run (tiered countdown losesDuplicate) 1 (.inr 0) ↔
      answer ∈ run countdown 1 (.inr 0)) ∧
      run (tiered countdown losesDuplicate) 1 (.inr 0) ≠ run countdown 1 (.inr 0) := by
  constructor
  · intro answer; simp [run, tiered, dispatch, countdown, losesDuplicate]
  · decide

end Controls

end Mettapedia.Machines.TypedBoundary
