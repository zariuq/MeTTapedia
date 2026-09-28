import Mettapedia.Machines.FiniteProducerLowering
import Mathlib.Data.List.Sublists

/-!
# Shared-code structurally recursive producers

The eager interpreter constructs a complete collection. The cursor instead
retains one shared recursive body and frames containing its list argument,
integer parameter and captured map continuations. Recursive branches do not
construct or compile a recursively expanded source tree.

Admission checks lexical guards: a tail call and a head capture require a
nonempty list, and predecessor calls additionally require a positive natural
parameter. Recursive calls always consume a list cell. The checked fragment
therefore supplies structural descent, singleton collection results and pure
execution; these are not user-supplied semantic conclusions.

Guarded conditionals commit to their selected branch. They represent ordered
base equations with explicit priority, not an unordered union of equations.
Callbacks are the resolved constructor-value plans checked by
`FiniteProducerLowering.compileCallback`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RecursiveFiniteProducer

open FinitePullProducer
open FiniteProducerLowering (CallbackPlan)

universe u v
variable {Item : Type u} {Value : Type v}

/-- Shared producer code. `unsupported` is a checked rejection point, not a
purported semantics for an arbitrary external call or effect. -/
inductive Code (Value : Type v) where
  | empty
  | singleton (value : Value)
  | append (left right : Code Value)
  | mapHead (body : Code Value)
  | map (callback : CallbackPlan Value) (body : Code Value)
  | ifZero (yes no : Code Value)
  | ifEmpty (yes no : Code Value)
  | callTail
  | callPredecessor
  | unsupported
deriving Repr

def Code.weight : Code Value → Nat
  | .empty | .singleton _ | .callTail | .callPredecessor | .unsupported => 1
  | .append left right | .ifZero left right | .ifEmpty left right =>
      left.weight + right.weight + 1
  | .mapHead body | .map _ body => body.weight + 1

theorem Code.weight_pos (body : Code Value) : 0 < body.weight := by
  cases body <;> simp [Code.weight]

/-- Syntactic guard requirements. The assumptions concern only current input
shape and an integer guard, never termination or correctness of execution. -/
def Admissible (nonempty positive : Prop) : Code Value → Prop
  | .empty | .singleton _ => True
  | .append left right => Admissible nonempty positive left ∧ Admissible nonempty positive right
  | .mapHead body => nonempty ∧ Admissible nonempty positive body
  | .map _ body => Admissible nonempty positive body
  | .ifZero yes no => Admissible nonempty False yes ∧ Admissible nonempty True no
  | .ifEmpty yes no => Admissible False positive yes ∧ Admissible True positive no
  | .callTail => nonempty
  | .callPredecessor => nonempty ∧ positive
  | .unsupported => False

def check (nonempty positive : Bool) : Code Value → Bool
  | .empty | .singleton _ => true
  | .append left right => check nonempty positive left && check nonempty positive right
  | .mapHead body => nonempty && check nonempty positive body
  | .map _ body => check nonempty positive body
  | .ifZero yes no => check nonempty false yes && check nonempty true no
  | .ifEmpty yes no => check false positive yes && check true positive no
  | .callTail => nonempty
  | .callPredecessor => nonempty && positive
  | .unsupported => false

theorem check_iff (body : Code Value) (nonempty positive : Bool) :
    check nonempty positive body = true ↔
      Admissible (nonempty = true) (positive = true) body := by
  induction body generalizing nonempty positive <;>
    cases nonempty <;> cases positive <;> simp_all [check, Admissible]

theorem Admissible.strengthen {P Q P' Q' : Prop} (body : Code Value)
    (nonempty : P → P') (positive : Q → Q') (admitted : Admissible P Q body) :
    Admissible P' Q' body := by
  induction body generalizing P Q P' Q' with
  | empty => trivial
  | singleton _ => trivial
  | append left right leftIH rightIH =>
      exact ⟨leftIH nonempty positive admitted.1, rightIH nonempty positive admitted.2⟩
  | mapHead body ih => exact ⟨nonempty admitted.1, ih nonempty positive admitted.2⟩
  | map _ body ih => exact ih nonempty positive admitted
  | ifZero yes no yesIH noIH =>
      exact ⟨yesIH nonempty id admitted.1, noIH nonempty id admitted.2⟩
  | ifEmpty yes no yesIH noIH =>
      exact ⟨yesIH id positive admitted.1, noIH id positive admitted.2⟩
  | callTail => exact nonempty admitted
  | callPredecessor => exact ⟨nonempty admitted.1, positive admitted.2⟩
  | unsupported => exact admitted.elim

theorem admitted_of_check (body : Code Value) (accepted : check false false body = true) :
    Admissible False False body := by
  simpa using (check_iff body false false).mp accepted

/-- The eager source performs complete recursive calls, appends their result
lists, and maps over completed collections. Unsupported or unguarded operations
fail before a complete singleton collection can be returned. -/
def eager (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (items : List Item) (parameter : Nat) : Code Value → Option (List Value)
  | .empty => some []
  | .singleton value => some [value]
  | .append left right => do
      let earlier ← eager construct callbackConstruct program items parameter left
      let later ← eager construct callbackConstruct program items parameter right
      pure (earlier ++ later)
  | .mapHead body =>
      match items with
      | [] => none
      | head :: tail =>
          (eager construct callbackConstruct program (head :: tail) parameter body).map
            (List.map (construct head))
  | .map callback body =>
      (eager construct callbackConstruct program items parameter body).map
        (List.map (callback.run callbackConstruct))
  | .ifZero yes no =>
      if parameter = 0 then eager construct callbackConstruct program items parameter yes
      else eager construct callbackConstruct program items parameter no
  | .ifEmpty yes no =>
      if items = [] then eager construct callbackConstruct program items parameter yes
      else eager construct callbackConstruct program items parameter no
  | .callTail =>
      match items with
      | [] => none
      | _ :: tail => eager construct callbackConstruct program tail parameter program
  | .callPredecessor =>
      match items with
      | [] => none
      | _ :: tail =>
          match parameter with
          | 0 => none
          | count + 1 => eager construct callbackConstruct program tail count program
  | .unsupported => none
termination_by body => (items.length, body.weight)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Code.weight]
  all_goals omega

/-- Executable checked code always completes one finite collection. The proof
follows the actual guards and structurally smaller recursive arguments. -/
theorem eager_total (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (programGood : Admissible False False program)
    (items : List Item) (parameter : Nat) (body : Code Value)
    (bodyGood : Admissible (items ≠ []) (0 < parameter) body) :
    ∃ result, eager construct callbackConstruct program items parameter body = some result := by
  cases body with
  | empty => exact ⟨[], by simp [eager]⟩
  | singleton value => exact ⟨[value], by simp [eager]⟩
  | append left right =>
      obtain ⟨earlier, first⟩ := eager_total construct callbackConstruct program programGood
        items parameter left bodyGood.1
      obtain ⟨later, second⟩ := eager_total construct callbackConstruct program programGood
        items parameter right bodyGood.2
      exact ⟨earlier ++ later, by simp [eager, first, second]⟩
  | mapHead body =>
      cases items with
      | nil => exact (bodyGood.1 rfl).elim
      | cons head tail =>
          obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
            (head :: tail) parameter body bodyGood.2
          exact ⟨result.map (construct head), by simp [eager, done]⟩
  | map callback body =>
      obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
        items parameter body bodyGood
      exact ⟨result.map (callback.run callbackConstruct), by simp [eager, done]⟩
  | ifZero yes no =>
      by_cases zero : parameter = 0
      · obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
          items parameter yes (bodyGood.1.strengthen yes id False.elim)
        exact ⟨result, by rw [eager, if_pos zero]; exact done⟩
      · obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
          items parameter no
          (bodyGood.2.strengthen no id (fun _ => Nat.pos_of_ne_zero zero))
        exact ⟨result, by simp [eager, zero, done]⟩
  | ifEmpty yes no =>
      by_cases empty : items = []
      · obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
          items parameter yes (bodyGood.1.strengthen yes False.elim id)
        exact ⟨result, by rw [eager, if_pos empty]; exact done⟩
      · obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
          items parameter no (bodyGood.2.strengthen no (fun _ => empty) id)
        exact ⟨result, by simp [eager, empty, done]⟩
  | callTail =>
      cases items with
      | nil => exact (bodyGood rfl).elim
      | cons head tail =>
          obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
            tail parameter program (programGood.strengthen program False.elim False.elim)
          exact ⟨result, by simp [eager, done]⟩
  | callPredecessor =>
      cases items with
      | nil => exact (bodyGood.1 rfl).elim
      | cons head tail =>
          cases parameter with
          | zero => exact (Nat.lt_irrefl 0 bodyGood.2).elim
          | succ count =>
              obtain ⟨result, done⟩ := eager_total construct callbackConstruct program programGood
                tail count program (programGood.strengthen program False.elim False.elim)
              exact ⟨result, by simp [eager, done]⟩
  | unsupported => exact bodyGood.elim
termination_by (items.length, body.weight)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Code.weight]
  all_goals omega

theorem checked_eager_total (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (accepted : check false false program = true) (items : List Item) (parameter : Nat) :
    ∃ result, eager construct callbackConstruct program items parameter program = some result := by
  have admitted := admitted_of_check program accepted
  exact eager_total construct callbackConstruct program admitted items parameter program
    (admitted.strengthen program False.elim False.elim)

/-- Maps retain their captured head values while recursive calls change the
current list argument. Re-reading the callee's head would capture incorrectly. -/
inductive Mapper (Item : Type u) (Value : Type v) where
  | head (captured : Item)
  | callback (plan : CallbackPlan Value)
deriving Repr

def applyMaps (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) :
    List (Mapper Item Value) → Value → Value
  | [], value => value
  | .head captured :: rest, value =>
      applyMaps construct callbackConstruct rest (construct captured value)
  | .callback callback :: rest, value =>
      applyMaps construct callbackConstruct rest (callback.run callbackConstruct value)

structure Frame (Item : Type u) (Value : Type v) where
  code : Code Value
  items : List Item
  parameter : Nat
  maps : List (Mapper Item Value)
deriving Repr

abbrev State (Item : Type u) (Value : Type v) := List (Frame Item Value)

inductive Step (Value : Type v) (State : Type u) where
  | advance (next : State)
  | yield (value : Value) (next : State)
  | finish
  | decline
deriving Repr

/-- One instruction. Recursive calls reference the original shared program;
all per-invocation changes are arguments and captured map continuations. -/
def step (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value) :
    State Item Value → Step Value (State Item Value)
  | [] => .finish
  | ⟨.empty, _, _, _⟩ :: rest => .advance rest
  | ⟨.singleton value, _, _, maps⟩ :: rest =>
      .yield (applyMaps construct callbackConstruct maps value) rest
  | ⟨.append left right, items, parameter, maps⟩ :: rest =>
      .advance (⟨left, items, parameter, maps⟩ :: ⟨right, items, parameter, maps⟩ :: rest)
  | ⟨.mapHead _, [], _, _⟩ :: _ => .decline
  | ⟨.mapHead body, head :: tail, parameter, maps⟩ :: rest =>
      .advance (⟨body, head :: tail, parameter, .head head :: maps⟩ :: rest)
  | ⟨.map callback body, items, parameter, maps⟩ :: rest =>
      .advance (⟨body, items, parameter, .callback callback :: maps⟩ :: rest)
  | ⟨.ifZero yes _, items, 0, maps⟩ :: rest =>
      .advance (⟨yes, items, 0, maps⟩ :: rest)
  | ⟨.ifZero _ no, items, count + 1, maps⟩ :: rest =>
      .advance (⟨no, items, count + 1, maps⟩ :: rest)
  | ⟨.ifEmpty yes _, [], parameter, maps⟩ :: rest =>
      .advance (⟨yes, [], parameter, maps⟩ :: rest)
  | ⟨.ifEmpty _ no, head :: tail, parameter, maps⟩ :: rest =>
      .advance (⟨no, head :: tail, parameter, maps⟩ :: rest)
  | ⟨.callTail, [], _, _⟩ :: _ => .decline
  | ⟨.callTail, _ :: tail, parameter, maps⟩ :: rest =>
      .advance (⟨program, tail, parameter, maps⟩ :: rest)
  | ⟨.callPredecessor, [], _, _⟩ :: _ => .decline
  | ⟨.callPredecessor, _ :: _, 0, _⟩ :: _ => .decline
  | ⟨.callPredecessor, _ :: tail, count + 1, maps⟩ :: rest =>
      .advance (⟨program, tail, count, maps⟩ :: rest)
  | ⟨.unsupported, _, _, _⟩ :: _ => .decline

/-- Proof-only rank. Its exponential allowance accounts for branching
recursive calls; it is neither an allocated search tree nor runtime fuel. -/
def Frame.weight (program : Code Value) (frame : Frame Item Value) : Nat :=
  frame.code.weight * (program.weight + 1) ^ frame.items.length

def stateWeight (program : Code Value) : State Item Value → Nat
  | [] => 0
  | frame :: rest => frame.weight program + stateWeight program rest

@[simp] theorem power_pos (program : Code Value) (count : Nat) :
    0 < (program.weight + 1) ^ count := Nat.pow_pos (by omega)

@[simp] theorem recursive_rank_decreases (program : Code Value) (count : Nat) :
    program.weight * (program.weight + 1) ^ count < (program.weight + 1) ^ (count + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm ((program.weight + 1) ^ count)]
  exact Nat.mul_lt_mul_of_pos_right (by omega) (power_pos program count)

theorem step_advance_decreases (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state next : State Item Value)
    (advanced : step construct callbackConstruct program state = .advance next) :
    stateWeight program next < stateWeight program state := by
  fun_cases step construct callbackConstruct program state <;> simp [step] at advanced
  all_goals subst next
  all_goals simp [stateWeight, Frame.weight, Code.weight, Nat.add_mul, Nat.add_assoc]
  case case8 yes no items maps rest =>
    have positive := power_pos program items.length
    omega
  case case9 yes no items count maps rest =>
    have positive := power_pos program items.length
    omega
  case case10 => omega
  case case11 yes no head tail parameter maps rest =>
    have positive := power_pos program (tail.length + 1)
    omega

/-- Normalize only administrative instructions until one value is available.
The decreasing rank is a termination proof, not an input-dependent runtime
budget and not a reason to fall back on a large collection. -/
def pull (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state : State Item Value) : PullStep Value (State Item Value) :=
  match _observed : step construct callbackConstruct program state with
  | .advance next => pull construct callbackConstruct program next
  | .yield value next => .yield value next
  | .finish => .finish []
  | .decline => .decline
termination_by stateWeight program state
decreasing_by exact step_advance_decreases construct callbackConstruct program state next _observed

def denote (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value) :
    State Item Value → Option (List Value)
  | [] => some []
  | frame :: rest => do
      let values ← eager construct callbackConstruct program frame.items frame.parameter frame.code
      let suffix ← denote construct callbackConstruct program rest
      pure (values.map (applyMaps construct callbackConstruct frame.maps) ++ suffix)

theorem step_meaning (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state : State Item Value) :
    denote construct callbackConstruct program state =
      match step construct callbackConstruct program state with
      | .advance next => denote construct callbackConstruct program next
      | .yield value next => (denote construct callbackConstruct program next).map (value :: ·)
      | .finish => some []
      | .decline => none := by
  fun_cases step construct callbackConstruct program state <;>
    simp [denote, eager, applyMaps, Option.map_eq_bind, Option.bind_assoc, List.map_map,
      List.map_append, Function.comp_def, List.append_assoc]

/-- Run at most this many administrative instructions. An `advance` result is
a resumable state, not failure, fallback or restart. Primitive constructor and
callback costs still require their own native interruption contract. -/
def runBudget (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value) :
    Nat → State Item Value → Step Value (State Item Value)
  | 0, state => .advance state
  | budget + 1, state =>
      match step construct callbackConstruct program state with
      | .advance next => runBudget construct callbackConstruct program budget next
      | .yield value next => .yield value next
      | .finish => .finish
      | .decline => .decline

/-- Suspending at an instruction budget preserves the complete pending
observation. Resumption therefore need not rebuild or replay the prefix. -/
theorem runBudget_meaning (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (budget : Nat) (state : State Item Value) :
    denote construct callbackConstruct program state =
      match runBudget construct callbackConstruct program budget state with
      | .advance next => denote construct callbackConstruct program next
      | .yield value next => (denote construct callbackConstruct program next).map (value :: ·)
      | .finish => some []
      | .decline => none := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      have meaning := step_meaning construct callbackConstruct program state
      cases observed : step construct callbackConstruct program state with
      | advance next =>
          simp only [runBudget, observed]
          have same : denote construct callbackConstruct program state =
              denote construct callbackConstruct program next := by
            simpa only [observed] using meaning
          exact same.trans (ih next)
      | yield value next => simpa only [runBudget, observed] using meaning
      | finish => simpa only [runBudget, observed] using meaning
      | decline => simpa only [runBudget, observed] using meaning

theorem pull_meaning (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state : State Item Value) :
    denote construct callbackConstruct program state =
      match pull construct callbackConstruct program state with
      | .yield value next => (denote construct callbackConstruct program next).map (value :: ·)
      | .finish suffix => some suffix
      | .decline => none := by
  have meaning := step_meaning construct callbackConstruct program state
  cases observed : step construct callbackConstruct program state with
  | advance next =>
      simp only [observed] at meaning
      rw [pull, observed, meaning]
      exact pull_meaning construct callbackConstruct program next
  | yield value next =>
      rw [pull, observed]
      simpa only [observed] using meaning
  | finish =>
      rw [pull, observed]
      simpa only [observed] using meaning
  | decline =>
      rw [pull, observed]
      simpa only [observed] using meaning
termination_by stateWeight program state
decreasing_by exact step_advance_decreases construct callbackConstruct program state next observed

theorem finish_empty (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state : State Item Value) (suffix : List Value)
    (finished : pull construct callbackConstruct program state = .finish suffix) : suffix = [] := by
  fun_induction pull construct callbackConstruct program state <;> simp_all

/-- A complete eager result supplies the cursor invariant. At the public
boundary `checked_eager_total` derives this premise from admission. -/
theorem produces (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state : State Item Value) (items : List Value)
    (meaning : denote construct callbackConstruct program state = some items) :
    Produces (pull construct callbackConstruct program) state items (items.length + 1) := by
  have sound := pull_meaning construct callbackConstruct program state
  rw [meaning] at sound
  cases observed : pull construct callbackConstruct program state with
  | decline => simp [observed] at sound
  | finish suffix =>
      have empty := finish_empty construct callbackConstruct program state suffix observed
      simp only [observed, empty, Option.some.injEq] at sound
      subst items
      exact Produces.finish (by simpa [empty] using observed)
  | yield item next =>
      simp only [observed] at sound
      cases tail : denote construct callbackConstruct program next with
      | none => simp [tail] at sound
      | some rest =>
          simp only [tail, Option.map_some, Option.some.injEq] at sound
          subst items
          exact Produces.yield observed
            (produces construct callbackConstruct program next rest tail)
termination_by items.length
decreasing_by
  simp_all only [Option.map_some, Option.some.injEq]
  simp_all only [List.length_cons]
  omega

def takePrefix (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value) :
    Nat → State Item Value → Option (List Value)
  | 0, _ => some []
  | bound + 1, state =>
      match pull construct callbackConstruct program state with
      | .decline => none
      | .finish suffix => some (suffix.take (bound + 1))
      | .yield value next =>
          (takePrefix construct callbackConstruct program bound next).map (value :: ·)

theorem takePrefix_refines_take (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (bound : Nat) (state : State Item Value) (items : List Value)
    (meaning : denote construct callbackConstruct program state = some items) :
    takePrefix construct callbackConstruct program bound state = some (items.take bound) := by
  induction bound generalizing state items with
  | zero => rfl
  | succ bound ih =>
      have sound := pull_meaning construct callbackConstruct program state
      rw [meaning] at sound
      cases observed : pull construct callbackConstruct program state with
      | decline => simp [observed] at sound
      | finish suffix =>
          simp only [observed, Option.some.injEq] at sound
          simp [takePrefix, observed, sound]
      | yield item next =>
          simp only [observed] at sound
          cases tail : denote construct callbackConstruct program next with
          | none => simp [tail] at sound
          | some rest =>
              simp only [tail, Option.map_some, Option.some.injEq] at sound
              simp [takePrefix, observed, sound, ih next rest tail]

def initial (program : Code Value) (items : List Item) (parameter : Nat) : State Item Value :=
  [⟨program, items, parameter, []⟩]

theorem denote_initial (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (items : List Item) (parameter : Nat) :
    denote construct callbackConstruct program (initial program items parameter) =
      eager construct callbackConstruct program items parameter program := by
  simp [denote, initial, applyMaps]

/-- Checked shared recursive code and its streaming cursor have the same
complete result and every bounded ordered occurrence prefix. The existential
result is derived by structural descent, not assumed as an admission premise. -/
theorem checked_bounded_correct (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (accepted : check false false program = true) (items : List Item) (parameter : Nat) :
    ∃ result,
      eager construct callbackConstruct program items parameter program = some result ∧
      ∀ bound, takePrefix construct callbackConstruct program bound
        (initial program items parameter) = some (result.take bound) := by
  obtain ⟨result, completed⟩ :=
    checked_eager_total construct callbackConstruct program accepted items parameter
  refine ⟨result, completed, fun bound => ?_⟩
  exact takePrefix_refines_take construct callbackConstruct program bound
    (initial program items parameter) result
    ((denote_initial construct callbackConstruct program items parameter).trans completed)

theorem checked_fold_correct {Accumulator : Type v}
    (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (accepted : check false false program = true) (items : List Item) (parameter : Nat)
    (combine : Accumulator → Value → Accumulator) (accumulator : Accumulator) :
    ∃ result,
      eager construct callbackConstruct program items parameter program = some result ∧
      pullFold (pull construct callbackConstruct program) (totalConsumer combine)
        (result.length + 1) (initial program items parameter) accumulator =
          .commit (result.foldl combine accumulator) := by
  obtain ⟨result, completed⟩ :=
    checked_eager_total construct callbackConstruct program accepted items parameter
  refine ⟨result, completed, ?_⟩
  exact pullFold_refines_foldl (pull construct callbackConstruct program) combine
    (produces construct callbackConstruct program (initial program items parameter) result
      ((denote_initial construct callbackConstruct program items parameter).trans completed))
    accumulator

/-- A native signed integer may implement this natural parameter only after
checking nonnegativity and its representable upper bound. Under the positive
guard, decrement agrees with integer subtraction and stays in that range. -/
theorem guarded_predecessor_in_range (parameter limit : Nat)
    (positive : 0 < parameter) (bounded : parameter ≤ limit) :
    parameter - 1 < parameter ∧ parameter - 1 ≤ limit ∧
      (Int.ofNat (parameter - 1)) = Int.ofNat parameter - 1 := by
  cases parameter with
  | zero => omega
  | succ count => simp; omega

theorem zero_bound_no_body (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state : State Item Value) :
    takePrefix construct callbackConstruct program 0 state = some [] := rfl

theorem exact_bound_no_lookahead (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : Code Value)
    (state next : State Item Value) (value : Value)
    (yielded : pull construct callbackConstruct program state = .yield value next) :
    takePrefix construct callbackConstruct program 1 state = some [value] := by
  simp [takePrefix, yielded]

namespace Combinations

/-- Include-first fixed-size sublists. This is ordinary code of the admitted
grammar; admission and the cursor have no function-name test for combinations. -/
def program : Code (List Item) :=
  .ifZero (.singleton [])
    (.ifEmpty .empty (.append (.mapHead .callPredecessor) .callTail))

theorem admitted : check false false (program (Item := Item)) = true := rfl

/-- The callback algebra is unused by this particular program. It remains a
parameter so the example does not smuggle in an additional execution lane. -/
theorem eager_eq_sublistsLen_reverse
    (callbackConstruct : Nat → List Item → List Item → List Item)
    (items : List Item) (parameter : Nat) :
    eager List.cons callbackConstruct program items parameter program =
      some ((items.sublistsLen parameter).reverse) := by
  induction items generalizing parameter with
  | nil =>
      cases parameter <;> simp [program, eager]
  | cons head tail ih =>
      cases parameter with
      | zero => simp [program, eager]
      | succ count =>
          have mapRec :
              eager List.cons callbackConstruct program (head :: tail) (count + 1)
                  (.mapHead .callPredecessor) =
                (eager List.cons callbackConstruct program tail count program).map
                  (List.map (List.cons head)) := by
            rw [eager, eager]
          have tailRec :
              eager List.cons callbackConstruct program (head :: tail) (count + 1)
                  .callTail =
                eager List.cons callbackConstruct program tail (count + 1) program := by
            rw [eager]
          change eager List.cons callbackConstruct program (head :: tail) (count + 1)
            (.ifZero (.singleton [])
              (.ifEmpty .empty (.append (.mapHead .callPredecessor) .callTail))) = _
          rw [eager]
          simp only [Nat.succ_ne_zero, ↓reduceIte]
          rw [eager]
          simp only [List.cons_ne_nil, ↓reduceIte]
          rw [eager, mapRec, tailRec, ih, ih]
          simp [List.reverse_append, List.map_reverse]

/-- The full source collection has the standard binomial cardinality. -/
theorem cardinality
    (callbackConstruct : Nat → List Item → List Item → List Item)
    (items : List Item) (parameter : Nat) :
    (eager List.cons callbackConstruct program items parameter program).map List.length =
      some (items.length.choose parameter) := by
  rw [eager_eq_sublistsLen_reverse]
  simp

theorem bounded_cursor_eq_sublistsLen_reverse
    (callbackConstruct : Nat → List Item → List Item → List Item)
    (items : List Item) (parameter bound : Nat) :
    takePrefix List.cons callbackConstruct program bound (initial program items parameter) =
      some (((items.sublistsLen parameter).reverse).take bound) := by
  apply takePrefix_refines_take
  rw [denote_initial, eager_eq_sublistsLen_reverse]

end Combinations

namespace RepeatedOccurrences

/-- A second recursive shape duplicates the tail result. Its exponential
occurrence count must be retained even though every payload is equal. -/
def program (value : Value) : Code Value :=
  .ifEmpty (.singleton value) (.append .callTail .callTail)

theorem admitted (value : Value) : check false false (program value) = true := rfl

theorem eager_eq_replicate (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (value : Value) (items : List Item) (parameter : Nat) :
    eager construct callbackConstruct (program value) items parameter (program value) =
      some (List.replicate (2 ^ items.length) value) := by
  induction items with
  | nil => simp [program, eager]
  | cons head tail ih =>
      have tailRec :
          eager construct callbackConstruct (program value) (head :: tail) parameter .callTail =
            eager construct callbackConstruct (program value) tail parameter (program value) := by
        rw [eager]
      change eager construct callbackConstruct (program value) (head :: tail) parameter
        (.ifEmpty (.singleton value) (.append .callTail .callTail)) = _
      rw [eager]
      simp only [List.cons_ne_nil, ↓reduceIte]
      rw [eager, tailRec, ih]
      simp [Nat.pow_succ, Nat.mul_two]

theorem bounded_cursor_eq_replicate (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (value : Value) (items : List Item) (parameter bound : Nat) :
    takePrefix construct callbackConstruct (program value) bound
        (initial (program value) items parameter) =
      some (List.replicate (min bound (2 ^ items.length)) value) := by
  have exactPrefix := takePrefix_refines_take construct callbackConstruct (program value)
    bound (initial (program value) items parameter) (List.replicate (2 ^ items.length) value)
    ((denote_initial construct callbackConstruct (program value) items parameter).trans
      (eager_eq_replicate construct callbackConstruct value items parameter))
  simpa using exactPrefix

end RepeatedOccurrences

namespace Controls

def listConstructor (_tag : Nat) (left right : List Nat) : List Nat := left ++ right

theorem combinations_prefix :
    takePrefix List.cons listConstructor Combinations.program 2
      (initial Combinations.program [1, 2, 3, 4] 2) = some [[1, 2], [1, 3]] := by
  rw [Combinations.bounded_cursor_eq_sublistsLen_reverse]
  decide

theorem duplicate_inputs_preserve_occurrences :
    takePrefix List.cons listConstructor Combinations.program 20
      (initial Combinations.program [1, 1, 2] 2) = some [[1, 1], [1, 2], [1, 2]] := by
  rw [Combinations.bounded_cursor_eq_sublistsLen_reverse]
  decide

theorem twenty_from_forty_cardinality : Nat.choose 40 20 = 137846528820 := by decide

/-- Testing list emptiness before the zero base equation changes the answer
on the overlap. Code preserves authored branch priority and its local commit. -/
theorem base_equation_priority_matters :
    eager List.cons listConstructor Combinations.program [] 0 Combinations.program = some [[]] ∧
      eager List.cons listConstructor Combinations.program [] 0
        (.ifEmpty .empty (.ifZero (.singleton []) .empty)) = some [] := by
  constructor
  · rw [Combinations.eager_eq_sublistsLen_reverse]; rfl
  · simp [eager]

theorem unguarded_recursion_and_capture_rejected :
    check false false (Code.callTail : Code (List Nat)) = false ∧
      check true false (Code.callPredecessor : Code (List Nat)) = false ∧
      check false true (Code.mapHead (.singleton []) : Code (List Nat)) = false ∧
      check true true (Code.unsupported : Code (List Nat)) = false := by decide

/-- A mapper captures the caller's head before entering a recursive call. -/
theorem map_head_captures_before_call :
    step List.cons listConstructor Combinations.program
      [⟨.mapHead .callPredecessor, [1, 2, 3], 2, []⟩] =
        .advance [⟨.callPredecessor, [1, 2, 3], 2, [.head 1]⟩] ∧
      step List.cons listConstructor Combinations.program
        [⟨.callPredecessor, [1, 2, 3], 2, [.head 1]⟩] =
        .advance [⟨Combinations.program, [2, 3], 1, [.head 1]⟩] := by
  exact ⟨rfl, rfl⟩

end Controls

end Mettapedia.Machines.RecursiveFiniteProducer
