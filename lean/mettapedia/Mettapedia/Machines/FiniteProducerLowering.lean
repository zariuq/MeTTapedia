import Mettapedia.Machines.FinitePullProducer
import Mettapedia.Machines.SuperposeFusion
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences

/-!
# Checked lowering of finite collection producers

An independently defined eager source builds collections from flat data,
constructors, append, captured callbacks, and a structurally decreasing range.
A checked compiler accepts only constructor-valued callbacks with resolved
captures. Failure, branching, effects, and a divergent callback are explicit
source forms and are rejected, rather than discharged by a totality premise.

The lowered machine walks source-independent plan frames and callback
continuations. It yields occurrences without constructing the collection
spine. Its complete pull trace and every bounded prefix are proved from the
compiled grammar. The prefix boundary checks zero before executing the body.

This is a finite pure fragment and a sequential compilation theorem, not a
native-runtime correspondence. Data constructors and numeral construction are
total semantic primitives. Their runtime realizations, captures, dialect plans,
revision stability, allocation, and interruption behavior require refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FiniteProducerLowering

open FinitePullProducer

universe u

variable {Value : Type u}

/-- Complete eager execution: a finite ordered answer list with event trace,
or divergence before a complete result is available. This does not observe
partial output prefixes of a divergent eager computation. -/
inductive Execution (Answer : Type u) where
  | done (answers : List Answer) (events : List Nat)
  | diverges
deriving DecidableEq, Repr

namespace Execution

def map {A B : Type u} (f : A → B) : Execution A → Execution B
  | .done answers events => .done (answers.map f) events
  | .diverges => .diverges

/-- Left-to-right finite product; eventful/nondeterministic combinations are
outside the admitted fragment, but remain explicit in the source calculus. -/
def product {A B C : Type u} (f : A → B → C) :
    Execution A → Execution B → Execution C
  | .done left earlier, .done right later =>
      .done (left.flatMap fun x => right.map (f x)) (earlier ++ later)
  | _, _ => .diverges

def alternatives {A : Type u} : Execution A → Execution A → Execution A
  | .done left earlier, .done right later => .done (left ++ right) (earlier ++ later)
  | _, _ => .diverges

def emit {A : Type u} (event : Nat) : Execution A → Execution A
  | .done answers events => .done answers (event :: events)
  | .diverges => .diverges

def traverseAlternatives {A B : Type u} (next : A → Execution B) :
    List A → Execution B
  | [] => .done [] []
  | first :: rest => alternatives (next first) (traverseAlternatives next rest)

def bind {A B : Type u} (execution : Execution A) (next : A → Execution B) : Execution B :=
  match execution with
  | .diverges => .diverges
  | .done answers events =>
      match traverseAlternatives next answers with
      | .diverges => .diverges
      | .done results later => .done results (events ++ later)

@[simp] theorem map_done_single {A B : Type u} (f : A → B) (a : A) :
    map f (.done [a] []) = .done [f a] [] := rfl

@[simp] theorem product_done_single {A B C : Type u} (f : A → B → C) (a : A) (b : B) :
    product f (.done [a] []) (.done [b] []) = .done [f a b] [] := rfl

theorem bind_done_single {A B : Type u} (a : A) (next : A → Execution B) :
    bind (.done [a] []) next = next a := by
    cases result : next a <;> simp [bind, traverseAlternatives, alternatives, result]

theorem traverse_identity {A : Type u} (answers : List A) :
    traverseAlternatives (fun a => done [a] []) answers = done answers [] := by
  induction answers with
  | nil => rfl
  | cons a answers ih => simp [traverseAlternatives, alternatives, ih]

/-- A continuation which only returns its private received value adds neither
events nor occurrences. Forwarding retains divergence as well. The native
admission must separately establish privacy and preserve its matching scope. -/
theorem bind_identity {A : Type u} (execution : Execution A) :
    bind execution (fun a => done [a] []) = execution := by
  cases execution <;> simp [bind, traverse_identity]

end Execution

/-- Callback syntax distinguishes values and captures from executable effects. -/
inductive Callback (Value : Type u) where
  | argument
  | captured (slot : Nat)
  | value (value : Value)
  | constructor (tag : Nat) (left right : Callback Value)
  | fail
  | choice (left right : Callback Value)
  | effect (event : Nat) (body : Callback Value)
  | loop
deriving Repr

/-- A callback value carries its captured values, not source to re-evaluate. -/
structure Closure (Value : Type u) where
  body : Callback Value
  captures : List Value
deriving Repr

def evalCallback (construct : Nat → Value → Value → Value)
    (captures : List Value) (argument : Value) : Callback Value → Execution Value
  | .argument => .done [argument] []
  | .captured slot =>
      match captures[slot]? with
      | some value => .done [value] []
      | none => .done [] []
  | .value value => .done [value] []
  | .constructor tag left right =>
      .product (construct tag)
        (evalCallback construct captures argument left)
        (evalCallback construct captures argument right)
  | .fail => .done [] []
  | .choice left right =>
      .alternatives (evalCallback construct captures argument left)
        (evalCallback construct captures argument right)
  | .effect event body => .emit event (evalCallback construct captures argument body)
  | .loop => .diverges

def evalClosure (construct : Nat → Value → Value → Value)
    (closure : Closure Value) (argument : Value) : Execution Value :=
  evalCallback construct closure.captures argument closure.body

/-- The accepted callback language has no failure, choice, effect or open
capture instruction. Resolving captures is part of compilation. -/
inductive CallbackPlan (Value : Type u) where
  | argument
  | value (value : Value)
  | constructor (tag : Nat) (left right : CallbackPlan Value)
deriving Repr

def CallbackPlan.run (construct : Nat → Value → Value → Value)
    (argument : Value) : CallbackPlan Value → Value
  | .argument => argument
  | .value stored => stored
  | .constructor tag left right =>
      construct tag (left.run construct argument) (right.run construct argument)

def compileCallback (captures : List Value) : Callback Value → Option (CallbackPlan Value)
  | .argument => some .argument
  | .captured slot => (captures[slot]?).map .value
  | .value value => some (.value value)
  | .constructor tag left right => do
      let first ← compileCallback captures left
      let second ← compileCallback captures right
      pure (.constructor tag first second)
  | .fail | .choice _ _ | .effect _ _ | .loop => none

def compileClosure (closure : Closure Value) : Option (CallbackPlan Value) :=
  compileCallback closure.captures closure.body

/-- Admission establishes singleton, finite, effect-free callback execution
for every argument. None of those conclusions is an assumption. -/
theorem compileCallback_sound (construct : Nat → Value → Value → Value)
    (captures : List Value) (callback : Callback Value) (plan : CallbackPlan Value)
    (admitted : compileCallback captures callback = some plan) (argument : Value) :
    evalCallback construct captures argument callback = .done [plan.run construct argument] [] := by
  induction callback generalizing plan with
  | argument =>
      simp only [compileCallback, Option.some.injEq] at admitted
      subst plan
      rfl
  | captured slot =>
      cases found : captures[slot]? with
      | none => simp [compileCallback, found] at admitted
      | some value =>
          simp only [compileCallback, found, Option.map_some, Option.some.injEq] at admitted
          subst plan
          simp [evalCallback, found, CallbackPlan.run]
  | value value =>
      simp only [compileCallback, Option.some.injEq] at admitted
      subst plan
      rfl
  | constructor tag left right leftIH rightIH =>
      cases first : compileCallback captures left with
      | none => simp [compileCallback, first] at admitted
      | some firstPlan =>
          cases second : compileCallback captures right with
          | none => simp [compileCallback, first, second] at admitted
          | some secondPlan =>
              simp [compileCallback, first, second] at admitted
              subst plan
              simp [evalCallback, leftIH _ first, rightIH _ second, CallbackPlan.run]
  | fail => simp [compileCallback] at admitted
  | choice _ _ _ _ => simp [compileCallback] at admitted
  | effect _ _ _ => simp [compileCallback] at admitted
  | loop => simp [compileCallback] at admitted

theorem compileClosure_sound (construct : Nat → Value → Value → Value)
    (closure : Closure Value) (plan : CallbackPlan Value)
    (admitted : compileClosure closure = some plan) (argument : Value) :
    evalClosure construct closure argument = .done [plan.run construct argument] [] :=
  compileCallback_sound construct closure.captures closure.body plan admitted argument

/-- Eager relational map constructs every complete result list. -/
def eagerMap (callback : Value → Execution Value) : List Value → Execution (List Value)
  | [] => .done [[]] []
  | first :: rest => .product List.cons (callback first) (eagerMap callback rest)

theorem eagerMap_single (callback : Value → Execution Value) (f : Value → Value)
    (single : ∀ value, callback value = .done [f value] []) (items : List Value) :
    eagerMap callback items = .done [items.map f] [] := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [eagerMap, single, ih]

/-- This collection grammar is independent of the machine's continuation
representation. `down` recurses structurally on a natural-number input. -/
inductive Source (Value : Type u) where
  | flat (items : List Value)
  | cons (head : Value) (tail : Source Value)
  | append (left right : Source Value)
  | map (callback : Closure Value) (items : Source Value)
  | down (count : Nat)
deriving Repr

def descending (number : Nat → Value) : Nat → List Value
  | 0 => []
  | count + 1 => number (count + 1) :: descending number count

def eager (construct : Nat → Value → Value → Value) (number : Nat → Value) :
    Source Value → Execution (List Value)
  | .flat items => .done [items] []
  | .cons head tail => .map (head :: ·) (eager construct number tail)
  | .append left right =>
      .product List.append (eager construct number left) (eager construct number right)
  | .map callback items =>
      .bind (eager construct number items) (eagerMap (evalClosure construct callback))
  | .down count => .done [descending number count] []

inductive Plan (Value : Type u) where
  | flat (items : List Value)
  | cons (head : Value) (tail : Plan Value)
  | append (left right : Plan Value)
  | map (callback : CallbackPlan Value) (items : Plan Value)
  | down (count : Nat)
deriving Repr

def lower : Source Value → Option (Plan Value)
  | .flat items => some (.flat items)
  | .cons head tail => (lower tail).map (.cons head)
  | .append left right => do
      let first ← lower left
      let second ← lower right
      pure (.append first second)
  | .map callback items => do
      let body ← compileClosure callback
      let source ← lower items
      pure (.map body source)
  | .down count => some (.down count)

/-- Extensional meaning of a plan, used only in proofs. `pull` below does not
call this function or materialize its list. -/
def Plan.materialize (construct : Nat → Value → Value → Value) (number : Nat → Value) :
    Plan Value → List Value
  | .flat items => items
  | .cons head tail => head :: tail.materialize construct number
  | .append left right => left.materialize construct number ++ right.materialize construct number
  | .map callback items => (items.materialize construct number).map fun v => callback.run construct v
  | .down count => descending number count

theorem lower_sound (construct : Nat → Value → Value → Value) (number : Nat → Value)
    (source : Source Value) (plan : Plan Value) (admitted : lower source = some plan) :
    eager construct number source = .done [plan.materialize construct number] [] := by
  induction source generalizing plan with
  | flat items =>
      simp only [lower, Option.some.injEq] at admitted
      subst plan
      rfl
  | cons head tail ih =>
      cases lowered : lower tail with
      | none => simp [lower, lowered] at admitted
      | some tailPlan =>
          simp only [lower, lowered, Option.map_some, Option.some.injEq] at admitted
          subst plan
          simp [eager, ih _ lowered, Plan.materialize]
  | append left right leftIH rightIH =>
      cases first : lower left with
      | none => simp [lower, first] at admitted
      | some firstPlan =>
          cases second : lower right with
          | none => simp [lower, first, second] at admitted
          | some secondPlan =>
              simp [lower, first, second] at admitted
              subst plan
              simp [eager, leftIH _ first, rightIH _ second, Plan.materialize]
  | map callback items ih =>
      cases compiled : compileClosure callback with
      | none => simp [lower, compiled] at admitted
      | some body =>
          cases lowered : lower items with
          | none => simp [lower, compiled, lowered] at admitted
          | some itemsPlan =>
              simp [lower, compiled, lowered] at admitted
              subst plan
              simp only [eager, ih _ lowered, Execution.bind_done_single, Plan.materialize]
              exact eagerMap_single _ _ (compileClosure_sound construct callback body compiled) _
  | down count =>
      simp only [lower, Option.some.injEq] at admitted
      subst plan
      rfl

/-- Pending maps are applied from the innermost source map outwards. -/
def runCallbacks (construct : Nat → Value → Value → Value) :
    List (CallbackPlan Value) → Value → Value
  | [], value => value
  | callback :: rest, value => runCallbacks construct rest (callback.run construct value)

/-- A frame holds collection code and its enclosing map continuations. -/
abbrev Frame (Value : Type u) := Plan Value × List (CallbackPlan Value)

abbrev Stack (Value : Type u) := List (Frame Value)

def Plan.weight : Plan Value → Nat
  | .flat items => items.length + 1
  | .cons _ tail => tail.weight + 1
  | .append left right => left.weight + right.weight + 1
  | .map _ items => items.weight + 1
  | .down count => count + 1

def stackWeight : Stack Value → Nat
  | [] => 0
  | (plan, _) :: rest => plan.weight + stackWeight rest

/-- Demand one occurrence. Administrative instructions only rearrange plan
frames; neither this function nor its callback runner builds an intermediate
collection spine. Its decreasing weight includes a structurally recursive
range, so finite traces are established from code rather than postulated. -/
def pull (construct : Nat → Value → Value → Value) (number : Nat → Value) :
    Stack Value → PullStep Value (Stack Value)
  | [] => .finish []
  | (.flat [], _) :: rest => pull construct number rest
  | (.flat (value :: items), callbacks) :: rest =>
      .yield (runCallbacks construct callbacks value) ((.flat items, callbacks) :: rest)
  | (.cons value tail, callbacks) :: rest =>
      .yield (runCallbacks construct callbacks value) ((tail, callbacks) :: rest)
  | (.append left right, callbacks) :: rest =>
      pull construct number ((left, callbacks) :: (right, callbacks) :: rest)
  | (.map callback items, callbacks) :: rest =>
      pull construct number ((items, callback :: callbacks) :: rest)
  | (.down 0, _) :: rest => pull construct number rest
  | (.down (count + 1), callbacks) :: rest =>
      .yield (runCallbacks construct callbacks (number (count + 1)))
        ((.down count, callbacks) :: rest)
termination_by state => stackWeight state
decreasing_by all_goals simp [stackWeight, Plan.weight] <;> omega

/-- Extensional observation of all pending frames, not used by execution. -/
def denoteStack (construct : Nat → Value → Value → Value) (number : Nat → Value) :
    Stack Value → List Value
  | [] => []
  | (plan, callbacks) :: rest =>
      (plan.materialize construct number).map (runCallbacks construct callbacks) ++
        denoteStack construct number rest

/-- One independently executed machine step exposes exactly the first pending
occurrence, or terminates with an empty suffix. It never declines after checked
lowering has eliminated the unsupported callback forms. -/
theorem pull_spec (construct : Nat → Value → Value → Value) (number : Nat → Value)
    (state : Stack Value) :
    match pull construct number state with
    | .yield item next =>
        denoteStack construct number state = item :: denoteStack construct number next
    | .finish suffix => denoteStack construct number state = suffix ∧ suffix = []
    | .decline => False := by
  fun_induction pull construct number state <;>
    simp_all [denoteStack, Plan.materialize, descending,
      runCallbacks, List.map_append, List.map_map, Function.comp_def, List.append_assoc]

/-- The grammar itself supplies a complete finite pull trace. The trace uses
one transition per yielded occurrence and one terminal transition. -/
theorem produces (construct : Nat → Value → Value → Value) (number : Nat → Value)
    (state : Stack Value) :
    Produces (pull construct number) state (denoteStack construct number state)
      ((denoteStack construct number state).length + 1) := by
  have spec := pull_spec construct number state
  cases observed : pull construct number state with
  | decline => simp [observed] at spec
  | finish suffix =>
      simp only [observed] at spec
      have empty : denoteStack construct number state = [] := spec.1.trans spec.2
      rw [empty]
      exact Produces.finish (by simpa [spec.2] using observed)
  | yield item next =>
      simp only [observed] at spec
      rw [spec]
      exact Produces.yield observed (produces construct number next)
termination_by (denoteStack construct number state).length
decreasing_by
  simp only [observed] at spec
  have lengths := congrArg List.length spec
  simp only [List.length_cons] at lengths
  omega

/-- A bounded consumer checks zero before asking the producer for a step.
Exactly reaching the bound never inspects the continuation. -/
def takePrefix (construct : Nat → Value → Value → Value) (number : Nat → Value) :
    Nat → Stack Value → Option (List Value)
  | 0, _ => some []
  | bound + 1, state =>
      match pull construct number state with
      | .decline => none
      | .finish suffix => some (suffix.take (bound + 1))
      | .yield item next => (takePrefix construct number bound next).map (item :: ·)

theorem takePrefix_refines_take (construct : Nat → Value → Value → Value)
    (number : Nat → Value) (bound : Nat) (state : Stack Value) :
    takePrefix construct number bound state =
      some ((denoteStack construct number state).take bound) := by
  induction bound generalizing state with
  | zero => rfl
  | succ bound ih =>
      have spec := pull_spec construct number state
      cases observed : pull construct number state with
      | decline => simp [observed] at spec
      | finish suffix =>
          simp only [observed] at spec
          simp [takePrefix, observed, spec.1]
      | yield item next =>
          simp only [observed] at spec
          simp [takePrefix, observed, spec, ih]

@[simp] theorem denote_initial (construct : Nat → Value → Value → Value)
    (number : Nat → Value) (plan : Plan Value) :
    denoteStack construct number [(plan, [])] = plan.materialize construct number := by
  simp [denoteStack, runCallbacks]

/-- Whole eager execution followed by the bounded value-enumeration observer.
Zero is handled at the enclosing control boundary, before entering the body. -/
def eagerPrefix (construct : Nat → Value → Value → Value) (number : Nat → Value) :
    Nat → Source Value → Execution Value
  | 0, _ => .done [] []
  | bound + 1, source =>
      match eager construct number source with
      | .diverges => .diverges
      | .done collections events =>
          .done ((collections.flatMap id).take (bound + 1)) events

theorem eagerPrefix_of_admitted (construct : Nat → Value → Value → Value)
    (number : Nat → Value) (source : Source Value) (plan : Plan Value)
    (admitted : lower source = some plan) (bound : Nat) :
    eagerPrefix construct number bound source =
      .done ((plan.materialize construct number).take bound) [] := by
  cases bound <;> simp [eagerPrefix, lower_sound construct number source plan admitted]

/-- Checked source-to-producer lowering preserves the requested ordered
occurrence prefix. This includes duplicates and every finite structural range;
source termination and callback singleness are conclusions of admission. -/
theorem lower_bounded_correct (construct : Nat → Value → Value → Value)
    (number : Nat → Value) (source : Source Value) (plan : Plan Value)
    (admitted : lower source = some plan) (bound : Nat) :
    eagerPrefix construct number bound source =
        .done ((plan.materialize construct number).take bound) [] ∧
      takePrefix construct number bound [(plan, [])] =
        some ((plan.materialize construct number).take bound) := by
  constructor
  · exact eagerPrefix_of_admitted construct number source plan admitted bound
  · simpa using takePrefix_refines_take construct number bound [(plan, [])]

/-- The existing pull/fold representation theorem is now instantiated by a
trace proved from compiled code, rather than a caller-supplied trace premise. -/
theorem lowered_fold_correct {Accumulator : Type u}
    (construct : Nat → Value → Value → Value) (number : Nat → Value)
    (combine : Accumulator → Value → Accumulator) (plan : Plan Value)
    (initial : Accumulator) :
    pullFold (pull construct number) (totalConsumer combine)
        ((plan.materialize construct number).length + 1) [(plan, [])] initial =
      .commit ((plan.materialize construct number).foldl combine initial) := by
  simpa using pullFold_refines_foldl (pull construct number) combine
    (produces construct number [(plan, [])]) initial

theorem zero_bound_no_body (construct : Nat → Value → Value → Value)
    (number : Nat → Value) (source : Source Value) (state : Stack Value) :
    eagerPrefix construct number 0 source = .done [] [] ∧
      takePrefix construct number 0 state = some [] := by
  exact ⟨rfl, rfl⟩

theorem exact_bound_no_lookahead (construct : Nat → Value → Value → Value)
    (number : Nat → Value) (state next : Stack Value) (item : Value)
    (step : pull construct number state = .yield item next) :
    takePrefix construct number 1 state = some [item] := by
  simp [takePrefix, step]

/-- Producer requests made by the bounded consumer. This counts abstract pull
requests, not the administrative plan instructions or callback work within one
request, and is not a native instruction or wall-time bound. -/
def pullRequests (construct : Nat → Value → Value → Value) (number : Nat → Value) :
    Nat → Stack Value → Nat
  | 0, _ => 0
  | bound + 1, state =>
      match pull construct number state with
      | .yield _ next => 1 + pullRequests construct number bound next
      | .finish _ | .decline => 1

theorem pullRequests_exact (construct : Nat → Value → Value → Value)
    (number : Nat → Value) (bound : Nat) (state : Stack Value) :
    pullRequests construct number bound state =
      min bound ((denoteStack construct number state).length + 1) := by
  induction bound generalizing state with
  | zero => simp [pullRequests]
  | succ bound ih =>
      have spec := pull_spec construct number state
      cases observed : pull construct number state with
      | decline => simp [observed] at spec
      | finish suffix =>
          simp only [observed] at spec
          simp [pullRequests, observed, spec.1, spec.2]
      | yield item next =>
          simp only [observed] at spec
          simp only [pullRequests, observed, ih, spec, List.length_cons]
          omega

/-! ## Adapter obligations

The proved producer exposes values. PeTTa member enumeration at a value
boundary has this reading. An adapter which evaluates each element (including
authored PeTTa disjunctions and relevant HE paths) is a different observation.
The adapter equality below requires inert elements; it is not inferred from
surface spelling or a dialect-wide assertion.
-/

def evaluateElements (evaluate : Value → List Value) (items : List Value) : List Value :=
  items.flatMap evaluate

theorem evaluated_elements_agree_of_inert (evaluate : Value → List Value)
    (items : List Value) (inert : ∀ value ∈ items, evaluate value = [value]) :
    evaluateElements evaluate items = SuperposeFusion.answers items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      have firstInert := inert first (by simp)
      have restInert : ∀ value ∈ rest, evaluate value = [value] :=
        fun value member => inert value (by simp [member])
      simpa [evaluateElements, SuperposeFusion.answers, firstInert] using ih restInert

/-- The independently defined eager map has precisely the relational product
semantics of `SuperposeFusion.mapAtom` on pure finite callback answers. -/
theorem eagerMap_pure_product (callback : Value → List Value) (items : List Value) :
    eagerMap (fun value => .done (callback value) []) items =
      .done (SuperposeFusion.mapAtom callback items) [] := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [eagerMap, ih, Execution.product, SuperposeFusion.mapAtom]

namespace Controls

/-- Arithmetic here only makes the constructed data easy to inspect; the
general theorem admits arbitrary total data-constructor interpretations. -/
def combine (tag left right : Nat) : Nat := tag + left + right

def capturedOffset : Closure Nat :=
  ⟨.constructor 0 .argument (.captured 0), [10]⟩

def mixedSource : Source Nat :=
  .append (.cons 7 (.flat [7])) (.map capturedOffset (.down 3))

def mixedPlan : Plan Nat :=
  .append (.cons 7 (.flat [7]))
    (.map (.constructor 0 .argument (.value 10)) (.down 3))

theorem captured_source_admitted : lower mixedSource = some mixedPlan := rfl

theorem eager_captured_source :
    eager combine id mixedSource = .done [[7, 7, 13, 12, 11]] [] := by decide

theorem pull_preserves_duplicates_and_capture :
    takePrefix combine id 4 [(mixedPlan, [])] = some [7, 7, 13, 12] := by
  simp [takePrefix, pull, mixedPlan, runCallbacks, CallbackPlan.run, combine]

theorem full_collection_and_fold :
    takePrefix combine id 20 [(mixedPlan, [])] = some [7, 7, 13, 12, 11] ∧
      pullFold (pull combine id) (totalConsumer Nat.add) 6 [(mixedPlan, [])] 0 =
        .commit 50 := by
  constructor
  · simp [takePrefix_refines_take, mixedPlan, Plan.materialize, descending,
      CallbackPlan.run, combine]
  · simpa [mixedPlan, Plan.materialize, descending, CallbackPlan.run, combine] using
      lowered_fold_correct combine id Nat.add mixedPlan 0

theorem bounded_requests_stop_exactly :
    pullRequests combine id 0 [(mixedPlan, [])] = 0 ∧
      pullRequests combine id 4 [(mixedPlan, [])] = 4 ∧
      pullRequests combine id 5 [(mixedPlan, [])] = 5 ∧
      pullRequests combine id 20 [(mixedPlan, [])] = 6 := by
  simp [pullRequests_exact, mixedPlan, Plan.materialize, descending,
    CallbackPlan.run, combine]

theorem unresolved_capture_rejected :
    compileClosure (⟨.captured 1, [10]⟩ : Closure Nat) = none := rfl

theorem unsafe_callbacks_rejected :
    compileCallback ([] : List Nat) .fail = none ∧
      compileCallback ([] : List Nat) (.choice .argument .argument) = none ∧
      compileCallback ([] : List Nat) (.effect 9 .argument) = none ∧
      compileCallback ([] : List Nat) .loop = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def lateFailure : Source Nat :=
  .append (.flat [1]) (.map ⟨.fail, []⟩ (.flat [2]))

/-- Returning the first left-hand value before completing an eager collection
is unsound when a later required mapper application fails. -/
theorem late_failure_cancels_collection :
    eagerPrefix combine id 1 lateFailure = .done [] [] ∧
      eagerPrefix combine id 1 lateFailure ≠ .done [1] [] ∧
      lower lateFailure = none := by decide

def lateChoice : Source Nat :=
  .map ⟨.choice .argument (.constructor 0 .argument (.value 10)), []⟩ (.flat [1, 2])

/-- Eager relational map duplicates preceding occurrences for each complete
choice of mapped results. A flatMap replacement has different multiplicity. -/
theorem nondeterministic_map_is_not_stream_flatMap :
    eagerPrefix combine id 20 lateChoice = .done [1, 2, 1, 12, 11, 2, 11, 12] [] ∧
      ([1, 2] : List Nat).flatMap (fun x => [x, x + 10]) = [1, 11, 2, 12] ∧
      lower lateChoice = none := by decide

def lateEffect : Source Nat :=
  .append (.flat [1]) (.map ⟨.effect 9 .argument, []⟩ (.flat [2]))

theorem early_return_would_omit_late_effect :
    eagerPrefix combine id 1 lateEffect = .done [1] [9] ∧
      eagerPrefix combine id 1 lateEffect ≠ .done [1] [] ∧
      lower lateEffect = none := by decide

def lateLoop : Source Nat :=
  .append (.flat [1]) (.map ⟨.loop, []⟩ (.flat [2]))

theorem early_return_would_hide_late_divergence :
    eagerPrefix combine id 1 lateLoop = .diverges ∧
      eagerPrefix combine id 1 lateLoop ≠ .done [1] [] ∧
      lower lateLoop = none := by decide

theorem zero_bound_avoids_divergent_body :
    eagerPrefix combine id 0 lateLoop = .done [] [] := rfl

/-- The checker is deliberately conservative: even an unreachable looping
mapper is rejected. This is a decidable sufficient fragment, not a purported
complete decision procedure for semantic termination. -/
theorem conservative_admission_is_not_termination_decision :
    eager combine id (.map ⟨.loop, []⟩ (.flat [])) = .done [[]] [] ∧
      lower (Value := Nat) (.map ⟨.loop, []⟩ (.flat [])) = none := by decide

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
  (evalCode evalIn choices finish)

def callValue : Atom := .expression [.symbol "foo"]

def atomConstructor (tag : Nat) (left right : Atom) : Atom :=
  .expression [.grounded (.int tag), left, right]

def capturedCall : Closure Atom := ⟨.captured 0, [callValue]⟩

theorem captured_call_remains_value :
    evalClosure atomConstructor capturedCall (.symbol "unused") = .done [callValue] [] ∧
      compileClosure capturedCall = some (.value callValue) := by
  exact ⟨rfl, rfl⟩

theorem value_and_evaluating_adapters_differ :
    SuperposeFusion.answers [callValue] = [callValue] ∧
      evaluateElements
        (evalCode Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences.Examples.callsSymbols)
        [callValue] = [.grounded (.int 42)] := by
  constructor
  · rfl
  · simp [evaluateElements, evalIn, evalIn.evalList, choices, finish, callValue,
      Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences.Examples.callsSymbols]

end Controls

end Mettapedia.Machines.FiniteProducerLowering
