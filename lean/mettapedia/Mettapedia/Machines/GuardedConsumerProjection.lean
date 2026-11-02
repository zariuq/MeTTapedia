import Mettapedia.Machines.GuardConjunctionCompiler

/-!
# Complete support for guarded, effectful consumers

Projection retains the bindings used by every guard, effect argument and
answer template. A finite capture stores those coordinates only. Restoring
arbitrary values elsewhere preserves the full execution: answers with their
multiplicity, ordered query reads, ordered effect calls, partial world changes
on failure, and completion status.

Guard atoms and effects are resolved operations interpreted by the supplied
semantics, not recognized by source spelling. Support extraction from native
terms, type profiles and hidden host dependencies remains a separate boundary.
The computed static support is sufficient, not asserted minimal.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GuardedConsumerProjection

open GuardConjunctionCompiler

variable {Var Value Operation Effect World Fault : Type}

inductive Operand (Var Value : Type) where
  | literal (value : Value)
  | slot (name : Var)
  deriving DecidableEq

def Operand.support : Operand Var Value → List Var
  | .literal _ => []
  | .slot name => [name]

def Operand.eval (bindings : Var → Value) : Operand Var Value → Value
  | .literal value => value
  | .slot name => bindings name

def argumentSupport (args : List (Operand Var Value)) : List Var := args.flatMap Operand.support
def arguments (bindings : Var → Value) (args : List (Operand Var Value)) : List Value :=
  args.map (Operand.eval bindings)

abbrev Call (Operation Var Value : Type) := Operation × List (Operand Var Value)
abbrev ResolvedCall (Operation Value : Type) := Operation × List Value

def resolve (bindings : Var → Value) (call : Call Operation Var Value) : ResolvedCall Operation Value :=
  (call.1, arguments bindings call.2)

def guardSupport : Guard (Call Operation Var Value) → List Var
  | .constant _ => []
  | .atom call => argumentSupport call.2
  | .neg body => guardSupport body
  | .both left right | .either left right => guardSupport left ++ guardSupport right

def instantiate (bindings : Var → Value) : Guard (Call Operation Var Value) → Guard (ResolvedCall Operation Value)
  | .constant value => .constant value
  | .atom call => .atom (resolve bindings call)
  | .neg body => .neg (instantiate bindings body)
  | .both left right => .both (instantiate bindings left) (instantiate bindings right)
  | .either left right => .either (instantiate bindings left) (instantiate bindings right)

abbrev Agrees (left right : Var → Value) (needed : List Var) : Prop :=
  ∀ name ∈ needed, left name = right name

theorem agrees_append (left right : Var → Value) (first second : List Var) :
    Agrees left right (first ++ second) ↔ Agrees left right first ∧ Agrees left right second := by
  simp only [Agrees, List.mem_append, or_imp, forall_and]

theorem operand_congr (left right : Var → Value) (operand : Operand Var Value)
    (agree : Agrees left right operand.support) : operand.eval left = operand.eval right := by
  cases operand with
  | literal value => rfl
  | slot name => exact agree name (by simp [Operand.support])

theorem arguments_congr (left right : Var → Value) (args : List (Operand Var Value))
    (agree : Agrees left right (argumentSupport args)) : arguments left args = arguments right args := by
  apply List.map_congr_left
  intro operand member
  exact operand_congr left right operand (fun name hn =>
    agree name (List.mem_flatMap.mpr ⟨operand, member, hn⟩))

theorem instantiate_congr (left right : Var → Value) (guard : Guard (Call Operation Var Value))
    (agree : Agrees left right (guardSupport guard)) : instantiate left guard = instantiate right guard := by
  induction guard with
  | constant value => rfl
  | atom call =>
      have args := arguments_congr left right call.2 agree
      simp only [instantiate, resolve, args]
  | neg body ih => exact congrArg Guard.neg (ih agree)
  | both a b iha ihb =>
      obtain ⟨ha, hb⟩ := (agrees_append left right _ _).mp agree
      exact congrArg₂ Guard.both (iha ha) (ihb hb)
  | either a b iha ihb =>
      obtain ⟨ha, hb⟩ := (agrees_append left right _ _).mp agree
      exact congrArg₂ Guard.either (iha ha) (ihb hb)

inductive Completion (Fault : Type) where
  | complete
  | fault (reason : Fault)
  | unavailable
  deriving DecidableEq

inductive Consumer (Operation Effect Var Value : Type) where
  | answer (templates : List (List (Operand Var Value)))
  | effect (operation : Effect) (args : List (Operand Var Value))
      (next : Consumer Operation Effect Var Value)
  | branch (guard : Guard (Call Operation Var Value))
      (yes no : Consumer Operation Effect Var Value)

def support : Consumer Operation Effect Var Value → List Var
  | .answer templates => templates.flatMap argumentSupport
  | .effect _ args next => argumentSupport args ++ support next
  | .branch guard yes no => guardSupport guard ++ (support yes ++ support no)

structure Outcome (Operation Effect Value World Fault : Type) where
  answers : List (List Value)
  world : World
  queries : ReadOnlyQuery.Reads (ResolvedCall Operation Value) (Verdict Fault)
  effects : List (Effect × List Value)
  completion : Completion Fault

structure Semantics (Operation Effect Value World Fault : Type) where
  query : World → ResolvedCall Operation Value → Verdict Fault
  action : Effect → List Value → World → World × Completion Fault

def execute (semantics : Semantics Operation Effect Value World Fault) (bindings : Var → Value) :
    Consumer Operation Effect Var Value → World → Outcome Operation Effect Value World Fault
  | .answer templates, world => ⟨templates.map (arguments bindings), world, [], [], .complete⟩
  | .effect operation args next, world =>
      let values := arguments bindings args
      let changed := semantics.action operation values world
      match changed.2 with
      | .complete =>
          let later := execute semantics bindings next changed.1
          { later with effects := (operation, values) :: later.effects }
      | stop => ⟨[], changed.1, [], [(operation, values)], stop⟩
  | .branch guard yes no, world =>
      let observed := evaluate (semantics.query world) (instantiate bindings guard)
      match observed.answer with
      | .boolean selected =>
          let later := if selected then execute semantics bindings yes world
            else execute semantics bindings no world
          { later with queries := observed.reads ++ later.queries }
      | .fault reason => ⟨[], world, observed.reads, [], .fault reason⟩
      | .unavailable => ⟨[], world, observed.reads, [], .unavailable⟩

/-- Guard variables are part of the support even when neither effects nor
answer templates contain them. The equality includes every observable field. -/
theorem execute_congr (semantics : Semantics Operation Effect Value World Fault)
    (program : Consumer Operation Effect Var Value) (left right : Var → Value)
    (agree : Agrees left right (support program)) (world : World) :
    execute semantics left program world = execute semantics right program world := by
  induction program generalizing world with
  | answer templates =>
      have equal : templates.map (arguments left) = templates.map (arguments right) := by
        apply List.map_congr_left
        intro args member
        exact arguments_congr left right args (fun name hn =>
          agree name (List.mem_flatMap.mpr ⟨args, member, hn⟩))
      simp only [execute, equal]
  | effect operation args next ih =>
      obtain ⟨ha, hn⟩ := (agrees_append left right _ _).mp agree
      have equal := arguments_congr left right args ha
      simp only [execute, equal]
      cases performed : semantics.action operation (arguments right args) world with
      | mk changed stop =>
          cases stop <;> simp only [ih hn]
  | branch guard yes no ihy ihn =>
      obtain ⟨hg, rest⟩ := (agrees_append left right _ _).mp agree
      obtain ⟨hy, hn⟩ := (agrees_append left right _ _).mp rest
      have equal := instantiate_congr left right guard hg
      simp only [execute, equal]
      cases answer : (evaluate (semantics.query world) (instantiate right guard)).answer with
      | boolean value => cases value <;> simp only [Bool.false_eq_true, ↓reduceIte, ihy hy, ihn hn]
      | fault reason => rfl
      | unavailable => rfl

def capture (needed : List Var) (bindings : Var → Value) : List (Var × Value) :=
  needed.map (fun name => (name, bindings name))

def restore [DecidableEq Var] (captured : List (Var × Value)) (defaultValue : Var → Value) : Var → Value :=
  fun name => (captured.lookup name).getD (defaultValue name)

theorem lookup_capture [DecidableEq Var] (needed : List Var) (bindings : Var → Value)
    (name : Var) (present : name ∈ needed) : (capture needed bindings).lookup name = some (bindings name) := by
  induction needed with
  | nil => simp at present
  | cons first rest ih =>
      by_cases same : name = first
      · subst name; simp [capture]
      · have later : name ∈ rest := (List.mem_cons.mp present).resolve_left same
        have different : (name == first) = false := by simpa only [beq_eq_false_iff_ne] using same
        simpa [capture, List.lookup_cons, different] using ih later

theorem capture_sufficient [DecidableEq Var] (needed : List Var) (bindings fallback : Var → Value) :
    Agrees bindings (restore (capture needed bindings) fallback) needed := by
  intro name present
  simp [restore, lookup_capture needed bindings name present]

/-- The packed binding capture is an actual finite list; omitted values
can be arbitrary without changing the consumer's complete execution. -/
theorem execute_projected [DecidableEq Var]
    (semantics : Semantics Operation Effect Value World Fault)
    (program : Consumer Operation Effect Var Value) (bindings fallback : Var → Value) (world : World) :
    execute semantics (restore (capture (support program) bindings) fallback) program world =
      execute semantics bindings program world :=
  (execute_congr semantics program bindings _ (capture_sufficient _ bindings fallback) world).symm

namespace Controls

def semantics : Semantics Unit Unit Nat Nat Nat where
  query := fun _ call => .boolean (call.2 == [1])
  action := fun _ _ world => (world + 1, .complete)

def guarded : Consumer Unit Unit Nat Nat :=
  .branch (.atom ((), [.slot 7]))
    (.effect () [] (.answer [[.literal 10]])) (.answer [])

theorem guard_only_variable_cannot_be_dropped :
    (execute semantics (fun _ => 1) guarded 0).world = 1 ∧
    (execute semantics (fun _ => 0) guarded 0).world = 0 := by decide

theorem empty_branch_contributes_no_answer :
    (execute semantics (fun _ => 0) guarded 0).answers.length = 0 := by decide

theorem duplicate_answers_remain_distinct :
    (execute semantics (fun _ : Nat => 0) (.answer [[.literal 4], [.literal 4]]) 0).answers.length = 2 := by decide

def partialFault : Semantics Unit Unit Nat Nat Nat where
  query := fun _ _ => .boolean true
  action := fun _ _ world => (world + 1, .fault 9)

theorem failed_action_keeps_partial_world :
    (execute partialFault (fun _ : Nat => 0) (.effect () [] (.answer [[.literal 4]])) 0).world = 1 ∧
    (execute partialFault (fun _ : Nat => 0) (.effect () [] (.answer [[.literal 4]])) 0).completion = .fault 9 := by decide

def worldQuery : Semantics Unit Unit Nat Bool Nat where
  query := fun world _ => .boolean world
  action := fun _ _ world => (world, .complete)

def noBindingGuard : Consumer Unit Unit Nat Nat :=
  .branch (.atom ((), [])) (.answer [[.literal 1]]) (.answer [])

/-- An empty binding support does not mean an answer is independent of the
world or may be memoized without validating the query dependencies. -/
theorem projection_is_not_a_complete_cache_key :
    support noBindingGuard = [] ∧
    (execute worldQuery (fun _ => 0) noBindingGuard false).answers ≠
      (execute worldQuery (fun _ => 0) noBindingGuard true).answers := by decide

def argumentEffect : Semantics Unit Unit Nat Nat Nat where
  query := fun _ _ => .boolean true
  action := fun _ values world => (world + values.sum, .complete)

theorem same_answers_do_not_license_dropping_effect_arguments :
    let program : Consumer Unit Unit Nat Nat := .effect () [.slot 3] (.answer [])
    (execute argumentEffect (fun _ => 1) program 0).answers =
      (execute argumentEffect (fun _ => 2) program 0).answers ∧
    (execute argumentEffect (fun _ => 1) program 0).world ≠
      (execute argumentEffect (fun _ => 2) program 0).world := by decide

end Controls

#print axioms instantiate_congr
#print axioms execute_congr
#print axioms execute_projected

end Mettapedia.Machines.GuardedConsumerProjection
