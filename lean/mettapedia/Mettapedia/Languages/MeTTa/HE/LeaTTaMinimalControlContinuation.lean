import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution

/-!
# Continuation-preserving arithmetic and guard execution

These laws execute the existing interpreter's control prefixes. They retain
the surrounding stack, work queue, accumulated answers and binding frame, so
the resulting computation can be used inside a larger generated function.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution

open Metta Metta.Minimal
open FuelConvergenceInterpreter

theorem atomToStack_length (atom : Atom) (continuation : Stack) :
    continuation.length < (atomToStack atom continuation).length := by
  fun_induction atomToStack atom continuation <;> simp_all <;> omega

theorem atomToStack_pending (atom : Atom) (parent : Frame) (continuation : Stack)
    (bindings : Metta.Bindings) :
    isFinal ⟨atomToStack atom (parent :: continuation), bindings⟩ = false := by
  have longer := atomToStack_length atom (parent :: continuation)
  generalize atomToStack atom (parent :: continuation) = stack at *
  cases stack with
  | nil => simp [isFinal]
  | cons top rest =>
      cases rest with
      | nil => simp at longer
      | cons next tail => rfl

/-- Native subtraction followed by `chain` substitutes its exact integer
result into the continuation. Every surrounding queue and result is retained. -/
theorem integer_subtraction_chain_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parent : Frame) (continuation : Stack)
    (name : String) (template : Atom) (left right : Int) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table) :
    let source := Atom.expr [.sym "eval",
      .expr [.sym "-", .gnd (.int left), .gnd (.int right)]]
    let body := Atom.expr [.sym "chain", source, .var name, template]
    interpretFuel environment (fuel + 3) state
        (⟨atomToStack body (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Subst.apply [(name, .gnd (.int (left - right)))] template)
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro source body
  let scope := chainFrameVars (parent :: continuation) source template
  let frame : Frame := { atom := body, ret := .chain, vars := scope }
  let start : Item := ⟨{ atom := source, vars := scope } ::
    frame :: parent :: continuation, bindings⟩
  let first := finItem (frame :: parent :: continuation)
    (.gnd (.int (left - right))) bindings
  let second : Item := ⟨{ atom := .expr [.sym "chain", .gnd (.int (left - right)),
    .var name, template], ret := .chain, vars := scope } :: parent :: continuation, bindings⟩
  let third : Item := ⟨atomToStack
    (Subst.apply [(name, .gnd (.int (left - right)))] template)
    (parent :: continuation), bindings⟩
  have initial : atomToStack body (parent :: continuation) = start.stack := by
    simp [body, source, start, frame, scope, atomToStack, varsCopy, chainFrameVars]
  have firstStep (budget : Nat) :
      interpretStack1 environment budget state start = ([first], state) := by
    dsimp only [start, source]
    rw [step_eval]
    simpa [first] using evalOp_integer_subtraction environment state
      (frame :: parent :: continuation) bindings left right groundings
  have secondStep (budget : Nat) :
      interpretStack1 environment budget state first = ([second], state) := by
    simpa [first, second, frame, body, instantiate, Bindings.resolveAtom] using
      step_chain_result environment budget state (parent :: continuation) scope source
        (.gnd (.int (left - right))) template name bindings
  have thirdStep (budget : Nat) :
      interpretStack1 environment budget state second = ([third], state) := by
    exact step_chain_apply environment budget state (parent :: continuation) scope
      (.gnd (.int (left - right))) template name bindings
  rw [initial]
  change interpretFuel environment (fuel + 3) state (start :: rest) done = _
  rw [driver_singleton_step environment (fuel + 2) state state start first rest done
    (firstStep _) (by rfl)]
  rw [driver_singleton_step environment (fuel + 1) state state first second rest done
    (secondStep _) (by rfl)]
  exact driver_singleton_step environment fuel state state second third rest done
    (thirdStep _) (atomToStack_pending _ _ _ _)

/-- A nonzero integer guard selects only its fallback. The equation exposes
the actual substituted fallback and the retained function frame; it does not
assume that the selected body has already executed. -/
theorem integer_nonzero_guard_selects_in_frame (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom)
    (amount : Int) (fuel : Nat) (parent : Frame) (continuation : Stack)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table) (nonzero : amount ≠ 0) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int amount), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack body (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation)
          (Subst.apply [(name, .gnd (.bool false))] otherwise) bindings :: rest) done := by
  intro equality template body
  let scope := chainFrameVars (parent :: continuation) equality template
  let start : Item := ⟨{ atom := equality, vars := scope } ::
    { atom := body, ret := .chain, vars := scope } :: parent :: continuation, bindings⟩
  let first := finItem ({ atom := body, ret := .chain, vars := scope } ::
    parent :: continuation) (.gnd (.bool false)) bindings
  let second : Item := ⟨{ atom := .expr [.sym "chain", .gnd (.bool false), .var name, template], ret := .chain, vars := scope } :: parent :: continuation, bindings⟩
  let selected := Atom.expr [.sym "unify", .gnd (.bool false), .gnd (.bool true),
    .expr [.sym "return", .sym marker], Subst.apply [(name, .gnd (.bool false))] otherwise]
  let third : Item := ⟨atomToStack selected (parent :: continuation), bindings⟩
  let fourth := finItem (parent :: continuation)
    (Subst.apply [(name, .gnd (.bool false))] otherwise) bindings
  have initial : atomToStack body (parent :: continuation) = start.stack := by
    simp [body, equality, start, scope, atomToStack, varsCopy, chainFrameVars]
  have firstStep (budget : Nat) :
      interpretStack1 environment budget state start = ([first], state) := by
    dsimp only [start, equality]
    rw [step_eval]
    have refused : (amount == 0) = false := beq_eq_false_iff_ne.mpr nonzero
    simpa [first, refused] using evalOp_integer_equality environment state
      ({ atom := body, ret := .chain, vars := scope } :: parent :: continuation)
      bindings amount 0 groundings
  have secondStep (budget : Nat) :
      interpretStack1 environment budget state first = ([second], state) := by
    simpa [first, second, body, instantiate, Bindings.resolveAtom] using
      step_chain_result environment budget state (parent :: continuation) scope equality
        (.gnd (.bool false)) template name bindings
  have thirdStep (budget : Nat) :
      interpretStack1 environment budget state second = ([third], state) := by
    rw [show second = ⟨{ atom := .expr [.sym "chain", .gnd (.bool false), .var name, template], ret := .chain, vars := scope } :: parent :: continuation, bindings⟩ from rfl,
      step_chain_apply]
    simp [third, selected, template, Subst.apply, Subst.lookup]
  have fourthStep (budget : Nat) :
      interpretStack1 environment budget state third = ([fourth], state) := by
    simp only [third, selected, atomToStack, step_unify]
    exact congrArg (fun items => (items, state)) (unifyOp_false _ _ _ _)
  rw [initial]
  change interpretFuel environment (fuel + 4) state (start :: rest) done = _
  rw [driver_singleton_step environment (fuel + 3) state state start first rest done
    (firstStep _) (by rfl)]
  rw [driver_singleton_step environment (fuel + 2) state state first second rest done
    (secondStep _) (by rfl)]
  rw [driver_singleton_step environment (fuel + 1) state state second third rest done
    (thirdStep _) (by rfl)]
  exact driver_singleton_step environment fuel state state third fourth rest done
    (fourthStep _) (by rfl)

/-- A newly opened function uses the same nonzero guard transition. -/
theorem integer_nonzero_guard_selects (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom)
    (amount : Int) (fuel : Nat) (continuation : Stack)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table) (nonzero : amount ≠ 0) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int amount), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    let parent : Frame := { atom := .expr [.sym "function", body], ret := .function, vars := varsCopy continuation }
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack (.expr [.sym "function", body]) continuation, bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation)
          (Subst.apply [(name, .gnd (.bool false))] otherwise) bindings :: rest) done := by
  intro equality template body parent
  simpa only [body, equality, template, parent, atomToStack] using
    integer_nonzero_guard_selects_in_frame environment state bindings name marker otherwise
      amount fuel parent continuation rest done groundings nonzero

/-- A function resumes an embedded chain after resolving the incoming
bindings. Its local chain binder must remain a variable. -/
theorem step_function_chain (environment : MinEnv) (state : St) (fuel : Nat)
    (bindings : Metta.Bindings) (parentBody : Atom) (scope : List VarName)
    (continuation : Stack) (source template : Atom) (name : String)
    (fresh : instantiate bindings (.var name) = .var name) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretStack1 environment fuel state
        (finItem (parent :: continuation)
          (.expr [.sym "chain", source, .var name, template]) bindings) =
      ([⟨atomToStack
        (.expr [.sym "chain", instantiate bindings source, .var name,
          instantiate bindings template]) (parent :: continuation), bindings⟩], state) := by
  intro parent
  have fixed : Bindings.resolveAtom bindings (.var name) = .var name := fresh
  simp [interpretStack1, finItem, parent, instantiate, Bindings.resolveAtom,
    fixed, isEmbeddedOp]

theorem substitute_fresh (name : String) (value atom : Atom)
    (fresh : name ∉ atom.vars) : Subst.apply [(name, value)] atom = atom := by
  induction atom with
  | sym | gnd => simp [Subst.apply]
  | var other =>
      have different : other ≠ name := by simpa [Atom.vars, eq_comm] using fresh
      simp [Subst.apply, Subst.lookup, different]
  | expr items ih =>
      simp only [Subst.apply, Atom.expr.injEq]
      have untouched : ∀ child ∈ items, Subst.apply [(name, value)] child = child := by
        intro child member
        apply ih child member
        intro occurrence
        apply fresh
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, member, rfl⟩, occurrence⟩
      simpa using List.map_congr_left untouched

/-- The whole nonzero fuel prefix performs native comparison and subtraction,
then enters the materialized body with the decremented integer substituted.
Freshness is a syntactic side condition, independent of the body's behavior. -/
theorem integer_nonzero_guard_enters_in_frame (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (guard remaining marker : String) (body : Atom)
    (amount : Int) (fuel : Nat) (parentBody : Atom) (scope : List VarName) (continuation : Stack)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table) (nonzero : amount ≠ 0)
    (different : remaining ≠ guard) (privateGuard : guard ∉ body.vars)
    (privateRemaining : instantiate bindings (.var remaining) = .var remaining) :
    let subtraction := Atom.expr [.sym "eval",
      .expr [.sym "-", .gnd (.int amount), .gnd (.int 1)]]
    let fallback := Atom.expr [.sym "chain", subtraction, .var remaining, body]
    let equality := Atom.expr [.sym "eval",
      .expr [.sym "==", .gnd (.int amount), .gnd (.int 0)]]
    let guarded := Atom.expr [.sym "chain", equality, .var guard,
      .expr [.sym "unify", .var guard, .gnd (.bool true),
        .expr [.sym "return", .sym marker], fallback]]
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 8) state
        (⟨atomToStack guarded (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Subst.apply [(remaining, .gnd (.int (amount - 1)))]
          (instantiate bindings body)) (parent :: continuation), bindings⟩ :: rest) done := by
  intro subtraction fallback equality guarded parent
  have fallbackInert : Subst.apply [(guard, .gnd (.bool false))] fallback = fallback := by
    simp [fallback, subtraction, Subst.apply, Subst.lookup, different,
      substitute_fresh guard (.gnd (.bool false)) body privateGuard]
  have selection := integer_nonzero_guard_selects_in_frame environment state bindings guard marker
    fallback amount (fuel + 4) parent continuation rest done groundings nonzero
  change interpretFuel environment ((fuel + 4) + 4) state
    (⟨atomToStack guarded (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment (fuel + 4) state
        (finItem (parent :: continuation)
          (Subst.apply [(guard, .gnd (.bool false))] fallback) bindings :: rest) done at selection
  rw [fallbackInert] at selection
  rw [show fuel + 8 = (fuel + 4) + 4 by omega, selection]
  let opened : Item := ⟨atomToStack
    (.expr [.sym "chain", subtraction, .var remaining, instantiate bindings body])
    (parent :: continuation), bindings⟩
  have resume (budget : Nat) :
      interpretStack1 environment budget state (finItem (parent :: continuation) fallback bindings) =
        ([opened], state) := by
    simpa [fallback, parent, opened, subtraction, instantiate, Bindings.resolveAtom] using
      step_function_chain environment state budget bindings
        parentBody scope continuation
        subtraction body remaining privateRemaining
  rw [driver_singleton_step environment (fuel + 3) state state
    (finItem (parent :: continuation) fallback bindings) opened rest done
    (resume _) (atomToStack_pending _ _ _ _)]
  exact integer_subtraction_chain_enters environment state bindings parent continuation
    remaining (instantiate bindings body) amount 1 fuel rest done groundings

/-- The newly opened function case follows from the retained-frame law. -/
theorem integer_nonzero_guard_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (guard remaining marker : String) (body : Atom)
    (amount : Int) (fuel : Nat) (continuation : Stack)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table) (nonzero : amount ≠ 0)
    (different : remaining ≠ guard) (privateGuard : guard ∉ body.vars)
    (privateRemaining : instantiate bindings (.var remaining) = .var remaining) :
    let subtraction := Atom.expr [.sym "eval",
      .expr [.sym "-", .gnd (.int amount), .gnd (.int 1)]]
    let fallback := Atom.expr [.sym "chain", subtraction, .var remaining, body]
    let equality := Atom.expr [.sym "eval",
      .expr [.sym "==", .gnd (.int amount), .gnd (.int 0)]]
    let guarded := Atom.expr [.sym "chain", equality, .var guard,
      .expr [.sym "unify", .var guard, .gnd (.bool true),
        .expr [.sym "return", .sym marker], fallback]]
    let parent : Frame := { atom := .expr [.sym "function", guarded], ret := .function, vars := varsCopy continuation }
    interpretFuel environment (fuel + 8) state
        (⟨atomToStack (.expr [.sym "function", guarded]) continuation, bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Subst.apply [(remaining, .gnd (.int (amount - 1)))]
          (instantiate bindings body)) (parent :: continuation), bindings⟩ :: rest) done := by
  intro subtraction fallback equality guarded parent
  simpa only [guarded, equality, parent, atomToStack] using
    integer_nonzero_guard_enters_in_frame environment state bindings guard remaining marker body
      amount fuel (.expr [.sym "function", guarded]) (varsCopy continuation) continuation
      rest done groundings nonzero different privateGuard privateRemaining

/-- A closed return value exits the retained function frame exactly once.
The actual driver's public-result filter is made explicit. -/
theorem closed_return_finishes (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (fuel : Nat) (closed : value.vars = []) (visible : (value != emptyA) = true) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 2) state
        [⟨atomToStack (.expr [.sym "return", value]) [parent], bindings⟩] [] =
      ([(value, bindings)], state) := by
  intro parent
  let start : Item := ⟨{ atom := .expr [.sym "return", value], vars := scope } ::
    [parent], bindings⟩
  let middle : Item := ⟨{ atom := .expr [.sym "return", value], fin := true, vars := scope } ::
    [parent], bindings⟩
  have fixed : Bindings.resolveAtom bindings value = value :=
    Metta.instantiate_of_closed bindings value closed
  have initial : atomToStack (.expr [.sym "return", value]) [parent] = start.stack := by
    simp [atomToStack, start, parent, varsCopy]
  have firstStep (budget : Nat) :
      interpretStack1 environment budget state start = ([middle], state) := by
    simp [interpretStack1, start, middle, isEmbeddedOp]
  have lastStep (budget : Nat) :
      interpretStack1 environment budget state middle = ([finItem [] value bindings], state) := by
    simp [interpretStack1, middle, parent, instantiate, Bindings.resolveAtom, fixed]
  rw [initial]
  change interpretFuel environment (fuel + 2) state [start] [] = _
  rw [driver_singleton_step environment (fuel + 1) state state start middle [] []
    (firstStep _) (by rfl)]
  rw [interpretFuel_succ_of environment fuel state state middle []
    [finItem [] value bindings] [] (lastStep _)]
  change interpretFuel environment fuel state [] [(instantiate bindings value, bindings)] = _
  rw [interpretFuel_nil]
  simp [instantiate, fixed, visible]

end Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
