import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingMaterialization
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlContinuation
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlReturn
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaExpressionScope
import MettaHyperonFull.Runtime.Parser

/-!
# The emitted fuel guard in the existing minimal interpreter

The compiler uses the reader's Boolean literal representation. Exhaustion
then follows by native integer equality, sequencing, ordinary matching and
function return, independently of the guarded source computation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Metta.Minimal

/-- Both spellings print alike, but only the Boolean atom agrees with the
actual reader. The emitter must choose that atom before execution proofs. -/
theorem boolean_guard_reader :
    Metta.Runtime.parseAtomToken (render (.grounded (.bool true))) =
      toLeaTTaAtom (.grounded (.bool true)) ∧
    Metta.Runtime.parseAtomToken (render (.symbol "True")) ≠
      toLeaTTaAtom (.symbol "True") ∧
    render (.grounded (.bool true)) = render (.symbol "True") := by
  refine ⟨?_, ?_, ?_⟩
  · simp [render, Metta.Runtime.parseAtomToken, toLeaTTaAtom, toLeaTTaGround,
      Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue.toString]
  · simp [render, Metta.Runtime.parseAtomToken, toLeaTTaAtom]
  · simp [render, Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue.toString]

/-- The actual emitted guard produces exactly one exhaustion result at zero
source fuel, for every guarded body and acyclic incoming binding frame.
The interpreter's separate execution budget may be any value at least five. -/
theorem withFuel_zero_execution (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (build : Atom → Emit Atom) (first fuel : Nat)
    (groundings : environment.gt = Metta.Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    Metta.Minimal.interpretFuel environment (fuel + 5) state
        [⟨Metta.Minimal.atomToStack
            (toLeaTTaAtom (call "function"
              [(withFuel (.grounded (.int 0)) build first).1])) [], bindings⟩] [] =
      ([(.sym "nik:Exhausted", bindings)], state) := by
  let emitted := build (.var ("nik" ++ toString first)) (first + 1)
  exact integer_zero_guard_returns environment state bindings
    ("nik" ++ toString emitted.2) "nik:Exhausted"
    (toLeaTTaAtom (call "chain"
      [call "eval" [call "-" [.grounded (.int 0), .grounded (.int 1)]],
        .var ("nik" ++ toString first), emitted.1]))
    fuel groundings acyclic (by decide)

/-- Every expression emitted by the compiler uses the qualified guard. This
includes recursive calls and primitive requests; none is run at zero source
fuel. -/
theorem expression_zero_execution (program : Program) (names : Names) (source : Term)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (first fuel : Nat)
    (groundings : environment.gt = Metta.Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    Metta.Minimal.interpretFuel environment (fuel + 5) state
        [⟨Metta.Minimal.atomToStack
            (toLeaTTaAtom (call "function"
              [(expression program names (.grounded (.int 0)) source first).1])) [], bindings⟩] [] =
      ([(.sym "nik:Exhausted", bindings)], state) := by
  rw [expression]
  exact withFuel_zero_execution environment state bindings _ first fuel groundings acyclic

/-- The predecessor variable occurs in every generated guard. -/
theorem withFuel_remaining_occurs (fuel : Atom) (build : Atom → Emit Atom)
    (first : Nat) (rename : String → String) :
    rename (freshName first) ∈
      (renBy rename (toLeaTTaAtom (withFuel fuel build first).1)).vars := by
  let emitted := build (.var (freshName first)) (first + 1)
  change rename (freshName first) ∈ (renBy rename (toLeaTTaAtom
    (call "chain" [call "eval" [call "==" [fuel, .grounded (.int 0)]],
      .var (freshName emitted.2),
      call "unify" [.var (freshName emitted.2), .grounded (.bool true),
        returned (.symbol "nik:Exhausted"),
        call "chain" [call "eval" [call "-" [fuel, .grounded (.int 1)]],
          .var (freshName first), emitted.1]]]))).vars
  simp only [renBy_vars, List.mem_map]
  refine ⟨freshName first, ?_, rfl⟩
  simp [call, returned, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars]

/-- Every compiled expression retains its own guard variable. -/
theorem expression_remaining_occurs (program : Program) (names : Names) (sourceFuel : Atom)
    (source : Term) (first : Nat) (rename : String → String) :
    rename (freshName first) ∈
      (renBy rename (toLeaTTaAtom (expression program names sourceFuel source first).1)).vars := by
  rw [expression]
  exact withFuel_remaining_occurs _ _ _ _

/-- Exhaustion reaches the retained function handler without running its fallback. -/
theorem renamed_withFuel_zero_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (rename : String → String)
    (build : Atom → Emit Atom) (first fuel : Nat) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 4) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom (withFuel (.grounded (.int 0)) build first).1))
        (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (finItem (parent :: continuation) (.expr [.sym "return", .sym "nik:Exhausted"])
        bindings :: rest) done := by
  intro parent
  let emitted := build (.var (freshName first)) (first + 1)
  have emittedShape : (withFuel (.grounded (.int 0)) build first).1 =
      call "chain" [call "eval" [call "==" [.grounded (.int 0), .grounded (.int 0)]],
        .var (freshName emitted.2),
        call "unify" [.var (freshName emitted.2), .grounded (.bool true),
          returned (.symbol "nik:Exhausted"),
          call "chain" [call "eval" [call "-" [.grounded (.int 0), .grounded (.int 1)]],
            .var (freshName first), emitted.1]]] := rfl
  simpa only [emittedShape, call, returned, toLeaTTaAtom, toLeaTTaAtoms,
    toLeaTTaGround, renBy, List.map_cons, List.map_nil] using
    integer_zero_guard_selects_in_frame environment state bindings
    (rename (freshName emitted.2)) "nik:Exhausted"
    (renBy rename (toLeaTTaAtom (call "chain"
      [call "eval" [call "-" [.grounded (.int 0), .grounded (.int 1)]],
        .var (freshName first), emitted.1]))) fuel parent continuation rest done groundings acyclic

/-- Exhaustion of a freshly renamed function returns through an arbitrary
caller. Source exhaustion is a returned outcome, not an invalid-proof claim
or exhaustion of the interpreter's own execution budget. -/
theorem renamed_withFuel_zero_to_caller_in_frame (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings) (rename : String → String)
    (build : Atom → Emit Atom) (first fuel : Nat)
    (parentBody : Metta.Atom) (scope : List Metta.VarName) (caller : Metta.Minimal.Frame)
    (continuation : Metta.Minimal.Stack) (rest : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let parent : Metta.Minimal.Frame := { atom := parentBody, ret := .function, vars := scope }
    Metta.Minimal.interpretFuel environment (fuel + 5) state
        (⟨Metta.Minimal.atomToStack
          (renBy rename (toLeaTTaAtom (withFuel (.grounded (.int 0)) build first).1))
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation) (.sym "nik:Exhausted")
          bindings :: rest) done := by
  intro parent
  let emitted := build (.var (freshName first)) (first + 1)
  have emittedShape : (withFuel (.grounded (.int 0)) build first).1 =
      call "chain" [call "eval" [call "==" [.grounded (.int 0), .grounded (.int 0)]],
        .var (freshName emitted.2),
        call "unify" [.var (freshName emitted.2), .grounded (.bool true),
          returned (.symbol "nik:Exhausted"),
          call "chain" [call "eval" [call "-" [.grounded (.int 0), .grounded (.int 1)]],
            .var (freshName first), emitted.1]]] := rfl
  simpa only [parent, emittedShape, call, returned, toLeaTTaAtom, toLeaTTaAtoms,
    toLeaTTaGround, renBy, List.map_cons, List.map_nil] using
    integer_zero_guard_to_caller_in_frame environment state bindings
      (rename (freshName emitted.2)) "nik:Exhausted"
      (renBy rename (toLeaTTaAtom (call "chain"
        [call "eval" [call "-" [.grounded (.int 0), .grounded (.int 1)]],
          .var (freshName first), emitted.1])))
      fuel parentBody scope caller continuation rest done groundings acyclic

/-- Opening a function is a special case of exhaustion inside its retained frame. -/
theorem renamed_withFuel_zero_to_caller (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings) (rename : String → String)
    (build : Atom → Emit Atom) (first fuel : Nat) (caller : Metta.Minimal.Frame)
    (continuation : Metta.Minimal.Stack) (rest : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    Metta.Minimal.interpretFuel environment (fuel + 5) state
        (⟨Metta.Minimal.atomToStack
          (renBy rename (toLeaTTaAtom (call "function"
            [(withFuel (.grounded (.int 0)) build first).1])))
          (caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation) (.sym "nik:Exhausted")
          bindings :: rest) done := by
  let function := renBy rename (toLeaTTaAtom (call "function"
    [(withFuel (.grounded (.int 0)) build first).1]))
  have shape : ∃ items, renBy rename
      (toLeaTTaAtom (withFuel (.grounded (.int 0)) build first).1) = .expr items := by
    change ∃ items, renBy rename (toLeaTTaAtom (call "chain" [_, _, _])) = .expr items
    simp only [call, toLeaTTaAtom, renBy]
    exact ⟨_, rfl⟩
  obtain ⟨items, shape⟩ := shape
  simpa only [function, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
    List.map_cons, List.map_nil, shape, Metta.Minimal.atomToStack] using
    renamed_withFuel_zero_to_caller_in_frame environment state bindings rename build first fuel
      function (Metta.Minimal.varsCopy (caller :: continuation)) caller continuation rest done
      groundings acyclic

/-- The zero-fuel expression case inside an existing dispatcher frame.
No guest expression is evaluated before exhaustion returns to the caller. -/
theorem renamed_expression_zero_to_caller_in_frame (program : Program) (names : Names)
    (source : Term) (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (rename : String → String) (first fuel : Nat)
    (parentBody : Metta.Atom) (scope : List Metta.VarName)
    (caller : Metta.Minimal.Frame) (continuation : Metta.Minimal.Stack)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let parent : Metta.Minimal.Frame := { atom := parentBody, ret := .function, vars := scope }
    Metta.Minimal.interpretFuel environment (fuel + 5) state
        (⟨Metta.Minimal.atomToStack
          (renBy rename (toLeaTTaAtom
            (expression program names (.grounded (.int 0)) source first).1))
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation) (.sym "nik:Exhausted")
          bindings :: rest) done := by
  rw [expression]
  exact renamed_withFuel_zero_to_caller_in_frame environment state bindings rename _ first fuel
    parentBody scope caller continuation rest done groundings acyclic

/-- The zero-fuel base case holds for every source expression, including
recursive calls, without imposing any premise on the guest operation. -/
theorem renamed_expression_zero_to_caller (program : Program) (names : Names)
    (source : Term) (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (rename : String → String) (first fuel : Nat)
    (caller : Metta.Minimal.Frame) (continuation : Metta.Minimal.Stack)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    Metta.Minimal.interpretFuel environment (fuel + 5) state
        (⟨Metta.Minimal.atomToStack
          (renBy rename (toLeaTTaAtom (call "function"
            [(expression program names (.grounded (.int 0)) source first).1])))
          (caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation) (.sym "nik:Exhausted")
          bindings :: rest) done := by
  rw [expression]
  exact renamed_withFuel_zero_to_caller environment state bindings rename _ first fuel
    caller continuation rest done groundings acyclic

/-- Capture-avoiding rule freshening preserves the compiled fuel guard.
The runtime substitutes the predecessor for the renamed private variable,
while materializing the body in its incoming frame. -/
theorem renamed_withFuel_positive_execution_in_frame (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (build : Atom → Emit Atom) (first remaining fuel : Nat)
    (parentBody : Metta.Atom) (scope : List Metta.VarName)
    (continuation : Metta.Minimal.Stack) (rest : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (rename (freshName first))) =
      .var (rename (freshName first)))
    (bodyBound : first + 1 ≤ (build (.var (freshName first)) (first + 1)).2 ∧
      UsesBefore (build (.var (freshName first)) (first + 1)).2
        (build (.var (freshName first)) (first + 1)).1) :
    let emitted := build (.var (freshName first)) (first + 1)
    let parent : Metta.Minimal.Frame := { atom := parentBody, ret := .function, vars := scope }
    Metta.Minimal.interpretFuel environment (fuel + 8) state
        (⟨Metta.Minimal.atomToStack
          (renBy rename (toLeaTTaAtom
            (withFuel (.grounded (.int (remaining + 1))) build first).1))
          (parent :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (⟨Metta.Minimal.atomToStack
          (Metta.Subst.apply [(rename (freshName first), .gnd (.int remaining))]
            (Metta.instantiate bindings (renBy rename (toLeaTTaAtom emitted.1))))
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro emitted parent
  change first + 1 ≤ emitted.2 ∧ UsesBefore emitted.2 emitted.1 at bodyBound
  have different : rename (freshName first) ≠ rename (freshName emitted.2) := by
    intro same
    have equalIndex := freshName_injective (injective same)
    omega
  have privateGuard : rename (freshName emitted.2) ∉
      (renBy rename (toLeaTTaAtom emitted.1)).vars := by
    intro occurrence
    rw [renBy_vars] at occurrence
    obtain ⟨name, member, same⟩ := List.mem_map.mp occurrence
    have sameName := injective same
    rw [sameName] at member
    exact bodyBound.2.excludes emitted.2 le_rfl
      (Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance.atomOccurs_of_mem_translated_vars
        member)
  have predecessor : (remaining : Int) + 1 - 1 = remaining := by omega
  have emittedShape : (withFuel (.grounded (.int (remaining + 1))) build first).1 =
      call "chain" [call "eval" [call "=="
        [.grounded (.int (remaining + 1)), .grounded (.int 0)]],
        .var (freshName emitted.2),
        call "unify" [.var (freshName emitted.2), .grounded (.bool true),
          returned (.symbol "nik:Exhausted"),
          call "chain" [call "eval" [call "-"
            [.grounded (.int (remaining + 1)), .grounded (.int 1)]],
            .var (freshName first), emitted.1]]] := rfl
  simpa only [parent, emittedShape, call, returned,
    toLeaTTaAtom, toLeaTTaAtoms, toLeaTTaGround, renBy, List.map_cons, List.map_nil, predecessor] using
    integer_nonzero_guard_enters_in_frame environment state bindings (rename (freshName emitted.2))
      (rename (freshName first)) "nik:Exhausted" (renBy rename (toLeaTTaAtom emitted.1))
      (remaining + 1) fuel parentBody scope continuation rest done groundings (by omega)
      different privateGuard privateRemaining

/-- The same positive-fuel law applies when the function frame is newly opened. -/
theorem renamed_withFuel_positive_execution (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (build : Atom → Emit Atom) (first remaining fuel : Nat)
    (continuation : Metta.Minimal.Stack) (rest : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (rename (freshName first))) =
      .var (rename (freshName first)))
    (bodyBound : first + 1 ≤ (build (.var (freshName first)) (first + 1)).2 ∧
      UsesBefore (build (.var (freshName first)) (first + 1)).2
        (build (.var (freshName first)) (first + 1)).1) :
    let emitted := build (.var (freshName first)) (first + 1)
    let function := renBy rename (toLeaTTaAtom (call "function"
      [(withFuel (.grounded (.int (remaining + 1))) build first).1]))
    let parent : Metta.Minimal.Frame := { atom := function, ret := .function, vars := Metta.Minimal.varsCopy continuation }
    Metta.Minimal.interpretFuel environment (fuel + 8) state
        (⟨Metta.Minimal.atomToStack function continuation, bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (⟨Metta.Minimal.atomToStack
          (Metta.Subst.apply [(rename (freshName first), .gnd (.int remaining))]
            (Metta.instantiate bindings (renBy rename (toLeaTTaAtom emitted.1))))
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro emitted function parent
  have shape : ∃ items, renBy rename
      (toLeaTTaAtom (withFuel (.grounded (.int (remaining + 1))) build first).1) =
      .expr items := by
    change ∃ items, renBy rename (toLeaTTaAtom (call "chain" [_, _, _])) = .expr items
    simp only [call, toLeaTTaAtom, renBy]
    exact ⟨_, rfl⟩
  obtain ⟨items, shape⟩ := shape
  simpa only [function, parent, emitted, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
    List.map_cons, List.map_nil, shape, Metta.Minimal.atomToStack] using
    renamed_withFuel_positive_execution_in_frame environment state bindings rename injective
      build first remaining fuel function (Metta.Minimal.varsCopy continuation)
      continuation rest done groundings privateRemaining bodyBound

/-- Positive source fuel enters the actual compiled body with the predecessor
substituted for the allocated fuel variable. The surrounding stack and work
queue are arbitrary. The ordinary allocation bound discharges guard freshness. -/
theorem withFuel_positive_execution (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (build : Atom → Emit Atom) (first remaining fuel : Nat)
    (continuation : Metta.Minimal.Stack) (rest : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first))
    (bodyBound : first + 1 ≤ (build (.var (freshName first)) (first + 1)).2 ∧
      UsesBefore (build (.var (freshName first)) (first + 1)).2
        (build (.var (freshName first)) (first + 1)).1) :
    let emitted := build (.var (freshName first)) (first + 1)
    let function := toLeaTTaAtom (call "function"
      [(withFuel (.grounded (.int (remaining + 1))) build first).1])
    let parent : Metta.Minimal.Frame := { atom := function, ret := .function, vars := Metta.Minimal.varsCopy continuation }
    Metta.Minimal.interpretFuel environment (fuel + 8) state
        (⟨Metta.Minimal.atomToStack function continuation, bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (⟨Metta.Minimal.atomToStack
          (Metta.Subst.apply [(freshName first, .gnd (.int remaining))]
            (Metta.instantiate bindings (toLeaTTaAtom emitted.1)))
          (parent :: continuation), bindings⟩ :: rest) done := by
  have identity (atom : Metta.Atom) : renBy id atom = atom := by
    change renBy (applyRen []) atom = atom
    rw [← renameVars_eq_renBy]
    exact Metta.renameVars_nil atom
  simpa only [identity, id_eq] using
    renamed_withFuel_positive_execution environment state bindings id (fun _ _ same => same)
      build first remaining fuel continuation rest done groundings privateRemaining bodyBound

/-- Closed generated data remains inert under the target's runtime bindings. -/
theorem data_atom_runtime_closed {atom : Atom} (data : MeTTaData.DataAtom atom) :
    (toLeaTTaAtom atom).vars = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  exact data_has_no_variables data name
    (Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance.atomOccurs_of_mem_translated_vars member)

/-- Generated data tags cannot be mistaken for the driver's empty-result marker. -/
theorem data_atom_runtime_visible {atom : Atom} (data : MeTTaData.DataAtom atom) :
    (toLeaTTaAtom atom != Metta.Minimal.emptyA) = true := by
  cases data with
  | symbol tag =>
      rename_i name
      have distinct : name ≠ "Empty" := by
        rintro rfl
        simp [MeTTaData.dataSymbols] at tag
      change (name != "Empty") = true
      simp [distinct]
  | grounded value => cases value <;> rfl
  | expression => rfl

/-- A positive-fuel compiled data return completes with exactly one result.
It preserves state and bindings and performs no guest operation. -/
theorem withFuel_return_execution (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings) (result : Atom)
    (data : MeTTaData.DataAtom result) (first remaining fuel : Nat)
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first)) :
    Metta.Minimal.interpretFuel environment (fuel + 10) state
        [⟨Metta.Minimal.atomToStack (toLeaTTaAtom (call "function"
          [(withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned result)) first).1])) [], bindings⟩] [] =
      ([(toLeaTTaAtom result, bindings)], state) := by
  have resultScope : UsesBefore (first + 1) result := by
    intro name occurrence
    exact False.elim (data_has_no_variables data name occurrence)
  have bodyBound : first + 1 ≤
      ((fun (_ : Atom) => pure (returned result) : Atom → Emit Atom)
        (.var (freshName first)) (first + 1)).2 ∧
      UsesBefore ((fun (_ : Atom) => pure (returned result) : Atom → Emit Atom)
        (.var (freshName first)) (first + 1)).2
        ((fun (_ : Atom) => pure (returned result) : Atom → Emit Atom)
          (.var (freshName first)) (first + 1)).1 := by
    change first + 1 ≤ first + 1 ∧ UsesBefore (first + 1) (returned result)
    simpa [returned] using resultScope
  have closed := data_atom_runtime_closed data
  have returnedClosed : (toLeaTTaAtom (returned result)).vars = [] := by
    simp [returned, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars, closed]
  have computation := withFuel_positive_execution environment state bindings
    (fun _ => pure (returned result)) first remaining (fuel + 2) [] [] []
    groundings privateRemaining bodyBound
  rw [show fuel + 10 = (fuel + 2) + 8 by omega, computation]
  rw [show ((pure (returned result) : Emit Atom) (first + 1)).1 = returned result from rfl]
  rw [Metta.instantiate_of_closed bindings _ returnedClosed,
    Metta.Subst.apply_of_closed _ _ returnedClosed]
  exact closed_return_finishes environment state bindings _ (toLeaTTaAtom result) [] fuel
    closed (data_atom_runtime_visible data)

private theorem encoded_value_data (term : Term) :
    MeTTaData.DataAtom (value (MeTTaData.encode term)) := by
  apply MeTTaData.DataAtom.expression
  intro atom member
  rcases List.mem_cons.mp member with rfl | member
  · exact .symbol (by simp [MeTTaData.dataSymbols])
  · rcases List.mem_singleton.mp member with rfl
    exact MeTTaData.encode_data term

/-- An arbitrary guest symbol, including an instruction-like spelling, is
returned as encoded data by the actual expression compiler and interpreter. -/
theorem expression_symbol_execution (program : Program) (names : Names) (name : String)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (first remaining fuel : Nat)
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first)) :
    Metta.Minimal.interpretFuel environment (fuel + 10) state
        [⟨Metta.Minimal.atomToStack (toLeaTTaAtom (call "function"
          [(expression program names (.grounded (.int (remaining + 1)))
            (.sym name) first).1])) [], bindings⟩] [] =
      ([(toLeaTTaAtom (value (MeTTaData.encode (.sym name))), bindings)], state) := by
  simpa only [expression] using withFuel_return_execution environment state bindings
    (value (MeTTaData.encode (.sym name))) (encoded_value_data (.sym name))
    first remaining fuel groundings privateRemaining

/-- A missing source variable returns the compiler's failure outcome exactly;
it cannot become an unresolved target variable or start a query. -/
theorem expression_missing_variable_execution (program : Program) (names : Names)
    (name : String) (missing : names.find? (fun entry => entry.1 == name) = none)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (first remaining fuel : Nat)
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first)) :
    Metta.Minimal.interpretFuel environment (fuel + 10) state
        [⟨Metta.Minimal.atomToStack (toLeaTTaAtom (call "function"
          [(expression program names (.grounded (.int (remaining + 1)))
            (.var name) first).1])) [], bindings⟩] [] =
      ([(.sym "nik:Failure", bindings)], state) := by
  simpa only [expression, missing, toLeaTTaAtom] using
    withFuel_return_execution environment state bindings (.symbol "nik:Failure")
      (.symbol (by simp [MeTTaData.dataSymbols])) first remaining fuel
      groundings privateRemaining

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
