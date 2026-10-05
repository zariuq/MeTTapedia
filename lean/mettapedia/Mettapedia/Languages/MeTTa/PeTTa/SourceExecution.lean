import Mettapedia.Languages.MeTTa.PeTTa.SourceEvaluation

/-!
# Finite execution of the PeTTa source machine

A completed run preserves and reflects a finite path in the operational GSLT,
including the final store, ordered answers, unconsumed input and printed output.
Fuel is a resource bound on transitions. Increasing it cannot change an already
completed run, and every finite successful path has a sufficient bound.

These are execution laws for arbitrary source programs. Agreement with a guest
kernel is an additional program-correctness theorem, not a premise here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourceExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi
open SourceProgram (Program)
open SourcePrimitives (State)
open SourceEvaluation

def finished (state : State) (answers input output : List Atom) : Configuration :=
  { state, control := .returned answers, input, output }

@[simp] theorem run_finished (program : Program) (fuel : Nat)
    (state : State) (answers input output : List Atom) :
    run program fuel (finished state answers input output) =
      .complete state answers input output := by
  cases fuel <;> simp [run, finished]

theorem run_succ_of_step (program : Program) (fuel : Nat)
    (source target : Configuration) (transition : step program source = some target) :
    run program (fuel + 1) source = run program fuel target := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals try solve | simp [step] at transition
      all_goals simp only [run, transition]

theorem path_lifts_completed_run (program : Program) {source target : Configuration}
    (path : (theory program).MultiStep source target) (fuel : Nat)
    (state : State) (answers input output : List Atom)
    (completed : run program fuel target = .complete state answers input output) :
    ∃ fuel, run program fuel source = .complete state answers input output := by
  have lift {system : Mettapedia.GSLT.GSLT} {property : system.Term → Prop}
      (backwards : ∀ {first second}, system.Step first second → property second → property first)
      {first last} (path : system.MultiStep first last) (atLast : property last) :
      property first := by
    induction path with
    | refl _ => exact atLast
    | step transition _ ih => exact backwards transition (ih atLast)
  apply lift (system := theory program)
    (property := fun configuration =>
      ∃ fuel, run program fuel configuration = .complete state answers input output)
    (path := path) (atLast := ⟨fuel, completed⟩)
  intro first second transition ⟨fuel, completed⟩
  exact ⟨fuel + 1, (run_succ_of_step program fuel first second transition).trans completed⟩

theorem path_has_sufficient_fuel (program : Program) (source : Configuration)
    (state : State) (answers input output : List Atom)
    (path : (theory program).MultiStep source (finished state answers input output)) :
    ∃ fuel, run program fuel source = .complete state answers input output :=
  path_lifts_completed_run program path 0 state answers input output (run_finished ..)

theorem completed_run_has_path (program : Program) (fuel : Nat)
    (source : Configuration) (state : State) (answers input output : List Atom)
    (completed : run program fuel source = .complete state answers input output) :
    (theory program).MultiStep source (finished state answers input output) := by
  induction fuel generalizing source with
  | zero =>
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames <;> simp only [run] at completed
          all_goals first | contradiction | cases completed; exact .refl _
  | succ fuel ih =>
      have advance (current : Configuration)
          (completed : run program (fuel + 1) current = .complete state answers input output)
          (unfolded : run program (fuel + 1) current =
            match step program current with
            | some next => run program fuel next
            | none => .exhausted current) :
          (theory program).MultiStep current (finished state answers input output) := by
        rw [unfolded] at completed
        cases transition : step program current with
        | none => simp [transition] at completed
        | some next =>
            exact .step transition (ih next (by simpa [transition] using completed))
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames
          all_goals try solve | simp only [run] at completed; cases completed; all_goals exact .refl _
          all_goals exact advance _ completed rfl

theorem completed_run_iff_path (program : Program) (source : Configuration)
    (state : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel source = .complete state answers input output) ↔
      (theory program).MultiStep source (finished state answers input output) :=
  ⟨fun ⟨fuel, completed⟩ => completed_run_has_path program fuel source state answers input output completed,
    path_has_sufficient_fuel program source state answers input output⟩

theorem completed_run_more_fuel (program : Program) (fuel extra : Nat)
    (source : Configuration) (state : State) (answers input output : List Atom)
    (completed : run program fuel source = .complete state answers input output) :
    run program (fuel + extra) source = .complete state answers input output := by
  induction fuel generalizing source with
  | zero =>
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames <;> simp only [run] at completed
          all_goals first
            | contradiction
            | cases completed
              all_goals cases extra <;> rfl
  | succ fuel ih =>
      have advance (current : Configuration)
          (completed : run program (fuel + 1) current = .complete state answers input output)
          (unfolded : run program (fuel + 1) current =
            match step program current with
            | some next => run program fuel next
            | none => .exhausted current) :
          run program (fuel + 1 + extra) current = .complete state answers input output := by
        rw [unfolded] at completed
        cases transition : step program current with
        | none => simp [transition] at completed
        | some next =>
            have later := ih next (by simpa [transition] using completed)
            simpa [Nat.add_right_comm] using
              (run_succ_of_step program (fuel + extra) current next transition).trans later
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames
          all_goals try solve
            | simp only [run] at completed
              cases completed
              all_goals exact run_finished program (fuel + 1 + extra) state answers input output
          all_goals exact advance _ completed rfl

theorem completed_result_unique (program : Program) (firstFuel secondFuel : Nat)
    (source : Configuration) (first second : State)
    (firstAnswers firstInput firstOutput secondAnswers secondInput secondOutput : List Atom)
    (one : run program firstFuel source = .complete first firstAnswers firstInput firstOutput)
    (two : run program secondFuel source = .complete second secondAnswers secondInput secondOutput) :
    first = second ∧ firstAnswers = secondAnswers ∧
      firstInput = secondInput ∧ firstOutput = secondOutput := by
  have left := completed_run_more_fuel program firstFuel secondFuel source first
    firstAnswers firstInput firstOutput one
  have right := completed_run_more_fuel program secondFuel firstFuel source second
    secondAnswers secondInput secondOutput two
  rw [Nat.add_comm secondFuel firstFuel] at right
  exact Outcome.complete.inj (left.symm.trans right)

/-- Caller frames are suspended beneath the current computation. -/
def withFrames (configuration : Configuration) (caller : List Frame) : Configuration :=
  { configuration with frames := configuration.frames ++ caller }

theorem step_with_caller_frames (program : Program) (source target : Configuration)
    (caller : List Frame) (transition : step program source = some target) :
    step program (withFrames source caller) = some (withFrames target caller) := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals simp only [step] at transition
      all_goals simp only [withFrames, step, List.nil_append, List.cons_append]
      all_goals
        repeat' first
          | contradiction
          | split at transition
          | solve | cases transition; simp_all

theorem path_with_caller_frames (program : Program) (caller : List Frame) :
    {source target : Configuration} → (theory program).MultiStep source target →
      (theory program).MultiStep (withFrames source caller) (withFrames target caller)
  | _, _, .refl _ => .refl _
  | _, _, .step transition rest =>
      .step (step_with_caller_frames program _ _ caller transition)
        (path_with_caller_frames program caller rest)

theorem completed_computation_in_caller (program : Program) (fuel : Nat)
    (source : Configuration) (caller : List Frame)
    (state : State) (answers input output : List Atom)
    (completed : run program fuel source = .complete state answers input output) :
    (theory program).MultiStep (withFrames source caller)
      (withFrames (finished state answers input output) caller) :=
  path_with_caller_frames program caller
    (completed_run_has_path program fuel source state answers input output completed)

/-! ## Composition of single-answer computations

These laws use the source machine's paths and frames. They do not prescribe a
guest algorithm. A function proof can compose its actual expression bodies
without unfolding the caller or expanding a stored proof into certificates.
-/

private theorem path_trans {system : Mettapedia.GSLT.GSLT}
    {first middle last : system.Term}
    (one : system.MultiStep first middle) (two : system.MultiStep middle last) :
    system.MultiStep first last := by
  induction one with
  | refl _ => exact two
  | step transition _ ih => exact .step transition (ih two)

/-- Ordered answers, retaining both repeated occurrences and empty results. -/
abbrev Returns (program : Program) (bindings : MORK.Subst)
    (before : State) (expression : Atom) (after : State) (answers : List Atom) : Prop :=
  (theory program).MultiStep { state := before, control := .evaluate bindings expression }
    (finished after answers [] [])

abbrev PureReturns (program : Program) (bindings : MORK.Subst)
    (before : State) (expression : Atom) (after : State) (value : Atom) : Prop :=
  Returns program bindings before expression after [value]

theorem variable_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (name : String) :
    PureReturns program bindings state (.var name) state (MORK.applySubst bindings (.var name)) :=
  .step rfl (.refl _)

theorem symbol_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (name : String) :
    PureReturns program bindings state (.symbol name) state (.symbol name) :=
  .step rfl (.refl _)

theorem grounded_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) :
    PureReturns program bindings state (.grounded value) state (.grounded value) :=
  .step rfl (.refl _)

theorem single_sequence_answers (program : Program) (before after : State)
    (control : Control) (value : List Atom)
    (computed : (theory program).MultiStep { state := before, control }
      (finished after value [] [])) :
    (theory program).MultiStep { state := before, control := .sequence [control] [] }
      (finished after value [] []) := by
  refine .step rfl (path_trans (path_with_caller_frames program [.sequence [] []] computed) ?_)
  exact .step rfl (.step rfl (.refl _))


theorem single_sequence_returns (program : Program) (before after : State)
    (control : Control) (value : Atom)
    (computed : (theory program).MultiStep { state := before, control }
      (finished after [value] [] [])) :
    (theory program).MultiStep { state := before, control := .sequence [control] [] }
      (finished after [value] [] []) :=
  single_sequence_answers program before after control [value] computed


/-- Collection preserves the exact ordered occurrence list, not its set. -/
theorem collapse_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (expression : Atom) (answers : List Atom)
    (returned : Returns program bindings before expression after answers) :
    PureReturns program bindings before (.expression [.symbol "collapse", expression]) after
      (.expression answers) := by
  refine .step rfl (path_trans (path_with_caller_frames program [.collect] returned) ?_)
  exact .step rfl (.refl _)

theorem let_returns (program : Program) (bindings bound : MORK.Subst)
    (before middle after : State) (pattern expression body value answer : Atom)
    (first : PureReturns program bindings before expression middle value)
    (matched : SourceProgram.matchValue bindings pattern value = some bound)
    (second : PureReturns program bound middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "let", pattern, expression, body]) after answer := by
  refine .step rfl
    (path_trans (path_with_caller_frames program [.bind bindings pattern body] first) ?_)
  refine .step ?_ (single_sequence_returns program middle after (.evaluate bound body) answer second)
  change step program _ = some _
  simp [withFrames, finished, step, matched]

/-- Entering the body records its caller, without assuming that body returns. -/
theorem let_enters (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (pattern expression body value : Atom)
    (computed : PureReturns program bindings before expression after value)
    (matched : SourceProgram.matchValue bindings pattern value = some bound) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "let", pattern, expression, body]) }
      { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := by
  refine .step rfl
    (path_trans (path_with_caller_frames program [.bind bindings pattern body] computed) ?_)
  have entered : (theory program).Step
      { state := after, control := .sequence [.evaluate bound body] [] }
      { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := rfl
  refine .step (u := ({ state := after, control := .sequence [.evaluate bound body] [] } : Configuration))
    ?_ (.step entered (.refl _))
  change step program _ = some _
  simp [withFrames, finished, step, matched]

theorem let_reaches (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (pattern expression body value : Atom) (target : Configuration)
    (computed : PureReturns program bindings before expression after value)
    (matched : SourceProgram.matchValue bindings pattern value = some bound)
    (continuation : (theory program).MultiStep
      { state := after, control := .evaluate bound body } target) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "let", pattern, expression, body]) }
      (withFrames target [.sequence [] []]) :=
  path_trans (let_enters program bindings bound before after pattern expression body value computed matched)
    (path_with_caller_frames program [.sequence [] []] continuation)

theorem read_cases_encoded (cases : SourceProgram.Cases) :
    readCases (cases.map fun row => .expression [row.1, row.2]) = some cases := by
  induction cases with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨pattern, body⟩
      simp [readCases, ih]

theorem case_returns (program : Program) (bindings bound : MORK.Subst)
    (before middle after : State) (expression value body answer : Atom)
    (rows : List Atom) (cases : SourceProgram.Cases)
    (decoded : readCases rows = some cases)
    (first : PureReturns program bindings before expression middle value)
    (selected : SourceProgram.selectCase bindings value cases = some (bound, body))
    (second : PureReturns program bound middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "case", expression, .expression rows]) after answer := by
  refine .step ?_
    (path_trans (path_with_caller_frames program [.select bindings cases] first) ?_)
  · change step program _ = some _
    simp [step, withFrames, decoded]
  · refine .step ?_ (single_sequence_returns program middle after (.evaluate bound body) answer second)
    change step program _ = some _
    simp [withFrames, finished, step, selected]

theorem case_enters (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (expression value body : Atom)
    (rows : List Atom) (cases : SourceProgram.Cases)
    (decoded : readCases rows = some cases)
    (computed : PureReturns program bindings before expression after value)
    (selected : SourceProgram.selectCase bindings value cases = some (bound, body)) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "case", expression, .expression rows]) }
      { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := by
  refine .step ?_
    (path_trans (path_with_caller_frames program [.select bindings cases] computed) ?_)
  · change step program _ = some _
    simp [step, withFrames, decoded]
  · have entered : (theory program).Step
        { state := after, control := .sequence [.evaluate bound body] [] }
        { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := rfl
    refine .step (u := ({ state := after, control := .sequence [.evaluate bound body] [] } : Configuration))
      ?_ (.step entered (.refl _))
    change step program _ = some _
    simp [withFrames, finished, step, selected]

theorem case_reaches (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (expression value body : Atom)
    (rows : List Atom) (cases : SourceProgram.Cases) (target : Configuration)
    (decoded : readCases rows = some cases)
    (computed : PureReturns program bindings before expression after value)
    (selected : SourceProgram.selectCase bindings value cases = some (bound, body))
    (continuation : (theory program).MultiStep
      { state := after, control := .evaluate bound body } target) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "case", expression, .expression rows]) }
      (withFrames target [.sequence [] []]) :=
  path_trans (case_enters program bindings bound before after expression value body rows cases
    decoded computed selected) (path_with_caller_frames program [.sequence [] []] continuation)

theorem if_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (condition value yes no answer : Atom)
    (tested : PureReturns program bindings before condition middle value)
    (chosen : PureReturns program bindings middle
      (if value == SourcePrimitives.boolean true then yes else no) after answer) :
    PureReturns program bindings before
      (.expression [.symbol "if", condition, yes, no]) after answer := by
  refine .step rfl
    (path_trans (path_with_caller_frames program [.branch bindings yes no] tested) ?_)
  exact .step rfl (single_sequence_returns program middle after _ answer chosen)

theorem pure_returns_has_sufficient_fuel (program : Program) (bindings : MORK.Subst)
    (before after : State) (expression value : Atom)
    (computed : PureReturns program bindings before expression after value) :
    ∃ fuel, run program fuel { state := before, control := .evaluate bindings expression } =
      .complete after [value] [] [] :=
  path_has_sufficient_fuel program _ after [value] [] [] computed

theorem clauses_use_only_the_named_equations (program : Program) (head : String)
    (values : List Atom) :
    clauses program head values =
      (program.equations.filter (fun equation => equation.head == head)).filterMap
        (fun equation =>
          (SourceProgram.matchValue [] (.expression equation.arguments) (.expression values)).map
            fun bindings => .evaluate bindings equation.body) := by
  cases program with
  | mk equations declarations initializers =>
      unfold clauses
      induction equations with
      | nil => rfl
      | cons equation equations ih =>
          dsimp only at ih ⊢
          by_cases same : equation.head = head <;> simp [List.filterMap_cons, same, ih]

theorem authored_function_arguments_return (program : Program) (bindings callee : MORK.Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat)
    (body answer : Atom) (ordinary : ioHead head = false)
    (authored : SourcePrimitives.known head = false)
    (selected : clauses program head values = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after [answer] [] []) := by
  refine .step ?_ (single_sequence_returns program before after (.evaluate callee body) answer computed)
  change step program _ = some _
  simp [step, ordinary, authored, selected]

theorem native_function_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat)
    (answer : List Atom) (ordinary : ioHead head = false)
    (native : SourcePrimitives.known head = true)
    (computed : SourcePrimitives.apply before head values = .ok (after, answer)) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after answer [] []) := by
  refine .step ?_ (.refl _)
  change step program _ = some _
  simp [step, ordinary, native, computed, finished]


theorem native_function_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat)
    (answer : Atom) (ordinary : ioHead head = false)
    (native : SourcePrimitives.known head = true)
    (computed : SourcePrimitives.apply before head values = .ok (after, [answer])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after [answer] [] []) :=
  native_function_arguments_answers program bindings before after head values index [answer] ordinary native computed

theorem raw_argument_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (argument : Atom)
    (arguments values : List Atom) (index : Nat) (answers : List Atom)
    (raw : argumentIsRaw program head index = true)
    (rest : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments
          (values ++ [MORK.applySubst bindings argument]) (index + 1) }
      (finished after answers [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) (argument :: arguments) values index }
      (finished after answers [] []) := by
  let intermediate : Configuration :=
    { state := before, control := .returned [MORK.applySubst bindings argument]
      frames := [.argument bindings (.function head) arguments values index] }
  refine .step (u := intermediate) ?_
    (.step ?_ (single_sequence_answers program before after _ answers rest))
  · change step program _ = some _
    simp [step, raw, intermediate]
  · change step program _ = some _
    simp [step, intermediate]

theorem raw_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments values : List Atom) (index : Nat)
    (answer : List Atom)
    (raw : ∀ offset < arguments.length, argumentIsRaw program head (index + offset) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) []
          (values ++ arguments.map (MORK.applySubst bindings)) (index + arguments.length) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments values index }
      (finished after answer [] []) := by
  induction arguments generalizing values index with
  | nil => simpa using computed
  | cons argument arguments ih =>
      have firstRaw : argumentIsRaw program head index = true := by simpa using raw 0 (by simp)
      have tailRaw : ∀ offset < arguments.length,
          argumentIsRaw program head (index + 1 + offset) = true := by
        intro offset bounded
        simpa [Nat.add_assoc, Nat.add_comm 1] using raw (offset + 1) (by simpa using bounded)
      have tailComputed := ih (values ++ [MORK.applySubst bindings argument]) (index + 1)
        tailRaw (by simpa [List.map, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using computed)
      exact raw_argument_answers program bindings before after head argument arguments values index
        answer firstRaw tailComputed


theorem raw_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments values : List Atom) (index : Nat)
    (answer : Atom)
    (raw : ∀ offset < arguments.length, argumentIsRaw program head (index + offset) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) []
          (values ++ arguments.map (MORK.applySubst bindings)) (index + arguments.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments values index }
      (finished after [answer] [] []) :=
  raw_arguments_answers program bindings before after head arguments values index [answer] raw computed

theorem evaluated_argument_answers (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (target : Target) (argument value : Atom) (answer : List Atom)
    (arguments values : List Atom) (index : Nat)
    (demanded : (match target with
      | .function head => argumentIsRaw program head index
      | .data => false) = false)
    (first : PureReturns program bindings before argument middle value)
    (rest : (theory program).MultiStep
      { state := middle, control := .arguments bindings target arguments
          (values ++ [value]) (index + 1) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (argument :: arguments) values index }
      (finished after answer [] []) := by
  refine .step ?_ (path_trans
    (path_with_caller_frames program [.argument bindings target arguments values index] first) ?_)
  · change step program _ = some _
    simp [step, withFrames]
    exact demanded
  · refine .step ?_ (single_sequence_answers program middle after _ answer rest)
    change step program _ = some _
    simp [step, withFrames, finished]


theorem evaluated_argument_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (target : Target) (argument value answer : Atom)
    (arguments values : List Atom) (index : Nat)
    (demanded : (match target with
      | .function head => argumentIsRaw program head index
      | .data => false) = false)
    (first : PureReturns program bindings before argument middle value)
    (rest : (theory program).MultiStep
      { state := middle, control := .arguments bindings target arguments
          (values ++ [value]) (index + 1) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (argument :: arguments) values index }
      (finished after [answer] [] []) :=
  evaluated_argument_answers program bindings before middle after target argument value [answer] arguments values index demanded first rest

theorem variable_prefix_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (remaining values : List Atom)
    (index : Nat) (answer : List Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target remaining
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var ++ remaining) values index }
      (finished after answer [] []) := by
  induction names generalizing values index with
  | nil => simpa using computed
  | cons name names ih =>
      have rest := ih (values ++ [MORK.applySubst bindings (.var name)]) (index + 1)
        (by simpa [List.map, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using computed)
      cases demand : (match target with
        | .function head => argumentIsRaw program head index
        | .data => false) with
      | false =>
          exact evaluated_argument_answers program bindings before before after target
            (.var name) (MORK.applySubst bindings (.var name)) answer _ values index demand
            (variable_returns program bindings before name) rest
      | true =>
          let intermediate : Configuration :=
            { state := before, control := .returned [MORK.applySubst bindings (.var name)]
              frames := [.argument bindings target (names.map Atom.var ++ remaining) values index] }
          refine .step (u := intermediate) ?_
            (.step ?_ (single_sequence_answers program before after _ answer rest))
          · change step program _ = some _
            simp [step, intermediate]
            exact demand
          · change step program _ = some _
            simp [step, intermediate]

theorem variable_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (values : List Atom)
    (index : Nat) (answer : List Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target []
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var) values index }
      (finished after answer [] []) := by
  simpa only [List.append_nil] using variable_prefix_arguments_answers program bindings
    before after target names [] values index answer computed

theorem variable_prefix_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (remaining values : List Atom)
    (index : Nat) (answer : Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target remaining
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var ++ remaining) values index }
      (finished after [answer] [] []) :=
  variable_prefix_arguments_answers program bindings before after target names remaining values index [answer] computed


theorem variable_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (values : List Atom)
    (index : Nat) (answer : Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target []
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var) values index }
      (finished after [answer] [] []) :=
  variable_arguments_answers program bindings before after target names values index [answer] computed

theorem call_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : List Atom)
    (dispatch : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments [] 0 }
      (finished after answer [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    Returns program bindings before (.expression (.symbol head :: arguments)) after answer := by
  refine .step ?_ computed
  change step program _ = some _
  simp at ordinary
  rcases ordinary with ⟨notLet, notLetStar, notCase, notIf, notCollapse⟩
  simp only [step]
  split <;> simp_all <;> grind


theorem call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (dispatch : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments [] 0 }
      (finished after [answer] [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer :=
  call_answers program bindings before after head arguments [answer] dispatch computed ordinary

theorem raw_call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (dispatch : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = true)
    (raw : ∀ index < arguments.length, argumentIsRaw program head index = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) []
          (arguments.map (MORK.applySubst bindings)) arguments.length }
      (finished after [answer] [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer :=
  call_returns program bindings before after head arguments answer dispatch
    (raw_arguments_return program bindings before after head arguments [] 0 answer
      (by simpa using raw) (by simpa using computed)) ordinary

theorem native_variable_call_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (names : List String) (answers : List Atom)
    (ordinary : ioHead head = false)
    (native : SourcePrimitives.known head = true)
    (computed : SourcePrimitives.apply before head
      (names.map (fun name => MORK.applySubst bindings (.var name))) = .ok (after, answers))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    Returns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answers := by
  apply call_answers program bindings before after head (names.map Atom.var) answers
    (by simp [native]) _ notControl
  exact variable_arguments_answers program bindings before after (.function head) names [] 0 answers
    (by simpa using (native_function_arguments_answers program bindings before after head
      (names.map (fun name => MORK.applySubst bindings (.var name))) names.length
      answers ordinary native computed))

theorem native_variable_call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (names : List String) (answer : Atom)
    (ordinary : ioHead head = false)
    (native : SourcePrimitives.known head = true)
    (computed : SourcePrimitives.apply before head
      (names.map (fun name => MORK.applySubst bindings (.var name))) = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answer :=
  native_variable_call_answers program bindings before after head names [answer] ordinary native computed notControl

theorem native_binary_call_returns (program : Program) (bindings : MORK.Subst)
    (before firstState secondState after : State) (head : String)
    (left right leftValue rightValue answer : Atom)
    (ordinary : ioHead head = false) (native : SourcePrimitives.known head = true)
    (leftDemanded : argumentIsRaw program head 0 = false)
    (rightDemanded : argumentIsRaw program head 1 = false)
    (leftReturns : PureReturns program bindings before left firstState leftValue)
    (rightReturns : PureReturns program bindings firstState right secondState rightValue)
    (computed : SourcePrimitives.apply secondState head [leftValue, rightValue] = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after answer := by
  apply call_returns program bindings before after head [left, right] answer
    (by simp [native]) _ notControl
  have last := native_function_arguments_return program bindings secondState after head
    [leftValue, rightValue] 2 answer ordinary native computed
  have rest := evaluated_argument_returns program bindings firstState secondState after (.function head)
    right rightValue answer [] [leftValue] 1 rightDemanded rightReturns last
  exact evaluated_argument_returns program bindings before firstState after (.function head)
    left leftValue answer [right] [] 0 leftDemanded leftReturns rest

theorem native_unary_call_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (head : String) (argument value answer : Atom)
    (ordinary : ioHead head = false) (native : SourcePrimitives.known head = true)
    (demanded : argumentIsRaw program head 0 = false)
    (argumentReturns : PureReturns program bindings before argument middle value)
    (computed : SourcePrimitives.apply middle head [value] = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before (.expression [.symbol head, argument]) after answer := by
  apply call_returns program bindings before after head [argument] answer
    (by simp [native]) _ notControl
  exact evaluated_argument_returns program bindings before middle after (.function head) argument value answer
    [] [] 0 demanded argumentReturns
    (native_function_arguments_return program bindings middle after head [value] 1 answer ordinary native computed)

theorem authored_variable_call_returns (program : Program) (bindings callee : MORK.Subst)
    (before after : State) (head : String) (names : List String) (body answer : Atom)
    (ordinary : ioHead head = false)
    (authored : SourcePrimitives.known head = false)
    (dispatch : program.equations.any (·.head == head) = true)
    (selected : clauses program head
      (names.map (fun name => MORK.applySubst bindings (.var name))) = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer)
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answer := by
  apply call_returns program bindings before after head (names.map Atom.var) answer
    (by simp [dispatch]) _ notControl
  exact variable_arguments_return program bindings before after (.function head) names [] 0 answer
    (by simpa using (authored_function_arguments_return program bindings callee before after head
      (names.map (fun name => MORK.applySubst bindings (.var name))) names.length body answer
      ordinary authored selected computed))

theorem authored_binary_call_returns (program : Program) (bindings callee : MORK.Subst)
    (before firstState secondState after : State) (head : String)
    (left right leftValue rightValue body answer : Atom)
    (ordinary : ioHead head = false) (authored : SourcePrimitives.known head = false)
    (dispatch : program.equations.any (·.head == head) = true)
    (leftDemanded : argumentIsRaw program head 0 = false)
    (rightDemanded : argumentIsRaw program head 1 = false)
    (leftReturns : PureReturns program bindings before left firstState leftValue)
    (rightReturns : PureReturns program bindings firstState right secondState rightValue)
    (selected : clauses program head [leftValue, rightValue] = [.evaluate callee body])
    (computed : PureReturns program callee secondState body after answer)
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after answer := by
  apply call_returns program bindings before after head [left, right] answer (by simp [dispatch]) _ notControl
  apply evaluated_argument_returns program bindings before firstState after (.function head)
    left leftValue answer [right] [] 0 leftDemanded leftReturns
  apply evaluated_argument_returns program bindings firstState secondState after (.function head)
    right rightValue answer [] [leftValue] 1 rightDemanded rightReturns
  exact authored_function_arguments_return program bindings callee secondState after head
    [leftValue, rightValue] 2 body answer ordinary authored selected computed

theorem data_arguments_values_return (program : Program) (bindings : MORK.Subst)
    (state : State) (values : List Atom) (index : Nat) :
    (theory program).MultiStep
      { state, control := .arguments bindings .data [] values index }
      (finished state [.expression values] [] []) :=
  .step rfl (.refl _)

theorem data_call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (inert : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = false)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings .data (.symbol head :: arguments) [] 0 }
      (finished after [answer] [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer := by
  refine .step ?_ computed
  change step program _ = some _
  simp at ordinary
  rcases ordinary with ⟨notLet, notLetStar, notCase, notIf, notCollapse⟩
  simp only [step]
  split <;> simp_all

theorem constructor_variables_return (program : Program) (bindings : MORK.Subst)
    (state : State) (head : String) (names : List String)
    (inert : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings state
      (.expression (.symbol head :: names.map Atom.var)) state
      (.expression (.symbol head :: names.map (fun name => MORK.applySubst bindings (.var name)))) := by
  apply data_call_returns program bindings state state head (names.map Atom.var) _ inert _ ordinary
  have captured := variable_arguments_return program bindings state state .data names [.symbol head] 1 _
    (data_arguments_values_return program bindings state _ (1 + names.length))
  exact evaluated_argument_returns program bindings state state state .data (.symbol head) (.symbol head)
    _ (names.map Atom.var) [] 0 rfl (symbol_returns program bindings state head) captured

/-- A tuple whose first source element is a variable is data syntax. Captured
elements remain values even when one of them contains an executable head. -/
theorem tuple_variables_return (program : Program) (bindings : MORK.Subst)
    (state : State) (names : List String) :
    PureReturns program bindings state (.expression (names.map Atom.var)) state
      (.expression (names.map (fun name => MORK.applySubst bindings (.var name)))) := by
  let intermediate : Configuration :=
    { state := state, control := .arguments bindings .data (names.map Atom.var) [] 0 }
  refine .step (u := intermediate) ?_ ?_
  · cases names <;> rfl
  · exact variable_arguments_return program bindings state state .data names [] 0 _
      (by simpa using data_arguments_values_return program bindings state _ names.length)

theorem unary_constructor_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (head name : String)
    (inert : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings state (.expression [.symbol head, .var name]) state
      (.expression [.symbol head, MORK.applySubst bindings (.var name)]) :=
  constructor_variables_return program bindings state head [name] inert ordinary

theorem empty_constructor_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (head : String)
    (inert : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"]) :
    PureReturns program bindings state
      (.expression [.symbol head, .expression []]) state
      (.expression [.symbol head, .expression []]) := by
  apply data_call_returns program bindings state state head [.expression []] _ inert _ ordinary
  apply evaluated_argument_returns program bindings state state state .data
    (.symbol head) (.symbol head) _ [.expression []] [] 0 rfl
    (symbol_returns program bindings state head)
  apply evaluated_argument_returns program bindings state state state .data
    (.expression []) (.expression []) _ [] [.symbol head] 1 rfl
    (.step rfl (.step rfl (.refl _)))
  exact data_arguments_values_return program bindings state _ 2

theorem unary_constructor_of_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (expression value : Atom)
    (inert : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"])
    (computed : PureReturns program bindings before expression after value) :
    PureReturns program bindings before (.expression [.symbol head, expression]) after
      (.expression [.symbol head, value]) := by
  apply data_call_returns program bindings before after head [expression] _ inert _ ordinary
  apply evaluated_argument_returns program bindings before before after .data
    (.symbol head) (.symbol head) _ [expression] [] 0 rfl
    (symbol_returns program bindings before head)
  apply evaluated_argument_returns program bindings before after after .data
    expression value _ [] [.symbol head] 1 rfl computed
  exact data_arguments_values_return program bindings after _ 2

theorem binary_constructor_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (head : String) (left right leftValue rightValue : Atom)
    (inert : (ioHead head || SourcePrimitives.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse"])
    (leftReturns : PureReturns program bindings before left middle leftValue)
    (rightReturns : PureReturns program bindings middle right after rightValue) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after
      (.expression [.symbol head, leftValue, rightValue]) := by
  apply data_call_returns program bindings before after head [left, right] _ inert _ ordinary
  apply evaluated_argument_returns program bindings before before after .data
    (.symbol head) (.symbol head) _ [left, right] [] 0 rfl
    (symbol_returns program bindings before head)
  apply evaluated_argument_returns program bindings before middle after .data
    left leftValue _ [right] [.symbol head] 1 rfl leftReturns
  apply evaluated_argument_returns program bindings middle after after .data
    right rightValue _ [] [.symbol head, leftValue] 2 rfl rightReturns
  exact data_arguments_values_return program bindings after _ 3

/-- A native space query followed by `collapse` retains its ordered answers,
including empty queries and duplicate occurrences. -/
theorem match_collapse_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (spaceName : String) (pattern template : Atom) (answers : List Atom)
    (queried : SourcePrimitives.apply before "match"
      [MORK.applySubst bindings (.var spaceName), MORK.applySubst bindings pattern,
        MORK.applySubst bindings template] = .ok (after, answers)) :
    PureReturns program bindings before (.expression [.symbol "collapse",
      .expression [.symbol "match", .var spaceName, pattern, template]]) after (.expression answers) := by
  apply collapse_returns program bindings before after _ answers
  apply call_answers program bindings before after "match" [.var spaceName, pattern, template]
    answers (by simp [SourcePrimitives.known]) _ (by decide)
  have queriedPath := native_function_arguments_answers program bindings before after "match"
    [MORK.applySubst bindings (.var spaceName), MORK.applySubst bindings pattern,
      MORK.applySubst bindings template] 3 answers (by decide) (by decide) queried
  have tailPath := raw_arguments_answers program bindings before after "match" [pattern, template]
    [MORK.applySubst bindings (.var spaceName)] 1 answers
    (by intro offset bounded; have : offset < 2 := bounded
        have positions : offset = 0 ∨ offset = 1 := by omega
        rcases positions with rfl | rfl <;>
          simp [argumentIsRaw, SourcePrimitives.known, SourcePrimitives.rawArgument])
    (by simpa using queriedPath)
  exact evaluated_argument_answers program bindings before before after (.function "match")
    (.var spaceName) (MORK.applySubst bindings (.var spaceName)) answers [pattern, template] [] 0
    (by simp [argumentIsRaw, SourcePrimitives.known, SourcePrimitives.rawArgument])
    (variable_returns program bindings before spaceName) tailPath

end Mettapedia.Languages.MeTTa.PeTTa.SourceExecution
