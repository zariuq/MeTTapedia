import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedEveryRun

/-!
# Grounded operations on HE's table, on every run: runtime errors, declined calls, PeTTa's faults

`GroundedTables` gives HE's table operation by operation (`measuredOutcome`). Here HE's world
machine runs with it, read-only (`WorldServices.readOnlyGrounded`), and the outcomes that are not a
value are read on every complete run.

## The two outcomes without a value, for any grounded dispatch

* `declined_steps`, `declined_source_of`, `declined_every_run`: a host operation that declines its
  arguments (`incorrectArgument`): HE's grounded call takes `callGroundedDone` with the
  `incorrectArgument` plan, which returns the call itself; a complete run exists, and every
  complete run publishes the call. Every derivation goes through the host call: the program's
  equations for the operation's name are never consulted (`CallRel.equations` needs a call that is
  not a host call).
* `error_steps`, `error_source_of`, `error_every_run_of`: a host operation that reports the runtime
  error `m`: the `runtimeError` plan returns `(Error call m)`, which success priority keeps, since
  no other answer exists; a complete run exists, and every complete run publishes `(Error call m)`.
* `verdict_every_run`: the contract on a grounded table (`GroundedTables.GroundedTable.Contract`)
  read on one call: the table's verdict (an answer, a decline, an error) publishes one list, a
  complete run exists, and every complete run publishes that list. Both of HE's tables meet the
  contract (`GroundedTables.model_contract`, `GroundedTables.measured_contract`).

## Controls, on HE's table against PeTTa's machine

* `Controls.zero_divisor_every_run`: `(% 7 0)`: every complete HE run publishes
  `(Error (% 7 0) DivisionByZero)`; PeTTa stops at the `zeroDivisor` fault, with no value.
* `Controls.division_by_zero_every_run`: `(/ 7 0)`: every complete HE run publishes
  `(Error (/ 7 0) DivisionByZero)` (the PeTTa model has no `/`).
* `Controls.overflow_every_run`: `(+ 9223372036854775807 1)`: every complete HE run publishes
  `(Error (+ 9223372036854775807 1) IntegerOverflow)`; PeTTa yields `9223372036854775808`.
* `Controls.non_numeric_every_run`: `(+ a 4)`: every complete HE run publishes `(+ a 4)`; PeTTa stops
  at the `invalidArguments` fault, with no value.
* `Controls.model_overflow_every_run`: the parting run of the two tables. With the model's table,
  `(+ 9223372036854775807 1)` settles and every complete run publishes `9223372036854775808`; it is
  outside the class of HE's table, which errs there.

The reason is one design split: HE's grounded operations report a missing value or an error as
data; PeTTa's primitives raise, and with no enclosing handler the request has no answer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace GroundedDifferences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load WorldSteps)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation WorldConfiguration)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables GroundedTables GroundedRuns
  GroundedEveryRun

variable {lookup : CastLookup} {policy : Policy}

/-! ## Finishing on errors -/

/-- **An error answer is closed** when the call it reports is. -/
theorem error_closed {call : Atom}
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs call name)
    (message : String) :
    ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (Atom.error call (.symbol message)) name := by
  intro name occurs
  cases occurs with
  | expression member inner =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · cases inner
      · exact closed name inner
      · cases inner

theorem error_isError (call : Atom) (message : String) :
    isErrorAtom (Atom.error call (.symbol message)) = true := rfl

/-- **A batch of closed error answers is published as it is**: success priority keeps every error
when no answer succeeds. -/
theorem finish_error_steps {dispatch : GroundedDispatch} {atoms : List Atom} {live : List Atom}
    {scope : List String} (c : Atom) (results : List Result)
    (closed : ∀ r ∈ results, ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs r.1.erase name)
    (errors : ∀ r ∈ results, isErrorAtom r.1.erase = true)
    (stack : List Continuation) (emitted : List Result) :
    ∃ published : List Result,
      published.map (fun r => r.1.erase) = results.map (fun r => r.1.erase) ∧
      HERuns.HESteps dispatch lookup policy
        ⟨Space.ofList atoms, .returning results,
          .append (.calls live scope Atom.undefinedType []) :: .publish c :: stack, emitted⟩
        ⟨Space.ofList atoms, .returning published, stack, emitted⟩ := by
  have unchanged : (results ++ []).map (Completed.readResult policy) = results := by
    rw [List.append_nil]
    exact map_fixed fun r member => HERuns.readResult_closed policy r (closed r member)
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ((results ++ []).map (Completed.readResult policy)) results := by
    rw [unchanged]
    exact .allErrors errors
  refine ⟨results.map (Completed.publishResult policy c), ?_, ?_⟩
  · simp [Completed.publishResult]
  · refine .head (.internal .append) ?_
    refine .head (.internal .callsNil) ?_
    refine .head (.internal .prepend) ?_
    exact .single (.internal (.publish selected))

/-! ## A host operation that declines its arguments -/

section Generic

variable {dispatch : GroundedDispatch}

theorem call_items {op : String} {args : List Atom} (head : DataAtom (.symbol op))
    (arguments : ∀ a ∈ args, DataAtom a) : ∀ x ∈ Atom.symbol op :: args, DataAtom x := by
  intro x member
  rcases List.mem_cons.mp member with rfl | inArgs
  · exact head
  · exact arguments x inArgs

/-- **A complete run on a declined host call** publishes the call itself. -/
theorem declined_steps (noMinimal : dispatch.minimal = none) (minimal : Minimal.Services)
    (answers : AnswersUndefined lookup) {atoms : List Atom} {op : String} {args : List Atom}
    (executable : dispatch.executable (.symbol op)) (head : DataAtom (.symbol op))
    (arguments : ∀ a ∈ args, DataAtom a)
    (declines : dispatch.outcome (.symbol op) args .incorrectArgument)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = []) :
    ∃ emitted : List Result,
      emitted.map (fun r => r.1.erase) = [.expression (.symbol op :: args)] ∧
      WorldSteps (fun (_ : Unit) => id) (WorldServices.readOnlyGrounded minimal dispatch) dispatch
        lookup policy
        (WorldConfiguration.ofReadOnly
          (load (Space.ofList atoms) (.expression (.symbol op :: args)) Atom.undefinedType))
        (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩) := by
  have clean : ∀ r ∈ [(callValue op args, Completed.Frame.empty)], Answerable r.1.erase := by
    intro r member
    rw [List.mem_singleton] at member
    subst member
    rw [callValue_erase]
    exact call_answerable head arguments
  obtain ⟨published, erased, finish⟩ := HERuns.finish_steps (dispatch := dispatch)
    (lookup := lookup) (policy := policy) (atoms := atoms) (live := []) (scope := [])
    (.expression (.symbol op :: args)) [(callValue op args, Completed.Frame.empty)] clean [] []
  have produced : (WorldServices.readOnlyGrounded minimal dispatch).groundedAt (Space.ofList atoms)
      () [] [] Completed.Frame.empty (callValue op args) .incorrectArgument () :=
    ⟨.symbol op, args, .incorrectArgument, callValue_erase op args, declines, rfl⟩
  have planned : Completed.NativeOutcomeRel policy dispatch (.symbol op) args
      (callValue op args) (some Atom.undefinedType) Completed.Frame.empty .incorrectArgument
      (.done [(callValue op args, Completed.Frame.empty)]) :=
    .incorrectArgument
  have notError : ¬ IsErrorRel (callValue op args).erase :=
    HERuns.value_not_error head (callValue_erase op args)
  refine ⟨[] ++ published, by simp [erased, callValue_erase], ?_⟩
  refine .trans (lift_path_of noMinimal _ (HERuns.call_entry_steps answers (call_items head arguments)
    untyped [] [] Completed.Frame.empty [] [])) ?_
  refine .head (.internal
    (Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.WorldLocalStepWith.callGroundedDone
      (callValue_erase op args) executable notError produced planned)) ?_
  exact .trans (lift_path_of noMinimal _ finish)
    (lift_path_of noMinimal _ (HERuns.publish_all _ published []))

variable {minimal : Minimal.Services}

/-- **The grounded-head rule**: every derivation of a host call whose operation declines its
arguments returns the call itself. No derivation consults the program's equations for the
operation's name, whatever equations the program gives it. -/
theorem declined_source_of {atoms : List Atom} {op : String} {args : List Atom}
    (executable : dispatch.executable (.symbol op)) (head : DataAtom (.symbol op))
    (declines : ∀ outcome, dispatch.outcome (.symbol op) args outcome →
      outcome = .incorrectArgument)
    {live : List Atom} {scope : List String} {after : Frame} {children : List Result}
    {w₁ w₂ : Unit}
    (called : Completed.Stateful.CallRel (worldEnvOf minimal dispatch lookup) (Space.ofList atoms)
      w₁ live scope (callValue op args) Atom.undefinedType after children w₂ (policy := policy)) :
    children = [(callValue op args, after)] := by
  have host : Minimal.HostCall dispatch (callValue op args).erase :=
    ⟨.symbol op, args, callValue_erase op args, executable⟩
  have outcomeOf : ∀ {outcome : GroundedResult Entry.Value} {w₃ w₄ : Unit},
      (WorldServices.readOnlyGrounded minimal dispatch).groundedAt (Space.ofList atoms) w₃ live
        scope after (callValue op args) outcome w₄ → outcome = .incorrectArgument := by
    intro outcome w₃ w₄ produced
    obtain ⟨operator, arguments, raw, shaped, executed, rfl⟩ := produced
    rw [callValue_erase] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    obtain ⟨rfl, rfl⟩ := shaped
    rw [declines raw executed]
    rfl
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head (callValue_erase op _))
  | embedded _ notHost _ _ _ => exact absurd host notHost
  | absent _ nonGrounded _ => exact absurd host nonGrounded.1
  | equations _ nonGrounded _ _ _ => exact absurd host nonGrounded.1
  | groundedDone _ _ _ produced planned =>
      rw [outcomeOf produced] at planned
      cases planned
      rfl
  | groundedResume _ _ _ produced planned _ =>
      rw [outcomeOf produced] at planned
      cases planned

/-- **Every complete run on a declined host call publishes the call itself.** -/
theorem declined_every_run (contract : LookupContract lookup) {atoms : List Atom} {op : String}
    {args : List Atom} (executable : dispatch.executable (.symbol op)) (head : DataAtom (.symbol op))
    (arguments : ∀ a ∈ args, DataAtom a)
    (declines : ∀ outcome, dispatch.outcome (.symbol op) args outcome →
      outcome = .incorrectArgument)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = [])
    (emitted : List Result)
    (run : WorldSteps (fun (_ : Unit) => id) (WorldServices.readOnlyGrounded minimal dispatch)
      dispatch lookup policy
      (WorldConfiguration.ofReadOnly
        (load (Space.ofList atoms) (.expression (.symbol op :: args)) Atom.undefinedType))
      (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩)) :
    emitted.map (fun r => r.1.erase) = [.expression (.symbol op :: args)] := by
  obtain ⟨after, children, selected, w₁, w₂, called, chosen, erased⟩ :=
    call_source_of contract head arguments untyped (complete_source_of run)
  rw [declined_source_of executable head declines called] at chosen
  exact single_call_published (call_answerable head arguments) chosen erased

/-! ## A host operation that reports a runtime error -/

/-- The error answer of a host call. -/
def errorValue (op : String) (args : List Atom) (message : String) : Entry.Value :=
  Entry.Value.ofAtom (Atom.error (.expression (.symbol op :: args)) (.symbol message))

theorem errorValue_erase (op : String) (args : List Atom) (message : String) :
    (errorValue op args message).erase =
      Atom.error (.expression (.symbol op :: args)) (.symbol message) :=
  Entry.Value.erase_ofAtom _

/-- **A complete run on a host call that reports a runtime error** publishes the error. -/
theorem error_steps (noMinimal : dispatch.minimal = none) (minimal : Minimal.Services)
    (answers : AnswersUndefined lookup) {atoms : List Atom} {op : String} {args : List Atom}
    (executable : dispatch.executable (.symbol op)) (head : DataAtom (.symbol op))
    (arguments : ∀ a ∈ args, DataAtom a) {message : String}
    (fails : dispatch.outcome (.symbol op) args (.runtimeError message))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = []) :
    ∃ emitted : List Result,
      emitted.map (fun r => r.1.erase) =
        [Atom.error (.expression (.symbol op :: args)) (.symbol message)] ∧
      WorldSteps (fun (_ : Unit) => id) (WorldServices.readOnlyGrounded minimal dispatch) dispatch
        lookup policy
        (WorldConfiguration.ofReadOnly
          (load (Space.ofList atoms) (.expression (.symbol op :: args)) Atom.undefinedType))
        (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩) := by
  have callClosed := (call_answerable head arguments).closed
  have closed : ∀ r ∈ [(errorValue op args message, Completed.Frame.empty)], ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs r.1.erase name := by
    intro r member
    rw [List.mem_singleton] at member
    subst member
    rw [errorValue_erase]
    exact error_closed callClosed message
  have errors : ∀ r ∈ [(errorValue op args message, Completed.Frame.empty)],
      isErrorAtom r.1.erase = true := by
    intro r member
    rw [List.mem_singleton] at member
    subst member
    rw [errorValue_erase]
    rfl
  obtain ⟨published, erased, finish⟩ := finish_error_steps (dispatch := dispatch)
    (lookup := lookup) (policy := policy) (atoms := atoms) (live := []) (scope := [])
    (.expression (.symbol op :: args)) [(errorValue op args message, Completed.Frame.empty)] closed
    errors [] []
  have produced : (WorldServices.readOnlyGrounded minimal dispatch).groundedAt (Space.ofList atoms)
      () [] [] Completed.Frame.empty (callValue op args) (.runtimeError message) () :=
    ⟨.symbol op, args, .runtimeError message, callValue_erase op args, fails, rfl⟩
  have planned : Completed.NativeOutcomeRel policy dispatch (.symbol op) args
      (callValue op args) (some Atom.undefinedType) Completed.Frame.empty (.runtimeError message)
      (.done [(errorValue op args message, Completed.Frame.empty)]) := by
    have rule := Completed.NativeOutcomeRel.runtimeError (policy := policy) (dispatch := dispatch)
      (operator := .symbol op) (arguments := args) (original := callValue op args)
      (expected := some Atom.undefinedType) (frame := Completed.Frame.empty) message
    rwa [callValue_erase] at rule
  have notError : ¬ IsErrorRel (callValue op args).erase :=
    HERuns.value_not_error head (callValue_erase op args)
  refine ⟨[] ++ published, by simp [erased, errorValue_erase], ?_⟩
  refine .trans (lift_path_of noMinimal _ (HERuns.call_entry_steps answers (call_items head arguments)
    untyped [] [] Completed.Frame.empty [] [])) ?_
  refine .head (.internal
    (Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.WorldLocalStepWith.callGroundedDone
      (callValue_erase op args) executable notError produced planned)) ?_
  exact .trans (lift_path_of noMinimal _ finish)
    (lift_path_of noMinimal _ (HERuns.publish_all _ published []))

/-- **Every derivation of a host call that reports a runtime error returns the error.** -/
theorem error_source_of {atoms : List Atom} {op : String} {args : List Atom}
    (executable : dispatch.executable (.symbol op)) (head : DataAtom (.symbol op)) {message : String}
    (fails : ∀ outcome, dispatch.outcome (.symbol op) args outcome →
      outcome = .runtimeError message)
    {live : List Atom} {scope : List String} {after : Frame} {children : List Result}
    {w₁ w₂ : Unit}
    (called : Completed.Stateful.CallRel (worldEnvOf minimal dispatch lookup) (Space.ofList atoms)
      w₁ live scope (callValue op args) Atom.undefinedType after children w₂ (policy := policy)) :
    children = [(errorValue op args message, after)] := by
  have host : Minimal.HostCall dispatch (callValue op args).erase :=
    ⟨.symbol op, args, callValue_erase op args, executable⟩
  have outcomeOf : ∀ {outcome : GroundedResult Entry.Value} {w₃ w₄ : Unit},
      (WorldServices.readOnlyGrounded minimal dispatch).groundedAt (Space.ofList atoms) w₃ live
        scope after (callValue op args) outcome w₄ → outcome = .runtimeError message := by
    intro outcome w₃ w₄ produced
    obtain ⟨operator, arguments, raw, shaped, executed, rfl⟩ := produced
    rw [callValue_erase] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    obtain ⟨rfl, rfl⟩ := shaped
    rw [fails raw executed]
    rfl
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head (callValue_erase op _))
  | embedded _ notHost _ _ _ => exact absurd host notHost
  | absent _ nonGrounded _ => exact absurd host nonGrounded.1
  | equations _ nonGrounded _ _ _ => exact absurd host nonGrounded.1
  | groundedDone _ _ _ produced planned =>
      rw [outcomeOf produced] at planned
      cases planned
      simp only [errorValue, callValue_erase]
  | groundedResume _ _ _ produced planned _ =>
      rw [outcomeOf produced] at planned
      cases planned

/-- **Every complete run on a host call that reports a runtime error publishes the error.** -/
theorem error_every_run_of (contract : LookupContract lookup) {atoms : List Atom} {op : String}
    {args : List Atom} (executable : dispatch.executable (.symbol op)) (head : DataAtom (.symbol op))
    (arguments : ∀ a ∈ args, DataAtom a) {message : String}
    (fails : ∀ outcome, dispatch.outcome (.symbol op) args outcome →
      outcome = .runtimeError message)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = [])
    (emitted : List Result)
    (run : WorldSteps (fun (_ : Unit) => id) (WorldServices.readOnlyGrounded minimal dispatch)
      dispatch lookup policy
      (WorldConfiguration.ofReadOnly
        (load (Space.ofList atoms) (.expression (.symbol op :: args)) Atom.undefinedType))
      (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩)) :
    emitted.map (fun r => r.1.erase) =
      [Atom.error (.expression (.symbol op :: args)) (.symbol message)] := by
  obtain ⟨after, children, selected, w₁, w₂, called, chosen, erased⟩ :=
    call_source_of contract head arguments untyped (complete_source_of run)
  rw [error_source_of executable head fails called] at chosen
  have closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (errorValue op args message, after).1.erase name := by
    rw [errorValue_erase]
    exact error_closed (call_answerable head arguments).closed message
  have unchanged : [(errorValue op args message, after)].map (Completed.readResult policy) =
      [(errorValue op args message, after)] := by
    rw [List.map_singleton, HERuns.readResult_closed policy _ closed]
  rw [unchanged] at chosen
  have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional chosen
    (.allErrors fun r member => by
      rw [List.mem_singleton] at member
      subst member
      rw [errorValue_erase]
      rfl)
  rw [erased, same]
  simp [errorValue_erase]

end Generic

/-! ## The contract on one call -/

/-- **What HE's machine publishes for a call, by the table's verdict**: the value the table answers,
the call itself when it declines, `(Error call m)` when it errs with `m`. -/
inductive VerdictPublishes (T : GroundedTable) (op : String) (args : List Atom) : List Atom → Prop
  | answers {v : Atom} : DataAtom v → v ≠ Atom.notReducible → T.Answers (.symbol op) args v →
      VerdictPublishes T op args [v]
  | declines : T.Declines (.symbol op) args →
      VerdictPublishes T op args [.expression (.symbol op :: args)]
  | errs {message : String} : T.Errs (.symbol op) args message →
      VerdictPublishes T op args [Atom.error (.expression (.symbol op :: args)) (.symbol message)]

/-- A table's verdict on a call publishes one list. -/
theorem VerdictPublishes.unique {T : GroundedTable} {op : String} {args : List Atom} {L₁ L₂ : List Atom}
    (first : VerdictPublishes T op args L₁) (second : VerdictPublishes T op args L₂) : L₁ = L₂ := by
  cases first with
  | answers _ _ answered =>
      cases second with
      | answers _ _ again => rw [GroundedTable.answers_unique answered again]
      | declines declined => exact absurd declined (GroundedTable.answers_not_declines answered)
      | errs failed => exact absurd failed (GroundedTable.answers_not_errs answered)
  | declines declined =>
      cases second with
      | answers _ _ answered => exact absurd declined (GroundedTable.answers_not_declines answered)
      | declines _ => rfl
      | errs failed => exact absurd failed (GroundedTable.declines_not_errs declined)
  | errs failed =>
      cases second with
      | answers _ _ answered => exact absurd failed (GroundedTable.answers_not_errs answered)
      | declines declined => exact absurd failed (GroundedTable.declines_not_errs declined)
      | errs again =>
          have same := (again.2 _).mp ((failed.2 _).mpr rfl)
          cases same
          rfl

/-- **Every complete run of HE's world machine with the table `T` on the call `(op args)` publishes
`L`, and one exists.** -/
def CallPublishes (minimal : Minimal.Services) (T : GroundedTable) (lookup : CastLookup)
    (policy : Policy) (atoms : List Atom) (op : String) (args : List Atom) (L : List Atom) : Prop :=
  (∃ emitted : List Result,
    WorldSteps (fun (_ : Unit) => id) (services minimal T) T.dispatch lookup policy
      (WorldConfiguration.ofReadOnly
        (load (Space.ofList atoms) (.expression (.symbol op :: args)) Atom.undefinedType))
      (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩) ∧
    emitted.map (fun r => r.1.erase) = L) ∧
  ∀ emitted : List Result,
    WorldSteps (fun (_ : Unit) => id) (services minimal T) T.dispatch lookup policy
      (WorldConfiguration.ofReadOnly
        (load (Space.ofList atoms) (.expression (.symbol op :: args)) Atom.undefinedType))
      (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩) →
    emitted.map (fun r => r.1.erase) = L

/-- **A verdict, on every run**: for a call of data arguments whose operator the program does not
declare, the list a table's verdict publishes is what every complete run publishes, and one exists. -/
theorem verdict_runs {T : GroundedTable} {op : String} {args : List Atom} {L : List Atom}
    (verdict : VerdictPublishes T op args L) (minimal : Minimal.Services)
    (answers : AnswersUndefined lookup) (lookupContract : LookupContract lookup) (policy : Policy)
    {atoms : List Atom} (head : DataAtom (.symbol op)) (arguments : ∀ a ∈ args, DataAtom a)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = []) :
    CallPublishes minimal T lookup policy atoms op args L := by
  cases verdict with
  | @answers v data notRefused table =>
      refine ⟨?_, fun emitted run => ?_⟩
      · obtain ⟨R, eraseR, path⟩ := he_answer_W minimal (policy := policy) answers head arguments data
          notRefused table untyped [] [] Completed.Frame.empty [] []
        exact ⟨R, path.trans (lift_path minimal (HERuns.publish_all _ R [])), eraseR⟩
      · obtain ⟨after, children, selected, w₁, w₂, called, chosen, erased⟩ :=
          call_source_W lookupContract head arguments untyped (complete_source_W run)
        have erasedChildren := answer_source_W lookupContract head data notRefused table called
        have clean : ∀ r ∈ children, Answerable r.1.erase := by
          intro r member
          have inside : r.1.erase ∈ [v] := by
            rw [← erasedChildren]
            exact List.mem_map.mpr ⟨r, member, rfl⟩
          rw [List.mem_singleton] at inside
          rw [inside]
          exact answerable_of_data data
        have unchanged : children.map (Completed.readResult policy) = children :=
          map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
        rw [unchanged] at chosen
        have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
          chosen (HERuns.success_all children fun r member => (clean r member).notError)
        rw [erased, same, erasedChildren]
  | declines declines =>
      refine ⟨?_, fun emitted run =>
        declined_every_run (dispatch := T.dispatch) lookupContract declines.1 head arguments
          (fun outcome produced => (declines.2 outcome).mp produced) untyped emitted run⟩
      obtain ⟨emitted, erased, run⟩ := declined_steps (dispatch := T.dispatch) (policy := policy) rfl
        minimal answers (atoms := atoms) declines.1 head arguments ((declines.2 _).mpr rfl) untyped
      exact ⟨emitted, run, erased⟩
  | errs errs =>
      refine ⟨?_, fun emitted run =>
        error_every_run_of (dispatch := T.dispatch) lookupContract errs.1 head arguments
          (fun outcome produced => (errs.2 outcome).mp produced) untyped emitted run⟩
      obtain ⟨emitted, erased, run⟩ := error_steps (dispatch := T.dispatch) (policy := policy) rfl
        minimal answers (atoms := atoms) errs.1 head arguments ((errs.2 _).mpr rfl) untyped
      exact ⟨emitted, run, erased⟩

/-- **The contract, read on one call, on every run.** For a table meeting the contract, and an
operator it executes, applied to data arguments and undeclared in the program, the table's verdict
publishes one list: a complete run of HE's world machine with the table exists, and every complete
run publishes that list. -/
theorem verdict_every_run {T : GroundedTable} (contract : T.Contract) (minimal : Minimal.Services)
    (answers : AnswersUndefined lookup) (lookupContract : LookupContract lookup) (policy : Policy)
    {atoms : List Atom} {op : String} {args : List Atom} (executes : T.executes (.symbol op))
    (head : DataAtom (.symbol op)) (arguments : ∀ a ∈ args, DataAtom a)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = []) :
    ∃ L : List Atom, VerdictPublishes T op args L ∧ CallPublishes minimal T lookup policy atoms op args L := by
  rcases contract (.symbol op) args executes with ⟨v, data, notRefused, table⟩ | declines |
    ⟨message, errs⟩
  · exact ⟨_, .answers data notRefused table, verdict_runs (.answers data notRefused table) minimal
      answers lookupContract policy head arguments untyped⟩
  · exact ⟨_, .declines declines, verdict_runs (.declines declines) minimal answers lookupContract
      policy head arguments untyped⟩
  · exact ⟨_, .errs errs, verdict_runs (.errs errs) minimal answers lookupContract policy head
      arguments untyped⟩

/-- **The model's machine does not read the types of a grounded call's arguments.** On two programs
that both leave the operator undeclared, whatever else they declare (types for the arguments
included), every complete run of the call publishes the same list, the table's verdict. HE reads
such declarations: it checks the call against the operation's type first
(`GroundedTables.TypedRegion`, and the controls below). -/
theorem machine_reads_no_argument_types {T : GroundedTable} (contract : T.Contract)
    (minimal : Minimal.Services) (answers : AnswersUndefined lookup)
    (lookupContract : LookupContract lookup) (policy : Policy) {atoms₁ atoms₂ : List Atom}
    {op : String} {args : List Atom} (executes : T.executes (.symbol op))
    (head : DataAtom (.symbol op)) (arguments : ∀ a ∈ args, DataAtom a)
    (untyped₁ : (Space.ofList atoms₁).atoms.filter (typeRegion (.symbol op)) = [])
    (untyped₂ : (Space.ofList atoms₂).atoms.filter (typeRegion (.symbol op)) = []) :
    ∃ L : List Atom, VerdictPublishes T op args L ∧
      CallPublishes minimal T lookup policy atoms₁ op args L ∧
      CallPublishes minimal T lookup policy atoms₂ op args L := by
  obtain ⟨L₁, first, publishes₁⟩ := verdict_every_run contract minimal answers lookupContract policy
    (atoms := atoms₁) executes head arguments untyped₁
  obtain ⟨L₂, second, publishes₂⟩ := verdict_every_run contract minimal answers lookupContract policy
    (atoms := atoms₂) executes head arguments untyped₂
  rw [first.unique second] at publishes₁
  exact ⟨L₂, second, publishes₁, publishes₂⟩

/-- The fault a stopped PeTTa run holds: its one remaining job is a fault at the root. -/
def stoppedAt : List Streaming.Job → Option Effects.Fault
  | [.execute ⟨.fault reason, []⟩] => some reason
  | _ => none

namespace Controls

open AnswerBags.Controls (sym app)

/-- HE's read-only host services with HE's table. -/
abbrev measuredServices (minimal : Minimal.Services) : WorldServices Space Unit :=
  WorldServices.readOnlyGrounded minimal measuredDispatch

theorem executable_of (name : String) (member : name ∈ measuredNames) :
    measuredDispatch.executable (.symbol name) := ⟨name, rfl, member⟩

theorem outcome_eq {op : String} {args : List Atom} {result : GroundedResult}
    (computed : measuredOutcome (.symbol op) args = result) :
    ∀ outcome, measuredDispatch.outcome (.symbol op) args outcome → outcome = result := by
  intro outcome same
  exact same.trans computed

theorem symbol_head (name : String) (notError : name ≠ "Error") (notEmpty : name ≠ "Empty") :
    DataAtom (.symbol name) := .symbol notEmpty notError

/-- **Division by zero, on both machines**: `(% 7 0)`, a call in HE's typed region. On HE's table a
complete run of HE's world machine exists, and every complete run publishes
`(Error (% 7 0) DivisionByZero)`; PeTTa's run stops at the `zeroDivisor` fault, with no value. -/
theorem zero_divisor_every_run (minimal : Minimal.Services) (policy : Policy) :
    TypedRegion [] "%" [num 7, num 0] ∧
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "%" [num 7, num 0])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "%" [num 7, num 0])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) =
          [Atom.error (app "%" [num 7, num 0]) (sym "DivisionByZero")]) ∧
      stoppedAt (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "%" [num 7, num 0]))).agenda =
          some .zeroDivisor ∧
      Streaming.values (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "%" [num 7, num 0]))) = [] := by
  have head := symbol_head "%" (by decide) (by decide)
  have arguments : ∀ a ∈ [num 7, num 0], DataAtom a := by
    intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .grounded _
  have computed : measuredOutcome (.symbol "%") [num 7, num 0] = .runtimeError "DivisionByZero" := by
    decide
  have untyped : (Space.ofList []).atoms.filter (typeRegion (.symbol "%")) = [] := rfl
  obtain ⟨R, _, path⟩ := error_steps (policy := policy) measuredDispatch_minimal minimal raw_answers
    (atoms := []) (executable_of "%" (by decide)) head arguments computed.symm untyped
  exact ⟨by decide +kernel, ⟨⟨R, path⟩, fun emitted run => error_every_run_of raw_contract
    (executable_of "%" (by decide)) head arguments (outcome_eq computed) untyped emitted run⟩,
    by decide +kernel, by decide +kernel⟩

/-- **Division by zero with `/`**: `(/ 7 0)`, a call in HE's typed region. On HE's table a complete
run exists, and every complete run publishes `(Error (/ 7 0) DivisionByZero)`. -/
theorem division_by_zero_every_run (minimal : Minimal.Services) (policy : Policy) :
    TypedRegion [] "/" [num 7, num 0] ∧
    (∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "/" [num 7, num 0])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "/" [num 7, num 0])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) =
          [Atom.error (app "/" [num 7, num 0]) (sym "DivisionByZero")] := by
  have head := symbol_head "/" (by decide) (by decide)
  have arguments : ∀ a ∈ [num 7, num 0], DataAtom a := by
    intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .grounded _
  have computed : measuredOutcome (.symbol "/") [num 7, num 0] = .runtimeError "DivisionByZero" := by
    decide
  have untyped : (Space.ofList []).atoms.filter (typeRegion (.symbol "/")) = [] := rfl
  obtain ⟨R, _, path⟩ := error_steps (policy := policy) measuredDispatch_minimal minimal raw_answers
    (atoms := []) (executable_of "/" (by decide)) head arguments computed.symm untyped
  exact ⟨by decide +kernel, ⟨R, path⟩, fun emitted run => error_every_run_of raw_contract
    (executable_of "/" (by decide)) head arguments (outcome_eq computed) untyped emitted run⟩

/-- **Overflow, on both machines**: `(+ 9223372036854775807 1)`, a call in HE's typed region. On
HE's table a complete run exists, and every complete run publishes
`(Error (+ 9223372036854775807 1) IntegerOverflow)`; PeTTa's run yields `9223372036854775808`. -/
theorem overflow_every_run (minimal : Minimal.Services) (policy : Policy) :
    TypedRegion [] "+" [num 9223372036854775807, num 1] ∧
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList [])
            (app "+" [num 9223372036854775807, num 1]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList [])
            (app "+" [num 9223372036854775807, num 1]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) =
          [Atom.error (app "+" [num 9223372036854775807, num 1]) (sym "IntegerOverflow")]) ∧
      Streaming.values (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "+" [num 9223372036854775807, num 1]))) =
          [num 9223372036854775808] := by
  have head := symbol_head "+" (by decide) (by decide)
  have arguments : ∀ a ∈ [num 9223372036854775807, num 1], DataAtom a := by
    intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .grounded _
  have computed : measuredOutcome (.symbol "+") [num 9223372036854775807, num 1] =
      .runtimeError "IntegerOverflow" := by
    decide
  have untyped : (Space.ofList []).atoms.filter (typeRegion (.symbol "+")) = [] := rfl
  obtain ⟨R, _, path⟩ := error_steps (policy := policy) measuredDispatch_minimal minimal raw_answers
    (atoms := []) (executable_of "+" (by decide)) head arguments computed.symm untyped
  exact ⟨by decide +kernel, ⟨⟨R, path⟩, fun emitted run => error_every_run_of raw_contract
    (executable_of "+" (by decide)) head arguments (outcome_eq computed) untyped emitted run⟩,
    by decide +kernel⟩

/-- **Non-numeric argument, on both machines**: `(+ a 4)`, with `a` undeclared, a call in HE's typed
region. On HE's table a complete run exists, and every complete run publishes `(+ a 4)`; PeTTa's run
stops at the uncaught `invalidArguments` fault, with no value. -/
theorem non_numeric_every_run (minimal : Minimal.Services) (policy : Policy) :
    TypedRegion [] "+" [sym "a", num 4] ∧
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "+" [sym "a", num 4])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "+" [sym "a", num 4])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [app "+" [sym "a", num 4]]) ∧
      stoppedAt (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "+" [sym "a", num 4]))).agenda =
          some (.invalidArguments "+") ∧
      Streaming.values (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "+" [sym "a", num 4]))) = [] := by
  have head := symbol_head "+" (by decide) (by decide)
  have arguments : ∀ a ∈ [sym "a", num 4], DataAtom a := by
    intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .symbol (by decide) (by decide)
    · exact .grounded _
  have computed : measuredOutcome (.symbol "+") [sym "a", num 4] = .incorrectArgument := rfl
  have untyped : (Space.ofList []).atoms.filter (typeRegion (.symbol "+")) = [] := rfl
  obtain ⟨R, _, path⟩ := declined_steps (policy := policy) measuredDispatch_minimal minimal raw_answers
    (atoms := []) (executable_of "+" (by decide)) head arguments computed.symm untyped
  exact ⟨by decide +kernel, ⟨⟨R, path⟩, fun emitted run => declined_every_run raw_contract
    (executable_of "+" (by decide)) head arguments (outcome_eq computed) untyped emitted run⟩,
    by decide +kernel, by decide +kernel⟩

/-- **Where the model's table and HE's part on a whole run**, the control of the table-generic
theorems. `(+ 9223372036854775807 1)` is in the class of the model's table, whose integers have no
width: a complete run of the world machine with that table exists, and every complete run publishes
`9223372036854775808`. It is not in the class of HE's table, which errs there
(`GroundedTables.verdicts_part`); with HE's table every complete run publishes the `IntegerOverflow`
error (`overflow_every_run`). -/
theorem model_overflow_every_run (minimal : Minimal.Services) (policy : Policy) :
    GroundedRuns.SettlesG modelTable [] (app "+" [num 9223372036854775807, num 1]) ∧
      ¬ GroundedRuns.SettlesG measuredTable [] (app "+" [num 9223372036854775807, num 1]) ∧
      (∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal modelTable) modelTable.dispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "+" [num 9223372036854775807,
            num 1]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal modelTable) modelTable.dispatch
          Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "+" [num 9223372036854775807,
            num 1]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [num 9223372036854775808] := by
  have settles : GroundedRuns.SettlesG modelTable [] (app "+" [num 9223372036854775807, num 1]) :=
    .grounded 9223372036854775807 1 .plus (model_answers .plus _ _) rfl
  have outside : ¬ GroundedRuns.SettlesG measuredTable [] (app "+" [num 9223372036854775807, num 1]) := by
    intro measured
    cases measured with
    | data data _ => cases data
    | constructor ordinary _ => exact ordinary.notHost (measured_executable .plus)
    | call ordinary _ _ => exact ordinary.notHost (measured_executable .plus)
    | grounded a b known table _ => exact GroundedTable.answers_not_errs table verdicts_part.2
  have program : BoundProgram ([] : List Atom) := fun row member => by cases member
  have computed : Streaming.values (Streaming.advance (translate []) 30
      (Streaming.enter { state := store [] } (app "+" [num 9223372036854775807, num 1]))) =
      [num 9223372036854775808] := by
    decide +kernel
  have finished : (Streaming.advance (translate []) 30
      (Streaming.enter { state := store [] }
        (app "+" [num 9223372036854775807, num 1]))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨⟨heAnswers, path, _⟩, _⟩ := answer_bags_every_run_G minimal policy program settles
  obtain ⟨N, every⟩ := every_complete_run_G minimal raw_answers raw_contract policy program settles
  refine ⟨settles, outside, ⟨heAnswers, path⟩, fun emitted run => ?_⟩
  have bag := every (max N 30) (le_max_left _ _) emitted run
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) (max N 30) (le_max_right _ _),
    computed] at bag
  exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp bag.symm)

/-! ### The typed region: where the model's untyped grounded calls are HE's -/

/-- A data test on atoms, computed. -/
def dataTest : Atom → Bool
  | .symbol name => name != "Empty" && name != "Error"
  | .grounded _ => true
  | _ => false

theorem data_of_test {a : Atom} (test : dataTest a = true) : DataAtom a := by
  cases a with
  | symbol name =>
      simp only [dataTest, Bool.and_eq_true, bne_iff_ne, ne_eq] at test
      exact .symbol test.1 test.2
  | grounded value => exact .grounded value
  | var _ => cases test
  | expression _ => cases test

theorem all_data {args : List Atom} (test : args.all dataTest = true) : ∀ a ∈ args, DataAtom a :=
  fun a member => data_of_test (List.all_eq_true.mp test a member)

/-- HE's table declines a call: its verdict publishes the call. -/
theorem measured_declines {op : String} {args : List Atom} (member : op ∈ measuredNames)
    (computed : measuredOutcome (.symbol op) args = .incorrectArgument) :
    VerdictPublishes measuredTable op args [.expression (.symbol op :: args)] :=
  .declines ⟨executable_of op member, fun outcome => by
    change outcome = measuredOutcome _ _ ↔ _
    rw [computed]⟩

/-- HE's table answers a Boolean: its verdict publishes it. -/
theorem measured_bool {op : String} {args : List Atom} {value : Bool} (member : op ∈ measuredNames)
    (computed : measuredOutcome (.symbol op) args = .ok [(.grounded (.bool value), Bindings.empty)]) :
    VerdictPublishes measuredTable op args [.grounded (.bool value)] :=
  .answers (.grounded _) (fun same => by cases same) ⟨executable_of op member, fun outcome => by
    change outcome = measuredOutcome _ _ ↔ _
    rw [computed]⟩

/-- `(: c Color)`. -/
def colorRows : List Atom := [.expression [.symbol ":", .symbol "c", .symbol "Color"]]

/-- `(: n Number)`. -/
def numberRows : List Atom := [.expression [.symbol ":", .symbol "n", .symbol "Number"]]

/-- `True`, HE's Boolean. -/
abbrev boolTrue : Atom := .grounded (.bool true)

/-- **Outside the typed region the model's answer is not HE's.** Eight calls, each outside
`TypedRegion`, each with the model's every-run answer on HE's table (a complete run exists, and every
complete run publishes the list) and, in this docstring, HE's measured answer (hyperon-experimental
0.2.10 with three later fixes, one call per file):

* with `(: c Color)`, `(+ c 4)`: the model `(+ c 4)`; HE `(Error (+ c 4) (BadArgType 1 Number Color))`;
* `(+ 1 True)`: the model `(+ 1 True)`; HE `(Error (+ 1 True) (BadArgType 2 Number Bool))`;
* `(+ 1)`: the model `(+ 1)`; HE `(Error (+ 1) IncorrectNumberOfArguments)`;
* `(== 5 True)`: the model `False`; HE `(Error (== 5 True) (BadArgType 2 Number Bool))`;
* with `(: c Color)`, `(== c 5)`: the model `False`; HE `(Error (== c 5) (BadArgType 2 Color Number))`;
* `(< 1 True)`: the model `(< 1 True)`; HE `(Error (< 1 True) (BadArgType 2 Number Bool))`;
* `(and True 5)`: the model `(and True 5)`; HE `(Error (and True 5) (BadArgType 2 Bool Number))`;
* `(not 5)`: the model `(not 5)`; HE `(Error (not 5) (BadArgType 1 Bool Number))`.

The model reads no type here (`machine_reads_no_argument_types`); HE types the call first. -/
theorem outside_region (minimal : Minimal.Services) (policy : Policy) :
    (¬ TypedRegion colorRows "+" [sym "c", num 4] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy colorRows "+" [sym "c", num 4]
        [app "+" [sym "c", num 4]]) ∧
    (¬ TypedRegion [] "+" [num 1, boolTrue] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "+" [num 1, boolTrue]
        [app "+" [num 1, boolTrue]]) ∧
    (¬ TypedRegion [] "+" [num 1] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "+" [num 1] [app "+" [num 1]]) ∧
    (¬ TypedRegion [] "==" [num 5, boolTrue] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "==" [num 5, boolTrue]
        [.grounded (.bool false)]) ∧
    (¬ TypedRegion colorRows "==" [sym "c", num 5] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy colorRows "==" [sym "c", num 5]
        [.grounded (.bool false)]) ∧
    (¬ TypedRegion [] "<" [num 1, boolTrue] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "<" [num 1, boolTrue]
        [app "<" [num 1, boolTrue]]) ∧
    (¬ TypedRegion [] "and" [boolTrue, num 5] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "and" [boolTrue, num 5]
        [app "and" [boolTrue, num 5]]) ∧
    (¬ TypedRegion [] "not" [num 5] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "not" [num 5]
        [app "not" [num 5]]) := by
  have colorUntyped : ∀ op : String, op ∈ ["+", "=="] →
      (Space.ofList colorRows).atoms.filter (typeRegion (.symbol op)) = [] := by
    intro op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  refine ⟨⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩,
    ⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩,
    ⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩⟩
  · exact verdict_runs (measured_declines (by decide) rfl) minimal raw_answers raw_contract policy
      (symbol_head "+" (by decide) (by decide)) (all_data rfl) (colorUntyped "+" (by simp))
  · exact verdict_runs (measured_declines (by decide) rfl) minimal raw_answers raw_contract policy
      (symbol_head "+" (by decide) (by decide)) (all_data rfl) rfl
  · exact verdict_runs (measured_declines (by decide) rfl) minimal raw_answers raw_contract policy
      (symbol_head "+" (by decide) (by decide)) (all_data rfl) rfl
  · exact verdict_runs (measured_bool (by decide) (by decide)) minimal raw_answers raw_contract
      policy (symbol_head "==" (by decide) (by decide)) (all_data rfl) rfl
  · exact verdict_runs (measured_bool (by decide) (by decide)) minimal raw_answers raw_contract
      policy (symbol_head "==" (by decide) (by decide)) (all_data rfl) (colorUntyped "==" (by simp))
  · exact verdict_runs (measured_declines (by decide) rfl) minimal raw_answers raw_contract policy
      (symbol_head "<" (by decide) (by decide)) (all_data rfl) rfl
  · exact verdict_runs (measured_declines (by decide) rfl) minimal raw_answers raw_contract policy
      (symbol_head "and" (by decide) (by decide)) (all_data rfl) rfl
  · exact verdict_runs (measured_declines (by decide) rfl) minimal raw_answers raw_contract policy
      (symbol_head "not" (by decide) (by decide)) (all_data rfl) rfl

/-- **Inside the typed region the model's answer is HE's, as measured.** Four calls inside
`TypedRegion`, each with the model's every-run answer on HE's table, which is HE's measured answer
(listed here; agreement inside the region is measured on these programs, not proved):

* with `(: n Number)`, `(+ n 4)`: `(+ n 4)` (HE `[(+ n 4)]`);
* `(== a 5)`, `a` undeclared: `False` (HE `[False]`);
* with `(: c Color)`, `(== c c)`: `True` (HE `[True]`);
* `(and True False)`: `False` (HE `[False]`).

`non_numeric_every_run` is a fifth: `(+ a 4)` with `a` undeclared. -/
theorem inside_region (minimal : Minimal.Services) (policy : Policy) :
    (TypedRegion numberRows "+" [sym "n", num 4] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy numberRows "+" [sym "n", num 4]
        [app "+" [sym "n", num 4]]) ∧
    (TypedRegion [] "==" [sym "a", num 5] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "==" [sym "a", num 5]
        [.grounded (.bool false)]) ∧
    (TypedRegion colorRows "==" [sym "c", sym "c"] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy colorRows "==" [sym "c", sym "c"]
        [.grounded (.bool true)]) ∧
    (TypedRegion [] "and" [boolTrue, .grounded (.bool false)] ∧
      CallPublishes minimal measuredTable Completed.rawLookup policy [] "and"
        [boolTrue, .grounded (.bool false)] [.grounded (.bool false)]) := by
  refine ⟨⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩,
    ⟨by decide +kernel, ?_⟩⟩
  · exact verdict_runs (measured_declines (by decide) rfl) minimal raw_answers raw_contract policy
      (symbol_head "+" (by decide) (by decide)) (all_data rfl) (by decide +kernel)
  · exact verdict_runs (measured_bool (by decide) (by decide)) minimal raw_answers raw_contract
      policy (symbol_head "==" (by decide) (by decide)) (all_data rfl) rfl
  · exact verdict_runs (measured_bool (by decide) (by decide)) minimal raw_answers raw_contract
      policy (symbol_head "==" (by decide) (by decide)) (all_data rfl) (by decide +kernel)
  · exact verdict_runs (measured_bool (by decide) (by decide)) minimal raw_answers raw_contract
      policy (symbol_head "and" (by decide) (by decide)) (all_data rfl) rfl

end Controls

#print axioms error_closed
#print axioms finish_error_steps
#print axioms declined_steps
#print axioms declined_source_of
#print axioms declined_every_run
#print axioms error_steps
#print axioms error_source_of
#print axioms error_every_run_of
#print axioms VerdictPublishes.unique
#print axioms verdict_runs
#print axioms verdict_every_run
#print axioms machine_reads_no_argument_types
#print axioms Controls.zero_divisor_every_run
#print axioms Controls.division_by_zero_every_run
#print axioms Controls.overflow_every_run
#print axioms Controls.non_numeric_every_run
#print axioms Controls.model_overflow_every_run
#print axioms Controls.outside_region
#print axioms Controls.inside_region

end GroundedDifferences

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
