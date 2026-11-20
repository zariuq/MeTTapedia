import Mettapedia.Languages.MeTTa.ContextualTransform.HEStatefulContexts
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance

/-!
# Stateful HE argument contexts through the shared ordered traversal

These are the independent completed source judgments, not the separate finite
typed-application helper. Arguments evaluate under their declared demands and
resume each result with its own frame at the reached world. Changed errors stop
that branch; an unchanged error value is still an argument. Later alternative
occurrences remain governed by the ordered source traversal.

The correspondence preserves and reflects completed derivations. It neither
assumes completion of a producer nor supplies streaming-prefix completeness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEArgumentContexts

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Completed.Stateful
open Mettapedia.Machines.OrderedProtocol.Completion

variable {Context World : Type}

/-- One source result either stops this argument branch or evaluates its
remaining arguments from the current world and its own binding frame. -/
inductive ResumeArgument (environment : WorldEnvironment Context World) (label : Context)
    (live : List Atom) (scope : List String) (policy : Policy)
    (original : Entry.Value) (requests : List ArgumentRequest) :
    Result → World → List Result → World → Prop where
  | stopped {row world} : ArgumentStopped original row →
      ResumeArgument environment label live scope policy original requests row world [row] world
  | continuing {row before after children} : ¬ArgumentStopped original row →
      ArgumentsRel environment label before (row.1.erase :: live) scope requests row.2 children after
        (policy := policy) →
      ResumeArgument environment label live scope policy original requests row before
        (children.map (argumentPrepend row.1)) after

theorem branches_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {original : Entry.Value} {requests : List ArgumentRequest}
    {rows results : List Result} {before after : World} :
    ArgumentBranchesRel environment label before live scope original requests rows results after (policy := policy) ↔
      OrderedStateFlatMapRel (ResumeArgument environment label live scope policy original requests)
        rows before results after := by
  constructor
  · intro derived
    induction rows generalizing before results with
    | nil => cases derived; exact .nil _
    | cons row rows ih =>
        cases derived with
        | stopped stop rest => exact .cons (.stopped stop) (ih rest)
        | continuing allowed tail rest => exact .cons (.continuing allowed tail) (ih rest)
  · intro walked
    induction walked with
    | nil => exact .nil
    | cons first _ ih =>
        cases first with
        | stopped stop => exact .stopped stop ih
        | continuing allowed tail => exact .continuing allowed tail ih

theorem branches_append_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {original : Entry.Value} {requests : List ArgumentRequest}
    (left right : List Result) {results : List Result} {before after : World} :
    ArgumentBranchesRel environment label before live scope original requests (left ++ right) results after
        (policy := policy) ↔
      ∃ middle earlier later, results = earlier ++ later ∧
        ArgumentBranchesRel environment label before live scope original requests left earlier middle
          (policy := policy) ∧
        ArgumentBranchesRel environment label middle live scope original requests right later after
          (policy := policy) := by
  constructor
  · intro derived
    obtain ⟨middle, earlier, later, combined, first, rest⟩ :=
      OrderedStateFlatMapRel.split left right (branches_exact.mp derived)
    exact ⟨middle, earlier, later, combined, branches_exact.mpr first, branches_exact.mpr rest⟩
  · rintro ⟨middle, earlier, later, rfl, first, rest⟩
    exact branches_exact.mpr ((branches_exact.mp first).append (branches_exact.mp rest))

theorem arguments_cons_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {request : ArgumentRequest} {requests : List ArgumentRequest}
    {results : List Result} {before after : World} :
    ArgumentsRel environment label before live scope (request :: requests) frame results after (policy := policy) ↔
      ∃ middle heads,
        AtomRel environment label before (argumentScope requests ++ live) scope request.1 request.2 frame heads middle
          (policy := policy) ∧
        OrderedStateFlatMapRel (ResumeArgument environment label live scope policy request.1 requests)
          heads middle results after := by
  constructor
  · intro derived
    cases derived with
    | cons first branches => exact ⟨_, _, first, branches_exact.mp branches⟩
  · rintro ⟨middle, heads, first, branches⟩
    exact .cons first (branches_exact.mpr branches)

theorem delivery_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {value : Entry.Value} {expected : Atom} {results : List Result} {before after : World}
    (entry : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase expected .deliver) :
    AtomRel environment label before live scope value expected frame results after (policy := policy) ↔
      results = [(frame.read policy value, frame)] ∧ after = before := by
  constructor
  · intro derived
    cases derived with
    | delivered => exact ⟨rfl, rfl⟩
    | cast entered _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
    | tuple entered _ _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
    | function entered _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
    | fallback entered _ _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
    | selectionFailed entered _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
  · rintro ⟨rfl, rfl⟩
    exact .delivered entry

/-- Atom demand delivers even callable-looking syntax without a child
computation. Remaining arguments still execute under their own source policy. -/
theorem atom_demand_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {value : Entry.Value} {frame : Frame} {before after : World} {results : List Result} :
    AtomRel environment label before live scope value Atom.atomType frame results after
        (policy := policy) ↔
      results = [(frame.read policy value, frame)] ∧ after = before :=
  delivery_exact (Entry.atom_demand _ _ _)

/-- An expression metatype demand delivers the expression itself, even
when its head would run under an evaluation demand. The shape is checked
after reading the actual caller's bindings. -/
theorem expression_demand_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {value : Entry.Value} {frame : Frame} {before after : World} {results : List Result}
    {items : List Atom} (shape : (frame.read policy value).erase = .expression items) :
    AtomRel environment label before live scope value Atom.expressionType frame results after
        (policy := policy) ↔
      results = [(frame.read policy value, frame)] ∧ after = before := by
  apply delivery_exact
  rw [shape]
  by_cases stopped : IsEmptyOrErrorRel (.expression items)
  · exact .stopped stopped
  · exact .pass stopped (.expression items) (Or.inr (Or.inl rfl))

/-- Raw delivery is one operand phase; the remaining arguments still use their own demands. -/
theorem atom_argument_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {value : Entry.Value} {requests : List ArgumentRequest}
    {results : List Result} {before after : World} :
    ArgumentsRel environment label before live scope ((value, Atom.atomType) :: requests)
        frame results after (policy := policy) ↔
      OrderedStateFlatMapRel (ResumeArgument environment label live scope policy value requests)
        [(frame.read policy value, frame)] before results after := by
  rw [arguments_cons_exact]
  constructor
  · rintro ⟨middle, heads, evaluated, remaining⟩
    obtain ⟨rfl, rfl⟩ := atom_demand_exact.mp evaluated
    exact remaining
  · intro remaining
    exact ⟨before, _, atom_demand_exact.mpr ⟨rfl, rfl⟩, remaining⟩

/-- A last operand result is either a stopped result or one packet in
its own returned frame. This operation does not interpret the value. -/
def finishLastArgument (source : Entry.Value) (row : Result) : Result :=
  if isEmptyOrError row.1.erase && decide (row.1.erase ≠ source.erase) then row
  else (Entry.Value.argumentPacket [row.1], row.2)

theorem lastArgument_stops_iff (source : Entry.Value) (row : Result) :
    (isEmptyOrError row.1.erase && decide (row.1.erase ≠ source.erase)) = true ↔ ArgumentStopped source row := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, ArgumentStopped,
    ← Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]

theorem finishLastArgument_of_stopped {source : Entry.Value} {row : Result}
    (stopped : ArgumentStopped source row) : finishLastArgument source row = row :=
  if_pos ((lastArgument_stops_iff source row).mpr stopped)

theorem finishLastArgument_of_ordinary {source : Entry.Value} {row : Result}
    (ordinary : ¬ArgumentStopped source row) :
    finishLastArgument source row = (Entry.Value.argumentPacket [row.1], row.2) :=
  if_neg (fun stopped => ordinary ((lastArgument_stops_iff source row).mp stopped))

private theorem last_arguments_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {source : Entry.Value}
    {heads results : List Result} {before after : World} :
    ArgumentBranchesRel environment label before live scope source [] heads results after (policy := policy) ↔
      results = heads.map (finishLastArgument source) ∧ after = before := by
  induction heads generalizing before results with
  | nil =>
      constructor
      · intro run
        cases run
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact .nil
  | cons head rest ih =>
      constructor
      · intro run
        cases run with
        | stopped stopped tail =>
            obtain ⟨rfl, rfl⟩ := ih.mp tail
            simp [finishLastArgument_of_stopped stopped]
        | continuing allowed empty tail =>
            cases empty
            obtain ⟨rfl, rfl⟩ := ih.mp tail
            simp [finishLastArgument_of_ordinary allowed]
      · rintro ⟨rfl, rfl⟩
        by_cases stopped : ArgumentStopped source head
        · simpa [finishLastArgument_of_stopped stopped] using
            (Stateful.ArgumentBranchesRel.stopped stopped (ih.mpr ⟨rfl, rfl⟩))
        · simpa [finishLastArgument_of_ordinary stopped] using
            (Stateful.ArgumentBranchesRel.continuing stopped Stateful.ArgumentsRel.nil
              (ih.mpr ⟨rfl, rfl⟩))

/-- Evaluation precedes the last argument delivery. Packet formation
preserves every branch and its frame; it performs no second evaluation
or change to the world reached by that operand. -/
theorem singleton_arguments_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {source : Entry.Value} {demand : Atom} {results : List Result} {before after : World} :
    ArgumentsRel environment label before live scope [(source, demand)] frame results after (policy := policy) ↔
      ∃ heads, AtomRel environment label before live scope source demand frame heads after (policy := policy) ∧
        results = heads.map (finishLastArgument source) := by
  constructor
  · intro run
    cases run with
    | cons operand branches =>
      obtain ⟨rfl, rfl⟩ := last_arguments_exact.mp branches
      exact ⟨_, operand, rfl⟩
  · rintro ⟨heads, evaluated, rfl⟩
    exact .cons evaluated (last_arguments_exact.mpr ⟨rfl, rfl⟩)

/-- The last expression-demand operand is packed from its read syntax.
The ordinary argument stop rule still applies; no world effect can be
attributed to evaluating that operand. -/
theorem singleton_expression_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {value : Entry.Value} {results : List Result} {before after : World}
    {items : List Atom} (shape : (frame.read policy value).erase = .expression items) :
    ArgumentsRel environment label before live scope [(value, Atom.expressionType)]
        frame results after (policy := policy) ↔
      after = before ∧ results = [finishLastArgument value (frame.read policy value, frame)] := by
  rw [singleton_arguments_exact]
  constructor
  · rintro ⟨heads, ran, rfl⟩
    obtain ⟨rfl, rfl⟩ := (expression_demand_exact shape).mp ran
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, (expression_demand_exact shape).mpr ⟨rfl, rfl⟩, rfl⟩

/-- Compose one selected typed invocation from argument preparation through
its actual call and publication. Expected return demand and the original
diagnostic syntax are not taken from the prepared call. -/
theorem completed_typed_one
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {before middle final : World} {caller reached : Frame}
    {original operator prepared : Entry.Value} {operands : List Entry.Value} {expected : Atom}
    {signature : SelectedTypePolicy} {readiness : Entry.Status} {answer : Result}
    (entry : Entry.Rel policy.reentry (caller.read policy original).status
      (caller.read policy original).erase expected .interpret)
    (shape : caller.read policy original = .expression readiness (operator :: operands))
    (selected : environment.arguments.selection (environment.view before label) environment.lookup
      policy live scope (caller.read policy original).erase operator.erase expected caller
      (.selected signature [caller]))
    (arguments : FunctionRel environment label before (invocationReturnType signature :: live) scope
      expected signature operator operands caller [(prepared, reached)] middle (policy := policy))
    (call : CallRel environment label middle live scope prepared (invocationReturnType signature)
      reached [answer] final (policy := policy)) :
    AtomRel environment label before live scope original expected caller
      [publishResult policy (caller.read policy original).erase (readResult policy answer)] final
      (policy := policy) := by
  have calls : CallsRel environment label middle live scope (invocationReturnType signature)
      [(prepared, reached)] [answer] final (policy := policy) := by
    simpa only [List.append_nil] using Stateful.CallsRel.cons call Stateful.CallsRel.nil
  have invoked : InvocationsRel environment label before live scope expected signature operator operands
      [caller] [answer] final (policy := policy) := by
    simpa only [List.append_nil] using Stateful.InvocationsRel.cons arguments calls Stateful.InvocationsRel.nil
  have priority : SuccessPriorityRel (fun r : Result => isErrorAtom r.1.erase)
      ([answer].map (readResult policy)) [readResult policy answer] := by
    rw [List.map_singleton]
    cases error : isErrorAtom (readResult policy answer).1.erase
    · simpa [error] using
        (SuccessPriorityRel.successes
          (isError := fun r : Result => isErrorAtom r.1.erase) (raw := [readResult policy answer])
          ⟨_, List.mem_singleton_self _, error⟩)
    · exact .allErrors (by simpa using error)
  exact Stateful.AtomRel.function entry shape selected invoked priority

/-- The unary Atom argument either returns its changed stop value or packages its
materialized syntax. Neither case runs the operand or changes the world. -/
theorem singleton_atom_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {value : Entry.Value} {results : List Result} {before after : World} :
    let read := frame.read policy value
    ArgumentsRel environment label before live scope [(value, Atom.atomType)] frame results after
        (policy := policy) ↔
      after = before ∧
        ((ArgumentStopped value (read, frame) ∧ results = [(read, frame)]) ∨
          (¬ArgumentStopped value (read, frame) ∧
            results = [(Entry.Value.argumentPacket [read], frame)])) := by
  dsimp only
  rw [singleton_arguments_exact]
  constructor
  · rintro ⟨heads, ran, rfl⟩
    obtain ⟨rfl, rfl⟩ := atom_demand_exact.mp ran
    by_cases stopped : ArgumentStopped value (frame.read policy value, frame)
    · refine ⟨rfl, Or.inl ⟨stopped, ?_⟩⟩
      simp [finishLastArgument_of_stopped stopped]
    · refine ⟨rfl, Or.inr ⟨stopped, ?_⟩⟩
      simp [finishLastArgument_of_ordinary stopped]
  · rintro ⟨rfl, ⟨stops, rfl⟩ | ⟨continues, rfl⟩⟩
    · exact ⟨_, atom_demand_exact.mpr ⟨rfl, rfl⟩,
        by simp [finishLastArgument_of_stopped stops]⟩
    · exact ⟨_, atom_demand_exact.mpr ⟨rfl, rfl⟩,
        by simp [finishLastArgument_of_ordinary continues]⟩

/-- An ordinary held prefix does not run a child. It prepends the
value read at entry, even if later arguments change the world or frame. -/
theorem ordinary_atom_prefix_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {value : Entry.Value} {requests : List ArgumentRequest}
    {results : List Result} {before after : World}
    (ordinary : ¬ArgumentStopped value (frame.read policy value, frame)) :
    ArgumentsRel environment label before live scope ((value, Atom.atomType) :: requests)
        frame results after (policy := policy) ↔
      ∃ rest, ArgumentsRel environment label before ((frame.read policy value).erase :: live) scope
        requests frame rest after (policy := policy) ∧
        results = rest.map (argumentPrepend (frame.read policy value)) := by
  rw [atom_argument_exact]
  constructor
  · intro run
    cases run with
    | cons first rest =>
      cases rest
      cases first with
      | stopped stop => exact (ordinary stop).elim
      | continuing _ later => exact ⟨_, later, List.append_nil _⟩
  · rintro ⟨rest, later, rfl⟩
    simpa only [List.append_nil] using
      (OrderedStateFlatMapRel.cons (.continuing ordinary later) (.nil _))

/-- The last held slot of a mixed-demand call is read in the frame
owned by that operand result; this retains changed error packets. -/
def finishForcedThenHeld (policy : Policy) (operand template : Entry.Value) (row : Result) : Result :=
  if isEmptyOrError row.1.erase && decide (row.1.erase ≠ operand.erase) then row
  else argumentPrepend row.1 (finishLastArgument template (row.2.read policy template, row.2))

theorem finishForcedThenHeld_of_ordinary (policy : Policy) (template : Entry.Value)
    {operand : Entry.Value} {row : Result} (ordinary : ¬ArgumentStopped operand row) :
    finishForcedThenHeld policy operand template row =
      argumentPrepend row.1 (finishLastArgument template (row.2.read policy template, row.2)) :=
  if_neg (fun stop => ordinary ((lastArgument_stops_iff operand row).mp stop))

private theorem singleton_atom_finishes
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {template : Entry.Value} {results : List Result} {before after : World} :
    ArgumentsRel environment label before live scope [(template, Atom.atomType)] frame results after
        (policy := policy) ↔
      results = [finishLastArgument template (frame.read policy template, frame)] ∧ after = before := by
  rw [singleton_arguments_exact]
  constructor
  · rintro ⟨heads, evaluated, rfl⟩
    obtain ⟨rfl, rfl⟩ := atom_demand_exact.mp evaluated
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, atom_demand_exact.mpr ⟨rfl, rfl⟩, rfl⟩

private theorem forced_then_held_branches
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {operand template : Entry.Value} {rows results : List Result} {before after : World} :
    ArgumentBranchesRel environment label before live scope operand [(template, Atom.atomType)] rows
        results after (policy := policy) ↔
      results = rows.map (finishForcedThenHeld policy operand template) ∧ after = before := by
  induction rows generalizing before after results with
  | nil =>
    constructor
    · intro run
      cases run
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact .nil
  | cons row rows ih =>
    constructor
    · intro run
      cases run with
      | stopped stop rest =>
        obtain ⟨rfl, rfl⟩ := ih.mp rest
        have holds := (lastArgument_stops_iff operand row).mpr stop
        exact ⟨by rw [List.map_cons, finishForcedThenHeld, if_pos holds], rfl⟩
      | continuing ordinary last rest =>
        obtain ⟨rfl, rfl⟩ := singleton_atom_finishes.mp last
        obtain ⟨rfl, rfl⟩ := ih.mp rest
        exact ⟨congrArg (fun head => head :: rows.map (finishForcedThenHeld policy operand template))
          (finishForcedThenHeld_of_ordinary policy template ordinary).symm, rfl⟩
    · rintro ⟨rfl, rfl⟩
      by_cases stop : ArgumentStopped operand row
      · rw [List.map_cons, finishForcedThenHeld, if_pos ((lastArgument_stops_iff operand row).mpr stop)]
        exact .stopped stop (ih.mpr ⟨rfl, rfl⟩)
      · rw [List.map_cons, finishForcedThenHeld_of_ordinary policy template stop]
        exact .continuing stop (singleton_atom_finishes.mpr ⟨rfl, rfl⟩) (ih.mpr ⟨rfl, rfl⟩)

/-- The authored let signature has one forcing slot. Its other slots
retain their read syntax, and each surviving operand result supplies
its own caller frame to the held template. -/
theorem let_arguments_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {pattern operand template : Entry.Value} {results : List Result} {before after : World}
    (ordinary : ¬ArgumentStopped pattern (frame.read policy pattern, frame)) :
    ArgumentsRel environment label before live scope
        [(pattern, Atom.atomType), (operand, Atom.undefinedType), (template, Atom.atomType)] frame
        results after (policy := policy) ↔
      ∃ rows, AtomRel environment label before
          (argumentScope [(template, Atom.atomType)] ++ (frame.read policy pattern).erase :: live)
          scope operand Atom.undefinedType frame rows after (policy := policy) ∧
        results = (rows.map (finishForcedThenHeld policy operand template)).map
          (argumentPrepend (frame.read policy pattern)) := by
  rw [ordinary_atom_prefix_exact ordinary]
  constructor
  · rintro ⟨rest, run, rfl⟩
    cases run with
    | cons forced continued =>
      obtain ⟨rfl, rfl⟩ := forced_then_held_branches.mp continued
      exact ⟨_, forced, rfl⟩
  · rintro ⟨rows, forced, rfl⟩
    exact ⟨_, .cons forced (forced_then_held_branches.mpr ⟨rfl, rfl⟩), rfl⟩

theorem unchanged_error_is_not_argument_stop (original : Entry.Value) (frame : Frame) :
    ¬ArgumentStopped original (original, frame) := by
  simp [ArgumentStopped]

theorem stopped_argument_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {original : Entry.Value} {requests : List ArgumentRequest} {row : Result}
    {results : List Result} {before after : World} (stopped : ArgumentStopped original row) :
    ArgumentBranchesRel environment label before live scope original requests [row] results after (policy := policy) ↔
      results = [row] ∧ after = before := by
  constructor
  · intro derived
    cases derived with
    | stopped _ rest => cases rest; exact ⟨rfl, rfl⟩
    | continuing continues _ _ => exact False.elim (continues stopped)
  · rintro ⟨rfl, rfl⟩
    exact .stopped stopped .nil

/-- No answer from the evaluated operand means no later argument work, while
the world reached by that operand is retained. -/
theorem answerless_operand (environment : WorldEnvironment Context World) (label : Context)
    (live : List Atom) (scope : List String) (policy : Policy) (frame : Frame)
    (request : ArgumentRequest) (requests : List ArgumentRequest) (before reached : World)
    (evaluated : AtomRel environment label before (argumentScope requests ++ live) scope request.1 request.2
      frame [] reached (policy := policy)) :
    ArgumentsRel environment label before live scope (request :: requests) frame [] reached (policy := policy) :=
  .cons evaluated .nil

inductive ResumeFunction (environment : WorldEnvironment Context World) (label : Context)
    (live : List Atom) (scope : List String) (policy : Policy) (requests : List ArgumentRequest) :
    Result → World → List Result → World → Prop where
  | stopped {row world} : IsEmptyOrErrorRel row.1.erase →
      ResumeFunction environment label live scope policy requests row world [row] world
  | continuing {row before after children} : ¬IsEmptyOrErrorRel row.1.erase →
      ArgumentsRel environment label before (row.1.erase :: live) scope requests row.2 children after
        (policy := policy) →
      ResumeFunction environment label live scope policy requests row before
        (children.map (functionAssemble row.1)) after

theorem function_branches_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {requests : List ArgumentRequest}
    {rows results : List Result} {before after : World} :
    FunctionBranchesRel environment label before live scope requests rows results after (policy := policy) ↔
      OrderedStateFlatMapRel (ResumeFunction environment label live scope policy requests)
        rows before results after := by
  constructor
  · intro derived
    induction rows generalizing before results with
    | nil => cases derived; exact .nil _
    | cons row rows ih =>
        cases derived with
        | stopped stop rest => exact .cons (.stopped stop) (ih rest)
        | continuing allowed tail rest => exact .cons (.continuing allowed tail) (ih rest)
  · intro walked
    induction walked with
    | nil => exact .nil
    | cons first _ ih =>
        cases first with
        | stopped stop => exact .stopped stop ih
        | continuing allowed tail => exact .continuing allowed tail ih

theorem function_exact {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame : Frame}
    {expected : Atom} {signature : SelectedTypePolicy} {operator : Entry.Value}
    {arguments : List Entry.Value} {results : List Result} {before after : World} :
    FunctionRel environment label before live scope expected signature operator arguments frame results after
        (policy := policy) ↔
      arguments.length = signature.argumentTypes.length ∧ ∃ middle heads,
        AtomRel environment label before (signature.functionType :: arguments.map Entry.Value.erase ++ live)
          (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
          operator signature.functionType frame heads middle (policy := policy) ∧
        OrderedStateFlatMapRel
          (ResumeFunction environment label live scope policy (arguments.zip signature.argumentTypes))
          heads middle results after := by
  constructor
  · intro derived
    cases derived with
    | evaluated arity first branches => exact ⟨arity, _, _, first, function_branches_exact.mp branches⟩
  · rintro ⟨arity, middle, heads, first, branches⟩
    exact .evaluated arity first (function_branches_exact.mpr branches)

/-- A single returning operator starts its argument traversal in the
world and frame it reached. Assembling the call then retains the world
reached by the arguments, including their silent effects. -/
theorem function_of_one_operator {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy} {frame ready : Frame}
    {expected : Atom} {signature : SelectedTypePolicy} {operator head : Entry.Value}
    {arguments : List Entry.Value} {packets : List Result} {before middle after : World}
    (arity : arguments.length = signature.argumentTypes.length)
    (evaluated : AtomRel environment label before
      (signature.functionType :: arguments.map Entry.Value.erase ++ live)
      (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
      operator signature.functionType frame [(head, ready)] middle (policy := policy))
    (ordinary : ¬IsEmptyOrErrorRel head.erase)
    (delivered : ArgumentsRel environment label middle (head.erase :: live) scope
      (arguments.zip signature.argumentTypes) ready packets after (policy := policy)) :
    FunctionRel environment label before live scope expected signature operator arguments frame
      (packets.map (functionAssemble head)) after (policy := policy) := by
  apply Stateful.FunctionRel.evaluated arity evaluated
  simpa only [List.append_nil] using
    (Stateful.FunctionBranchesRel.continuing (head := (head, ready)) ordinary delivered
      Stateful.FunctionBranchesRel.nil)

theorem unchanged_atom_argument (environment : WorldEnvironment Context World) (label : Context)
    (world : World) (live : List Atom) (scope : List String) (policy : Policy)
    (value : Entry.Value) :
    ArgumentsRel environment label world live scope [(value, Atom.atomType)] Frame.empty
      [(Entry.Value.argumentPacket [value], Frame.empty)] world (policy := policy) := by
  apply singleton_atom_exact.mpr
  rw [Frame.read_empty]
  exact ⟨rfl, Or.inr ⟨unchanged_error_is_not_argument_stop value Frame.empty, rfl⟩⟩

namespace Controls

def error : Entry.Value := .expression .active [.symbol "Error", .symbol "cause", .symbol "message"]
def original : Entry.Value := .symbol "input"

theorem changed_error_stops_but_unchanged_error_is_argument_data :
    ArgumentStopped original (error, Frame.empty) ∧
      ¬ArgumentStopped error (error, Frame.empty) := by
  refine ⟨⟨Or.inr ⟨[.symbol "cause", .symbol "message"], by simp [error, Entry.Value.erase]⟩, ?_⟩,
    unchanged_error_is_not_argument_stop error Frame.empty⟩
  intro impossible
  simp [error, original, Entry.Value.erase] at impossible

/-- The same syntactic error is delivered as an Atom argument but stops
function-head traversal. Neither case invokes an opaque leaf evaluator. -/
theorem argument_and_operator_error_policies_differ
    (environment : WorldEnvironment Context World) (label : Context) (world : World)
    (live : List Atom) (scope : List String) (policy : Policy) :
    ArgumentsRel environment label world live scope [(error, Atom.atomType)] Frame.empty
      [(Entry.Value.argumentPacket [error], Frame.empty)] world (policy := policy) ∧
    FunctionBranchesRel environment label world live scope [] [(error, Frame.empty)]
      [(error, Frame.empty)] world (policy := policy) := by
  exact ⟨unchanged_atom_argument environment label world live scope policy error,
    .stopped (Or.inr ⟨[.symbol "cause", .symbol "message"], by simp [error, Entry.Value.erase]⟩) .nil⟩

theorem held_callable_syntax_has_no_operand_effect
    (environment : WorldEnvironment Context World) (label : Context) (world : World)
    (live : List Atom) (scope : List String) (policy : Policy) (head : String) (arguments : List Entry.Value) :
    ArgumentsRel environment label world live scope
      [(.expression .active (.symbol head :: arguments), Atom.atomType)] Frame.empty
      [(Entry.Value.argumentPacket [.expression .active (.symbol head :: arguments)], Frame.empty)]
      world (policy := policy) :=
  unchanged_atom_argument environment label world live scope policy _

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.HEArgumentContexts
