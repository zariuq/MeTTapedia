import Mettapedia.Languages.MeTTa.ContextualTransform.HEStatefulContexts

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
    obtain ⟨rfl, rfl⟩ := (delivery_exact (Entry.atom_demand _ _ _)).mp evaluated
    exact remaining
  · intro remaining
    exact ⟨before, _, .delivered (Entry.atom_demand _ _ _), remaining⟩

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

theorem unchanged_atom_argument (environment : WorldEnvironment Context World) (label : Context)
    (world : World) (live : List Atom) (scope : List String) (policy : Policy)
    (value : Entry.Value) :
    ArgumentsRel environment label world live scope [(value, Atom.atomType)] Frame.empty
      [(Entry.Value.argumentPacket [value], Frame.empty)] world (policy := policy) := by
  apply atom_argument_exact.mpr
  simp only [Frame.read_empty]
  apply OrderedStateFlatMapRel.singleton
  have continued : ResumeArgument environment label live scope policy value [] (value, Frame.empty) world
      ([(Entry.Value.argumentPacket [], Frame.empty)].map (argumentPrepend value)) world :=
    .continuing (unchanged_error_is_not_argument_stop value Frame.empty) .nil
  simpa only [List.map_cons, List.map_nil, argumentPrepend_packet] using continued

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
