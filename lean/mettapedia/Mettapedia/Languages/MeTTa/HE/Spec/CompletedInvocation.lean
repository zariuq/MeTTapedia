import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-! # Invocation inversion at the completed HE boundary -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeOccurrencesRel)
open Mettapedia.Machines.OrderedProtocol.Completion (SuccessPriorityRel)

/-- Complete a fixed invocation selection, retaining the invocation and
publication witnesses and the exact order of the results. -/
inductive InvocationResultRel (space : Space) (dispatch : GroundedDispatch)
    (lookup : CastLookup) (live : List Atom) (scope : List String) (source expected : Atom)
    (activation : Frame) (operator : Entry.Value) (arguments : List Entry.Value) (policy : Policy) :
    InvocationSelection → List Result → Prop where
  | selected {signature frames raw selected} :
      InvocationsRel space dispatch lookup live scope expected signature operator arguments frames raw
        (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (readResult policy)) selected →
      InvocationResultRel space dispatch lookup live scope source expected activation operator arguments
        policy (.selected signature frames) (selected.map (publishResult policy source))
  | fallback {errors rows raw selected} :
      TupleRel space dispatch lookup (expected :: live) scope (operator :: arguments)
        activation rows (policy := policy) →
      CallsRel space dispatch lookup live scope expected rows raw (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        ((raw ++ diagnosticResults errors activation).map (readResult policy)) selected →
      InvocationResultRel space dispatch lookup live scope source expected activation operator arguments
        policy (.exhausted errors true) (selected.map (publishResult policy source))
  | failed {errors selected} :
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        ((diagnosticResults errors activation).map (readResult policy)) selected →
      InvocationResultRel space dispatch lookup live scope source expected activation operator arguments
        policy (.exhausted errors false) (selected.map (publishResult policy source))

private theorem expression_head_args {value operator other : Entry.Value}
    {arguments otherArguments : List Entry.Value} {ready otherReady : Entry.Status}
    (shape : value = .expression ready (operator :: arguments))
    (otherShape : value = .expression otherReady (other :: otherArguments)) :
    operator = other ∧ arguments = otherArguments :=
  List.cons.inj (Entry.Value.expression.inj (shape.symm.trans otherShape)).2

/-- An interpreted expression with a head outside the direct tuple route
has precisely an invocation selection and its corresponding completion. -/
theorem AtomRel.iff_invocation
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup} {live : List Atom}
    {scope : List String} {value operator : Entry.Value} {expected : Atom} {activation : Frame}
    {results : List Result} {policy : Policy} {ready : Entry.Status} {arguments : List Entry.Value}
    (entry : Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .interpret)
    (shape : activation.read policy value = .expression ready (operator :: arguments))
    (noTuple : ¬ TypeOccurrencesRel (space.atoms : Multiset Atom) operator.erase {Atom.undefinedType}) :
    AtomRel space dispatch lookup live scope value expected activation results (policy := policy) ↔
      ∃ selection, InvocationSelectionRel space lookup policy live scope
        (activation.read policy value).erase operator.erase expected activation selection ∧
      InvocationResultRel space dispatch lookup live scope (activation.read policy value).erase
        expected activation operator arguments policy selection results := by
  constructor
  · intro derived
    cases derived with
    | delivered entered => cases Entry.functional entered entry
    | cast entered => cases Entry.functional entered entry
    | tuple _ shaped occurs _ _ _ =>
        obtain ⟨rfl, _⟩ := expression_head_args shape shaped
        exact (noTuple occurs).elim
    | function _ shaped chosen invoked priority =>
        obtain ⟨rfl, rfl⟩ := expression_head_args shape shaped
        exact ⟨_, chosen, .selected invoked priority⟩
    | fallback _ shaped chosen tuple calls priority =>
        obtain ⟨rfl, rfl⟩ := expression_head_args shape shaped
        exact ⟨_, chosen, .fallback tuple calls priority⟩
    | selectionFailed _ shaped chosen priority =>
        obtain ⟨rfl, rfl⟩ := expression_head_args shape shaped
        exact ⟨_, chosen, .failed priority⟩
  · rintro ⟨selection, chosen, result⟩
    cases result with
    | selected invoked priority => exact .function entry shape chosen invoked priority
    | fallback tuple calls priority => exact .fallback entry shape chosen tuple calls priority
    | failed priority => exact .selectionFailed entry shape chosen priority

/-- A single applicable frame runs the function and then its calls. -/
theorem InvocationsRel.singleton_iff
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup} {live : List Atom}
    {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value} {activation : Frame}
    {results : List Result} {policy : Policy} :
    InvocationsRel space dispatch lookup live scope expected signature operator arguments
        [activation] results (policy := policy) ↔
      ∃ interpreted,
        FunctionRel space dispatch lookup (invocationReturnType signature :: live) scope expected
            signature operator arguments activation interpreted (policy := policy) ∧
        CallsRel space dispatch lookup live scope (invocationReturnType signature)
          interpreted results (policy := policy) := by
  constructor
  · intro completed
    cases completed with
    | cons function calls rest =>
        cases rest
        exact ⟨_, function, by simpa only [List.append_nil] using calls⟩
  · rintro ⟨interpreted, function, calls⟩
    simpa only [List.append_nil] using InvocationsRel.cons function calls .nil

/-- With one continuing head, each result is assembled from the exact
ordered argument packet produced in its reached frame. -/
theorem FunctionBranchesRel.singleton_continuing_iff
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup} {live : List Atom}
    {scope : List String} {requests : List ArgumentRequest} {head : Result}
    {results : List Result} {policy : Policy} (active : ¬ IsEmptyOrErrorRel head.1.erase) :
    FunctionBranchesRel space dispatch lookup live scope requests [head] results
        (policy := policy) ↔
      ∃ packets,
        ArgumentsRel space dispatch lookup (head.1.erase :: live) scope requests head.2 packets
            (policy := policy) ∧
        results = packets.map (functionAssemble head.1) := by
  constructor
  · intro branches
    cases branches with
    | stopped stop _ => exact (active stop).elim
    | continuing _ arguments rest =>
        cases rest
        exact ⟨_, arguments, List.append_nil _⟩
  · rintro ⟨packets, arguments, rfl⟩
    simpa only [List.append_nil] using FunctionBranchesRel.continuing active arguments .nil

/-- Read one continuing result and retain the order of its completed suffix. -/
theorem ArgumentBranchesRel.singleton_continuing_iff
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup} {live : List Atom}
    {scope : List String} {original : Entry.Value} {requests : List ArgumentRequest}
    {head : Result} {results : List Result} {policy : Policy}
    (active : ¬ ArgumentStopped original head) :
    ArgumentBranchesRel space dispatch lookup live scope original requests [head] results
        (policy := policy) ↔
      ∃ packets,
        ArgumentsRel space dispatch lookup (head.1.erase :: live) scope requests head.2 packets
            (policy := policy) ∧
        results = packets.map (argumentPrepend head.1) := by
  constructor
  · intro branches
    cases branches with
    | stopped stop _ => exact (active stop).elim
    | continuing _ arguments rest =>
        cases rest
        exact ⟨_, arguments, List.append_nil _⟩
  · rintro ⟨packets, arguments, rfl⟩
    simpa only [List.append_nil] using ArgumentBranchesRel.continuing active arguments .nil

theorem ArgumentBranchesRel.continuing_singleton
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup} {live : List Atom}
    {scope : List String} {original : Entry.Value} {requests : List ArgumentRequest}
    {head : Result} {results : List Result} {policy : Policy}
    (branches : ArgumentBranchesRel space dispatch lookup live scope original requests [head] results
      (policy := policy))
    (active : ¬ ArgumentStopped original head) :
    ∃ packets,
      ArgumentsRel space dispatch lookup (head.1.erase :: live) scope requests head.2 packets
          (policy := policy) ∧
      results = packets.map (argumentPrepend head.1) :=
  (singleton_continuing_iff active).mp branches

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
