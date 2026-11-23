import Mettapedia.Languages.MeTTa.HE.Spec.CompletedInvocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.TypedEveryRun

/-!
# The declared head's error path, at any arity, on every run

`DeclaredEveryRun.declared_every_run` covers one call, `(f b)` against `(-> Number Number)`. Here a
declared head of any arity: `g` has one stored type, an arrow `(-> T₁ … Tₙ R)`, and the call
`(g a₁ … aₙ)` has data arguments with one stored type each. If the demands `T₁ … T_{k-1}` accept
their arguments and `T_k` rejects `a_k`, then **every** complete run of HE publishes exactly one
answer, the error `(Error (g a₁ … aₙ) (BadArgType k T_k A_k))`.

HE's applicability check threads the frames from one argument to the next: an accepted argument keeps
its frame (renewed or not), a rejected one keeps none, and the arguments after it are checked
against no frame at all, so they add no error (`prefix_accepted`, `rejected_here`,
`no_frames_no_errors`). The scan of `g`'s one arrow ends exhausted, with that error and without
tuple fallback (`selection_exhausted`), and the failed selection publishes it (`error_source`).

A complete run exists whenever the demands before position `k` accept with the bindings unchanged
(`error_run_exists`, `error_every_run_complete`): the accepted prefix keeps the frame, the rejected
position reports the error, and the arguments after it are checked against no frame.

The PeTTa model checks no declared type and answers by the program's equations. Both PeTTa hosts
check a call's declared argument and result types and give no answer on a mismatch, so the model's
answer is the hosts' only on the program without the head's declaration
(`DeclaredHeads.headUndeclared`); the PeTTa side of the controls is stated there.

## Controls

* `Controls.arity_three` (positive): `(h 1 b 2)` against `(-> Number Number Number Number)` answers
  `(Error (h 1 b 2) (BadArgType 2 Number Bool))` on every complete HE run; without `h`'s declaration
  PeTTa answers `yes`.
* `Controls.first_mismatch_only` (the theorem's precision): `(h b b 2)` reports only position 1;
  the second ill-typed argument is checked against no frame.
* `Controls.petta_model_reads_no_declaration`: on these programs, whose declarations have no `Atom`
  parameter, the PeTTa model answers the same with and without the head's declaration, which the
  PeTTa hosts do not; this is why the hypothesis is needed. (The model reads which parameters are
  `Atom`; these programs have none.)
* `Controls.subtype_row_needed`: with `(:< Bool Number)` the model still publishes the `BadArgType`
  error on every run, where HE answers `yes`; the typed theorems are exact for HE only on programs
  without subtype rows (`TypeQueryFragment`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DeclaredErrors

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom mkError)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun DeclaredHeads DeclaredEveryRun TypedEveryRun
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- The demand `expected` accepts the type `actual` at every frame. -/
def Accepts (policy : Policy) (expected actual : Atom) : Prop :=
  ∀ frame : Frame, ∃ output, policy.matching.Rel expected actual frame.bindings output

/-- The demand `expected` rejects the type `actual` under every bindings. -/
def Rejects (policy : Policy) (expected actual : Atom) : Prop :=
  ∀ (bindings output : Bindings), ¬ policy.matching.Rel expected actual bindings output

/-! ## Argument checks -/

/-- **Argument checks against no frame add no frame and no error.** -/
theorem no_frames_no_errors {space : Space} {expression : Atom} :
    ∀ {position : Nat} {arguments types : List Atom} {frames after : List Frame}
      {errors : List Atom},
      Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression position
        arguments types frames after errors →
      frames = [] → after = [] ∧ errors = [] := by
  intro position arguments types frames after errors checked
  induction checked with
  | nil => intro noFrames; exact ⟨noFrames, rfl⟩
  | cons head _ ih =>
      intro noFrames
      subst noFrames
      cases head
      obtain ⟨rfl, rfl⟩ := ih rfl
      exact ⟨rfl, rfl⟩

/-- **An accepted prefix keeps one frame**: after the arguments whose demands accept their one type,
the checks continue from a single frame, and add no error. -/
theorem prefix_accepted {space : Space} {expression : Atom} :
    ∀ (pre preT preA : List Atom) (position : Nat) (frame : Frame) (rest restT : List Atom)
      (after : List Frame) (errors : List Atom),
      List.Forall₂ (fun a A => StorageTypesRel space a [A]) pre preA →
      List.Forall₂ (fun T A => Accepts policy T A) preT preA →
      Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression position
        (pre ++ rest) (preT ++ restT) [frame] after errors →
      ∃ frame', Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression
        (position + pre.length) rest restT [frame'] after errors
  | [], preT, preA, position, frame, rest, restT, after, errors, stored, accepts, checked => by
      cases stored
      cases accepts
      exact ⟨frame, by simpa using checked⟩
  | a :: pre, preT, preA, position, frame, rest, restT, after, errors, stored, accepts, checked => by
      obtain ⟨A, preA', storedA, stored', rfl⟩ := List.forall₂_cons_left_iff.mp stored
      obtain ⟨T, preT', acceptsA, accepts', rfl⟩ := List.forall₂_cons_right_iff.mp accepts
      simp only [List.cons_append] at checked
      cases checked with
      | cons head later =>
          cases head with
          | cons queried paired nilChecks =>
              cases nilChecks
              have same := StorageTypesRel.unique (show StorageTypesRel space a _ from queried) storedA
              subst same
              obtain ⟨check, checks, checked, nilPaired, rfl⟩ := List.forall₂_cons_left_iff.mp paired
              obtain rfl := List.forall₂_nil_left_iff.mp nilPaired
              obtain ⟨frame₁, rfl⟩ := check_accepts (acceptsA frame) checked
              simp only [Completed.checkedFrames, Completed.checkedFailures, List.filterMap_cons,
                List.filterMap_nil, List.map_nil, List.append_nil, List.nil_append] at later ⊢
              obtain ⟨frame', rest'⟩ := prefix_accepted pre preT' preA' (position + 1) frame₁ rest restT
                after _ stored' accepts' later
              refine ⟨frame', ?_⟩
              rw [List.length_cons, show position + (pre.length + 1) = position + 1 + pre.length by
                omega]
              exact rest'

/-- **The rejected argument**: its check keeps no frame and reports one `BadArgType` error; the
arguments after it add nothing. -/
theorem rejected_here {space : Space} {expression : Atom} {position : Nat} {frame : Frame}
    {bad badType badActual : Atom} {post postT : List Atom} {after : List Frame} {errors : List Atom}
    (stored : StorageTypesRel space bad [badActual]) (rejects : Rejects policy badType badActual)
    (checked : Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression
      position (bad :: post) (badType :: postT) [frame] after errors) :
    after = [] ∧ errors = [mkError expression (.badArgType position badType badActual)] := by
  cases checked with
  | cons head later =>
      cases head with
      | cons queried paired nilChecks =>
          cases nilChecks
          have same := StorageTypesRel.unique (show StorageTypesRel space bad _ from queried) stored
          subst same
          obtain ⟨check, checks, checked, nilPaired, rfl⟩ := List.forall₂_cons_left_iff.mp paired
          obtain rfl := List.forall₂_nil_left_iff.mp nilPaired
          cases checked with
          | accepted renewed =>
              cases renewed with
              | unchanged matched => exact (rejects _ _ matched).elim
              | unified matched _ => exact (rejects _ _ matched).elim
          | rejected _ =>
              simp only [Completed.checkedFrames, Completed.checkedFailures, List.filterMap_cons,
                List.filterMap_nil, List.map_cons, List.map_nil, List.append_nil] at later ⊢
              obtain ⟨rfl, rfl⟩ := no_frames_no_errors later rfl
              exact ⟨rfl, rfl⟩

/-- **The application checks of the call**: no activation, exactly the first mismatch's error. -/
theorem checks_first_mismatch {space : Space} {g : String} {pre preT preA post postT : List Atom}
    {bad badType badActual : Atom} {signature : SelectedTypePolicy} {frames : List Frame}
    {errors : List Atom}
    (types : signature.argumentTypes = preT ++ badType :: postT)
    (lengths : post.length = postT.length)
    (stored : List.Forall₂ (fun a A => StorageTypesRel space a [A]) pre preA)
    (accepts : List.Forall₂ (fun T A => Accepts policy T A) preT preA)
    (badStored : StorageTypesRel space bad [badActual]) (rejects : Rejects policy badType badActual)
    (checks : Completed.ApplicationChecksRel space (rawTypeLookupRel space) policy
      (.expression (.symbol g :: (pre ++ bad :: post))) Atom.undefinedType signature
      Completed.Frame.empty frames errors) :
    frames = [] ∧ errors = [mkError (.expression (.symbol g :: (pre ++ bad :: post)))
      (.badArgType (1 + pre.length) badType badActual)] := by
  cases checks with
  | wrongArity shaped arity =>
      simp only [Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [types] at arity
      apply absurd _ arity
      simp only [List.length_append, List.length_cons, stored.length_eq, ← accepts.length_eq,
        lengths]
  | checked shaped arguments returned =>
      simp only [Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [types] at arguments
      obtain ⟨frame', rest⟩ := prefix_accepted pre preT preA 1 Completed.Frame.empty (bad :: post)
        (badType :: postT) _ _ stored accepts arguments
      obtain ⟨rfl, rfl⟩ := rejected_here badStored rejects rest
      cases returned
      simp [Completed.checkedFrames, Completed.checkedFailures]

/-- **Every admission of the call ends exhausted**, with the first mismatch's error and without
tuple fallback. -/
theorem selection_exhausted {atoms : List Atom} {g : String} {arrow returnType : Atom}
    {pre preT preA post postT : List Atom} {bad badType badActual : Atom}
    (gTypes : StorageTypesRel (Space.ofList atoms) (.symbol g) [arrow])
    (arrowShape : FunctionTypeRel arrow (preT ++ badType :: postT) returnType)
    (lengths : post.length = postT.length)
    (stored : List.Forall₂ (fun a A => StorageTypesRel (Space.ofList atoms) a [A]) pre preA)
    (accepts : List.Forall₂ (fun T A => Accepts policy T A) preT preA)
    (badStored : StorageTypesRel (Space.ofList atoms) bad [badActual])
    (rejects : Rejects policy badType badActual) {outcome : Completed.InvocationSelection}
    (chosen : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
      (.expression (.symbol g :: (pre ++ bad :: post))) (.symbol g) Atom.undefinedType
      Completed.Frame.empty outcome) :
    outcome = .exhausted [mkError (.expression (.symbol g :: (pre ++ bad :: post)))
      (.badArgType (1 + pre.length) badType badActual)] false := by
  obtain ⟨candidates, queried, scanned⟩ := chosen
  have same := StorageTypesRel.unique
    (show StorageTypesRel (Space.ofList atoms) (.symbol g) candidates from queried) gTypes
  have typesOf : ∀ {signature : SelectedTypePolicy}, signature.functionType = arrow →
      signature.argumentTypes = preT ++ badType :: postT := by
    intro signature functionType
    have shaped : FunctionTypeRel arrow signature.argumentTypes signature.returnType :=
      functionType ▸ signature.isFunction
    exact (FunctionTypeRel.unique shaped arrowShape).1
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨_, _, arrowShape⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      exact absurd (checks_first_mismatch (typesOf functionType) lengths stored accepts badStored
        rejects checks).1 nonempty
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨_, rfl⟩ := checks_first_mismatch (typesOf functionType) lengths stored accepts badStored
        rejects checks
      cases rest
      rfl

/-- **Every derivation of HE's completed relation for the call publishes the first mismatch's
error.** -/
theorem error_source {atoms : List Atom} {g : String} {arrow returnType : Atom}
    {pre preT preA post postT : List Atom} {bad badType badActual : Atom}
    (gData : DataAtom (.symbol g)) (notUndefined : arrow ≠ Atom.undefinedType)
    (gTypes : StorageTypesRel (Space.ofList atoms) (.symbol g) [arrow])
    (arrowShape : FunctionTypeRel arrow (preT ++ badType :: postT) returnType)
    (lengths : post.length = postT.length)
    (stored : List.Forall₂ (fun a A => StorageTypesRel (Space.ofList atoms) a [A]) pre preA)
    (accepts : List.Forall₂ (fun T A => Accepts policy T A) preT preA)
    (badStored : StorageTypesRel (Space.ofList atoms) bad [badActual])
    (rejects : Rejects policy badType badActual) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom (.expression (.symbol g :: (pre ++ bad :: post)))) Atom.undefinedType
      Completed.Frame.empty results (policy := policy)) :
    results.map (fun r => r.1.erase) = [mkError (.expression (.symbol g :: (pre ++ bad :: post)))
      (.badArgType (1 + pre.length) badType badActual)] := by
  set call : Atom := .expression (.symbol g :: (pre ++ bad :: post)) with callEq
  set err : Atom := mkError call (.badArgType (1 + pre.length) badType badActual) with errEq
  have entry := call_entry policy gData (pre ++ bad :: post)
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom call) =
      .expression .active (Entry.Value.ofAtom (.symbol g) ::
        (pre ++ bad :: post).map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty, callEq]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom call)).erase
        (Entry.Value.ofAtom (.symbol g)).erase Atom.undefinedType Completed.Frame.empty result →
      result = .exhausted [err] false := by
    intro result chosen
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
    exact selection_exhausted gTypes arrowShape lengths stored accepts badStored rejects chosen
  have errIsError : isErrorAtom err = true := by
    simp [errEq, Mettapedia.Languages.MeTTa.HE.mkError, Atom.error, isErrorAtom]
  obtain ⟨_, chosen, invocation⟩ :=
    (Completed.AtomRel.iff_invocation entry shape (fun occurs => by
        rw [Entry.Value.erase_ofAtom] at occurs
        have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
          gTypes.occurrences
        simp only [Multiset.coe_singleton, Multiset.singleton_inj] at same
        exact absurd same.symm notUndefined)).mp derived
  cases invocation with
  | selected _ _ =>
      cases outcome chosen
  | fallback _ _ _ =>
      cases outcome chosen
  | failed selected =>
      have exhausted := outcome chosen
      simp only [Completed.InvocationSelection.exhausted.injEq] at exhausted
      obtain ⟨rfl, _⟩ := exhausted
      have unread : (Completed.diagnosticResults [err] Completed.Frame.empty).map
          (Completed.readResult policy) = Completed.diagnosticResults [err] Completed.Frame.empty := by
        simp [Completed.diagnosticResults, Completed.readResult]
      rw [unread] at selected
      have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
        selected (.allErrors fun item member => by
          simp only [Completed.diagnosticResults, List.map_cons, List.map_nil,
            List.mem_singleton] at member
          subst member
          simpa using errIsError)
      subst same
      simp [Completed.diagnosticResults, Completed.publishResult]

/-- **The error path of a declared head, at any arity, on every run.** For a head `g` whose one
stored type is the arrow `(-> T₁ … Tₙ R)`, a call `(g a₁ … aₙ)` of data atoms with one stored type
each, the demands before position `k` accepting and `T_k` rejecting: every complete run of HE's
machine (historical lookup, any policy, any dispatch) publishes exactly
`(Error (g a₁ … aₙ) (BadArgType k T_k A_k))`. -/
theorem error_every_run {atoms : List Atom} {g : String} {arrow returnType : Atom}
    {pre preT preA post postT : List Atom} {bad badType badActual : Atom}
    (gData : DataAtom (.symbol g)) (notUndefined : arrow ≠ Atom.undefinedType)
    (gTypes : StorageTypesRel (Space.ofList atoms) (.symbol g) [arrow])
    (arrowShape : FunctionTypeRel arrow (preT ++ badType :: postT) returnType)
    (lengths : post.length = postT.length)
    (stored : List.Forall₂ (fun a A => StorageTypesRel (Space.ofList atoms) a [A]) pre preA)
    (accepts : List.Forall₂ (fun T A => Accepts policy T A) preT preA)
    (badStored : StorageTypesRel (Space.ofList atoms) bad [badActual])
    (rejects : Rejects policy badType badActual) (emitted : List Result)
    (run : Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
      (load (Space.ofList atoms) (.expression (.symbol g :: (pre ++ bad :: post))) Atom.undefinedType)
      ⟨Space.ofList atoms, .returning [], [], emitted⟩) :
    emitted.map (fun r => r.1.erase) = [mkError (.expression (.symbol g :: (pre ++ bad :: post)))
      (.badArgType (1 + pre.length) badType badActual)] :=
  error_source gData notUndefined gTypes arrowShape lengths stored accepts badStored rejects
    (complete_source run)

/-! ## A complete run -/

/-- The demand `expected` accepts the type `actual` at every frame, with the bindings unchanged. -/
def AcceptsKeeping (policy : Policy) (expected actual : Atom) : Prop :=
  ∀ frame : Frame, policy.matching.Rel expected actual frame.bindings frame.bindings

/-- Arguments checked against no frame: no frame and no error. -/
theorem no_frames_forward {space : Space} {expression : Atom} :
    ∀ (position : Nat) (arguments types : List Atom), arguments.length = types.length →
      Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression position
        arguments types [] [] []
  | _, [], [], _ => .nil
  | position, _ :: arguments, _ :: types, lengths =>
      .cons .nil (no_frames_forward (position + 1) arguments types (by simpa using lengths))
  | _, [], _ :: _, lengths => absurd lengths (by simp)
  | _, _ :: _, [], lengths => absurd lengths (by simp)

/-- The rejected argument: no frame survives, one `BadArgType` error. -/
theorem rejected_forward {space : Space} {expression : Atom} {position : Nat} {frame : Frame}
    {bad badType badActual : Atom} (stored : StorageTypesRel space bad [badActual])
    (rejects : Rejects policy badType badActual) {post postT : List Atom}
    (lengths : post.length = postT.length) :
    Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression position
      (bad :: post) (badType :: postT) [frame] []
      [mkError expression (.badArgType position badType badActual)] :=
  .cons (.cons stored (.cons (.rejected (rejects frame.bindings)) .nil) .nil)
    (no_frames_forward (position + 1) post postT lengths)

/-- An accepted prefix keeps the frame. -/
theorem prefix_forward {space : Space} {expression : Atom} :
    ∀ (pre preT preA : List Atom) (position : Nat) (frame : Frame) (rest restT : List Atom)
      (after : List Frame) (errors : List Atom),
      List.Forall₂ (fun a A => StorageTypesRel space a [A]) pre preA →
      List.Forall₂ (fun T A => AcceptsKeeping policy T A) preT preA →
      Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression
        (position + pre.length) rest restT [frame] after errors →
      Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression position
        (pre ++ rest) (preT ++ restT) [frame] after errors
  | [], preT, preA, position, frame, rest, restT, after, errors, stored, keeps, later => by
      cases stored
      cases keeps
      simpa using later
  | a :: pre, preT, preA, position, frame, rest, restT, after, errors, stored, keeps, later => by
      obtain ⟨A, preA', storedA, stored', rfl⟩ := List.forall₂_cons_left_iff.mp stored
      obtain ⟨T, preT', keepsA, keeps', rfl⟩ := List.forall₂_cons_right_iff.mp keeps
      have shift : position + (a :: pre).length = position + 1 + pre.length := by
        simp only [List.length_cons]
        omega
      rw [shift] at later
      exact .cons (.cons storedA (.cons (.accepted (.unchanged (keepsA frame))) .nil) .nil)
        (prefix_forward pre preT' preA' (position + 1) frame rest restT after errors stored' keeps'
          later)

/-- **A complete run of the declared call, publishing the first mismatch's error.** -/
theorem error_run_exists (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    {g : String} {arrow returnType : Atom} {pre preT preA post postT : List Atom}
    {bad badType badActual : Atom} (gData : DataAtom (.symbol g))
    (gTypes : StorageTypesRel (Space.ofList atoms) (.symbol g) [arrow])
    (arrowShape : FunctionTypeRel arrow (preT ++ badType :: postT) returnType)
    (lengths : post.length = postT.length)
    (stored : List.Forall₂ (fun a A => StorageTypesRel (Space.ofList atoms) a [A]) pre preA)
    (keeps : List.Forall₂ (fun T A => AcceptsKeeping policy T A) preT preA)
    (badStored : StorageTypesRel (Space.ofList atoms) bad [badActual])
    (rejects : Rejects policy badType badActual) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (.expression (.symbol g :: (pre ++ bad :: post)))
            Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [mkError (.expression (.symbol g :: (pre ++ bad :: post)))
          (.badArgType (1 + pre.length) badType badActual)] := by
  set call : Atom := .expression (.symbol g :: (pre ++ bad :: post)) with callEq
  set err : Atom := mkError call (.badArgType (1 + pre.length) badType badActual) with errEq
  let signature : SelectedTypePolicy := ⟨arrow, preT ++ badType :: postT, returnType, arrowShape⟩
  have arguments : Completed.ApplicabilityArgumentsRel (Space.ofList atoms)
      (rawTypeLookupRel (Space.ofList atoms)) policy call 1 (pre ++ bad :: post)
      (preT ++ badType :: postT) [Completed.Frame.empty] [] [err] :=
    prefix_forward pre preT preA 1 Completed.Frame.empty (bad :: post) (badType :: postT) [] [err]
      stored keeps (rejected_forward badStored rejects lengths)
  have checks : Completed.ApplicationChecksRel (Space.ofList atoms)
      (rawTypeLookupRel (Space.ofList atoms)) policy call Atom.undefinedType signature
      Completed.Frame.empty [] ([err] ++ []) :=
    .checked (operator := .symbol g) (arguments := pre ++ bad :: post) rfl arguments .nil
  have chosen : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
      call (.symbol g) Atom.undefinedType Completed.Frame.empty
      (.exhausted (([err] ++ []) ++ []) false) :=
    ⟨[signature.functionType], gTypes, .rejected checks .nil⟩
  have entry := call_entry policy gData (pre ++ bad :: post)
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom call) =
      .expression .active (Entry.Value.ofAtom (.symbol g) ::
        (pre ++ bad :: post).map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty, callEq]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom call)).erase
      (Entry.Value.ofAtom (.symbol g)).erase Atom.undefinedType Completed.Frame.empty
      (.exhausted (([err] ++ []) ++ []) false) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact chosen
  have step := LocalStepWith.atomSelectionFailed (admission := .historical)
    (space := Space.ofList atoms) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom call)).erase = call := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  set raw := Completed.diagnosticResults (([err] ++ []) ++ []) Completed.Frame.empty with rawEq
  have unread : raw.map (Completed.readResult policy) = raw := by
    rw [rawEq]
    simp [Completed.diagnosticResults, Completed.readResult]
  have allErrors : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase) (raw.map (Completed.readResult policy))
      raw := by
    rw [unread]
    exact .allErrors fun item member => by
      rw [rawEq] at member
      simp only [Completed.diagnosticResults, List.append_nil, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst member
      simp [errEq, Mettapedia.Languages.MeTTa.HE.mkError, Atom.error, isErrorAtom]
  refine ⟨raw.map (Completed.publishResult policy call), ?_, ?_⟩
  · refine .head (.internal step) ?_
    refine .head (.internal (.publish allErrors)) ?_
    exact HERuns.publish_all _ _ []
  · rw [rawEq]
    simp [Completed.diagnosticResults, Completed.publishResult]

/-- **The error path of a declared head, at any arity, on every run, with a complete run.** Under
the hypotheses of `error_every_run`, with the prefix demands accepting their types with the bindings
unchanged: a complete run exists, and every complete run publishes exactly the first mismatch's
`BadArgType` error. -/
theorem error_every_run_complete (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    {g : String} {arrow returnType : Atom} {pre preT preA post postT : List Atom}
    {bad badType badActual : Atom} (gData : DataAtom (.symbol g))
    (notUndefined : arrow ≠ Atom.undefinedType)
    (gTypes : StorageTypesRel (Space.ofList atoms) (.symbol g) [arrow])
    (arrowShape : FunctionTypeRel arrow (preT ++ badType :: postT) returnType)
    (lengths : post.length = postT.length)
    (stored : List.Forall₂ (fun a A => StorageTypesRel (Space.ofList atoms) a [A]) pre preA)
    (keeps : List.Forall₂ (fun T A => AcceptsKeeping policy T A) preT preA)
    (badStored : StorageTypesRel (Space.ofList atoms) bad [badActual])
    (rejects : Rejects policy badType badActual) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (.expression (.symbol g :: (pre ++ bad :: post)))
            Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) (.expression (.symbol g :: (pre ++ bad :: post)))
              Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) =
            [mkError (.expression (.symbol g :: (pre ++ bad :: post)))
              (.badArgType (1 + pre.length) badType badActual)] := by
  have accepts : List.Forall₂ (fun T A => Accepts policy T A) preT preA :=
    keeps.imp fun _ _ keeping frame => ⟨_, keeping frame⟩
  obtain ⟨heAnswers, path, _⟩ := error_run_exists dispatch policy gData gTypes arrowShape lengths stored
    keeps badStored rejects
  exact ⟨⟨heAnswers, path⟩, fun emitted run => error_every_run gData notUndefined gTypes arrowShape
    lengths stored accepts badStored rejects emitted run⟩

/-! ## Controls -/

namespace Controls

/-- `(-> Number Number Number Number)`. -/
abbrev arrow3 : Atom := .expression [.symbol "->", sym "Number", sym "Number", sym "Number", sym "Number"]

/-- `{(: h (-> Number Number Number Number)), (: b Bool), (= (h $x $y $z) yes)}`. -/
abbrev rows3 : List Atom :=
  [.expression [.symbol ":", sym "h", arrow3],
   .expression [.symbol ":", sym "b", sym "Bool"],
   rule (app "h" [.var "x", .var "y", .var "z"]) (sym "yes")]

theorem h_types : StorageTypesRel (Space.ofList rows3) (.symbol "h") [arrow3] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) .nil))) (by simp)

theorem b3_types : StorageTypesRel (Space.ofList rows3) (.symbol "b") [sym "Bool"] :=
  .symbolKnown (.skip (fun _ same => by simp at same)
    (.hit (.skip (fun _ same => by simp at same) .nil))) (by simp)

theorem int_types (n : Int) : StorageTypesRel (Space.ofList rows3) (.grounded (.int n)) [sym "Number"] :=
  .groundedKnown (.int n) (by simp [Atom.undefinedType])

theorem number_accepts_number : Accepts policy (sym "Number") (sym "Number") :=
  fun frame => ⟨_, Completed.Frame.preserved_type_match policy frame (number_matches _)⟩

theorem number_rejects : Rejects policy (sym "Number") (sym "Bool") :=
  fun bindings output => number_rejects_bool policy bindings output

theorem number_keeps : AcceptsKeeping policy (sym "Number") (sym "Number") :=
  fun frame => Completed.Frame.preserved_type_match policy frame (number_matches _)

/-- The arity-3 program lies in the measured type fragment. -/
theorem fragment_rows3 : TypeQueryFragment.MeasuredTypeFragment rows3 :=
  ⟨by decide, by unfold Mettapedia.Languages.MeTTa.HE.HOLContract.SubtypeFree; decide⟩

/-- **Positive control, arity 3**: on `rows3`, a program in the measured type fragment, a complete
HE run of `(h 1 b 2)` exists and every complete run publishes
`(Error (h 1 b 2) (BadArgType 2 Number Bool))`. On the program without `h`'s declaration PeTTa answers
`yes`, as the PeTTa hosts do; with the declaration the hosts answer nothing. -/
theorem arity_three (dispatch : GroundedDispatch) (policy : Policy) :
    TypeQueryFragment.MeasuredTypeFragment rows3 ∧
      (∃ heAnswers : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList rows3) (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)])
            Atom.undefinedType)
          ⟨Space.ofList rows3, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList rows3) (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)])
            Atom.undefinedType)
          ⟨Space.ofList rows3, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) =
          [mkError (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)])
            (.badArgType 2 (sym "Number") (sym "Bool"))]) ∧
      Streaming.values (Streaming.advance (translate (headUndeclared rows3 "h")) 60
        (Streaming.enter { state := store (headUndeclared rows3 "h") }
          (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)]))) = [sym "yes"] := by
  obtain ⟨exists_, every⟩ := error_every_run_complete (pre := [.grounded (.int 1)])
    (preT := [sym "Number"]) (preA := [sym "Number"]) (post := [.grounded (.int 2)])
    (postT := [sym "Number"]) dispatch policy (.symbol (by decide) (by decide)) (by decide) h_types
    rfl rfl (.cons (int_types 1) .nil) (.cons number_keeps .nil) b3_types number_rejects
  exact ⟨fragment_rows3, exists_, every, by decide +kernel⟩

/-- **The arity-3 control has a complete run**: HE's run of `(h 1 b 2)` reaches a completed phase,
and every completed run publishes `(Error (h 1 b 2) (BadArgType 2 Number Bool))`. -/
theorem arity_three_complete (dispatch : GroundedDispatch) (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList rows3) (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)])
            Atom.undefinedType)
          ⟨Space.ofList rows3, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList rows3) (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)])
              Atom.undefinedType)
            ⟨Space.ofList rows3, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) =
            [mkError (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)])
              (.badArgType 2 (sym "Number") (sym "Bool"))] :=
  error_every_run_complete (pre := [.grounded (.int 1)]) (preT := [sym "Number"])
    (preA := [sym "Number"]) (post := [.grounded (.int 2)]) (postT := [sym "Number"]) dispatch policy
    (.symbol (by decide) (by decide)) (by decide) h_types rfl rfl (.cons (int_types 1) .nil)
    (.cons number_keeps .nil) b3_types number_rejects

/-- **The first mismatch only**: `(h b b 2)` has two ill-typed arguments. On `rows3`, in the
measured type fragment, a complete HE run exists and every complete run
reports only position 1; the second is checked against no frame. On the program without `h`'s
declaration PeTTa answers `yes`, as the PeTTa hosts do; with the declaration the hosts answer
nothing. -/
theorem first_mismatch_only (dispatch : GroundedDispatch) (policy : Policy) :
    TypeQueryFragment.MeasuredTypeFragment rows3 ∧
      (∃ heAnswers : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList rows3) (app "h" [sym "b", sym "b", .grounded (.int 2)])
            Atom.undefinedType)
          ⟨Space.ofList rows3, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList rows3) (app "h" [sym "b", sym "b", .grounded (.int 2)])
            Atom.undefinedType)
          ⟨Space.ofList rows3, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) =
          [mkError (app "h" [sym "b", sym "b", .grounded (.int 2)])
            (.badArgType 1 (sym "Number") (sym "Bool"))]) ∧
      Streaming.values (Streaming.advance (translate (headUndeclared rows3 "h")) 60
        (Streaming.enter { state := store (headUndeclared rows3 "h") }
          (app "h" [sym "b", sym "b", .grounded (.int 2)]))) = [sym "yes"] := by
  obtain ⟨exists_, every⟩ := error_every_run_complete (pre := []) (preT := []) (preA := [])
    (post := [sym "b", .grounded (.int 2)]) (postT := [sym "Number", sym "Number"]) dispatch policy
    (.symbol (by decide) (by decide)) (by decide) h_types rfl rfl .nil .nil b3_types number_rejects
  exact ⟨fragment_rows3, exists_, every, by decide +kernel⟩

/-- **Control: the hypothesis "no declaration for the head" is needed on PeTTa's side.** On these
programs, whose declarations have no `Atom` parameter, the PeTTa model answers the same with and
without the head's declaration: `yes` to `(f 4)`, `(f b)`, `(h 1 b 2)` and `(h b b 2)`. Both PeTTa
hosts answer nothing on the declared programs and `yes` on the programs without the head's
declaration, so the model's answer is the hosts' only under that hypothesis. The model does read
one thing from declarations, which these programs do not exercise: it holds an argument as written
where some row of the name has `Atom` at that position (`Eval.argumentIsRaw_iff_declaredAtom`;
`ThreeDifferences.two_rows_models` shows it on a program with such a row). -/
theorem petta_model_reads_no_declaration :
    Streaming.values (Streaming.advance (translate declaredRows) 40
        (Streaming.enter { state := store declaredRows } typedCall)) =
      Streaming.values (Streaming.advance (translate (headUndeclared declaredRows "f")) 40
        (Streaming.enter { state := store (headUndeclared declaredRows "f") } typedCall)) ∧
    Streaming.values (Streaming.advance (translate declaredRows) 40
        (Streaming.enter { state := store declaredRows } declaredCall)) =
      Streaming.values (Streaming.advance (translate (headUndeclared declaredRows "f")) 40
        (Streaming.enter { state := store (headUndeclared declaredRows "f") } declaredCall)) ∧
    Streaming.values (Streaming.advance (translate rows3) 60
        (Streaming.enter { state := store rows3 }
          (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)]))) =
      Streaming.values (Streaming.advance (translate (headUndeclared rows3 "h")) 60
        (Streaming.enter { state := store (headUndeclared rows3 "h") }
          (app "h" [.grounded (.int 1), sym "b", .grounded (.int 2)]))) ∧
    Streaming.values (Streaming.advance (translate rows3) 60
        (Streaming.enter { state := store rows3 } (app "h" [sym "b", sym "b", .grounded (.int 2)]))) =
      Streaming.values (Streaming.advance (translate (headUndeclared rows3 "h")) 60
        (Streaming.enter { state := store (headUndeclared rows3 "h") }
          (app "h" [sym "b", sym "b", .grounded (.int 2)]))) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `declaredRows` with the subtype row `(:< Bool Number)`. -/
abbrev subtypeRows : List Atom :=
  declaredRows ++ [.expression [.symbol ":<", sym "Bool", sym "Number"]]

theorem f_types_subtype : StorageTypesRel (Space.ofList subtypeRows) (.symbol "f")
    [.expression [.symbol "->", sym "Number", sym "Number"]] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) .nil)))) (by simp)

theorem b_types_subtype : StorageTypesRel (Space.ofList subtypeRows) (.symbol "b") [sym "Bool"] :=
  .symbolKnown (.skip (fun _ same => by simp at same) (.hit (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) .nil)))) (by simp)

/-- **Control: no subtype row is needed.** With `(:< Bool Number)` added to the declared program,
outside the fragment, a complete run of the model on `(f b)` exists and every complete run still
publishes `(Error (f b) (BadArgType 1 Number Bool))`: the model reads no subtype row. HE reads it,
types `b` as `Bool` and `Number`, and answers `yes`. -/
theorem subtype_row_needed (dispatch : GroundedDispatch) (policy : Policy) :
    ¬ Mettapedia.Languages.MeTTa.HE.HOLContract.SubtypeFree (Space.ofList subtypeRows) ∧
      (∃ heAnswers : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList subtypeRows) declaredCall Atom.undefinedType)
          ⟨Space.ofList subtypeRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList subtypeRows) declaredCall Atom.undefinedType)
          ⟨Space.ofList subtypeRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [badArgument] := by
  obtain ⟨exists_, every⟩ := error_every_run_complete (pre := []) (preT := []) (preA := [])
    (post := []) (postT := []) (bad := sym "b") dispatch policy (.symbol (by decide) (by decide))
    (by decide) f_types_subtype rfl rfl .nil .nil b_types_subtype number_rejects
  exact ⟨by unfold Mettapedia.Languages.MeTTa.HE.HOLContract.SubtypeFree; decide, exists_, every⟩

end Controls

#print axioms no_frames_no_errors
#print axioms prefix_accepted
#print axioms rejected_here
#print axioms checks_first_mismatch
#print axioms selection_exhausted
#print axioms error_source
#print axioms error_every_run
#print axioms prefix_forward
#print axioms rejected_forward
#print axioms error_run_exists
#print axioms error_every_run_complete
#print axioms Controls.fragment_rows3
#print axioms Controls.arity_three
#print axioms Controls.arity_three_complete
#print axioms Controls.first_mismatch_only
#print axioms Controls.petta_model_reads_no_declaration
#print axioms Controls.subtype_row_needed

end DeclaredErrors

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
