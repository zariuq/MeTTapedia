import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceSubstitution
import Mettapedia.GSLT.Dynamics.ServiceResumption

/-!
# Scoped programs with repeatable judgment-service calls

Requests are authored inside the same scoped syntax as their continuations.
Sequencing binds the actual returned native value, so a subsequent request's
native environment may use it. Native computation is the existing reified
code, not a second term language. Ordinary sequencing and value-retaining
dependent sequencing remain distinct.

This candidate composition does not adopt an evaluation strategy, add a
proof-byte format, or identify a formed HOL proposition with a native proof
of it. A declined service must remain an observable stopped response.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServicePrograms

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation
open SharedJudgmentFragment SharedJudgmentServices
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption

abbrev NativeCode := ScopedComputation.Code Tower.Head ScopedComputation.NativeExamples.Operation

/-- The scope index counts native variables, including prior service values.
The binding bodies are syntax, not host-language functions. -/
inductive Code : Nat → Type where
  | native {n : Nat} (body : NativeCode n) : Code n
  | request {n : Nat} (input : Request n) : Code n
  | sequence {n : Nat} (first : Code n) (body : Code (n + 1)) : Code n
  | sequenceSigma {n : Nat} (first : Code n) (body : Code (n + 1)) : Code n
  | choose {n : Nat} (left right : Code n) : Code n

namespace Code

variable {n m k : Nat}

def substitute {n m : Nat} (environment : Sub Tower.Head n m) : Code n → Code m
  | .native body => .native (body.substitute environment)
  | .request input => .request (input.substitute environment)
  | .sequence first body =>
      .sequence (substitute environment first) (substitute (liftSub environment) body)
  | .sequenceSigma first body =>
      .sequenceSigma (substitute environment first) (substitute (liftSub environment) body)
  | .choose left right => .choose (substitute environment left) (substitute environment right)

theorem substitute_ext {first second : Sub Tower.Head n m}
    (same : ∀ index, first index = second index) (code : Code n) :
    code.substitute first = code.substitute second := by
  rw [funext same]

@[simp] theorem substitute_ids (code : Code n) : code.substitute ids = code := by
  induction code with
  | native body => simp only [substitute, ScopedComputation.Code.substitute_ids]
  | request input => simp only [substitute, Request.substitute_ids]
  | sequence first body firstIH bodyIH =>
      simp only [substitute, liftSub_ids, firstIH, bodyIH]
  | sequenceSigma first body firstIH bodyIH =>
      simp only [substitute, liftSub_ids, firstIH, bodyIH]
  | choose left right leftIH rightIH => simp only [substitute, leftIH, rightIH]

@[simp] theorem substitute_comp (later : Sub Tower.Head m k)
    (earlier : Sub Tower.Head n m) (code : Code n) :
    (code.substitute earlier).substitute later = code.substitute (subComp later earlier) := by
  induction code generalizing m k with
  | native body => simp only [substitute, ScopedComputation.Code.substitute_comp]
  | request input => simp only [substitute, Request.substitute_comp]
  | sequence first body firstIH bodyIH =>
      simp only [substitute, firstIH, bodyIH]
      congr 1
      exact substitute_ext (fun index => liftSub_comp_apply later earlier index) body
  | sequenceSigma first body firstIH bodyIH =>
      simp only [substitute, firstIH, bodyIH]
      congr 1
      exact substitute_ext (fun index => liftSub_comp_apply later earlier index) body
  | choose left right leftIH rightIH => simp only [substitute, leftIH, rightIH]

/-- Opening one native binder uses the already proved substitution algebra. -/
def instantiate (value : Tower.Tm n) (body : Code (n + 1)) : Code n :=
  body.substitute (subst0 value)

theorem substitute_instantiate (environment : Sub Tower.Head n m)
    (value : Tower.Tm n) (body : Code (n + 1)) :
    (body.instantiate value).substitute environment =
      (body.substitute (liftSub environment)).instantiate (subst environment value) := by
  simp only [instantiate, substitute_comp]
  apply substitute_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    exact (inst0_rename_wk (subst environment value) (environment prior)).symm

end Code

/-- Preserve the existing one-crossing source as an authored sequence. -/
def ofSource {n : Nat} (source : Source n) : Code n :=
  .sequence (.request source.request) (.native source.continuation)

theorem ofSource_substitute {n m : Nat} (environment : Sub Tower.Head n m)
    (source : Source n) :
    (ofSource source).substitute environment = ofSource (source.substitute environment) := rfl

/-- A stopped response is retained as data at its exact request index. It is
neither a returned native value nor an empty collection of successful worlds. -/
inductive Outcome (n : Nat) where
  | value (term : Tower.Tm n)
  | stopped (reply : Sigma (@Response n))

namespace Outcome

def map {n : Nat} (function : Tower.Tm n → Tower.Tm n) : Outcome n → Outcome n
  | .value term => .value (function term)
  | .stopped reply => .stopped reply

end Outcome

abbrev Execution (n : Nat) := Resumption (Request n) (@Response n) Bool (Outcome n) Nat

/-- Expose a request node before invoking its service. The interpreter does
not precompute this crossing into a native effect body. -/
def requestProgram {n : Nat} (request : Request n) : Execution n :=
  .request request fun response => .pure <|
    match response.nativePayload? with
    | some payload => .value payload.1
    | none => .stopped ⟨request, response⟩

namespace Code

variable {n m k : Nat}

/-- Interpret all nested requests through one supplied assembly and all
native bodies through its handler at the target scope. Success opens the
same capture-avoiding environment used by ordinary native sequencing. -/
def interpret {n : Nat} (assembly : Assembly) (environment : Sub Tower.Head n m) : Code n → Execution m
  | .native body =>
      (embed (ScopedComputation.Code.interpret (assembly.execution m).handler environment body)).map
        Outcome.value
  | .request input => requestProgram (input.substitute environment)
  | .sequence first body =>
      (interpret assembly environment first).bind fun outcome =>
        match outcome with
        | .value value => interpret assembly (consSub value environment) body
        | .stopped reply => .pure (.stopped reply)
  | .sequenceSigma first body =>
      (interpret assembly environment first).bind fun outcome =>
        match outcome with
        | .value value =>
            (interpret assembly (consSub value environment) body).map (Outcome.map (.pair value))
        | .stopped reply => .pure (.stopped reply)
  | .choose left right =>
      .choose (interpret assembly environment left) (interpret assembly environment right)

/-- One target handler suffices: this law does not assume that execution
handlers at different scopes commute with substitution. -/
theorem interpret_substitute (assembly : Assembly) (later : Sub Tower.Head m k)
    (earlier : Sub Tower.Head n m) (code : Code n) :
    interpret assembly later (code.substitute earlier) =
      interpret assembly (subComp later earlier) code := by
  induction code generalizing m with
  | native body =>
      simp only [substitute, interpret, ScopedComputation.Code.interpret_substitute]
  | request input => simp only [substitute, interpret, Request.substitute_comp]
  | sequence first body firstIH bodyIH =>
      simp only [substitute, interpret, firstIH]
      congr 1
      funext outcome
      cases outcome with
      | value value => simp only [bodyIH, ScopedComputation.Code.consSub_liftSub_comp]
      | stopped reply => rfl
  | sequenceSigma first body firstIH bodyIH =>
      simp only [substitute, interpret, firstIH]
      congr 1
      funext outcome
      cases outcome with
      | value value => simp only [bodyIH, ScopedComputation.Code.consSub_liftSub_comp]
      | stopped reply => rfl
  | choose left right leftIH rightIH => simp only [substitute, interpret, leftIH, rightIH]

theorem interpret_instantiate (assembly : Assembly) (environment : Sub Tower.Head n m)
    (value : Tower.Tm n) (body : Code (n + 1)) :
    interpret assembly environment (body.instantiate value) =
      interpret assembly (consSub (subst environment value) environment) body := by
  rw [instantiate, interpret_substitute]
  congr 1
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

/-- The exact ordered worlds retain intermediate service replies even when
the last outcome is stopped. This is execution by the supplied callback, not
an independently authored backend or a termination claim for proof search. -/
def run (assembly : Assembly) (environment : Sub Tower.Head n m) (code : Code n)
    (state : Bool) (branch : BranchTrace) :=
  runWorldsAt (invoke assembly) (interpret assembly environment code) state branch

/-- Direct recursion on the authored program, with primitive native world
lists rather than native effect interpretation. The request case calls the
assembly's actual operation and retains its indexed reply independently of
whether a native value is returned. -/
def worlds {n : Nat} (assembly : Assembly) (environment : Sub Tower.Head n m) :
    Code n → Bool → BranchTrace → List (Result (Request m) (@Response m) Bool (Outcome m) Nat)
  | .native body, state, branch =>
      (ScopedComputation.Code.worlds (assembly.execution m).primitive environment body state branch).map
        fun world =>
          { world :=
              { branch := world.branch, answer := .value world.answer,
                state := world.state, intents := world.intents }
            replies := [] }
  | .request input, state, branch =>
      let request := input.substitute environment
      let response := invoke assembly request
      let outcome := match response.nativePayload? with
        | some payload => Outcome.value payload.1
        | none => Outcome.stopped ⟨request, response⟩
      [{ world := { branch := branch, answer := outcome, state := state, intents := [] }
         replies := [⟨request, response⟩] }]
  | .sequence first body, state, branch =>
      (worlds assembly environment first state branch).flatMap fun prior =>
        match prior.world.answer with
        | .value value =>
            (worlds assembly (consSub value environment) body prior.world.state prior.world.branch).map
              (Result.prepend prior.world.intents prior.replies)
        | .stopped _ => [prior]
  | .sequenceSigma first body, state, branch =>
      (worlds assembly environment first state branch).flatMap fun prior =>
        match prior.world.answer with
        | .value value =>
            (worlds assembly (consSub value environment) body prior.world.state prior.world.branch).map
              fun later => Result.prepend prior.world.intents prior.replies
                (Result.mapAnswer (Outcome.map (.pair value)) later)
        | .stopped _ => [prior]
  | .choose left right, state, branch =>
      worlds assembly environment left state (false :: branch) ++
        worlds assembly environment right state (true :: branch)

/-- Every finite authored service program has exactly its independently
defined ordered worlds under the qualified native implementation. This is
not merely agreement of answer sets or a proof for one displayed workload. -/
theorem interpret_worlds (assembly : Assembly) (execution : ExecutionQualified assembly)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace) :
    run assembly environment code state branch = worlds assembly environment code state branch := by
  unfold run
  induction code generalizing state branch with
  | native body =>
      rw [interpret, runWorldsAt_map, runWorldsAt_embed,
        ScopedComputation.ImplementationStudy.qualified_worlds
          (assembly.execution m) (execution m)]
      simp only [worlds, List.map_map, Function.comp_def, Result.mapAnswer,
        Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer]
  | request input =>
      simp only [interpret, requestProgram, runWorldsAt_request, runWorldsAt_pure,
        worlds, List.map_cons, List.map_nil, Result.prepend, List.append_nil]
  | sequence first body firstIH bodyIH =>
      rw [interpret, runWorldsAt_bind, firstIH]
      change _ = (worlds assembly environment first state branch).flatMap _
      apply List.flatMap_congr
      intro prior _
      cases same : prior.world.answer with
      | value value => simp only [bodyIH]
      | stopped reply =>
          simp only [runWorldsAt_pure, List.map_cons, List.map_nil,
            Result.prepend, List.append_nil]
          cases prior with
          | mk world replies => cases world; cases same; rfl
  | sequenceSigma first body firstIH bodyIH =>
      rw [interpret, runWorldsAt_bind, firstIH]
      change _ = (worlds assembly environment first state branch).flatMap _
      apply List.flatMap_congr
      intro prior _
      cases same : prior.world.answer with
      | value value => simp only [runWorldsAt_map, bodyIH, List.map_map, Function.comp_def]
      | stopped reply =>
          simp only [runWorldsAt_pure, List.map_cons, List.map_nil,
            Result.prepend, List.append_nil]
          cases prior with
          | mk world replies => cases world; cases same; rfl
  | choose left right leftIH rightIH =>
      simp only [interpret, worlds, runWorldsAt_choose, leftIH, rightIH]

theorem sequence_request_worlds (assembly : Assembly) (environment : Sub Tower.Head n m)
    (input : Request n) (body : Code (n + 1)) (state : Bool) (branch : BranchTrace)
    {payload type : Tower.Tm m}
    (returned : (invoke assembly (input.substitute environment)).nativePayload? = some (payload, type)) :
    worlds assembly environment (.sequence (.request input) body) state branch =
      (worlds assembly (consSub payload environment) body state branch).map
        (Result.prepend [] [⟨input.substitute environment, invoke assembly (input.substitute environment)⟩]) := by
  simp only [worlds, returned, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Failure stops this sequence but retains the exact submitted request and
returned status. It cannot be mistaken for an empty successful answer list. -/
theorem stopped_request_worlds (assembly : Assembly) (environment : Sub Tower.Head n m)
    (input : Request n) (body : Code (n + 1)) (state : Bool) (branch : BranchTrace)
    (stopped : (invoke assembly (input.substitute environment)).nativePayload? = none) :
    worlds assembly environment (.sequence (.request input) body) state branch =
      [{ world :=
           { branch := branch
             answer := .stopped ⟨input.substitute environment, invoke assembly (input.substitute environment)⟩
             state := state, intents := [] }
         replies := [⟨input.substitute environment, invoke assembly (input.substitute environment)⟩] }] := by
  simp only [worlds, stopped, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The second submitted request is instantiated with the first actual
payload. Both full request/reply pairs precede every later reply. -/
theorem two_request_worlds (assembly : Assembly) (environment : Sub Tower.Head n m)
    (first : Request n) (second : Request (n + 1)) (body : Code (n + 2))
    (state : Bool) (branch : BranchTrace) {firstValue firstType secondValue secondType : Tower.Tm m}
    (firstReturned : (invoke assembly (first.substitute environment)).nativePayload? =
      some (firstValue, firstType))
    (secondReturned : (invoke assembly (second.substitute (consSub firstValue environment))).nativePayload? =
      some (secondValue, secondType)) :
    worlds assembly environment (.sequence (.request first) (.sequence (.request second) body)) state branch =
      (worlds assembly (consSub secondValue (consSub firstValue environment)) body state branch).map
        (Result.prepend []
          [⟨first.substitute environment, invoke assembly (first.substitute environment)⟩,
           ⟨second.substitute (consSub firstValue environment),
             invoke assembly (second.substitute (consSub firstValue environment))⟩]) := by
  rw [sequence_request_worlds assembly environment first _ state branch firstReturned,
    sequence_request_worlds assembly _ second body state branch secondReturned]
  simp only [List.map_map, Function.comp_def, Result.prepend_comp,
    List.nil_append, List.cons_append]

/-- A later decline retains the successful earlier crossing and the actual
failed request, while the body after that request is never evaluated. -/
theorem two_request_stopped_worlds (assembly : Assembly) (environment : Sub Tower.Head n m)
    (first : Request n) (second : Request (n + 1)) (body : Code (n + 2))
    (state : Bool) (branch : BranchTrace) {firstValue firstType : Tower.Tm m}
    (firstReturned : (invoke assembly (first.substitute environment)).nativePayload? =
      some (firstValue, firstType))
    (secondStopped : (invoke assembly (second.substitute (consSub firstValue environment))).nativePayload? =
      none) :
    worlds assembly environment (.sequence (.request first) (.sequence (.request second) body)) state branch =
      [{ world :=
           { branch := branch
             answer := .stopped ⟨second.substitute (consSub firstValue environment),
               invoke assembly (second.substitute (consSub firstValue environment))⟩
             state := state, intents := [] }
         replies := [⟨first.substitute environment, invoke assembly (first.substitute environment)⟩,
           ⟨second.substitute (consSub firstValue environment),
             invoke assembly (second.substitute (consSub firstValue environment))⟩] }] := by
  rw [sequence_request_worlds assembly environment first _ state branch firstReturned,
    stopped_request_worlds assembly _ second body state branch secondStopped]
  simp only [List.map_cons, List.map_nil, Result.prepend, List.nil_append, List.cons_append]

end Code

/-- On success the repeatable syntax executes the original one-crossing
native body exactly, adding only the retained request/reply history. This
does not identify the old optional failure with an empty successful run. -/
theorem ofSource_success {n : Nat} (assembly : Assembly) (source : Source n)
    {payload type : Tower.Tm n}
    (returned : (invoke assembly source.request).nativePayload? = some (payload, type))
    (state : Bool) (branch : BranchTrace) :
    Code.run assembly ids (ofSource source) state branch =
      (Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.runWorldsAt
        (ScopedComputation.Code.interpret (assembly.execution n).handler
          (consSub payload ids) source.continuation) state branch).map fun world =>
        { world :=
            { branch := world.branch, answer := .value world.answer,
              state := world.state, intents := world.intents }
          replies := [⟨source.request, invoke assembly source.request⟩] } := by
  have requestSame := congrArg (@requestProgram n) (Request.substitute_ids source.request)
  unfold Code.run ofSource
  simp only [Code.interpret]
  rw [requestSame]
  simp only [requestProgram,
    runWorldsAt_bind, runWorldsAt_request, runWorldsAt_pure, returned,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Result.prepend, List.nil_append, runWorldsAt_map, runWorldsAt_embed, List.map_map,
    Function.comp_def, Result.mapAnswer,
    Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer]

namespace Examples

def matchingRequest (n : Nat) : Request n :=
  .matching PolarizedNeedMatchedIndex.Examples.canonical.request
    (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.canonical)

def holRequest (n : Nat) : Request n :=
  .hol [] (UniformListChartNIKService.actualRequest []) Fin.elim0

def changedHOLRequest (n : Nat) : Request n :=
  .hol [] { UniformListChartNIKService.actualRequest [] with
    claim := (Mettapedia.Logic.HOL.UniformListInduction.equations,
      Mettapedia.Logic.HOL.UniformListInduction.mapLength) } Fin.elim0

@[simp] theorem matchingRequest_substitute {n m : Nat} (environment : Sub Tower.Head n m) :
    (matchingRequest n).substitute environment = matchingRequest m := rfl

@[simp] theorem holRequest_substitute {n m : Nat} (environment : Sub Tower.Head n m) :
    (holRequest n).substitute environment = holRequest m := by
  simp only [holRequest, Request.substitute]
  congr 1
  funext index
  exact Fin.elim0 index

@[simp] theorem changedHOLRequest_substitute {n m : Nat} (environment : Sub Tower.Head n m) :
    (changedHOLRequest n).substitute environment = changedHOLRequest m := by
  simp only [changedHOLRequest, Request.substitute]
  congr 1
  funext index
  exact Fin.elim0 index

def matchingValue (n : Nat) : Tower.Tm n :=
  liftClosed SharedJudgmentServices.Examples.canonicalTransport.source

def matchingType (n : Nat) : Tower.Tm n :=
  liftClosed SharedJudgmentServices.Examples.canonicalTransport.proposition

def holValue (n : Nat) : Tower.Tm n :=
  subst Fin.elim0 FormationSensitiveHOLUniformList.rawMapLength

theorem matching_returned (n : Nat) :
    (invoke common (matchingRequest n)).nativePayload? = some (matchingValue n, matchingType n) := by
  have crossing : Invocation common (matchingRequest n)
      (.matched SharedJudgmentServices.Examples.canonicalTransport.source
        SharedJudgmentServices.Examples.canonicalTransport.proposition) :=
    SharedJudgmentServices.Examples.canonical_matching_crossing.substitute
      (fun _ => (.const `Data : Tower.Tm n))
  rw [(invoke_iff _ _ _).mpr crossing]
  rfl

theorem hol_returned (n : Nat) :
    (invoke common (holRequest n)).nativePayload? =
      some (holValue n, .const `HOLUniformList.prop) := by
  have crossing : Invocation common (holRequest n)
      (.holProof (UniformListChartNIKService.actualNativeProof [])
        FormationSensitiveHOLUniformList.rawMapLength) :=
    .holSuccess (UniformListChartNIKService.actual_produced [])
      (FormationSensitiveHOLUniformList.mapLength_represented [])
  rw [(invoke_iff _ _ _).mpr crossing]
  rfl

theorem changed_hol_declined (n : Nat) :
    invoke common (changedHOLRequest n) = .declined (changedHOLRequest n) :=
  (invoke_iff _ _ _).mpr
    (.holDecline (UniformListChartNIKService.missing_induction_request_rejected []))

theorem changed_hol_no_payload (n : Nat) :
    (invoke common (changedHOLRequest n)).nativePayload? = none := by
  rw [changed_hol_declined]
  rfl

/-- Two different actual services supply the two variables used by the final
native pair. Changing either reply changes what this body receives. -/
def matchingThenHOL : Code 2 :=
  .sequence (.request (matchingRequest 2))
    (.sequence (.request (holRequest 3))
      (.native (.returnValue (.pair (.var 1) (.var 0)))))

def matchingThenChangedHOL : Code 2 :=
  .sequence (.request (matchingRequest 2))
    (.sequence (.request (changedHOLRequest 3))
      (.native (.returnValue (.pair (.var 1) (.var 0)))))

theorem matching_then_hol_worlds (state : Bool) (branch : BranchTrace) :
    Code.run common ids matchingThenHOL state branch =
      [{ world :=
           { branch := branch, answer := .value (.pair (matchingValue 2) (holValue 2))
             state := state, intents := [] }
         replies := [⟨matchingRequest 2, invoke common (matchingRequest 2)⟩,
           ⟨holRequest 2, invoke common (holRequest 2)⟩] }] := by
  rw [Code.interpret_worlds common (common_qualified .execution (by simp [specification]))]
  have first := matching_returned 2
  have second := hol_returned 2
  have requestSame := holRequest_substitute (consSub (matchingValue 2) (ids (Head := Tower.Head)))
  have secondReturned :=
    (congrArg (fun input : Request 2 => (invoke common input).nativePayload?) requestSame).trans second
  have replySame := congrArg (fun input : Request 2 =>
    (⟨input, invoke common input⟩ : Sigma (@Response 2))) requestSame
  unfold matchingThenHOL
  rw [Code.two_request_worlds common ids (matchingRequest 2) (holRequest 3)
    (.native (.returnValue (.pair (.var 1) (.var 0)))) state branch
    (by simpa only [matchingRequest_substitute] using first)
    secondReturned]
  simp only [matchingRequest_substitute, replySame,
    Code.worlds, ScopedComputation.Code.worlds, subst, consSub_zero,
    List.map_cons, List.map_nil, Result.prepend, List.append_nil]
  rfl

theorem matching_then_changed_hol_stops (state : Bool) (branch : BranchTrace) :
    Code.run common ids matchingThenChangedHOL state branch =
      [{ world :=
           { branch := branch
             answer := .stopped ⟨changedHOLRequest 2, invoke common (changedHOLRequest 2)⟩
             state := state, intents := [] }
         replies := [⟨matchingRequest 2, invoke common (matchingRequest 2)⟩,
           ⟨changedHOLRequest 2, invoke common (changedHOLRequest 2)⟩] }] := by
  rw [Code.interpret_worlds common (common_qualified .execution (by simp [specification]))]
  have requestSame := changedHOLRequest_substitute (consSub (matchingValue 2) (ids (Head := Tower.Head)))
  have secondStopped :=
    (congrArg (fun input : Request 2 => (invoke common input).nativePayload?) requestSame).trans
      (changed_hol_no_payload 2)
  have replySame := congrArg (fun input : Request 2 =>
    (⟨input, invoke common input⟩ : Sigma (@Response 2))) requestSame
  unfold matchingThenChangedHOL
  rw [Code.two_request_stopped_worlds common ids (matchingRequest 2) (changedHOLRequest 3)
    (.native (.returnValue (.pair (.var 1) (.var 0)))) state branch
    (by simpa only [matchingRequest_substitute] using matching_returned 2) secondStopped]
  simp only [matchingRequest_substitute, replySame]

/-- The failed second request contributes a stopped world, not a native
inhabitant and not an empty result collection. -/
theorem stopped_run_nonempty_without_value (state : Bool) (branch : BranchTrace) :
    Code.run common ids matchingThenChangedHOL state branch ≠ [] ∧
      ∀ output ∈ Code.run common ids matchingThenChangedHOL state branch,
        ¬ ∃ value, output.world.answer = .value value := by
  rw [matching_then_changed_hol_stops]
  simp

end Examples

#print axioms Code.substitute_comp
#print axioms Code.substitute_instantiate
#print axioms Code.interpret_substitute
#print axioms Code.interpret_worlds
#print axioms Code.two_request_worlds
#print axioms Code.two_request_stopped_worlds
#print axioms ofSource_success
#print axioms Examples.matching_then_hol_worlds
#print axioms Examples.matching_then_changed_hol_stops
#print axioms Examples.stopped_run_nonempty_without_value

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServicePrograms
