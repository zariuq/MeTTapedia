import Mettapedia.Languages.MeTTa.HE.RecursiveMachine

/-!
# Ordered correspondence for retained recursive HE control

The machine's first-order expansion and the existing recursive evaluator
are separate computations. Their meanings agree at each internal advance.
Result publication transfers one retained occurrence into the observed history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine

def expandedDenote (space : Space) (dispatch : GroundedDispatch)
    (expanded : Control × List Frame) : ResultSet :=
  expanded.2.foldl (fun results frame => frame.denote space dispatch results)
    (expanded.1.denote space dispatch)

theorem resume_denote (space : Space) (dispatch : GroundedDispatch)
    (frame : Frame) (results : ResultSet) :
    expandedDenote space dispatch (resume space frame results) = frame.denote space dispatch results := by
  cases frame with
  | invocationReturn mode original fuel live => cases mode <;> rfl
  | producerResults mode original incoming fuel live emptyReply => cases results <;> rfl
  | _ => rfl

private theorem keep_nonempty (results : ResultSet) :
    (if !results.isEmpty then results else []) = results := by
  cases results <;> rfl

theorem enter_atom_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    expandedDenote space dispatch (enter space dispatch (.atom value expected bindings fuel live)) =
      (Task.atom value expected bindings fuel live).denote space dispatch := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      by_cases empty : isEmptyOrError value = true
      · simp only [enter, Task.denote, evalAtom, empty, if_true]
        rfl
      · by_cases trivial : (expected == Atom.atomType || expected == getMetaType value ||
            getMetaType value == Atom.variableType) = true
        · simp only [enter, Task.denote, evalAtom, empty, trivial, if_true]
          rfl
        · by_cases scalar : (getMetaType value == Atom.symbolType ||
              getMetaType value == Atom.groundedType || value == Atom.unit) = true
          · simp only [enter, Task.denote, evalAtom, empty, trivial, scalar, if_true]
            rfl
          · by_cases expression : (getMetaType value == Atom.expressionType) = true
            · simp only [enter, Task.denote, evalAtom, empty, trivial, scalar, expression, if_true]
              rfl
            · simp only [enter, Task.denote, evalAtom, empty, trivial, scalar, expression]
              rfl

theorem enter_expression_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    expandedDenote space dispatch (enter space dispatch (.expression value expected bindings fuel live)) =
      (Task.expression value expected bindings fuel live).denote space dispatch := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases value with
      | symbol name => rfl
      | var name => rfl
      | grounded value => rfl
      | expression elements =>
          cases elements with
          | nil => rfl
          | cons operator arguments =>
              let value := Atom.expression (operator :: arguments)
              let types := getAtomTypes space operator
              let functions := (Task.functions value expected bindings fuel types live).denote space dispatch
              let tuples := (Task.tupleCalls value expected bindings fuel live).denote space dispatch
              cases selected : (getAtomTypes space operator).any
                  (fun type => !isFunctionType type || type == Atom.undefinedType) with
              | true =>
                  simp only [enter, rawTypeLookup, Task.denote, interpretExpression, selected, Bool.not_true,
                    Bool.false_eq_true, if_false, if_true, expandedDenote, List.foldl_cons,
                    List.foldl_nil, Frame.denote, Control.denote]
                  change functions ++ tuples = (if !(functions ++ tuples).isEmpty then functions ++ tuples else [])
                  exact (keep_nonempty (functions ++ tuples)).symm
              | false =>
                  simp only [enter, rawTypeLookup, Task.denote, interpretExpression, selected, Bool.false_eq_true,
                    if_false, Bool.not_false, if_true, expandedDenote, List.foldl_cons,
                    List.foldl_nil, Frame.denote, Control.denote, List.append_nil]
                  rfl

theorem enter_call_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    expandedDenote space dispatch (enter space dispatch (.call value expected bindings fuel live)) =
      (Task.call value expected bindings fuel live).denote space dispatch := by
  rfl

set_option maxHeartbeats 1200000 in
theorem enter_invocation_denote (space : Space) (dispatch : GroundedDispatch)
    (mode : InvocationMode) (value : Atom) (bindings : Bindings) (fuel : Nat)
    (live : List Atom) (caller : Option Atom) :
    expandedDenote space dispatch (enter space dispatch (.invocation mode value bindings fuel live caller)) =
      (Task.invocation mode value bindings fuel live caller).denote space dispatch := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      change expandedDenote space dispatch (enter space dispatch
        (.invocation mode value bindings (fuel + 1) live caller)) =
        invoke space dispatch mode value bindings (fuel + 1) live caller
      rw [invoke]
      generalize expanded : enter space dispatch (.invocation mode value bindings (fuel + 1) live caller) = entered
      simp only [enter] at expanded
      repeat' split at expanded
      all_goals subst entered
      all_goals cases mode
      all_goals simp_all [expandedDenote, Control.denote, Frame.denote,
        Task.denote, rawQueryResults, invocationFinish, List.flatMap_assoc]
      all_goals simp only [List.isEmpty_iff]
      all_goals split <;> simp_all [List.flatMap_assoc]

theorem equation_candidates_denote (space : Space) (dispatch : GroundedDispatch)
    (original rhs expected : Atom) (fuel : Nat) (live : List Atom) (alternatives : List Bindings) :
    ((alternatives.filterMap fun merged =>
      if merged.hasLoop then none else some (merged.applyFull rhs fuel, merged)).flatMap
        fun (value, bindings) => ordinaryCallReturn original value bindings
          (fun value bindings => evalAtom space dispatch value expected bindings fuel live)) =
      alternatives.flatMap (fun merged =>
        if merged.hasLoop then []
        else ordinaryCallReturn original (merged.applyFull rhs fuel) merged
          (fun value bindings => evalAtom space dispatch value expected bindings fuel live)) := by
  induction alternatives with
  | nil => rfl
  | cons bindings remaining ih =>
      cases loop : bindings.hasLoop <;> simp [loop, ih]

set_option maxHeartbeats 1200000 in
theorem enter_denote (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    expandedDenote space dispatch (enter space dispatch task) = task.denote space dispatch := by
  cases task with
  | atom value expected bindings fuel live =>
      exact enter_atom_denote space dispatch value expected bindings fuel live
  | expression value expected bindings fuel live =>
      exact enter_expression_denote space dispatch value expected bindings fuel live
  | func value operatorType bindings fuel live =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases value with
          | symbol name => rfl
          | var name => rfl
          | grounded value => rfl
          | expression elements => cases elements <;> rfl
  | args values types bindings fuel live =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases values <;> cases types <;> rfl
  | tuple value bindings fuel live =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases value with
          | symbol name => rfl
          | var name => rfl
          | grounded value => rfl
          | expression elements =>
              cases elements with
              | nil => rfl
              | cons head rest => cases rest <;> rfl
  | call value expected bindings fuel live =>
      exact enter_call_denote space dispatch value expected bindings fuel live
  | functions value expected bindings fuel types live =>
      cases types with
      | nil => rfl
      | cons operatorType remaining =>
          simp only [enter]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | bindingAlternatives value operatorType expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | heads operatorType arguments fuel alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons head remaining =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | argumentHeads original remaining types fuel alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | tupleHeads tail fuel alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | calls expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | atoms expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | returned original value expected bindings fuel live =>
      simp only [enter]
      repeat' split
      all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote, ordinaryCallReturn]
  | returns original expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | equations original expected incoming fuel alternatives live =>
      cases alternatives <;> rfl
  | grounded original expected incoming fuel alternatives live =>
      cases alternatives <;> rfl
  | tupleCalls value expected bindings fuel live => rfl
  | invocation mode value bindings fuel live caller =>
      exact enter_invocation_denote space dispatch mode value bindings fuel live caller
  | produced value bindings fuel live caller provenance =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [enter, Task.denote, invocationResult]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | productions fuel alternatives live caller provenance =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | minimal value bindings fuel live caller =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [enter, Task.denote, minimalRun]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | minimals fuel alternatives live caller =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | primitive value bindings fuel live caller =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [enter, Task.denote, minimalStep]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
          all_goals
            exfalso
            rename_i impossible same
            exact impossible _ _ _ _ same.symm
  | chainRows name template fuel alternatives => cases alternatives <;> rfl
  | functionBody value bindings fuel live caller => cases fuel <;> rfl
  | bodyResults fuel alternatives live caller =>
      cases alternatives with
      | nil => rfl
      | cons pair remaining =>
          rcases pair with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | producerResults mode original incoming fuel live emptyReply results =>
      cases results <;> rfl
  | completed value expected bindings fuel => rfl

end Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness

namespace Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual

open Spec.Eval
open Spec.Eval.Completed (Policy Result)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

/-- Every actual local control step reconstructs an independent source
completion. Pending continuations retain their exact contextual results. -/
theorem local_source_back
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {lookup : Completed.CastLookup} {policy : Policy}
    {before after : Control × List Continuation} {current pending : List Result}
    (advanced : LocalStep space dispatch lookup policy before after)
    (controlled : after.1.SourceRel space dispatch lookup policy current)
    (continued : StackRel space dispatch lookup policy after.2 current pending) :
    ∃ initial, before.1.SourceRel space dispatch lookup policy initial ∧
      StackRel space dispatch lookup policy before.2 initial pending := by
  induction advanced generalizing current pending with
  | delivered entered =>
      cases controlled
      exact ⟨_,.work (.delivered entered),continued⟩
  | cast entered casted transported =>
      cases controlled
      exact ⟨_,.work (.cast entered casted transported),continued⟩
  | atomTuple entered shaped untyped =>
      cases controlled with
      | work tuple =>
          cases continued with
          | cons called remaining =>
              cases called with
              | calls calls =>
                  cases remaining with
                  | cons published rest =>
                      cases published with
                      | publish priority =>
                          exact ⟨_,.work (.tuple entered shaped untyped tuple calls priority),rest⟩
  | atomFunction entered shaped selected =>
      cases controlled with
      | work invoked =>
          cases continued with
          | cons published rest =>
              cases published with
              | publish priority => exact ⟨_,.work (.function entered shaped selected invoked priority),rest⟩
  | atomFallback entered shaped selected =>
      cases controlled with
      | work tuple =>
          cases continued with
          | cons called remaining =>
              cases called with
              | calls calls =>
                  cases remaining with
                  | cons diagnosed remaining =>
                      cases diagnosed
                      cases remaining with
                      | cons published rest =>
                          cases published with
                          | publish priority => exact ⟨_,.work (.fallback entered shaped selected tuple calls priority),rest⟩
  | atomSelectionFailed entered shaped selected =>
      cases controlled
      cases continued with
      | cons published rest =>
          cases published with
          | publish priority => exact ⟨_,.work (.selectionFailed entered shaped selected priority),rest⟩
  | tupleNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | tupleSingleton =>
      cases controlled with
      | work child =>
          cases continued with
          | cons singleton rest =>
              cases singleton
              exact ⟨_,.work (.singleton child),rest⟩
  | tupleCons =>
      cases controlled with
      | work head =>
          cases continued with
          | cons branches rest =>
              cases branches with
              | branches tail => exact ⟨_,.work (.cons head tail),rest⟩
  | branchesNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | branchesStopped stopped =>
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,.work (.stopped stopped tail),rest⟩
  | branchesContinue running =>
      cases controlled with
      | work child =>
          cases continued with
          | cons tupleTail remaining =>
              cases tupleTail
              cases remaining with
              | cons appended rest =>
                  cases appended with
                  | append tail => exact ⟨_,.work (.continuing running child tail),rest⟩
  | argumentsNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | argumentsCons =>
      cases controlled with
      | work head =>
          cases continued with
          | cons arguments rest =>
              cases arguments with
              | arguments tail => exact ⟨_,.work (.cons head tail),rest⟩
  | argumentBranchesNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | argumentBranchesStopped stopped =>
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,.work (.stopped stopped tail),rest⟩
  | argumentBranchesContinue running =>
      cases controlled with
      | work child =>
          cases continued with
          | cons argumentTail remaining =>
              cases argumentTail
              cases remaining with
              | cons appended rest =>
                  cases appended with
                  | append tail => exact ⟨_,.work (.continuing running child tail),rest⟩
  | functionStart arity =>
      cases controlled with
      | work head =>
          cases continued with
          | cons branched rest =>
              cases branched with
              | functionHeads branches => exact ⟨_,.work (.evaluated arity head branches),rest⟩
  | functionBranchesNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | functionBranchesStopped stopped =>
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,.work (.stopped stopped tail),rest⟩
  | functionBranchesContinue running =>
      cases controlled with
      | work child =>
          cases continued with
          | cons assembled remaining =>
              cases assembled
              cases remaining with
              | cons appended rest =>
                  cases appended with
                  | append tail => exact ⟨_,.work (.continuing running child tail),rest⟩
  | invocationsNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | invocationsCons =>
      cases controlled with
      | work interpreted =>
          cases continued with
          | cons called remaining =>
              cases called with
              | calls calls =>
                  cases remaining with
                  | cons appended rest =>
                      cases appended with
                      | append tail => exact ⟨_,.work (.cons interpreted calls tail),rest⟩
  | callsNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | callsCons =>
      cases controlled with
      | work child =>
          cases continued with
          | cons appended rest =>
              cases appended with
              | append tail => exact ⟨_,.work (.cons child tail),rest⟩
  | callError failed =>
      cases controlled
      exact ⟨_,.work (.error failed),continued⟩
  | callEmbedded clean ordinary entered =>
      cases controlled with
      | work child =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch returned => exact ⟨_,.work (.embedded clean ordinary entered child returned),rest⟩
  | callAbsent clean ordinary frontier =>
      cases controlled
      exact ⟨_,.work (.absent clean ordinary frontier),continued⟩
  | callEquations clean ordinary frontier nonempty =>
      cases controlled with
      | work bodies => exact ⟨_,.work (.equations clean ordinary frontier nonempty bodies),continued⟩
  | equationsNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | equationsCons reached unified =>
      cases controlled with
      | work child =>
          cases continued with
          | cons followed remaining =>
              cases followed with
              | boundaryBatch returned =>
                  cases remaining with
                  | cons appended rest =>
                      cases appended with
                      | append tail => exact ⟨_,.work (.cons reached unified child returned tail),rest⟩
  | returnRefused refused =>
      cases controlled
      exact ⟨_,.work (.notReducible refused),continued⟩
  | returnStopped stopped =>
      cases controlled
      exact ⟨_,.work (.stopped stopped),continued⟩
  | returnEvaluate accepted running =>
      cases controlled with
      | work child => exact ⟨_,.work (.evaluate accepted running child),continued⟩
  | minimalData terminal =>
      cases controlled
      exact ⟨_,.work (.data terminal),continued⟩
  | minimalEval =>
      cases controlled with
      | work child => exact ⟨_,.work (.eval child),continued⟩
  | minimalEvalc services =>
      cases controlled with
      | context child saved =>
          cases child with
          | work child =>
              cases saved
              exact ⟨_,.work (.evalc services child),continued⟩
  | minimalChain =>
      cases controlled with
      | work child =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch batch => exact ⟨_,.work (.chain child batch),rest⟩
  | minimalUnifyYes selected unified =>
      cases controlled
      exact ⟨_,.work (.unifyYes selected unified),continued⟩
  | minimalUnifyNo missing =>
      cases controlled
      exact ⟨_,.work (.unifyNo missing),continued⟩
  | minimalUnifyBadArity malformed =>
      cases controlled
      exact ⟨_,.work (.unifyBadArity malformed),continued⟩
  | minimalConsAtom =>
      cases controlled
      exact ⟨_,.work .consAtom,continued⟩
  | minimalDeconsAtom =>
      cases controlled
      exact ⟨_,.work .deconsAtom,continued⟩
  | minimalFunction shaped =>
      cases controlled with
      | work body =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch batch => exact ⟨_,.work (.function shaped body batch),rest⟩
  | minimalMetta services =>
      cases controlled with
      | context child saved =>
          cases child with
          | work child =>
              cases saved
              exact ⟨_,.work (.metta services child),continued⟩
  | minimalContextSpace services =>
      cases controlled
      exact ⟨_,.work (.contextSpace services),continued⟩
  | bodyStart =>
      cases controlled with
      | work child =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch batch => exact ⟨_,.work (.run child batch),rest⟩
  | invocationEmbedded ordinary entered =>
      cases controlled with
      | work child => exact ⟨_,.work (.embedded ordinary entered child),continued⟩
  | invocationAbsent ordinary frontier =>
      cases controlled
      exact ⟨_,.work (.absent ordinary frontier),continued⟩
  | invocationEquations ordinary frontier nonempty =>
      cases controlled with
      | work children => exact ⟨_,.work (.equations ordinary frontier nonempty children),continued⟩
  | invocationEquationsNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | invocationEquationsCons reached unified =>
      cases controlled with
      | work child =>
          cases continued with
          | cons appended rest =>
              cases appended with
              | append tail => exact ⟨_,.work (.cons reached unified child tail),rest⟩
  | boundaryChain =>
      cases controlled with
      | work child => exact ⟨_,.work (.chain child),continued⟩
  | boundaryBodyTerminal terminal =>
      cases controlled
      exact ⟨_,.work (.bodyTerminal terminal),continued⟩
  | boundaryBodyResume entered =>
      cases controlled with
      | work child => exact ⟨_,.work (.bodyResume entered child),continued⟩
  | boundaryFunctionReturn =>
      cases controlled
      exact ⟨_,.work .functionReturn,continued⟩
  | boundaryFunctionNoReturn noReturn =>
      cases controlled
      exact ⟨_,.work (.functionNoReturn noReturn),continued⟩
  | boundaryProducerRaw ordinary =>
      cases controlled
      exact ⟨_,.work (.producerRaw ordinary),continued⟩
  | boundaryProducerFunction activeFunction =>
      cases controlled with
      | work child => exact ⟨_,.work (.producerFunction activeFunction child),continued⟩
  | boundaryReturned =>
      cases controlled with
      | work child => exact ⟨_,.work (.returned child),continued⟩
  | boundaryBatchNil =>
      cases controlled
      exact ⟨_,.work .nil,continued⟩
  | boundaryBatchCons =>
      cases controlled with
      | work child =>
          cases continued with
          | cons appended rest =>
              cases appended with
              | append tail => exact ⟨_,.work (.cons child tail),rest⟩
  | boundaryNativeEmittedRaw =>
      cases controlled with
      | work child => exact ⟨_,.work (.nativeEmittedRaw child),continued⟩
  | boundaryNativeEmittedReturn =>
      cases controlled with
      | work child =>
          cases continued with
          | cons returned rest =>
              cases returned with
              | boundaryBatch batch => exact ⟨_,.work (.nativeEmittedReturn child batch),rest⟩
  | boundaryNativeCompletedRaw =>
      cases controlled
      exact ⟨_,.work .nativeCompletedRaw,continued⟩
  | boundaryNativeCompletedReturn returned =>
      cases controlled
      exact ⟨_,.work (.nativeCompletedReturn returned),continued⟩
  | publish priority =>
      cases controlled
      exact ⟨_,.returning _,.cons (.publish priority) continued⟩
  | singleton =>
      cases controlled
      exact ⟨_,.returning _,.cons (.singleton _) continued⟩
  | branches =>
      cases controlled with
      | work tail => exact ⟨_,.returning _,.cons (.branches tail) continued⟩
  | tupleTail =>
      cases controlled
      exact ⟨_,.returning _,.cons (.tupleTail _ _) continued⟩
  | arguments =>
      cases controlled with
      | work tail => exact ⟨_,.returning _,.cons (.arguments tail) continued⟩
  | argumentTail =>
      cases controlled
      exact ⟨_,.returning _,.cons (.argumentTail _ _) continued⟩
  | functionHeads =>
      cases controlled with
      | work branches => exact ⟨_,.returning _,.cons (.functionHeads branches) continued⟩
  | functionAssemble =>
      cases controlled
      exact ⟨_,.returning _,.cons (.functionAssemble _ _) continued⟩
  | diagnostics =>
      cases controlled
      exact ⟨_,.returning _,.cons (.diagnostics _ _ _) continued⟩
  | boundaryBatch =>
      cases controlled with
      | work batch => exact ⟨_,.returning _,.cons (.boundaryBatch batch) continued⟩
  | calls =>
      cases controlled with
      | work calls => exact ⟨_,.returning _,.cons (.calls calls) continued⟩
  | append =>
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,.returning _,.cons (.append tail) rest⟩
  | prepend =>
      cases controlled
      exact ⟨_,.returning _,.cons (.prepend _ _) continued⟩
  | contextStep _ ih =>
      cases controlled with
      | context child inner =>
          obtain ⟨initial,earlier,saved⟩ := ih child inner
          exact ⟨_,.context earlier saved,continued⟩
  | contextReturn =>
      cases controlled
      exact ⟨_,.context (.returning _) (.nil _),continued⟩

theorem step_source_back
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    {before after : Configuration} {answers : List Result}
    (advanced : Step dispatch lookup policy before after)
    (source : after.SourceRel dispatch lookup policy answers) :
    before.SourceRel dispatch lookup policy answers := by
  obtain ⟨current,pending,controlled,continued,same⟩ := source
  cases advanced with
  | internal advance =>
      obtain ⟨initial,earlier,saved⟩ := local_source_back advance controlled continued
      exact ⟨initial,pending,earlier,saved,same⟩
  | publish =>
      cases controlled
      cases continued
      refine ⟨_,_,.returning _,.nil _,?_⟩
      simpa only [List.append_assoc,List.singleton_append] using same

theorem steps_source_back
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    {before after : Configuration} {answers : List Result}
    (path : Steps dispatch lookup policy before after)
    (source : after.SourceRel dispatch lookup policy answers) :
    before.SourceRel dispatch lookup policy answers := by
  revert source
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun source => source
  | head first _ ih => exact fun source => step_source_back first (ih source)

theorem initial_source_iff
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) (task : Task) (answers : List Result) :
    (Configuration.initial space task).SourceRel dispatch lookup policy answers ↔
      task.SourceRel space dispatch lookup policy answers := by
  constructor
  · rintro ⟨current,pending,controlled,continued,same⟩
    cases controlled with
    | work source =>
        cases continued
        simp only [Configuration.initial,List.nil_append] at same
        cases same
        exact source
  · intro source
    exact ⟨answers,answers,.work source,.nil _,rfl⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.Stateful

open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldEnvironment)
open RecursiveTasks.Contextual RecursiveMachine.Contextual

variable {Context World : Type} {environment : WorldEnvironment Context World} {policy : Policy}

/-- Ordinary transitions read the reached world's space. Their completed
source reconstruction retains the worlds of every saved child. -/
private theorem core_source_back
    {label : Context} {world childWorld finalWorld : World}
    {before after : Control Context} {flatBefore flatAfter : Control}
    {stack remaining : List Continuation} {current pending : List Result}
    (advanced : LocalStep (admission := environment.arguments) (environment.view world label) environment.dispatch environment.lookup policy
      (flatBefore,stack) (flatAfter,remaining))
    (first : UnscopedControl before flatBefore) (managed : managedContextControl before = false)
    (last : UnscopedControl after flatAfter)
    (controlled : after.WorldSourceRel environment policy label world current childWorld)
    (continued : WorldStackRel environment policy label childWorld remaining current pending finalWorld) :
    ∃ initial initialWorld, before.WorldSourceRel environment policy label world initial initialWorld ∧
      WorldStackRel environment policy label initialWorld stack initial pending finalWorld := by
  cases advanced with
  | delivered entered =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.delivered entered),continued⟩
  | cast entered casted transported =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.cast entered casted transported),continued⟩
  | atomTuple entered shaped untyped =>
      cases first
      cases last
      cases controlled with
      | work tuple =>
          cases continued with
          | cons called remaining =>
              cases called with
              | calls calls =>
                  cases remaining with
                  | cons published rest =>
                      cases published with
                      | publish priority =>
                          exact ⟨_,_,.work (.tuple entered shaped untyped tuple calls priority),rest⟩
  | atomFunction entered shaped selected =>
      cases first
      cases last
      cases controlled with
      | work invoked =>
          cases continued with
          | cons published rest =>
              cases published with
              | publish priority => exact ⟨_,_,.work (.function entered shaped selected invoked priority),rest⟩
  | atomFallback entered shaped selected =>
      cases first
      cases last
      cases controlled with
      | work tuple =>
          cases continued with
          | cons called remaining =>
              cases called with
              | calls calls =>
                  cases remaining with
                  | cons diagnosed remaining =>
                      cases diagnosed
                      cases remaining with
                      | cons published rest =>
                          cases published with
                          | publish priority => exact ⟨_,_,.work (.fallback entered shaped selected tuple calls priority),rest⟩
  | atomSelectionFailed entered shaped selected =>
      cases first
      cases last
      cases controlled
      cases continued with
      | cons published rest =>
          cases published with
          | publish priority => exact ⟨_,_,.work (.selectionFailed entered shaped selected priority),rest⟩
  | tupleNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | tupleSingleton =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons singleton rest =>
              cases singleton
              exact ⟨_,_,.work (.singleton child),rest⟩
  | tupleCons =>
      cases first
      cases last
      cases controlled with
      | work head =>
          cases continued with
          | cons branches rest =>
              cases branches with
              | branches tail => exact ⟨_,_,.work (.cons head tail),rest⟩
  | branchesNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | branchesStopped stopped =>
      cases first
      cases last
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,_,.work (.stopped stopped tail),rest⟩
  | branchesContinue running =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons tupleTail remaining =>
              cases tupleTail
              cases remaining with
              | cons appended rest =>
                  cases appended with
                  | append tail => exact ⟨_,_,.work (.continuing running child tail),rest⟩
  | argumentsNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | argumentsCons =>
      cases first
      cases last
      cases controlled with
      | work head =>
          cases continued with
          | cons arguments rest =>
              cases arguments with
              | arguments tail => exact ⟨_,_,.work (.cons head tail),rest⟩
  | argumentBranchesNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | argumentBranchesStopped stopped =>
      cases first
      cases last
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,_,.work (.stopped stopped tail),rest⟩
  | argumentBranchesContinue running =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons argumentTail remaining =>
              cases argumentTail
              cases remaining with
              | cons appended rest =>
                  cases appended with
                  | append tail => exact ⟨_,_,.work (.continuing running child tail),rest⟩
  | functionStart arity =>
      cases first
      cases last
      cases controlled with
      | work head =>
          cases continued with
          | cons branched rest =>
              cases branched with
              | functionHeads branches => exact ⟨_,_,.work (.evaluated arity head branches),rest⟩
  | functionBranchesNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | functionBranchesStopped stopped =>
      cases first
      cases last
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,_,.work (.stopped stopped tail),rest⟩
  | functionBranchesContinue running =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons assembled remaining =>
              cases assembled
              cases remaining with
              | cons appended rest =>
                  cases appended with
                  | append tail => exact ⟨_,_,.work (.continuing running child tail),rest⟩
  | invocationsNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | invocationsCons =>
      cases first
      cases last
      cases controlled with
      | work interpreted =>
          cases continued with
          | cons called remaining =>
              cases called with
              | calls calls =>
                  cases remaining with
                  | cons appended rest =>
                      cases appended with
                      | append tail => exact ⟨_,_,.work (.cons interpreted calls tail),rest⟩
  | callsNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | callsCons =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons appended rest =>
              cases appended with
              | append tail => exact ⟨_,_,.work (.cons child tail),rest⟩
  | callError failed =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.error failed),continued⟩
  | callEmbedded clean ordinary entered =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch returned => exact ⟨_,_,.work (.embedded clean ordinary entered child returned),rest⟩
  | callAbsent clean ordinary frontier =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.absent clean ordinary frontier),continued⟩
  | callEquations clean ordinary frontier nonempty =>
      cases first
      cases last
      cases controlled with
      | work bodies => exact ⟨_,_,.work (.equations clean ordinary frontier nonempty bodies),continued⟩
  | equationsNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | equationsCons reached unified =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons followed remaining =>
              cases followed with
              | boundaryBatch returned =>
                  cases remaining with
                  | cons appended rest =>
                      cases appended with
                      | append tail => exact ⟨_,_,.work (.cons reached unified child returned tail),rest⟩
  | returnRefused refused =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.notReducible refused),continued⟩
  | returnStopped stopped =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.stopped stopped),continued⟩
  | returnEvaluate accepted running =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.evaluate accepted running child),continued⟩
  | minimalData terminal =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.data terminal),continued⟩
  | minimalEval =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.eval child),continued⟩
  | minimalEvalc => cases last
  | minimalChain =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch batch => exact ⟨_,_,.work (.chain child batch),rest⟩
  | minimalUnifyYes selected unified =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.unifyYes selected unified),continued⟩
  | minimalUnifyNo missing =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.unifyNo missing),continued⟩
  | minimalUnifyBadArity malformed =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.unifyBadArity malformed),continued⟩
  | minimalConsAtom =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .consAtom,continued⟩
  | minimalDeconsAtom =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .deconsAtom,continued⟩
  | minimalFunction shaped =>
      cases first
      cases last
      cases controlled with
      | work body =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch batch => exact ⟨_,_,.work (.function shaped body batch),rest⟩
  | minimalMetta => cases last
  | minimalContextSpace =>
      cases first
      simp [managedContextControl] at managed
  | bodyStart =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons followed rest =>
              cases followed with
              | boundaryBatch batch => exact ⟨_,_,.work (.run child batch),rest⟩
  | invocationEmbedded ordinary entered =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.embedded ordinary entered child),continued⟩
  | invocationAbsent ordinary frontier =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.absent ordinary frontier),continued⟩
  | invocationEquations ordinary frontier nonempty =>
      cases first
      cases last
      cases controlled with
      | work children => exact ⟨_,_,.work (.equations ordinary frontier nonempty children),continued⟩
  | invocationEquationsNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | invocationEquationsCons reached unified =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons appended rest =>
              cases appended with
              | append tail => exact ⟨_,_,.work (.cons reached unified child tail),rest⟩
  | boundaryChain =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.chain child),continued⟩
  | boundaryBodyTerminal terminal =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.bodyTerminal terminal),continued⟩
  | boundaryBodyResume entered =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.bodyResume entered child),continued⟩
  | boundaryFunctionReturn =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .functionReturn,continued⟩
  | boundaryFunctionNoReturn noReturn =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.functionNoReturn noReturn),continued⟩
  | boundaryProducerRaw ordinary =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.producerRaw ordinary),continued⟩
  | boundaryProducerFunction activeFunction =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.producerFunction activeFunction child),continued⟩
  | boundaryReturned =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.returned child),continued⟩
  | boundaryBatchNil =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nil,continued⟩
  | boundaryBatchCons =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons appended rest =>
              cases appended with
              | append tail => exact ⟨_,_,.work (.cons child tail),rest⟩
  | boundaryNativeEmittedRaw =>
      cases first
      cases last
      cases controlled with
      | work child => exact ⟨_,_,.work (.nativeEmittedRaw child),continued⟩
  | boundaryNativeEmittedReturn =>
      cases first
      cases last
      cases controlled with
      | work child =>
          cases continued with
          | cons returned rest =>
              cases returned with
              | boundaryBatch batch => exact ⟨_,_,.work (.nativeEmittedReturn child batch),rest⟩
  | boundaryNativeCompletedRaw =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work .nativeCompletedRaw,continued⟩
  | boundaryNativeCompletedReturn returned =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.work (.nativeCompletedReturn returned),continued⟩
  | publish priority =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.returning _,.cons (.publish priority) continued⟩
  | singleton =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.returning _,.cons (.singleton _) continued⟩
  | branches =>
      cases first
      cases last
      cases controlled with
      | work tail => exact ⟨_,_,.returning _,.cons (.branches tail) continued⟩
  | tupleTail =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.returning _,.cons (.tupleTail _ _) continued⟩
  | arguments =>
      cases first
      cases last
      cases controlled with
      | work tail => exact ⟨_,_,.returning _,.cons (.arguments tail) continued⟩
  | argumentTail =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.returning _,.cons (.argumentTail _ _) continued⟩
  | functionHeads =>
      cases first
      cases last
      cases controlled with
      | work branches => exact ⟨_,_,.returning _,.cons (.functionHeads branches) continued⟩
  | functionAssemble =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.returning _,.cons (.functionAssemble _ _) continued⟩
  | diagnostics =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.returning _,.cons (.diagnostics _ _ _) continued⟩
  | boundaryBatch =>
      cases first
      cases last
      cases controlled with
      | work batch => exact ⟨_,_,.returning _,.cons (.boundaryBatch batch) continued⟩
  | calls =>
      cases first
      cases last
      cases controlled with
      | work calls => exact ⟨_,_,.returning _,.cons (.calls calls) continued⟩
  | append =>
      cases first
      cases last
      cases controlled with
      | work tail =>
          cases continued with
          | cons prepended rest =>
              cases prepended
              exact ⟨_,_,.returning _,.cons (.append tail) rest⟩
  | prepend =>
      cases first
      cases last
      cases controlled
      exact ⟨_,_,.returning _,.cons (.prepend _ _) continued⟩
  | contextStep => cases first
  | contextReturn => cases first

/-- Every local world transition reconstructs a source completion. A native
reply changes the world once; nested contexts return that actual world. -/
theorem local_source_back
    {label : Context} {world afterWorld childWorld finalWorld : World}
    {before after : Control Context × List Continuation} {current pending : List Result}
    (advanced : WorldLocalStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      world label before afterWorld after)
    (controlled : after.1.WorldSourceRel environment policy label afterWorld current childWorld)
    (continued : WorldStackRel environment policy label childWorld after.2 current pending finalWorld) :
    ∃ initial initialWorld, before.1.WorldSourceRel environment policy label world initial initialWorld ∧
      WorldStackRel environment policy label initialWorld before.2 initial pending finalWorld := by
  induction advanced generalizing current pending childWorld finalWorld with
  | core first managed primitive last => exact core_source_back primitive first managed last controlled continued
  | context _ ih =>
      cases controlled with
      | context child inner =>
          obtain ⟨initial,initialWorld,earlier,saved⟩ := ih child inner
          exact ⟨_,_,.context earlier saved,continued⟩
  | contextReturn =>
      cases controlled
      exact ⟨_,_,.context (.returning _) (.nil _),continued⟩
  | evalc =>
      cases controlled with
      | context child saved =>
          cases child with
          | work child =>
              cases saved
              exact ⟨_,_,.work (.evalc child),continued⟩
  | metta =>
      cases controlled with
      | context child saved =>
          cases child with
          | work child =>
              cases saved
              exact ⟨_,_,.work (.metta child),continued⟩
  | contextSpace =>
      cases controlled
      exact ⟨_,_,.work .contextSpace,continued⟩
  | native called =>
      cases controlled
      exact ⟨_,_,.work (.native called),continued⟩
  | callGroundedDone shaped executable nonerror produced outcome =>
      cases controlled
      exact ⟨_,_,.work (.groundedDone shaped executable nonerror produced outcome),continued⟩
  | callGroundedResume shaped executable nonerror produced outcome =>
      cases controlled with
      | work batch => exact ⟨_,_,.work (.groundedResume shaped executable nonerror produced outcome batch),continued⟩
  | invocationGroundedDone shaped executable produced outcome =>
      cases controlled
      exact ⟨_,_,.work (.groundedDone shaped executable produced outcome),continued⟩
  | invocationGroundedResume shaped executable produced outcome =>
      cases controlled with
      | work batch => exact ⟨_,_,.work (.groundedResume shaped executable produced outcome batch),continued⟩
  | collapseEnter provided =>
      cases controlled with
      | work child =>
          cases continued with
          | cons collected rest =>
              cases collected with
              | collect installed captured => exact ⟨_,_,.work (.collapseBind installed child captured),rest⟩
  | collectEnter provided =>
      cases controlled with
      | work source =>
          obtain ⟨snapshots,packed,installed,captured,same⟩ := source
          cases same
          exact ⟨_,_,.returning _,.cons (.collect installed captured) continued⟩
  | captureNil provided =>
      cases controlled
      exact ⟨_,_,.work ⟨_,_,provided,.nil,rfl⟩,continued⟩
  | captureEmpty provided missing =>
      cases controlled with
      | work source =>
          obtain ⟨snapshots,packed,installed,captured,same⟩ := source
          have agreement := Option.some.inj (provided.symm.trans installed)
          cases agreement
          exact ⟨_,_,.work ⟨_,packed,provided,.empty missing captured,same⟩,continued⟩
  | captureOne provided present stored =>
      cases controlled with
      | work source =>
          obtain ⟨snapshots,packed,installed,captured,same⟩ := source
          have agreement := Option.some.inj (provided.symm.trans installed)
          cases agreement
          exact ⟨_,_,.work ⟨_,packed,provided,.cons present stored captured,same⟩,continued⟩
  | superposeEnter provided =>
      cases controlled with
      | work source =>
          obtain ⟨snapshots,installed,reached,restored⟩ := source
          cases reached
          exact ⟨_,_,.work (.superposeBind installed restored),continued⟩
  | restoreNil provided =>
      cases controlled
      exact ⟨_,_,.work ⟨_,provided,rfl,.nil⟩,continued⟩
  | restoreOne provided loaded merged =>
      cases controlled with
      | work source =>
          obtain ⟨snapshots,installed,reached,restored⟩ := source
          cases reached
          have agreement := Option.some.inj (provided.symm.trans installed)
          cases agreement
          exact ⟨_,_,.work ⟨_,provided,rfl,.cons loaded merged restored⟩,continued⟩
  | restoreRejected provided loaded impossible =>
      cases controlled with
      | work source =>
          obtain ⟨snapshots,installed,reached,restored⟩ := source
          cases reached
          have agreement := Option.some.inj (provided.symm.trans installed)
          cases agreement
          exact ⟨_,_,.work ⟨_,provided,rfl,.rejected loaded impossible restored⟩,continued⟩

theorem step_source_back
    {before after : WorldConfiguration Context World} {answers : List Result} {finalWorld : World}
    (advanced : WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy before after)
    (source : after.SourceRel environment policy answers finalWorld) :
    before.SourceRel environment policy answers finalWorld := by
  obtain ⟨current,pending,childWorld,controlled,continued,same⟩ := source
  cases advanced with
  | internal advance =>
      obtain ⟨initial,initialWorld,earlier,saved⟩ := local_source_back advance controlled continued
      exact ⟨initial,pending,initialWorld,earlier,saved,same⟩
  | publish =>
      cases controlled
      cases continued
      refine ⟨_,_,_,.returning _,.nil _,?_⟩
      simpa only [List.append_assoc,List.singleton_append] using same

theorem steps_source_back
    {before after : WorldConfiguration Context World} {answers : List Result} {finalWorld : World}
    (path : WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy before after)
    (source : after.SourceRel environment policy answers finalWorld) :
    before.SourceRel environment policy answers finalWorld := by
  revert source
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun source => source
  | head first _ ih => exact fun source => step_source_back first (ih source)

end Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.Stateful
