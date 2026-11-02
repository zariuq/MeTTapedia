import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBaseControlStep
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnEntryInstances
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClauseDispatch

/-! Successful independent return transitions enable actual prepared base
steps. Caller continuations, captures, clause order and administrative
application/build requests are retained in their source control points.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

private theorem return_success {program : OCaml.Program} {actual : OCaml.Value} {rest : OCaml.Continuation}
    {next : OCaml.MachineState} (step : OCaml.machineStep program (.returned actual rest) = .ok (some next)) :
    OCaml.returnValue program actual rest = .ok next := by
  cases answer : OCaml.returnValue program actual rest <;> simp_all [OCaml.machineStep, Except.map]

theorem prepared_frame_can_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (actual : OCaml.Value) (frame : OCaml.Frame) (rest : OCaml.Continuation)
    (encodedRest encodedFrame : Pattern) (next : OCaml.MachineState)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (framed : frame? (patterns program) frame encodedRest = some encodedFrame)
    (sourceStep : OCaml.machineStep program (.returned actual (frame :: rest)) = .ok (some next)) :
    ∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value actual, encodedFrame]) target := by
  have point : ControlPoint program (.returned actual (frame :: rest)) (node "MlReturn" [value actual, encodedFrame]) 0 :=
    .state (by simp only [state?, continuation?, resolved, framed, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
  have success := return_success sourceStep
  cases frame with
  | argument function captured =>
    have same : encodedFrame = node "MlKArgument" [code function, environment captured, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have targetPoint : ControlPoint program (.evaluate function captured (.function actual :: rest))
        (node "MlEvaluate" [code function, environment captured, node "MlKFunction" [value actual, encodedRest]]) 0 :=
      .state (by simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
    exact ⟨_, prepared_base_control_step program prepared table 1 (by decide +kernel) built signatures point targetPoint
      (return_argument_instance _ _ _ _)⟩
  | function argument =>
    have same : encodedFrame = node "MlKFunction" [value argument, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have targetPoint : ControlPoint program next (node "MlApply" [value actual, value argument, encodedRest]) 2 :=
      .application resolved success
    exact ⟨_, prepared_base_control_step program prepared table 2 (by decide +kernel) built signatures point targetPoint
      (return_function_instance _ _ _)⟩
  | letValue parameter body captured =>
    cases referenced : patternReference? (patterns program) parameter with
    | none => simp [frame?, referenced] at framed
    | some patternCode =>
      have same : encodedFrame = node "MlKLet" [patternCode, code body, environment captured, encodedRest] := by
        simpa only [frame?, referenced, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] using framed.symm
      subst encodedFrame
      have raw := referenced
      unfold patternReference? at raw
      obtain ⟨index, found, codeSame⟩ := Option.map_eq_some_iff.mp raw
      subst patternCode
      have targetPoint : ControlPoint program (OCaml.enterBody parameter actual body captured rest)
          (node "MlMatchOne" [patternId index, value actual, code body, environment captured, encodedRest]) 1 :=
        .matchOne (OCaml.patternIndex?_sound parameter (patterns program) index found) resolved
      exact ⟨_, prepared_base_control_step program prepared table 3 (by decide +kernel) built signatures point targetPoint
        (return_let_instance _ _ _ _ _)⟩
  | consTail head captured =>
    have same : encodedFrame = node "MlKConsTail" [code head, environment captured, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have targetPoint : ControlPoint program (.evaluate head captured (.consHead actual :: rest))
        (node "MlEvaluate" [code head, environment captured, node "MlKConsHead" [value actual, encodedRest]]) 0 :=
      .state (by simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
    exact ⟨_, prepared_base_control_step program prepared table 12 (by decide +kernel) built signatures point targetPoint
      (return_cons_tail_instance _ _ _ _)⟩
  | consHead tail =>
    have same : encodedFrame = node "MlKConsHead" [value tail, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have targetPoint : ControlPoint program (.returned (.cons actual tail) rest)
        (node "MlReturn" [value (.cons actual tail), encodedRest]) 0 :=
      .state (by simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
    exact ⟨_, prepared_base_control_step program prepared table 13 (by decide +kernel) built signatures point targetPoint
      (return_cons_head_instance _ _ _)⟩
  | matchValue clauses captured =>
    cases listed : clauseList? (patterns program) clauses with
    | none => simp [frame?, listed] at framed
    | some encodedClauses =>
      have same : encodedFrame = node "MlKMatch" [encodedClauses, environment captured, encodedRest] := by
        simpa only [frame?, listed, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] using framed.symm
      subst encodedFrame
      have targetPoint : ControlPoint program next
          (node "MlSelect" [encodedClauses, value actual, environment captured, encodedRest]) (2 * clauses.length + 1) :=
        .select listed resolved success
      exact ⟨_, prepared_base_control_step program prepared table 22 (by decide +kernel) built signatures point targetPoint
        (return_match_instance _ _ _ _)⟩
  | gather kind remaining captured suffix =>
    have same : encodedFrame = node "MlKBuild" [build kind, codes (remaining.map code), environment captured, valueList suffix, encodedRest] :=
      (Option.some.inj framed).symm
    subst encodedFrame
    cases remaining with
    | nil =>
      have targetPoint : ControlPoint program next
          (node "MlBuildConfig" [build kind, valueList (actual :: suffix), encodedRest]) 3 := .build resolved success
      exact ⟨_, prepared_base_control_step program prepared table 15 (by decide +kernel) built signatures point targetPoint
        (return_build_last_instance _ _ _ _ _)⟩
    | cons head later =>
      have targetPoint : ControlPoint program (.evaluate head captured (.gather kind later captured (actual :: suffix) :: rest))
          (node "MlEvaluate" [code head, environment captured, node "MlKBuild"
            [build kind, codes (later.map code), environment captured, valueList (actual :: suffix), encodedRest]]) 0 :=
        .state (by simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
      exact ⟨_, prepared_base_control_step program prepared table 14 (by decide +kernel) built signatures point targetPoint
        (return_build_more_instance _ _ _ _ _ _ _)⟩
  | branch yes no captured =>
    have same : encodedFrame = node "MlKBranch" [code yes, code no, environment captured, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have targetPoint : ControlPoint program (.evaluate (if choice then yes else no) captured rest) (node "MlEvaluate" [if choice then code yes else code no, environment captured, encodedRest]) 0 := by
          cases choice <;> exact .state (by simp [state?, resolved])
        exact ⟨_, prepared_base_control_step program prepared table (if choice then 4 else 5) (by cases choice <;> decide +kernel) built signatures point targetPoint
          (return_branch_instance choice (code yes) (code no) (environment captured) encodedRest)⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success
  | andThen right captured =>
    have same : encodedFrame = node "MlKAnd" [code right, environment captured, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have targetPoint : ControlPoint program (if choice then .evaluate right captured (.booleanResult :: rest) else .returned (.literal (.boolean false)) rest) (if choice then node "MlEvaluate" [code right, environment captured, node "MlKBoolean" [encodedRest]] else node "MlReturn" [literal (.boolean false), encodedRest]) 0 := by
          cases choice <;> exact .state (by simp [state?, continuation?, frame?, resolved, value, literal])
        exact ⟨_, prepared_base_control_step program prepared table (if choice then 7 else 6) (by cases choice <;> decide +kernel) built signatures point targetPoint
          (return_and_instance choice (code right) (environment captured) encodedRest)⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success
  | orElse right captured =>
    have same : encodedFrame = node "MlKOr" [code right, environment captured, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have targetPoint : ControlPoint program (if choice then .returned (.literal (.boolean true)) rest else .evaluate right captured (.booleanResult :: rest)) (if choice then node "MlReturn" [literal (.boolean true), encodedRest] else node "MlEvaluate" [code right, environment captured, node "MlKBoolean" [encodedRest]]) 0 := by
          cases choice <;> exact .state (by simp [state?, continuation?, frame?, resolved, value, literal])
        exact ⟨_, prepared_base_control_step program prepared table (if choice then 8 else 9) (by cases choice <;> decide +kernel) built signatures point targetPoint
          (return_or_instance choice (code right) (environment captured) encodedRest)⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success
  | booleanResult =>
    have same : encodedFrame = node "MlKBoolean" [encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have targetPoint : ControlPoint program (.returned (.literal (.boolean choice)) rest) (node "MlReturn" [literal (.boolean choice), encodedRest]) 0 := by
          cases choice <;> exact .state (by simp [state?, resolved, value, literal])
        exact ⟨_, prepared_base_control_step program prepared table (if choice then 10 else 11) (by cases choice <;> decide +kernel) built signatures point targetPoint
          (return_boolean_instance choice encodedRest)⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success

#print axioms prepared_frame_can_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
