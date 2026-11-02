import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledBooleanReturn
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledGather
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPoint
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnTerminal
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnBranches
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnCons
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClauseDispatch
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCallFiring

/-! Every actual prepared return firing enters a source control point. The
continuation and returned Boolean select their authored rows; construction,
application, pattern entry and clause selection retain administrative work.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

private theorem return_success {program : OCaml.Program} {actual : OCaml.Value} {rest : OCaml.Continuation}
    {next : OCaml.MachineState}
    (step : OCaml.machineStep program (.returned actual rest) = .ok (some next)) :
    OCaml.returnValue program actual rest = .ok next := by
  cases answer : OCaml.returnValue program actual rest <;> simp_all [OCaml.machineStep, Except.map]

private theorem single_return_row (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} (label : String) (actual : Pattern) (inputs : List Pattern)
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {index : Nat}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (unique : returnCandidates label = [index])
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlReturn" [actual, node label inputs]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[index]? = some row.authored := by
  obtain ⟨selected, authored, member⟩ := enabled_return_continuation program prepared table label actual inputs built position firing
  rw [unique] at member
  have same := List.mem_singleton.mp member
  subst selected
  exact authored

theorem prepared_return_frame_entry (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (actual : OCaml.Value) (frame : OCaml.Frame) (rest : OCaml.Continuation)
    (encodedRest encodedFrame target : Pattern) (next : OCaml.MachineState)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (framed : frame? (patterns program) frame encodedRest = some encodedFrame)
    (sourceStep : OCaml.machineStep program (.returned actual (frame :: rest)) = .ok (some next))
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlReturn" [value actual, encodedFrame]) ordinal trace captured completed history target) :
    ∃ rank, ControlPoint program next target rank := by
  have zero := prepared_selected_row_zero program prepared table built position
  have success := return_success sourceStep
  cases frame with
  | argument function sourceEnvironment =>
    have same : encodedFrame = node "MlKArgument" [code function, environment sourceEnvironment, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have authored := single_return_row (index := 1) program prepared table "MlKArgument" _ _ built position (by decide +kernel) firing
    obtain ⟨_, _, actualNext, step, encoded⟩ := return_argument_source_step (program := program) position authored zero resolved firing
    have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
    subst actualNext
    exact ⟨0, .state encoded⟩
  | consTail head sourceEnvironment =>
    have same : encodedFrame = node "MlKConsTail" [code head, environment sourceEnvironment, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have authored := single_return_row (index := 12) program prepared table "MlKConsTail" _ _ built position (by decide +kernel) firing
    obtain ⟨_, _, actualNext, step, encoded⟩ := return_cons_tail_source_step (program := program) position authored zero resolved firing
    have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
    subst actualNext
    exact ⟨0, .state encoded⟩
  | consHead tail =>
    have same : encodedFrame = node "MlKConsHead" [value tail, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have authored := single_return_row (index := 13) program prepared table "MlKConsHead" _ _ built position (by decide +kernel) firing
    obtain ⟨_, _, actualNext, step, encoded⟩ := return_cons_head_source_step (program := program) position authored zero resolved firing
    have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
    subst actualNext
    exact ⟨0, .state encoded⟩
  | function argument =>
    have same : encodedFrame = node "MlKFunction" [value argument, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have authored := single_return_row (index := 2) program prepared table "MlKFunction" _ _ built position (by decide +kernel) firing
    obtain ⟨_, _, targetSame⟩ := base_instance_firing position authored zero
      (return_function_instance (value actual) (value argument) encodedRest) firing
    rw [targetSame]
    exact ⟨2, .application resolved success⟩
  | letValue parameter body sourceEnvironment =>
    cases referenced : patternReference? (patterns program) parameter with
    | none => simp [frame?, referenced] at framed
    | some patternCode =>
      have same : encodedFrame = node "MlKLet" [patternCode, code body, environment sourceEnvironment, encodedRest] := by
        simpa only [frame?, referenced, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] using framed.symm
      subst encodedFrame
      have authored := single_return_row (index := 3) program prepared table "MlKLet" _ _ built position (by decide +kernel) firing
      obtain ⟨_, _, targetSame⟩ := base_instance_firing position authored zero
        (return_let_instance (value actual) patternCode (code body) (environment sourceEnvironment) encodedRest) firing
      unfold patternReference? at referenced
      obtain ⟨index, found, codeSame⟩ := Option.map_eq_some_iff.mp referenced
      subst patternCode
      have sameNext : next = OCaml.enterBody parameter actual body sourceEnvironment rest := Except.ok.inj success.symm
      rw [sameNext, targetSame]
      exact ⟨1, .matchOne (OCaml.patternIndex?_sound parameter (patterns program) index found) resolved⟩
  | matchValue clauses sourceEnvironment =>
    cases listed : clauseList? (patterns program) clauses with
    | none => simp [frame?, listed] at framed
    | some encodedClauses =>
      have same : encodedFrame = node "MlKMatch" [encodedClauses, environment sourceEnvironment, encodedRest] := by
        simpa only [frame?, listed, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] using framed.symm
      subst encodedFrame
      have authored := single_return_row (index := 22) program prepared table "MlKMatch" _ _ built position (by decide +kernel) firing
      obtain ⟨_, _, targetSame⟩ := return_match_firing position authored zero firing
      rw [targetSame]
      exact ⟨2 * clauses.length + 1, .select listed resolved success⟩
  | gather kind remaining sourceEnvironment suffix =>
    have same : encodedFrame = node "MlKBuild" [build kind, codes (remaining.map code), environment sourceEnvironment,
        valueList suffix, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    have authored := enabled_gather_row program prepared table _ _ _ _ _ remaining built position firing
    cases remaining with
    | nil =>
      obtain ⟨_, _, targetSame⟩ := return_build_last_firing position authored zero firing
      rw [targetSame]
      exact ⟨3, .build resolved success⟩
    | cons head later =>
      obtain ⟨_, _, actualNext, step, encoded⟩ := return_build_more_source_step (program := program) position authored zero resolved firing
      have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
      subst actualNext
      exact ⟨0, .state encoded⟩
  | branch yes no sourceEnvironment =>
    have same : encodedFrame = node "MlKBranch" [code yes, code no, environment sourceEnvironment, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have authored := enabled_boolean_return program prepared table "MlKBranch" choice _ built position (by simp) firing
        have selected : baseLanguage.rewrites[if choice then 4 else 5]? = some row.authored := by simpa [booleanReturnIndex] using authored
        obtain ⟨_, _, actualNext, step, encoded⟩ := branch_return_source_step (program := program) position selected zero resolved firing
        have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
        subst actualNext
        exact ⟨0, .state encoded⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success
  | andThen right sourceEnvironment =>
    have same : encodedFrame = node "MlKAnd" [code right, environment sourceEnvironment, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have authored := enabled_boolean_return program prepared table "MlKAnd" choice _ built position (by simp) firing
        have selected : baseLanguage.rewrites[if choice then 7 else 6]? = some row.authored := by simpa [booleanReturnIndex] using authored
        obtain ⟨_, _, actualNext, step, encoded⟩ := return_and_source_step (program := program) position selected zero resolved firing
        have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
        subst actualNext
        exact ⟨0, .state encoded⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success
  | orElse right sourceEnvironment =>
    have same : encodedFrame = node "MlKOr" [code right, environment sourceEnvironment, encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have authored := enabled_boolean_return program prepared table "MlKOr" choice _ built position (by simp) firing
        have selected : baseLanguage.rewrites[if choice then 8 else 9]? = some row.authored := by simpa [booleanReturnIndex] using authored
        obtain ⟨_, _, actualNext, step, encoded⟩ := return_or_source_step (program := program) position selected zero resolved firing
        have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
        subst actualNext
        exact ⟨0, .state encoded⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success
  | booleanResult =>
    have same : encodedFrame = node "MlKBoolean" [encodedRest] := (Option.some.inj framed).symm
    subst encodedFrame
    cases actual with
    | literal datum =>
      cases datum with
      | boolean choice =>
        have authored := enabled_boolean_return program prepared table "MlKBoolean" choice _ built position (by simp) firing
        have selected : baseLanguage.rewrites[if choice then 10 else 11]? = some row.authored := by simpa [booleanReturnIndex] using authored
        obtain ⟨_, _, actualNext, step, encoded⟩ := return_boolean_source_step (program := program) position selected zero resolved firing
        have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
        subst actualNext
        exact ⟨0, .state encoded⟩
      | _ => simp [OCaml.returnValue] at success
    | _ => simp [OCaml.returnValue] at success

#print axioms prepared_return_frame_entry

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
