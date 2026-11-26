import Mettapedia.Languages.MeTTa.SpaceTheory.HEContextEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotEntry

/-!
# Local HE instructions

These instructions operate on the current activation and task. The
step for `eval`, `chain`, or `function` schedules work; it does not run it.
Unification keeps both the logical candidate and contextual readout
premises. Context entry and binding snapshots are separate authorities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEMinimalEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (mkErrorMessage)
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation Task Control managedContextControl)
open HEFocused (Focus Leaf Parent NativeRequest)

def covered : Task → Bool
  | .minimal .. => true
  | _ => false

inductive Plan (dispatch : GroundedDispatch) (p : Policy) : Task → Leaf → List Continuation → Prop where
  | data {live scope caller value activation} :
      Minimal.embeddedInstruction value.erase = false →
      Plan dispatch p (.minimal live scope caller value activation) (.returning [(value, activation)]) []
  | eval {live scope caller status operand activation} :
      Plan dispatch p (.minimal live scope caller (.expression status [.symbol "eval", operand]) activation)
        (.work (.invocation live scope caller (activation.read p operand) activation)) []
  | chain {live scope caller status operand name template activation} :
      Plan dispatch p (.minimal live scope caller
        (.expression status [.symbol "chain", operand, .var name, template]) activation)
        (.work (.minimal ((.expression [.symbol "chain", operand.erase, .var name, template.erase]) :: live) scope
          (some (.expression [.symbol "chain", operand.erase, .var name, template.erase])) operand activation))
        [.boundaryBatch live scope caller (.chain name template)]
  | unify {live scope caller status target pattern yes no activation output} :
      UnifyCandidateRel target.erase pattern.erase activation.bindings output.bindings →
      Entry.Value.UnifyRel p.rebuilding activation.environment target pattern output.environment →
      Plan dispatch p (.minimal live scope caller
        (.expression status [.symbol "unify", target, pattern, yes, no]) activation)
        (.returning [(output.read p yes, output)]) []
  | noMatch {live scope caller status target pattern yes no activation} :
      UnifyNoMatchRel target.erase pattern.erase activation.bindings →
      Plan dispatch p (.minimal live scope caller
        (.expression status [.symbol "unify", target, pattern, yes, no]) activation)
        (.returning [(no, activation)]) []
  | badArity {live scope caller status tail activation} :
      tail.length ≠ 4 →
      Plan dispatch p (.minimal live scope caller (.expression status (.symbol "unify" :: tail)) activation)
        (.returning [(Entry.Value.ofAtom (mkErrorMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase))
          (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase)))), activation)]) []
  | cons {live scope caller status tailStatus head tail activation} :
      Plan dispatch p (.minimal live scope caller
        (.expression status [.symbol "cons-atom", head, .expression tailStatus tail]) activation)
        (.returning [(.expression .active (head :: tail), activation)]) []
  | decons {live scope caller status valueStatus head tail activation} :
      Plan dispatch p (.minimal live scope caller
        (.expression status [.symbol "decons-atom", .expression valueStatus (head :: tail)]) activation)
        (.returning [(.expression .active [head, .expression .active tail], activation)]) []
  | function {live scope caller status body bodyStatus children activation} :
      body = .expression bodyStatus children →
      Plan dispatch p (.minimal live scope caller (.expression status [.symbol "function", body]) activation)
        (.work (.body ((.expression [.symbol "function", body.erase]) :: live) scope
          (some (.expression [.symbol "function", body.erase])) body activation))
        [.boundaryBatch live scope caller .functionDone]

theorem Plan.covered {dispatch p task body frames} (plan : Plan dispatch p task body frames) :
    covered task = true := by cases plan <;> rfl

theorem Plan.frames_bound {dispatch p task body frames} (plan : Plan dispatch p task body frames) :
    frames.length ≤ 1 := by cases plan <;> simp

variable {Context World : Type}

private theorem unmanaged (task : Task) (noScope : HEContextEntry.Request.recognize task = none) :
    managedContextControl (.work task : Control Context) = false := by
  unfold managedContextControl
  split <;> simp_all [HEContextEntry.Request.recognize]

theorem step_iff (env : WorldEnvironment Context World) (p : Policy)
    (task : Task) (supported : covered task = true)
    (noNative : NativeRequest.recognize task = none)
    (noScope : HEContextEntry.Request.recognize task = none) (noSnapshot : HESnapshotEntry.covered task = false)
    (world : World) (active : Context) (stack : List Continuation) (parents : List (Parent Context))
    (seen : List Result) (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
        ⟨world, active, .work task, stack, parents, seen⟩ target ↔
      ∃ body frames, Plan env.dispatch p task body frames ∧
        target = ⟨world, active, body, frames ++ stack, parents, seen⟩ := by
  constructor
  · intro moved
    cases task <;> simp only [covered, Bool.false_eq_true] at supported
    case minimal live scope caller value activation =>
      cases moved with
      | perform edge =>
        cases edge with
        | core incoming local' stepped outgoing =>
          cases incoming
          cases stepped <;> cases outgoing
          all_goals first
            | exact ⟨_, _, .data (by assumption), rfl⟩
            | exact ⟨_, _, .eval, rfl⟩
            | exact ⟨_, _, .chain, rfl⟩
            | exact ⟨_, _, .unify (by assumption) (by assumption), rfl⟩
            | exact ⟨_, _, .noMatch (by assumption), rfl⟩
            | exact ⟨_, _, .badArity (by assumption), rfl⟩
            | exact ⟨_, _, .cons, rfl⟩
            | exact ⟨_, _, .decons, rfl⟩
            | exact ⟨_, _, .function (by assumption), rfl⟩
            | cases local'
        | evalc => cases noScope
        | metta => cases noScope
        | contextSpace => cases noScope
        | native _ => cases noNative
        | collapseEnter _ => cases noSnapshot
        | superposeEnter _ => cases noSnapshot
  · rintro ⟨body, frames, plan, rfl⟩
    let before : Focus Context World := ⟨world, active, .work task, stack, parents, seen⟩
    have local' := unmanaged (Context := Context) task noScope
    cases plan with
    | data bare => exact .perform (before := before) (.core (.work _) local' (.minimalData bare) (.returning _))
    | eval => exact .perform (before := before) (.core (.work _) local' .minimalEval (.work _))
    | chain => exact .perform (before := before) (.core (.work _) local' .minimalChain (.work _))
    | unify matched values =>
      exact .perform (before := before) (.core (.work _) local' (.minimalUnifyYes matched values) (.returning _))
    | noMatch missed =>
      exact .perform (before := before) (.core (.work _) local' (.minimalUnifyNo missed) (.returning _))
    | badArity bad =>
      exact .perform (before := before) (.core (.work _) local' (.minimalUnifyBadArity bad) (.returning _))
    | cons => exact .perform (before := before) (.core (.work _) local' .minimalConsAtom (.returning _))
    | decons => exact .perform (before := before) (.core (.work _) local' .minimalDeconsAtom (.returning _))
    | function shape =>
      exact .perform (before := before) (.core (.work _) local' (.minimalFunction shape) (.work _))

end Mettapedia.Languages.MeTTa.SpaceTheory.HEMinimalEntry
