import Mettapedia.Languages.MeTTa.PeTTa.LiveEquations
import Mettapedia.Languages.MeTTa.PeTTa.BetaInlining

/-!
# Inlining a call while its equations are live

PeTTa selects the equations of a call from the `=` rows of `&self` that are there when the call is
made (`LiveEquations`). Beta inlining replaces a call of a one-equation function by its body with
the arguments substituted (`BetaInlining.beta_complete`), on the machine whose equations are fixed
when the program is loaded.

**Inlining on a stretch without redefinition** (`live_beta_complete`). If the live rows are the
program's equations when the call is made, and no configuration that the live machine reaches from
the call, or from the inlined body, adds or removes a row of `&self` (`KeepsRows`), the call and
its inlined body complete on the live machine with the same store, the same answers in the same
order and multiplicity, and the same remaining input and output. The condition is a premise about
the run, not a rule of the language: redefinition stays available to every program.

**A redefinition in the middle of the run breaks it** (`inlining_across_redefinition`). With
`(= (f $x) (a $x))` loaded, `(let $u (add-atom &self (= (f $x) (b $x))) (f 1))` answers
`(a 1) (b 1)`, while the same request with `(f 1)` unfolded by the equation live when the run
starts answers `(a 1)`. On `Eval.step` of the loaded program, whose equations stay fixed, both
answer `(a 1)`.

The transport along a stretch (`live_path_of_keepsRows`, `fixed_path_of_live`,
`live_path_of_liveRuns`) uses `liveTransition_of_live`, `transition_of_live`,
`transition_keeps_core` and `live_of_same_core` of `LiveEquations`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LiveInlining

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program)
open Effects (State)
open Eval
open DeclarativeSpec (Runs)
open LiveEquations
open BetaInlining

/-- **No configuration that the live machine reaches from `source` adds or removes a row of
`&self`.** -/
def KeepsRows (registry : Program) (source : Configuration) : Prop :=
  ∀ current, (liveTheory registry).MultiStep source current → ¬ EditsSelf current

/-- A path of `Eval.step registry` from a configuration whose live rows are `registry`'s
equations, and from which the live machine reaches no edit of `&self`, is a path of the live
machine. -/
theorem live_path_of_keepsRows {registry : Program} :
    {source target : Configuration} →
    (theory registry).MultiStep source target →
    EquationsLive registry source.state →
    KeepsRows registry source →
    (liveTheory registry).MultiStep source target
  | _, _, .refl current, _, _ => Mettapedia.GSLT.GSLT.MultiStep.refl (S := liveTheory registry) current
  | _, _, .step transition rest, live, keeps => by
      have notEdit := keeps _ (Mettapedia.GSLT.GSLT.MultiStep.refl (S := liveTheory registry) _)
      have next := live_of_same_core live (transition_keeps_core transition notEdit)
      have step := liveTransition_of_live live transition
      refine Mettapedia.GSLT.GSLT.MultiStep.step (S := liveTheory registry) step
        (live_path_of_keepsRows rest next ?_)
      intro current reach
      exact keeps current (Mettapedia.GSLT.GSLT.MultiStep.step (S := liveTheory registry) step reach)

/-- Conversely, such a path of the live machine is a path of `Eval.step registry`. -/
theorem fixed_path_of_live {registry : Program} {source target : Configuration}
    (path : (liveTheory registry).MultiStep source target)
    (live : EquationsLive registry source.state) (keeps : KeepsRows registry source) :
    (theory registry).MultiStep source target :=
  path_of_live_path path live fun current reach _ => keeps current reach

/-- A completed live run is a live path to its finished configuration. -/
theorem live_path_of_liveRuns {registry : Program} {source : Configuration} {state : State}
    {answers input output : List Atom}
    (running : LiveRuns registry source (.complete state answers input output)) :
    (liveTheory registry).MultiStep source (finished state answers input output) := by
  generalize result : Outcome.complete state answers input output = outcome at running
  induction running with
  | completed control frames =>
      rename_i source' answers'
      cases result
      obtain ⟨st, k, fs, i, o⟩ := source'
      simp only at control frames
      subst control frames
      exact Mettapedia.GSLT.GSLT.MultiStep.refl (S := liveTheory registry) _
  | fault _ => cases result
  | next transition _ ih =>
      exact Mettapedia.GSLT.GSLT.MultiStep.step (S := liveTheory registry) transition (ih result)

section Beta

variable {program : Program} {f : String} {params args : List String} {body : Atom}
  {names : String → String} {caller : Subst} {state : State} {frames : List Frame}
  {input output : List Atom}

/-- One direction of the transport: a completed live run from a configuration that keeps the
rows is a completed run of `Eval.step`, and back. -/
theorem runs_iff_liveRuns {source : Configuration} (live : EquationsLive program source.state)
    (keeps : KeepsRows program source) (after : State) (answers input' output' : List Atom) :
    Runs program source (.complete after answers input' output') ↔
      LiveRuns program source (.complete after answers input' output') := by
  constructor
  · intro running
    have path := (completed_derivation_iff_path program source after answers input' output').mp
      running
    exact liveRuns_of_path (live_path_of_keepsRows path live keeps) rfl rfl
  · intro running
    exact (completed_derivation_iff_path program source after answers input' output').mpr
      (fixed_path_of_live (live_path_of_liveRuns running) live keeps)

/-- **Law 5, inlining on a stretch without redefinition.** When the live rows are the program's
equations at the call, and neither the call nor its inlined body reaches an edit of `&self` on the
live machine, the call and its inlined body complete with the same store, answers, input and
output. -/
theorem live_beta_complete (premises : Inlinable program f params args body names caller)
    (live : EquationsLive program state)
    (keepsCall : KeepsRows program (callConfiguration f args caller state frames input output))
    (keepsInlined :
      KeepsRows program (inlinedConfiguration body names caller state frames input output))
    (after : State) (answers input' output' : List Atom) :
    LiveRuns program (callConfiguration f args caller state frames input output)
        (.complete after answers input' output') ↔
      LiveRuns program (inlinedConfiguration body names caller state frames input output)
        (.complete after answers input' output') := by
  rw [← runs_iff_liveRuns (source := callConfiguration f args caller state frames input output)
      live keepsCall,
    ← runs_iff_liveRuns (source := inlinedConfiguration body names caller state frames input output)
      live keepsInlined]
  exact beta_complete (state := state) (frames := frames) (input := input) (output := output)
    premises after answers input' output'

end Beta

/-! ## A redefinition in the middle of the run -/

private def int (value : Int) : Atom := .grounded (.int value)
private def sym (name : String) : Atom := .symbol name
private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private def row (head : String) (arguments : List Atom) (body : Atom) : Atom :=
  call "=" [call head arguments, body]

/-- `(let $u (add-atom &self (= (f $x) (b $x))) rest)` -/
private def redefineThen (rest : Atom) : Atom :=
  call "let" [.var "u", call "add-atom" [sym "&self", row "f" [.var "x"] (call "b" [.var "x"])],
    rest]

/-- **Inlining across a redefinition changes the answers.** With `(= (f $x) (a $x))` loaded, the
request that adds `(= (f $x) (b $x))` and then calls `(f 1)` answers `(a 1) (b 1)` on the live
machine; with `(f 1)` unfolded to `(a 1)` by the equation live when the run starts, it answers
`(a 1)`. The machine with fixed equations answers `(a 1)` to both. -/
theorem inlining_across_redefinition :
    (liveRequests redefined 64 (Effects.loaded redefined)
        [redefineThen (call "f" [int 1])]).map observed =
      [.answers [call "a" [int 1], call "b" [int 1]]] ∧
    (liveRequests redefined 64 (Effects.loaded redefined)
        [redefineThen (call "a" [int 1])]).map observed =
      [.answers [call "a" [int 1]]] ∧
    (fixedRequests redefined 64 (Effects.loaded redefined)
        [redefineThen (call "f" [int 1])]).map observed =
      [.answers [call "a" [int 1]]] ∧
    (fixedRequests redefined 64 (Effects.loaded redefined)
        [redefineThen (call "a" [int 1])]).map observed =
      [.answers [call "a" [int 1]]] := by
  decide +kernel

/-- **Without a redefinition the two agree**, as `live_beta_complete` says: `(f 1)` and `(a 1)`
answer alike on the live machine. -/
theorem inlining_without_redefinition :
    (liveRequests redefined 64 (Effects.loaded redefined) [call "f" [int 1]]).map observed =
      (liveRequests redefined 64 (Effects.loaded redefined) [call "a" [int 1]]).map observed := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.LiveInlining
