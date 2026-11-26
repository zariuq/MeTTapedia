import MeTTaIL.Semantics.Eval

/-! Adjacent kernel-checked checkpoints compose with their declared fuel. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Checkpoints

open MeTTaIL

/-- Each block starts at the exact endpoint of its predecessor. -/
inductive ReplayTrace (program : Presentation) : AST → Nat → AST → Prop
  | done (state : AST) : ReplayTrace program state 0 state
  | next {source middle target : AST} {fuel rest : Nat}
      (step : eval program fuel source = middle) (tail : ReplayTrace program middle rest target) :
      ReplayTrace program source (fuel + rest) target

theorem ReplayTrace.evaluated {program : Presentation} {source target : AST} {fuel : Nat}
    (trace : ReplayTrace program source fuel target) : eval program fuel source = target := by
  induction trace with
  | done => rfl
  | next step _ evaluatesTail => rw [eval_add, step, evaluatesTail]

private def marker (name : String) : AST := .sexp (.id name) []

private def twoSteps : Presentation := .mk [] [] []
  [{ name := "first", rw := .base (marker "a") (marker "b") },
   { name := "second", rw := .base (marker "b") (marker "c") }] []

example : ReplayTrace twoSteps (marker "a") 2 (marker "c") :=
  .next (fuel := 1) (by rfl) (.next (fuel := 1) (by rfl) (.done _))

example : ¬ ReplayTrace twoSteps (marker "a") 2 (marker "b") := by
  intro trace
  have terminal : eval twoSteps 2 (marker "a") = marker "c" := rfl
  have impossible : false = true :=
    congrArg (fun state => state == marker "b") (terminal.symm.trans trace.evaluated)
  exact Bool.false_ne_true impossible

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Checkpoints
