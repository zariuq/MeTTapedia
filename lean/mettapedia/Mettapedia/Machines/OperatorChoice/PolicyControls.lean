import Mettapedia.Machines.OperatorChoice.HeadRoleBridge
import Mettapedia.Machines.OperatorChoice.AtomHeadDispatch
import Mettapedia.Machines.OperatorChoice.PrivateMachineViews
import Mettapedia.Machines.OperatorChoice.ClosureObservations
import Mettapedia.Machines.OperatorChoice.OverApplicationResume
import Mettapedia.Machines.OperatorChoice.ArityChoices

/-!
# Executable observations of the operator-policy comparisons

The matrix exhausts the stated three-Boolean head-selection family. The other
rows are independent component controls, not native conformance results. Their
reference theorems retain scope, payload multiplicity, effect history, captured
authority and pending work at the observation boundaries named in each module.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.PolicyControls

open HeadDispatchDesigns

def designs : List Design :=
  [false, true].flatMap fun general => [false, true].flatMap fun held =>
    [false, true].map fun scopedView => ⟨general, held, scopedView⟩

theorem eight_designs : designs.length = 8 := by decide
theorem designs_are_distinct : designs.Nodup := by decide

theorem designs_are_exhaustive (design : Design) : design ∈ designs := by
  rcases design with ⟨general, held, scopedView⟩
  cases general <;> cases held <;> cases scopedView <;> decide

theorem the_three_law_combination_is_present :
    designs.filter (fun design => design.generalHeads && design.protectHeld && design.respectScope) =
      [HeadDispatchDesigns.Controls.scopedGeneral] := by decide

def matrix : List (Design × List Nat × List Nat × List Nat) :=
  designs.map fun design =>
    (design,
      select design 0 ⟨"f", 1, true⟩ [⟨0, some "f", 1, 7⟩],
      select design 0 ⟨"f", 1, false⟩ [⟨1, some "f", 1, 9⟩],
      select design 0 ⟨"f", 1, false⟩ [⟨0, none, 1, 8⟩])

def observations : List (String × String) :=
  let source := AtomHeadDispatch.Controls.call "foo" 5
  let rows := [AtomHeadDispatch.Controls.row]
  let live := ClosureObservations.Controls.first
  let aliases := ClosureObservations.Controls.second
  let before := ClosureObservations.Controls.table
  let after := Function.update before 1 11
  [ ("G01-function-no-match", reprStr (AtomHeadDispatch.functionResult true 0 rows source)),
    ("G02-rewrite-no-match", reprStr (AtomHeadDispatch.rewriteResult 0 rows source)),
    ("G03-general-head-binding", reprStr <|
      AtomHeadDispatch.answers 0 [AtomHeadDispatch.Controls.tagged]
        (AtomHeadDispatch.Controls.call "double" 4)),
    ("P01-private-row-count", reprStr PrivateMachineViews.Controls.engine.internal.length),
    ("P02-source-only-query", reprStr <|
      (QueryState.run (PrivateMachineViews.engineStep HeadDispatchDesigns.Controls.scopedGeneral)
        PrivateMachineViews.Controls.client PrivateMachineViews.Controls.engine).answer),
    ("C01-current-alias-answers", reprStr <|
      ((ClosureObservations.invoke ClosureObservations.LiveNames.handler before live [5]).1,
       (ClosureObservations.invoke ClosureObservations.LiveNames.handler before aliases [5]).1)),
    ("C02-alias-answers-after-edit", reprStr <|
      ((ClosureObservations.invoke ClosureObservations.LiveNames.handler after live [5]).1,
       (ClosureObservations.invoke ClosureObservations.LiveNames.handler after aliases [5]).1)),
    ("C03-retained-answer-after-edit", reprStr <|
      (ClosureObservations.invoke ClosureObservations.LiveNames.retainedHandler after
        (ClosureObservations.LiveNames.capture before live) [5]).1),
    ("A01-batch-effectful-refusal", reprStr <|
      OverApplication.batch OverApplication.Controls.effectful 0 [3, 4]),
    ("A02-curried-effectful-refusal", reprStr <|
      OverApplication.curried OverApplication.Controls.effectful 1 0 [3, 4]),
    ("A03-curried-callable-success", reprStr <|
      OverApplication.curried OverApplication.Controls.forwarding 2 0 [3, 4]),
    ("A04-pause-keeps-forwarded-call", reprStr OverApplication.ResumeControls.cut),
    ("A05-resume-keeps-prefix-once", reprStr <|
      OverApplication.resume OverApplication.ResumeControls.program 1 OverApplication.ResumeControls.cut),
    ("A06-root-replay-repeats-prefix", reprStr <|
      OverApplication.attachPrefix OverApplication.ResumeControls.cut.effects
        OverApplication.ResumeControls.cut.work
        (OverApplication.curried OverApplication.ResumeControls.program 2 0 [3, 4])),
    ("O01-retained-arity-choices", reprStr (ArityChoices.classify [2, 4] 1)),
    ("O02-minimum-choice-loses-completion", reprStr (ArityChoices.classify [2] 3)),
    ("O03-maximum-choice-delays-exact", reprStr (ArityChoices.classify [4] 2)),
    ("O04-unique-arity-license", reprStr (ArityChoices.onlyFuture [1, 4] 2)) ]

end Mettapedia.Machines.OperatorChoice.PolicyControls
