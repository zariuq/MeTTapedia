import Mettapedia.Machines.ScopedCommit
import Mettapedia.Machines.EquationCut

/-!
# Equation-call unfolding into delimited commitment

The existing call-cut model has an independently defined continuation
semantics and frame machine. Here a bounded unfolding of its calls produces
finite `ScopedCommit.Body` programs. Every equation body runs inside the
call's delimiter, while its continuation returns to the caller's delimiter.

`unfold_correct` proves exact answer equality for every unfolding depth and
every source body, with arbitrary success and failure continuations. The
depth belongs to the existing reference semantics; it is not a fixed resource
limit or a proposed restriction on MeTTa programs. The target fragment uses
no world effects; the effectful scoped core is verified separately.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedCommitCall

open ScopedCommit

universe u

variable {Local : Type u}

def pureEval (body : Body Local Unit) (s : Local)
    (success : Local → List Local → List Local) (failure saved : List Local) : List Local :=
  eval body s (fun t alternatives _ => success t (alternatives ()))
    (fun _ => failure) (fun _ => saved) ()

private theorem unit_function (f : Unit → List Local) : f = fun _ => f () := by
  funext value
  cases value
  rfl

theorem eval_unit (body : Body Local Unit) (s : Local)
    (success : Local → List Local → List Local) (failure saved : Unit → List Local) :
    eval body s (fun t alternatives _ => success t (alternatives ())) failure saved () =
      pureEval body s success (failure ()) (saved ()) := by
  rw [unit_function failure, unit_function saved]
  rfl

theorem pureEval_choice (left right : Body Local Unit) (s : Local)
    (success : Local → List Local → List Local) (failure saved : List Local) :
    pureEval (.choice left right) s success failure saved =
      pureEval left s success (pureEval right s success failure saved) saved := by
  unfold pureEval
  rw [eval, eval_unit]

theorem pureEval_choose (alternatives : Local → List Local) (next : Body Local Unit)
    (s : Local) (success : Local → List Local → List Local) (failure saved : List Local) :
    pureEval (.choose (fun t _ => alternatives t) next) s success failure saved =
      (alternatives s).foldr (fun t rest => pureEval next t success rest saved) failure := by
  unfold pureEval
  rw [eval]
  generalize alternatives s = values
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.foldr_cons]
      rw [eval_unit]
      rw [ih]
      rfl

theorem pureEval_scope (body next : Body Local Unit) (s : Local)
    (success : Local → List Local → List Local) (failure saved : List Local) :
    pureEval (.scope body next) s success failure saved =
      pureEval body s (fun t rest => pureEval next t success rest saved) failure failure := by
  unfold pureEval
  rw [eval]

/-- Ordered alternatives of the active operational policy, with no delimiter
of their own. The enclosing call installs the delimiter. -/
def equationChoice (equations : List (Body Local Unit)) : Body Local Unit :=
  equations.foldr .choice .fail

theorem pureEval_equationChoice (equations : List (Body Local Unit)) (s : Local)
    (success : Local → List Local → List Local) (failure saved : List Local) :
    pureEval (equationChoice equations) s success failure saved =
      equations.foldr (fun body rest => pureEval body s success rest saved) failure := by
  induction equations with
  | nil => rfl
  | cons body equations ih =>
      simp only [equationChoice, List.foldr_cons, pureEval_choice] at *
      rw [ih]

def unfold (program : EquationCut.Program Local) : Nat → EquationCut.Body Local → Body Local Unit
  | _, .done => .done
  | depth, .prim operation next =>
      .choose (fun s _ => operation s) (unfold program depth next)
  | depth, .cut next => .commit (unfold program depth next)
  | depth, .branch test yes no =>
      .branch (fun s _ => test s) (unfold program depth yes) (unfold program depth no)
  | 0, .call _ _ => .fail
  | depth + 1, .call relation next =>
      .scope (equationChoice ((program relation).map (unfold program depth)))
        (unfold program (depth + 1) next)
termination_by depth body => (depth, sizeOf body)

/-- Exact comparison with the existing independent call-cut interpretation.
The equation body, earlier goal choices and caller alternatives receive the
same distinct failure continuations under the constructed scope. -/
theorem unfold_correct (program : EquationCut.Program Local) :
    ∀ (depth : Nat) (body : EquationCut.Body Local) (s : Local)
      (success : Local → List Local → List Local) (failure saved : List Local),
      pureEval (unfold program depth body) s success failure saved =
        EquationCut.den program depth body s success failure saved
  | depth, .done, s, success, failure, saved => by
      rw [unfold, EquationCut.den]
      rfl
  | depth, .prim operation next, s, success, failure, saved => by
      rw [unfold, pureEval_choose, EquationCut.den]
      apply congrArg (fun f => (operation s).foldr f failure)
      funext value rest
      exact unfold_correct program depth next value success rest saved
  | depth, .cut next, s, success, failure, saved => by
      rw [unfold, EquationCut.den]
      change pureEval (unfold program depth next) s success saved saved = _
      exact unfold_correct program depth next s success saved saved
  | depth, .branch test yes no, s, success, failure, saved => by
      rw [unfold, EquationCut.den]
      change (if test s then pureEval (unfold program depth yes) s success failure saved
        else pureEval (unfold program depth no) s success failure saved) = _
      cases test s
      · exact unfold_correct program depth no s success failure saved
      · exact unfold_correct program depth yes s success failure saved
  | 0, .call relation next, s, success, failure, saved => by
      rw [unfold, EquationCut.den]
      rfl
  | depth + 1, .call relation next, s, success, failure, saved => by
      rw [unfold, pureEval_scope, pureEval_equationChoice, List.foldr_map,
        EquationCut.den_call, EquationCut.equations]
      have continuation :
          (fun value rest => pureEval (unfold program (depth + 1) next)
            value success rest saved) =
          (fun value rest => EquationCut.den program (depth + 1) next
            value success rest saved) := by
        funext value rest
        exact unfold_correct program (depth + 1) next value success rest saved
      rw [continuation]
      apply congrArg (fun f => (program relation).foldr f failure)
      funext equation rest
      exact unfold_correct program depth equation s _ rest failure
termination_by depth body _ _ _ _ => (depth, sizeOf body)

/-- Forgetting the inert world connects the effectful evaluator's ordinary
answer collection to its pure continuation interpretation. -/
theorem run_pure (body : Body Local Unit) (s : Local) :
    (run body s ()).1 = pureEval body s (fun value rest => value :: rest) [] [] := by
  have natural := eval_natural Prod.fst body s collect
    (fun value alternatives w => value :: alternatives w) finish finish () (by
      intro value alternatives w
      rfl)
  simpa only [run, pureEval, finish] using natural.symm

theorem run_unfold_correct (program : EquationCut.Program Local) (depth : Nat)
    (body : EquationCut.Body Local) (s : Local) :
    (run (unfold program depth body) s ()).1 =
      EquationCut.den program depth body s (fun value rest => value :: rest) [] [] := by
  rw [run_pure, unfold_correct]

/-- The independently defined frame machine emits a prefix of the constructed
scoped program's observations at every finite step budget. -/
theorem frame_run_prefix (program : EquationCut.Program Local) (steps depth : Nat)
    (body : EquationCut.Body Local) (s : Local) :
    (EquationCut.run program steps (EquationCut.start depth body s)).1 <+:
      (run (unfold program depth body) s ()).1 := by
  rw [run_unfold_correct]
  exact EquationCut.run_prefix program steps depth body s

/-- On completion the frame machine and the constructed scoped program have
exactly the same ordered occurrences. No native-C correspondence is inferred. -/
theorem frame_run_answers (program : EquationCut.Program Local) (steps depth : Nat)
    (body : EquationCut.Body Local) (s : Local)
    (finished : (EquationCut.run program steps (EquationCut.start depth body s)).2.act = none)
    (exhausted : (EquationCut.run program steps (EquationCut.start depth body s)).2.frames = []) :
    (EquationCut.run program steps (EquationCut.start depth body s)).1 =
      (run (unfold program depth body) s ()).1 := by
  rw [run_unfold_correct]
  exact EquationCut.run_answers program steps depth body s finished exhausted

end Mettapedia.Machines.ScopedCommitCall
