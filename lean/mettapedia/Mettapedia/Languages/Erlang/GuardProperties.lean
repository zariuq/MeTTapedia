import Mettapedia.Languages.Erlang.Machine

/-! Guard attempts delimit ordinary faults. Failed attempts discard the
candidate clause's bindings and resume the remaining clauses in the outer
environment. Internal malformed-IR diagnostics are not language faults and
are never hidden by these laws. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

theorem choose_failed_pattern (arguments : List Value) (clause : Clause) (rest : List Clause)
    (environment : Environment) (continuation : Continuation)
    (failed : matchFields environment clause.patterns arguments = none) :
    chooseClause arguments (clause :: rest) environment continuation =
      .choose arguments rest environment continuation := by
  simp [chooseClause, failed]

theorem choose_matched_pattern (arguments : List Value) (clause : Clause) (rest : List Clause)
    (environment : Environment) (continuation : Continuation) (bindings : List Value)
    (matched : matchFields environment clause.patterns arguments = some bindings) :
    chooseClause arguments (clause :: rest) environment continuation =
      .evaluate clause.guard (extend environment bindings)
        (.guardResult arguments rest clause.body (extend environment bindings) environment :: continuation) := by
  simp [chooseClause, matched]

theorem guard_accepts_true (program : Program) (arguments : List Value) (rest : List Clause)
    (body : Code) (bound outer : Environment) (continuation : Continuation) :
    returnValues program [boolean true] (.guardResult arguments rest body bound outer :: continuation) =
      .ok (.evaluate body bound continuation) := by
  simp only [returnValues, boolean, acceptsGuard, if_true]
  rfl

theorem guard_rejects_other (program : Program) (values arguments : List Value) (rest : List Clause)
    (body : Code) (bound outer : Environment) (continuation : Continuation)
    (notTrue : acceptsGuard values = false) :
    returnValues program values (.guardResult arguments rest body bound outer :: continuation) =
      .ok (.choose arguments rest outer continuation) := by
  simp only [returnValues, notTrue, Bool.false_eq_true, if_false]
  rfl

theorem guard_fault_restores_outer (fault : Fault) (above : Continuation)
    (arguments : List Value) (rest : List Clause) (body : Code) (bound outer : Environment)
    (continuation : Continuation) (noGuard : guardActive above = false) :
    raiseFault fault (above ++ .guardResult arguments rest body bound outer :: continuation) =
      .choose arguments rest outer continuation := by
  induction above with
  | nil => rfl
  | cons frame frames ih =>
      unfold guardActive at noGuard
      rw [List.any_cons] at noGuard
      have remaining : guardActive frames = false := (Bool.or_eq_false_iff.mp noGuard).2
      cases frame <;> simp at noGuard
      all_goals simpa only [List.cons_append, raiseFault] using ih remaining

end Mettapedia.Languages.Erlang
