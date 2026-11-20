import Mettapedia.Machines.OperatorChoice.OverApplication

/-!
# Resuming callable chaining without replaying its prefix

The current program is fixed during this comparison. A paused report keeps its
next callable and already captured argument vector; resume preserves earlier
effects and work exactly once. This supplies the missing operational
qualification of the arity-controller comparison, rather than equating only
fully drained answer values.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.OverApplication

variable {Fn Arg Value Effect : Type}

def resume (program : Program Fn Arg Value Effect) (fuel : Nat)
    (report : Report Fn Arg Value Effect) : Report Fn Arg Value Effect :=
  match report.status with
  | .paused name arguments => attachPrefix report.effects report.work (curried program fuel name arguments)
  | _ => report

theorem attach_associative (first second : List Effect) (firstWork secondWork : Nat)
    (report : Report Fn Arg Value Effect) :
    attachPrefix first firstWork (attachPrefix second secondWork report) =
      attachPrefix (first ++ second) (firstWork + secondWork) report := by
  simp [attachPrefix, List.append_assoc, Nat.add_assoc]

theorem resume_attach (program : Program Fn Arg Value Effect) (fuel : Nat)
    (effects : List Effect) (work : Nat) (report : Report Fn Arg Value Effect) :
    resume program fuel (attachPrefix effects work report) =
      attachPrefix effects work (resume program fuel report) := by
  rcases report with ⟨status, previousEffects, previousWork⟩
  cases status <;> simp [resume, attachPrefix, List.append_assoc, Nat.add_assoc]

theorem curried_add (program : Program Fn Arg Value Effect) (first later : Nat)
    (name : Fn) (arguments : List Arg) :
    curried program (first + later) name arguments =
      resume program later (curried program first name arguments) := by
  induction first generalizing name arguments with
  | zero => simp [curried, resume, attachPrefix]
  | succ first ih =>
    have budget : first + 1 + later = first + later + 1 := by omega
    rw [budget]
    cases found : program name with
    | none => simp [curried, found, resume]
    | some body =>
      by_cases short : arguments.length < body.arity
      · simp [curried, found, short, resume]
      · by_cases ended : (arguments.drop body.arity).isEmpty = true
        · simp [curried, found, short, ended, resume, completed]
        · cases value : (body.run (arguments.take body.arity)).value with
          | data result => simp [curried, found, short, ended, value, resume]
          | closure target bound =>
            simp only [curried, found, if_neg short, if_neg ended, value]
            rw [ih]
            exact (resume_attach program later
              (body.run (arguments.take body.arity)).effects
              (body.run (arguments.take body.arity)).work
              (curried program first target (bound ++ arguments.drop body.arity))).symm

theorem resume_zero (program : Program Fn Arg Value Effect) (report : Report Fn Arg Value Effect) :
    resume program 0 report = report := by
  rcases report with ⟨status, effects, work⟩
  cases status <;> simp [resume, curried, attachPrefix]

theorem resume_add (program : Program Fn Arg Value Effect) (first later : Nat)
    (report : Report Fn Arg Value Effect) :
    resume program (first + later) report = resume program later (resume program first report) := by
  rcases report with ⟨status, effects, work⟩
  cases status with
  | done value => rfl
  | failed fault => rfl
  | paused name arguments =>
    change attachPrefix effects work (curried program (first + later) name arguments) =
      resume program later (attachPrefix effects work (curried program first name arguments))
    rw [curried_add, resume_attach]

namespace ResumeControls

def program : Program Nat Nat Nat String
  | 0 => some ⟨1, fun arguments => ⟨.closure 1 arguments, ["outer"], 1⟩⟩
  | 1 => some ⟨2, fun arguments => ⟨.data arguments.sum, ["inner"], 2⟩⟩
  | _ => none

def cut := curried program 1 0 [3, 4]

theorem paused_forwarding_keeps_the_changed_callable :
    cut = ⟨.paused 1 [3, 4], ["outer"], 1⟩ := by decide

theorem exact_resume_runs_the_outer_effect_only_once :
    resume program 1 cut = ⟨.done (.data 7), ["outer", "inner"], 3⟩ := by decide

theorem restarting_the_root_would_repeat_the_outer_effect :
    attachPrefix cut.effects cut.work (curried program 2 0 [3, 4]) =
      ⟨.done (.data 7), ["outer", "outer", "inner"], 4⟩ := by decide

def zeroArityLoop : Program Nat Nat Nat String
  | 0 => some ⟨0, fun _ => ⟨.closure 0 [], ["tick"], 1⟩⟩
  | _ => none

theorem zero_arity_forwarding_is_not_instant_arity_failure :
    batch zeroArityLoop 0 [99] = ⟨.failed (.over 0 0 1), [], 0⟩ ∧
      curried zeroArityLoop 3 0 [99] = ⟨.paused 0 [99], ["tick", "tick", "tick"], 3⟩ := by decide

end ResumeControls

end Mettapedia.Machines.OperatorChoice.OverApplication
