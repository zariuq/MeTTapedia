import Mettapedia.Machines.FunctionalCorrespondence
import Mettapedia.Machines.BoundedDeterministicRun

/-!
# Executable, classified runs of the source CEK and Krivine machines

Every driver follows the original transition function and retains its entire
state. A terminal literal with a pending Krivine argument is stuck, rather
than a successful result. A live transition at zero remaining fuel is
exhaustion. Fuel is a transition budget, not the reference evaluator's depth.
-/

set_option autoImplicit false

namespace Mettapedia.Machines

namespace CEK

def answer : St → Bool
  | ⟨.ret _, []⟩ => true
  | _ => false

def run (fuel : Nat) (state : St) : St := BoundedDeterministicRun.run step fuel state
def execute (fuel : Nat) (state : St) : BoundedDeterministicRun.Result St :=
  BoundedDeterministicRun.execute step answer fuel state

theorem run_steps (fuel : Nat) (state : St) : Steps state (run fuel state) :=
  BoundedDeterministicRun.run_reachable step fuel state

theorem execute_steps (fuel : Nat) (state : St) : Steps state (execute fuel state).state := by
  rw [execute, BoundedDeterministicRun.execute_state]
  exact run_steps fuel state

theorem completed_value (fuel : Nat) (state : St)
    (completed : (execute fuel state).outcome = .completed) :
    ∃ value, (execute fuel state).state = ⟨.ret value, []⟩ := by
  have accepted := (BoundedDeterministicRun.completed_is_answer step answer fuel state completed).2
  change answer (execute fuel state).state = true at accepted
  cases result : (execute fuel state).state with
  | mk control continuation =>
      rw [result] at accepted
      cases control with
      | ev term environment => simp [answer] at accepted
      | ret value =>
          cases continuation with
          | nil => exact ⟨value, rfl⟩
          | cons _ _ => simp [answer] at accepted

end CEK

namespace Krivine

def answer : KSt → Bool
  | ⟨.lam _, _, []⟩ => true
  | ⟨.lit _, _, []⟩ => true
  | _ => false

def run (fuel : Nat) (state : KSt) : KSt := BoundedDeterministicRun.run kstep fuel state
def execute (fuel : Nat) (state : KSt) : BoundedDeterministicRun.Result KSt :=
  BoundedDeterministicRun.execute kstep answer fuel state

theorem run_steps (fuel : Nat) (state : KSt) : KSteps state (run fuel state) :=
  BoundedDeterministicRun.run_reachable kstep fuel state

theorem execute_steps (fuel : Nat) (state : KSt) : KSteps state (execute fuel state).state := by
  rw [execute, BoundedDeterministicRun.execute_state]
  exact run_steps fuel state

theorem completed_presents (fuel : Nat) (state : KSt)
    (completed : (execute fuel state).outcome = .completed) :
    ∃ value, Presents value [] (execute fuel state).state := by
  have accepted := (BoundedDeterministicRun.completed_is_answer kstep answer fuel state completed).2
  change answer (execute fuel state).state = true at accepted
  cases result : (execute fuel state).state with
  | mk term environment stack =>
      rw [result] at accepted
      cases term <;> cases stack <;> simp [answer] at accepted
      · exact ⟨.clo _ environment, rfl⟩
      · exact ⟨.lit _, environment, rfl⟩

end Krivine

namespace FunctionalCorrespondenceRuns

def identity : Tm := .lam (.var 0)
def constant : Tm := .lam (.lam (.var 1))
def substitution : Tm := .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
def identityApplied : Tm := .app identity (.lit 7)
def constantApplied : Tm := .app (.app constant (.lit 7)) (.lit 9)
def substitutionApplied : Tm := .app (.app (.app substitution constant) constant) (.lit 7)
def capture : Tm := .app (.lam (.app (.lam (.var 1)) (.lit 22))) (.lit 11)
def failingArgument : Tm := .app (.lit 0) (.lit 1)
def discardFailure : Tm := .app (.lam (.lit 7)) failingArgument

def cek (fuel : Nat) (term : Tm) : BoundedDeterministicRun.Result CEK.St :=
  CEK.execute fuel ⟨.ev term [], []⟩

def krivine (fuel : Nat) (term : Tm) : BoundedDeterministicRun.Result Krivine.KSt :=
  Krivine.execute fuel ⟨term, [], []⟩

theorem identity_cek : (cek 32 identityApplied).state = ⟨.ret (.lit 7), []⟩ := rfl
theorem identity_krivine : (krivine 32 identityApplied).state = ⟨.lit 7, [], []⟩ := rfl
theorem constant_cek : (cek 32 constantApplied).state = ⟨.ret (.lit 7), []⟩ := rfl
theorem substitution_cek : (cek 128 substitutionApplied).state = ⟨.ret (.lit 7), []⟩ := rfl
theorem capture_cek : (cek 32 capture).state = ⟨.ret (.lit 11), []⟩ := rfl

theorem discarded_failure_differs :
    (cek 32 discardFailure).outcome = .stuck ∧ (krivine 32 discardFailure).outcome = .completed := by
  exact ⟨rfl, rfl⟩

theorem literal_application_stuck :
    (cek 32 failingArgument).outcome = .stuck ∧ (krivine 32 failingArgument).outcome = .stuck := by
  exact ⟨rfl, rfl⟩

theorem unfinished_is_exhausted :
    (cek 1 identityApplied).outcome = .exhausted ∧ (krivine 1 identityApplied).outcome = .exhausted := by
  exact ⟨rfl, rfl⟩

theorem terminal_at_zero_is_completed :
    (CEK.execute 0 ⟨.ret (.lit 3), []⟩).outcome = .completed ∧
    (Krivine.execute 0 ⟨.lit 3, [], []⟩).outcome = .completed := by
  exact ⟨rfl, rfl⟩

end FunctionalCorrespondenceRuns

end Mettapedia.Machines
