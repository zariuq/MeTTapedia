import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProtectedParameters
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedVariables
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability

/-!
# Protected parameters, delayed checks and transported absence
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def rigid (name : Nat) : Prop := name = 0

instance : DecidablePred rigid := fun name => inferInstanceAs (Decidable (name = 0))

/-- A shared caller variable can be bound to a rigid parameter. -/
theorem shared_variable_can_refer_to_rigid_parameter : ∃ answer,
    RigidUnification.solve rigid [(Term.var (σ := signature) 0, .var 1)] = some answer := by
  apply RigidUnification.solve_complete (σ := signature)
  refine ⟨Subst.single 1 (.var 0), ?_, ?_⟩
  · intro name isRigid
    have same : name = 0 := isRigid
    subst name
    rfl
  · intro equation member
    have same : equation = (Term.var (σ := signature) 0, Term.var (σ := signature) 1) := by
      simpa using member
    subst equation
    rfl

/-- Unification cannot change that same rigid parameter into a constant. -/
theorem rigid_parameter_cannot_be_assigned :
    RigidUnification.solve rigid [(Term.var (σ := signature) 0, .const 0)] = none := by
  apply (RigidUnification.solve_none_iff (σ := signature) rigid _).mpr
  rintro ⟨answer, fixed, solved⟩
  have same := solved (Term.var 0, .const 0) (by simp)
  have protectedValue := fixed 0 rfl
  change answer 0 = .const 0 at same
  rw [protectedValue] at same
  cases same

theorem unresolved_absence_stays_pending (probe : Check (Term signature) → Option Bool)
    (sound : Check.ProbeSound A [] label {1} probe) :
    probe (.absent (.const 0)) = none :=
  Check.unresolved_not_discharged A sound
    ⟨open_absence_is_not_entailed, open_presence_is_not_entailed⟩

theorem accepting_every_unbound_check_is_unsound :
    ¬ Check.ProbeSound A [] label {1} (fun _ => some true) := by
  intro sound
  have pending := unresolved_absence_stays_pending _ sound
  cases pending

def blockerLabel (_ : Nat) : Term signature := .const 0

/-- Consuming one blocker and then checking absence retains exactly the
original single-occurrence condition, even with duplicate-valued blockers. -/
theorem absence_after_consumption_is_exact (world : Finset Nat) (present : 3 ∈ world) :
    A.Entails [] (fun σ => (Check.absent (.const 0)).Holds A σ blockerLabel
      (fire world (Commit.takeOne 3 : Commit Nat (Term signature)))) ↔ world = {3} := by
  constructor
  · intro entailed
    apply Finset.Subset.antisymm
    · intro o member
      by_contra notSingleton
      have different : o ≠ 3 := by simpa using notSingleton
      have survives : o ∈ fire world (Commit.takeOne 3 : Commit Nat (Term signature)) := by
        simp [fire, Commit.takeOne, member, different]
      exact entailed zero (A.models_nil zero) o survives rfl
    · exact Finset.singleton_subset_iff.mpr present
  · intro same
    subst world
    intro σ model o member
    simp [fire, Commit.takeOne] at member

theorem duplicate_valued_blocker_prevents_absence :
    ¬ A.Entails [] (fun σ => (Check.absent (.const 0)).Holds A σ blockerLabel
      (fire {3, 7} (Commit.takeOne 3 : Commit Nat (Term signature)))) := by
  rw [absence_after_consumption_is_exact _ (by simp)]
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls
