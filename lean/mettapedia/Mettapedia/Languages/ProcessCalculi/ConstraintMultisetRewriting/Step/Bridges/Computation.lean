import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Progress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProgramStreams

/-!
# The fixed descriptor program as an operational correspondence

Both sides are existing relations: scoped package reduction and admitted
firings of the fixed descriptor restriction of the dependent full step.
The relation reads the unique live computational row; it retains the actual
knowledge and requires its solvability. Every target step, not only a
selected implementation, reads back to one source step.

The source here includes head conversion. This adapter does not identify
that relation with directed evaluation, nor the descriptor program with an
ordinary rule-syntax compilation. Choice multiplicity is not claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Computation

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing ComputationProfile ComputationProgram
open LogicOverTheStep.StepSpan FragmentsOfTheStep.TransitionMaps

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (program : ComputationProgram.Program S.R) [DecidableRel S.R.headEq] [DecidableEq Head]
  (qualified : Qualified S)

abbrev Code := Σ n : Nat, Tm Head n

def source : GSLT := theoryOf (Code (Head := Head)) (Stream.ScopedStep (S := S))

abbrev target : GSLT := Execution.theory (restricted program qualified)

def Represents (code : Code (Head := Head)) (state : State S.R Nat) : Prop :=
  ∃ active : Nat, state.present = {active} ∧ (frames S.levels).Solvable state.knowledge ∧
    readout state active = code

omit [DecidableRel S.R.headEq] [DecidableEq Head] in
theorem represents_configuration (configuration : ComputationProfile.Configuration (S := S))
    (single : configuration.state.present = {configuration.active}) :
    Represents (S := S) ⟨configuration.state.frame.arity, configuration.code⟩ configuration.state :=
  ⟨configuration.active, single, configuration.consistent, rfl⟩

omit [DecidableRel S.R.headEq] [DecidableEq Head] in
theorem represents_functional {first second : Code (Head := Head)} {state : State S.R Nat}
    (one : Represents (S := S) first state) (two : Represents (S := S) second state) : first = second := by
  obtain ⟨a, singleA, _, readA⟩ := one
  obtain ⟨b, singleB, _, readB⟩ := two
  have same : a = b := Finset.singleton_injective (singleA.symm.trans singleB)
  subst b
  exact readA.symm.trans readB

theorem forward_step {before after : Code (Head := Head)} {state : State S.R Nat}
    (represented : Represents (S := S) before state) (reduction : (source (S := S)).Step before after) :
    ∃ next, (target program qualified).Step state next ∧ Represents (S := S) after next := by
  obtain ⟨active, single, consistent, read⟩ := represented
  rw [← read] at reduction
  obtain ⟨n, left, right, beforeEq, afterEq, step⟩ := reduction
  have arity : state.frame.arity = n := congrArg Sigma.fst beforeEq
  cases arity
  have termEq : (state.label active).2.code = left := eq_of_heq (Sigma.mk.inj beforeEq).2
  rw [← termEq] at step
  let configuration := singleConfiguration state active single consistent
  obtain ⟨instruction, output⟩ := source_complete (presentation := program.presentation)
    (configuration := configuration) step
  let fresh := configuration.fresh
  have missing : fresh ∉ state.present := configuration.fresh_not_present
  have accepted : (restricted program qualified).Admits (instruction.compile qualified fresh) :=
    ⟨(instruction.admitted_iff qualified fresh).mpr missing,
      instruction_permitted program qualified instruction fresh⟩
  refine ⟨(instruction.next qualified fresh missing).state,
    ⟨instruction.compile qualified fresh, accepted, rfl⟩, fresh,
    next_single program qualified single instruction fresh missing,
    (instruction.next qualified fresh missing).consistent, ?_⟩
  have readNext := congrArg (Sigma.mk state.frame.arity)
    (instruction.next_code qualified fresh missing)
  exact readNext.trans ((congrArg (Sigma.mk state.frame.arity) output).trans afterEq.symm)

omit [DecidableEq Head] in
theorem backward_step {before : Code (Head := Head)} {state next : State S.R Nat}
    (represented : Represents (S := S) before state) (fired : (target program qualified).Step state next) :
    ∃ after, (source (S := S)).Step before after ∧ Represents (S := S) after next := by
  obtain ⟨active, single, consistent, read⟩ := represented
  obtain ⟨firing, accepted, rfl⟩ := fired
  obtain ⟨proposal, same⟩ := accepted.2
  subst firing
  have shape := (proposal.admitted_iff qualified).mp accepted.1
  have sourceEq : proposal.source = active := by
    have member := shape.1
    rw [single] at member
    exact Finset.mem_singleton.mp member
  subst active
  let instruction := proposal.instruction shape.1 consistent
  have afterSingle := next_single program qualified single instruction proposal.target shape.2.1
  have afterConsistent := (instruction.next qualified proposal.target shape.2.1).consistent
  refine ⟨readout ((restricted program qualified).result (proposal.compile qualified) accepted) proposal.target,
    ?_, proposal.target, afterSingle, afterConsistent, rfl⟩
  rw [← read]
  exact firing_readout program qualified accepted single afterSingle

/-- The native program, with its actual intermediate states, supplies both
laws of the existing finite operational correspondence. -/
def correspondence : OperationalCorrespondence (source (S := S)) (target program qualified) where
  related := Represents
  readStep represented fired := .inr (backward_step program qualified represented fired)
  forward represented reduction := by
    obtain ⟨next, fired, representedNext⟩ := forward_step program qualified represented reduction
    exact ⟨next, ⟨.cons ⟨fired⟩ (.refl next)⟩, representedNext⟩

theorem positive_forward {before after : Code (Head := Head)} {state : State S.R Nat}
    (represented : Represents (S := S) before state) (reduction : (source (S := S)).Step before after) :
    ∃ next, ∃ path : ExecutionPath (target program qualified) state next,
      path.length = 1 ∧ Represents (S := S) after next := by
  obtain ⟨next, fired, representedNext⟩ := forward_step program qualified represented reduction
  exact ⟨next, .cons ⟨fired⟩ (.refl next), rfl, representedNext⟩

/-- Reflection exposes one source step on every actual target step, so
this program has no administrative transition to hide. -/
def progress : Progress.Certificate (correspondence program qualified).toOperationalReadback :=
  Progress.Certificate.ofReflection (backward_step program qualified)

theorem normalization_iff {before : Code (Head := Head)} {state : State S.R Nat}
    (represented : Represents (S := S) before state) :
    Acc (fun after before => (source (S := S)).Step before after) before ↔
      Acc (fun next state => (target program qualified).Step state next) state := by
  apply Progress.normalization_iff (correspondence program qualified) (progress program qualified)
    (related := represented)
  intro origin after current related stepped
  obtain ⟨next, path, length, representedNext⟩ := positive_forward program qualified related stepped
  exact ⟨next, path, by rw [length]; decide, representedNext⟩

/-- A property of the literal result code has exactly the same reachable
answers on source reductions and actual admitted target runs. -/
theorem observed_runs_iff (observes : Code (Head := Head) → Prop)
    {before : Code (Head := Head)} {state : State S.R Nat}
    (represented : Represents (S := S) before state) :
    (∃ after, (source (S := S)).MultiStep before after ∧ observes after) ↔
      ∃ run : (restricted program qualified).Run state,
        ∃ after, Represents (S := S) after run.last ∧ observes after := by
  have transported := (correspondence program qualified).reachable_iff observes
    (fun state => ∃ code, Represents (S := S) code state ∧ observes code) (by
      intro code current related
      constructor
      · intro observed
        exact ⟨code, related, observed⟩
      · rintro ⟨other, otherRelated, observed⟩
        exact (represents_functional otherRelated related) ▸ observed) represented
  exact transported.trans (Execution.reachable_iff_run (restricted program qualified) _ state)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Computation

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Computation.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Computation.observed_runs_iff
