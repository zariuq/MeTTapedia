import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Computation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.DirectedSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Progress
import Mettapedia.GSLT.Meredith.GSLT

/-!
# Directed evaluation by actual restricted native firings

The fixed descriptor program is restricted by a Boolean test of its decoded
action: head conversion is excluded. The source relation is the existing
directed reduction. Every admitted target firing reads back to one directed
step, and every directed step has an admitted firing of this fixed program.

The source arity is arbitrary and fixed along an execution; descriptors still
carry their changing inner arities under binders. The target retains the real
dependent state, its knowledge and its unique live computational occurrence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing ComputationProfile ComputationProgram
open LogicOverTheStep.StepSpan FragmentsOfTheStep.TransitionMaps

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (program : ComputationProgram.Program S.R) [DecidableRel S.R.headEq]
  (qualified : Qualified S)

/-- Permission inspects the decoded root-action tag, without a source-step premise. -/
def permits {state : State S.R Nat} (firing : Firing S.levels state) : Prop :=
  ∃ proposal : Proposal program state,
    DirectedSyntax.allowed proposal.event.action = true ∧ proposal.compile qualified = firing

def restricted := Spaces.restrict (step S.levels Nat).toStep (permits program qualified)

theorem permitted_in_full_program {state : State S.R Nat} {firing : Firing S.levels state}
    (allowed : permits program qualified firing) : ComputationProgram.permits program qualified firing := by
  obtain ⟨proposal, _, same⟩ := allowed
  exact ⟨proposal, same⟩

/-- An existing scoped instruction passing the action test has a finite decoded proposal.
The generated proposal has the same native take/make effect as that instruction. -/
theorem instruction_permitted {configuration : ComputationProfile.Configuration (S := S)}
    (instruction : Instruction program.presentation configuration)
    (allowed : DirectedSyntax.allowed instruction.event.action = true) (target : Nat) :
    permits program qualified (instruction.compile qualified target) := by
  have reduction := DirectedSyntax.event_reduces instruction.event allowed
  rw [instruction.source] at reduction
  obtain ⟨code, event, parsed, allowed', starts, ends⟩ :=
    DirectedSyntax.source_has_code program.presentation program.table program.same reduction
  let proposal : Proposal program configuration.state :=
    ⟨configuration.active, target, code, event, parsed, starts⟩
  refine ⟨proposal, allowed', ?_⟩
  have output : proposal.output qualified = instruction.output qualified := totalTerm_ext rfl ends
  change ComputationResources.firing S.levels configuration.state configuration.active target
      (proposal.output qualified) =
    ComputationResources.firing S.levels configuration.state configuration.active target (instruction.output qualified)
  exact congrArg (ComputationResources.firing S.levels configuration.state configuration.active target) output

def source (n : Nat) : GSLT := theoryOf (Tm Head n) (StrongNormalization.Reduces S.R)

abbrev target : GSLT := Execution.theory (restricted program qualified)

def Represents {n : Nat} (term : Tm Head n) (state : State S.R Nat) : Prop :=
  Computation.Represents (S := S) ⟨n, term⟩ state

omit [DecidableRel S.R.headEq] in
theorem represents_functional {n : Nat} {first second : Tm Head n} {state : State S.R Nat}
    (one : Represents (S := S) first state) (two : Represents (S := S) second state) : first = second :=
  eq_of_heq (Sigma.mk.inj (Computation.represents_functional one two)).2

theorem forward_step {n : Nat} {before after : Tm Head n} {state : State S.R Nat}
    (represented : Represents (S := S) before state) (reduction : (source (S := S) n).Step before after) :
    ∃ next, (target program qualified).Step state next ∧ Represents (S := S) after next := by
  obtain ⟨active, single, consistent, read⟩ := represented
  have arity : state.frame.arity = n := congrArg Sigma.fst read
  cases arity
  have termEq : (state.label active).2.code = before := eq_of_heq (Sigma.mk.inj read).2
  rw [← termEq] at reduction
  let configuration := singleConfiguration state active single consistent
  obtain ⟨code, event, parsed, allowed, starts, ends⟩ :=
    DirectedSyntax.source_has_code program.presentation program.table program.same reduction
  let proposal : Proposal program state :=
    ⟨active, configuration.fresh, code, event, parsed, starts⟩
  have fresh : proposal.target ∉ state.present := configuration.fresh_absent
  have present : proposal.source ∈ state.present := configuration.present
  have accepted : (restricted program qualified).Admits (proposal.compile qualified) :=
    ⟨(proposal.admitted_iff qualified).mpr ⟨present, fresh, consistent⟩,
      proposal, allowed, rfl⟩
  let instruction := proposal.instruction present consistent
  refine ⟨(restricted program qualified).result (proposal.compile qualified) accepted,
    ⟨proposal.compile qualified, accepted, rfl⟩, proposal.target,
    next_single program qualified single instruction proposal.target fresh,
    (instruction.next qualified proposal.target fresh).consistent, ?_⟩
  have codeAfter := congrArg (fun row : TotalTerm state.frame =>
    (⟨state.frame.arity, row.2.code⟩ : Σ n : Nat, Tm Head n))
    (ComputationResources.result_label S.levels state proposal.source proposal.target
      (proposal.output qualified) accepted.1)
  exact codeAfter.trans (congrArg (Sigma.mk state.frame.arity) ends)

theorem backward_step {n : Nat} {before : Tm Head n} {state next : State S.R Nat}
    (represented : Represents (S := S) before state) (fired : (target program qualified).Step state next) :
    ∃ after, (source (S := S) n).Step before after ∧ Represents (S := S) after next := by
  obtain ⟨active, single, consistent, read⟩ := represented
  have arity : state.frame.arity = n := congrArg Sigma.fst read
  cases arity
  have termEq : (state.label active).2.code = before := eq_of_heq (Sigma.mk.inj read).2
  obtain ⟨firing, accepted, rfl⟩ := fired
  obtain ⟨proposal, allowed, same⟩ := accepted.2
  subst firing
  have shape := (proposal.admitted_iff qualified).mp accepted.1
  have sourceEq : proposal.source = active := by
    have present := shape.1
    rw [single] at present
    exact Finset.mem_singleton.mp present
  have directed := DirectedSyntax.event_reduces proposal.event allowed
  rw [proposal.aligned, sourceEq, termEq] at directed
  let instruction := proposal.instruction shape.1 consistent
  have singleSource : state.present = {proposal.source} := sourceEq.symm ▸ single
  refine ⟨proposal.event.target, directed, proposal.target,
    next_single program qualified singleSource instruction proposal.target shape.2.1,
    (instruction.next qualified proposal.target shape.2.1).consistent, ?_⟩
  exact congrArg (fun row : TotalTerm state.frame =>
    (⟨state.frame.arity, row.2.code⟩ : Σ n : Nat, Tm Head n))
    (ComputationResources.result_label S.levels state proposal.source proposal.target
      (proposal.output qualified) accepted.1)

def correspondence (n : Nat) :
    OperationalCorrespondence (source (S := S) n) (target program qualified) where
  related := Represents
  readStep represented fired := .inr (backward_step program qualified represented fired)
  forward represented reduction := by
    obtain ⟨next, fired, nextRelated⟩ := forward_step program qualified represented reduction
    exact ⟨next, ⟨.cons ⟨fired⟩ (.refl next)⟩, nextRelated⟩

def progress (n : Nat) : Progress.Certificate (correspondence program qualified n).toOperationalReadback :=
  Progress.Certificate.ofReflection (backward_step program qualified)

theorem positive_forward {n : Nat} {before after : Tm Head n} {state : State S.R Nat}
    (represented : Represents (S := S) before state) (reduction : (source (S := S) n).Step before after) :
    ∃ next, ∃ path : ExecutionPath (target program qualified) state next,
      0 < path.length ∧ Represents (S := S) after next := by
  obtain ⟨next, fired, nextRelated⟩ := forward_step program qualified represented reduction
  exact ⟨next, .cons ⟨fired⟩ (.refl next), by change 0 < 1; decide, nextRelated⟩

theorem normalization_iff {n : Nat} {before : Tm Head n} {state : State S.R Nat}
    (represented : Represents (S := S) before state) :
    Acc (fun after origin => StrongNormalization.Reduces S.R origin after) before ↔
      Acc (fun next current => (target program qualified).Step current next) state :=
  Progress.normalization_iff (correspondence program qualified n) (progress program qualified n)
    (positive_forward program qualified) represented

/-- The executable profile's stopping contract is exactly directed normality. -/
theorem normal_iff_no_firing {n : Nat} {before : Tm Head n} {state : State S.R Nat}
    (represented : Represents (S := S) before state) :
    ContextualDependentExecutableJoin.Normal S.R before ↔
      ¬ ∃ firing : Firing S.levels state, (restricted program qualified).Admits firing := by
  constructor
  · rintro normal ⟨firing, accepted⟩
    obtain ⟨after, reduced, _⟩ := backward_step program qualified represented ⟨firing, accepted, rfl⟩
    exact normal after reduced
  · intro stopped after reduction
    obtain ⟨next, fired, _⟩ := forward_step program qualified represented reduction
    obtain ⟨firing, accepted, _⟩ := fired
    exact stopped ⟨firing, accepted⟩

omit [DecidableRel S.R.headEq] in
theorem multiStep_iff {n : Nat} {before after : Tm Head n} :
    (source (S := S) n).MultiStep before after ↔ StrongNormalization.ReducesStar S.R before after :=
  Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen (source (S := S) n) before after

theorem observed_runs_iff {n : Nat} (observe : Tm Head n → Prop)
    {before : Tm Head n} {state : State S.R Nat} (represented : Represents (S := S) before state) :
    (∃ after, StrongNormalization.ReducesStar S.R before after ∧ observe after) ↔
      ∃ run : (restricted program qualified).Run state,
        ∃ after, Represents (S := S) after run.last ∧ observe after := by
  have transported := (correspondence program qualified n).reachable_iff observe
    (fun state => ∃ term, Represents (S := S) term state ∧ observe term) (by
      intro term current related
      constructor
      · exact fun observed => ⟨term, related, observed⟩
      · rintro ⟨other, otherRelated, observed⟩
        exact (represents_functional otherRelated related) ▸ observed) represented
  have actualRuns := transported.trans (Execution.reachable_iff_run (restricted program qualified) _ state)
  constructor
  · rintro ⟨after, steps, observed⟩
    exact actualRuns.mp ⟨after, multiStep_iff.mpr steps, observed⟩
  · rintro ⟨run, after, related, observed⟩
    obtain ⟨last, steps, holds⟩ := actualRuns.mpr ⟨run, after, related, observed⟩
    exact ⟨last, multiStep_iff.mp steps, holds⟩

/-- Directed answers are exactly final normal readouts of actual native runs of this restriction. -/
theorem answers_by_run_iff {n : Nat} {before value : Tm Head n} {state : State S.R Nat}
    (represented : Represents (S := S) before state) :
    DirectedAnswers.DirectedAnswer S.R before value ↔
      ∃ run : (restricted program qualified).Run state,
        Represents (S := S) value run.last ∧ ContextualDependentExecutableJoin.Normal S.R value := by
  have observed := observed_runs_iff program qualified
    (fun term => term = value ∧ ContextualDependentExecutableJoin.Normal S.R term) represented
  constructor
  · rintro ⟨steps, normal⟩
    obtain ⟨run, after, related, same, finalNormal⟩ := observed.mp ⟨value, steps, rfl, normal⟩
    subst after
    exact ⟨run, related, finalNormal⟩
  · rintro ⟨run, related, normal⟩
    obtain ⟨after, steps, same, finalNormal⟩ := observed.mpr ⟨run, value, related, rfl, normal⟩
    subst after
    exact ⟨steps, finalNormal⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed.normalization_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Directed.answers_by_run_iff
