import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationInputs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationControls

/-!
# The source programs used by the context-certificate experiment

Every program pairs a locally reduced addition chain with a fixed vector.
The same independently typed source programs and answers are used by both
certificate representations. The general bridge supplies actual full-step
runs for every size. The experiment measures the scope-compatibility part of
class-certificate reuse, not the entire dependent type checker or runtime.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Programs

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (numC zeroC succC ttC addC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D level1)
open ComputationProfile

abbrev setting := ComputationProfile.Controls.setting
abbrev qualified := ComputationProfile.Controls.qualified
abbrev presentation := ComputationProfile.Controls.presentation

def number {n : Nat} : Nat → Tower.Tm n
  | 0 => zeroC
  | size + 1 => succC (number size)

def payload {n : Nat} : Nat → Tower.Tm n
  | 0 => ttC
  | size + 1 => .pair zeroC (payload size)

def localTerm {n : Nat} : Nat → Tower.Tm n
  | 0 => zeroC
  | count + 1 => addC zeroC (localTerm count)

def context (size : Nat) : ComputationSyntax.Context Tower.Head 0 0 :=
  .pairFst .hole (payload size)

def program (size count : Nat) : Tower.Tm 0 := (context size).plug (localTerm count)

theorem number_subst {n m : Nat} (σ : Sub Tower.Head n m) :
    ∀ size, subst σ (number size) = number size := by
  intro size
  induction size with
  | zero => rfl
  | succ size ih => simp [number, succC, subst, ih]

theorem number_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    ∀ size, Typed pkg Γ (number size) numC
  | 0 => D.zero_typed
  | size + 1 => D.succ_typed (number_typed size)

theorem payload_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    ∀ size, Typed pkg Γ (payload size) (vecC numC (number size))
  | 0 => D.nil_typed D.num_typed
  | size + 1 => D.cons_typed D.num_typed (number_typed size) D.zero_typed (payload_typed size)

theorem local_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    ∀ count, Typed pkg Γ (localTerm count) numC
  | 0 => D.zero_typed
  | count + 1 => TowerVectorsPrograms.add_typed level1 D.zero_typed (local_typed count)

theorem program_typed (size count : Nat) :
    Typed pkg .nil (program size count) (.sigma numC (vecC numC (number size))) := by
  refine .pairIntro (D.tower.sigma_small D.num_typed (D.vec_typed D.num_typed (number_typed size)))
    (LevelTower.IsUniverse.sort _) (local_typed count) ?_
  simpa only [inst0, subst, vecC, numC, number_subst] using (payload_typed (Γ := .nil) size)

theorem local_step (count : Nat) :
    StepCore pkg.computation pkg.headEq (localTerm (count + 1) : Tower.Tm 0) (localTerm count) :=
  (ComputationProfile.Controls.zeroAction (localTerm count)).sound

theorem program_reduces (size : Nat) :
    ∀ count, ConversionCoherence.StepStar pkg (program size count) (program size 0)
  | 0 => .refl
  | count + 1 => (program_reduces size count).head (.congPairFst (local_step count))

theorem payload_normal {n : Nat} : ∀ size, ConstructorSystem.Normal pkg (payload size : Tower.Tm n)
  | 0 => Vectors.const_normal level1 (by decide)
  | size + 1 => Vectors.pair_normal level1 (Vectors.const_normal level1 (by decide)) (payload_normal size)

theorem program_answer (size count : Nat) : Answer pkg (program size count) (program size 0) :=
  ⟨program_reduces size count,
    Vectors.pair_normal level1 (Vectors.const_normal level1 (by decide)) (payload_normal size)⟩

noncomputable def input (size count : Nat) : ComputationProfile.Configuration (S := setting) :=
  ComputationProfile.Configuration.ofTyped (empty pkg) (program_typed size count)

theorem program_has_actual_run (size count : Nat) :
    ∃ run : (step setting.levels Nat).toStep.Run (input size count).state,
      ∃ profile : RunProfile qualified presentation (input size count) run,
        profile.execution.term = program size 0 ∧ ConstructorSystem.Normal pkg profile.execution.term :=
  (full_answers_iff qualified presentation (configuration := input size count)).mp
    (program_answer size count)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Programs

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Programs.program_has_actual_run
