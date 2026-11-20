import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationResources
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Qualification

/-!
# A syntactically pinned computational profile of the dependent full step

An instruction selects a scoped primitive redex or declared equation from
the independent schema presentation. Its only source alignment field is a
literal syntax equality. Qualified subject reduction derives the output
typing. Compilation then constructs the actual take/make firing, whose
admission and resource effects are proved independently.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (qualified : Qualified S) (presentation : SchemaPresentation S.R)

structure Configuration where
  state : State S.R Nat
  active : Nat
  present : active ∈ state.present
  consistent : (frames S.levels).Solvable state.knowledge

def Configuration.code (configuration : Configuration (S := S)) : Tm Head configuration.state.frame.arity :=
  (configuration.state.label configuration.active).2.code

structure Instruction (configuration : Configuration (S := S)) where
  event : ComputationSyntax.Event presentation configuration.state.frame.arity
  source : event.source = configuration.code

variable {presentation}

theorem Instruction.reduction {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) :
    StepCore S.R.computation S.R.headEq configuration.code instruction.event.target := by
  have reduction := instruction.event.sound
  rwa [instruction.source] at reduction

def Instruction.output {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) : TotalTerm configuration.state.frame :=
  ⟨(configuration.state.label configuration.active).1,
    ⟨instruction.event.target,
      (qualified.subjectReduction configuration.state.frame.formed (.single instruction.reduction)
        (configuration.state.label configuration.active).2.typed).1⟩⟩

def Instruction.compile {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) (target : Nat) : Firing S.levels configuration.state :=
  ComputationResources.firing S.levels configuration.state configuration.active target (instruction.output qualified)

theorem Instruction.admitted_iff {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) (target : Nat) :
    (step S.levels Nat).Admits (instruction.compile qualified target) ↔ target ∉ configuration.state.present := by
  unfold Instruction.compile
  rw [ComputationResources.admitted_iff]
  exact ⟨fun h => h.2.1, fun fresh => ⟨configuration.present, fresh, configuration.consistent⟩⟩

def Configuration.fresh (configuration : Configuration (S := S)) : Nat :=
  configuration.state.present.sup id + 1

theorem Configuration.fresh_not_present (configuration : Configuration (S := S)) :
    configuration.fresh ∉ configuration.state.present := by
  intro member
  have bound : configuration.fresh ≤ configuration.state.present.sup id := Finset.le_sup (f := id) member
  unfold Configuration.fresh at bound
  omega

theorem source_complete {configuration : Configuration (S := S)} {result : Tm Head configuration.state.frame.arity}
    (reduction : StepCore S.R.computation S.R.headEq configuration.code result) :
    ∃ instruction : Instruction presentation configuration, instruction.event.target = result := by
  obtain ⟨event, source, target⟩ := ComputationSyntax.complete presentation reduction
  exact ⟨⟨event, source⟩, target⟩

theorem source_realized {configuration : Configuration (S := S)} {result : Tm Head configuration.state.frame.arity}
    (reduction : StepCore S.R.computation S.R.headEq configuration.code result) :
    ∃ instruction : Instruction presentation configuration,
      instruction.event.target = result ∧
      (step S.levels Nat).Admits (instruction.compile qualified configuration.fresh) := by
  obtain ⟨instruction, target⟩ := source_complete (presentation := presentation) reduction
  exact ⟨instruction, target, (instruction.admitted_iff qualified _).mpr configuration.fresh_not_present⟩

theorem instruction_reflects {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) (target : Nat)
    (accepted : (step S.levels Nat).Admits (instruction.compile qualified target)) :
    StepCore S.R.computation S.R.headEq configuration.code
      (((step S.levels Nat).toStep.result (instruction.compile qualified target) accepted).label target).2.code := by
  have same := ComputationResources.result_label S.levels configuration.state configuration.active target
    (instruction.output qualified) accepted
  have code := congrArg (fun row : TotalTerm configuration.state.frame => row.2.code) same
  exact code.symm ▸ instruction.reduction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.source_realized
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.instruction_reflects
