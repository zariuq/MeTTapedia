import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationHeadBoundary

/-!
# A raw firing does not uniquely determine its scoped source profile

Two different head-equality steps occur in the left and right fields of one
typed pair. Their contexts differ, but both compile to the same raw firing
because the complete source and target rows coincide. The two actual
RunProfiles are distinct. This is separate from the duplicate table-ordinal
control, which distinguishes retained source origins rather than contexts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Ambiguity

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (U0)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D)

abbrev setting := Controls.setting
abbrev qualified := Controls.qualified
abbrev presentation := Controls.presentation

def U1 {n : Nat} : Tower.Tm n := .head (.sort (.succ (.const 0)))

theorem pair_typed : Typed pkg .nil (.pair U0 U0) (.sigma U1 U1) :=
  .pairIntro
    (.sigmaForm (.headType (.sort _)) (LevelTower.IsUniverse.sort _)
      (.headType (.sort _)) (LevelTower.IsUniverse.sort _) (.sorts _ _))
    (LevelTower.IsUniverse.sort _) D.tower.u0_typed D.tower.u0_typed

def input : Configuration (S := setting) := Configuration.ofTyped (empty pkg) pair_typed

def left : Instruction presentation input :=
  ⟨⟨0, .pairFst .hole U0,
    .head (.sort (.const 0)) (.sort (.const 0)) HeadBoundary.head_reflexive⟩, rfl⟩

def right : Instruction presentation input :=
  ⟨⟨0, .pairSnd U0 .hole,
    .head (.sort (.const 0)) (.sort (.const 0)) HeadBoundary.head_reflexive⟩, rfl⟩

theorem fresh : 1 ∉ input.state.present := by decide

def leftExecution : Execution qualified presentation input :=
  .cons left 1 fresh (.nil (left.next qualified 1 fresh))

def rightExecution : Execution qualified presentation input :=
  .cons right 1 fresh (.nil (right.next qualified 1 fresh))

theorem raw_firings_agree : left.compile qualified 1 = right.compile qualified 1 := rfl

theorem raw_runs_agree : leftExecution.toRun = rightExecution.toRun := rfl

def contextSide {n m : Nat} : ComputationSyntax.Context Tower.Head n m → Bool
  | .pairFst _ _ => false
  | _ => true

def profileSide {configuration : Configuration (S := setting)}
    {run : (step setting.levels Nat).toStep.Run configuration.state} :
    RunProfile qualified presentation configuration run → Bool
  | .nil _ => false
  | .cons instruction _ _ _ => contextSide instruction.event.context

theorem two_profiles_differ : leftExecution.profile ≠ rightExecution.profile := by
  intro same
  have impossible : false = true := congrArg profileSide same
  cases impossible

theorem raw_profile_uniqueness_false :
    ¬ Subsingleton (RunProfile qualified presentation input leftExecution.toRun) := by
  intro unique
  exact two_profiles_differ (@Subsingleton.elim _ unique leftExecution.profile rightExecution.profile)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Ambiguity

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Ambiguity.raw_profile_uniqueness_false
