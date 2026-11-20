import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Readings

/-!
# A verified interpreter, its full-step execution, and a dependent consumer

The interpreter is the existing typed-syntax package, whose object expressions
are represented extrinsically. Its independent reduction computes two plus
three to five. The general compilation theorem realizes that reduction as
actual dependent full-step firings. The later proof has a type mentioning
the interpreter call, rather than only its printed answer.

The finite budget control is not a normalization theorem: a short run returns
no result even though the semantic computation has an answer. Six is refused
as an answer by the independent source semantics and by the target profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (U0 numC)
open TowerSyntaxModel (valC tnumC evalC addE litE)

abbrev level := Syntax.L0
abbrev package := TowerSyntaxModel.rules level
abbrev setting := TowerSyntaxModel.setting level (fun _ => 0)
abbrev qualified := Syntax.sq level
abbrev presentation := Syntax.syntaxPresentation level

abbrev number {n : Nat} (value : Nat) : Tower.Tm n := TowerSyntaxModel.numeral value

def call {n : Nat} : Tower.Tm n :=
  evalC tnumC (addE (litE (number 2)) (litE (number 3)))

theorem call_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed package Γ call (valC tnumC) :=
  TowerSyntaxModel.eval_typed level (TowerSyntaxModel.tnum_typed level)
    (TowerSyntaxModel.add_typed level
      (TowerSyntaxModel.lit_typed level (TowerSyntaxModel.numeral_typed level 2))
      (TowerSyntaxModel.lit_typed level (TowerSyntaxModel.numeral_typed level 3)))

def valueType (Γ : Context package) : TypeOver Γ :=
  ⟨valC tnumC, .sort (.const 0), LevelTower.IsUniverse.sort _,
    TowerSyntaxModel.val_typed level (TowerSyntaxModel.tnum_typed level)⟩

def start : Configuration (S := setting) where
  state := ⟨empty package, [], {0}, fun _ => ⟨valueType (empty package), ⟨call, call_typed⟩⟩⟩
  active := 0
  present := Finset.mem_singleton_self _
  consistent := ⟨empty package, 𝟙 _, Frames.models_nil _⟩

theorem interpreter_has_full_run :
    ∃ run : (step setting.levels Nat).toStep.Run start.state,
      ∃ profile : RunProfile qualified presentation start run,
        profile.execution.term = number 5 ∧
          ConstructorSystem.Normal package profile.execution.term :=
  (full_answers_iff qualified presentation).mp Syntax.eval_answer

theorem interpreter_never_answers_six :
    ¬ ∃ run : (step setting.levels Nat).toStep.Run start.state,
      ∃ profile : RunProfile qualified presentation start run,
        profile.execution.term = number 6 ∧
          ConstructorSystem.Normal package profile.execution.term := by
  intro wrong
  exact Syntax.eval_not_six ((full_answers_iff qualified presentation).mpr wrong)

theorem exhausted_but_answered :
    Syntax.syntaxNormalize level 3 (call : Tower.Tm 0) = none ∧
      ∃ run : (step setting.levels Nat).toStep.Run start.state,
        ∃ profile : RunProfile qualified presentation start run,
          profile.execution.term = number 5 ∧
            ConstructorSystem.Normal package profile.execution.term :=
  ⟨Syntax.eval_budget, interpreter_has_full_run⟩

def claim {n : Nat} : Tower.Tm n := .id numC call (number 5)

theorem claim_formed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed package Γ claim U0 :=
  .idForm (TowerSyntaxModel.num_typed level) (LevelTower.IsUniverse.sort _)
    (.conv call_typed (TowerSyntaxModel.val_tnum_eq level) (LevelTower.IsUniverse.sort _))
    (TowerSyntaxModel.numeral_typed level 5)

/-- This later consumer uses computation in its displayed type. -/
theorem proof_typed (Γ : Context package) :
    Typed package Γ.raw (.refl (number 5)) claim :=
  .conv (.reflIntro (TowerSyntaxModel.numeral_typed level 5))
    (.idCong (.refl (TowerSyntaxModel.num_typed level)) (LevelTower.IsUniverse.sort _)
      (TowerSyntaxModel.eval_two_plus_three level Γ.formed).2.symm
      (.refl (TowerSyntaxModel.numeral_typed level 5)))
    (LevelTower.IsUniverse.sort _)

def claimType (Γ : Context package) : TypeOver Γ :=
  ⟨claim, .sort (.const 0), LevelTower.IsUniverse.sort _, claim_formed⟩

def proofRow (Γ : Context package) : TotalTerm Γ :=
  ⟨claimType Γ, ⟨.refl (number 5), proof_typed Γ⟩⟩

theorem consumer_type_really_mentions_call :
    (proofRow (empty package)).1.code = .id numC start.code (number 5) := rfl

theorem consumer_exists_after_actual_execution :
    ∃ run : (step setting.levels Nat).toStep.Run start.state,
      ∃ profile : RunProfile qualified presentation start run,
        profile.execution.term = number 5 ∧
          Typed package run.last.frame.raw
            (proofRow run.last.frame).2.code (proofRow run.last.frame).1.code := by
  obtain ⟨run, profile, same, _⟩ := interpreter_has_full_run
  exact ⟨run, profile, same, (proofRow run.last.frame).2.typed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer.interpreter_has_full_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer.proof_typed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer.exhausted_but_answered
