import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationReplay

/-!
# Computation under a binder and replay with the correct scope

The addition schema fires below a lambda. Its substitution uses the lambda's
bound variable, not a variable from the surrounding empty frame. A finite code
retains that scope and the original row ordinal. Substitution can introduce a
redex into a previously normal variable, so completed-answer evidence cannot
be transported merely because substitution preserves typing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.BinderControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (numC zeroC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)

abbrev setting := Controls.setting
abbrev qualified := Controls.qualified
abbrev presentation := Controls.presentation

def functionType (Γ : Context pkg) : TypeOver Γ :=
  ⟨.pi numC numC, TowerNumbersModel.u, LevelTower.IsUniverse.sort _,
    D.tower.pi_small D.num_typed D.num_typed⟩

def start : Configuration (S := setting) where
  state := ⟨empty pkg, [], {0}, fun _ => ⟨functionType (empty pkg),
    ⟨.lam (addC zeroC (.var 0)),
      .lamIntro (D.tower.pi_small D.num_typed D.num_typed) (LevelTower.IsUniverse.sort _)
        (TowerVectorsPrograms.add_typed level1 D.zero_typed (Derivable.var 0))⟩⟩⟩
  active := 0
  present := Finset.mem_singleton_self _
  consistent := ⟨empty pkg, 𝟙 _, Frames.models_nil _⟩

def action : ComputationSyntax.Action presentation 1 :=
  .declared (addC zeroC (.var 0)) (.var 0)
    (by
      change (⟨1, (addC zeroC (.var 0), .var 0)⟩ :
        Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ Vectors.vectorEquations
      decide)
    (fun index => .var index)

def instruction : Instruction presentation start := ⟨⟨1, .lam .hole, action⟩, rfl⟩

theorem fresh : 1 ∉ start.state.present := by decide

def finish := instruction.next qualified 1 fresh

def program : Execution qualified presentation start :=
  .cons instruction 1 fresh (.nil finish)

theorem lambda_computes : program.term = .lam (.var 0) := instruction.next_code qualified 1 fresh

theorem actual_binder_firing : program.toRun.word.length = 1 ∧
    Typed pkg .nil program.term (.pi numC numC) := ⟨rfl, program.typed.1⟩

local instance headPolicy : DecidableRel setting.R.headEq := Classical.decRel _

theorem table_same {arity : Nat} (left right : Tower.Tm arity) :
    presentation.schema left right ↔ Vectors.vectorEquations.family left right := Iff.rfl

def replayCode : ComputationReplay.Code (Head := Tower.Head) 0 :=
  .congLam (.root ⟨7, [.var 0]⟩)

def escapedCode : ComputationReplay.Code (Head := Tower.Head) 0 :=
  .root ⟨7, [zeroC]⟩

theorem binder_code_accepted :
    (ComputationReplay.read? presentation Vectors.vectorEquations table_same start replayCode).isSome = true := by
  decide +kernel

theorem wrong_scope_refused :
    (ComputationReplay.read? presentation Vectors.vectorEquations table_same start escapedCode).isSome = false := by
  decide +kernel

theorem substitution_exposes_redex :
    subst (fun _ : Fin 1 => (addC zeroC zeroC : Tower.Tm 0)) (.var 0 : Tower.Tm 1) = addC zeroC zeroC ∧
      StepCore pkg.computation pkg.headEq (addC zeroC zeroC : Tower.Tm 0) zeroC := by
  exact ⟨rfl, (Controls.zeroAction zeroC).sound⟩

theorem variable_normal : ConstructorSystem.Normal pkg (.var 0 : Tower.Tm 1) := by
  intro target reduction
  cases reduction with
  | root root => exact (Vectors.vectorConstructors level1).no_root_of_spineHead root rfl

theorem normality_not_substitution_stable :
    ConstructorSystem.Normal pkg (.var 0 : Tower.Tm 1) ∧
      ¬ ConstructorSystem.Normal pkg
        (subst (fun _ : Fin 1 => (addC zeroC zeroC : Tower.Tm 0)) (.var 0 : Tower.Tm 1)) :=
  ⟨variable_normal, fun normal => normal substitution_exposes_redex.2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.BinderControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.BinderControls.actual_binder_firing
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.BinderControls.binder_code_accepted
