import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationEvolution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers

/-!
# Carrying actual computation states into an extended rule theory

Rule inclusion transports formed contexts, displayed types, typed rows and
the complete knowledge store. Solvability is derived by transporting its
actual solution. The present occurrences and raw labels stay the same.
Qualification of the new theory is a separate obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing

variable {Head L : Type} [UniverseLevel.LevelOrder L] {old next : Setting Head L}
  (inclusion : RulesSub old.R next.R)

include inclusion in
theorem formed_mono {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed old.R Γ) : CtxFormed next.R Γ := by
  induction formed with
  | nil => exact .nil
  | snoc _ type ih =>
    obtain ⟨levelHead, witness, typing⟩ := type
    exact .snoc ih ⟨levelHead, inclusion.isUniverse witness, TypedEquality.Normalization.Derivable.mono inclusion typing⟩

def context (Γ : Context old.R) : Context next.R := ⟨Γ.arity, Γ.raw, formed_mono inclusion Γ.formed⟩

def type {Γ : Context old.R} (annotation : TypeOver Γ) : TypeOver (context inclusion Γ) :=
  ⟨annotation.code, annotation.level, inclusion.isUniverse annotation.universeWitness,
    TypedEquality.Normalization.Derivable.mono inclusion annotation.formed⟩

def row {Γ : Context old.R} (value : TotalTerm Γ) : TotalTerm (context inclusion Γ) :=
  ⟨type inclusion value.1, ⟨value.2.code, TypedEquality.Normalization.Derivable.mono inclusion value.2.typed⟩⟩

def morphism {Γ Δ : Context old.R} (solution : Δ ⟶ Γ) : context inclusion Δ ⟶ context inclusion Γ :=
  ⟨solution.substitution, fun index => TypedEquality.Normalization.Derivable.mono inclusion (solution.typed index)⟩

def problem {Γ : Context old.R} (knowledge : EquationStore (TotalTerm Γ)) :
    EquationStore (TotalTerm (context inclusion Γ)) :=
  knowledge.map fun equation => (row inclusion equation.1, row inclusion equation.2)

theorem models {Γ Δ : Context old.R} (solution : Δ ⟶ Γ)
    {knowledge : EquationStore (TotalTerm Γ)} (solved : (frames old.levels).Models solution knowledge) :
    (frames next.levels).Models (morphism inclusion solution) (problem inclusion knowledge) := by
  apply (ContextualDependentEta.models_iff next.levels _ _).mpr
  intro equation member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨typeEqual, termEqual⟩ := (ContextualDependentEta.models_iff old.levels _ _).mp solved original originalMember
  obtain ⟨levelHead, witness, typeDerivation⟩ := typeEqual
  exact ⟨⟨levelHead, inclusion.isUniverse witness,
    TypedEquality.Normalization.Derivable.mono inclusion typeDerivation⟩,
    TypedEquality.Normalization.Derivable.mono inclusion termEqual⟩

theorem solvable {Γ : Context old.R} {knowledge : EquationStore (TotalTerm Γ)}
    (consistent : (frames old.levels).Solvable knowledge) :
    (frames next.levels).Solvable (problem inclusion knowledge) := by
  obtain ⟨observer, solution, solved⟩ := consistent
  exact ⟨context inclusion observer, morphism inclusion solution, models inclusion solution solved⟩

def state (source : State old.R Nat) : State next.R Nat :=
  ⟨context inclusion source.frame, problem inclusion source.knowledge, source.present,
    fun occurrence => row inclusion (source.label occurrence)⟩

def configuration (source : ComputationProfile.Configuration (S := old)) :
    ComputationProfile.Configuration (S := next) :=
  ⟨state inclusion source.state, source.active, source.present, solvable inclusion source.consistent⟩

theorem raw_code_unchanged (source : ComputationProfile.Configuration (S := old)) :
    (configuration inclusion source).code = source.code := rfl

theorem all_rows_kept (source : ComputationProfile.Configuration (S := old)) :
    (configuration inclusion source).state.present = source.state.present ∧
      ∀ occurrence, ((configuration inclusion source).state.label occurrence).2.code =
        (source.state.label occurrence).2.code := ⟨rfl, fun _ => rfl⟩

theorem declared_type_kept (source : ComputationProfile.Configuration (S := old)) :
    ((configuration inclusion source).state.label source.active).1.code =
      (source.state.label source.active).1.code := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory.models
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationTheory.solvable
