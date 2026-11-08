import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReductionBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualComparison

/-!
# Normalizing the newest declaration through typed context comparison

The original annotation is independently formed. Reduction retains its
universe metadata and earns typed equality with the normal annotation.
The existing extension comparison gives inverse context maps; transporting
the complete equation store preserves all future solutions and obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDeclarationNormalization

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

structure Normalized (root : ExecutableReduction.RootEvaluator S.R) {Γ : Context S.R} (original : TypeOver Γ) where
  annotation : TypeOver Γ
  path : Reduces S.R original.code annotation.code
  stopped : ExecutableReduction.step S.R root annotation.code = none
  same : TypeEq S.R Γ.raw original.code annotation.code
  level : annotation.level = original.level

def Normalized.comparison {root : ExecutableReduction.RootEvaluator S.R} {Γ : Context S.R} {original : TypeOver Γ}
    (result : Normalized root original) : extend Γ result.annotation ≅ extend Γ original :=
  extensionComparison result.annotation original result.same.symm

def Normalized.update {root : ExecutableReduction.RootEvaluator S.R} {Γ : Context S.R} {original : TypeOver Γ}
    (result : Normalized root original) (problem : EquationStore (TotalTerm (extend Γ original))) :
    Update S.levels problem where
  target := extend Γ result.annotation
  answer := result.comparison.hom
  remaining := (frames S.levels).applyStore result.comparison.hom problem
  sound := by
    intro Δ residual solved
    exact (Frames.models_applyStore (X := frames S.levels) result.comparison.hom residual problem).mp solved
  complete := by
    intro Δ solution solved
    refine ⟨solution ≫ result.comparison.inv, ?_, fun term => ?_⟩
    · apply (Frames.models_applyStore (X := frames S.levels) result.comparison.hom _ problem).mpr
      change (frames S.levels).Models ((solution ≫ result.comparison.inv) ≫ result.comparison.hom) problem
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using solved
    · rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact ((frames S.levels).equivalence Δ).refl _

variable (root : ExecutableReduction.RootEvaluator S.R)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

def normalize (fuel : Nat) {Γ : Context S.R} (original : TypeOver Γ) : Option (Normalized root original) :=
  match computed : ExecutableReduction.normalize S.R root fuel original.code with
  | none => none
  | some result => some <| by
      have preserved := Reduces.preserve facts roots heads Γ.formed result.property original.formed
      exact ⟨⟨result.val, original.level, original.universeWitness, preserved.1⟩, result.property,
        ContextualDependentReductionBudget.stopped_of_success S.R root computed,
        ⟨original.level, original.universeWitness, preserved.2⟩, rfl⟩

theorem normalize_zero {Γ : Context S.R} (original : TypeOver Γ) :
    normalize root facts roots heads 0 original = none := rfl

theorem normalize_success_iff (fuel : Nat) {Γ : Context S.R} (original : TypeOver Γ) :
    (normalize root facts roots heads fuel original).isSome = true ↔
      (ExecutableReduction.normalize S.R root fuel original.code).isSome = true := by
  unfold normalize
  split <;> simp_all

end ContextualDependentDeclarationNormalization
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
