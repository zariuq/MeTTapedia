import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate

/-!
# Normalizing a dependent telescope without changing its obligations

Every declaration type is normalized and its formation transported through
the already normalized prefix. The result retains every declaration, with
typed identity-variable substitutions in both directions. These inverse
maps give a solution-preserving solver update for the entire equation store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentContextNormalization

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalSelection ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

structure Normalized {n : Nat} (original : Ctx Head n) where
  raw : Ctx Head n
  formed : CtxFormed S.R raw
  normal : NormalContext (S := S) raw
  forward : CtxEq S.R original raw
  backward : CtxEq S.R raw original

def Normalized.context {n : Nat} {original : Ctx Head n} (result : Normalized (S := S) original) :
    Context S.R := ⟨n, result.raw, result.formed⟩

def Normalized.iso {Γ : Context S.R} (result : Normalized (S := S) Γ.raw) : result.context ≅ Γ where
  hom := ⟨ids, result.forward.substMor⟩
  inv := ⟨ids, result.backward.substMor⟩
  hom_inv_id := Hom.ext (subComp_ids_left ids)
  inv_hom_id := Hom.ext (subComp_ids_left ids)

def Normalized.update {Γ : Context S.R} (result : Normalized (S := S) Γ.raw)
    (problem : EquationStore (TotalTerm Γ)) : Update S.levels problem where
  target := result.context
  answer := result.iso.hom
  remaining := (frames S.levels).applyStore result.iso.hom problem
  sound := by
    intro Δ residual solved
    exact (Frames.models_applyStore (X := frames S.levels) result.iso.hom residual problem).mp solved
  complete := by
    intro Δ solution solved
    refine ⟨solution ≫ result.iso.inv, ?_, fun term => ?_⟩
    · apply (Frames.models_applyStore (X := frames S.levels) result.iso.hom _ problem).mpr
      change (frames S.levels).Models ((solution ≫ result.iso.inv) ≫ result.iso.hom) problem
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using solved
    · rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact ((frames S.levels).equivalence Δ).refl _

private theorem prefixFormed {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (formed : CtxFormed S.R (.snoc Γ type)) : CtxFormed S.R Γ := by cases formed; assumption

private theorem lastFormed {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (formed : CtxFormed S.R (.snoc Γ type)) : IsType S.R Γ type := by cases formed; assumption

variable (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

def normalize (fuel : Nat) : {n : Nat} → (raw : Ctx Head n) → CtxFormed S.R raw →
    Option (Normalized (S := S) raw)
  | _, .nil, _ => some ⟨.nil, .nil, .nil, .nil, .nil⟩
  | _, .snoc raw type, formed =>
      match normalize fuel raw (prefixFormed formed) with
      | none => none
      | some prior =>
          match reduced : ExecutableReduction.normalize S.R root fuel type with
          | none => none
          | some result => some <| by
              have same := Reduces.typeEq facts roots heads (prefixFormed formed) result.property (lastFormed formed)
              have resultFormed : IsType S.R raw result.val := by
                obtain ⟨level, universeWitness, typed⟩ := lastFormed formed
                exact ⟨level, universeWitness,
                  (Reduces.preserve facts roots heads (prefixFormed formed) result.property typed).1⟩
              exact ⟨.snoc prior.raw result.val, .snoc prior.formed (resultFormed.stable prior.forward),
                .snoc prior.normal (ContextualDependentReductionBudget.normal_of_stopped S.R root rootComplete result.val
                  (ContextualDependentReductionBudget.stopped_of_success S.R root reduced)),
                .snoc prior.forward (same.symm.stable prior.forward), .snoc prior.backward same⟩

inductive Finished (fuel : Nat) : {n : Nat} → Ctx Head n → Prop
  | nil : Finished fuel .nil
  | snoc {n : Nat} {raw : Ctx Head n} {type : Tm Head n} :
      Finished fuel raw → (ExecutableReduction.normalize S.R root fuel type).isSome = true →
      Finished fuel (.snoc raw type)

set_option backward.isDefEq.respectTransparency false in
theorem normalize_success_iff (fuel : Nat) {n : Nat} (raw : Ctx Head n) (formed : CtxFormed S.R raw) :
    (normalize root rootComplete facts roots heads fuel raw formed).isSome = true ↔ Finished root fuel raw := by
  induction raw with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | snoc raw type ih =>
      simp only [normalize]
      cases priorRun : normalize root rootComplete facts roots heads fuel raw (prefixFormed formed) with
      | none =>
          constructor
          · intro impossible; cases impossible
          · intro finished
            cases finished with
            | snoc prior _ =>
                have success := ih (prefixFormed formed) |>.mpr prior
                rw [priorRun] at success
                cases success
      | some prior =>
          have priorFinished := (ih (prefixFormed formed)).mp (by rw [priorRun]; rfl)
          dsimp only
          split
          · rename_i missing
            constructor
            · intro impossible; cases impossible
            · intro finished
              cases finished with
              | snoc _ last => rw [missing] at last; cases last
          · rename_i result computed
            exact ⟨fun _ => .snoc priorFinished (by rw [computed]; rfl), fun _ => rfl⟩

end ContextualDependentContextNormalization
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
