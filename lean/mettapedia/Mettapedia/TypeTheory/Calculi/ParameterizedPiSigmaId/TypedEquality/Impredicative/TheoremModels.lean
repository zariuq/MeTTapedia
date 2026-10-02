import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Fundamental

/-!
# Published theorems in the models of a package

A package with a published theorem `name : T := body` is sound for a model of
the package when the model computes the new δ-rule: model SN
(`withTheorem_soundS`) when its value side steps `name` to `body`, its
candidates are closed under that expansion, and the package declares `name`,
if at all, at `T`; and the consistency model (`withTheorem_sound`) when its
reduction steps `name` to `body`. The constant is then valid at its statement
as a definition by one equation, and its δ-rule preserves meaning as a step of
the model's own computation. Model SN reads a root step of the package with the
typing facts of its redex, which are those of the declared type of the redex's
constant; the extended package keeps them when it keeps that declared type.

The premises on the model are needed: a model of a package does not in general
compute a constant the package does not declare, and the same model need not
validate the extended package (`CodeModel.withTheorem_soundS_design_false` and
`CodeModel.withTheorem_sound_design_false` for the object package).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open TelescopeAbstraction (closeType applyClosed subst_empty)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## A step of the model's own computation preserves meaning -/

theorem ModelSN.rootSemanticS_of_step {M : ModelSN.SNModel Head L} (laws : M.Laws) {n : Nat}
    {l r : Tm Head n} (step : M.rules.computation.step l r) : ModelSN.RootSemanticS M l r := by
  intro Γ A validL validR
  refine ⟨validL, validR, fun {_ _ _ σ _ _} e {_} den => ?_⟩
  exact (den.expansive laws.value).left
    (Relation.ReflTransGen.single (WhStep.root (M.rules.computation.substitute σ step)))
    (validR.2 e den).1

theorem Consistency.rootSemantic_of_step {M : Consistency.Model Head L} {n : Nat} {l r : Tm Head n}
    (step : M.rules.computation.step l r) : Consistency.RootSemantic M l r := by
  intro Γ A validL validR
  refine ⟨validL, validR, fun {_ _ σ _} e {_} den => ?_⟩
  obtain ⟨_, relR⟩ := validR
  exact Consistency.Den.expandLeft den
    (Relation.ReflTransGen.single (WhStep.root (M.rules.computation.substitute σ step))) (relR e den)

/-! ## Soundness of the extended package -/

variable {R : Rules Head} {name : DeclName} {T body : Tm Head 0}

/-- The typing facts of a spine in the extended package are those in the
package, when the package declares `name`, if at all, at `T`. -/
theorem ModelSN.SpineFacts.of_withTheorem {M : ModelSN.SNModel Head L}
    (agrees : ∀ {T₀ : Tm Head 0}, R.constantType name = some T₀ → T₀ = T) {n : Nat}
    {Γ : Ctx Head n} {t A : Tm Head n}
    (facts : ModelSN.SpineFacts (R.withTheorem name T body) M Γ t A) :
    ModelSN.SpineFacts R M Γ t A := by
  intro c args T₀ spine declared
  refine facts spine ?_
  by_cases same : c = name
  · subst same
    rw [withTheorem_constantType_self, agrees declared]
  · rw [withTheorem_constantType_of_ne same]
    exact declared

/-- **Model SN with a published theorem.** A model of the package that computes
the new δ-rule on its value side, and whose candidates are closed under
expanding `name` to `body`, is a model of the extended package, when the
package declares `name`, if at all, at `T`. -/
theorem withTheorem_soundS {M : ModelSN.SNModel Head L} (sound : ModelSN.TypedSoundS R M)
    (formed : IsType R .nil T) (typed : Typed R .nil body T)
    (agrees : ∀ {T₀ : Tm Head 0}, R.constantType name = some T₀ → T₀ = T)
    (valueStep : ∀ {n : Nat}, M.rules.computation.step (.const name : Tm Head n) (liftClosed body))
    (realizerExpand : ∀ {r : Nat} (X : M.Cand), X.mem (liftClosed body : Tm Head r) →
      X.mem (.const name : Tm Head r)) :
    ModelSN.TypedSoundS (R.withTheorem name T body) M where
  laws := sound.laws
  headTyping := sound.headTyping
  isUniverse := sound.isUniverse
  join := sound.join
  cumulative := sound.cumulative
  headEq := sound.headEq
  root := by
    intro n l r step
    rcases step with step | ⟨rfl, rfl⟩
    · rcases sound.root step with semantic | typedRoot
      · exact .inl semantic
      · exact .inr fun facts => typedRoot (ModelSN.SpineFacts.of_withTheorem agrees facts)
    · exact .inl (ModelSN.rootSemanticS_of_step sound.laws valueStep)
  constants := by
    intro c A declared
    by_cases same : c = name
    · subst same
      rw [withTheorem_constantType_self, Option.some.injEq] at declared
      subst declared
      exact ModelSN.ValidTmS.definition (Θ := .nil) (C := T) (rhs := body) (f := c) sound formed
        typed
        (fun σ => by
          rw [subst_empty]
          exact Relation.ReflTransGen.single (WhStep.root valueStep))
        (fun ς _ X h => by
          rw [subst_empty] at h
          exact realizerExpand X h)
    · rw [withTheorem_constantType_of_ne same] at declared
      exact sound.constants declared

/-- **The consistency model with a published theorem.** A model of the package
whose reduction computes the new δ-rule is a model of the extended package. -/
theorem withTheorem_sound {M : Consistency.Model Head L} (sound : Consistency.Sound R M)
    (formed : IsType R .nil T) (typed : Typed R .nil body T)
    (valueStep : ∀ {n : Nat}, M.rules.computation.step (.const name : Tm Head n) (liftClosed body)) :
    Consistency.Sound (R.withTheorem name T body) M where
  laws := sound.laws
  headTyping := sound.headTyping
  isUniverse := sound.isUniverse
  join := sound.join
  cumulative := sound.cumulative
  headEq := sound.headEq
  root := by
    intro n l r step
    rcases step with step | ⟨rfl, rfl⟩
    · exact sound.root step
    · exact Consistency.rootSemantic_of_step valueStep
  constants := by
    intro c A declared
    by_cases same : c = name
    · subst same
      rw [withTheorem_constantType_self, Option.some.injEq] at declared
      subst declared
      exact Consistency.ValidTm.definition (Θ := .nil) (C := T) (rhs := body) (f := c) sound formed typed
        (fun σ => by
          rw [subst_empty]
          exact Relation.ReflTransGen.single (WhStep.root valueStep))
    · rw [withTheorem_constantType_of_ne same] at declared
      exact sound.constants declared

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
