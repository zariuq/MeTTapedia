import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Model

/-!
# The definitional unfolding, as an opt-in variant

The strong variant of the package adds one root computation to the extended
package: the recursor unfolds definitionally at every accessibility proof,

`rec P R F a q ⟶ F a (λ y r. rec P R F y (inv R a q y r))`.

Its conversion therefore identifies the recursor with its unfolding, and it can
diverge at abstract accessibility proofs. The same model that validates the
propositional variant computes this step, so the strong variant is sound for it
(`sound_strongRules`) and consistent (`strong_consistent`). The propositional
variant is the strong variant without the step: its computation is the base
package's (`Signature.rules_computation`), and it is included in the strong one
(`derivable_rules_strong`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency
open Presentation.TypedEquality.Normalization (definitionComputation DefinitionStep DecoderStep)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

namespace Signature

variable (S : Signature Head)

/-- The recursor's definitional unfolding, as a root computation. -/
def unfoldComputation : RootComputation Head :=
  definitionComputation S.recursor S.recTelescope
    (S.unfolding (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

/-- The strong base: the extended base, whose computation also unfolds the
recursor. -/
def strongBase : Rules Head :=
  { S.accBase with
    computation := Normalization.RootComputation.union S.base.computation S.unfoldComputation }

/-- The strong variant: the strong base with the codes. -/
abbrev strongRules : Rules Head := S.codes.extend S.strongBase

/-- A step of the unfolding is an instance of the recursor's equation. -/
theorem unfoldComputation_step {n : Nat} {l r : Tm Head n} (step : S.unfoldComputation.step l r) :
    ∃ P R F a q, l = S.recSpine P R F a q ∧ r = S.unfolding P R F a q := by
  obtain ⟨σ, rfl, rfl⟩ := step
  exact ⟨σ 4, σ 3, σ 2, σ 1, σ 0, rfl, rfl⟩

/-- Every full application of the recursor unfolds in the strong variant. -/
theorem unfoldComputation_of {n : Nat} (P R F a q : Tm Head n) :
    S.unfoldComputation.step (S.recSpine P R F a q) (S.unfolding P R F a q) :=
  ⟨consSub q (consSub a (consSub F (consSub R (consSub P (fun i => Fin.elim0 i))))), rfl, rfl⟩

theorem strongRules_step {n : Nat} (P R F a q : Tm Head n) :
    S.strongRules.computation.step (S.recSpine P R F a q) (S.unfolding P R F a q) :=
  Or.inl (Or.inr (S.unfoldComputation_of P R F a q))

/-- The propositional variant is included in the strong variant: the same
universes and declarations, and fewer root steps. -/
theorem rules_sub_strong : Normalization.RulesSub S.rules S.strongRules where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := id
  computation := fun step => step.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr h)

/-- **Every derivation of the propositional variant is a derivation of the
strong variant.** -/
theorem derivable_rules_strong {st : Statement Head} (d : Derivable S.rules st) :
    Derivable S.strongRules st :=
  Normalization.Derivable.mono S.rules_sub_strong d

end Signature

variable {M : Model Head L} {Ac : Carrier .gen} {S : Signature Head}

/-- **The strong variant is sound** for a model that computes the recursor: its
extra root step is a step of the model's own computation. -/
theorem sound_strongRules (H : ComputesRecursor S M Ac) (L : S.Laws) (sound : Sound S.baseRules M) :
    Sound S.strongRules M where
  laws := H.laws
  headTyping := (sound_rules H L sound).headTyping
  isUniverse := (sound_rules H L sound).isUniverse
  join := (sound_rules H L sound).join
  cumulative := (sound_rules H L sound).cumulative
  headEq := (sound_rules H L sound).headEq
  root := fun {n l r} step => by
    change (S.base.computation.step l r ∨ S.unfoldComputation.step l r) ∨
      DecoderStep S.codes.decoders l r at step
    rcases step with (h | h) | h
    · exact (sound_rules H L sound).root (Or.inl h)
    · obtain ⟨P, R, F, a, q, rfl, rfl⟩ := S.unfoldComputation_step h
      exact rootSemantic_of_modelStep (H.step P R F a q)
    · exact (sound_rules H L sound).root (Or.inr h)
  constants := (sound_rules H L sound).constants

/-- **Consistency of the strong variant**, in the same model. -/
theorem strong_consistent (H : ComputesRecursor S M Ac) (L : S.Laws)
    (sound : Sound S.baseRules M) {c : Tm Head 0} {P : Prop}
    (truth : Truth M.reading World.closed c P) (false_ : ¬ P) (t : Tm Head 0) :
    ¬ Typed S.strongRules .nil t (S.codes.holdsOf c) := by
  rw [Codes.holdsOf, H.codes.holds]
  exact no_closed_proof (sound_strongRules H L sound) truth false_ t

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
