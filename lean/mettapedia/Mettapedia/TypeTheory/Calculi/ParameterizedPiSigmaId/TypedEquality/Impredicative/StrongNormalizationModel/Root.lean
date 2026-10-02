import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Formation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TypeLike

/-!
# Root computations in model SN

A root step of an object package is read in the model in one of two ways:

* as a step of the value side's own computation, which is closed under
  substitution, so the two sides of the step are related by weak-head
  expansion;
* as a decoding of a code, `holds c ⟶ D`, where the value side keeps
  `holds c` rigid. Both sides are type-like terms. In a universe they have one
  pack and one shape at every world reached by a morphism: a decoding and
  `holds` of its code have one pack wherever both are interpreted
  (`decoder_coherent`), and one shape (`decoder_shape`), so the universe
  relates the one to what the other is related to, by transitivity of shapes.
  Elsewhere a pack relates any two type-like terms as soon as it relates two.

The latter is a fact of every value side over every realizer algebra: a pack
at a level relates two type-like terms that are related to type-like terms of
one pack and one shape (`ValueSide.InterpAt.typeLike_coherent`).

Heads that the package identifies have one pack at every level, and one shape:
universes of one level, or two leaves (`ValueSide.head_coherent`). This gives
the equality of such heads by the same argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph Truth TypeLike Stuck Decodes)
open Realizability (Daimonic)
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-! ## Heads -/

/-- Heads that are the same up to the package's head equality are validly equal
wherever each is a valid term. -/
theorem ValidEqS.headEq (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {h h' : Head}
    {A : Tm Head n} (same : M.rules.headEq h h') (valid : ValidTmS M Γ (.head h) A)
    (valid' : ValidTmS M Γ (.head h') A) : ValidEqS M Γ (.head h) (.head h') A := by
  refine ⟨valid, valid', fun {_ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨l, interp⟩ := den
  exact InterpAt.typeLike_coherent laws.value interp (y := .head h') (.head h) (.head h)
    (.head h')
    (fun {_ _ _ _} _ {_ _} first second => head_coherent laws.value same first second)
    (valid.2 e ⟨l, interp⟩).1 (valid'.2 e ⟨l, interp⟩).1

/-! ## Root steps -/

/-- A root step of an object package, read in model SN: a step of the value
side's own computation, or a decoding. -/
def ModelRootS (M : SNModel Head L) (D : Decoders Head) {n : Nat} (l r : Tm Head n) : Prop :=
  M.rules.computation.step l r ∨ DecoderStep D l r

/-- A root step preserves meaning in model SN when its two sides are validly
equal wherever each is a valid term of one type. -/
def RootSemanticS (M : SNModel Head L) {n : Nat} (l r : Tm Head n) : Prop :=
  ∀ {Γ : Ctx Head n} {A : Tm Head n}, ValidTmS M Γ l A → ValidTmS M Γ r A →
    ValidEqS M Γ l r A

/-- **The two sides of a root step of the object package, read in the model,
are validly equal wherever each is a valid term.** At a universe, a code and
its decoding have one pack and one shape at every world reached by a
morphism. -/
theorem ValidEqS.root (laws : M.Laws) {D : Decoders Head} (decodes : Decodes M.toModel D)
    {n : Nat} {Γ : Ctx Head n} {l r A : Tm Head n} (root : ModelRootS M D l r)
    (validL : ValidTmS M Γ l A) (validR : ValidTmS M Γ r A) : ValidEqS M Γ l r A := by
  refine ⟨validL, validR, fun {_ _ _ σ σ' _} e {P} den => ?_⟩
  have hl := (validL.2 e den).1
  have hr := (validR.2 e den).1
  rcases root with step | step
  · exact (den.expansive laws.value).left
      (.single (WhStep.root (M.rules.computation.substitute σ step))) hr
  · obtain ⟨k, interp⟩ := den
    exact InterpAt.typeLike_coherent laws.value interp (y := Presentation.subst σ r)
      (Consistency.DecoderStep.typeLike_left decodes (step.substitute σ))
      (Consistency.DecoderStep.typeLike_left decodes (step.substitute σ'))
      (Consistency.DecoderStep.typeLike_right (step.substitute σ'))
      (fun {_ _ _ ρ} _ {_ _} first second =>
        ⟨decoder_coherent laws.value decodes ((step.substitute σ).rename ρ) first second,
          decoder_shape laws.value decodes ((step.substitute σ).rename ρ) first second⟩) hl hr

/-- A root step read in the model, as a step of the value side's own computation
or a decoding of its codes, preserves meaning. -/
theorem ModelRootS.semantic (laws : M.Laws) {D : Decoders Head}
    (decodes : Decodes M.toModel D) {n : Nat} {l r : Tm Head n} (root : ModelRootS M D l r) :
    RootSemanticS M l r :=
  fun validL validR => ValidEqS.root laws decodes root validL validR

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
