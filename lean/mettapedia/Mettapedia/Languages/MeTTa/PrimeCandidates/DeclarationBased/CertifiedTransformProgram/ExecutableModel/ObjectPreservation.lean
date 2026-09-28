import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvObject

/-!
# Preservation of typing in the object package

The object package keeps the universes, heads and cumulativity of the executable
package, so its head equality steps preserve typing and its cumulativity order
is an algebra, with no hypothesis (`objectRules_heads`, `objectRules_algebra`).
Both sides of a derivable equality are typed there, as in every package with a
level model (`object_equal_typed`).

Given the facts about the weak-head forms of its types, every root step of the
object package preserves typing (`objectRules_roots`):

* a root step of the executable package, by the executable package's own
  declarations, whose preservation holds in every package containing it;
* a decoding of a code, since the code is a typed constructor spine at the type
  of codes, which decodes to a type of the universe of proofs.

So, given the facts, reduction preserves typing (`object_reduces_preserve`), the
conversion algorithm is sound (`object_algorithm_sound`), and the algorithmic
equality has the laws of the generic equality once spine comparisons lift
(`object_algorithmic_laws`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Package (U0)

namespace CodeModel
namespace ConvRules

/-- The normalization setting of the object package at typed equality. -/
abbrev objectSetting : Setting Tower.Head ℕ := objectSettingAt (declarative objectRules)

variable {n : Nat} {Γ : Tower.Ctx n}

/-! ## Without the facts -/

/-- **Both sides of a derivable equality of the object package are typed**, in a
formed context. -/
theorem object_equal_typed {a b A : Tower.Tm n} (formed : CtxFormed objectRules Γ)
    (equal : Equal objectRules Γ a b A) : Typed objectRules Γ a A ∧ Typed objectRules Γ b A :=
  Equal.typed (S := objectSetting) equal formed

/-- **Head equality steps of the object package preserve typing.** -/
theorem objectRules_heads : HeadPreserving objectRules := by
  intro n Γ h h' A same typing
  obtain ⟨w, headTyping, le⟩ := Typed.generation typing
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : objectRules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

/-- **The cumulativity order of the object package is an algebra.** -/
theorem objectRules_algebra : CumulativeAlgebra objectRules where
  trans := algebra.trans
  same_left := algebra.same_left
  same_right := algebra.same_right
  join_least := algebra.join_least

/-! ## Given the facts -/

section Facts

variable (facts : FormFacts objectRules objectRoles)
include facts

/-- **The root steps of the object package preserve typing**, given the facts
about the weak-head forms of its types: the executable package's root steps by
its declarations, and a decoding because its code is a typed constructor spine
at the type of codes. -/
theorem objectRules_roots : RootPreserving objectRules := by
  intro n Γ l r A formed step typing
  rcases step with step | step
  · exact roots_in (S := objectSetting) facts rules_sub_objectRules formed step typing
  · obtain ⟨k, args, rfl, role⟩ : ∃ k args, l = .app (.const holdsN) (appSpine (.const k) args) ∧
        objectRoles k = .constructor args.length := by
      cases step with
      | imp p q => exact ⟨impN, [p, q], rfl, objectRoles_imp⟩
      | all carrier f => exact ⟨_, [f], rfl, objectDecoderRoles.all carrier⟩
      | eq carrier x y => exact ⟨_, [x, y], rfl, objectDecoderRoles.eq carrier⟩
    obtain ⟨mor, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
      (.snoc .nil (.const propN)) (.head (.sort Tower.zero)) declared_holds
      (σ := consSub (appSpine (.const k) args) fun i => Fin.elim0 i) typing
    have code : Typed objectRules Γ (appSpine (.const k) args) (.const propN) := mor 0
    obtain ⟨D, decoding, -, typedD⟩ := objectRules_decodes facts formed code role
    obtain rfl := objectShape.deterministic (.inr step) decoding
    exact Typed.subsume typedD le

/-- **Reduction of the object package preserves typing** and is a typed equality,
given the facts. -/
theorem object_reduces_preserve {t t' T : Tower.Tm n} (formed : CtxFormed objectRules Γ)
    (red : Reduces objectRules t t') (typing : Typed objectRules Γ t T) :
    Typed objectRules Γ t' T ∧ Equal objectRules Γ t t' T :=
  Reduces.preserve (S := objectSetting) facts (objectRules_roots facts) objectRules_heads formed
    red typing

/-- **The conversion algorithm is sound for the object package**, given the
facts. -/
theorem object_algorithm_sound {st : AlgorithmStatement Tower.Head}
    (derivation : Algorithm objectRules st) : AlgorithmSound objectSetting st :=
  Algorithm.sound (S := objectSetting) facts (objectRules_roots facts) objectRules_heads
    objectRules_algebra derivation

/-- **The algorithmic equality of the object package has the laws of the generic
equality**, given the facts and the lifting of spine comparisons. -/
theorem object_algorithmic_laws (lift : SpineLift objectSetting) :
    (algorithmic objectRules objectRoles).Laws objectRules objectRoles :=
  algorithmic_laws (S := objectSetting) facts (objectRules_roots facts) objectRules_heads
    objectRules_algebra lift

end Facts

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
