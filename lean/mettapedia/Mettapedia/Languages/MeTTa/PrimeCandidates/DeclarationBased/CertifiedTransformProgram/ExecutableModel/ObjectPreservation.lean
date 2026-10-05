import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvObject

/-!
# Preservation of typing in the package of an extension

The package of an extension of the transport value model (`TExtension`) keeps the universes,
heads and cumulativity of the executable package, so its head equality steps preserve typing
and its cumulativity order is an algebra, with no hypothesis (`realRules_heads`,
`realRules_algebra`). Both sides of a derivable equality are typed there, as in every package
with a level model (`real_equal_typed`). The object package is the extension by no name
(`objectTExt`); the object package with a declared datatype is another.

Given the facts about the weak-head forms of its types, and that its root steps at its new
names preserve typing, every root step of the package preserves typing (`realRules_roots`):

* a root step of the executable package, by the executable package's own
  declarations, whose preservation holds in every package containing it;
* a decoding of a code, since the code is a typed constructor spine at the type
  of codes, which decodes to a type of the universe of proofs.

So, under the same inputs, reduction preserves typing (`real_reduces_preserve`), the
conversion algorithm is sound (`real_algorithm_sound`), and the algorithmic equality has the
laws of the generic equality once spine comparisons lift (`real_algorithmic_laws`). For the
object package there is no new name, and the facts are the only input.

Negative: a root step that does not preserve typing breaks this, and the extension's new steps
must be checked; an iota step of a declared recursor preserves typing by its declared type.
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

/-- The normalization setting of the package of an extension at typed equality. -/
abbrev realSetting (X : TExtension) : Setting Tower.Head ℕ :=
  realSettingAt X (declarative X.realRules)

variable (X : TExtension) {n : Nat} {Γ : Tower.Ctx n}

/-! ## Without the facts -/

/-- **Both sides of a derivable equality of the package of an extension are typed**, in a
formed context. -/
theorem real_equal_typed {a b A : Tower.Tm n} (formed : CtxFormed X.realRules Γ)
    (equal : Equal X.realRules Γ a b A) : Typed X.realRules Γ a A ∧ Typed X.realRules Γ b A :=
  Equal.typed (S := realSetting X) equal formed

/-- **Head equality steps of the package of an extension preserve typing.** -/
theorem realRules_heads : HeadPreserving X.realRules := by
  intro n Γ h h' A same typing
  obtain ⟨w, headTyping, le⟩ := Typed.generation typing
  have same' := X.realHeadEq same
  cases X.realHeadTyping headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType (X.realSub.headTyping .legacyGround)) le
      | sort _ => exact same'.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same'.elim
      | sort r =>
          have raise : objectRules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same' ν
            omega
          exact Typed.subsume (.cumul (.headType (X.realSub.headTyping (.sort r)))
            (X.realSub.cumulative raise)) le

/-- Heads the package of an extension identifies are identified in the object package. -/
theorem realHeadSame {u u' : Tower.Head} (same : HeadSame X.realRules u u') :
    HeadSame objectRules u u' :=
  same.imp id X.realHeadEq

/-- **The cumulativity order of the package of an extension is an algebra.** -/
theorem realRules_algebra : CumulativeAlgebra X.realRules where
  trans := fun c c' => X.realSub.cumulative
    (algebra.trans (X.realCumulative c) (X.realCumulative c'))
  same_left := fun same c => X.realSub.cumulative
    (algebra.same_left (realHeadSame X same) (X.realCumulative c))
  same_right := fun c same => X.realSub.cumulative
    (algebra.same_right (X.realCumulative c) (realHeadSame X same))
  join_least := fun join c c' => X.realSub.cumulative
    (algebra.join_least (X.realJoin join) (X.realCumulative c) (X.realCumulative c'))

/-! ## Given the facts -/

section Facts

variable (facts : FormFacts X.realRules X.realRoles)
  (newRoots : ∀ {n : Nat} {Γ : Tower.Ctx n} {c : DeclName} {args : List (Tower.Tm n)}
    {r A : Tower.Tm n}, CtxFormed X.realRules Γ → c ∈ X.names →
      X.realRules.computation.step (appSpine (.const c) args) r →
      Typed X.realRules Γ (appSpine (.const c) args) A → Typed X.realRules Γ r A)
include facts newRoots

/-- **The root steps of the package of an extension preserve typing**, given the facts about
the weak-head forms of its types and that its root steps at new names do: the executable
package's root steps by its declarations, and a decoding because its code is a typed
constructor spine at the type of codes. -/
theorem realRules_roots : RootPreserving X.realRules := by
  intro n Γ l r A formed step typing
  obtain ⟨c, arity, inspect, args, -, hl, -, -⟩ := X.realShape.spine step
  by_cases new : c ∈ X.names
  · subst hl
    exact newRoots formed new step typing
  have old : objectRules.computation.step l r := by
    subst hl
    exact X.realStepOld new step
  rcases old with step' | step'
  · exact roots_in (S := realSetting X) facts (rules_sub_objectRules.trans X.realSub) formed step'
      typing
  · obtain ⟨k, args', rfl, role⟩ : ∃ k args', l = .app (.const holdsN) (appSpine (.const k) args') ∧
        X.realRoles k = .constructor args'.length := by
      cases step' with
      | imp p q => exact ⟨impN, [p, q], rfl, X.realDecoderRoles.imp⟩
      | all carrier f => exact ⟨_, [f], rfl, X.realDecoderRoles.all carrier⟩
      | eq carrier x y => exact ⟨_, [x, y], rfl, X.realDecoderRoles.eq carrier⟩
    obtain ⟨mor, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
      (.snoc .nil (.const propN)) (.head (.sort Tower.zero)) (X.realSub.constantType declared_holds)
      (σ := consSub (appSpine (.const k) args') fun i => Fin.elim0 i) typing
    have code : Typed X.realRules Γ (appSpine (.const k) args') (.const propN) := mor 0
    obtain ⟨D, decoding, -, typedD⟩ := realRules_decodes X facts formed code role
    obtain rfl := X.realShape.deterministic (X.realDecodes step') decoding
    exact Typed.subsume typedD le

/-- **Reduction of the package of an extension preserves typing** and is a typed equality,
given the facts and that the root steps at new names preserve typing. -/
theorem real_reduces_preserve {t t' T : Tower.Tm n} (formed : CtxFormed X.realRules Γ)
    (red : Reduces X.realRules t t') (typing : Typed X.realRules Γ t T) :
    Typed X.realRules Γ t' T ∧ Equal X.realRules Γ t t' T :=
  Reduces.preserve (S := realSetting X) facts (realRules_roots X facts newRoots)
    (realRules_heads X) formed red typing

/-- **The conversion algorithm is sound for the package of an extension**, given the facts and
that the root steps at new names preserve typing. -/
theorem real_algorithm_sound {st : AlgorithmStatement Tower.Head}
    (derivation : Algorithm X.realRules st) : AlgorithmSound (realSetting X) st :=
  Algorithm.sound (S := realSetting X) facts (realRules_roots X facts newRoots)
    (realRules_heads X) (realRules_algebra X) derivation

/-- **The algorithmic equality of the package of an extension has the laws of the generic
equality**, given the facts, that the root steps at new names preserve typing, and the
lifting of spine comparisons. -/
theorem real_algorithmic_laws (lift : SpineLift (realSetting X)) :
    (algorithmic X.realRules X.realRoles).Laws X.realRules X.realRoles :=
  algorithmic_laws (S := realSetting X) facts (realRules_roots X facts newRoots)
    (realRules_heads X) (realRules_algebra X) lift

end Facts

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
