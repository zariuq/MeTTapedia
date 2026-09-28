import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectAlgorithmic

/-!
# Controls for the decoder along algorithmic comparisons

* **A code variable has its decoding compared with itself**, with no
  hypothesis: the decoding of a variable of the type of codes is a neutral type
  headed by the decoder, compared as a spine (`holds_var_compared`).
* **The congruence of the decoder has content**: a generic equality relating
  every two terms at the type of codes and no terms at the universe of proofs is
  not a congruence of the decoder (`codesOnly_not_holdsCongruence`).
* **Saturation is exact**: implication applied to two codes is a code
  (`imp_code_typed`), and, given the facts about the weak-head forms of types,
  implication applied to one code is not (`imp_partial_not_code`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Package (U0)

namespace CodeModel
namespace ConvRules

/-! ## A code variable -/

/-- **The decoding of a code variable is compared with itself** at the universe
of proofs: a neutral type headed by the decoder, compared as a spine. -/
theorem holds_var_compared :
    Algorithmic objectRules objectRoles (.terms (.snoc .nil (.const propN))
      (.app (.const holdsN) (.var 0)) (.app (.const holdsN) (.var 0)) U0) := by
  have hu : objectRules.isUniverse (.sort Tower.zero) := Tower.IsUniverse.sort _
  have typed : Typed objectRules (.snoc .nil (.const propN)) (.var 0) (.const propN) := .var 0
  have holdsT : Typed objectRules (.snoc .nil (.const propN)) (.app (.const holdsN) (.var 0)) U0 :=
    .appElim holds_typedO typed
  have isU0 : IsType objectRules (.snoc .nil (.const propN)) U0 :=
    ⟨_, Tower.IsUniverse.sort _, U0_typedU tower_sub_objectRules⟩
  have isProp : IsType objectRules (.snoc .nil (.const propN)) (.const propN) :=
    ⟨_, hu, prop_typedO⟩
  have isPi : IsType objectRules (.snoc .nil (.const propN)) (.pi (.const propN) U0) :=
    ⟨_, Tower.IsUniverse.sort _, piO (raiseO prop_typedO) U0_typedO⟩
  have neutral : Neutral objectRoles (.app (.const holdsN) (.var 0) : Tower.Tm 1) :=
    Neutral.stuck_single (before := []) (after := []) objectRoles_holds rfl (.var 0)
  have codes : Algorithmic objectRules objectRoles
      (.terms (.snoc .nil (.const propN)) (.var 0) (.var 0) (.const propN)) :=
    .terms (RedTy.refl isProp) (.inr (.inr (.inr (.inr (.inl prop_neutral))))) (RedTm.refl typed)
      (RedTm.refl typed) (.spine (.inr (.inl prop_neutral)) (.inl (.var 0)) (.inl (.var 0)) typed
        typed (.spinesW (.var 0) (RedTy.refl isProp) (.inr (.inr (.inr (.inr (.inl prop_neutral)))))))
  exact .terms (RedTy.refl isU0) (.inl ⟨_, rfl⟩) (RedTm.refl holdsT) (RedTm.refl holdsT)
    (.univ hu holdsT holdsT (.neutralTypes neutral neutral hu
      (.spinesW (.app (.spinesW (.const declared_holds holds_typedO) (RedTy.refl isPi)
        (.inr (.inl ⟨_, _, rfl⟩))) codes) (RedTy.refl isU0) (.inl ⟨_, rfl⟩))))

/-! ## A generic equality that is no congruence of the decoder -/

/-- The generic equality relating every two terms at the type of codes, and
nothing else. -/
def codesOnly : GenericEquality Tower.Head where
  convTy := fun _ _ _ => False
  convTm := fun _ _ _ A => A = .const propN
  convNe := fun _ _ _ _ => False

/-- **Relating codes does not relate their decodings**: the generic equality
relating every two terms at the type of codes is no congruence of the decoder. -/
theorem codesOnly_not_holdsCongruence : ¬ HoldsCongruence codesOnly programCodes := by
  intro congruence
  have related : (Tm.head (.sort Tower.zero) : Tower.Tm 0) = .const propN :=
    congruence (Γ := .nil) (c := .const propN) (c' := .const propN) rfl
  cases related

/-! ## Saturated and partial implications -/

/-- **Implication applied to two codes is a code.** -/
theorem imp_code_typed {n : Nat} {Γ : Tower.Ctx n} {p q : Tower.Tm n}
    (typedP : Typed objectRules Γ p (.const propN)) (typedQ : Typed objectRules Γ q (.const propN)) :
    Typed objectRules Γ (appSpine (.const impN) [p, q]) (.const propN) :=
  .appElim (.appElim imp_typedO typedP) typedQ

/-- **Implication applied to one code is not a code**, given the facts: a typed
constructor spine at the type of codes is saturated. -/
theorem imp_partial_not_code (facts : FormFacts objectRules objectRoles) {n : Nat}
    {Γ : Tower.Ctx n} (formed : CtxFormed objectRules Γ) (p : Tower.Tm n) :
    ¬ Typed objectRules Γ (appSpine (.const impN) [p]) (.const propN) := fun typing =>
  absurd (ctorSpine_saturated facts formed typing objectRoles_imp)
    (show ¬ (1 : Nat) = 2 by decide)

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
