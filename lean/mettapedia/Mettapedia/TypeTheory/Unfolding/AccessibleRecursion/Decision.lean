import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Judgments

/-!
# Carved conversion is beta conversion, decided by normalization

In the carved variant the recursor has no computation rule, so every symbol
of the signature is an inert variable of the one-ground calculus.  Carved
definitional equality is therefore exactly `BetaConv` of that calculus
(`carved_conv_iff`); in particular it ignores the hypotheses.  Beta
conversion of the one-ground calculus is decided by computing normal forms
(`ConversionDecision.decideConversion`), so carved definitional equality is
decided by normalization (`decideCarvedConv_iff`), without a budget and
without inspecting any derivation.

The decision inherits the axioms of the reused strong-normalization theorem
of the one-ground calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.Logic
open Mettapedia.TypeTheory.Unfolding
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

variable {A P : Ty}

/-- What carved derivability says about definitional equality: it is beta
conversion.  The other judgment forms are not constrained here. -/
def ConvMeaning : Judgment A P → Prop
  | .holds _ _ _ => True
  | .conv _ _ _ left right => BetaConv left right
  | .equal _ _ _ _ _ => True

theorem carved_convMeaning {judgment : Judgment A P} (derivation : Carved A P judgment) :
    ConvMeaning judgment := by
  refine Derives.least ConvMeaning ?_ derivation
  intro premises conclusion rule meanings
  rcases rule with rule | rule
  · cases rule <;> trivial
  · cases rule with
    | beta left right convertible => exact convertible
    | symm left right => exact Relation.EqvGen.symm _ _ (meanings _ mem₀)
    | trans left middle right =>
        exact Relation.EqvGen.trans _ _ _ (meanings _ mem₀) (meanings _ mem₁)
    | app function function' argument argument' =>
        exact BetaConv.app (meanings _ mem₀) (meanings _ mem₁)
    | lam body body' => exact BetaConv.lam (meanings _ mem₀)

/-- **Carved definitional equality is beta conversion.** -/
theorem carved_conv_iff {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    {left right : Tm A P Γ T} :
    Carved A P (.conv Γ hyps T left right) ↔ BetaConv left right :=
  ⟨carved_convMeaning, fun convertible => derives₀ (Or.inr (ConvRule.beta left right convertible))⟩

/-- Carved definitional equality does not depend on the hypotheses. -/
theorem carved_conv_hyps_irrelevant {Γ : List Ty} {hyps hyps' : List (Tm A P Γ prop)} {T : Ty}
    {left right : Tm A P Γ T} :
    Carved A P (.conv Γ hyps T left right) ↔ Carved A P (.conv Γ hyps' T left right) :=
  carved_conv_iff.trans carved_conv_iff.symm

/-- The carved conversion checker: compare computed normal forms. -/
def decideCarvedConv {Γ : List Ty} {T : Ty} (left right : Tm A P Γ T) : Bool :=
  ConversionDecision.decideConversion left right

/-- **Carved definitional equality is decided by normalization.** -/
theorem decideCarvedConv_iff {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    {left right : Tm A P Γ T} :
    decideCarvedConv left right = true ↔ Carved A P (.conv Γ hyps T left right) :=
  (ConversionDecision.decideConversion_correct left right).trans carved_conv_iff.symm

instance carvedConvDecidable {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    {left right : Tm A P Γ T} : Decidable (Carved A P (.conv Γ hyps T left right)) :=
  decidable_of_iff _ decideCarvedConv_iff

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
