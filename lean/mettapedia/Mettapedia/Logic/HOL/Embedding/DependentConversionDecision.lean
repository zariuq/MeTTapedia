import Mettapedia.Logic.HOL.Embedding.ConversionEvidenceBridge
import Mettapedia.TypeTheory.ConversionDecisionComparison

/-!
# Conversion-decision interfaces for the dependent comparison calculus

The dependent comparison core has a syntax-directed typing relation, a
declarative conversion closure, and proof-relevant conversion receipts.  This
file states the exact additional obligations for two algorithmic
organizations without selecting either one:

* a complete decidable invariant over typed expressions; or
* a complete decidable invariant over an erased representation, together with
  preservation and reflection of conversion.

Either organization decides the same declarative conversion relation.  When
placed after the syntax-directed checker, either also reconstructs exactly the
existing typing-with-conversion judgment.  Hence the difference between the
organizations is evidence, algorithm, and cost—not theoremhood.

The interfaces deliberately do not claim that normalization, normalization
by evaluation, or an erased conversion algorithm has already been built for
this calculus.  Supplying one means inhabiting the corresponding structure.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
namespace DependentConversionDecision

open Expr
open ConversionEvidenceBridge
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ConversionDecisionComparison

universe u v uCode uRawState uRawStep uRawCode

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Expressions of the comparison calculus as a one-index state family. -/
abbrev ExpressionState
    (Base : Type u) (Const : Ty Base → Type v) (_index : Unit) :
    Type (max u v) :=
  Expr Base Const

/-- Root beta evidence as the primitive conversion generator. -/
abbrev BetaGenerator
    (Base : Type u) (Const : Ty Base → Type v) :
    {index : Unit} →
      ExpressionState Base Const index →
      ExpressionState Base Const index → Type (max u v) :=
  fun {_index : Unit} => BetaStep Base Const

/-! ## Direct complete conversion decisions -/

/-- A direct algorithmic organization of conversion.  `Code` may be a normal
form, a semantic value used by normalization by evaluation, or any other
complete invariant. -/
structure CompleteConversionDecision
    (Base : Type u) (Const : Ty Base → Type v) where
  Code : Type uCode
  invariant : CompleteInvariant
    (ExpressionState Base Const) (BetaGenerator Base Const)
    (fun _ : Unit => Code)
  codeDecidableEq : DecidableEq Code

namespace CompleteConversionDecision

/-- Execute the direct Boolean conversion decision. -/
def decide
    (decision : CompleteConversionDecision Base Const)
    (source target : Expr Base Const) : Bool := by
  letI : DecidableEq decision.Code := decision.codeDecidableEq
  exact decision.invariant.decideConversion () source target

/-- A direct complete invariant decides exactly declarative beta conversion. -/
theorem decide_eq_true_iff_conv
    (decision : CompleteConversionDecision Base Const)
    {source target : Expr Base Const} :
    decision.decide source target = true ↔ Conv source target := by
  letI : DecidableEq decision.Code := decision.codeDecidableEq
  exact
    (decision.invariant.decideConversion_eq_true_iff
      (index := ()) (source := source) (target := target)).trans
      conv_iff_nonempty_path.symm

/-- Syntax-directed typing followed by the direct decision procedure is
exactly declarative typing with conversion. -/
theorem hasTypeC_iff_syntaxDirected_and_decides
    (decision : CompleteConversionDecision Base Const)
    {context : List (Expr Base Const)}
    {term targetType : Expr Base Const} :
    HasTypeC context term targetType ↔
      ∃ sourceType : Expr Base Const,
        HasType context term sourceType ∧
          decision.decide sourceType targetType = true := by
  constructor
  · intro convertedTyping
    rcases ConversionEvidenceBridge.HasTypeC.hasReceipt convertedTyping with
      ⟨receipt⟩
    exact ⟨receipt.sourceType, receipt.typing,
      decision.decide_eq_true_iff_conv.mpr
        (pathToConv receipt.conversion)⟩
  · rintro ⟨sourceType, coreTyping, accepted⟩
    exact HasTypeC.conv (.of coreTyping)
      (decision.decide_eq_true_iff_conv.mp accepted)

/-- The same factorization stated at the proof-relevant receipt boundary. -/
theorem nonemptyReceipt_iff_syntaxDirected_and_decides
    (decision : CompleteConversionDecision Base Const)
    {context : List (Expr Base Const)}
    {term targetType : Expr Base Const} :
    Nonempty (TypingReceipt context term targetType) ↔
      ∃ sourceType : Expr Base Const,
        HasType context term sourceType ∧
          decision.decide sourceType targetType = true :=
  hasTypeC_iff_nonempty_receipt.symm.trans
    decision.hasTypeC_iff_syntaxDirected_and_decides

/-- The simple HOL slice incurs no nontrivial conversion obligation at its
own embedded type. -/
theorem embeddedHolType_decides_reflexively
    (decision : CompleteConversionDecision Base Const)
    {context : Ctx Base} {A : Ty Base}
    (_term : Term Const context A) :
    decision.decide (tyToExpr A) (tyToExpr A) = true :=
  decision.decide_eq_true_iff_conv.mpr (Conv.refl _)

/-- A beta-expanded target type is accepted for `top`, exhibiting where the
dependent layer actually pays for conversion beyond syntax-directed typing. -/
theorem top_decides_betaExpandedType
    (decision : CompleteConversionDecision Base Const)
    (base : Base) :
    decision.decide
      prop (app (lam (Expr.base base) prop) top) = true :=
  decision.decide_eq_true_iff_conv.mpr
    (Conv.symm (Conv.beta (Expr.base base) prop top))

/-- The accepted beta-expanded target reconstructs declarative converted
typing, while the core source typing remains `top : prop`. -/
theorem top_has_betaExpandedType
    (decision : CompleteConversionDecision Base Const)
    (base : Base) :
    HasTypeC ([] : List (Expr Base Const)) top
      (app (lam (Expr.base base) prop) top) :=
  decision.hasTypeC_iff_syntaxDirected_and_decides.mpr
    ⟨prop, HasType.top, decision.top_decides_betaExpandedType base⟩

end CompleteConversionDecision

/-! ## Conversion-reflecting erased decisions -/

/-- An erased conversion organization.  The erasure must preserve primitive
beta steps and reflect raw path existence; the raw classifier must be a
complete invariant.  Preservation without reflection is intentionally
insufficient. -/
structure ConversionReflectingErasedDecision
    (Base : Type u) (Const : Ty Base → Type v) where
  RawState : Type uRawState
  RawStep : RawState → RawState → Type uRawStep
  Code : Type uRawCode
  erasure : ExactConversionErasure
    (ExpressionState Base Const) (BetaGenerator Base Const)
    RawState RawStep
  invariant : CompleteInvariant
    (fun _ : Unit => RawState) (fun {_index : Unit} => RawStep)
    (fun _ : Unit => Code)
  codeDecidableEq : DecidableEq Code

namespace ConversionReflectingErasedDecision

/-- Execute conversion on the erased representation. -/
def decide
    (decision : ConversionReflectingErasedDecision Base Const)
    (source target : Expr Base Const) : Bool := by
  letI : DecidableEq decision.Code := decision.codeDecidableEq
  exact decision.invariant.decideConversion ()
    (decision.erasure.erase (index := ()) source)
    (decision.erasure.erase (index := ()) target)

/-- Erased checking agrees with declarative conversion precisely because the
erasure reflects and the raw invariant is complete. -/
theorem decide_eq_true_iff_conv
    (decision : ConversionReflectingErasedDecision Base Const)
    {source target : Expr Base Const} :
    decision.decide source target = true ↔ Conv source target := by
  letI : DecidableEq decision.Code := decision.codeDecidableEq
  simpa [decide] using
    (decision.erasure.erasedDecision_eq_true_iff decision.invariant
      (index := ()) (source := source) (target := target)).trans
      conv_iff_nonempty_path.symm

/-- Syntax-directed typing followed by erased conversion checking is exactly
the same declarative typing-with-conversion judgment. -/
theorem hasTypeC_iff_syntaxDirected_and_decides
    (decision : ConversionReflectingErasedDecision Base Const)
    {context : List (Expr Base Const)}
    {term targetType : Expr Base Const} :
    HasTypeC context term targetType ↔
      ∃ sourceType : Expr Base Const,
        HasType context term sourceType ∧
          decision.decide sourceType targetType = true := by
  constructor
  · intro convertedTyping
    rcases ConversionEvidenceBridge.HasTypeC.hasReceipt convertedTyping with
      ⟨receipt⟩
    exact ⟨receipt.sourceType, receipt.typing,
      decision.decide_eq_true_iff_conv.mpr
        (pathToConv receipt.conversion)⟩
  · rintro ⟨sourceType, coreTyping, accepted⟩
    exact HasTypeC.conv (.of coreTyping)
      (decision.decide_eq_true_iff_conv.mp accepted)

/-- The simple HOL slice also pays no nontrivial erased-conversion cost at its
own embedded type. -/
theorem embeddedHolType_decides_reflexively
    (decision : ConversionReflectingErasedDecision Base Const)
    {context : Ctx Base} {A : Ty Base}
    (_term : Term Const context A) :
    decision.decide (tyToExpr A) (tyToExpr A) = true :=
  decision.decide_eq_true_iff_conv.mpr (Conv.refl _)

end ConversionReflectingErasedDecision

/-! ## Information boundary -/

/-- Declarative conversion, normalization decisions, and erased decisions can
agree on endpoints without retaining the supplied conversion history. -/
theorem declarative_shadow_cannot_recover_conversion_history
    (expression : Expr Base Const) :
    ¬ ∃ recover : Nonempty (ConversionPath expression expression) →
          ConversionPath expression expression,
        ∀ path, recover ⟨path⟩ = path :=
  no_path_history_retraction
    (singleReflexivityPath expression)
    (doubledReflexivityPath expression)
    (singleReflexivityPath_ne_doubled expression)

/-! ## Axiom audit -/

#print axioms CompleteConversionDecision.decide_eq_true_iff_conv
#print axioms CompleteConversionDecision.hasTypeC_iff_syntaxDirected_and_decides
#print axioms CompleteConversionDecision.nonemptyReceipt_iff_syntaxDirected_and_decides
#print axioms CompleteConversionDecision.embeddedHolType_decides_reflexively
#print axioms CompleteConversionDecision.top_has_betaExpandedType
#print axioms ConversionReflectingErasedDecision.decide_eq_true_iff_conv
#print axioms ConversionReflectingErasedDecision.hasTypeC_iff_syntaxDirected_and_decides
#print axioms ConversionReflectingErasedDecision.embeddedHolType_decides_reflexively
#print axioms declarative_shadow_cannot_recover_conversion_history

end DependentConversionDecision
end Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
