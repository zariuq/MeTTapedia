import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntensionalCode
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision

/-!
# Canonical code is a coherent alternative to source-preserving code

The existing terminating normalizer supplies a beta-extensional quotation
operation. It preserves interpretation and necessarily forgets distinctions
between some authored programs. It is a separate operation from literal code
construction; no equality on raw code is changed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.IntensionalCode

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision

universe u

variable {Γ : List Ty} {A : Ty} {Ground : Type u}

/-- Compute and then retain the normal-form syntax. -/
def canonicalQuote (term : Term Γ A) : CodeName Γ A :=
  ⟨(normalize term).normalForm⟩

theorem canonicalQuote_respects_beta {left right : Term Γ A}
    (equal : BetaConv left right) :
    canonicalQuote left = canonicalQuote right := by
  apply congrArg CodeName.mk
  exact (normalize_eq_iff_betaConv left right).2 equal

theorem canonicalQuote_preserves_run (term : Term Γ A)
    (environment : Environment Ground Γ) :
    (canonicalQuote term).run environment = term.denote environment :=
  ((normalize_convert term).denote environment).symm

theorem canonicalQuote_idempotent (term : Term Γ A) :
    canonicalQuote (canonicalQuote term).body = canonicalQuote term := by
  apply congrArg CodeName.mk
  exact normalize_idempotent term

theorem canonicalQuote_forgets_redex_shape :
    canonicalQuote redexCode.body = canonicalQuote identityCode.body :=
  canonicalQuote_respects_beta constructed_redex_beta_converts

/-- Beta-extensional quotation is possible, but exact source reconstruction
is not one of its laws. -/
theorem canonicalQuote_not_source_injective :
    ¬ Function.Injective
      (canonicalQuote : Term [] FunctionType → CodeName [] FunctionType) := by
  intro faithful
  exact constructed_redex_is_not_identity_syntax
    (faithful canonicalQuote_forgets_redex_shape)

theorem canonicalQuote_identity :
    canonicalQuote identityCode.body = identityCode := by
  apply congrArg CodeName.mk
  apply normalize_of_irreducible
  intro target step
  cases step with
  | lam inner => cases inner

/-- Exposing the source name retains a redex; canonicalization changes it. -/
theorem expose_differs_from_canonicalize :
    redexCode.expose ≠ (canonicalQuote redexCode.body).expose := by
  rw [canonicalQuote_forgets_redex_shape, canonicalQuote_identity]
  exact constructed_redex_is_not_identity_syntax

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.IntensionalCode
