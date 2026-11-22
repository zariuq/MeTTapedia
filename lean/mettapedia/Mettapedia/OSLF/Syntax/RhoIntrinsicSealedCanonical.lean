import Mettapedia.OSLF.Syntax.RhoIntrinsicReadbackQuoteSafety

/-!
# Exact comparison with the authored closed rho carrier

Restricting the complete intrinsic canonical equivalence by its proved
quote-safe-representative criterion gives precisely the canonical elements of
the actual authored closed name and process carriers. This comparison keeps
the full intrinsic quotient and the sealing admission as separate structures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

def SealedCanonicalPattern (sort : Srt) :=
  {pattern : CanonicalPattern [] sort // binderSafeAt "NQuote" 0 pattern.val = true}

def sealedClassEquiv (sort : Srt) :
    {value : TermQ rhoSourceE [] sort // HasQuoteSafeRepresentative value} ≃
      SealedCanonicalPattern sort where
  toFun := fun value =>
    ⟨encodeCanonical value.val, (has_quote_safe_representative_iff value.val).mp value.property⟩
  invFun := fun pattern =>
    ⟨decodeCanonical pattern.val, (has_quote_safe_representative_iff _).mpr (by
      change binderSafeAt "NQuote" 0 (encodeCanonical (decodeCanonical pattern.val)).val = true
      rw [encode_decode]
      exact pattern.property)⟩
  left_inv := fun value => Subtype.ext (decode_encode value.val)
  right_inv := fun pattern => Subtype.ext (encode_decode pattern.val)

def authoredSort : Srt → LangSort rhoCalc
  | .nm => rhoName
  | .pr => rhoProc

theorem authored_closed_admission (sort : Srt) (pattern : Pattern) :
    RhoClosedTermWellSorted (authoredSort sort) pattern ↔
      Sorted [] sort pattern ∧ binderSafeAt "NQuote" 0 pattern = true := by
  cases sort with
  | nm => exact rhoClosedTermWellSorted_name_iff pattern
  | pr => exact rhoClosedTermWellSorted_process_iff pattern

def AuthoredCanonicalCarrier (sort : Srt) :=
  {term : RhoClosedTerm (authoredSort sort) // canonicalize term.val = term.val}

def authoredSealedEquiv (sort : Srt) :
    SealedCanonicalPattern sort ≃ AuthoredCanonicalCarrier sort where
  toFun := fun pattern =>
    ⟨⟨pattern.val.val, (authored_closed_admission sort _).mpr
      ⟨pattern.val.property.1, pattern.property⟩⟩, pattern.val.property.2⟩
  invFun := fun term =>
    ⟨⟨term.val.val, ((authored_closed_admission sort _).mp term.val.property).1,
      term.property⟩, ((authored_closed_admission sort _).mp term.val.property).2⟩
  left_inv := fun pattern => by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := fun term => by apply Subtype.ext; apply Subtype.ext; rfl

def authoredClosedClassEquiv (sort : Srt) :
    {value : TermQ rhoSourceE [] sort // HasQuoteSafeRepresentative value} ≃
      AuthoredCanonicalCarrier sort := (sealedClassEquiv sort).trans (authoredSealedEquiv sort)

theorem authoredClosedClassEquiv_pattern (sort : Srt)
    (value : {value : TermQ rhoSourceE [] sort // HasQuoteSafeRepresentative value}) :
    (authoredClosedClassEquiv sort value).val.val = encodeEquationClass value.val := rfl

theorem authoredClosedClassEquiv_inverse (sort : Srt)
    (term : AuthoredCanonicalCarrier sort) :
    authoredClosedClassEquiv sort ((authoredClosedClassEquiv sort).symm term) = term :=
  (authoredClosedClassEquiv sort).apply_symm_apply term

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
