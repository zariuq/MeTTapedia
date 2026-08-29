import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularAccessibleConversion

/-!
# Normalization semantics for identity witnesses

The regular fragment has identity formation and reflexivity, but no identity
eliminator.  For the strong-normalization theorem, identity witnesses may
therefore be interpreted by the existing contextual normalizing candidate.
This is deliberately only a normalization semantics: it does not identify
endpoints and does not claim to model propositional equality.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction

/-- Accessibility of a reflexivity witness reflects to its payload. -/
theorem reductionAccessible_refl_argument {term : PureTm n}
    (witnessAccessible : ReductionAccessible (.refl term)) :
    ReductionAccessible term := by
  have inversion : ∀ (whole : PureTm n), ReductionAccessible whole →
      ∀ payload, whole = .refl payload → ReductionAccessible payload := by
    intro whole accessible
    induction accessible with
    | intro whole smaller ih =>
        intro payload wholeEq
        subst wholeEq
        constructor
        intro target step
        exact ih (.refl target) (.congRefl step) target rfl
  exact inversion (.refl term) witnessAccessible term rfl

/-- Reflexivity introduction for the normalization interpretation of identity.
The payload may inhabit any contextual candidate; CR1 supplies exactly the
accessibility needed by the reflexivity constructor. -/
theorem contextual_refl_intro_normalizing
    {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context)
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {term : PureTm m} (termCovered : type.pred environment term) :
    (ContextualCandidateType.normalizing context).pred environment
      (.refl term) :=
  reductionAccessible_refl (type.cr1 environmentRealized termCovered)

/-- A concrete reflexivity witness is admitted by the normalization
interpretation. -/
theorem contextual_refl_u0_normalizing :
    (ContextualCandidateType.normalizing CoherentCandidateContext.empty).pred
      (ids : Sub 0 0) (.refl .u0) :=
  reductionAccessible_refl reductionAccessible_u0

/-- Reflexivity does not hide divergence: a witness carrying omega is rejected
by the normalization interpretation. -/
theorem contextual_refl_omega_not_normalizing :
    ¬ (ContextualCandidateType.normalizing CoherentCandidateContext.empty).pred
      (ids : Sub 0 0) (.refl regularOmega) := by
  intro witnessAccessible
  exact omega_not_in_normalizing_candidate
    (reductionAccessible_refl_argument witnessAccessible)

/-! ## Axiom audit -/

#print axioms reductionAccessible_refl_argument
#print axioms contextual_refl_intro_normalizing
#print axioms contextual_refl_u0_normalizing
#print axioms contextual_refl_omega_not_normalizing

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
