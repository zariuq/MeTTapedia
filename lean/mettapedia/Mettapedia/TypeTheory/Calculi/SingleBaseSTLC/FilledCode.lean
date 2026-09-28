import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CanonicalCode

/-!
# Filling a sealed template with values

A quotation keeps its authored syntax, so it may not observe how a program was
reached. Substitution into a quotation is coherent exactly when what is
substituted is a value: two beta-equal normal forms are one term, so plugging
values into a sealed template respects conversion, while plugging an
unevaluated argument quotes the route by which it was reached.

`fill` plugs the value of an argument into a template's hole and keeps the
template's own syntax, redexes included. It is congruent in the argument, runs
as the template at the argument, and on an argument that is already a value it
is plain substitution. A `let` that binds a value and then builds a quotation
is therefore coherent; beta reduction with an unevaluated argument is not.

Filling an open argument and substituting into it later gives a different
name from substituting first and then filling. Filling therefore happens when
the construction runs, on closed values, never beneath a binder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.IntensionalCode

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision

universe u

variable {Γ : List Ty} {A B : Ty} {Ground : Type u}

/-- Plug the value of an argument into a template's hole. The template keeps
its authored syntax. -/
def fill (template : CodeName (A :: Γ) B) (argument : Term Γ A) : CodeName Γ B :=
  template.splice (canonicalQuote argument)

/-- **Values are canonical**: two beta-equal normal forms are one term. -/
theorem value_eq_of_betaConv {value value' : Term Γ A} (normal : Normal value)
    (normal' : Normal value') (equal : BetaConv value value') : value = value' := by
  have same := (normalize_eq_iff_betaConv value value').2 equal
  rwa [normalize_of_irreducible value (Normal.iff_no_betaStep.mp normal),
    normalize_of_irreducible value' (Normal.iff_no_betaStep.mp normal')] at same

/-- **Substituting values into a quotation respects conversion.** -/
theorem splice_values_respects_beta (template : CodeName (A :: Γ) B)
    {value value' : Term Γ A} (normal : Normal value) (normal' : Normal value')
    (equal : BetaConv value value') :
    template.splice ⟨value⟩ = template.splice ⟨value'⟩ := by
  rw [value_eq_of_betaConv normal normal' equal]

/-- On a value, filling is plain substitution into the template. -/
theorem fill_value (template : CodeName (A :: Γ) B) {value : Term Γ A}
    (normal : Normal value) : fill template value = template.splice ⟨value⟩ := by
  unfold fill canonicalQuote
  rw [normalize_of_irreducible value (Normal.iff_no_betaStep.mp normal)]

/-- **Filling respects conversion of the argument.** -/
theorem fill_respects_beta (template : CodeName (A :: Γ) B) {argument argument' : Term Γ A}
    (equal : BetaConv argument argument') : fill template argument = fill template argument' := by
  unfold fill
  rw [canonicalQuote_respects_beta equal]

/-- Filling runs as the template at the argument. -/
theorem fill_run (template : CodeName (A :: Γ) B) (argument : Term Γ A)
    (environment : Environment Ground Γ) :
    (fill template argument).run environment =
      (template.splice ⟨argument⟩).run environment := by
  unfold fill
  rw [CodeName.run_splice, CodeName.run_splice, canonicalQuote_preserves_run]
  rfl

/-- The bare hole, as a template. -/
def hole : CodeName (A :: Γ) A := ⟨.var .zero⟩

/-- **Substituting an unevaluated argument into a quotation is not coherent**:
one program, reached by two conversion routes, is quoted as two names. -/
theorem splice_as_written_not_coherent :
    BetaConv redexCode.body identityCode.body ∧
      (hole (Γ := [])).splice redexCode ≠ (hole (Γ := [])).splice identityCode :=
  ⟨constructed_redex_beta_converts,
    fun equal => constructed_redex_is_not_identity_syntax (congrArg CodeName.body equal)⟩

/-- The identity applied to the hole: a template with a redex of its own. -/
def applyIdentityTemplate : CodeName [FunctionType] FunctionType :=
  ⟨.app (.lam (.var .zero)) (.var .zero)⟩

/-- **Filling keeps the template's authored syntax.** Its own redex survives,
while canonicalizing the whole result would remove it. -/
theorem fill_keeps_template_redex :
    fill applyIdentityTemplate identityCode.body = redexCode ∧
      canonicalQuote (applyIdentityTemplate.splice identityCode).body = identityCode := by
  refine ⟨?_, ?_⟩
  · unfold fill
    rw [canonicalQuote_identity]
    rfl
  · have spliced : (applyIdentityTemplate.splice identityCode).body = redexCode.body := rfl
    rw [spliced, canonicalQuote_forgets_redex_shape, canonicalQuote_identity]

/-! ## Filling happens on closed values -/

/-- A context holding one function on functions. -/
abbrev WrapperContext : List Ty := [.arr FunctionType FunctionType]

/-- `y (λz. z)` with `y` free: a value, since its head is a variable. -/
def openApplication : Term WrapperContext FunctionType := .app (.var .zero) (.lam (.var .zero))

theorem openApplication_irreducible : ∀ target, ¬ BetaStep openApplication target := by
  intro target step
  cases step with
  | appLeft inner => cases inner
  | appRight inner =>
      cases inner with
      | lam inner' => cases inner'

/-- Later, `y` is instantiated with the identity on functions. -/
def wrapperSubstitution : Substitution WrapperContext [] :=
  fun {_} typedVar => match typedVar with
    | .zero => identityWrapper.body

/-- **Filling beneath a binder is not stable under the later substitution.**
Filling the open value and then substituting yields a redex; substituting
first and then filling yields its value. The two names differ, though they
name convertible programs. -/
theorem fill_then_substitute_differs :
    (fill (hole (Γ := WrapperContext)) openApplication).reindex wrapperSubstitution =
        redexCode ∧
      fill (hole (Γ := [])) (openApplication.substitute wrapperSubstitution) = identityCode ∧
      redexCode ≠ identityCode ∧
      BetaConv redexCode.body identityCode.body := by
  have normal : canonicalQuote openApplication = ⟨openApplication⟩ :=
    congrArg CodeName.mk (normalize_of_irreducible _ openApplication_irreducible)
  refine ⟨?_, ?_, ?_, constructed_redex_beta_converts⟩
  · unfold fill
    rw [normal]
    rfl
  · unfold fill
    have substituted : openApplication.substitute wrapperSubstitution = redexCode.body := rfl
    rw [substituted, canonicalQuote_forgets_redex_shape, canonicalQuote_identity]
    rfl
  · exact fun equal => constructed_redex_is_not_identity_syntax (congrArg CodeName.body equal)

#print axioms value_eq_of_betaConv
#print axioms fill_respects_beta
#print axioms fill_run
#print axioms splice_as_written_not_coherent
#print axioms fill_keeps_template_redex
#print axioms fill_then_substitute_differs

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.IntensionalCode
