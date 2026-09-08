import Mettapedia.Languages.Megalodon.HenkinErasureInversion
import Mettapedia.Languages.Megalodon.HenkinTermSubstitution
import Mettapedia.Languages.Megalodon.HenkinTermStrengthening
import Mettapedia.Languages.Megalodon.HenkinDeltaSemantics

/-!
# Henkin semantics of native beta/eta normalization

The actual native normalization pass preserves the intrinsic interpretation of
its supported input syntax. Beta substitution and eta strengthening preserve
literal denotation, even in models with proper Henkin function domains. This
does not identify arbitrary extensionally related function arguments.

The iterated theorem concerns successful finite-fuel executions. Definition
unfolding additionally requires the independent equations of the chosen model.
Prefix type abstraction and specialization are outside this term interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

universe w

variable {environment : Environment} {Γ : Ctx Base} {τ σ : Ty Base}

private theorem beta_head_interpretation
    (function : Term (Constant environment) Γ (σ ⇒ τ))
    (argument : Term (Constant environment) Γ σ) {rawFunction rawArgument : Tm}
    (erasedFunction : erase function = some rawFunction)
    (erasedArgument : erase argument = some rawArgument) :
    ∃ result : Term (Constant environment) Γ τ,
      erase result = some (match (generalizing := false) rawFunction with
        | .lam _ body => Tm.instantiate rawArgument body
        | _ => .app rawFunction rawArgument) ∧
      ∀ (M : HenkinModel.{0, 0, w} Base (Constant environment)) (valuation : M.Valuation Γ),
        M.denote result valuation = M.denote (.app function argument) valuation := by
  cases rawFunction with
  | lam rawType rawBody =>
      obtain ⟨body, rfl, _, erasedBody⟩ := erase_lam_inv erasedFunction
      refine ⟨instantiate argument body, ?_, ?_⟩
      · rw [erase_instantiate argument body erasedArgument, erasedBody]
        rfl
      · intro M valuation
        exact Soundness.denote_instantiate_term M argument body valuation
  | db | named | prim | app | imp | all | typeApp | typeLam | typeAll =>
      exact ⟨.app function argument, by simp [erase, erasedFunction, erasedArgument],
        fun _ _ => rfl⟩

private theorem eta_head_interpretation
    (body : Term (Constant environment) (σ :: Γ) τ) {rawBody : Tm}
    (erasedBody : erase body = some rawBody) :
    ∃ result : Term (Constant environment) Γ (σ ⇒ τ),
      erase result = some (match (generalizing := false) rawBody with
        | .app function (.db 0) =>
            match Tm.dropAt? 0 function with
            | some contracted => contracted
            | none => .lam (reifyType σ) rawBody
        | _ => .lam (reifyType σ) rawBody) ∧
      ∀ (M : HenkinModel.{0, 0, w} Base (Constant environment)) (valuation : M.Valuation Γ),
        M.denote result valuation = M.denote (.lam body) valuation := by
  cases rawBody with
  | app rawFunction rawArgument =>
      cases rawArgument with
      | db index =>
          cases index with
          | zero =>
              cases dropped : Tm.dropAt? 0 rawFunction with
              | none =>
                  exact ⟨.lam body, by simp [dropped, erase, erasedBody], fun _ _ => rfl⟩
              | some contracted =>
                  obtain ⟨a, function, argument, rfl, erasedFunction, erasedArgument⟩ :=
                    erase_app_inv erasedBody
                  obtain ⟨rfl, equalArgument⟩ := erase_db_zero_inv erasedArgument
                  have sameArgument := eq_of_heq equalArgument
                  subst argument
                  obtain ⟨lowered, erasedLowered, equalFunction⟩ :=
                    erase_dropAt?_strengthen function erasedFunction dropped
                  refine ⟨lowered, by simpa [dropped] using erasedLowered, ?_⟩
                  intro M valuation
                  subst function
                  funext x
                  change M.denote lowered valuation x =
                    M.denote (weaken lowered) (M.extend valuation x) x
                  rw [Soundness.denote_weaken]
          | succ index =>
              refine ⟨.lam body, ?_, fun _ _ => rfl⟩
              simp [erase, erasedBody]
      | named | prim | app | lam | imp | all | typeApp | typeLam | typeAll =>
          exact ⟨.lam body, by simp [erase, erasedBody], fun _ _ => rfl⟩
  | db | named | prim | lam | imp | all | typeApp | typeLam | typeAll =>
      exact ⟨.lam body, by simp [erase, erasedBody], fun _ _ => rfl⟩

/-- One actual native pass has an intrinsic output of the same type and the
same literal denotation. Unsupported prefix syntax is not silently erased. -/
theorem normalizeOne_interpretation (term : Term (Constant environment) Γ τ)
    {raw : Tm} (erased : erase term = some raw) :
    ∃ result : Term (Constant environment) Γ τ,
      erase result = some (Tm.normalizeOne raw).1 ∧
      ∀ (M : HenkinModel.{0, 0, w} Base (Constant environment)) (valuation : M.Valuation Γ),
        M.denote result valuation = M.denote term valuation := by
  induction term generalizing raw with
  | var v =>
      simp only [erase, Option.some.injEq] at erased
      subst raw
      exact ⟨.var v, rfl, fun _ _ => rfl⟩
  | const c =>
      cases c <;> simp only [erase, Constant.erase, Option.some.injEq] at erased <;>
        subst raw <;> exact ⟨_, rfl, fun _ _ => rfl⟩
  | app function argument ihf iha =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
      subst raw
      obtain ⟨f', ef', sf'⟩ := ihf hf
      obtain ⟨a', ea', sa'⟩ := iha ha
      obtain ⟨result, resultErased, resultMeaning⟩ := beta_head_interpretation f' a' ef' ea'
      refine ⟨result, ?_, ?_⟩
      · simp only [Tm.normalizeOne]
        split <;> simp only [*]
      · intro M valuation
        exact (resultMeaning M valuation).trans (by
          change M.denote f' valuation (M.denote a' valuation) =
            M.denote function valuation (M.denote argument valuation)
          rw [sf', sa'])
  | lam body ih =>
      cases hb : erase body <;>
        simp [erase, hb] at erased
      subst raw
      obtain ⟨body', bodyErased, bodyMeaning⟩ := ih hb
      obtain ⟨result, resultErased, resultMeaning⟩ := eta_head_interpretation body' bodyErased
      refine ⟨result, ?_, ?_⟩
      · simp only [Tm.normalizeOne]
        split
        · split <;> simp only [*]
        · simp only [*]
      · intro M valuation
        exact (resultMeaning M valuation).trans (by
          funext x
          exact bodyMeaning M (M.extend valuation x))
  | imp left right ihl ihr =>
      cases hl : erase left <;> cases hr : erase right <;>
        simp [erase, hl, hr] at erased
      subst raw
      obtain ⟨left', erasedLeft, meaningLeft⟩ := ihl hl
      obtain ⟨right', erasedRight, meaningRight⟩ := ihr hr
      refine ⟨.imp left' right', ?_, ?_⟩
      · simp [erase, erasedLeft, erasedRight, Tm.normalizeOne]
      · intro M valuation
        change ULift.up ((M.denote left' valuation).down → (M.denote right' valuation).down) =
          ULift.up ((M.denote left valuation).down → (M.denote right valuation).down)
        rw [meaningLeft, meaningRight]
  | all body ih =>
      cases hb : erase body <;>
        simp [erase, hb] at erased
      subst raw
      obtain ⟨body', bodyErased, bodyMeaning⟩ := ih hb
      refine ⟨.all body', ?_, ?_⟩
      · simp [erase, bodyErased, Tm.normalizeOne]
      · intro M valuation
        change ULift.up (∀ x, M.adm _ x → (M.denote body' (M.extend valuation x)).down) =
          ULift.up (∀ x, M.adm _ x → (M.denote body (M.extend valuation x)).down)
        simp only [bodyMeaning]
  | top | bot | and | or | not | eq | ex => simp [erase] at erased

/-- Successful finite-fuel beta/eta normalization has an intrinsic output of
the same type and literal denotation. This is conditional on the actual native
success, not a termination or normalization-completeness theorem. -/
theorem betaEtaNormalize_interpretation (term : Term (Constant environment) Γ τ)
    {raw result : Tm} {fuel : Nat} (erased : erase term = some raw)
    (normalized : Tm.normalize fuel raw = some result) :
    ∃ output : Term (Constant environment) Γ τ,
      erase output = some result ∧
      ∀ (M : HenkinModel.{0, 0, w} Base (Constant environment)) (valuation : M.Valuation Γ),
        M.denote output valuation = M.denote term valuation := by
  induction fuel generalizing term raw with
  | zero =>
      obtain ⟨output, outputErased, outputMeaning⟩ := normalizeOne_interpretation term erased
      simp only [Tm.normalize] at normalized
      split at normalized
      · have resultEqual := Option.some.inj normalized
        exact ⟨output, outputErased.trans (congrArg some resultEqual), outputMeaning⟩
      · cases normalized
  | succ fuel ih =>
      obtain ⟨intermediate, intermediateErased, intermediateMeaning⟩ :=
        normalizeOne_interpretation term erased
      simp only [Tm.normalize] at normalized
      split at normalized
      · have resultEqual := Option.some.inj normalized
        exact ⟨intermediate, intermediateErased.trans (congrArg some resultEqual),
          intermediateMeaning⟩
      · obtain ⟨output, outputErased, outputMeaning⟩ := ih intermediate intermediateErased normalized
        exact ⟨output, outputErased, fun M valuation =>
          (outputMeaning M valuation).trans (intermediateMeaning M valuation)⟩

/-- The native pipeline unfolds definitions before beta/eta normalization.
The same-typed output and exact erasure do not depend on a model. Its meaning
is preserved when that model satisfies the independently supplied declaration
equations; no such equations are inferred from native typing. -/
theorem nativeNormalize_interpretation (checked : CheckedPlainDefinitions environment)
    (term : Term (Constant environment) Γ τ) {raw result : Tm} {fuel : Nat}
    (erased : erase term = some raw)
    (normalized : MathdataKernel.normalize environment fuel raw = some result) :
    ∃ output : Term (Constant environment) Γ τ,
      erase output = some result ∧
      ∀ (M : HenkinModel.{0, 0, w} Base (Constant environment)),
        DefinitionEquations checked M → ∀ valuation : M.Valuation Γ,
          M.denote output valuation = M.denote term valuation := by
  obtain ⟨expanded, expansion, normalization⟩ := Option.bind_eq_some_iff.mp normalized
  obtain ⟨intermediate, interpreted, intermediateErased⟩ :=
    (deltaNormalize_eq_some_iff checked fuel term erased).mp expansion
  obtain ⟨output, outputErased, outputMeaning⟩ :=
    betaEtaNormalize_interpretation intermediate intermediateErased normalization
  refine ⟨output, outputErased, ?_⟩
  intro M equations valuation
  exact (outputMeaning M valuation).trans
    (denote_deltaInterpretation checked M equations fuel term intermediate interpreted valuation)

/-- For independently supplied intrinsic endpoints, actual beta/eta success
implies equality of their meanings in every Henkin model. -/
theorem denote_betaEtaNormalize
    (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (term output : Term (Constant environment) Γ τ) {raw result : Tm} {fuel : Nat}
    (erased : erase term = some raw) (outputErased : erase output = some result)
    (normalized : Tm.normalize fuel raw = some result) (valuation : M.Valuation Γ) :
    M.denote output valuation = M.denote term valuation := by
  obtain ⟨interpreted, interpretedErased, meaning⟩ :=
    betaEtaNormalize_interpretation term erased normalized
  have same : interpreted = output := erase_injective_of_eq_some interpretedErased outputErased
  subst interpreted
  exact meaning M valuation

/-- Same-model preservation for the complete actual delta/beta/eta pipeline,
with independently supplied intrinsic input and output terms. -/
theorem denote_nativeNormalize (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (equations : DefinitionEquations checked M)
    (term output : Term (Constant environment) Γ τ) {raw result : Tm} {fuel : Nat}
    (erased : erase term = some raw) (outputErased : erase output = some result)
    (normalized : MathdataKernel.normalize environment fuel raw = some result)
    (valuation : M.Valuation Γ) : M.denote output valuation = M.denote term valuation := by
  obtain ⟨interpreted, interpretedErased, meaning⟩ :=
    nativeNormalize_interpretation checked term erased normalized
  have same : interpreted = output := erase_injective_of_eq_some interpretedErased outputErased
  subst interpreted
  exact meaning M equations valuation

#print axioms normalizeOne_interpretation
#print axioms betaEtaNormalize_interpretation
#print axioms nativeNormalize_interpretation
#print axioms denote_betaEtaNormalize
#print axioms denote_nativeNormalize

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
