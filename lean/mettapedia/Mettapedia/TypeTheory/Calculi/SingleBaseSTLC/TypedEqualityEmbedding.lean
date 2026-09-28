import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Conversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction

/-!
# The simple fragment uses the dependent calculus's typed judgment

The existing atom/arrow translation uses the dependent calculus's actual
variables, lambdas, applications and nondependent products. Its typing,
substitution and beta conversion are validated by `TypedEquality`, with no
second typing kernel. The result works for every rule package extending the
displayed head, universe and product rules; constants and computation rules
are unrestricted parameters.

This theorem does not reflect arbitrary dependent inhabitants into simple
syntax. It preserves source beta conversion; the target also has eta, so it
does not assert reflection into a beta-only source equality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TypedEqualityEmbedding

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open IntrinsicSTT TowerDTT SubstitutionTranslation

/-- Only formation rules are required of the selected dependent package. -/
structure HeadRules (R : Rules Tower.Head) : Prop where
  ground : R.headTyping .legacyGround (.sort Tower.zero)
  universes : ∀ l, R.isUniverse (.sort l)
  product : ∀ l k, R.join (.sort l) (.sort k) (.sort (.max l k))

variable {R : Rules Tower.Head} (heads : HeadRules R)
variable {Γ Δ : List Ty} {A B : Ty}

include heads

theorem type_formed (type : Ty) {n : Nat} (context : Tower.Ctx n) :
    Typed R context (eraseTypeAt n type) (sortTm (levelOf type)) := by
  induction type generalizing n with
  | atom => exact .headType heads.ground
  | arr domain codomain domainIH codomainIH =>
      exact .piForm (domainIH context) (heads.universes _)
        (codomainIH (.snoc context (eraseTypeAt n domain))) (heads.universes _)
        (heads.product _ _)

theorem context_formed (context : List Ty) : CtxFormed R (eraseContext context) := by
  induction context with
  | nil => exact .nil
  | cons head tail ih =>
      exact .snoc ih ⟨_, heads.universes _, type_formed heads head (eraseContext tail)⟩

theorem term_typed (term : Term Γ A) :
    Typed R (eraseContext Γ) (eraseTerm term) (eraseTypeAt Γ.length A) := by
  induction term with
  | var typedVar =>
      simpa only [eraseTerm, lookup_eraseContext] using
        (Derivable.var (R := R) (Γ := eraseContext _) (eraseVar typedVar))
  | @lam domain context codomain body ih =>
      exact .lamIntro (type_formed heads (.arr domain codomain) (eraseContext context))
        (heads.universes _) ih
  | app function argument functionIH argumentIH =>
      simpa only [eraseTerm, eraseTypeAt, inst0, eraseTypeAt_subst] using
        (Derivable.appElim functionIH argumentIH)

theorem substitution_typed (σ : Substitution Γ Δ) :
    SubstMor R (eraseContext Γ) (eraseContext Δ) (eraseSubstitution σ) := by
  intro index
  have typed := term_typed heads (σ (typedVarAt Γ index))
  have lookup := lookup_eraseContext (typedVarAt Γ index)
  rw [eraseVar_typedVarAt] at lookup
  change Typed R (eraseContext Δ) (eraseSubstitution σ index)
    (Presentation.subst (eraseSubstitution σ) ((eraseContext Γ).lookup index))
  rw [lookup, eraseTypeAt_subst]
  simpa only [← eraseSubstitution_apply, eraseVar_typedVarAt] using typed

/-- Both substitution routes have the same term, and the native structural
rule checks the route that substitutes after translation. -/
theorem substitution_square (σ : Substitution Γ Δ) (term : Term Γ A) :
    eraseTerm (term.substitute σ) = Presentation.subst (eraseSubstitution σ) (eraseTerm term) ∧
    Typed R (eraseContext Δ) (Presentation.subst (eraseSubstitution σ) (eraseTerm term))
      (eraseTypeAt Δ.length A) := by
  refine ⟨eraseTerm_substitute σ term, ?_⟩
  simpa only [eraseTypeAt_subst] using
    (term_typed heads term).substitute (substitution_typed heads σ)

theorem beta_equal (body : Term (A :: Γ) B) (argument : Term Γ A) :
    Equal R (eraseContext Γ) (eraseTerm (.app (.lam body) argument))
      (eraseTerm (body.instantiateNewest argument)) (eraseTypeAt Γ.length B) := by
  have eq := Derivable.betaPi
    (type_formed heads (.arr A B) (eraseContext Γ)) (heads.universes _)
    (term_typed heads body) (term_typed heads argument)
  simpa only [eraseTerm, eraseTypeAt, inst0, eraseTypeAt_subst,
    eraseTerm_instantiateNewest] using eq

theorem step_equal {left right : Term Γ A} (step : BetaStep left right) :
    Equal R (eraseContext Γ) (eraseTerm left) (eraseTerm right) (eraseTypeAt Γ.length A) := by
  induction step with
  | beta body argument => exact beta_equal heads body argument
  | @lam Γ A B body body' _ ih =>
      exact .lamCong (type_formed heads (.arr A B) (eraseContext Γ)) (heads.universes _) ih
  | appLeft step ih =>
      simpa only [eraseTerm, eraseTypeAt, inst0, eraseTypeAt_subst] using
        (Derivable.appCong ih (.refl (term_typed heads _)))
  | @appRight Γ A B f a a' step ih =>
      simpa only [eraseTerm, eraseTypeAt, inst0, eraseTypeAt_subst] using
        (Derivable.appCong (.refl (term_typed heads f)) ih)

theorem conversion_equal {left right : Term Γ A} (conversion : BetaConv left right) :
    Equal R (eraseContext Γ) (eraseTerm left) (eraseTerm right) (eraseTypeAt Γ.length A) := by
  induction conversion with
  | rel _ _ step => exact step_equal heads step
  | refl term => exact .refl (term_typed heads term)
  | symm _ _ _ ih => exact .symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

omit heads

/-- The closed cumulative tower supplies the actual formation rules. -/
theorem towerHeads : HeadRules Tower.rules :=
  ⟨.legacyGround, fun _ => .sort _, fun _ _ => .sorts _ _⟩

/-- A genuine beta computation: source and target differ as syntax. -/
theorem canonical_beta :
    Equal Tower.rules (eraseContext canonicalContext)
      (eraseTerm canonicalClaim.source) (eraseTerm canonicalClaim.target)
      (.head .legacyGround) ∧
    eraseTerm canonicalClaim.source ≠ eraseTerm canonicalClaim.target :=
  ⟨beta_equal towerHeads canonicalBody canonicalArgument, canonical_source_ne_target⟩

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TypedEqualityEmbedding
