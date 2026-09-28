import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonizationData

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Canonization

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics

noncomputable def coreRule {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (children : Evidence CoreDerivation (Statics.premises shape))
    (ih : Evidence CoreMotive (Statics.premises shape)) : CoreMotive j := by
  cases shape <;> simp only [Statics.premises] at children ih
  case empty => exact ⟨.nil, rfl, .nil⟩
  case extend Γ A =>
    let prior := ih 0
    let entry := ih 1
    exact ⟨prior.value.snoc entry.value, Observation.context_snoc prior.observed entry.observed,
      .snoc prior.equality entry.equality⟩
  case formation Γ k a =>
    let term := ih 0
    exact ⟨.el k term.value, Observation.typeParameter_observed ⟨k, a⟩ term.observed,
      Derivation.core (.typeEquality Γ k a (embedTerm term.value))
        (consEvidence CoreDerivation term.equality (noEvidence CoreDerivation))⟩
  case sort Γ k =>
    exact ⟨.sort k, rfl, termReflexivity
      (Derivation.core (.sort Γ k) (consEvidence CoreDerivation (children 0) (noEvidence CoreDerivation)))⟩
  case «variable» Γ v =>
    refine ⟨.var (readVar v), rfl, ?_⟩
    have result := termReflexivity (Derivation.core (.variable Γ v)
      (consEvidence CoreDerivation (children 0) (noEvidence CoreDerivation)))
    simp only [embedTerm, embed_readVar]
    exact result
  case pi Γ A B =>
    let domain := ih 0
    let codomain := ih 1
    let body := Observation.typeBodyView B codomain.observed
    refine ⟨.pi domain.value body.body, Observation.typeBody_pi_observed domain.observed body.observed, ?_⟩
    have domainEqual : CoreDerivation (Statics.typeEqual Γ A.code (embedTypeParameter domain.value).code) := by
      simpa only [embedTypeParameter_code] using domain.equality
    have codomainEqual : CoreDerivation
        (Statics.typeEqual (Γ.snoc A.code) B.open.code (embedTypeBody body.body).open.code) := by
      simpa only [embedTypeBody_open, embedTypeParameter_code] using
        codomain.at (Observation.typeBody_open_observed body.observed)
    have result := Derivation.core (.piCongruence Γ A (embedTypeParameter domain.value) B (embedTypeBody body.body))
      (consEvidence CoreDerivation (children 0) (consEvidence CoreDerivation domainEqual
        (consEvidence CoreDerivation codomainEqual (noEvidence CoreDerivation))))
    simp only [embedTypeBody_pi] at result
    exact result
  case lambda Γ A B body =>
    let term := ih 2
    let view := Observation.termBodyView body term.observed
    refine ⟨.lam view.body, Observation.termBody_lambda_observed view.observed, ?_⟩
    have bodies : CoreDerivation
        (Statics.termEqual (Γ.snoc A.code) body.open (embedTermBody view.body).open B.open.code) := by
      simpa only [embedTermBody_open, view.open_eq] using term.equality
    have result := administrativeOperations.lambdaCongruence (first := body) (second := embedTermBody view.body)
      (children 0) (children 1) (children 2) bodies.termEndpoints.right bodies
    simp only [embedTermBody_lambda] at result
    exact result
  case application Γ A B f u =>
    let head := ih 0
    let argument := ih 1
    refine ⟨head.value.app argument.value, Observation.app_observed head.observed argument.observed, ?_⟩
    exact applicationCongruence (A := A) (B := B) head.equality argument.equality
  case conversion Γ t A B =>
    let term := ih 0
    exact ⟨term.value, term.observed, termConversion term.equality (children 1)⟩
  case typeEquality | reflexivity | symmetry | transitivity | equalityConversion | piCongruence
    | applicationCongruence | beta | eta => exact ⟨⟩

end Mettapedia.Languages.Agda.StaticAdequacy.Canonization
