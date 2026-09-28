import Mettapedia.Languages.Agda.Adequacy.StaticReflectionData

/-!
# Source interpretation of the structural static rule table

Every ordered premise is interpreted by an actual source derivation. Observation
equations align their dependent boundaries; they never supply a typing premise.
The algebra below is independent of the recursive proof family in which these
eighteen rule shapes are used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Reflection

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural.Statics

def interpretRule {j : Judgment} (shape : RuleShape j)
    (ih : Evidence Interpretation (premises shape)) : Interpretation j := by
  cases shape <;> simp only [premises] at ih
  case empty => exact ⟨.nil, rfl, .nil⟩
  case extend Γ A =>
    let prior := ih 0
    let entry := ih 1 prior.value prior.observed
    exact ⟨prior.value.snoc entry.value, Observation.context_snoc prior.observed entry.observed,
      .snoc prior.proof entry.proof⟩
  case formation Γ k a =>
    intro Δ ctx
    let value := ih 0 Δ ctx
    exact ⟨.el k value.value, Observation.typeParameter_observed ⟨k, a⟩ value.observed,
      .ofTyping (value.atType (Observation.universeType_observed _ k))⟩
  case sort Γ k =>
    intro Δ ctx
    exact ⟨.sort k, .universe (k + 1), rfl, rfl, .sort k ((ih 0).at ctx)⟩
  case «variable» Γ v =>
    intro Δ ctx
    exact ⟨.var (readVar v), Δ.lookup (readVar v), rfl, Observation.context_lookup ctx v,
      .var (readVar v) ((ih 0).at ctx)⟩
  case pi Γ A B =>
    intro Δ ctx
    let domain := ih 0 Δ ctx
    let codomain := ih 1 (Δ.snoc domain.value) (Observation.context_snoc ctx domain.observed)
    let body := Observation.typeBodyView B codomain.observed
    refine ⟨.pi domain.value body.body, .universe (max A.level B.level),
      Observation.typeBody_pi_observed domain.observed body.observed, rfl, ?_⟩
    have typed := StaticSpecification.Typing.pi domain.proof (codomain.at (Observation.typeBody_open_observed body.observed))
    simpa only [Observation.typeParameter_level A domain.observed,
      Observation.typeBody_level B body.observed] using typed
  case lambda Γ A B body =>
    intro Δ ctx
    let domain := ih 0 Δ ctx
    let extended := Observation.context_snoc ctx domain.observed
    let codomain := ih 1 (Δ.snoc domain.value) extended
    let termValue := ih 2 (Δ.snoc domain.value) extended
    let sourceBody := Observation.typeBodyView B codomain.observed
    let sourceTerm := Observation.termBodyView body termValue.observed
    refine ⟨.lam sourceTerm.body, .pi domain.value sourceBody.body,
      Observation.termBody_lambda_observed sourceTerm.observed,
      Observation.piType_observed A B domain.observed sourceBody.observed, ?_⟩
    exact .lam domain.proof (codomain.at (Observation.typeBody_open_observed sourceBody.observed))
      (termValue.at (termValue.observed.trans (congrArg some sourceTerm.open_eq).symm)
        (Observation.typeBody_open_observed sourceBody.observed))
  case application Γ A B f a =>
    intro Δ ctx
    let head := ih 0 Δ ctx
    let argument := ih 1 Δ ctx
    let parts := Observation.piView A B head.typeObserved
    exact ⟨head.value.app argument.value, parts.body.instantiate argument.value,
      Observation.app_observed head.observed argument.observed,
      Observation.typeBody_instantiate B parts.body_eq argument.observed,
      .app (head.atType (Observation.piType_observed A B parts.domain_eq parts.body_eq))
        (argument.atType parts.domain_eq)⟩
  case conversion Γ t A B =>
    intro Δ ctx
    let value := ih 0 Δ ctx
    let equality := ih 1 Δ ctx
    exact ⟨value.value, equality.right, value.observed, equality.rightObserved,
      .conv (value.atType equality.leftObserved) equality.proof⟩
  case typeEquality Γ k a b =>
    intro Δ ctx
    let equal := ih 0 Δ ctx
    exact ⟨.el k equal.left, .el k equal.right,
      Observation.typeParameter_observed ⟨k, a⟩ equal.leftObserved,
      Observation.typeParameter_observed ⟨k, b⟩ equal.rightObserved,
      .atSort (equal.atType (Observation.universeType_observed _ k))⟩
  case reflexivity Γ t A =>
    intro Δ ctx
    let value := ih 0 Δ ctx
    exact ⟨value.value, value.value, value.typeValue, value.observed, value.observed, value.typeObserved,
      .refl value.proof⟩
  case symmetry Γ t u A =>
    intro Δ ctx
    let value := ih 0 Δ ctx
    exact ⟨value.right, value.left, value.typeValue, value.rightObserved, value.leftObserved,
      value.typeObserved, .symm value.proof⟩
  case transitivity Γ t u v A =>
    intro Δ ctx
    let first := ih 0 Δ ctx
    let second := ih 1 Δ ctx
    exact ⟨first.left, second.right, first.typeValue, first.leftObserved, second.rightObserved,
      first.typeObserved, .trans first.proof
        (second.at first.rightObserved second.rightObserved first.typeObserved)⟩
  case equalityConversion Γ t u A B =>
    intro Δ ctx
    let terms := ih 0 Δ ctx
    let types := ih 1 Δ ctx
    exact ⟨terms.left, terms.right, types.right, terms.leftObserved, terms.rightObserved, types.rightObserved,
      .conv (terms.atType types.leftObserved) types.proof⟩
  case piCongruence Γ A A' B B' =>
    intro Δ ctx
    let domain := ih 0 Δ ctx
    let domains := ih 1 Δ ctx
    let codomains := ih 2 (Δ.snoc domain.value) (Observation.context_snoc ctx domain.observed)
    let firstBody := Observation.typeBodyView B codomains.leftObserved
    let secondBody := Observation.typeBodyView B' codomains.rightObserved
    refine ⟨.pi domain.value firstBody.body, .pi domains.right secondBody.body,
      .universe (max A.level B.level),
      Observation.typeBody_pi_observed domain.observed firstBody.observed,
      Observation.typeBody_pi_observed domains.rightObserved secondBody.observed, rfl, ?_⟩
    have typed := StaticSpecification.TermEq.piCong domain.proof
      (domains.at domain.observed domains.rightObserved)
      (codomains.at (Observation.typeBody_open_observed firstBody.observed)
        (Observation.typeBody_open_observed secondBody.observed))
    simpa only [Observation.typeParameter_level A domain.observed,
      Observation.typeBody_level B firstBody.observed] using typed
  case applicationCongruence Γ A B f g a b =>
    intro Δ ctx
    let heads := ih 0 Δ ctx
    let args := ih 1 Δ ctx
    let parts := Observation.piView A B heads.typeObserved
    exact ⟨heads.left.app args.left, heads.right.app args.right, parts.body.instantiate args.left,
      Observation.app_observed heads.leftObserved args.leftObserved,
      Observation.app_observed heads.rightObserved args.rightObserved,
      Observation.typeBody_instantiate B parts.body_eq args.leftObserved,
      .appCong (heads.atType (Observation.piType_observed A B parts.domain_eq parts.body_eq))
        (args.atType parts.domain_eq)⟩
  case beta Γ A B body a =>
    intro Δ ctx
    let domain := ih 0 Δ ctx
    let extended := Observation.context_snoc ctx domain.observed
    let codomain := ih 1 (Δ.snoc domain.value) extended
    let termValue := ih 2 (Δ.snoc domain.value) extended
    let argument := ih 3 Δ ctx
    let sourceBody := Observation.typeBodyView B codomain.observed
    let sourceTerm := Observation.termBodyView body termValue.observed
    refine ⟨(StaticSpecification.Term.lam sourceTerm.body).app argument.value,
      sourceTerm.body.instantiate argument.value, sourceBody.body.instantiate argument.value,
      Observation.app_observed (Observation.termBody_lambda_observed sourceTerm.observed) argument.observed,
      Observation.termBody_instantiate_observed sourceTerm.observed argument.observed,
      Observation.typeBody_instantiate B sourceBody.observed argument.observed, ?_⟩
    exact .beta domain.proof (codomain.at (Observation.typeBody_open_observed sourceBody.observed))
      (termValue.at (termValue.observed.trans (congrArg some sourceTerm.open_eq).symm)
        (Observation.typeBody_open_observed sourceBody.observed)) (argument.atType domain.observed)
  case eta Γ A B f g =>
    intro Δ ctx
    let domain := ih 0 Δ ctx
    let extended := Observation.context_snoc ctx domain.observed
    let codomain := ih 1 (Δ.snoc domain.value) extended
    let head := ih 2 Δ ctx
    let other := ih 3 Δ ctx
    let equal := ih 4 (Δ.snoc domain.value) extended
    let sourceBody := Observation.typeBodyView B codomain.observed
    let inputObserved := Observation.piType_observed A B domain.observed sourceBody.observed
    have headWeak : Observation.term (bind (Telescope.projection (S := Structural.sig) .term _) f) =
        some head.value.weaken := (Observation.projection_observed f).trans
          (congrArg (Option.map StaticSpecification.Term.weaken) head.observed)
    have otherWeak : Observation.term (bind (Telescope.projection (S := Structural.sig) .term _) g) =
        some other.value.weaken := (Observation.projection_observed g).trans
          (congrArg (Option.map StaticSpecification.Term.weaken) other.observed)
    exact ⟨head.value, other.value, .pi domain.value sourceBody.body, head.observed, other.observed,
      inputObserved, .eta domain.proof (codomain.at (Observation.typeBody_open_observed sourceBody.observed))
        (head.atType inputObserved) (other.atType inputObserved)
        (equal.at (Observation.app_observed headWeak (Observation.variable_eq (n := _ + 1) .zero))
          (Observation.app_observed otherWeak (Observation.variable_eq (n := _ + 1) .zero))
          (Observation.typeBody_open_observed sourceBody.observed))⟩

end Mettapedia.Languages.Agda.StaticAdequacy.Reflection
