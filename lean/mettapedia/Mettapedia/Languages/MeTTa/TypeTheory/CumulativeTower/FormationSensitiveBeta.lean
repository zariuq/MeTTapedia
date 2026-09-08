import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveExamples

/-!
# Root beta preservation for formation-sensitive typing

Generation retains the actual formation-sensitive derivations. Lambda
generation records its original formed Pi and the directed result-type
adjustment. Application generation additionally retains a proved replay of
its conversion and cumulativity tail, including all stored formation proofs.

Pi conversion injectivity and Pi/head separation align the lambda's original
domain with the application's domain. Typed substitution then constructs the
contractum; regularity supplies the formation needed by its final conversion.

This is preservation of the typed root beta relation. It neither chooses an
evaluation strategy nor proves preservation of arbitrary declared computation,
confluence, strong normalization, or adoption of this candidate profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {R : Rules Head} {n : Nat}

namespace Typing

private theorem lamGenerationAux {Γ : Ctx Head n} {term displayed : Tm Head n}
    (typing : Typing R Γ term displayed) :
    ∀ {body : Tm Head (n + 1)}, term = .lam body →
      ∃ domain codomain u,
        Typing R Γ (.pi domain codomain) (.head u) ∧ R.isUniverse u ∧
        Typing R (.snoc Γ domain) body codomain ∧
        TypeAdjustment R (.pi domain codomain) displayed := by
  induction typing with
  | lamIntro formed universeWitness bodyTyped _ _ =>
      intro body equality
      cases equality
      exact ⟨_, _, _, formed, universeWitness, bodyTyped, .refl _⟩
  | cumul _ order ih =>
      intro body equality
      obtain ⟨domain, codomain, u, formed, universeWitness, bodyTyped, adjustment⟩ :=
        ih equality
      exact ⟨domain, codomain, u, formed, universeWitness, bodyTyped,
        .trans adjustment (.cumulative order)⟩
  | conv _ _ _ conversion ih _ =>
      intro body equality
      obtain ⟨domain, codomain, u, formed, universeWitness, bodyTyped, adjustment⟩ :=
        ih equality
      exact ⟨domain, codomain, u, formed, universeWitness, bodyTyped,
        .trans adjustment (.conversion conversion)⟩
  | _ =>
      intro body equality
      cases equality

/-- A typed lambda retains the formed Pi and body derivation used at its
introduction, even after conversion or cumulative result adjustment. -/
theorem lamGeneration {Γ : Ctx Head n} {body : Tm Head (n + 1)}
    {displayed : Tm Head n} (typing : Typing R Γ (.lam body) displayed) :
    ∃ domain codomain u,
      Typing R Γ (.pi domain codomain) (.head u) ∧ R.isUniverse u ∧
      Typing R (.snoc Γ domain) body codomain ∧
      TypeAdjustment R (.pi domain codomain) displayed :=
  lamGenerationAux typing rfl

private theorem appGenerationAux {Γ : Ctx Head n} {term displayed : Tm Head n}
    (typing : Typing R Γ term displayed) :
    ∀ {function argument : Tm Head n}, term = .app function argument →
      ∃ domain codomain,
        Typing R Γ function (.pi domain codomain) ∧ Typing R Γ argument domain ∧
        TypeAdjustment R (inst0 argument codomain) displayed ∧
        (∀ {replacement}, Typing R Γ replacement (inst0 argument codomain) →
          Typing R Γ replacement displayed) := by
  induction typing with
  | appElim functionTyped argumentTyped _ _ =>
      intro function argument equality
      cases equality
      exact ⟨_, _, functionTyped, argumentTyped, .refl _, fun replacement => replacement⟩
  | cumul _ order ih =>
      intro function argument equality
      obtain ⟨domain, codomain, functionTyped, argumentTyped, adjustment, replay⟩ :=
        ih equality
      exact ⟨domain, codomain, functionTyped, argumentTyped,
        .trans adjustment (.cumulative order), fun replacement =>
          .cumul (replay replacement) order⟩
  | conv _ formed universeWitness conversion ih _ =>
      intro function argument equality
      obtain ⟨domain, codomain, functionTyped, argumentTyped, adjustment, replay⟩ :=
        ih equality
      exact ⟨domain, codomain, functionTyped, argumentTyped,
        .trans adjustment (.conversion conversion), fun replacement =>
          .conv (replay replacement) formed universeWitness conversion⟩
  | _ =>
      intro function argument equality
      cases equality

/-- Application inversion exposes its genuine premises and the exact
result adjustment. Its replay proof reuses the original formation-sensitive
tail on any replacement with the principal application type. -/
theorem appGeneration {Γ : Ctx Head n} {function argument displayed : Tm Head n}
    (typing : Typing R Γ (.app function argument) displayed) :
    ∃ domain codomain,
      Typing R Γ function (.pi domain codomain) ∧ Typing R Γ argument domain ∧
      TypeAdjustment R (inst0 argument codomain) displayed ∧
      (∀ {replacement}, Typing R Γ replacement (inst0 argument codomain) →
        Typing R Γ replacement displayed) :=
  appGenerationAux typing rfl

/-- A typed raw beta redex retains its displayed type after contraction.
The lambda's introduction domain need not be the displayed application
domain; the independently justified Pi boundary aligns them. -/
theorem betaPi {Γ : Ctx Head n} {body : Tm Head (n + 1)}
    {argument displayed : Tm Head n}
    (typing : Typing R Γ (.app (.lam body) argument) displayed)
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    (context : ContextFormation R Γ) :
    Typing R Γ (inst0 argument body) displayed := by
  obtain ⟨observedDomain, observedCodomain, functionTyped, argumentTyped,
      _adjustment, replay⟩ := typing.appGeneration
  obtain ⟨originalDomain, originalCodomain, _u, originalPiFormed, _universe,
      bodyTyped, lambdaAdjustment⟩ := functionTyped.lamGeneration
  have components := boundary.components (lambdaAdjustment.toConvOfPiTarget boundary)
  obtain ⟨_domainUniverse, _codomainUniverse, _joinedUniverse,
      domainFormed, domainUniverse, _codomainFormed, _codomainIsUniverse, _join⟩ :=
    originalPiFormed.piFormation
  have originalArgument : Typing R Γ argument originalDomain :=
    .conv argumentTyped domainFormed domainUniverse
      (Relation.EqvGen.symm _ _ components.1)
  have contractum := bodyTyped.instantiate originalArgument
  obtain ⟨_resultUniverse, resultUniverse, resultFormed⟩ :=
    (Typing.appElim functionTyped argumentTyped).regularity universes context
  exact replay (.conv contractum resultFormed resultUniverse
    (components.2.substitute (subst0 argument)))

end Typing

/-- The complete formed-context judgment is retained by the same root
contraction. No context erasure or reconstruction is used. -/
theorem Judgment.betaPi {Γ : Ctx Head n} {body : Tm Head (n + 1)}
    {argument displayed : Tm Head n}
    (judgment : Judgment R Γ (.app (.lam body) argument) displayed)
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R) :
    Judgment R Γ (inst0 argument body) displayed :=
  ⟨judgment.context, judgment.typing.betaPi universes boundary judgment.context⟩

/-! ## Dependent specialization and the conversion boundary -/

namespace BetaExamples

/-- The codomain of the first identity binder really depends on its type
argument: opening it constructs the corresponding endomorphism type. -/
theorem polymorphic_identity_instantiated_codomain (A : Tower.Tm n) :
    inst0 A (.pi (.var 0) (.var 1)) = .pi A (rename wk A) := by
  rfl

/-- Genuine dependent specialization through the general displayed-type
preservation theorem. The tower's Pi-conversion boundary remains an explicit
qualification; this result does not assert that it has been discharged. -/
theorem polymorphic_identity_beta {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {level : LevelExpr} (context : ContextFormation Tower.rules Γ)
    (formed : Typing Tower.rules Γ A (sortTm level))
    (boundary : PiConversionBoundary Tower.rules) :
    Typing Tower.rules Γ (.lam (.var 0)) (.pi A (rename wk A)) := by
  have source := Typing.appElim (Examples.polymorphicIdentity_typed Γ level) formed
  have preserved := source.betaPi towerUniverseRegularity boundary context
  exact preserved

/-- Independently, the same specialization has a direct formation-sensitive
derivation from the formed argument. This control does not require a global
conversion boundary. -/
theorem polymorphic_identity_beta_direct {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {level : LevelExpr} (formed : Typing Tower.rules Γ A (sortTm level)) :
    Typing Tower.rules Γ (.lam (.var 0)) (.pi A (rename wk A)) := by
  apply Typing.lamIntro
  · apply Typing.piForm formed (.sort level)
    · simpa only [sortTm, rename] using formed.weaken (extension := A)
    · exact .sort level
    · exact .sorts level level
  · exact .sort _
  · exact .var 0

/-- The existing formed-endpoint looping profile does not satisfy the Pi
boundary. Formation alone therefore cannot instantiate the general theorem's
qualification, even though the relevant types themselves are formed. -/
theorem formed_endpoints_do_not_supply_pi_boundary :
    UniverseRegularity Examples.ConversionCollapse.rules ∧
      ¬ PiConversionBoundary Examples.ConversionCollapse.rules :=
  ⟨Examples.ConversionCollapse.universeRegularity,
    Examples.ConversionCollapse.no_pi_conversion_boundary⟩

end BetaExamples

#print axioms Typing.lamGeneration
#print axioms Typing.appGeneration
#print axioms Typing.betaPi
#print axioms Judgment.betaPi
#print axioms BetaExamples.polymorphic_identity_beta
#print axioms BetaExamples.polymorphic_identity_beta_direct
#print axioms BetaExamples.formed_endpoints_do_not_supply_pi_boundary

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
