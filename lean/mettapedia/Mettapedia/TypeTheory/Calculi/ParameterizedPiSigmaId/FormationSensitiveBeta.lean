import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypingGeneration

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

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
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

#print axioms Typing.lamGeneration
#print axioms Typing.appGeneration
#print axioms Typing.betaPi
#print axioms Judgment.betaPi

end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
