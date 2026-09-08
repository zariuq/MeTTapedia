import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveBeta

/-!
# Recovering dependent arguments of declared application spines

A named declaration fixes a principal type; each successive application
opens one binder. Pi conversion qualification recovers the argument typing
from any observed derivation of that application, including conversion and
cumulativity tails. This is not uniqueness of typing for arbitrary raw
lambdas: the spine is explicitly rooted in one declaration lookup.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {R : Rules Head} {n : Nat}

private theorem constantAdjustmentAux {Γ : Ctx Head n} {term displayed : Tm Head n}
    (typing : Typing R Γ term displayed) :
    ∀ {name : DeclName} {declared : Tm Head 0}, term = .const name →
      R.constantType name = some declared →
        TypeAdjustment R (liftClosed declared) displayed := by
  induction typing with
  | const known _ _ _ =>
      intro name declared equality lookup
      cases equality
      rw [known] at lookup
      cases lookup
      exact .refl _
  | cumul _ order ih =>
      intro name declared equality lookup
      exact .trans (ih equality lookup) (.cumulative order)
  | conv _ _ _ conversion ih _ =>
      intro name declared equality lookup
      exact .trans (ih equality lookup) (.conversion conversion)
  | _ => intro name declared equality; cases equality

theorem Typing.constantAdjustment {Γ : Ctx Head n} {name : DeclName}
    {declared : Tm Head 0} {displayed : Tm Head n}
    (typing : Typing R Γ (.const name) displayed)
    (known : R.constantType name = some declared) :
    TypeAdjustment R (liftClosed declared) displayed :=
  constantAdjustmentAux typing rfl known

private theorem constantReplayAux {Γ : Ctx Head n} {term displayed : Tm Head n}
    (typing : Typing R Γ term displayed) :
    ∀ {name : DeclName} {declared : Tm Head 0} {replacement : Tm Head n},
      term = .const name → R.constantType name = some declared →
      Typing R Γ replacement (liftClosed declared) → Typing R Γ replacement displayed := by
  induction typing with
  | const known _ _ _ =>
      intro name declared replacement equality lookup replacementTyped
      cases equality
      rw [known] at lookup
      cases lookup
      exact replacementTyped
  | cumul _ order ih =>
      intro name declared replacement equality lookup replacementTyped
      exact .cumul (ih equality lookup replacementTyped) order
  | conv _ formed universeWitness conversion ih _ =>
      intro name declared replacement equality lookup replacementTyped
      exact .conv (ih equality lookup replacementTyped) formed universeWitness conversion
  | _ => intro name declared replacement equality; cases equality

/-- A real declaration followed by checked dependent applications. No
arbitrary lambda or assumed type-uniqueness law is a constructor. -/
inductive DeclarationSpine (R : Rules Head) (Γ : Ctx Head n) :
    Tm Head n → Tm Head n → Prop where
  | constant {name : DeclName} {declared : Tm Head 0} {u : Head} :
      R.constantType name = some declared →
      Typing R .nil declared (.head u) → R.isUniverse u →
        DeclarationSpine R Γ (.const name) (liftClosed declared)
  | app {function argument domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      DeclarationSpine R Γ function (.pi domain codomain) →
      Typing R Γ argument domain →
        DeclarationSpine R Γ (.app function argument) (inst0 argument codomain)

theorem DeclarationSpine.typing {Γ : Ctx Head n} {term type : Tm Head n}
    (spine : DeclarationSpine R Γ term type) : Typing R Γ term type := by
  induction spine with
  | constant known formed universeWitness => exact .const known formed universeWitness
  | app _ argumentTyped ih => exact .appElim ih argumentTyped

/-- Any observed type is reached from the declaration's instantiated type
by the actual directed conversion/cumulativity adjustment. -/
theorem DeclarationSpine.adjustment (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} {term type : Tm Head n}
    (spine : DeclarationSpine R Γ term type) :
    ∀ {displayed}, Typing R Γ term displayed → TypeAdjustment R type displayed := by
  induction spine with
  | constant known _ _ =>
      intro displayed observed
      exact observed.constantAdjustment known
  | @app function argument domain codomain previous argumentTyped ih =>
      intro displayed observed
      obtain ⟨observedDomain, observedCodomain, observedFunction, _, adjustment, _⟩ :=
        observed.appGeneration
      have components := boundary.components ((ih observedFunction).toConvOfPiTarget boundary)
      exact .trans (.conversion (components.2.substitute (subst0 argument))) adjustment

/-- Recover a dependent argument and the principal next spine from an
arbitrary observed application. Replay retains the original formed result
and every conversion/cumulativity step, so a later reduct keeps that exact
displayed type. -/
theorem DeclarationSpine.recoverApplication
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} {function argument domain displayed : Tm Head n}
    {codomain : Tm Head (n + 1)}
    (spine : DeclarationSpine R Γ function (.pi domain codomain))
    (context : ContextFormation R Γ)
    (observed : Typing R Γ (.app function argument) displayed) :
    Typing R Γ argument domain ∧
      DeclarationSpine R Γ (.app function argument) (inst0 argument codomain) ∧
      TypeAdjustment R (inst0 argument codomain) displayed ∧
      (∀ {replacement}, Typing R Γ replacement (inst0 argument codomain) →
        Typing R Γ replacement displayed) := by
  obtain ⟨observedDomain, observedCodomain, observedFunction, observedArgument,
      adjustment, replay⟩ := observed.appGeneration
  have components := boundary.components
    ((spine.adjustment boundary observedFunction).toConvOfPiTarget boundary)
  obtain ⟨_, _, principalFormed⟩ := spine.typing.regularity universes context
  obtain ⟨_, _, _, domainFormed, universeDomain, _, _, _⟩ := principalFormed.piFormation
  have argumentTyped : Typing R Γ argument domain :=
    .conv observedArgument domainFormed universeDomain (.symm _ _ components.1)
  have resultConversion := components.2.substitute (subst0 argument)
  refine ⟨argumentTyped, .app spine argumentTyped,
    .trans (.conversion resultConversion) adjustment, ?_⟩
  intro replacement replacementTyped
  obtain ⟨_, universeResult, resultFormed⟩ :=
    (Typing.appElim observedFunction observedArgument).regularity universes context
  exact replay (.conv replacementTyped resultFormed universeResult resultConversion)

/-- Replay an observed derivation's type adjustments on another term at
the same declaration-derived principal type. -/
theorem DeclarationSpine.replay
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} {term type displayed replacement : Tm Head n}
    (spine : DeclarationSpine R Γ term type) (context : ContextFormation R Γ)
    (observed : Typing R Γ term displayed)
    (replacementTyped : Typing R Γ replacement type) :
    Typing R Γ replacement displayed := by
  cases spine with
  | constant known _ _ =>
      exact constantReplayAux observed rfl known replacementTyped
  | app previous _ =>
      exact (previous.recoverApplication universes boundary context observed).2.2.2
        replacementTyped

#print axioms Typing.constantAdjustment
#print axioms DeclarationSpine.typing
#print axioms DeclarationSpine.adjustment
#print axioms DeclarationSpine.recoverApplication
#print axioms DeclarationSpine.replay

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
