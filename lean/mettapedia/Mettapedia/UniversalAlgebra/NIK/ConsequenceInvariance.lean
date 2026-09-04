import Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
import Mettapedia.UniversalAlgebra.ConsequenceEquivalence
import Mettapedia.UniversalAlgebra.NIK.Authority

/-!
# NIK authority invariance under equational consequence equivalence

Finite equation systems may differ as occurrence-bearing source data while
generating the same deductive and semantic theory.  This file states the
corresponding NIK invariant at the correct extensional boundary:

* theorem scope agrees;
* independently defined model-theoretic meaning agrees;
* a claim has an accepted certificate on one side exactly when it has one on
  the other.

No claim is made that the concrete certificate types, occurrence indices, or
checker executions are definitionally equal.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.NIK

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- Extensional acceptance of one equation by the exact NIK replay authority.
The concrete certificate remains existentially hidden. -/
def HasAcceptedCertificate (system : EquationSystem S)
    (equation : Equation S) : Prop :=
  ∃ certificate,
    ((contract system).checker ()).check equation certificate = true

/-- Exact replay accepts some certificate precisely for generated equational
consequences. -/
theorem hasAcceptedCertificate_iff_consequence
    (system : EquationSystem S) (equation : Equation S) :
    HasAcceptedCertificate system equation ↔
      EquationalConsequence system equation := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact ((contract system).scopeAuthority ()).sound equation certificate
      accepted
  · intro consequence
    exact ((contract system).scopeAuthority ()).complete equation consequence

/-- Consequence-equivalent systems have the same NIK theorem scope. -/
theorem theory_scope_iff_of_sameConsequences
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right)
    (equation : Equation S) :
    (theory left).Scope () equation ↔ (theory right).Scope () equation := by
  change EquationalConsequence left equation ↔
    EquationalConsequence right equation
  exact equivalent equation

/-- Consequence-equivalent systems have the same independently defined NIK
meaning predicate. -/
theorem theory_meaning_iff_of_sameConsequences
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right)
    (equation : Equation S) :
    (theory left).Meaning () equation ↔ (theory right).Meaning () equation := by
  change Entails left equation ↔ Entails right equation
  exact entails_iff_of_sameConsequences equivalent equation

/-- Consequence equivalence is exactly equality of the extensional accepted
claim sets of the two exact replay authorities. -/
theorem sameConsequences_iff_acceptedClaims
    {left right : EquationSystem S} :
    EquationSystem.SameConsequences left right ↔
      ∀ equation,
        HasAcceptedCertificate left equation ↔
          HasAcceptedCertificate right equation := by
  constructor
  · intro equivalent equation
    rw [hasAcceptedCertificate_iff_consequence,
      hasAcceptedCertificate_iff_consequence]
    exact equivalent equation
  · intro acceptedClaims equation
    rw [← hasAcceptedCertificate_iff_consequence,
      ← hasAcceptedCertificate_iff_consequence]
    exact acceptedClaims equation

/-- The identity map on equations gives a semantic theory translation whenever
the source and target systems generate the same consequences. -/
def identityOnEquationsTranslation
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right) :
    TheoryTranslation (theory left) (theory right) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind equation => equation
  scope_preserved := by
    intro _kind equation inScope
    exact (equivalent equation).mp inScope
  meaning_preserved := by
    intro _kind equation meaningful
    exact (entails_iff_of_sameConsequences equivalent equation).mp meaningful

/-- The identity-on-equations translation is conservative: it neither invents
theorems nor changes model-theoretic meaning. -/
theorem identityOnEquationsTranslation_conservative
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right) :
    (identityOnEquationsTranslation equivalent).Conservative := by
  constructor
  · intro _kind equation inScope
    exact (equivalent equation).mpr inScope
  · intro _kind equation meaningful
    exact (entails_iff_of_sameConsequences equivalent equation).mpr meaningful

end Mettapedia.UniversalAlgebra.NIK

