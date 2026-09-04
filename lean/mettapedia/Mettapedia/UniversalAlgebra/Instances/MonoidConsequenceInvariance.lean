import Mettapedia.UniversalAlgebra.Instances.MonoidConservativeExtension
import Mettapedia.UniversalAlgebra.NIK.ConsequenceInvariance
import Mettapedia.UniversalAlgebra.NIK.Simulation

/-!
# Monoid controls for consequence and authority invariance

The monoid system and its extension by the already-derived equation
`(1 * x) * 1 = x` have the same models, semantic consequences, NIK theorem
scope, and extensionally accepted claims.  Their source data nevertheless have
different numbers of equation occurrences.

The extension identifying two distinct variables is the negative control: it
does not preserve generated consequence or accepted claims.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Mettapedia.UniversalAlgebra

/-- The redundant extension preserves every model in the selected carrier
universe. -/
theorem derivedExtension_sameModels (Carrier : Type)
    (model : Model signature Carrier) :
    model.Satisfies derivedExtension ↔ model.Satisfies equationSystem :=
  Model.satisfies_iff_of_sameConsequences
    derivedExtension_sameConsequences model

/-- The redundant extension preserves model-theoretic consequence. -/
theorem derivedExtension_sameEntailment (equation : Equation signature) :
    Entails derivedExtension equation ↔ Entails equationSystem equation :=
  entails_iff_of_sameConsequences derivedExtension_sameConsequences equation

/-- The redundant extension preserves the NIK theorem scope. -/
theorem derivedExtension_sameNIKScope (equation : Equation signature) :
    (NIK.theory derivedExtension).Scope () equation ↔
      (NIK.theory equationSystem).Scope () equation :=
  NIK.theory_scope_iff_of_sameConsequences
    derivedExtension_sameConsequences equation

/-- The redundant extension preserves the existence of accepted NIK
certificates for every equation. -/
theorem derivedExtension_sameAcceptedClaims (equation : Equation signature) :
    NIK.HasAcceptedCertificate derivedExtension equation ↔
      NIK.HasAcceptedCertificate equationSystem equation :=
  (NIK.sameConsequences_iff_acceptedClaims.mp
    derivedExtension_sameConsequences) equation

/-- The equivalent systems mutually simulate one another in the conservative
semantic-translation preorder. -/
theorem derivedExtension_mutuallyConservativelySimulates :
    Mettapedia.Logic.TheorySimulation.MutuallyConservativelySimulates
      (NIK.theoryObject derivedExtension) (NIK.theoryObject equationSystem) :=
  NIK.mutuallyConservativelySimulates_of_sameConsequences
    derivedExtension_sameConsequences

/-- Positive representation canary: the source equation-occurrence counts are
different even though theorem scope and accepted claims agree. -/
theorem derivedExtension_occurrenceCount_differs :
    derivedExtension.equations.length ≠ equationSystem.equations.length := by
  simp [derivedExtension, EquationSystem.extend, equationSystem]

/-- Negative authority canary: the collapsing extension changes the
extensional accepted-claim set. -/
theorem collapsingExtension_not_sameAcceptedClaims :
    ¬ ∀ equation,
      NIK.HasAcceptedCertificate collapsingExtension equation ↔
        NIK.HasAcceptedCertificate equationSystem equation := by
  intro acceptedClaims
  exact collapsingExtension_not_sameConsequences
    (NIK.sameConsequences_iff_acceptedClaims.mpr acceptedClaims)

end Mettapedia.UniversalAlgebra.Monoid
