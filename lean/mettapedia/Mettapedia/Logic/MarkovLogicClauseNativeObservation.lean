import Mettapedia.Logic.MarkovLogicClauseWorldModel
import Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
import Mettapedia.OSLF.Framework.WMCalculusNativeObservation

/-!
# Clause MLN probability readouts as native observations

The compiled clause MLN is already a factorized `BinaryWorldModel` whose
state is a ledger of sources. Its probability is a readout of binary evidence,
not an additive evidence value. Here the readout becomes a native predicate
on WM state terms, and rewriting transports that predicate in every context.
For the singleton source state, predicate membership is the MLN query
probability theorem rather than a new probabilistic semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.MarkovLogicClauseNativeObservation

open scoped ENNReal
open _root_.CategoryTheory
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicClauseWorldModel
open GroundMLN
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.ProbabilityTheory.BayesianNetworks

variable {Atom : Type} {ClauseId : Type*} [DecidableEq Atom] [Fintype Atom]

private abbrev wmLanguage : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

private abbrev ClauseState (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :=
  ValuationWorldModel.WMState (compiledClauseFactorGraph M support)

/-- The existing factor-ledger reading, with its authored singleton MLN as
the denotation of every state atom. -/
noncomputable def mlnReading
    (M : GroundMLN Atom ClauseId) (support : Finset ClauseId)
    (q : ConstraintQuery Atom) :
    WMReading (ClauseState M support) (ConstraintQuery Atom) BinaryEvidence := by
  letI := clauseWorldModel M support
  exact additiveReading (Ev := BinaryEvidence)
    (fun _ => clauseWMState M support) (fun _ => q)

/-- A query-probability level set is invariant under WM behavioral agreement.
The proof uses equality of underlying binary evidence, not additivity of the
probability readout. -/
theorem strength_observation_invariant
    (M : GroundMLN Atom ClauseId) (support : Finset ClauseId)
    (q : ConstraintQuery Atom) (probability : ℝ≥0∞) :
    ObservationInvariant (mlnReading M support q) .state
      (fun state => BinaryWorldModel.queryStrength state q = probability) := by
  intro first second agree observed
  have evidenceAgree :
      BinaryWorldModel.evidence first q = BinaryWorldModel.evidence second q := by
    exact agree q
  change BinaryEvidence.toStrength (BinaryWorldModel.evidence first q) = probability at observed
  change BinaryEvidence.toStrength (BinaryWorldModel.evidence second q) = probability
  rwa [← evidenceAgree]

/-- The native type whose inhabitants are states assigning a chosen strength
to an MLN constraint query. -/
noncomputable def mlnStrengthNativeType
    (M : GroundMLN Atom ClauseId) (support : Finset ClauseId)
    (q : ConstraintQuery Atom) (probability : ℝ≥0∞) :
    FullPresheafGrothendieckObj wmLanguage :=
  observationNativeType (mlnReading M support q) .state
    (fun state => BinaryWorldModel.queryStrength state q = probability)

/-- The encoded singleton clause state inhabits the native type exactly
when the original MLN query probability has the specified value. -/
theorem mlnStrengthNativeType_singleton_iff
    (M : GroundMLN Atom ClauseId) (support : Finset ClauseId)
    (q : ConstraintQuery Atom) (probability : ℝ≥0∞)
    (X : Opposite (ConstructorObj wmLanguage)) :
    (ULift.up (encodeWM (.state "mln")) :
      (languageProgramObj wmLanguage).obj X) ∈
        (mlnStrengthNativeType M support q probability).fiber.obj X ↔
      (clauseMassSemantics M support).queryProb q = probability := by
  change (ULift.up (encodeWM (.state "mln")) :
    (languageProgramObj wmLanguage).obj X) ∈
      (observationPredicate (mlnReading M support q) .state
        (fun state => BinaryWorldModel.queryStrength state q = probability)).obj X ↔
    (clauseMassSemantics M support).queryProb q = probability
  rw [observationPredicate_encoded_iff]
  change BinaryWorldModel.queryStrength (clauseWMState M support) q = probability ↔
    (clauseMassSemantics M support).queryProb q = probability
  rw [clauseWM_queryStrength_eq_queryProb M support q]

/-- The strength observation is transported through a contextual WM rewrite
in the full presheaf predicate category. -/
noncomputable def mlnStrengthRewriteTransport
    (M : GroundMLN Atom ClauseId) (support : Finset ClauseId)
    (q : ConstraintQuery Atom) (probability : ℝ≥0∞)
    {Γ : languagePresheafObj wmLanguage}
    {p r : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p r) :
    FullPresheafGrothendieckHom wmLanguage
      (observationInContext (mlnReading M support q) .state
        (fun state => BinaryWorldModel.queryStrength state q = probability) Γ p)
      (observationInContext (mlnReading M support q) .state
        (fun state => BinaryWorldModel.queryStrength state q = probability) Γ r) := by
  exact observationRewriteTransport
    (mlnReading M support q)
    (additiveReading_coreLaws
      (Ev := BinaryEvidence)
      (fun _ => clauseWMState M support) (fun _ => q))
    .state (fun state => BinaryWorldModel.queryStrength state q = probability)
    (strength_observation_invariant M support q probability) step

end Mettapedia.Logic.MarkovLogicClauseNativeObservation
