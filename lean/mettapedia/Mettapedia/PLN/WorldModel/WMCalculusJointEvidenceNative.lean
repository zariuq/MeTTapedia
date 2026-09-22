import Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
import Mettapedia.OSLF.Framework.WMCalculusNativeObservation
import Mettapedia.OSLF.Framework.WMCalculusNativeCapability
import Mettapedia.Logic.BDD.WMPLNBDDWMCExact

/-!
# Joint evidence, native observation, and compiled BDD readouts

World-indexed joint evidence is an additive WM reading when extraction is
the unnormalized mass of a Boolean world query. A proposition strength is
a derived readout of two such masses. It is stable under WM behavioral
agreement, so it determines a native observation type closed under WM
contextual computation. An ordered, query-faithful BDD computes an actual
inhabitant of that type for the compiled ProbLog state.

No probability-additivity law is asserted: the additive evidence is mass,
while the normalized strength and BDD WMC live in the readout layer.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMCalculusJointEvidenceNative

open scoped ENNReal
open _root_.CategoryTheory
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.Logic.BDDCore
open Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics

private abbrev wmLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

variable {n : ℕ}

/-- Finite-world mass extraction is additive over joint-evidence revision. -/
noncomputable instance :
    AdditiveWorldModel (JointEvidence n) (Fin (2 ^ n) → Bool) ℝ≥0∞ where
  extract := countWorld
  extract_add first second query := countWorld_add first second query

/-- A Boolean-world query can be used as the denominator event of a
normalized readout only when it has positive finite evidence mass.
This is a partial capability, not a change to the additive WM extraction. -/
noncomputable def normalizableMassCapability
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool) :
    WMCapability (additiveReading (Ev := ℝ≥0∞) world queryName) where
  supports := fun state query =>
    0 < countWorld state query ∧ countWorld state query < ⊤
  respectsAgree := by
    intro first second query agree
    have same := agree query
    change countWorld first query = countWorld second query at same
    rw [same]

/-- The zero ledger has no normalization-eligible Boolean-world query. -/
theorem normalizableMassCapability_zero_unsupported
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (query : Fin (2 ^ n) → Bool) :
    ¬ (normalizableMassCapability world queryName).supports
      (0 : JointEvidence n) query := by
  simp [normalizableMassCapability, countWorld]

/-- A one-world positive ledger supports its certain event. -/
theorem normalizableMassCapability_one_supported
    (world : String → JointEvidence 0)
    (queryName : String → Fin (2 ^ 0) → Bool) :
    (normalizableMassCapability world queryName).supports
      (fun _ => 1 : JointEvidence 0) (fun _ => true) := by
  norm_num [normalizableMassCapability, countWorld, Fin.sum_univ_one]

/-- Positive but infinite mass is also excluded from finite-denominator
normalization; mere positivity would be an unsound capability test. -/
theorem normalizableMassCapability_infinite_unsupported
    (world : String → JointEvidence 0)
    (queryName : String → Fin (2 ^ 0) → Bool) :
    ¬ (normalizableMassCapability world queryName).supports
      (fun _ => ⊤ : JointEvidence 0) (fun _ => true) := by
  norm_num [normalizableMassCapability, countWorld, Fin.sum_univ_one]

/-- Derived proposition strength is invariant under all Boolean-world
mass observations, although strength itself is not an additive extraction. -/
theorem propositionStrength_invariant
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (A : Fin n) (value : ℝ≥0∞) :
    ObservationInvariant
      (additiveReading (Ev := ℝ≥0∞) world queryName) .state
      (fun state => (state.propEvidence A).toStrength = value) := by
  intro first second agree observed
  have positive := agree (fun w => worldToAssignment n w A)
  have negative := agree (fun w => !(worldToAssignment n w A))
  change countWorld first (fun w => worldToAssignment n w A) =
    countWorld second (fun w => worldToAssignment n w A) at positive
  change countWorld first (fun w => !(worldToAssignment n w A)) =
    countWorld second (fun w => !(worldToAssignment n w A)) at negative
  have evidenceEqual : first.propEvidence A = second.propEvidence A := by
    simp only [propEvidence, positive, negative]
  rw [← evidenceEqual]
  exact observed

/-- The strength readout becomes an actual object of the full presheaf
predicate fibration of the authored WM calculus. -/
noncomputable def propositionStrengthNativeType
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (A : Fin n) (value : ℝ≥0∞) :
    FullPresheafGrothendieckObj wmLanguage :=
  observationNativeType (additiveReading (Ev := ℝ≥0∞) world queryName)
    .state (fun state => (state.propEvidence A).toStrength = value)

/-- Contextual computation transports the derived probability observation
through its native dependent fiber, using additivity only for the mass
evidence underneath. -/
noncomputable def propositionStrengthRewriteTransport
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (A : Fin n) (value : ℝ≥0∞)
    {Γ : languagePresheafObj wmLanguage}
    {source target : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel source target) :
    FullPresheafGrothendieckHom wmLanguage
      (observationInContext
        (additiveReading (Ev := ℝ≥0∞) world queryName) .state
        (fun state => (state.propEvidence A).toStrength = value) Γ source)
      (observationInContext
        (additiveReading (Ev := ℝ≥0∞) world queryName) .state
        (fun state => (state.propEvidence A).toStrength = value) Γ target) :=
  observationRewriteTransport
    (additiveReading (Ev := ℝ≥0∞) world queryName)
    (additiveReading_coreLaws world queryName)
    .state (fun state => (state.propEvidence A).toStrength = value)
    (propositionStrength_invariant world queryName A value) step

/-- The ProbLog-compiled state inhabits the native proposition-strength
type at the exact WMC value of an ordered BDD faithful to that proposition. -/
theorem bddWmc_native_member
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (p : ProbAssignment n) (A : Fin n)
    (f : BDD n) {bound : Option (Fin n)} (ordered : f.Ordered bound)
    (normalized : ∀ i, p i ≤ 1)
    (faithful : ∀ numberedWorld,
      f.eval (worldAssignmentEquiv n numberedWorld) =
        worldToAssignment n numberedWorld A)
    (compiled : world "facts" = probLogToJointEvidence p)
    (X : Opposite (ConstructorObj wmLanguage)) :
    (ULift.up (encodeWM (WMTerm.state "facts")) :
      (languageProgramObj wmLanguage).obj X) ∈
      (observationPredicate
        (additiveReading (Ev := ℝ≥0∞) world queryName) .state
        (fun state => (state.propEvidence A).toStrength = bdd_wmc f p)).obj X := by
  apply (observationPredicate_encoded_iff
    (additiveReading (Ev := ℝ≥0∞) world queryName) .state
    (fun state => (state.propEvidence A).toStrength = bdd_wmc f p)
    X (.state "facts")).mpr
  change ((world "facts").propEvidence A).toStrength = bdd_wmc f p
  rw [compiled]
  exact (bdd_wmc_eq_wmPropositionStrength f ordered p normalized A faithful).symm

/-- Strength cannot replace unnormalized mass as the additive WM evidence.
Duplicating one positive-only source keeps its strength at one, while adding
the two readout strengths gives two. -/
theorem propositionStrength_not_additive :
    ∃ first second : JointEvidence 1,
      ((first + second).propEvidence 0).toStrength ≠
        (first.propEvidence 0).toStrength +
          (second.propEvidence 0).toStrength := by
  let evidence : JointEvidence 1 :=
    fun world => if worldToAssignment 1 world 0 then 1 else 0
  have single : evidence.propEvidence 0 = (⟨1, 0⟩ : BinaryEvidence) := by
    ext
    · change (∑ world : Fin 2,
        if worldToAssignment 1 world 0 then
          (if worldToAssignment 1 world 0 then (1 : ℝ≥0∞) else 0) else 0) = 1
      rw [Fin.sum_univ_two]
      norm_num [worldToAssignment]
    · change (∑ world : Fin 2,
        if !(worldToAssignment 1 world 0) then
          (if worldToAssignment 1 world 0 then (1 : ℝ≥0∞) else 0) else 0) = 0
      rw [Fin.sum_univ_two]
      norm_num [worldToAssignment]
  have doubled : (evidence + evidence).propEvidence 0 =
      (⟨2, 0⟩ : BinaryEvidence) := by
    rw [propEvidence_add, single]
    norm_num [BinaryEvidence.hplus_def]
  have singleStrength : (⟨1, 0⟩ : BinaryEvidence).toStrength = 1 := by
    norm_num [BinaryEvidence.toStrength, BinaryEvidence.total]
  have doubleStrength : (⟨2, 0⟩ : BinaryEvidence).toStrength = 1 := by
    norm_num [BinaryEvidence.toStrength, BinaryEvidence.total]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  refine ⟨evidence, evidence, ?_⟩
  simp only [single, doubled, singleStrength, doubleStrength]
  norm_num

end Mettapedia.PLN.WorldModel.WMCalculusJointEvidenceNative
