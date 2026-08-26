import Mettapedia.GSLT.LanguageDef.InferencePresentationWireFormat
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering
import Mettapedia.GSLT.LanguageDef.InferenceCettaExecutionRefinement

/-!
# Exact inference-wire refinement to generic ABT operations

The versioned inference wire retains generic side conditions exactly, while
the physical ABT carrier interprets binder depths uniformly from constructor
fields.  These commuting theorems connect those two boundaries: decoding a
canonical condition packet and executing its ABT operation has precisely the
logical meaning used by inference replay.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceABTWireRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferencePresentationWire
open Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering
open Mettapedia.GSLT.LanguageDef.InferenceCettaExecutionRefinement

namespace Cetta

open Mettapedia.GSLT.LanguageDef.InferenceCettaWire

/-- The concrete CeTTa side-condition packet decodes to the same generic ABT
obligation as the logical presentation wire. -/
theorem explicitSubstitution_packet_refines
    (ambientDepth bodyArgument replacementArgument resultArgument : Nat)
    (arguments : List Pattern) (body replacement result : Pattern)
    (bodyLookup : arguments[bodyArgument]? = some body)
    (replacementLookup : arguments[replacementArgument]? = some replacement)
    (resultLookup : arguments[resultArgument]? = some result) :
    InferenceCettaWire.decodeSideCondition
        (InferenceCettaWire.encodeSideCondition
          (.explicitSubstitution ambientDepth bodyArgument
            replacementArgument resultArgument)) =
      some (.explicitSubstitution ambientDepth bodyArgument
        replacementArgument resultArgument) ∧
    (PatternABT.instantiateAt 0 (PatternABT.encode replacement)
          (PatternABT.encode body) = PatternABT.encode result ↔
      RuleSideCondition.holds arguments
          (.explicitSubstitution ambientDepth bodyArgument
            replacementArgument resultArgument) = true) := by
  constructor
  · rfl
  · rw [PatternABT.instantiateAt_zero_eq_iff]
    simp [RuleSideCondition.holds, bodyLookup, replacementLookup, resultLookup]

/-- The concrete CeTTa unused-binder packet retains the same partial ABT
operation as logical replay. -/
theorem unusedBinder_packet_refines
    (ambientDepth bodyArgument resultArgument : Nat)
    (arguments : List Pattern) (body result : Pattern)
    (bodyLookup : arguments[bodyArgument]? = some body)
    (resultLookup : arguments[resultArgument]? = some result) :
    InferenceCettaWire.decodeSideCondition
        (InferenceCettaWire.encodeSideCondition
          (.unusedBinderElimination ambientDepth bodyArgument resultArgument)) =
      some (.unusedBinderElimination ambientDepth bodyArgument resultArgument) ∧
    (PatternABT.dropAt? 0 (PatternABT.encode body) =
          some (PatternABT.encode result) ↔
      RuleSideCondition.holds arguments
          (.unusedBinderElimination ambientDepth bodyArgument resultArgument) =
        true) := by
  constructor
  · rfl
  · rw [PatternABT.dropAt_zero_eq_some_iff]
    simp [RuleSideCondition.holds, bodyLookup, resultLookup]

/-- A successful local replay by the exact closed-payload runtime projection
lowers the complete ordered rule application through one support-indexed ABT
environment. -/
theorem runtime_rule_application_refines_abt
    (presentation : ValidatedPresentation) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (checked :
      (RuntimePresentation.ofPresentation presentation.1).instantiateRule?
          ruleInstance = some (premises, conclusion)) :
    ABTRuleApplication presentation ruleInstance premises conclusion := by
  exact instantiateRule?_eq_some_implies_abt
    (RuntimePresentation.instantiateRule?_sound
      presentation ruleInstance premises conclusion checked)

/-- Acceptance of an exact CeTTa carrier packet yields a proof-relevant ABT
derivation at every node, and erasing that derivation recovers the identical
chronological article. -/
theorem checkPacket_acceptance_has_abt_derivation
    (presentation : ValidatedPresentation) (goal : Pattern)
    (proof : RawProof)
    (accepted :
      InferenceCettaWire.checkPacket
          (InferenceCettaWire.encodeRuntimePresentation
            (RuntimePresentation.ofPresentation presentation.1))
          (InferenceCettaWire.encodePattern goal)
          (InferenceCettaWire.encodeRawProof proof) = some true) :
    ∃ derivation : ABTDerivation presentation goal,
      ABTDerivation.erase derivation = proof := by
  obtain ⟨derivation, erases⟩ :=
    InferenceCettaWire.checkPacket_encode_acceptance_sound
      presentation goal proof accepted
  refine ⟨derivationToABT derivation, ?_⟩
  rw [derivationToABT_erase, erases]

/-- Acceptance of an exact CeTTa carrier packet can additionally be replayed
through the direct physical schema walk at every node.  The resulting article
retains the identical chronological erasure and support-indexed ABT meaning. -/
theorem checkPacket_acceptance_has_physical_abt_derivation
    (presentation : ValidatedPresentation) (goal : Pattern)
    (proof : RawProof)
    (accepted :
      InferenceCettaWire.checkPacket
          (InferenceCettaWire.encodeRuntimePresentation
            (RuntimePresentation.ofPresentation presentation.1))
          (InferenceCettaWire.encodePattern goal)
          (InferenceCettaWire.encodeRawProof proof) = some true) :
    ∃ derivation : PhysicalABTDerivation presentation goal,
      PhysicalABTDerivation.erase derivation = proof := by
  obtain ⟨derivation, erases⟩ :=
    InferenceCettaWire.checkPacket_encode_acceptance_sound
      presentation goal proof accepted
  refine ⟨derivationToPhysicalABT derivation, ?_⟩
  rw [derivationToPhysicalABT_erase, erases]

end Cetta

/-- Canonical Pattern wire followed by the physical ABT support provider is
exactly the logical argument-validity check used by inference replay. -/
theorem patternSupport_wire_abt_refines
    (depth : Nat) (pattern : Pattern) :
    decodePattern (encodePattern pattern) = some pattern ∧
      (PatternABT.argumentSupportedAt depth pattern = true ↔
        argumentValidAt depth pattern = true) := by
  constructor
  · simp
  · rw [PatternABT.argumentSupportedAt_eq_argumentValidAt]

/-- Canonical explicit-substitution packets retain exactly the generic ABT
obligation checked by inference replay. -/
theorem explicitSubstitution_wire_abt_refines
    (ambientDepth bodyArgument replacementArgument resultArgument : Nat)
    (arguments : List Pattern) (body replacement result : Pattern)
    (bodyLookup : arguments[bodyArgument]? = some body)
    (replacementLookup : arguments[replacementArgument]? = some replacement)
    (resultLookup : arguments[resultArgument]? = some result) :
    decodeSideCondition
        (encodeSideCondition
          (.explicitSubstitution ambientDepth bodyArgument
            replacementArgument resultArgument)) =
      some (.explicitSubstitution ambientDepth bodyArgument
        replacementArgument resultArgument) ∧
    (PatternABT.instantiateAt 0 (PatternABT.encode replacement)
          (PatternABT.encode body) = PatternABT.encode result ↔
      RuleSideCondition.holds arguments
          (.explicitSubstitution ambientDepth bodyArgument
            replacementArgument resultArgument) = true) := by
  constructor
  · rfl
  · rw [PatternABT.instantiateAt_zero_eq_iff]
    simp [RuleSideCondition.holds, bodyLookup, replacementLookup, resultLookup]

/-- Canonical unused-binder packets retain exactly the partial generic ABT
obligation checked by inference replay. -/
theorem unusedBinder_wire_abt_refines
    (ambientDepth bodyArgument resultArgument : Nat)
    (arguments : List Pattern) (body result : Pattern)
    (bodyLookup : arguments[bodyArgument]? = some body)
    (resultLookup : arguments[resultArgument]? = some result) :
    decodeSideCondition
        (encodeSideCondition
          (.unusedBinderElimination ambientDepth bodyArgument resultArgument)) =
      some (.unusedBinderElimination ambientDepth bodyArgument resultArgument) ∧
    (PatternABT.dropAt? 0 (PatternABT.encode body) =
          some (PatternABT.encode result) ↔
      RuleSideCondition.holds arguments
          (.unusedBinderElimination ambientDepth bodyArgument resultArgument) =
        true) := by
  constructor
  · rfl
  · rw [PatternABT.dropAt_zero_eq_some_iff]
    simp [RuleSideCondition.holds, bodyLookup, resultLookup]

/-- Positive binder canary: the exact wire obligation reduces the identity
body to its replacement. -/
theorem identity_beta_packet_accepts :
    RuleSideCondition.holds
        [.bvar 0, .apply "Zero" [], .apply "Zero" []]
        (.explicitSubstitution 0 0 1 2) = true := by
  simp [RuleSideCondition.holds, instantiateBVar, instantiateBVarAt,
    liftBVars]

/-- Negative binder canary: the same packet rejects a fabricated result. -/
theorem fabricated_beta_packet_rejects :
    RuleSideCondition.holds
        [.bvar 0, .apply "Zero" [], .apply "Nat" []]
        (.explicitSubstitution 0 0 1 2) = false := by
  simp [RuleSideCondition.holds, instantiateBVar, instantiateBVarAt,
    liftBVars]

/-- Negative support canary: a depth-one formal cannot carry index one. -/
theorem out_of_scope_argument_packet_rejects :
    PatternABT.argumentSupportedAt 1 (.bvar 1) = false := by
  rfl

end Mettapedia.GSLT.LanguageDef.InferenceABTWireRefinement
