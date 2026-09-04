import Mettapedia.Languages.ProcessCalculi.MORK.MM2SurfaceProgramSafety

/-

/-!
# Compositional renderer-domain safety for source-action loading

The deferred source-action extension stores a supplied finite rule inventory
in both passive reload rows and active source-action rows. This module proves
that ordinary-MM2 rendering remains safe by construction from certificates for
its named fixed components and its supplied extension inventory, without
reducing the complete combined verifier program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceActionRendererSafety

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
open Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

private theorem sourceVerifierRuleRow_head_safe :
    bareSymbolSafe "mm-internal-source-verifier-rule" = true := by
  decide +kernel

/-- Wrapping an ordinary rule as passive source-verifier data preserves its
ordinary-MM2 atom spelling domain. -/
theorem sourceVerifierRuleRow_atomSafe (rule : Atom)
    (safe : atomSafe rule = true) :
    atomSafe (sourceVerifierRuleRow rule) = true := by
  simpa [sourceVerifierRuleRow, atomSafe, atomsSafe,
    sourceVerifierRuleRow_head_safe] using safe

/-- The passive source-verifier wrapper introduces no variable occurrence. -/
theorem sourceVerifierRuleRow_variableBudget (rule : Atom) :
    atomVariableBudget (sourceVerifierRuleRow rule) =
      atomVariableBudget rule := by
  simp [sourceVerifierRuleRow, atomVariableBudget,
    atomVariableNames, atomsVariableNames]

/-- A complete passive reload-row inventory is renderer-safe whenever the
underlying ordinary rule inventory is renderer-safe. -/
theorem sourceVerifierRuleRows_programSafe (rules : List Atom)
    (safe : programSafe rules = true) :
    programSafe (rules.map sourceVerifierRuleRow) = true := by
  apply programSafe_map sourceVerifierRuleRow rules
  · exact sourceVerifierRuleRow_atomSafe
  · intro rule budget
    simpa [sourceVerifierRuleRow_variableBudget] using budget
  · exact safe

/-- The deferred source-action extension preserves ordinary-MM2 renderer
admission from the renderer certificates for the fixed source-action profile
and the explicit extension inventory it transports. -/
theorem compressedNormalSourceActionExtension_programSafe
    (extensionRules : List Atom)
    (terminalRowsSafe :
      programSafe compressedNormalTerminalReloadRows = true)
    (baseVerifierRulesSafe :
      programSafe compressedNormalBaseSourceVerifierRules.dropLast = true)
    (reloadRuleSafe : programSafe [sourceVerifierReloadRule] = true)
    (baseActionRulesSafe :
      programSafe compressedNormalBaseSourceActionRules = true)
    (verdictRulesSafe :
      programSafe (sourceVerdictRules normalProofMachineRuleInventory) = true)
    (reloadCaptureSafe : programSafe [sourceVerifierReloadCaptureRow] = true)
    (safe : programSafe extensionRules = true) :
    programSafe (compressedNormalSourceActionExtension extensionRules) = true := by
  have verifierRulesSafe :
      programSafe (compressedNormalSourceVerifierRulesWith extensionRules) = true := by
    change programSafe
      (compressedNormalBaseSourceVerifierRules.dropLast ++ extensionRules ++
        [sourceVerifierReloadRule]) = true
    apply (programSafe_append_iff
      compressedNormalBaseSourceVerifierRules.dropLast
      (extensionRules ++ [sourceVerifierReloadRule])).mpr
    refine ⟨baseVerifierRulesSafe, ?_⟩
    exact (programSafe_append_iff extensionRules [sourceVerifierReloadRule]).mpr
      ⟨safe, reloadRuleSafe⟩
  have passiveRowsSafe :
      programSafe ((compressedNormalSourceVerifierRulesWith extensionRules).map
        sourceVerifierRuleRow) = true :=
    sourceVerifierRuleRows_programSafe _ verifierRulesSafe
  have activeRowsSafe :
      programSafe (compressedNormalSourceActionRulesWith extensionRules) = true := by
    change programSafe
      (compressedNormalBaseSourceActionRules ++ extensionRules) = true
    exact (programSafe_append_iff compressedNormalBaseSourceActionRules
      extensionRules).mpr ⟨baseActionRulesSafe,
        safe⟩
  change programSafe
    (compressedNormalTerminalReloadRows ++
      (compressedNormalSourceVerifierRulesWith extensionRules).map
        sourceVerifierRuleRow ++
        compressedNormalSourceActionRulesWith extensionRules ++
          sourceVerdictRules normalProofMachineRuleInventory ++
            [sourceVerifierReloadCaptureRow]) = true
  apply (programSafe_append_iff compressedNormalTerminalReloadRows
    ((compressedNormalSourceVerifierRulesWith extensionRules).map
      sourceVerifierRuleRow ++
      compressedNormalSourceActionRulesWith extensionRules ++
        sourceVerdictRules normalProofMachineRuleInventory ++
          [sourceVerifierReloadCaptureRow])).mpr
  refine ⟨terminalRowsSafe, ?_⟩
  apply (programSafe_append_iff
    ((compressedNormalSourceVerifierRulesWith extensionRules).map
      sourceVerifierRuleRow)
    (compressedNormalSourceActionRulesWith extensionRules ++
      sourceVerdictRules normalProofMachineRuleInventory ++
        [sourceVerifierReloadCaptureRow])).mpr
  refine ⟨passiveRowsSafe, ?_⟩
  apply (programSafe_append_iff
    (compressedNormalSourceActionRulesWith extensionRules)
    (sourceVerdictRules normalProofMachineRuleInventory ++
      [sourceVerifierReloadCaptureRow])).mpr
  refine ⟨activeRowsSafe, ?_⟩
  exact (programSafe_append_iff
    (sourceVerdictRules normalProofMachineRuleInventory)
    [sourceVerifierReloadCaptureRow]).mpr
      ⟨verdictRulesSafe, reloadCaptureSafe⟩

section AxiomAudit

#print axioms sourceVerifierRuleRow_atomSafe
#print axioms sourceVerifierRuleRow_variableBudget
#print axioms sourceVerifierRuleRows_programSafe
#print axioms compressedNormalSourceActionExtension_programSafe

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceActionRendererSafety
-/

/-!
# Compositional renderer-domain safety for deferred action profiles

The deferred-action loader has five independently generated row regions. This
small interface records that composition without importing any one concrete
verifier. A concrete profile must still provide its own row certificates; this
theorem only combines them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceActionRendererSafety

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-- The renderer-relevant layout of a deferred-action program. Each region has
an independent compiler owner, which permits bounded certificates rather than
one monolithic renderer reduction. -/
structure DeferredActionRendererProfile where
  terminalRows : List Atom
  passiveReloadRows : List Atom
  activeActionRows : List Atom
  verdictRows : List Atom
  captureRows : List Atom

/-- Flatten the profile in the order consumed by the deferred-action loader. -/
def DeferredActionRendererProfile.program
    (profile : DeferredActionRendererProfile) : List Atom :=
  profile.terminalRows ++ profile.passiveReloadRows ++ profile.activeActionRows ++
    profile.verdictRows ++ profile.captureRows

/-- Named renderer certificates compose to a certificate for the complete
deferred-action program. -/
theorem deferredActionProfile_programSafe
    (profile : DeferredActionRendererProfile)
    (terminalSafe : programSafe profile.terminalRows = true)
    (passiveSafe : programSafe profile.passiveReloadRows = true)
    (activeSafe : programSafe profile.activeActionRows = true)
    (verdictSafe : programSafe profile.verdictRows = true)
    (captureSafe : programSafe profile.captureRows = true) :
    programSafe profile.program = true := by
  unfold DeferredActionRendererProfile.program
  simp only [List.append_assoc]
  apply (programSafe_append_iff profile.terminalRows
    (profile.passiveReloadRows ++
      (profile.activeActionRows ++
        (profile.verdictRows ++ profile.captureRows)))).mpr
  refine ⟨terminalSafe, ?_⟩
  apply (programSafe_append_iff profile.passiveReloadRows
    (profile.activeActionRows ++
      (profile.verdictRows ++ profile.captureRows))).mpr
  refine ⟨passiveSafe, ?_⟩
  apply (programSafe_append_iff profile.activeActionRows
    (profile.verdictRows ++ profile.captureRows)).mpr
  exact ⟨activeSafe,
    (programSafe_append_iff profile.verdictRows profile.captureRows).mpr
      ⟨verdictSafe, captureSafe⟩⟩

section AxiomAudit

#print axioms deferredActionProfile_programSafe

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceActionRendererSafety
