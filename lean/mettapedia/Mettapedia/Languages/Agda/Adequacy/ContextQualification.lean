import Mettapedia.Languages.Agda.Adequacy.Qualification
import Mettapedia.Languages.Agda.Structural.ContextGeometryCwf
import Mettapedia.Languages.Agda.StaticSpecification.Audit
import Mettapedia.GSLT.Core.ContextualAdmissionMorphism
import Mettapedia.Logic.HOL.Embedding.SignatureImageAdmission

/-!
# Axiom gate for raw contexts and conditional admission

This gate includes the structural computation fragment, raw telescope geometry,
the generic restriction to supported syntax, its retained evidence fibres, and
the HOL signature-image instance. It also includes the separately authored
finite-universe Pi reference and its structural admissibility proofs.

These are distinct checked components. Their joint import does not establish
static adequacy between the independent reference and the structural Agda
presentation, a normalization theorem, or a native Agda checking algorithm.
-/

open Lean Lean.Elab.Command

run_cmd do
  let prefixes : List Name := [
    `Mettapedia.Languages.Agda.Specification,
    `Mettapedia.Languages.Agda.StaticSpecification,
    `Mettapedia.Languages.Agda.Structural,
    `Mettapedia.Languages.Agda.Adequacy,
    `Mettapedia.OSLF.Binding.CompatibleDerivations,
    `Mettapedia.OSLF.Binding.Telescope,
    `Mettapedia.GSLT.Core.ContextualLadder.CwfDerivations,
    `Mettapedia.Logic.HOL.SignatureImageAdmission]
  let names : List Name := [
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.ComprehensionData,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.decompose,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.assemble,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.assemble_decompose,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.decompose_assemble,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.comprehensionEquiv,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.precomposeData,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.decompose_natural,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.assemble_natural,
    `Mettapedia.GSLT.Core.ContextualLadder.Cwf.pair_distinguishes_terms]
  let allowed := [``propext, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if prefixes.any (·.isPrefixOf name) || names.contains name then
      let excess := (← collectAxioms name).filter fun dependency => !allowed.contains dependency
      unless excess.isEmpty do
        throwError "Context foundation axiom gate failed for {name}: {excess}"
      count := count + 1
  logInfo m!"Context foundations and independent static reference: {count} declarations within [propext, Quot.sound]."
