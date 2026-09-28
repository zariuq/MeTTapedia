import Mettapedia.Languages.Agda.Adequacy.AdministrativePreservationQualification
import Mettapedia.Languages.Agda.SourceMetatheory.Audit
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctionControls
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentAdjunction
import Mettapedia.Languages.Agda.Structural.AdministrativeDependentObjectControls
import Mettapedia.OSLF.Syntax.FiniteRuleProofWireControls

/-!
# Native foundation qualification

The finite-Set/relevant-Pi source fundamental theorem supplies actual Pi
components used by native beta preservation. All twenty-nine compatible
structural reduction rules now preserve the thirty-six-rule static family.
The actual presentation-tree and path adapters return native typing/equality;
these maps do not assert an injection of operational histories into proofs.

Dependent sections over categories of elements provide evaluation, currying,
and the hom-set adjunction. Actual typed local application supplies supported
result sections. Neither a converse nor a complete classifying construction
is claimed. The optional choice-bearing Mathlib Adjunction wrapper is excluded.

The generic native proof codec preserves complete ordered derivations. Its
executable instances require effective shape codecs, judgment equality and
ordered-premise computation. No concrete Agda codec, proof-producing checker,
full normalization/decision theorem or source-host qualification is included.
-/

open Lean Lean.Elab.Command

run_cmd do
  let prefixes : List Name := [
    `Mettapedia.Languages.Agda.Specification,
    `Mettapedia.Languages.Agda.StaticSpecification,
    `Mettapedia.Languages.Agda.StaticMetatheory,
    `Mettapedia.Languages.Agda.SourceEvidence,
    `Mettapedia.Languages.Agda.SourceMetatheory,
    `Mettapedia.Languages.Agda.Structural,
    `Mettapedia.Languages.Agda.Adequacy,
    `Mettapedia.Languages.Agda.StaticAdequacy,
    `Mettapedia.OSLF.Binding.CompatibleDerivations,
    `Mettapedia.OSLF.Binding.Telescope,
    `Mettapedia.OSLF.Binding.FiniteRulePremiseLists,
    `Mettapedia.OSLF.Binding.FiniteRuleProofWire,
    `Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback,
    `Mettapedia.GSLT.Core.ContextualLadder.ContextualJudgment,
    `Mettapedia.GSLT.Core.ContextualLadder.CwfDerivations,
    `Mettapedia.GSLT.Topos.ConstructivePresheaf,
    `Mettapedia.GSLT.Topos.PresheafEventModalities,
    `Mettapedia.OSLF.Binding.IntrinsicScopedLocalTelescopePresheaf,
    `Mettapedia.OSLF.Binding.BindingTelescopeConstructorPresheaf,
    `Mettapedia.Logic.HOL.SignatureImageAdmission]
  let names : List Name := [
    `Mettapedia.GSLT.Core.ContextualLadder.ContextualRulePresentation,
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
  let modulePrefixes : List Name := [
    `Mettapedia.Languages.Agda.Specification,
    `Mettapedia.Languages.Agda.StaticSpecification,
    `Mettapedia.Languages.Agda.StaticMetatheory,
    `Mettapedia.Languages.Agda.SourceEvidence,
    `Mettapedia.Languages.Agda.SourceMetatheory,
    `Mettapedia.Languages.Agda.Structural,
    `Mettapedia.Languages.Agda.Adequacy]
  let modules : List Name := [
    `Mettapedia.GSLT.Topos.ConstructivePresheafOperations,
    `Mettapedia.GSLT.Topos.ConstructivePresheafBaseChange,
    `Mettapedia.GSLT.Topos.ConstructivePresheafBaseChangeControls,
    `Mettapedia.GSLT.Topos.ConstructivePresheafFunctions,
    `Mettapedia.GSLT.Topos.ConstructivePresheafFunctionPredicates,
    `Mettapedia.GSLT.Topos.ConstructivePresheafFunctionControls,
    `Mettapedia.GSLT.Topos.ConstructivePresheafFunctionLogic,
    `Mettapedia.GSLT.Topos.ConstructivePresheafDependentPredicates,
    `Mettapedia.GSLT.Topos.ConstructivePresheafDependentControls,
    `Mettapedia.GSLT.Topos.ConstructivePresheafFamilies,
    `Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions,
    `Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctionControls,
    `Mettapedia.GSLT.Topos.ConstructivePresheafDependentResultFamilies,
    `Mettapedia.GSLT.Topos.ConstructivePresheafDependentAdjunction,
    `Mettapedia.OSLF.Syntax.FiniteRuleProofWire,
    `Mettapedia.OSLF.Syntax.FiniteRuleProofWireControls,
    `Mettapedia.GSLT.Topos.PresheafEventModalities,
    `Mettapedia.GSLT.Topos.PresheafEventModalControls,
    `Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTelescopePresheaf,
    `Mettapedia.OSLF.Syntax.BindingTelescopeConstructorPresheaf]
  let allowed := [``propext, ``Quot.sound]
  let env ← getEnv
  let mut count : Nat := 0
  let mut namespaceCount : Nat := 0
  let mut moduleCount : Nat := 0
  for (name, _) in env.constants.toList do
    let byName := prefixes.any (·.isPrefixOf name) || names.contains name
    let byModule := match env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) with
      | none => false
      | some info => modulePrefixes.any (·.isPrefixOf info.module) || modules.contains info.module
    if byName then namespaceCount := namespaceCount + 1
    if byModule then moduleCount := moduleCount + 1
    if byName || byModule then
      let excess := (← collectAxioms name).filter fun dependency => !allowed.contains dependency
      unless excess.isEmpty do
        throwError "Native foundation axiom gate failed for {name}: {excess}"
      count := count + 1
  logInfo m!"Native foundation: {namespaceCount} namespace/name-selected declarations; {moduleCount} module-origin declarations; {count} in their union, all within [propext, Quot.sound]."
