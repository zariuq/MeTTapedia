import Mettapedia.Languages.Agda.Adequacy.ContextQualification
import Mettapedia.Languages.Agda.Adequacy.StaticControls
import Mettapedia.Languages.Agda.Adequacy.StaticForwardControls
import Mettapedia.Languages.Agda.Structural.StaticAdmissionControls
import Mettapedia.Languages.Agda.Structural.SpineAdmissionControls
import Mettapedia.Languages.Agda.StaticMetatheory.Controls
import Mettapedia.Languages.Agda.Structural.StaticRegularityControls
import Mettapedia.Languages.Agda.Adequacy.StaticObservationControls
import Mettapedia.Languages.Agda.Adequacy.StaticSpineObservationControls
import Mettapedia.Languages.Agda.Adequacy.StaticReflectionControls
import Mettapedia.Languages.Agda.Adequacy.StaticSpineReflection
import Mettapedia.Languages.Agda.Adequacy.AdministrativeReflectionControls
import Mettapedia.Languages.Agda.Structural.AdministrativeRegularityControls
import Mettapedia.Languages.Agda.Structural.AdministrativePreservationControls
import Mettapedia.Languages.Agda.Structural.AdministrativeConstructorControls
import Mettapedia.GSLT.Topos.PresheafEventModalControls
import Mettapedia.GSLT.Topos.ConstructivePresheafBaseChangeControls
import Mettapedia.Languages.Agda.Structural.AdministrativeBinderPreservationControls
import Mettapedia.GSLT.Topos.ConstructivePresheafFunctionControls
import Mettapedia.GSLT.Topos.ConstructivePresheafFunctionLogic
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentControls
import Mettapedia.Languages.Agda.Structural.AdministrativeDependentFunctionControls
import Mettapedia.Languages.Agda.Structural.AdministrativeLocalFunctionControls
import Mettapedia.Languages.Agda.SourceEvidence.CodecAudit

/-!
# Qualification of structural statics and internal predicates

The imported constructions include source-to-presentation translation and
reflection of arbitrary native trees for the finite-universe Pi fragment.
All five embedded source judgments have inhabitedness equivalences. Reflection
does not give an equivalence of proof histories. The recursive administrative
presentation has native renaming, typed substitution, endpoint regularity,
functionality, dependent context conversion and an admitted context CwF.
The independent source metatheory remains separately frozen and mechanically
isolated from the presentation.

Native certificates prove administrative root preservation and the displayed
compatible constructions, including lambda, Pi and annotated-type positions.
Actual computation histories form a
presheaf over admitted contexts; static support and constructor-derived
predicates are stable under typed substitution. Internal modal adjunctions and
predicate base change hold with the stated pullback data. Internal function
objects have constructive currying laws. Native dependent application supplies
future-arrow predicates, including local free annotations indexed by the
category of elements. These predicates do not characterize static typing by
a converse implication. The separately derived source codec preserves all
source proof histories and reconstructs evidence from known inhabitation;
it is neither native derivation serialization nor a decision procedure.

These constructions do not yet establish full subject reduction, normalization, a classifying
native type theory, or a native Agda checker. The canonical presentation's
subject-reduction counterexample remains a checked boundary control.
-/

open Lean Lean.Elab.Command

run_cmd do
  let prefixes : List Name := [
    `Mettapedia.Languages.Agda.Specification,
    `Mettapedia.Languages.Agda.StaticSpecification,
    `Mettapedia.Languages.Agda.StaticMetatheory,
    `Mettapedia.Languages.Agda.SourceEvidence,
    `Mettapedia.Languages.Agda.Structural,
    `Mettapedia.Languages.Agda.Adequacy,
    `Mettapedia.Languages.Agda.StaticAdequacy,
    `Mettapedia.OSLF.Binding.CompatibleDerivations,
    `Mettapedia.OSLF.Binding.Telescope,
    `Mettapedia.OSLF.Binding.FiniteRulePremiseLists,
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
        throwError "Structural statics axiom gate failed for {name}: {excess}"
      count := count + 1
  logInfo m!"Structural statics and internal predicates: {namespaceCount} namespace/name-selected declarations; {moduleCount} module-origin declarations; {count} in their union, all within [propext, Quot.sound]."
