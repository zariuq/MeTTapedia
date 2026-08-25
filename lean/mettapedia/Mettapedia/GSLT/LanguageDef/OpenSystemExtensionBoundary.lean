import Mettapedia.GSLT.LanguageDef.ExtensionGluing
import Mettapedia.GSLT.LanguageDef.NIKInferenceExtensionAdmission

/-!
# Open-system extension boundary

Open language growth is represented by validated presentation extensions,
not by a closed enumeration of future syntax.  A current validated extension
transports every old checked judgment while retaining both its goal and exact
raw proof.  This is the conservative branch.

Authored extension data remains composable more generally.  When two layers
cross the declared interaction boundary, however, their successful authored
merge is not itself admission evidence.  The merged presentation must be
validated.  The negative control packages two individually admitted calculi
whose authored merge is rejected and proves that no validated-composite
witness can exist for that merge.

The distinction is the open-system analogue of relational primacy: proposed
growth remains inspectable data; current validated growth earns functional
transport of protected judgments.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OpenSystemExtensionBoundary

open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.ExtensionGluing
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferencePresentationExtension
open Mettapedia.GSLT.LanguageDef.NIKInferenceExtensionAdmission
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uState

/-! ## Current conservative growth -/

/-- A validated extension together with a current dependency view.  The
extension supplies structural conservativity; the revision proof supplies
current authority. -/
structure CurrentValidatedGrowth
    (base : ValidatedPresentation) (dependencies : DependencySystem)
    (admittedRevision currentRevision : dependencies.Revision) where
  extension : ValidatedExtension base
  current : dependencies.SameDependencies admittedRevision currentRevision

namespace CurrentValidatedGrowth

variable {base : ValidatedPresentation} {dependencies : DependencySystem}
variable {admittedRevision currentRevision : dependencies.Revision}

/-- The already-proved NIK transport cell activated at the current revision. -/
def activeTransport
    (growth : CurrentValidatedGrowth base dependencies admittedRevision
      currentRevision) :
    (admitTransportAt growth.extension dependencies admittedRevision).Active
      currentRevision :=
  (admitTransportAt growth.extension dependencies admittedRevision).activate
    growth.current

/-- The retained interface of a checked judgment: its indexed goal and exact
raw proof artifact. -/
def protectedView {presentation : ValidatedPresentation}
    (state : CheckedState presentation) : Pattern × RawProof :=
  (state.goal, state.derivation.erase)

/-- Current validated growth preserves every old protected judgment exactly.
No finiteness assumption is made on future extensions or on the term language. -/
theorem activeTransport_preserves_protectedView
    (growth : CurrentValidatedGrowth base dependencies admittedRevision
      currentRevision)
    (state : CheckedState base) :
    protectedView ((growth.activeTransport).run ⟨state⟩).down =
      protectedView state := by
  change
    ((transportState growth.extension state).goal,
      (transportState growth.extension state).derivation.erase) =
      (state.goal, state.derivation.erase)
  apply Prod.ext
  · exact transportState_goal growth.extension state
  · exact transportState_erase growth.extension state

/-- The same preservation law, split into the two informative fibres used by
downstream observers. -/
theorem activeTransport_preserves_goal_and_derivation
    (growth : CurrentValidatedGrowth base dependencies admittedRevision
      currentRevision)
    (state : CheckedState base) :
    let result := ((growth.activeTransport).run ⟨state⟩).down
    result.goal = state.goal ∧
      result.derivation.erase = state.derivation.erase := by
  change
    (transportState growth.extension state).goal = state.goal ∧
      (transportState growth.extension state).derivation.erase =
        state.derivation.erase
  exact ⟨rfl, transportState_erase growth.extension state⟩

end CurrentValidatedGrowth

/-! ## Revalidation at an interaction boundary -/

/-- A composite is admitted only when it retains both its authored merge
witness and validation of the resulting presentation. -/
structure ValidatedComposite
    (language : LanguageDef) (first second : ProofCalculus) where
  merged : ProofCalculus
  authored : proofCalculusMonoid.op first second = some merged
  admitted : (Presentation.mk language merged).isValidV2 = true

/-- An invalid authored merge cannot be repackaged as a validated composite. -/
theorem invalidAuthoredMerge_has_no_validatedComposite
    {language : LanguageDef} {first second merged : ProofCalculus}
    (authored : proofCalculusMonoid.op first second = some merged)
    (invalid : (Presentation.mk language merged).isValidV2 = false) :
    ¬ Nonempty (ValidatedComposite language first second) := by
  rintro ⟨composite⟩
  have sameSome : (some composite.merged : Option ProofCalculus) = some merged :=
    composite.authored.symm.trans authored
  have same : composite.merged = merged := Option.some.inj sameSome
  have compositeAdmitted := composite.admitted
  rw [same, invalid] at compositeAdmitted
  contradiction

/-- If two individually admitted calculi have an invalid authored merge, the
declared compatibility boundary was crossed. -/
theorem invalidAuthoredMerge_not_compatible
    {language : LanguageDef} {first second merged : ProofCalculus}
    (firstValid : (Presentation.mk language first).isValidV2 = true)
    (secondValid : (Presentation.mk language second).isValidV2 = true)
    (authored : proofCalculusMonoid.op first second = some merged)
    (invalid : (Presentation.mk language merged).isValidV2 = false) :
    ¬ Compatible first second := by
  intro compatible
  have glued := gluing_of_compatible language first second
    firstValid secondValid compatible
  have sameSome : (some merged : Option ProofCalculus) =
      some (mergeOf first second) := authored.symm.trans glued.1
  have same : merged = mergeOf first second := Option.some.inj sameSome
  rw [same, glued.2] at invalid
  contradiction

/-- Concrete boundary control: two admitted layers can compose as authored
data while their overlap invalidates the result.  The proposal remains data,
but there is no validated composite and therefore no silent executable
authority. -/
theorem boundary_crossing_requires_revalidation :
    ∃ (language : LanguageDef) (first second merged : ProofCalculus),
      (Presentation.mk language first).isValidV2 = true ∧
        (Presentation.mk language second).isValidV2 = true ∧
        proofCalculusMonoid.op first second = some merged ∧
        ¬ Compatible first second ∧
        (Presentation.mk language merged).isValidV2 = false ∧
        ¬ Nonempty (ValidatedComposite language first second) := by
  obtain ⟨language, first, second, merged, firstValid, secondValid,
      authored, invalid⟩ := admission_not_closed_under_composition
  exact ⟨language, first, second, merged, firstValid, secondValid, authored,
    invalidAuthoredMerge_not_compatible firstValid secondValid authored invalid,
    invalid, invalidAuthoredMerge_has_no_validatedComposite authored invalid⟩

/-- Absence of an admitted growth path does not refute or erase the original
checked judgment. -/
theorem missing_growth_preserves_source_judgment
    {presentation : ValidatedPresentation}
    (state : CheckedState presentation) :
    Nonempty (CheckedState presentation) :=
  missing_admission_preserves_checked_state state

#print axioms CurrentValidatedGrowth.activeTransport_preserves_protectedView
#print axioms CurrentValidatedGrowth.activeTransport_preserves_goal_and_derivation
#print axioms invalidAuthoredMerge_has_no_validatedComposite
#print axioms invalidAuthoredMerge_not_compatible
#print axioms boundary_crossing_requires_revalidation
#print axioms missing_growth_preserves_source_judgment

end Mettapedia.GSLT.LanguageDef.OpenSystemExtensionBoundary
