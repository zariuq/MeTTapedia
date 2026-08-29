import Mettapedia.Computability.FragmentwiseComputationalTrinity
import Mettapedia.GSLT.Core.StructuralIsomorphism
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Intentional fragmentwise computational trinity

The computational trinity compares operational, logical, and spatial
presheaves.  A useful crown must retain more than their extensional triangle:

* selected fragments remain substitution stable;
* each face retains an inspectable material GSLT presentation;
* changing a presentation by a structural GSLT isomorphism transports its
  interpretation without changing the selected semantic fragments; and
* a nonempty spatial subfragment may be checked by an independently stated
  native proof system.

The ambient authority is deliberately separate from the three presentations.
Its judgment is not defined from fragment membership, and its executable
kernel must decide that independently stated judgment exactly.  This blocks a
presentation from validating itself merely by being named as a logic or a
space.

The construction is fragmentwise.  It does not assert that the complete
program, logic, and variable-set faces are globally equivalent, nor that an
ambient authority covers every spatial element.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ComputationalTrinityCrown

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.GSLT
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity

universe uContext vContext uFace uClaim uProof

variable {Context : Type uContext}
  [CategoryTheory.Category.{vContext} Context]

/-! ## Inspectable material presentations -/

/-- The constant contextual face carried by the raw terms of one GSLT
presentation. -/
abbrev termFace (presentation : GSLT.{uFace}) :
    Face.{uContext, vContext, uFace} Context :=
  (CategoryTheory.Functor.const Contextᵒᵖ).obj presentation.Term

/-- An inspectable GSLT presentation of a semantic face.  Authored equations
must be sound for the displayed interpretation.  Primitive steps remain
inspectable in `presentation`; no quotient of them is installed here. -/
structure MaterialPresentation
    (face : Face.{uContext, vContext, uFace} Context) where
  presentation : GSLT.{uFace}
  realize : termFace presentation ⟶ face
  equation_sound : ∀ context left right,
    presentation.Equiv left right →
      realize.app context left = realize.app context right

namespace MaterialPresentation

variable {face : Face.{uContext, vContext, uFace} Context}

/-- The inverse syntax map of a structural isomorphism, viewed as a natural
transformation between constant term faces. -/
def inverseTermMap {sourcePresentation targetPresentation : GSLT.{uFace}}
    (isomorphism :
      StructuralIsomorphism sourcePresentation targetPresentation) :
    termFace (Context := Context) targetPresentation ⟶
      termFace (Context := Context) sourcePresentation where
  app _ := TypeCat.ofHom (fun term => isomorphism.termEquiv.symm term)
  naturality := by
    intro source target substitution
    rfl

/-- Re-present a material face along an isomorphism which preserves and
reflects authored equations and primitive steps.  Semantic realization uses
the inverse syntax map; the semantic face itself is unchanged. -/
def transport {targetPresentation : GSLT.{uFace}}
    (material : MaterialPresentation face)
    (isomorphism :
      StructuralIsomorphism material.presentation targetPresentation) :
    MaterialPresentation face where
  presentation := targetPresentation
  realize := CategoryTheory.CategoryStruct.comp
    (inverseTermMap isomorphism) material.realize
  equation_sound := by
    intro context left right equivalent
    apply material.equation_sound
    exact (isomorphism.symm.equiv_iff left right).2 equivalent

/-- Transporting the forward image of a source term realizes exactly the
same semantic element. -/
@[simp] theorem transport_realize_forward
    {targetPresentation : GSLT.{uFace}}
    (material : MaterialPresentation face)
    (isomorphism :
      StructuralIsomorphism material.presentation targetPresentation)
    (context : Contextᵒᵖ) (term : material.presentation.Term) :
    (material.transport isomorphism).realize.app context
        (isomorphism.termEquiv term) =
      material.realize.app context term := by
  change material.realize.app context
      (isomorphism.termEquiv.symm (isomorphism.termEquiv term)) =
    material.realize.app context term
  rw [isomorphism.termEquiv.symm_apply_apply]

/-- Successive structural changes and their composite have the same semantic
realization. -/
theorem transport_realize_trans
    {middlePresentation targetPresentation : GSLT.{uFace}}
    (material : MaterialPresentation face)
    (first :
      StructuralIsomorphism material.presentation middlePresentation)
    (second : StructuralIsomorphism middlePresentation targetPresentation)
    (context : Contextᵒᵖ) (term : targetPresentation.Term) :
    ((material.transport first).transport second).realize.app context term =
      (material.transport (first.trans second)).realize.app context term := by
  rfl

end MaterialPresentation

/-! ## Independent ambient authority -/

/-- A nonempty subfragment of a spatial face checked by a native proof
system whose judgment is stated independently of the trinity comparison.

`claim_natural` makes the ambient question stable under contextual
substitution.  `witness` retains the exact native proof object for every
element in the named scope; the Boolean kernel earns authority only through
its correctness theorem for that independent judgment. -/
structure AmbientAuthoritySection
    (space : Face.{uContext, vContext, uFace} Context) where
  Claim : Type uClaim
  proofSystem : NativeProofSystem.{uClaim, uProof} Claim
  kernel : NativeProofKernel proofSystem
  claimAt : ∀ context, space.obj context → Claim
  claim_natural : ∀ {source target : Contextᵒᵖ}
      (substitution : source ⟶ target) (element : space.obj source),
    claimAt target (space.map substitution element) = claimAt source element
  scope : Constraint space
  nonempty_scope : ∃ context element, scope.holds context element
  witness : ∀ context element, scope.holds context element →
    proofSystem.ProofFibre (claimAt context element)

namespace AmbientAuthoritySection

variable {space : Face.{uContext, vContext, uFace} Context}

/-- Every scoped ambient witness is accepted by the independently correct
native checker. -/
theorem checked
    (ambient : AmbientAuthoritySection.{uContext, vContext, uFace,
      uClaim, uProof} space)
    (context : Contextᵒᵖ) (element : space.obj context)
    (inScope : ambient.scope.holds context element) :
    ambient.kernel.toChecker.check (ambient.claimAt context element)
        (ambient.witness context element inScope).1 = true := by
  exact (ambient.kernel.correct _ _).2
    (ambient.witness context element inScope).2

/-- The native proof retained by an ambient section survives reindexing.  The
claim equality is explicit rather than inferred from a Boolean check. -/
def reindexWitness
    (ambient : AmbientAuthoritySection.{uContext, vContext, uFace,
      uClaim, uProof} space)
    {source target : Contextᵒᵖ} (substitution : source ⟶ target)
    (element : space.obj source)
    (inScope : ambient.scope.holds source element) :
    ambient.proofSystem.ProofFibre
      (ambient.claimAt target (space.map substitution element)) := by
  rw [ambient.claim_natural substitution element]
  exact ambient.witness source element inScope

end AmbientAuthoritySection

/-! ## The crown and structural transport -/

/-- A fragmentwise computational trinity whose three semantic faces retain
material, inspectable GSLT presentations.  The spatial face is already an
object of the presheaf topos; this structure does not replace it by its raw
presentation. -/
structure Crown
    (comparison : Comparison.{uContext, vContext, uFace} Context) where
  fragments : ComputationalTrinity.FragmentwiseComparison comparison
  programMaterial : MaterialPresentation comparison.program
  logicMaterial : MaterialPresentation comparison.logic
  spaceMaterial : MaterialPresentation comparison.space

/-- A crown with a genuine, nonempty independently checked ambient section.
The section is scoped inside the selected spatial fragment rather than
silently promoted to a global universe claim. -/
structure AmbientCrown
    (comparison : Comparison.{uContext, vContext, uFace} Context)
    extends Crown comparison where
  ambient : AmbientAuthoritySection.{uContext, vContext, uFace,
    uClaim, uProof} comparison.space
  ambient_within_space : ambient.scope.Entails fragments.spaceFragment

namespace Crown

variable {comparison : Comparison.{uContext, vContext, uFace} Context}

/-- Re-present all three material faces by structural GSLT isomorphisms.  The
comparison and its selected fragments are unchanged. -/
def transport
    (crown : Crown comparison)
    {programPresentation logicPresentation spacePresentation : GSLT.{uFace}}
    (programIso : StructuralIsomorphism
      crown.programMaterial.presentation programPresentation)
    (logicIso : StructuralIsomorphism
      crown.logicMaterial.presentation logicPresentation)
    (spaceIso : StructuralIsomorphism
      crown.spaceMaterial.presentation spacePresentation) :
    Crown comparison where
  fragments := crown.fragments
  programMaterial := crown.programMaterial.transport programIso
  logicMaterial := crown.logicMaterial.transport logicIso
  spaceMaterial := crown.spaceMaterial.transport spaceIso

@[simp] theorem transport_fragments
    (crown : Crown comparison)
    {programPresentation logicPresentation spacePresentation : GSLT.{uFace}}
    (programIso : StructuralIsomorphism
      crown.programMaterial.presentation programPresentation)
    (logicIso : StructuralIsomorphism
      crown.logicMaterial.presentation logicPresentation)
    (spaceIso : StructuralIsomorphism
      crown.spaceMaterial.presentation spacePresentation) :
    (crown.transport programIso logicIso spaceIso).fragments =
      crown.fragments :=
  rfl

/-- The direct operational-to-spatial fragment theorem is inherited from the
fragmentwise comparison; adding material presentations does not strengthen it
to a global equivalence. -/
theorem programSpaceCompatible (crown : Crown comparison) :
    (crown.fragments.programFragment.pushforward
      comparison.programToSpace).Entails crown.fragments.spaceFragment :=
  crown.fragments.programSpaceCompatible

end Crown

namespace AmbientCrown

variable {comparison : Comparison.{uContext, vContext, uFace} Context}

/-- Structural re-presentation changes none of the ambient authority data or
its scoped relation to the spatial fragment. -/
def transport
    (crown : AmbientCrown.{uContext, vContext, uFace, uClaim, uProof}
      comparison)
    {programPresentation logicPresentation spacePresentation : GSLT.{uFace}}
    (programIso : StructuralIsomorphism
      crown.programMaterial.presentation programPresentation)
    (logicIso : StructuralIsomorphism
      crown.logicMaterial.presentation logicPresentation)
    (spaceIso : StructuralIsomorphism
      crown.spaceMaterial.presentation spacePresentation) :
    AmbientCrown.{uContext, vContext, uFace, uClaim, uProof} comparison where
  toCrown := crown.toCrown.transport programIso logicIso spaceIso
  ambient := crown.ambient
  ambient_within_space := crown.ambient_within_space

/-- A scoped ambient point is both part of the selected spatial fragment and
accepted by the independent native checker. -/
theorem scoped_point_is_spatial_and_checked
    (crown : AmbientCrown.{uContext, vContext, uFace, uClaim, uProof}
      comparison)
    (context : Contextᵒᵖ) (element : comparison.space.obj context)
    (inScope : crown.ambient.scope.holds context element) :
    crown.fragments.spaceFragment.holds context element ∧
      crown.ambient.kernel.toChecker.check
        (crown.ambient.claimAt context element)
        (crown.ambient.witness context element inScope).1 = true :=
  ⟨crown.ambient_within_space context element inScope,
    crown.ambient.checked context element inScope⟩

end AmbientCrown

#print axioms MaterialPresentation.transport_realize_forward
#print axioms MaterialPresentation.transport_realize_trans
#print axioms AmbientAuthoritySection.checked
#print axioms AmbientAuthoritySection.reindexWitness
#print axioms Crown.programSpaceCompatible
#print axioms AmbientCrown.scoped_point_is_spatial_and_checked

end Mettapedia.Computability.ComputationalTrinityCrown
