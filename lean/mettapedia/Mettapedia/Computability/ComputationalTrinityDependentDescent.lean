import Mathlib.CategoryTheory.EpiMono
import Mettapedia.Computability.SplitReadoutComparison
import Mettapedia.TypeTheory.UniversalDependentFamilyDescent

/-!
# Dependent-family descent in a computational trinity

A split interpretation between contextual faces has a selected representative
for every target element.  At each context it therefore induces a split
readout of ordinary carriers.  This module relates three properties of such an
interpretation:

* it loses no source element at any context;
* every dependent family on every source carrier descends through it; and
* ordinary source equality compares exactly with equality after observation.

The properties are equivalent.  Hence a computational-trinity leg which
deliberately forgets occurrence, schedule, provenance, evidence, revision, or
cost cannot simultaneously be a universal base for arbitrary dependent
families.  Selected fibre-invariant families may still descend, and exactness
may still hold on a selected fragment.

The theorem is contextual but pointwise at the level of dependent families.
It does not yet construct a dependent presheaf, comprehension structure, or
object-language translation; those require additional naturality and
substitution-coherence data.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ComputationalTrinityDependentDescent

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.UniversalDependentFamilyDescent

universe uContext vContext uFace uFibre

variable {Context : Type uContext} [Category.{vContext} Context]
variable {source target : Face.{uContext, vContext, uFace} Context}
variable {interpretation : source ⟶ target}

/-! ## A split natural interpretation as pointwise readouts -/

/-- The carrier-level split readout induced at one context by a split natural
interpretation. -/
def componentReadout
    (splitting : SplitEpi interpretation) (context : Contextᵒᵖ) :
    SplitReadout (source.obj context) (target.obj context) where
  observe := interpretation.app context
  representative := splitting.section_.app context
  observe_representative := by
    intro targetElement
    have componentIdentity :=
      congrArg (fun transformation ↦ transformation.app context targetElement)
        splitting.id
    exact componentIdentity

/-- The interpretation is injective at every context. -/
def PointwiseInjective (interpretation : source ⟶ target) : Prop :=
  forall context, Function.Injective (interpretation.app context)

/-- Every dependent family at every context descends through the induced
split readout. -/
def PointwiseAllFamiliesDescend
    (splitting : SplitEpi interpretation) : Prop :=
  forall context,
    AllFamiliesDescend.{uFace, uFace, uFibre}
      (componentReadout splitting context)

/-- Ordinary source equality compares exactly with equality after
interpretation at every context. -/
def PointwiseOrdinaryIdentityExact
    (splitting : SplitEpi interpretation) : Prop :=
  forall context,
    (ordinaryIdentityComparison
      (componentReadout splitting context)).Exact

/-- A split contextual interpretation is pointwise injective exactly when all
dependent families descend at every context. -/
theorem pointwiseInjective_iff_allFamiliesDescend
    (splitting : SplitEpi interpretation) :
    PointwiseInjective interpretation <->
      PointwiseAllFamiliesDescend.{uContext, vContext, uFace, uFibre}
        splitting := by
  constructor
  · intro injective context
    apply
      (exact_iff_allFamiliesDescend.{uFace, uFace, uFibre}
        (componentReadout splitting context)).1
    exact
      (componentReadout splitting context).exact_iff_faithful.mpr
        (injective context)
  · intro allFamilies context
    exact
      (componentReadout splitting context).exact_iff_faithful.mp
        ((exact_iff_allFamiliesDescend.{uFace, uFace, uFibre}
          (componentReadout splitting context)).2
            (allFamilies context))

/-- Pointwise universal family descent reaches exactly the same boundary as
pointwise exact transport of ordinary equality. -/
theorem allFamiliesDescend_iff_ordinaryIdentityExact
    (splitting : SplitEpi interpretation) :
    PointwiseAllFamiliesDescend.{uContext, vContext, uFace, uFibre}
        splitting <->
      PointwiseOrdinaryIdentityExact splitting := by
  constructor
  · intro allFamilies context
    exact
      (allFamiliesDescend_iff_ordinaryIdentityComparison_exact.{uFace,
        uFace, uFibre} (componentReadout splitting context)).1
          (allFamilies context)
  · intro identityExact context
    exact
      (allFamiliesDescend_iff_ordinaryIdentityComparison_exact.{uFace,
        uFace, uFibre} (componentReadout splitting context)).2
          (identityExact context)

/-! ## Computational-trinity information loss -/

/-- A trinity comparison loses no program information exactly when its direct
program-to-space interpretation is pointwise injective. -/
theorem not_losesProgramInformation_iff_pointwiseInjective
    (comparison : Comparison.{uContext, vContext, uFace} Context) :
    (Not comparison.LosesProgramInformation) <->
      PointwiseInjective comparison.programToSpace := by
  constructor
  · intro noLoss context left right sameObservation
    apply Classical.byContradiction
    intro different
    exact noLoss ⟨context, left, right, different, sameObservation⟩
  · intro injective
    rintro ⟨context, left, right, different, sameObservation⟩
    exact different (injective context sameObservation)

/-- For a split direct interpretation, absence of program-information loss is
equivalent to universal dependent-family descent. -/
theorem not_losesProgramInformation_iff_allFamiliesDescend
    (comparison : Comparison.{uContext, vContext, uFace} Context)
    (splitting : SplitEpi comparison.programToSpace) :
    (Not comparison.LosesProgramInformation) <->
      PointwiseAllFamiliesDescend.{uContext, vContext, uFace, uFibre}
        splitting :=
  (not_losesProgramInformation_iff_pointwiseInjective comparison).trans
    (pointwiseInjective_iff_allFamiliesDescend splitting)

/-- The full boundary: no program-information loss, universal dependent-family
descent, and exact ordinary-identity transport coincide for a split direct
interpretation. -/
theorem computationalTrinity_dependent_descent_boundary
    (comparison : Comparison.{uContext, vContext, uFace} Context)
    (splitting : SplitEpi comparison.programToSpace) :
    ((Not comparison.LosesProgramInformation) <->
        PointwiseAllFamiliesDescend.{uContext, vContext, uFace, uFibre}
          splitting) ∧
      (PointwiseAllFamiliesDescend.{uContext, vContext, uFace, uFibre}
          splitting <-> PointwiseOrdinaryIdentityExact splitting) :=
  ⟨not_losesProgramInformation_iff_allFamiliesDescend comparison splitting,
    allFamiliesDescend_iff_ordinaryIdentityExact splitting⟩

/-! ## Constant-face controls from ordinary split readouts -/

namespace Canary

open Mettapedia.Computability.SplitReadoutComparison
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-- The natural transformation induced by an ordinary split readout is a
split epimorphism between the corresponding constant faces. -/
def constantReadoutSplitEpi {Source Target : Type uFace}
    (readout : SplitReadout Source Target) :
    SplitEpi (readoutMap readout) where
  section_ :=
    (Functor.const SplitReadoutComparison.Contextᵒᵖ).map
      (↾(readout.representative : Target -> Source))
  id := by
    ext context target
    exact readout.observe_representative target

/-- The route-forgetting comparison is lawful and split, but it does not
support universal dependent-family descent. -/
theorem routeReadout_not_pointwiseAllFamiliesDescend :
    Not
      (PointwiseAllFamiliesDescend.{0, 0, 0, uFibre}
        (constantReadoutSplitEpi
          Mettapedia.TypeTheory.ExtensionalReadout.Canary.routeReadout)) := by
  intro allFamilies
  have noLoss :=
    (not_losesProgramInformation_iff_allFamiliesDescend.{0, 0, 0, uFibre}
      (SplitReadoutComparison.comparison
        Mettapedia.TypeTheory.ExtensionalReadout.Canary.routeReadout)
      (constantReadoutSplitEpi
        Mettapedia.TypeTheory.ExtensionalReadout.Canary.routeReadout)).2
          allFamilies
  exact noLoss SplitReadoutComparison.Canary.routeReadout_comparison_loses

/-- The identity readout gives the positive control. -/
theorem identityReadout_pointwiseAllFamiliesDescend :
    PointwiseAllFamiliesDescend.{0, 0, 0, uFibre}
      (constantReadoutSplitEpi
        Mettapedia.TypeTheory.UniversalDependentFamilyDescent.Canary.identityReadout) := by
  apply
    (pointwiseInjective_iff_allFamiliesDescend.{0, 0, 0, uFibre}
      (constantReadoutSplitEpi
        Mettapedia.TypeTheory.UniversalDependentFamilyDescent.Canary.identityReadout)).1
  intro context left right same
  exact same

/-- Paired contextual control. -/
theorem contextual_dependent_descent_boundary :
    PointwiseAllFamiliesDescend.{0, 0, 0, uFibre}
        (constantReadoutSplitEpi
          Mettapedia.TypeTheory.UniversalDependentFamilyDescent.Canary.identityReadout) ∧
      Not
        (PointwiseAllFamiliesDescend.{0, 0, 0, uFibre}
          (constantReadoutSplitEpi
            Mettapedia.TypeTheory.ExtensionalReadout.Canary.routeReadout)) :=
  ⟨identityReadout_pointwiseAllFamiliesDescend,
    routeReadout_not_pointwiseAllFamiliesDescend⟩

end Canary

#print axioms componentReadout
#print axioms pointwiseInjective_iff_allFamiliesDescend
#print axioms allFamiliesDescend_iff_ordinaryIdentityExact
#print axioms not_losesProgramInformation_iff_pointwiseInjective
#print axioms not_losesProgramInformation_iff_allFamiliesDescend
#print axioms computationalTrinity_dependent_descent_boundary
#print axioms Canary.routeReadout_not_pointwiseAllFamiliesDescend
#print axioms Canary.contextual_dependent_descent_boundary

end Mettapedia.Computability.ComputationalTrinityDependentDescent
