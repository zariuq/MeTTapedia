import Mettapedia.TypeTheory.IdentityObservationComparison

/-!
# Universal descent of dependent families

A split readout supports each selected dependent family precisely when that
family is invariant, up to equivalence, on the fibres of the readout.  This
module identifies the stronger boundary at which *every* dependent family can
be transported: universal dependent-family descent is equivalent to exactness
of the readout.

The converse is witnessed by anchored equality families.  If two source
points have the same observation, factorization of the equality family
anchored at the first point reflects their equality.  Thus a genuinely lossy
extensional readout cannot serve as a universal base for arbitrary dependent
families, even though constant and other fibre-invariant families may descend.

For ordinary proof-irrelevant source equality, the same boundary is exactly
the boundary for an exact comparison with equality after observation.  This
connects dependent-family descent and identity readout without selecting an
object-language identity type or requiring all retained route systems to be
proof irrelevant.

These are type-level factorization results.  They do not by themselves supply
substitution coherence, universe closure, a type-theory interpretation, or a
translation between concrete calculi.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniversalDependentFamilyDescent

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.IdentityObservationComparison

universe uSource uTarget uFibre

/-! ## Universal family descent -/

/-- Every family in a selected universe factors through the split readout, up
to fibrewise equivalence. -/
def AllFamiliesDescend
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target) : Prop :=
  forall family : Source -> Type uFibre,
    Nonempty (FamilyFactorization readout.observe family)

/-- An exact split readout transports every dependent family. -/
theorem allFamiliesDescend_of_exact
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target) (exact : readout.Exact) :
    AllFamiliesDescend.{uSource, uTarget, uFibre} readout := by
  have canonical :=
    readout.faithful_iff_canonicalize_eq.mp
      (readout.exact_iff_faithful.mp exact)
  intro family
  refine
    (FamilyFactorization.nonempty_iff_canonicalFibreEquivalences
      readout family).2 ?_
  refine ⟨fun source => ?_⟩
  simpa [canonical source] using (Equiv.refl (family source))

/-- An equality family lifted into the selected fibre universe.  Its fibre at
`source` is inhabited exactly when `anchor = source`. -/
def liftedAnchoredEquality
    {Source : Type uSource} (anchor : Source) (source : Source) : Type uFibre :=
  ULift.{uFibre} (PLift (anchor = source))

/-- Universal family descent forces the endpoint observation to be injective.
The proof uses only the factorization of lifted anchored equality families. -/
theorem observe_injective_of_allFamiliesDescend
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target)
    (allFamilies : AllFamiliesDescend.{uSource, uTarget, uFibre} readout) :
    Function.Injective readout.observe := by
  intro left right sameObservation
  obtain ⟨factorization⟩ :=
    allFamilies (liftedAnchoredEquality.{uSource, uFibre} left)
  let reflected :=
    (factorization.fibreEquiv sameObservation).toFun
      (ULift.up (PLift.up (rfl : left = left)))
  exact reflected.down.down

/-- For a split readout, universal dependent-family descent is exactly
exactness.  The result holds independently at every fibre universe. -/
theorem exact_iff_allFamiliesDescend
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target) :
    readout.Exact <->
      AllFamiliesDescend.{uSource, uTarget, uFibre} readout := by
  constructor
  · exact allFamiliesDescend_of_exact readout
  · intro allFamilies
    exact readout.exact_iff_faithful.mpr
      (observe_injective_of_allFamiliesDescend readout allFamilies)

/-! ## Agreement with ordinary source equality -/

/-- The canonical comparison from ordinary source equality to equality after
the readout. -/
def ordinaryIdentityComparison
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target) :
    Comparison
      (IdentityObservationComparison.Canary.equalityLayer Source)
      readout.observe :=
  ofEndpointReflection
    (IdentityObservationComparison.Canary.equalityLayer_reflects Source)
    readout.observe

/-- Exact comparison of ordinary source equality with observed equality is
equivalent to exactness of the split readout. -/
theorem ordinaryIdentityComparison_exact_iff_readout_exact
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target) :
    (ordinaryIdentityComparison readout).Exact <-> readout.Exact := by
  constructor
  · intro exact
    exact
      (splitReadout_exactComparison_iff
        (IdentityObservationComparison.Canary.equalityLayer_reflects Source)
        readout).mp exact |>.1
  · intro exact
    exact
      (splitReadout_exactComparison_iff
        (IdentityObservationComparison.Canary.equalityLayer_reflects Source)
        readout).mpr
          ⟨exact,
            IdentityObservationComparison.Canary.equalityLayer_uip Source⟩

/-- Universal dependent-family descent and exact transport of ordinary
identity reach the same observer boundary. -/
theorem allFamiliesDescend_iff_ordinaryIdentityComparison_exact
    {Source : Type uSource} {Target : Type uTarget}
    (readout : SplitReadout Source Target) :
    AllFamiliesDescend.{uSource, uTarget, uFibre} readout <->
      (ordinaryIdentityComparison readout).Exact :=
  (exact_iff_allFamiliesDescend.{uSource, uTarget, uFibre}
    readout).symm.trans
      (ordinaryIdentityComparison_exact_iff_readout_exact readout).symm

/-! ## Positive and negative controls -/

namespace Canary

/-- The identity split readout is exact. -/
def identityReadout : SplitReadout Bool Bool where
  observe := id
  representative := id
  observe_representative := fun _ => rfl

theorem identityReadout_exact : identityReadout.Exact :=
  ⟨Function.injective_id, Function.surjective_id⟩

/-- Consequently every dependent family descends through the identity
readout, at every universe level. -/
theorem identityReadout_allFamiliesDescend :
    AllFamiliesDescend.{0, 0, uFibre} identityReadout :=
  allFamiliesDescend_of_exact identityReadout identityReadout_exact

/-- The route-forgetting split readout is a negative control: it is complete
on visible values but cannot carry every dependent family. -/
theorem routeReadout_not_allFamiliesDescend :
    Not
      (AllFamiliesDescend.{0, 0, uFibre}
        ExtensionalReadout.Canary.routeReadout) := by
  rw [<-
    exact_iff_allFamiliesDescend.{0, 0, uFibre}
      ExtensionalReadout.Canary.routeReadout]
  exact ExtensionalReadout.Canary.routeReadout_not_exact

/-- The lifted equality family gives an explicit family-level obstruction for
the route-forgetting readout. -/
theorem routeReadout_liftedEquality_does_not_descend :
    Not
      (Nonempty
        (FamilyFactorization
          ExtensionalReadout.Canary.routeReadout.observe
          (liftedAnchoredEquality.{0, uFibre} (false, false)))) := by
  rintro ⟨factorization⟩
  let reflected :=
    (factorization.fibreEquiv
      (left := (false, false)) (right := (false, true)) rfl).toFun
        (ULift.up (PLift.up (rfl : (false, false) = (false, false))))
  exact Bool.false_ne_true (congrArg Prod.snd reflected.down.down)

/-- Paired control: exact readout supports all dependent families, while a
lawful lossy split readout does not. -/
theorem universal_descent_boundary :
    AllFamiliesDescend.{0, 0, uFibre} identityReadout ∧
      Not
        (AllFamiliesDescend.{0, 0, uFibre}
          ExtensionalReadout.Canary.routeReadout) :=
  ⟨identityReadout_allFamiliesDescend,
    routeReadout_not_allFamiliesDescend⟩

end Canary

#print axioms allFamiliesDescend_of_exact
#print axioms observe_injective_of_allFamiliesDescend
#print axioms exact_iff_allFamiliesDescend
#print axioms ordinaryIdentityComparison_exact_iff_readout_exact
#print axioms allFamiliesDescend_iff_ordinaryIdentityComparison_exact
#print axioms Canary.routeReadout_not_allFamiliesDescend
#print axioms Canary.universal_descent_boundary

end Mettapedia.TypeTheory.UniversalDependentFamilyDescent
