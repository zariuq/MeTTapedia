import Mettapedia.GSLT.Core.PolicyFamilyOperationClosure
import Mettapedia.TypeTheory.DependentFamilyDescentNaturality
import Mettapedia.TypeTheory.JointObservationDependentDescent

/-!
# Operation-stable descent of admitted policy families

A dependent consumer is admitted here by actual factorization data through
the requested policy vector. An operation-reindex witness supplies the
commuting observation square, so pulling back that particular consumer
retains its factorization. Neither operation closure nor a lossy readout
entails descent of every dependent family.

The same construction works on the compatible observational quotient and
on any supplied executable readout. No representative is selected by these
constructions. The comparison with joint observations reuses the existing
heterogeneous observation-family interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.PolicyFamily

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilyDescentNaturality
open Mettapedia.TypeTheory.JointObservationDependentDescent

universe uSource uMiddle uTarget uSourcePolicy uMiddlePolicy uTargetPolicy
  uSourceResult uMiddleResult uTargetResult uReadout uFibre

variable {Source : Type uSource} {Middle : Type uMiddle} {Target : Type uTarget}

/-- Regard the same policy coordinates as a joint observation family. -/
def observationFamily
    (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source) :
    ObservationFamily Source where
  Index := family.Policy
  Target := family.Result
  observe := family.decide

@[simp] theorem observationFamily_joint
    (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source) :
    family.observationFamily.joint = family.vector := rfl

/-- An executable readout carries every dependent consumer already admitted
to its policy vector. This does not admit a new consumer by fiat. -/
def ReadoutRealization.factorization
    {family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source}
    {Readout : Type uReadout} {readout : Source -> Readout}
    (realization : family.ReadoutRealization readout)
    {consumer : Source -> Type uFibre}
    (admitted : FamilyFactorization family.vector consumer) :
    FamilyFactorization readout consumer :=
  Descent.reindexAlongSquare admitted id readout
    (fun observed policy => realization.run policy observed)
    (fun state => funext fun policy => (realization.agrees policy state).symm)

/-- Admitted vector consumers also descend to compatible policy classes. -/
def factorizationOnClasses
    {family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source}
    {consumer : Source -> Type uFibre}
    (admitted : FamilyFactorization family.vector consumer) :
    FamilyFactorization family.toObservationClass consumer :=
  family.observationClassRealization.factorization admitted

namespace OperationReindex

variable
  {source : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source}
  {middle : PolicyFamily.{uMiddle, uMiddlePolicy, uMiddleResult} Middle}
  {target : PolicyFamily.{uTarget, uTargetPolicy, uTargetResult} Target}
  {operation : Source -> Target}

/-- The derived vector square reindexes a selected dependent consumer. -/
def reindexFactorization
    (witness : OperationReindex source target operation)
    {consumer : Target -> Type uFibre}
    (admitted : FamilyFactorization target.vector consumer) :
    FamilyFactorization source.vector (fun state => consumer (operation state)) :=
  Descent.reindexAlongSquare admitted operation source.vector witness.vectorMap
    (fun state => (witness.vectorMap_vector state).symm)

/-- The quotient square gives the corresponding selected-family descent on
compatible classes, using the operation congruence derived from coordinates. -/
def reindexClassFactorization
    (witness : OperationReindex source target operation)
    {consumer : Target -> Type uFibre}
    (admitted : FamilyFactorization target.toObservationClass consumer) :
    FamilyFactorization source.toObservationClass
      (fun state => consumer (operation state)) :=
  Descent.reindexAlongSquare admitted operation source.toObservationClass
    witness.classMap (fun _ => rfl)

/-- The target family after reindexing is the pullback along the same
executable vector action. -/
theorem reindexFactorization_targetFamily
    (witness : OperationReindex source target operation)
    {consumer : Target -> Type uFibre}
    (admitted : FamilyFactorization target.vector consumer) :
    (witness.reindexFactorization admitted).targetFamily =
      admitted.targetFamily ∘ witness.vectorMap := rfl

/-- Identity operation leaves the admitted target family unchanged. -/
theorem reindexFactorization_id_targetFamily
    (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source)
    {consumer : Source -> Type uFibre}
    (admitted : FamilyFactorization family.vector consumer) :
    ((id family).reindexFactorization admitted).targetFamily =
      admitted.targetFamily := rfl

/-- Identity also preserves the actual fibre-identification equivalences. -/
theorem reindexFactorization_id
    (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source)
    {consumer : Source -> Type uFibre}
    (admitted : FamilyFactorization family.vector consumer) :
    (id family).reindexFactorization admitted = admitted := by
  cases admitted
  rfl

/-- Sequential and composite operations produce the same descended target
family, not only isomorphic fibres. -/
theorem reindexFactorization_comp_targetFamily
    {earlier : Source -> Middle} {later : Middle -> Target}
    (first : OperationReindex source middle earlier)
    (second : OperationReindex middle target later)
    {consumer : Target -> Type uFibre}
    (admitted : FamilyFactorization target.vector consumer) :
    ((first.comp second).reindexFactorization admitted).targetFamily =
      (first.reindexFactorization (second.reindexFactorization admitted)).targetFamily :=
  rfl

/-- Composite reindexing retains the same identification data as two
successive reindexings, including the forced dependent casts. -/
theorem reindexFactorization_comp
    {earlier : Source -> Middle} {later : Middle -> Target}
    (first : OperationReindex source middle earlier)
    (second : OperationReindex middle target later)
    {consumer : Target -> Type uFibre}
    (admitted : FamilyFactorization target.vector consumer) :
    (first.comp second).reindexFactorization admitted =
      first.reindexFactorization (second.reindexFactorization admitted) := by
  cases admitted with
  | mk targetFamily identify =>
      dsimp only [reindexFactorization, Descent.reindexAlongSquare]
      congr 1
      funext state
      apply Equiv.ext
      intro value
      change cast _ (identify (later (earlier state)) value) =
        cast _ (cast _ (identify (later (earlier state)) value))
      exact (cast_cast _ _ _).symm

end OperationReindex

#print axioms ReadoutRealization.factorization
#print axioms factorizationOnClasses
#print axioms OperationReindex.reindexFactorization
#print axioms OperationReindex.reindexClassFactorization
#print axioms OperationReindex.reindexFactorization_id_targetFamily
#print axioms OperationReindex.reindexFactorization_comp_targetFamily
#print axioms OperationReindex.reindexFactorization_id
#print axioms OperationReindex.reindexFactorization_comp

end Mettapedia.GSLT.Core.PolicyFamily
