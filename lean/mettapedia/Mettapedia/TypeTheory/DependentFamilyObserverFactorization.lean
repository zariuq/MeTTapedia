import Mathlib.Logic.Equiv.Basic
import Mettapedia.TypeTheory.ExtensionalReadout

/-!
# Dependent families over extensional observations

An extensional readout may preserve every selected visible value while still
being too coarse to support a dependent family.  A family over the source
factors through an observation, up to fibrewise equivalence, when it is the
pullback of some family over the observation target.

For a split readout, such a factorization exists exactly when every source
fibre is equivalent to the fibre over its selected canonical representative.
In particular, every factorizing family is invariant up to equivalence inside
each observation fibre.  The negative criterion is useful for separating an
extensional companion from an intensional dependent layer: one pair of
observationally equal source points with non-equivalent fibres rules out the
factorization.

This is a type-level factorization statement.  It does not assert equality of
fibres, choose a type theory, or add descent coherence beyond the displayed
fibre equivalences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentFamilyObserverFactorization

open Mettapedia.TypeTheory.ExtensionalReadout

universe uSource uTarget uFibre uDependent

/-- A dependent family factors through an observation up to fibrewise
equivalence when it is equivalent to the pullback of a family on the target. -/
structure FamilyFactorization
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source -> Target) (family : Source -> Type uFibre) where
  targetFamily : Target -> Type uFibre
  identify : forall source, family source ≃ targetFamily (observe source)

namespace FamilyFactorization

variable {Source : Type uSource} {Target : Type uTarget}
variable {observe : Source -> Target} {family : Source -> Type uFibre}

/-- A family already defined on the observation target factors after
pullback, with identity fibre equivalences. -/
def pullback (observe : Source -> Target) (targetFamily : Target -> Type uFibre) :
    FamilyFactorization observe (fun source => targetFamily (observe source)) where
  targetFamily := targetFamily
  identify := fun _ => Equiv.refl _

/-- A constant family factors through every observation. -/
def constant (observe : Source -> Target) (Fibre : Type uFibre) :
    FamilyFactorization observe (fun _ => Fibre) where
  targetFamily := fun _ => Fibre
  identify := fun _ => Equiv.refl _

/-- A factorizing dependent family has equivalent fibres at every pair of
source points identified by the observation. -/
def fibreEquiv (factorization : FamilyFactorization observe family)
    {left right : Source} (sameObservation : observe left = observe right) :
    family left ≃ family right := by
  exact (factorization.identify left).trans
    ((Equiv.cast (congrArg factorization.targetFamily sameObservation)).trans
      (factorization.identify right).symm)

/-- A single observation fibre containing non-equivalent dependent fibres
prevents any type-level factorization through that observation. -/
theorem not_nonempty_of_nonEquivalent_fibres
    {left right : Source} (sameObservation : observe left = observe right)
    (notEquivalent : Not (Nonempty (family left ≃ family right))) :
    Not (Nonempty (FamilyFactorization observe family)) := by
  rintro ⟨factorization⟩
  exact notEquivalent ⟨factorization.fibreEquiv sameObservation⟩

/-! ## The exact split-readout criterion -/

variable {readout : SplitReadout Source Target}

/-- Equivalences from every source fibre to the fibre over its canonical
representative construct a family on the split-readout target. -/
def ofCanonicalFibreEquivalences
    (family : Source -> Type uFibre)
    (identify : forall source,
      family source ≃ family (readout.canonicalize source)) :
    FamilyFactorization readout.observe family where
  targetFamily := fun target => family (readout.representative target)
  identify := identify

/-- Every factorization through a split readout supplies equivalences to the
selected canonical fibres. -/
def canonicalFibreEquivalences
    (factorization : FamilyFactorization readout.observe family) :
    forall source, family source ≃ family (readout.canonicalize source) := by
  intro source
  let representative := readout.representative (readout.observe source)
  have representativeObservation :
      readout.observe representative = readout.observe source :=
    readout.observe_representative (readout.observe source)
  have representativeIdentification := factorization.identify representative
  rw [representativeObservation] at representativeIdentification
  exact (factorization.identify source).trans
    representativeIdentification.symm

/-- For a split readout, type-level factorization is exactly equivalence of
each source fibre with the fibre at its selected canonical representative. -/
theorem nonempty_iff_canonicalFibreEquivalences
    (readout : SplitReadout Source Target)
    (family : Source -> Type uFibre) :
    Nonempty (FamilyFactorization readout.observe family) ↔
      Nonempty (forall source,
        family source ≃ family (readout.canonicalize source)) := by
  constructor
  · rintro ⟨factorization⟩
    exact ⟨factorization.canonicalFibreEquivalences⟩
  · rintro ⟨identify⟩
    exact ⟨ofCanonicalFibreEquivalences family identify⟩

/-! ## Closure under dependent products and sums -/

/-- The observation induced on the total space of a factorizing family.  It
maps both the source point and its dependent value through the factorization. -/
def totalObservation
    (factorization : FamilyFactorization observe family) :
    (Sigma family) -> Sigma factorization.targetFamily
  | ⟨source, value⟩ =>
      ⟨observe source, factorization.identify source value⟩

/-- If a base family factors through an observer and a dependent second
family factors through the induced total-space observation, their dependent
sum factors through the original observer. -/
def dependentSigma
    {dependentFamily : Sigma family -> Type uDependent}
    (base : FamilyFactorization observe family)
    (dependent : FamilyFactorization base.totalObservation dependentFamily) :
    FamilyFactorization observe
      (fun source =>
        Sigma fun value : family source => dependentFamily ⟨source, value⟩) where
  targetFamily := fun target =>
    Sigma fun value : base.targetFamily target =>
      dependent.targetFamily ⟨target, value⟩
  identify := fun source =>
    Equiv.sigmaCongr (base.identify source)
      (fun value => dependent.identify ⟨source, value⟩)

/-- Under the same hypotheses, the dependent product also factors through
the original observer. -/
def dependentPi
    {dependentFamily : Sigma family -> Type uDependent}
    (base : FamilyFactorization observe family)
    (dependent : FamilyFactorization base.totalObservation dependentFamily) :
    FamilyFactorization observe
      (fun source =>
        forall value : family source, dependentFamily ⟨source, value⟩) where
  targetFamily := fun target =>
    forall value : base.targetFamily target,
      dependent.targetFamily ⟨target, value⟩
  identify := fun source =>
    Equiv.piCongr (base.identify source)
      (fun value => dependent.identify ⟨source, value⟩)

end FamilyFactorization

/-! ## Generic positive and negative controls -/

namespace Canary

/-- A deliberately coarse observation identifying two source points. -/
def coarseBool : Bool -> PUnit := fun _ => PUnit.unit

/-- Constant fibres are compatible with the coarse observation. -/
def constantFactors :
    FamilyFactorization coarseBool (fun _ => PUnit) :=
  FamilyFactorization.constant coarseBool PUnit

/-- A constant Boolean base family for the Pi/Sigma closure control. -/
def constantBoolFactors :
    FamilyFactorization coarseBool (fun _ => Bool) :=
  FamilyFactorization.constant coarseBool Bool

/-- A constant dependent second family over the induced total observation. -/
def constantDependentFactors :
    FamilyFactorization constantBoolFactors.totalObservation
      (fun _ => PUnit) :=
  FamilyFactorization.constant constantBoolFactors.totalObservation PUnit

/-- The closure constructions produce actual dependent-product and
dependent-sum factorizations, not only preservation propositions. -/
def dependentSigmaFactors :
    FamilyFactorization coarseBool
      (fun _source => Sigma fun _ : Bool => PUnit) :=
  constantBoolFactors.dependentSigma constantDependentFactors

def dependentPiFactors :
    FamilyFactorization coarseBool
      (fun _source => forall _ : Bool, PUnit) :=
  constantBoolFactors.dependentPi constantDependentFactors

/-- A genuinely varying family over the two source points. -/
def varying : Bool -> Type
  | false => PUnit
  | true => Bool

theorem unit_not_equiv_bool : Not (Nonempty (PUnit ≃ Bool)) := by
  rintro ⟨equivalence⟩
  have preimagesEqual :
      equivalence.symm false = equivalence.symm true :=
    Subsingleton.elim _ _
  exact Bool.false_ne_true
    (by simpa using congrArg equivalence preimagesEqual)

/-- The coarse observation cannot carry the varying family: its one fibre
would have to represent both a singleton and a two-element type. -/
theorem varying_does_not_factor :
    Not (Nonempty (FamilyFactorization coarseBool varying)) := by
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := false) (right := true) rfl unit_not_equiv_bool

/-- Paired control: one observation supports constant families without
thereby supporting every dependent family. -/
theorem constant_and_varying_boundary :
    Nonempty (FamilyFactorization coarseBool (fun _ => PUnit)) ∧
      Not (Nonempty (FamilyFactorization coarseBool varying)) :=
  ⟨⟨constantFactors⟩, varying_does_not_factor⟩

/-- Positive closure control: the same coarse observation supports the Pi
and Sigma families assembled from compatible component factorizations. -/
theorem dependentPiSigma_factorization_control :
    Nonempty
        (FamilyFactorization coarseBool
          (fun _source => Sigma fun _ : Bool => PUnit)) ∧
      Nonempty
        (FamilyFactorization coarseBool
          (fun _source => forall _ : Bool, PUnit)) :=
  ⟨⟨dependentSigmaFactors⟩, ⟨dependentPiFactors⟩⟩

end Canary

#print axioms FamilyFactorization.fibreEquiv
#print axioms FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
#print axioms FamilyFactorization.nonempty_iff_canonicalFibreEquivalences
#print axioms FamilyFactorization.dependentSigma
#print axioms FamilyFactorization.dependentPi
#print axioms Canary.unit_not_equiv_bool
#print axioms Canary.varying_does_not_factor
#print axioms Canary.constant_and_varying_boundary
#print axioms Canary.dependentPiSigma_factorization_control

end Mettapedia.TypeTheory.DependentFamilyObserverFactorization
