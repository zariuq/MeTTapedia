import Mettapedia.Logic.AnytimeEvidence
import Mettapedia.Logic.WorldModel.OpenEnded

/-!
# Finite evidence for open-ended world properties

A property of an infinite world can be useful to a finite observer without
being determined by one uniform finite horizon.  The relevant distinction is
pointwise and directional:

* `FinitelyConfirmable` means that every positive world has some finite
  observation whose entire observational fibre is positive;
* `FinitelyRefutable` applies the same condition to the complement;
* `FinitelyDetermined` remains the stronger, uniform condition already used
  by the finite-horizon language.

These are the observation-theoretic forms of finite positive evidence,
finite negative evidence, and a fixed finite decision boundary.  A prefix
confirmation gives a monotone finite-stage certificate.  Cantor space then
supplies the sharp control: “some bit is true” is finitely confirmable and has
a complete positive certificate, but it is neither finitely refutable nor
determined by any fixed prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WorldModel.FiniteEvidence

open Mettapedia.Logic.AnytimeEvidence
open Mettapedia.Logic.WorldModel.OpenEnded

universe uWorld uSnapshot

/-- The observation at `stage` around `world` is already sufficient positive
evidence for `property`: every observationally indistinguishable world also
has the property. -/
def PrefixConfirms {World : Type uWorld}
    (observation : PrefixObservation.{uWorld, uSnapshot} World)
    (property : World → Prop) (world : World) (stage : Nat) : Prop :=
  ∀ other, observation.observe stage other = observation.observe stage world →
    property other

/-- Every positive world has a finite prefix which confirms the property.
The witnessing stage may depend on the world. -/
def FinitelyConfirmable {World : Type uWorld}
    (observation : PrefixObservation.{uWorld, uSnapshot} World)
    (property : World → Prop) : Prop :=
  ∀ world, property world → ∃ stage,
    PrefixConfirms observation property world stage

/-- Every negative world has a finite prefix which confirms the complement. -/
def FinitelyRefutable {World : Type uWorld}
    (observation : PrefixObservation.{uWorld, uSnapshot} World)
    (property : World → Prop) : Prop :=
  FinitelyConfirmable observation (fun world => ¬ property world)

/-- A confirming prefix remains confirming when the observer sees a later,
more informative prefix. -/
theorem prefixConfirms_mono {World : Type uWorld}
    {observation : PrefixObservation.{uWorld, uSnapshot} World}
    {property : World → Prop} {world : World}
    {earlier later : Nat} (bounded : earlier ≤ later)
    (confirms : PrefixConfirms observation property world earlier) :
    PrefixConfirms observation property world later := by
  intro other sameLater
  apply confirms other
  have restricted := congrArg (observation.restrict bounded) sameLater
  simpa only [observation.observe_restrict] using restricted

/-- For one selected world, prefix confirmation is monotone sound evidence
for the world's property. -/
def confirmationCertificate {World : Type uWorld}
    (observation : PrefixObservation.{uWorld, uSnapshot} World)
    (property : World → Prop) (world : World) :
    MonotoneCertificate (property world) where
  acceptsAt := PrefixConfirms observation property world
  monotone bounded confirms := prefixConfirms_mono bounded confirms
  sound confirms := confirms world rfl

/-- Finite confirmability is exactly positive limit-completeness of the
canonical prefix-confirmation certificate at every positive world. -/
theorem finitelyConfirmable_iff_confirmationCertificate_complete
    {World : Type uWorld}
    (observation : PrefixObservation.{uWorld, uSnapshot} World)
    (property : World → Prop) :
    FinitelyConfirmable observation property ↔
      ∀ world, property world →
        (confirmationCertificate observation property world).EventuallyComplete := by
  constructor
  · intro confirmable world holds _sameClaim
    exact confirmable world holds
  · intro complete world holds
    exact complete world holds holds

/-- Uniform finite determination supplies finite positive evidence. -/
theorem finitelyConfirmable_of_finitelyDetermined
    {World : Type uWorld}
    {observation : PrefixObservation.{uWorld, uSnapshot} World}
    {property : World → Prop}
    (determined : FinitelyDetermined observation property) :
    FinitelyConfirmable observation property := by
  obtain ⟨stage, localProperty, determines⟩ := determined
  intro world holds
  refine ⟨stage, ?_⟩
  intro other sameObservation
  apply (determines other).mpr
  have localHolds := (determines world).mp holds
  simpa only [sameObservation] using localHolds

/-- Uniform finite determination also supplies finite negative evidence. -/
theorem finitelyRefutable_of_finitelyDetermined
    {World : Type uWorld}
    {observation : PrefixObservation.{uWorld, uSnapshot} World}
    {property : World → Prop}
    (determined : FinitelyDetermined observation property) :
    FinitelyRefutable observation property := by
  obtain ⟨stage, localProperty, determines⟩ := determined
  intro world doesNotHold
  refine ⟨stage, ?_⟩
  intro other sameObservation holdsOther
  have localOther := (determines other).mp holdsOther
  have localWorld : localProperty (observation.observe stage world) := by
    simpa only [sameObservation] using localOther
  exact doesNotHold ((determines world).mpr localWorld)

/-! ## Cantor-space positive and negative controls -/

open Mettapedia.Computability

/-- Direct finite-witness evidence for the existential open-tail property. -/
def someBitTrueCertificate (world : CantorSpace) :
    MonotoneCertificate (someBitTrue world) where
  acceptsAt depth := ∃ coordinate, coordinate < depth ∧ world coordinate = true
  monotone := by
    intro earlier later bounded
    rintro ⟨coordinate, within, isTrue⟩
    exact ⟨coordinate, within.trans_le bounded, isTrue⟩
  sound := by
    intro _stage
    rintro ⟨coordinate, _within, isTrue⟩
    exact ⟨coordinate, isTrue⟩

/-- Every true existential-tail claim is found at a finite stage, although no
single stage works for all worlds. -/
theorem someBitTrueCertificate_eventuallyComplete (world : CantorSpace) :
    (someBitTrueCertificate world).EventuallyComplete := by
  rintro ⟨coordinate, isTrue⟩
  exact ⟨coordinate + 1, coordinate, Nat.lt_succ_self coordinate, isTrue⟩

/-- “Some bit is true” is finitely confirmable. -/
theorem someBitTrue_finitelyConfirmable :
    FinitelyConfirmable cantorPrefixObservation someBitTrue := by
  intro world
  rintro ⟨coordinate, isTrue⟩
  refine ⟨coordinate + 1, ?_⟩
  intro other samePrefix
  refine ⟨coordinate, ?_⟩
  have sameCoordinate := congrFun samePrefix
    (⟨coordinate, Nat.lt_succ_self coordinate⟩ : Fin (coordinate + 1))
  change other coordinate = world coordinate at sameCoordinate
  rw [sameCoordinate, isTrue]

/-- The all-false world has no finite prefix which refutes “some bit is
true”: a true bit can always appear just beyond the observed prefix. -/
theorem someBitTrue_not_finitelyRefutable :
    ¬ FinitelyRefutable cantorPrefixObservation someBitTrue := by
  intro refutable
  let allFalse : CantorSpace := fun _ => false
  have allFalseNegative : ¬ someBitTrue allFalse := by
    rintro ⟨coordinate, isTrue⟩
    simp [allFalse] at isTrue
  obtain ⟨stage, confirmsNegative⟩ :=
    refutable allFalse allFalseNegative
  let lateTrue : CantorSpace := fun coordinate => decide (coordinate = stage)
  have samePrefix :
      cantorPrefixObservation.observe stage lateTrue =
        cantorPrefixObservation.observe stage allFalse := by
    funext coordinate
    simp [cantorPrefixObservation, prefixProj, lateTrue, allFalse,
      Nat.ne_of_lt coordinate.isLt]
  have lateNegative := confirmsNegative lateTrue samePrefix
  apply lateNegative
  exact ⟨stage, by simp [lateTrue]⟩

/-- Complete positive finite evidence coexists with the absence of both a
fixed finite decision horizon and finite negative evidence.  This is the
formal “accelerate without amputating the open tail” classification. -/
theorem someBitTrue_openEnded_evidence_profile :
    FinitelyConfirmable cantorPrefixObservation someBitTrue ∧
      ¬ FinitelyRefutable cantorPrefixObservation someBitTrue ∧
      ¬ FinitelyDetermined cantorPrefixObservation someBitTrue :=
  ⟨someBitTrue_finitelyConfirmable,
    someBitTrue_not_finitelyRefutable,
    someBitTrue_not_finitelyDetermined⟩

/-- Fixed-coordinate predicates provide the contrasting two-sided finite
case. -/
theorem firstBitTrue_twoSided_finiteEvidence :
    FinitelyConfirmable cantorPrefixObservation firstBitTrue ∧
      FinitelyRefutable cantorPrefixObservation firstBitTrue :=
  ⟨finitelyConfirmable_of_finitelyDetermined
      firstBitTrue_finitelyDetermined,
    finitelyRefutable_of_finitelyDetermined
      firstBitTrue_finitelyDetermined⟩

/-! ## Audited theorem crowns -/

#print axioms prefixConfirms_mono
#print axioms finitelyConfirmable_iff_confirmationCertificate_complete
#print axioms finitelyConfirmable_of_finitelyDetermined
#print axioms finitelyRefutable_of_finitelyDetermined
#print axioms someBitTrueCertificate_eventuallyComplete
#print axioms someBitTrue_openEnded_evidence_profile
#print axioms firstBitTrue_twoSided_finiteEvidence

end Mettapedia.Logic.WorldModel.FiniteEvidence
