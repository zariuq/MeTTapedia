import Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown
import Mettapedia.GSLT.LanguageDef.GSLTILObservationSelection
import Mettapedia.GSLT.LanguageDef.GSLTILObserverRelativeControl

/-!
# GSLT-IL bridge for observer-relative transformation capabilities

The generic observer-relative transformation laws specialize to authored
GSLT-IL in two independent places.

First, an elaboration profile is exactly a proof-relevant alternative family:
surface commands index the questions, internal patterns are the worlds, and
the authored acceptance relation supplies the fibre.  The generic coverage
and observer-invariance criterion therefore agrees with the existing
GSLT-IL observational-selection criterion without making elaboration
functional.

Second, a represented operational route transports complete event histories
and accounted removal ledgers.  Mapping a source transformation to the target
does not manufacture pruning authority: it consumes the source admission and
preserves the exact mapped removal multiset.

Together these bridges place elaboration selection, operational translation,
activation, and pruning under one observer-relative law while retaining their
distinct capability types.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.ObserverTransformationBridge

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection
open Mettapedia.GSLT.LanguageDef.GSLTIL.ObservationSelection
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uView

/-! ## Authored elaboration profiles are alternative families -/

/-- Forget only the GSLT-IL-specific field names.  The authored acceptance
relation itself is retained unchanged. -/
def profileAlternativeFamily {program : Program}
    (profile : Profile program) :
    AlternativeFamily profile.Command Pattern where
  accepts := profile.Accepts

@[simp] theorem profileAlternativeFamily_accepts
    {program : Program} (profile : Profile program)
    (command : profile.Command) (internal : Pattern) :
    (profileAlternativeFamily profile).accepts command internal =
      profile.Accepts command internal :=
  rfl

/-- GSLT-IL coverage is definitionally the generic fibre-coverage law. -/
theorem profileAlternativeFamily_covered_iff
    {program : Program} (profile : Profile program) :
    (profileAlternativeFamily profile).Covered <-> profile.Covered :=
  Iff.rfl

/-- GSLT-IL observation invariance is definitionally the generic
observer-fibre invariance law. -/
theorem profileAlternativeFamily_invariant_iff
    {program : Program} (profile : Profile program)
    {View : Type uView} (observer : Observer Pattern View) :
    (profileAlternativeFamily profile).ObserverInvariant observer <->
      ObservationInvariant profile observer :=
  Iff.rfl

/-- An existing authored observational selection supplies the generic
resolution capability without discarding any unselected elaboration world. -/
def toGenericResolution {program : Program} {profile : Profile program}
    {View : Type uView} {observer : Observer Pattern View}
    (selection : ObservationalSelection profile observer) :
    (profileAlternativeFamily profile).ObservationalResolution observer where
  select := selection.select
  selected := selection.selected
  observes := selection.observes

/-- A generic resolution over the unmodified authored acceptance family is
already a sound GSLT-IL observational selection. -/
def ofGenericResolution {program : Program} {profile : Profile program}
    {View : Type uView} {observer : Observer Pattern View}
    (resolution :
      (profileAlternativeFamily profile).ObservationalResolution observer) :
    ObservationalSelection profile observer where
  select := resolution.select
  selected := resolution.selected
  observes := resolution.observes

/-- The generic theorem and the authored GSLT-IL theorem classify exactly
the same admissible selections. -/
theorem generic_resolution_nonempty_iff_selection_nonempty
    {program : Program} (profile : Profile program)
    {View : Type uView} (observer : Observer Pattern View) :
    Nonempty
        ((profileAlternativeFamily profile).ObservationalResolution observer) <->
      Nonempty (ObservationalSelection profile observer) := by
  constructor
  · rintro ⟨resolution⟩
    exact ⟨ofGenericResolution resolution⟩
  · rintro ⟨selection⟩
    exact ⟨toGenericResolution selection⟩

/-- Re-derive the GSLT-IL selection boundary through the common capability
theorem.  This is a bridge between independently named presentations, not a
new selection policy. -/
theorem observationalSelection_iff_covered_and_invariant_via_generic
    {program : Program} (profile : Profile program)
    {View : Type uView} (observer : Observer Pattern View) :
    Nonempty (ObservationalSelection profile observer) <->
      profile.Covered /\ ObservationInvariant profile observer := by
  rw [← generic_resolution_nonempty_iff_selection_nonempty profile observer]
  exact
    AlternativeFamily.ObservationalResolution.nonempty_iff_covered_and_invariant
      (profileAlternativeFamily profile) observer

/-! ## Positive and negative controls use the same authored ambiguity -/

/-- The occurrence-ambiguous GSLT-IL profile has a generic resolution at the
declared constant observation. -/
def ambiguityGenericCoarseResolution :
    (profileAlternativeFamily AmbiguityCanary.profile).ObservationalResolution
      constantPatternObserver :=
  toGenericResolution
    (ObservationalSelection.atConstant AmbiguityCanary.chooseA)

/-- The same accepted worlds have no generic resolution at full internal
pattern observation. -/
theorem noAmbiguityGenericIdentityResolution :
    Not (Nonempty
      ((profileAlternativeFamily AmbiguityCanary.profile).ObservationalResolution
        (Observer.identity Pattern))) := by
  intro resolution
  have selection : Nonempty
      (ObservationalSelection AmbiguityCanary.profile
        (Observer.identity Pattern)) :=
    ⟨ofGenericResolution resolution.some⟩
  exact AmbiguityCanary.noExactSelection
    ((nonempty_identity_iff_exact AmbiguityCanary.profile).mp selection)

#print axioms profileAlternativeFamily_covered_iff
#print axioms profileAlternativeFamily_invariant_iff
#print axioms generic_resolution_nonempty_iff_selection_nonempty
#print axioms observationalSelection_iff_covered_and_invariant_via_generic
#print axioms noAmbiguityGenericIdentityResolution

end Mettapedia.GSLT.LanguageDef.GSLTIL.ObserverTransformationBridge

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObservationTransport
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

universe uTerm uIdentity uGuard uView uScore uReceipt

namespace RepresentedOperationalRoute

/-- Event-history compilation along a represented operational route is a
representation map preserving precisely the pulled-back target observation. -/
def eventHistoryRepresentation {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score) :
    ObserverPreservingMap (List source.LabeledStep)
      (List target.LabeledStep) View
      (route.pullbackControl targetDiscipline control).contract.observer
      control.contract.observer where
  transform := fun events =>
    events.map (mapEvent route.toOperationalTranslation)
  preserves := by intro events; rfl

@[simp] theorem eventHistoryRepresentation_transform
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    (events : List source.LabeledStep) :
    (route.eventHistoryRepresentation targetDiscipline control).transform
        events =
      events.map (mapEvent route.toOperationalTranslation) :=
  rfl

/-- Transport an already admitted, fully accounted source transformation.
The target receives the mapped live occurrences and mapped removal ledger;
the route itself supplies no additional pruning authority. -/
def mapAccountedTransformation
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (route.pullbackControl targetDiscipline control) Receipt) :
    AccountedTransformation control Receipt :=
  AccountedTransformation.ofPruning
    (route.mapAdmittedPruning targetDiscipline control
      transformation.toAdmittedPruning)

@[simp] theorem mapAccountedTransformation_source
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (route.pullbackControl targetDiscipline control) Receipt) :
    (route.mapAccountedTransformation targetDiscipline control
      transformation).source =
      transformation.source.map (mapEvent route.toOperationalTranslation) :=
  rfl

@[simp] theorem mapAccountedTransformation_target
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (route.pullbackControl targetDiscipline control) Receipt) :
    (route.mapAccountedTransformation targetDiscipline control
      transformation).target =
      transformation.target.map (mapEvent route.toOperationalTranslation) :=
  rfl

@[simp] theorem mapAccountedTransformation_removed
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (route.pullbackControl targetDiscipline control) Receipt) :
    (route.mapAccountedTransformation targetDiscipline control
      transformation).removed =
      transformation.removed.map (mapEvent route.toOperationalTranslation) :=
  rfl

/-- Mapped route transformations still satisfy exact no-silent-loss
accounting at the target event type. -/
theorem mapAccountedTransformation_no_silent_loss
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (route.pullbackControl targetDiscipline control) Receipt) :
    ((route.mapAccountedTransformation targetDiscipline control
        transformation).source :
          Multiset (route.targetCollectedArchitecture targetDiscipline).Event) =
      ((route.mapAccountedTransformation targetDiscipline control
          transformation).target :
            Multiset (route.targetCollectedArchitecture targetDiscipline).Event) +
        (route.mapAccountedTransformation targetDiscipline control
          transformation).removed :=
  (route.mapAccountedTransformation targetDiscipline control transformation
    ).no_silent_occurrence_loss

#print axioms eventHistoryRepresentation
#print axioms mapAccountedTransformation
#print axioms mapAccountedTransformation_removed
#print axioms mapAccountedTransformation_no_silent_loss

end RepresentedOperationalRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
