import Mettapedia.OSLF.Framework.WMCalculusNativeObservationalEquality

/-!
# What behavioral equality can transport dependently

Behavioral agreement is equality on the observational quotient, so it
transports every family indexed by that quotient. Conversely, transport of
every such family already forces behavioral agreement. It does not transport
arbitrary families indexed by raw states when distinct states have the same
observations. This is a precise dependent-family boundary for the native WM
equality predicate, not an authored identity eliminator for Prime.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusNativeObservationalEquality
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding

/-- Transport a dependent family indexed by the observational quotient
along agreement of raw WM states. -/
def transportQuotientFamily {State Query V : Type}
    (R : WMReading State Query V) (P : ObsState R → Type)
    {first second : State} (agree : R.Agree .state first second) :
    P (classOf R first) → P (classOf R second) :=
  cast (congrArg P ((classOf_eq_iff_agree R first second).2 agree))

/-- Agreement is exactly Leibniz transport for all dependent families over
the observable state quotient. The converse tests the equality family, so
this is not merely a restatement of one selected readout. -/
theorem agree_iff_all_quotient_families_transport
    {State Query V : Type} (R : WMReading State Query V)
    (first second : State) :
    R.Agree .state first second ↔
      Nonempty (∀ P : ObsState R → Type,
        P (classOf R first) → P (classOf R second)) := by
  constructor
  · intro agree
    exact ⟨fun P value => transportQuotientFamily R P agree value⟩
  · rintro ⟨transports⟩
    let P : ObsState R → Type :=
      fun state => { witness : Unit // classOf R first = state }
    have atFirst : P (classOf R first) := ⟨(), rfl⟩
    have atSecond := transports P atFirst
    exact (classOf_eq_iff_agree R first second).1 atSecond.property

/-- Membership in the native behavioral-equality subfunctor has exactly
the dependent transport meaning, at every constructor stage. -/
theorem behavioralEquality_obj_iff_quotientFamilyTransport
    {State Query V : Type} (R : WMReading State Query V)
    (stage : Opposite (ConstructorObj
      (Mettapedia.OSLF.Framework.WMCalculusContextClosure.wmExtVertexLanguageDefWithCong
        Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal)))
    (pair : State × State) :
    pair ∈ (behavioralEquality R).obj stage ↔
      Nonempty (∀ P : ObsState R → Type,
        P (classOf R pair.1) → P (classOf R pair.2)) := by
  exact agree_iff_all_quotient_families_transport R pair.1 pair.2

/-- Contextual WM computation preserves transport for every observable
dependent family, because it preserves the observational quotient class. -/
def contextualSteps_transport_quotient_families
    {State Query V : Type} (R : WMReading State Query V)
    (laws : R.CoreLaws) {first second : WMTerm .state}
    (steps : WMContextStepStar first second) :
    ∀ P : ObsState R → Type,
      P (classOf R (R.denote first)) →
        P (classOf R (R.denote second)) :=
  fun P value => transportQuotientFamily R P
    (laws.agree_of_contextStepStar steps) value

/-- A family over all raw states can be transported along every map from
`first` to `second` exactly when those states are literally equal. -/
theorem all_raw_families_transport_iff_eq {State : Type}
    (first second : State) :
    Nonempty (∀ P : State → Type, P first → P second) ↔
      first = second := by
  constructor
  · rintro ⟨transports⟩
    let P : State → Type := fun state => { witness : Unit // first = state }
    have atFirst : P first := ⟨(), rfl⟩
    exact (transports P atFirst).property
  · rintro rfl
    exact ⟨fun _ value => value⟩

/-- If a model hides a raw state distinction, behavioral agreement cannot
justify unrestricted dependent transport over raw-state families. -/
theorem distinct_agree_transport_boundary {State Query V : Type}
    (R : WMReading State Query V) {first second : State}
    (distinct : first ≠ second) (agree : R.Agree .state first second) :
    Nonempty (∀ P : ObsState R → Type,
      P (classOf R first) → P (classOf R second)) ∧
      ¬ Nonempty (∀ P : State → Type, P first → P second) := by
  refine ⟨(agree_iff_all_quotient_families_transport R first second).1 agree, ?_⟩
  intro rawTransport
  exact distinct ((all_raw_families_transport_iff_eq first second).1 rawTransport)

end Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport
