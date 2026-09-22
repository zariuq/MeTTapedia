import Mettapedia.Logic.Bridges.WMMeTTaSpaceAlgebra
import Mettapedia.Logic.Bridges.WMIndexedBindingSpaceAlgebra
import Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport

/-!
# MeTTa space equality as dependent observational transport

The existing MeTTa storage API's multiplicity equality, the WM calculus's
behavioral equality, and transport over the observable quotient coincide for
both the abstract multiplicity space and the concrete finite-support matcher
space. These two readings have separating query vocabularies, so in these
particular backends the same relation also coincides with transport of every
family indexed by raw storage states. That last fact is not generic for world
models with hidden histories.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMSpaceDependentEquality

open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.PLN.WorldModel.WMCalculusNativeBindingSpace
open Mettapedia.PLN.WorldModel.WMCalculusIndexedBindingSpace
open Mettapedia.PLN.WorldModel.WMCalculusNativeSpace
open Mettapedia.Logic.Bridges.WMMeTTaSpaceAlgebra
open Mettapedia.Logic.Bridges.WMIndexedBindingSpaceAlgebra

/-- For the multiplicity-space reading, the storage API's observational
equality is exactly dependent transport over the WM quotient. -/
theorem multiplicityObsEq_iff_quotientFamilyTransport
    {Atom : Type} [DecidableEq Atom]
    (world : String → MSpace Atom) (query : String → List Atom)
    (first second : MSpace Atom) :
    (multiplicitySpaceOps (Atom := Atom)).ObsEq first second ↔
      Nonempty (∀ P : ObsState (additiveReading (Ev := ℕ) world query) → Type,
        P (classOf (additiveReading (Ev := ℕ) world query) first) →
          P (classOf (additiveReading (Ev := ℕ) world query) second)) :=
  (storageObsEq_iff_wmAgree world query first second).trans
    (agree_iff_all_quotient_families_transport _ first second)

/-- Singleton-candidate queries separate this concrete storage carrier, so
its observational equality even supports all raw-state dependent families. -/
theorem multiplicityObsEq_iff_rawFamilyTransport
    {Atom : Type} [DecidableEq Atom]
    (world : String → MSpace Atom) (query : String → List Atom)
    (first second : MSpace Atom) :
    (multiplicitySpaceOps (Atom := Atom)).ObsEq first second ↔
      Nonempty (∀ P : MSpace Atom → Type, P first → P second) := by
  exact ((storageObsEq_iff_wmAgree world query first second).trans
    (spaceAgree_iff_eq world query first second)).trans
    (all_raw_families_transport_iff_eq first second).symm

/-- The actual finite-support MeTTaIL matcher gives the same quotient-family
transport meaning to the storage API's multiplicity equality. -/
theorem indexedObsEq_iff_quotientFamilyTransport
    (world : String → FinitePatternSpace) (query : String → Pattern)
    (first second : FinitePatternSpace) :
    indexedStorageOps.ObsEq first second ↔
      Nonempty (∀ P : ObsState (additiveReading (Ev := BindingBag) world query) → Type,
        P (classOf (additiveReading (Ev := BindingBag) world query) first) →
          P (classOf (additiveReading (Ev := BindingBag) world query) second)) :=
  (indexedStorageObsEq_iff_wmAgree world query first second).trans
    (agree_iff_all_quotient_families_transport _ first second)

/-- Variable-pattern binding queries separate finite-support storage states;
raw-family transport is therefore valid for this backend, not by fiat for
every lawful WM reading. -/
theorem indexedObsEq_iff_rawFamilyTransport
    (world : String → FinitePatternSpace) (query : String → Pattern)
    (first second : FinitePatternSpace) :
    indexedStorageOps.ObsEq first second ↔
      Nonempty (∀ P : FinitePatternSpace → Type,
        P first → P second) := by
  exact ((indexedStorageObsEq_iff_wmAgree world query first second).trans
    (indexedSpaceAgree_iff_eq world query first second)).trans
    (all_raw_families_transport_iff_eq first second).symm

end Mettapedia.Logic.Bridges.WMSpaceDependentEquality
