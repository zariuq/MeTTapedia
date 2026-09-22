import Mettapedia.PLN.WorldModel.WMCalculusIndexedBindingSpace
import Mettapedia.Languages.MeTTa.HE.SpaceAlgebra

/-!
# A finite-support matcher backend for the MeTTa space algebra

The finite-support WM binding space also implements the existing MeTTa
storage/query signature. Storage has counted-bag add/remove laws; its
relational exact lookup is coherent with actual matcher-produced binding
counts. Thus the storage API and WM reading share one concrete state carrier
and one notion of observable multiplicity. Runtime indexing and dialect
scoping are separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMIndexedBindingSpaceAlgebra

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.PLN.WorldModel.WMCalculusNativeBindingSpace
open Mettapedia.PLN.WorldModel.WMCalculusIndexedBindingSpace

/-- Add one occurrence; counted removal subtracts one occurrence and clamps
at zero. -/
noncomputable def indexedStorageOps :
    StorageOps FinitePatternSpace Pattern where
  empty := 0
  add := fun atom space => space + Finsupp.single atom 1
  remove := fun atom space => space - Finsupp.single atom 1
  multiplicity := fun space atom => space atom

/-- The concrete finite-support implementation obeys the counted-bag
variant of the common MeTTa storage API. -/
theorem indexedStorageOps_countedBag : CountedBagLaws indexedStorageOps where
  multiplicity_empty := by
    intro atom
    rfl
  multiplicity_add_self := by
    intro atom space
    simp [indexedStorageOps]
  multiplicity_add_other := by
    intro atom other space different
    simp [indexedStorageOps, Ne.symm different]
  multiplicity_remove_self := by
    intro atom space
    simp [indexedStorageOps, Finsupp.tsub_apply]
  multiplicity_remove_other := by
    intro atom other space different
    simp [indexedStorageOps, Finsupp.tsub_apply, Ne.symm different]

/-- Relational exact lookup returns the binding produced by the MeTTaIL
variable matcher precisely when that binding has positive count. -/
def indexedBindingLookup :
    QueryOps FinitePatternSpace Pattern Bindings where
  QueryRel := fun space atom result =>
    result = [("x", atom)] ∧
      0 < indexedBindingAnswers space (.fvar "x") result

/-- The actual matcher-backed query layer sees exactly the multiplicity
recorded by storage. Additions cannot be invisible to this query. -/
theorem indexedBindingLookup_coherent :
    QueryCoherent indexedStorageOps indexedBindingLookup
      (fun atom => [("x", atom)]) where
  visible_iff_present := by
    intro space atom
    change ([("x", atom)] = [("x", atom)] ∧
      0 < indexedBindingAnswers space (.fvar "x") [("x", atom)]) ↔
        0 < space atom
    simp only [true_and, variable_binding_recovers_multiplicity]

/-- A deterministic exact-lookup readout of the relational query. The
broader matcher result ordering remains a backend-specific concern. -/
noncomputable def indexedBindingLookupEnumeration :
    QueryEnumeration indexedBindingLookup where
  enumerate := fun space atom =>
    if 0 < space atom then [[("x", atom)]] else []
  mem_enumerate_iff := by
    intro space atom result
    constructor
    · intro member
      by_cases present : 0 < space atom
      · have equal : result = [("x", atom)] := by
          simpa [present] using member
        subst result
        exact ⟨rfl, by simpa only [variable_binding_recovers_multiplicity] using present⟩
      · simp [present] at member
    · rintro ⟨rfl, positive⟩
      have present : 0 < space atom := by
        simpa only [variable_binding_recovers_multiplicity] using positive
      simp [present]

/-- Storage addition is exactly revision by a singleton source in the
finite-support WM reading. -/
theorem indexedAdd_eq_wmRevise
    (world : String → FinitePatternSpace) (query : String → Pattern)
    (space : FinitePatternSpace) (atom : Pattern) :
    indexedStorageOps.add atom space =
      (additiveReading (Ev := BindingBag) world query).revise
        space (Finsupp.single atom 1) :=
  rfl

/-- Storage observational equality is exactly WM agreement for the real
matcher-valued reading; both separate finite-support multiplicities. -/
theorem indexedStorageObsEq_iff_wmAgree
    (world : String → FinitePatternSpace) (query : String → Pattern)
    (first second : FinitePatternSpace) :
    indexedStorageOps.ObsEq first second ↔
      (additiveReading (Ev := BindingBag) world query).Agree
        .state first second := by
  rw [indexedSpaceAgree_iff_eq]
  constructor
  · intro same
    ext atom
    exact same atom
  · intro equal
    subst second
    intro atom
    rfl

end Mettapedia.Logic.Bridges.WMIndexedBindingSpaceAlgebra
