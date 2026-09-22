import Mettapedia.PLN.WorldModel.WMCalculusNativeSpace
import Mettapedia.Languages.MeTTa.HE.SpaceAlgebra

/-!
# MeTTa storage algebra and world-model observation

The existing MeTTa `SpaceAlgebra` fixes a storage/query signature with
separate removal laws. The multiplicity-space world-model reading gives its
additive observation of union. This module connects the two interfaces on
the same concrete carrier: storage addition is WM revision by a singleton,
storage observational equality is WM behavioral agreement, and exact
lookup satisfies the storage/query coherence law.

Counted removal is deliberately not a WM revision by a fixed additive
delta. The WM calculus therefore interprets the additive observation layer,
not every operation of the storage API.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMMeTTaSpaceAlgebra

open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.PLN.WorldModel.WMCalculusNativeSpace

variable {Atom : Type} [DecidableEq Atom]

/-- One occurrence of an atom as a multiplicity space. -/
def singletonSpace (atom : Atom) : MSpace Atom :=
  fun other => if other = atom then 1 else 0

/-- Add one occurrence, retaining the WM-revision additive structure. -/
def addAtom (atom : Atom) (space : MSpace Atom) : MSpace Atom :=
  sUnion space (singletonSpace atom)

/-- Counted-bag removal clamps at zero and is not additive revision. -/
def removeAtom (atom : Atom) (space : MSpace Atom) : MSpace Atom :=
  fun other => if other = atom then space other - 1 else space other

/-- The existing storage signature instantiated by multiplicity spaces. -/
def multiplicitySpaceOps : StorageOps (MSpace Atom) Atom where
  empty := fun _ => 0
  add := addAtom
  remove := removeAtom
  multiplicity := fun space atom => space atom

/-- This storage instance satisfies the counted-bag, not set-removal,
variant of the established MeTTa space API. -/
theorem multiplicitySpaceOps_countedBag :
    CountedBagLaws (multiplicitySpaceOps (Atom := Atom)) where
  multiplicity_empty := by intro atom; rfl
  multiplicity_add_self := by
    intro atom space
    simp [multiplicitySpaceOps, addAtom, sUnion, singletonSpace]
  multiplicity_add_other := by
    intro atom other space different
    simp [multiplicitySpaceOps, addAtom, sUnion, singletonSpace, Ne.symm different]
  multiplicity_remove_self := by
    intro atom space
    simp [multiplicitySpaceOps, removeAtom]
  multiplicity_remove_other := by
    intro atom other space different
    simp [multiplicitySpaceOps, removeAtom, Ne.symm different]

/-- Exact lookup is a relational query, independent of result order. -/
def exactLookup : QueryOps (MSpace Atom) Atom Atom where
  QueryRel := fun space pattern result => result = pattern ∧ 0 < space pattern

/-- Exact lookup sees precisely the positive multiplicity recorded by the
storage layer. This is the existing API's anti-degeneracy coherence law. -/
theorem exactLookup_coherent :
    QueryCoherent (multiplicitySpaceOps (Atom := Atom))
      (exactLookup (Atom := Atom)) id where
  visible_iff_present := by
    intro space atom
    constructor
    · intro answer
      exact answer.2
    · intro present
      exact ⟨rfl, present⟩

/-- A finite, exact enumeration of the relational lookup. This certifies
content but intentionally does not prescribe a backend's broader query order. -/
def exactLookupEnumeration : QueryEnumeration (exactLookup (Atom := Atom)) where
  enumerate := fun space pattern =>
    if 0 < space pattern then [pattern] else []
  mem_enumerate_iff := by
    intro space pattern result
    by_cases present : 0 < space pattern
    · simp [exactLookup, present, eq_comm]
    · simp [exactLookup, present]

omit [DecidableEq Atom] in
/-- Positive exact lookup in the storage API is exactly a positive
singleton-candidate WM extraction. -/
theorem exactLookup_iff_wmPositive
    (world : String → MSpace Atom) (query : String → List Atom)
    (space : MSpace Atom) (atom : Atom) :
    (exactLookup (Atom := Atom)).QueryRel space atom atom ↔
      0 < (additiveReading (Ev := ℕ) world query).extract space [atom] := by
  change (atom = atom ∧ 0 < space atom) ↔ 0 < weightedAnswers space [atom]
  simp [weightedAnswers]

/-- Storage/query coherence therefore makes every addition visible to the
WM observer. The proof uses the existing SpaceAlgebra law, not an unrelated
counting argument. -/
theorem wm_extract_add_positive
    (world : String → MSpace Atom) (query : String → List Atom)
    (space : MSpace Atom) (atom : Atom) :
    0 < (additiveReading (Ev := ℕ) world query).extract (addAtom atom space) [atom] := by
  apply (exactLookup_iff_wmPositive world query (addAtom atom space) atom).mp
  exact query_sees_added
    (multiplicitySpaceOps_countedBag (Atom := Atom)).toStorageLaws
    (exactLookup_coherent (Atom := Atom)) atom space

/-- Storage addition is WM revision by one singleton state, not a new
unrelated space operation. -/
theorem addAtom_eq_wmRevise
    (world : String → MSpace Atom) (query : String → List Atom)
    (atom : Atom) (space : MSpace Atom) :
    addAtom atom space =
      (additiveReading (Ev := ℕ) world query).revise space (singletonSpace atom) := by
  rfl

/-- The storage API's observational equality is exactly WM behavioral
agreement when the WM reading admits every singleton candidate query. -/
theorem storageObsEq_iff_wmAgree
    (world : String → MSpace Atom) (query : String → List Atom)
    (first second : MSpace Atom) :
    (multiplicitySpaceOps (Atom := Atom)).ObsEq first second ↔
      (additiveReading (Ev := ℕ) world query).Agree .state first second := by
  rw [spaceAgree_iff_eq]
  constructor
  · intro same
    funext atom
    exact same atom
  · intro same
    subst second
    intro atom
    rfl

/-- There is no fixed additive WM state whose revision implements counted
removal: removing a present atom decreases its multiplicity. -/
theorem remove_not_fixed_wmRevision :
    ¬ ∃ delta : MSpace Unit,
      ∀ space : MSpace Unit,
        removeAtom () space = sUnion space delta := by
  rintro ⟨delta, always⟩
  have atOne := congrArg (fun space : MSpace Unit => space ())
    (always (singletonSpace ()))
  simp [removeAtom, singletonSpace, sUnion] at atOne
  omega

end Mettapedia.Logic.Bridges.WMMeTTaSpaceAlgebra
