import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mettapedia.GSLT.LanguageDef.EffectiveSection
import Mettapedia.OSLF.MeTTaIL.CollectionCode

/-!
# The bag normal form is effective

The normal form of `BagNormalForm` rewrites a pattern from the leaves up: the
components of every bag first, then the bag itself, by splicing nested bags,
dropping units, sorting the components by code, and removing an empty or
singleton wrapper.  Each of these operations on a bag is a primitive
recursive operation on the code of the bag, so the normal form is tracked by
a primitive recursive function on codes (`normalFormCode`).

Consequently the canonical section of every bag theory is effective: a
computable function on term codes tracks it
(`bagCanonicalSection_effective`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-! ## The normal form as a bottom-up rewriting -/

/-- Normalize a closed bag at the root; leave every other pattern as it is. -/
def normalizeRoot (unit : Option String) : Pattern → Pattern
  | .collection .hashBag elements none => normalizeBag unit elements
  | pattern => pattern

@[simp] theorem normalizeRoot_bag (unit : Option String) (elements : List Pattern) :
    normalizeRoot unit (.collection .hashBag elements none) = normalizeBag unit elements := rfl

/-- A pattern that is not a closed bag is left as it is. -/
theorem normalizeRoot_of_not_bag (unit : Option String) {pattern : Pattern}
    (notBag : ¬ IsBagNode pattern) : normalizeRoot unit pattern = pattern := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> first
        | rfl
        | exact absurd ⟨elements, rfl⟩ notBag
  | _ => rfl

/-- **The normal form rewrites from the leaves up**, normalizing a bag once
its components are normal. -/
theorem normalForm_eq_bottomUp (unit : Option String) (pattern : Pattern) :
    normalForm unit pattern = pattern.bottomUp (normalizeRoot unit) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly label arguments recurse =>
      simp only [normalForm, normalFormList_eq_map, Pattern.bottomUp,
        Pattern.bottomUpList_eq_map]
      rw [List.map_congr_left recurse]
      rfl
  | hlambda binder body recurse =>
      simp only [normalForm, Pattern.bottomUp, recurse]
      rfl
  | hmultiLambda arity binders body recurse =>
      simp only [normalForm, Pattern.bottomUp, recurse]
      rfl
  | hsubst body replacement recurseBody recurseReplacement =>
      simp only [normalForm, Pattern.bottomUp, recurseBody, recurseReplacement]
      rfl
  | hcollection kind elements rest recurse =>
      simp only [normalForm, normalFormList_eq_map, Pattern.bottomUp,
        Pattern.bottomUpList_eq_map]
      rw [List.map_congr_left recurse]
      cases kind <;> cases rest <;> simp [normalizeRoot]

/-! ## The operation at a bag, on codes -/

/-- The code of the unit of a bag, when it has one. -/
def unitCode (unit : Option String) : Option ℕ :=
  unit.map fun name => patternCode (.apply name [])

/-- Normalize, on codes, a bag whose components are already normal. -/
def normalizeBagCode : Option ℕ → List ℕ → ℕ
  | none, components =>
      closedCollectionCode (collectionCode .hashBag) (components.insertionSort (· ≤ ·))
  | some unit, components => normalizeCollectionCode (collectionCode .hashBag) unit components

theorem normalizeBagCode_map (unit : Option String) (elements : List Pattern) :
    normalizeBagCode (unitCode unit) (elements.map patternCode) =
      patternCode (normalizeBag unit elements) := by
  cases unit with
  | none =>
      rw [normalizeBag, patternCode_closedCollection, map_sortPatterns]
      rfl
  | some name =>
      exact normalizeCollectionCode_map (kind := .hashBag) (splice := splice)
        (collapse := collapse name) splice_bag (fun _ notBag => splice_of_not_bag notBag) rfl
        (fun _ => rfl) (fun _ _ _ => rfl) elements

/-- The root operation on codes: normalize a closed bag, leave every other
code as it is. -/
def normalizeRootCode (unit : Option ℕ) (code : ℕ) : ℕ :=
  if IsClosedCollectionCode (collectionCode .hashBag) code then
    normalizeBagCode unit (collectionComponents code)
  else code

/-- **The root operation is tracked on codes.** -/
theorem normalizeRootCode_patternCode (unit : Option String) (pattern : Pattern) :
    normalizeRootCode (unitCode unit) (patternCode pattern) =
      patternCode (normalizeRoot unit pattern) := by
  by_cases bag : IsBagNode pattern
  · obtain ⟨elements, rfl⟩ := bag
    rw [normalizeRootCode,
      if_pos ((isClosedCollectionCode_patternCode .hashBag _).mpr ⟨elements, rfl⟩),
      patternCode_closedCollection, collectionComponents_closedCollectionCode,
      normalizeBagCode_map, normalizeRoot_bag]
  · rw [normalizeRootCode,
      if_neg (mt (isClosedCollectionCode_patternCode .hashBag pattern).mp bag),
      normalizeRoot_of_not_bag unit bag]

theorem normalizeBagCode_primrec (unit : Option ℕ) : Primrec (normalizeBagCode unit) := by
  cases unit with
  | none => exact (closedCollectionCode_primrec _).comp sortCodes_primrec
  | some unit => exact normalizeCollectionCode_primrec _ unit

theorem normalizeRootCode_primrec (unit : Option ℕ) : Primrec (normalizeRootCode unit) :=
  Primrec.ite (isClosedCollectionCode_primrecPred _)
    ((normalizeBagCode_primrec unit).comp collectionComponents_primrec) Primrec.id

/-! ## The normal form on codes -/

/-- The function on codes that tracks the normal form. -/
def normalFormCode (unit : Option String) : ℕ → ℕ :=
  bottomUpCode (normalizeRootCode (unitCode unit))

/-- **The normal form is primitive recursive on codes.** -/
theorem normalFormCode_primrec (unit : Option String) : Primrec (normalFormCode unit) :=
  bottomUpCode_primrec (normalizeRootCode_primrec (unitCode unit))

/-- **The function on codes tracks the normal form.** -/
theorem normalFormCode_patternCode (unit : Option String) (pattern : Pattern) :
    normalFormCode unit (patternCode pattern) = patternCode (normalForm unit pattern) := by
  rw [normalForm_eq_bottomUp]
  exact bottomUpCode_patternCode (normalizeRootCode_patternCode unit) pattern

/-! ## The section -/

/-- **The canonical section of a bag theory is effective**: the normal form
on codes is a computable function that tracks it. -/
theorem bagCanonicalSection_effective (theory : IGSLT) {bag : GrammarRule}
    {unit : Option String}
    (laws : BagTheory theory.presentation.presentation.language bag unit) :
    (bagCanonicalSection theory laws).Effective :=
  ⟨normalFormCode unit, (normalFormCode_primrec unit).to_comp,
    fun term => (normalFormCode_patternCode unit term.1).symm⟩

end Mettapedia.GSLT.LanguageDef.BagNormalForm
