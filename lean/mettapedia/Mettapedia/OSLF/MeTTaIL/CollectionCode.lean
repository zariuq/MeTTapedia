import Mettapedia.OSLF.MeTTaIL.PatternCodeRecursion
import Mettapedia.OSLF.MeTTaIL.PatternCodeSort

/-!
# Normalizing a collection, on codes

A normalizer for an associative, commutative collection with a unit works on
a closed collection whose components are already normal: it splices nested
collections of the same kind, drops units, sorts the components by code, and
removes an empty or singleton wrapper.

This module gives each of these operations on the code of the collection, for
any kind of collection, and shows that each is primitive recursive.  The
operations on patterns are specified by their defining equations, so that the
same statements serve every normalizer of this shape.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Closed collections -/

/-- The code of the closed collection of a kind whose components have the
listed codes.  The kind is given by its code. -/
def closedCollectionCode (kind : ℕ) (components : List ℕ) : ℕ :=
  Nat.pair 6 (Nat.pair kind (Nat.pair (Encodable.encode components) (Nat.pair 0 0)))

/-- The code of a closed collection, from the codes of its components. -/
theorem patternCode_closedCollection (kind : CollType) (elements : List Pattern) :
    patternCode (.collection kind elements none) =
      closedCollectionCode (collectionCode kind) (elements.map patternCode) := by
  simp [patternCode, closedCollectionCode, optionStringCode, patternListCode_eq_encode]

/-- The number is shaped like the code of a closed collection of the kind. -/
def IsClosedCollectionCode (kind code : ℕ) : Prop :=
  code.unpair.1 = 6 ∧ code.unpair.2.unpair.1 = kind ∧
    code.unpair.2.unpair.2.unpair.2 = Nat.pair 0 0

instance (kind : ℕ) : DecidablePred (IsClosedCollectionCode kind) := fun code =>
  inferInstanceAs (Decidable (code.unpair.1 = 6 ∧ code.unpair.2.unpair.1 = kind ∧
    code.unpair.2.unpair.2.unpair.2 = Nat.pair 0 0))

/-- The code of a pattern has the shape of a closed collection of a kind
exactly when the pattern is one. -/
theorem isClosedCollectionCode_patternCode (kind : CollType) (pattern : Pattern) :
    IsClosedCollectionCode (collectionCode kind) (patternCode pattern) ↔
      ∃ elements, pattern = .collection kind elements none := by
  cases pattern with
  | collection actual elements rest =>
      cases rest with
      | none =>
          simp [IsClosedCollectionCode, patternCode, optionStringCode,
            collectionCode_injective.eq_iff, eq_comm]
      | some name =>
          simp [IsClosedCollectionCode, patternCode, optionStringCode, Nat.pair_eq_pair]
  | _ => simp [IsClosedCollectionCode, patternCode]

/-- The codes of the components of a closed collection, read off its code. -/
def collectionComponents (code : ℕ) : List ℕ :=
  Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2.unpair.1

@[simp] theorem collectionComponents_closedCollectionCode (kind : ℕ) (components : List ℕ) :
    collectionComponents (closedCollectionCode kind components) = components := by
  simp [collectionComponents, closedCollectionCode]

/-! ## The operations -/

/-- What a component contributes: the components of a closed collection of
the kind, or the component itself. -/
def spliceCode (kind code : ℕ) : List ℕ :=
  if IsClosedCollectionCode kind code then collectionComponents code else [code]

/-- The components of a collection: nested collections spliced, units
dropped. -/
def contentsCode (kind unit : ℕ) (components : List ℕ) : List ℕ :=
  (components.flatMap (spliceCode kind)).filter fun code => decide (code ≠ unit)

/-- Rebuild a collection without an empty or singleton wrapper. -/
def collapseCode (kind unit : ℕ) (components : List ℕ) : ℕ :=
  if components.length = 0 then unit
  else if components.length = 1 then components.headI
  else closedCollectionCode kind components

/-- Normalize a collection with a unit whose components are already normal. -/
def normalizeCollectionCode (kind unit : ℕ) (components : List ℕ) : ℕ :=
  collapseCode kind unit ((contentsCode kind unit components).insertionSort (· ≤ ·))

/-! ## What the operations compute on codes of patterns

Each statement takes the operation on patterns with its defining equations. -/

section Specifications

variable {kind : CollType} {splice : Pattern → List Pattern}

/-- Splicing. -/
theorem spliceCode_patternCode
    (onCollection : ∀ elements, splice (.collection kind elements none) = elements)
    (onOther : ∀ pattern, (¬ ∃ elements, pattern = .collection kind elements none) →
      splice pattern = [pattern])
    (pattern : Pattern) :
    spliceCode (collectionCode kind) (patternCode pattern) = (splice pattern).map patternCode := by
  by_cases collection : ∃ elements, pattern = .collection kind elements none
  · obtain ⟨elements, rfl⟩ := collection
    rw [spliceCode, if_pos ((isClosedCollectionCode_patternCode kind _).mpr ⟨elements, rfl⟩),
      patternCode_closedCollection, collectionComponents_closedCollectionCode, onCollection]
  · rw [spliceCode, if_neg (mt (isClosedCollectionCode_patternCode kind pattern).mp collection),
      onOther pattern collection]
    rfl

/-- Splicing nested collections and dropping units. -/
theorem contentsCode_map
    (onCollection : ∀ elements, splice (.collection kind elements none) = elements)
    (onOther : ∀ pattern, (¬ ∃ elements, pattern = .collection kind elements none) →
      splice pattern = [pattern])
    (unit : String) (elements : List Pattern) :
    contentsCode (collectionCode kind) (patternCode (.apply unit [])) (elements.map patternCode) =
      ((elements.flatMap splice).filter fun pattern =>
        decide (pattern ≠ .apply unit [])).map patternCode := by
  have spliced : (elements.map patternCode).flatMap (spliceCode (collectionCode kind)) =
      (elements.flatMap splice).map patternCode := by
    simp only [List.flatMap_map, List.map_flatMap,
      spliceCode_patternCode onCollection onOther]
  rw [contentsCode, spliced, List.filter_map]
  congr 1
  apply List.filter_congr
  intro pattern _
  simp [patternCode_injective.eq_iff]

/-- Removing an empty or singleton wrapper. -/
theorem collapseCode_map {unit : String} {collapse : List Pattern → Pattern}
    (onEmpty : collapse [] = .apply unit [])
    (onSingleton : ∀ pattern, collapse [pattern] = pattern)
    (onMore : ∀ first second rest,
      collapse (first :: second :: rest) = .collection kind (first :: second :: rest) none)
    (patterns : List Pattern) :
    collapseCode (collectionCode kind) (patternCode (.apply unit [])) (patterns.map patternCode) =
      patternCode (collapse patterns) := by
  match patterns with
  | [] => rw [onEmpty]; rfl
  | [pattern] => rw [onSingleton]; rfl
  | first :: second :: rest =>
      rw [onMore, patternCode_closedCollection]
      simp [collapseCode]

/-- The whole normalization of a collection with a unit. -/
theorem normalizeCollectionCode_map {unit : String} {collapse : List Pattern → Pattern}
    (onCollection : ∀ elements, splice (.collection kind elements none) = elements)
    (onOther : ∀ pattern, (¬ ∃ elements, pattern = .collection kind elements none) →
      splice pattern = [pattern])
    (onEmpty : collapse [] = .apply unit [])
    (onSingleton : ∀ pattern, collapse [pattern] = pattern)
    (onMore : ∀ first second rest,
      collapse (first :: second :: rest) = .collection kind (first :: second :: rest) none)
    (elements : List Pattern) :
    normalizeCollectionCode (collectionCode kind) (patternCode (.apply unit []))
        (elements.map patternCode) =
      patternCode (collapse (sortPatterns
        ((elements.flatMap splice).filter fun pattern => decide (pattern ≠ .apply unit [])))) := by
  rw [normalizeCollectionCode, contentsCode_map onCollection onOther, ← map_sortPatterns,
    collapseCode_map onEmpty onSingleton onMore]

end Specifications

/-! ## Primitive recursiveness -/

theorem closedCollectionCode_primrec (kind : ℕ) : Primrec (closedCollectionCode kind) :=
  Primrec₂.natPair.comp (Primrec.const 6)
    (Primrec₂.natPair.comp (Primrec.const kind)
      (Primrec₂.natPair.comp Primrec.encode (Primrec.const (Nat.pair 0 0))))

theorem isClosedCollectionCode_primrecPred (kind : ℕ) :
    PrimrecPred (IsClosedCollectionCode kind) := by
  have payload : Primrec fun code : ℕ => code.unpair.2 := Primrec.snd.comp Primrec.unpair
  have inner : Primrec fun code : ℕ => code.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp payload)
  exact (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 6)).and
    ((Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp payload)) (Primrec.const kind)).and
      (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp inner))
        (Primrec.const (Nat.pair 0 0))))

theorem collectionComponents_primrec : Primrec collectionComponents := by
  have payload : Primrec fun code : ℕ => code.unpair.2 := Primrec.snd.comp Primrec.unpair
  have inner : Primrec fun code : ℕ => code.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp payload)
  exact (Primrec.ofNat (List ℕ)).comp (Primrec.fst.comp (Primrec.unpair.comp inner))

theorem spliceCode_primrec (kind : ℕ) : Primrec (spliceCode kind) :=
  Primrec.ite (isClosedCollectionCode_primrecPred kind) collectionComponents_primrec
    (Primrec.list_cons.comp Primrec.id (Primrec.const []))

theorem contentsCode_primrec (kind unit : ℕ) : Primrec (contentsCode kind unit) := by
  have kept : PrimrecPred fun code : ℕ => code ≠ unit :=
    (Primrec.eq.comp Primrec.id (Primrec.const unit)).not
  exact (Primrec.listFilter kept).comp
    (Primrec.list_flatMap Primrec.id ((spliceCode_primrec kind).comp₂ Primrec₂.right))

theorem collapseCode_primrec (kind unit : ℕ) : Primrec (collapseCode kind unit) :=
  Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 0)) (Primrec.const unit)
    (Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1)) Primrec.list_headI
      (closedCollectionCode_primrec kind))

theorem normalizeCollectionCode_primrec (kind unit : ℕ) :
    Primrec (normalizeCollectionCode kind unit) :=
  (collapseCode_primrec kind unit).comp (sortCodes_primrec.comp (contentsCode_primrec kind unit))

end Mettapedia.OSLF.MeTTaIL.PatternCode
