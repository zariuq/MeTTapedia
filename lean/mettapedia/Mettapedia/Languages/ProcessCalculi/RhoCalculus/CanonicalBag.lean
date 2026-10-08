import Mathlib.Data.Multiset.Sort
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

/-!
# Canonical closed rho processes as bags of primes

The outer parallel monoid of a closed rho process is a genuine multiset of
canonical nonunit, nonparallel processes. Internal quotations, input bodies
and output payloads remain intact. The equivalence below is with the actual
sorted process equations, including the authored name equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

local instance : LinearOrder Pattern := patternLinearOrder

/-- A closed canonical atom of the outer parallel monoid. -/
def IsPrime (pattern : Pattern) : Prop :=
  RhoClosedTermWellSorted rhoProc pattern ∧ IsCanonical pattern ∧
    pattern ≠ .apply "PZero" [] ∧
    ∀ elements, pattern ≠ .collection .hashBag elements none

/-- Complete canonical primes with their actual multiplicities. -/
def Bag := { inventory : Multiset Pattern // ∀ pattern ∈ inventory, IsPrime pattern }

/-- Sort by the injective structural code, without identifying occurrences. -/
def ordered (inventory : Multiset Pattern) : List Pattern := inventory.sort

@[simp]
theorem ordered_coe (patterns : List Pattern) :
    ordered (patterns : Multiset Pattern) = sortPatterns patterns := rfl

@[simp]
theorem ordered_multiset (inventory : Multiset Pattern) :
    (ordered inventory : Multiset Pattern) = inventory :=
  Multiset.sort_eq inventory _

@[simp]
theorem mem_ordered {pattern : Pattern} {inventory : Multiset Pattern} :
    pattern ∈ ordered inventory ↔ pattern ∈ inventory :=
  Multiset.mem_sort _

theorem ordered_sorted (inventory : Multiset Pattern) :
    sortPatterns (ordered inventory) = ordered inventory := by
  rw [← ordered_coe, ordered_multiset]

def contents (process : RhoProcess) : List Pattern :=
  normalizeBagElements [canonicalize process.1]

theorem contents_prime (process : RhoProcess) {pattern : Pattern}
    (membership : pattern ∈ contents process) : IsPrime pattern := by
  have canonical := canonicalize_isCanonical process.1
  have singletonCanonical : IsCanonicalList [canonicalize process.1] :=
    ⟨canonical, trivial⟩
  have closed := (rhoClosedTermWellSorted_process_iff process.1).mp process.2
  have typed : ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty []
      (contents process) :=
    normalizeBagElements_procListWellSorted
      (.cons (canonicalize_procWellSorted [] closed.1) .nil) rfl
  have safe : binderSafeListAt "NQuote" 0 (contents process) = true :=
    normalizeBagElements_binderSafeListAt
      (by simp [binderSafeListAt, canonicalize_binderSafeAt _ _ closed.2])
  exact ⟨(rhoClosedTermWellSorted_process_iff pattern).mpr
      ⟨procListWellSorted_iff_forall_mem.mp typed pattern membership,
        (binderSafeListAt_eq_true_iff _ _ _).mp safe pattern membership⟩,
    normalizeBagElements_member_isCanonical singletonCanonical membership,
    normalizeBagElements_no_zero membership,
    normalizeBagElements_no_nested_bag singletonCanonical membership⟩

/-- Decompose the actual canonical representative of a closed process. -/
def fromProcess (process : RhoProcess) : Bag :=
  ⟨(contents process : Multiset Pattern), fun _ membership =>
    contents_prime process (by simpa using membership)⟩

theorem contents_sorted (process : RhoProcess) :
    sortPatterns (contents process) = contents process :=
  normalizeBagElements_sorted _

theorem collapse_contents (process : RhoProcess) :
    collapseBag (contents process) = canonicalize process.1 :=
  collapse_normalize_singleton_of_isCanonical (canonicalize_isCanonical _)

theorem contents_of_canonical_bag (process : RhoProcess) {patterns : List Pattern}
    (shape : canonicalize process.1 = .collection .hashBag patterns none) :
    contents process = patterns := by
  have canonical := canonicalize_isCanonical process.1
  rw [shape] at canonical
  have filtered : patterns.filter (fun pattern => pattern ≠ .apply "PZero" []) =
      patterns := List.filter_eq_self.mpr fun pattern membership =>
    by simpa using (canonical.2.2.1 pattern membership).1
  unfold contents
  rw [shape, normalizeBagElements_eq_sort_bagContents]
  simp only [bagContents, List.flatMap_cons, List.flatMap_nil, bagSplice,
    List.append_nil, filtered]
  exact canonical.2.1

theorem ordered_fromProcess (process : RhoProcess) :
    ordered (fromProcess process).1 = contents process := by
  change ordered (contents process : Multiset Pattern) = contents process
  rw [ordered_coe, contents_sorted]

theorem normalize_multiset (patterns : List Pattern) :
    (normalizeBagElements patterns : Multiset Pattern) = bagContents patterns := by
  rw [normalizeBagElements_eq_sort_bagContents]
  exact Multiset.coe_eq_coe.mpr (sortPatterns_perm _).symm

theorem fromProcess_inventory (process : RhoProcess) :
    (fromProcess process).1 = (bagContents [canonicalize process.1] : Multiset Pattern) :=
  normalize_multiset _

/-- A supplied list of actual closed processes forms a closed parallel process. -/
def ofList (patterns : List Pattern)
    (closed : ∀ pattern ∈ patterns, RhoClosedTermWellSorted rhoProc pattern) : RhoProcess :=
  ⟨.collection .hashBag patterns none,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel (procListWellSorted_iff_forall_mem.mpr fun _ membership =>
          ((rhoClosedTermWellSorted_process_iff _).mp (closed _ membership)).1),
        by
          change binderSafeListAt "NQuote" 0 patterns = true
          rw [binderSafeListAt_eq_true_iff]
          intro pattern membership
          exact ((rhoClosedTermWellSorted_process_iff _).mp (closed _ membership)).2⟩⟩

theorem canonical_list_map (patterns : List Pattern) :
    IsCanonicalList (patterns.map canonicalize) := by
  apply isCanonicalList_of_forall
  intro pattern membership
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp membership
  exact canonicalize_isCanonical _

theorem fromProcess_ofList_inventory (patterns : List Pattern)
    (closed : ∀ pattern ∈ patterns, RhoClosedTermWellSorted rhoProc pattern) :
    (fromProcess (ofList patterns closed)).1 =
      (bagContents (patterns.map canonicalize) : Multiset Pattern) := by
  rw [fromProcess_inventory]
  change (bagContents [canonicalize (.collection .hashBag patterns none)] :
    Multiset Pattern) = _
  rw [canonicalize_bag, bagContents_collapse_normalized (canonical_list_map patterns)]
  exact normalize_multiset _

theorem map_canonicalize_primes (patterns : List Pattern)
    (primes : ∀ pattern ∈ patterns, IsPrime pattern) :
    patterns.map canonicalize = patterns := by
  calc
    patterns.map canonicalize = patterns.map id :=
      List.map_congr_left fun pattern membership =>
        canonicalize_eq_of_isCanonical (primes pattern membership).2.1
    _ = patterns := List.map_id _

theorem fromProcess_ofList_primes (patterns : List Pattern)
    (primes : ∀ pattern ∈ patterns, IsPrime pattern) :
    (fromProcess (ofList patterns (fun _ membership => (primes _ membership).1))).1 =
      (patterns : Multiset Pattern) := by
  rw [fromProcess_ofList_inventory, map_canonicalize_primes patterns primes,
    bagContents_eq_self
      (fun _ membership => (primes _ membership).2.2.1)
      (fun _ membership => (primes _ membership).2.2.2)]

theorem fromProcess_cons_primes (process : RhoProcess) (patterns : List Pattern)
    (closed : ∀ pattern ∈ process.1 :: patterns, RhoClosedTermWellSorted rhoProc pattern)
    (primes : ∀ pattern ∈ patterns, IsPrime pattern) :
    (fromProcess (ofList (process.1 :: patterns) closed)).1 =
      (fromProcess process).1 + (patterns : Multiset Pattern) := by
  rw [fromProcess_ofList_inventory, List.map_cons,
    map_canonicalize_primes patterns primes,
    ← List.singleton_append, bagContents_append,
    bagContents_eq_self
      (fun _ membership => (primes _ membership).2.2.1)
      (fun _ membership => (primes _ membership).2.2.2),
    fromProcess_inventory, ← Multiset.coe_add]

theorem ordered_prime (inventory : Bag) {pattern : Pattern}
    (membership : pattern ∈ ordered inventory.1) : IsPrime pattern :=
  inventory.2 pattern (mem_ordered.mp membership)

theorem ordered_canonical (inventory : Bag) : IsCanonicalList (ordered inventory.1) :=
  isCanonicalList_of_forall fun _ membership => (ordered_prime inventory membership).2.1

theorem ordered_normalize (inventory : Bag) :
    normalizeBagElements (ordered inventory.1) = ordered inventory.1 := by
  rw [normalizeBagElements_eq_sort_bagContents,
    bagContents_eq_self
      (fun _ membership => (ordered_prime inventory membership).2.2.1)
      (fun _ membership => (ordered_prime inventory membership).2.2.2),
    ordered_sorted]

/-- Rebuild the process; its closed formation is derived from every member. -/
def toProcess (inventory : Bag) : RhoProcess :=
  RhoClosedTerm.canonicalize
    ⟨.collection .hashBag (ordered inventory.1) none,
      (rhoClosedTermWellSorted_process_iff _).mpr
        ⟨.parallel (procListWellSorted_iff_forall_mem.mpr fun _ membership =>
            ((rhoClosedTermWellSorted_process_iff _).mp
              (ordered_prime inventory membership).1).1),
          by
            change binderSafeListAt "NQuote" 0 (ordered inventory.1) = true
            rw [binderSafeListAt_eq_true_iff]
            intro pattern membership
            exact ((rhoClosedTermWellSorted_process_iff _).mp
              (ordered_prime inventory membership).1).2⟩⟩

theorem toProcess_pattern (inventory : Bag) :
    (toProcess inventory).1 = collapseBag (ordered inventory.1) := by
  change canonicalize (.collection .hashBag (ordered inventory.1) none) = _
  rw [canonicalize_bag, ← canonicalizeList_eq_map,
    canonicalizeList_eq_of_isCanonical (ordered_canonical inventory),
    ordered_normalize]

theorem toProcess_canonical (inventory : Bag) :
    canonicalize (toProcess inventory).1 = (toProcess inventory).1 :=
  canonicalize_idempotent _

theorem contents_toProcess (inventory : Bag) :
    contents (toProcess inventory) = ordered inventory.1 := by
  unfold contents
  rw [toProcess_canonical, toProcess_pattern, normalizeBagElements_eq_sort_bagContents]
  have collapse := bagContents_collapse_normalized (ordered_canonical inventory)
  rw [ordered_normalize] at collapse
  rw [collapse, ordered_sorted]

@[simp]
theorem fromProcess_toProcess (inventory : Bag) :
    fromProcess (toProcess inventory) = inventory := by
  apply Subtype.ext
  change (contents (toProcess inventory) : Multiset Pattern) = inventory.1
  rw [contents_toProcess, ordered_multiset]

theorem toProcess_fromProcess (process : RhoProcess) :
    toProcess (fromProcess process) = process.canonicalize := by
  apply Subtype.ext
  rw [toProcess_pattern]
  change collapseBag (ordered (contents process : Multiset Pattern)) = canonicalize process.1
  rw [ordered_coe, contents_sorted, collapse_contents]

/-- Equality of bags is exactly the actual closed process equation relation. -/
theorem fromProcess_eq_iff (first second : RhoProcess) :
    fromProcess first = fromProcess second ↔ rhoProcessEquations.r first second := by
  constructor
  · intro equal
    have same := congrArg toProcess equal
    rw [toProcess_fromProcess, toProcess_fromProcess] at same
    exact congrArg Subtype.val same
  · intro equal
    apply Subtype.ext
    change (normalizeBagElements [canonicalize first.1] : Multiset Pattern) =
      (normalizeBagElements [canonicalize second.1] : Multiset Pattern)
    rw [equal]

/-- The actual closed equational quotient is the free outer bag of primes. -/
def quotientEquiv : Quotient rhoProcessEquations ≃ Bag where
  toFun := Quotient.lift fromProcess fun _ _ equal => (fromProcess_eq_iff _ _).mpr equal
  invFun := fun inventory => Quotient.mk rhoProcessEquations (toProcess inventory)
  left_inv := by
    intro equivalenceClass
    refine Quotient.inductionOn equivalenceClass ?_
    intro process
    change Quotient.mk rhoProcessEquations (toProcess (fromProcess process)) = _
    apply Quotient.sound
    rw [toProcess_fromProcess]
    exact canonicalize_idempotent _
  right_inv := fromProcess_toProcess

def empty : Bag := ⟨0, fun _ membership => False.elim (by simp at membership)⟩

def append (first second : Bag) : Bag :=
  ⟨first.1 + second.1, fun pattern membership => by
    rcases Multiset.mem_add.mp membership with member | member
    · exact first.2 pattern member
    · exact second.2 pattern member⟩

@[simp]
theorem append_inventory (first second : Bag) :
    (append first second).1 = first.1 + second.1 := rfl

theorem append_assoc (first second third : Bag) :
    append (append first second) third = append first (append second third) := by
  apply Subtype.ext
  exact add_assoc _ _ _

theorem append_comm (first second : Bag) : append first second = append second first := by
  apply Subtype.ext
  exact add_comm _ _

@[simp]
theorem append_empty (inventory : Bag) : append inventory empty = inventory := by
  apply Subtype.ext
  exact add_zero _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
