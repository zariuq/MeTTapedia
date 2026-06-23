import Mettapedia.OSLF.PathMap.ProductOverlayZipper
import Mettapedia.OSLF.PathMap.Trie.DescendUntilRefinement
import Mettapedia.OSLF.PathMap.Trie.SortedPreservation
import Mettapedia.OSLF.PathMap.Trie.UnitBridge

/-!
# Overlay Descend-Until Refinement

This file lifts the plain finite-trie `descend_until` story to the next
PathMap layer: overlay tries.

The key idea is that an overlay trie is not given its own independent descent
semantics.  Instead, it is interpreted as the **virtual left-biased join** of
the local and base tries, and `descend_until` is defined through that joined
carrier.

This matches the intended machine story in `overlay_zipper.rs`:

- overlay navigation is over a virtual fused trie
- local values shadow base values
- stopping may occur at an internal prefix value
- branches remain stable
-/

namespace Mettapedia.OSLF.PathMap

open Trie
open Trie.FTrie

universe u

variable {V : Type u}

/-- The virtual trie represented by an overlay: local values shadow base values
    via left-biased join. -/
def OverlayTrie.virtualTrie (ot : OverlayTrie V) : FTrie V :=
  FTrie.join ot.local_ ot.base

/-- Overlay `descend_until` interpreted through the virtual joined trie. -/
def OverlayTrie.descendUntilPath (ot : OverlayTrie V) (start : List UInt8) : List UInt8 :=
  FTrie.descendUntilPath ot.virtualTrie start

/-- Child count at a focus in the overlay's virtual trie. -/
def OverlayTrie.childCountAt (ot : OverlayTrie V) (path : List UInt8) : Nat :=
  FTrie.childCount (ot.virtualTrie.subtreeAt path)

/-- Root value at a focus in the overlay's virtual trie. -/
def OverlayTrie.rootValAt? (ot : OverlayTrie V) (path : List UInt8) : Option V :=
  FTrie.rootVal? (ot.virtualTrie.subtreeAt path)

theorem OverlayTrie.virtualTrie_sorted (ot : OverlayTrie V)
    (hsl : ot.local_.Sorted) (hsb : ot.base.Sorted) :
    ot.virtualTrie.Sorted := by
  simpa [OverlayTrie.virtualTrie] using FTrie.join_sorted ot.local_ ot.base hsl hsb

theorem OverlayTrie.lookup_eq_virtualTrie_lookup (ot : OverlayTrie V) (path : List UInt8)
    (hsl : ot.local_.Sorted) (hsb : ot.base.Sorted) :
    ot.lookup path = ot.virtualTrie.lookup path := by
  simpa [OverlayTrie.virtualTrie] using overlay_lookup_eq_join ot path hsl hsb

theorem FTrie.rootVal?_subtreeAt_eq_lookup (t : FTrie V) (path : List UInt8) :
    FTrie.rootVal? (t.subtreeAt path) = t.lookup path := by
  have hLookup := FTrie.subtreeAt_lookup t path []
  cases h : t.subtreeAt path with
  | empty =>
      rw [h] at hLookup
      simpa [FTrie.rootVal?, FTrie.lookup] using hLookup
  | node val children =>
      rw [h] at hLookup
      simpa [FTrie.rootVal?, FTrie.lookup] using hLookup

theorem FTrie.subtreeAt_append (t : FTrie V) (pfx suffix : List UInt8) :
    (t.subtreeAt pfx).subtreeAt suffix = t.subtreeAt (pfx ++ suffix) := by
  induction pfx generalizing t with
  | nil =>
      simp [FTrie.subtreeAt_nil]
  | cons b rest ih =>
      cases t with
      | empty =>
          simp [FTrie.subtreeAt]
      | node val children =>
          simp [FTrie.subtreeAt]
          induction children with
          | nil =>
              simp [FTrie.subtreeAt]
          | cons hd tl ihc =>
              obtain ⟨k, child⟩ := hd
              by_cases hkb : (k == b) = true
              · simp [hkb]
                exact ih child
              · simp [hkb]
                exact ihc

theorem OverlayTrie.descendUntilPath_extends (ot : OverlayTrie V) (start : List UInt8) :
    start <+: ot.descendUntilPath start := by
  simpa [OverlayTrie.descendUntilPath, OverlayTrie.virtualTrie] using
    FTrie.descendUntilPath_extends ot.virtualTrie start

theorem OverlayTrie.descendUntilPath_stable_of_childCount_ne_one
    (ot : OverlayTrie V) (start : List UInt8)
    (h : ot.childCountAt start ≠ 1) :
    ot.descendUntilPath start = start := by
  simpa [OverlayTrie.descendUntilPath, OverlayTrie.childCountAt, OverlayTrie.virtualTrie] using
    FTrie.descendUntilPath_stable_of_childCount_ne_one ot.virtualTrie start h

theorem OverlayTrie.descendUntilPath_stops_at_first_internal_value
    (ot : OverlayTrie V) (start : List UInt8) (val : Option V)
    (b : UInt8) (child : FTrie V)
    (hfocus : ot.virtualTrie.subtreeAt start = FTrie.node val [(b, child)])
    (hval : (FTrie.rootVal? child).isSome = true) :
    ot.descendUntilPath start = start ++ [b] := by
  simpa [OverlayTrie.descendUntilPath] using
    FTrie.descendUntilPath_stops_at_first_internal_value ot.virtualTrie start val b child hfocus hval

theorem OverlayTrie.descendUntilPath_stops (ot : OverlayTrie V) (start : List UInt8)
    (hsl : ot.local_.Sorted) (hsb : ot.base.Sorted) :
    (ot.lookup (ot.descendUntilPath start)).isSome = true ∨
      ot.childCountAt (ot.descendUntilPath start) ≠ 1 := by
  let focus := ot.virtualTrie.subtreeAt start
  have hstop := FTrie.descendUntilSuffix_stops focus
  cases hstop with
  | inl hval =>
      left
      have hLookupFocus :
          (focus.lookup (FTrie.descendUntilSuffix focus)).isSome = true := by
        simpa [FTrie.rootVal?_subtreeAt_eq_lookup] using hval
      have hLookupVirtual :
          (ot.virtualTrie.lookup (start ++ FTrie.descendUntilSuffix focus)).isSome = true := by
        simpa [focus, FTrie.subtreeAt_lookup] using hLookupFocus
      have hOverlayEq :
          ot.lookup (start ++ FTrie.descendUntilSuffix focus) =
            ot.virtualTrie.lookup (start ++ FTrie.descendUntilSuffix focus) :=
        ot.lookup_eq_virtualTrie_lookup (start ++ FTrie.descendUntilSuffix focus) hsl hsb
      have hPath : ot.descendUntilPath start = start ++ FTrie.descendUntilSuffix focus := by
        rfl
      rw [hPath]
      rw [hOverlayEq]
      exact hLookupVirtual
  | inr hbranch =>
      right
      simpa [OverlayTrie.childCountAt, OverlayTrie.descendUntilPath, FTrie.descendUntilPath,
        focus, FTrie.subtreeAt_append]
        using hbranch

/-! ## Examples -/

def overlayInternalValue : OverlayTrie Unit :=
  { base := FTrie.singleton [1, 2, 3] ()
    local_ := FTrie.singleton [1] () }

def overlayBranch : OverlayTrie Unit :=
  { base := FTrie.singleton [1] ()
    local_ := FTrie.singleton [2] () }

/-- Positive example: local internal prefix value stops overlay descent early. -/
example :
    overlayInternalValue.descendUntilPath [] = [1] := by
  simp [overlayInternalValue, OverlayTrie.descendUntilPath, OverlayTrie.virtualTrie,
    FTrie.singleton, FTrie.join, FTrie.joinChildren, FTrie.descendUntilPath,
    FTrie.descendUntilSuffix, FTrie.subtreeAt, FTrie.rootVal?]

/-- Positive example: the descended overlay focus really carries the shadowing value. -/
example :
    overlayInternalValue.lookup (overlayInternalValue.descendUntilPath []) = some () := by
  simp [overlayInternalValue, OverlayTrie.lookup, OverlayTrie.descendUntilPath,
    OverlayTrie.virtualTrie, FTrie.singleton, FTrie.join, FTrie.joinChildren,
    FTrie.descendUntilPath, FTrie.descendUntilSuffix, FTrie.subtreeAt, FTrie.rootVal?,
    FTrie.lookup, FTrie.lookupChild, Option.orElse]

/-- Negative example: overlay descent does not move at a virtual branch. -/
example :
    overlayBranch.descendUntilPath [] = [] := by
  apply OverlayTrie.descendUntilPath_stable_of_childCount_ne_one
  simp [OverlayTrie.childCountAt, overlayBranch, OverlayTrie.virtualTrie, FTrie.childCount,
    FTrie.subtreeAt, FTrie.singleton, FTrie.join, FTrie.joinChildren]

/-! ## Summary

**0 sorries. 0 axioms.**

This file lifts `descend_until` from plain finite tries to overlay tries:

- overlay descent is defined through the virtual left-biased joined trie
- lookup after descent is the same lookup the overlay exposes publicly
- the stopping point may still be an internal prefix value
- virtual branches remain stable

This narrows the remaining `descend_until` uncertainty to the more complex
product and dependent zipper layers.
-/

end Mettapedia.OSLF.PathMap
