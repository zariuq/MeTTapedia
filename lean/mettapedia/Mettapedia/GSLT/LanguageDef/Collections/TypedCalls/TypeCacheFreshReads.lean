import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRowFreshening

/-!
# Allocated declaration reads preserve retained row answers

The existing occurrence allocator supplies the private-permutation evidence
used by the ordered row theorem. Different supplies may allocate different
names and advance differently; only the completed row answers are identified.
This does not erase allocation state in later recursive requests.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeCacheFreshReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open TypeDependencyAdmission TypeScopeMatcher NativeTypeViews TypeRowFreshening

theorem allocated_variant_permutation {scope : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel scope source target) :
    ∃ permutation : Equiv.Perm String, target = renameAtom permutation source := by
  have alpha : Alpha.ObservedTypeAlphaRel source target :=
    ⟨source, TypeVariableRenamingOf.refl source, variant.toTypeVariableRenamingOf⟩
  obtain ⟨permutation, same⟩ := (TypeAlphaComparison.check_iff_permutation source target).mp
    ((TypeAlphaComparison.check_iff_observed_alpha source target).mpr alpha)
  exact ⟨permutation, same.symm⟩

theorem variant_rows_permutations {scope : List String} {rows freshRows : List Atom}
    (variants : ArgumentAlphaVariantsRel scope rows freshRows) :
    List.Forall₂ (fun row freshRow =>
      ∃ permutation : Equiv.Perm String, freshRow = renameAtom permutation row)
      rows freshRows := by
  induction variants with
  | nil => exact .nil
  | cons head _ ih => exact .cons (allocated_variant_permutation head) ih

theorem allocated_rows_permutations (supply : TypeReadSupply.Supply) (rows : List Atom) :
    List.Forall₂ (fun row freshRow =>
      ∃ permutation : Equiv.Perm String, freshRow = renameAtom permutation row)
      rows (TypeReadSupply.freshList supply rows).1 :=
  variant_rows_permutations (TypeReadSupply.freshList_variants supply rows)

theorem allocated_rows_exact (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (normalizes : ∀ (permutation : Equiv.Perm String) atom, resourceFree atom = true →
      normalize (renameAtom permutation atom) = renameAtom permutation (normalize atom))
    (children : List (ChildView Atom Atom)) (childrenRetained : ChildrenRetained children)
    (rows : List Atom) (rowsSafe : resourceFreeList rows = true)
    (outputsRetained : ∀ row ∈ rows, ∀ result,
      transitionRow (ops external normalize subtypes) children row = some result →
        RetainedTypePayloads.admitted result = true)
    (supply : TypeReadSupply.Supply) :
    transitionRows (ops external normalize subtypes) children (TypeReadSupply.freshList supply rows).1 =
      transitionRows (ops external normalize subtypes) children rows :=
  independently_fresh_rows_exact external normalize subtypes normalizes children childrenRetained
    (allocated_rows_permutations supply rows) rowsSafe outputsRetained

theorem different_supplies_same_retained_rows (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (normalizes : ∀ (permutation : Equiv.Perm String) atom, resourceFree atom = true →
      normalize (renameAtom permutation atom) = renameAtom permutation (normalize atom))
    (children : List (ChildView Atom Atom)) (childrenRetained : ChildrenRetained children)
    (rows : List Atom) (rowsSafe : resourceFreeList rows = true)
    (outputsRetained : ∀ row ∈ rows, ∀ result,
      transitionRow (ops external normalize subtypes) children row = some result →
        RetainedTypePayloads.admitted result = true)
    (first second : TypeReadSupply.Supply) :
    transitionRows (ops external normalize subtypes) children (TypeReadSupply.freshList first rows).1 =
      transitionRows (ops external normalize subtypes) children (TypeReadSupply.freshList second rows).1 :=
  (allocated_rows_exact external normalize subtypes normalizes children childrenRetained rows rowsSafe
    outputsRetained first).trans
      (allocated_rows_exact external normalize subtypes normalizes children childrenRetained rows rowsSafe
        outputsRetained second).symm

namespace Controls

open TypeRowFreshening.Controls

def first : TypeReadSupply.Supply := ⟨[], 0⟩
def later : TypeReadSupply.Supply := ⟨["caller"], 7⟩

theorem freshened_duplicates_still_count_twice :
    transitionRows checkOps [number]
      (TypeReadSupply.freshList later [signature "a", signature "a"]).1 =
      [.symbol "Number", .symbol "Number"] := by cbv

theorem open_answers_keep_the_supply_observable :
    let rows := [.expression [.symbol "->", .var "argument", .var "result"]]
    transitionRows checkOps [number] (TypeReadSupply.freshList first rows).1 ≠
      transitionRows checkOps [number] (TypeReadSupply.freshList later rows).1 := by
  cbv
  simp

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeCacheFreshReads
