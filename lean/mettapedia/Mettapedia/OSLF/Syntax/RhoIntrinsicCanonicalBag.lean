import Mettapedia.OSLF.Syntax.RhoFiniteQuotationOrigins
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag

/-!
# Complete intrinsic rho processes as context-indexed parallel inventories

The existing closed-process bag normalization is reused on the complete
intrinsic carrier. Its prime admission uses the actual sorting judgment in
the supplied source context, without imposing the separate sealed quotation
profile. Sorted readback reconstructs every inventory. Both inverse laws
compare independently formed process classes and multiset inventories.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicCanonicalBag

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoCanonicalNamePairs
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback
open MeTTaIL.Syntax MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

local instance : LinearOrder Pattern := patternLinearOrder

def IsPrime (context : Ctx sig) (pattern : Pattern) : Prop :=
  Sorted context Srt.pr pattern ∧ IsCanonical pattern ∧
    pattern ≠ .apply "PZero" [] ∧ ∀ elements, pattern ≠ .collection .hashBag elements none

def Inventory (context : Ctx sig) :=
  {inventory : Multiset Pattern // ∀ pattern ∈ inventory, IsPrime context pattern}

theorem encoded_isCanonical {context : Ctx sig} {sort : Srt}
    (value : TermQ rhoSourceE context sort) : IsCanonical (encodeEquationClass value) := by
  have normal := canonicalize_isCanonical (encodeEquationClass value)
  rw [encoded_class_canonical] at normal
  exact normal

def contents {context : Ctx sig} (process : Process context) : List Pattern :=
  normalizeBagElements [encodeEquationClass process]

theorem contents_prime {context : Ctx sig} (process : Process context) {pattern : Pattern}
    (member : pattern ∈ contents process) : IsPrime context pattern := by
  have normal : IsCanonicalList [encodeEquationClass process] :=
    ⟨encoded_isCanonical process, trivial⟩
  have typed : ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) (contents process) :=
    normalizeBagElements_procListWellSorted (.cons (encoded_class_sorted process) .nil) rfl
  exact ⟨procListWellSorted_iff_forall_mem.mp typed pattern member,
    normalizeBagElements_member_isCanonical normal member,
    normalizeBagElements_no_zero member, normalizeBagElements_no_nested_bag normal member⟩

def decompose {context : Ctx sig} (process : Process context) : Inventory context :=
  ⟨(contents process : Multiset Pattern), fun _ member =>
    contents_prime process (by simpa only [Multiset.mem_coe] using member)⟩

def ordered {context : Ctx sig} (inventory : Inventory context) : List Pattern := inventory.val.sort

theorem ordered_multiset {context : Ctx sig} (inventory : Inventory context) :
    (ordered inventory : Multiset Pattern) = inventory.val := Multiset.sort_eq _ _

theorem mem_ordered {context : Ctx sig} {inventory : Inventory context} {pattern : Pattern} :
    pattern ∈ ordered inventory ↔ pattern ∈ inventory.val := Multiset.mem_sort _

theorem ordered_sorted {context : Ctx sig} (inventory : Inventory context) :
    sortPatterns (ordered inventory) = ordered inventory := by
  change CanonicalBag.ordered (ordered inventory : Multiset Pattern) = ordered inventory
  rw [ordered_multiset]
  rfl

theorem ordered_prime {context : Ctx sig} (inventory : Inventory context) {pattern : Pattern}
    (member : pattern ∈ ordered inventory) : IsPrime context pattern :=
  inventory.property pattern (mem_ordered.mp member)

theorem ordered_canonical {context : Ctx sig} (inventory : Inventory context) :
    IsCanonicalList (ordered inventory) :=
  isCanonicalList_of_forall fun _ member => (ordered_prime inventory member).2.1

theorem ordered_typed {context : Ctx sig} (inventory : Inventory context) :
    ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) (ordered inventory) :=
  procListWellSorted_iff_forall_mem.mpr fun _ member => (ordered_prime inventory member).1

theorem ordered_normalize {context : Ctx sig} (inventory : Inventory context) :
    normalizeBagElements (ordered inventory) = ordered inventory := by
  rw [normalizeBagElements_eq_sort_bagContents,
    bagContents_eq_self (fun _ member => (ordered_prime inventory member).2.2.1)
      (fun _ member => (ordered_prime inventory member).2.2.2), ordered_sorted]

def realize {context : Ctx sig} (inventory : Inventory context) : Process context :=
  decodeCanonical ⟨canonicalize (.collection .hashBag (ordered inventory) none),
    Sorted.canonicalize (MeTTaIL.DerivedPresentationSyntax.ProcWellSorted.parallel
      (ordered_typed inventory)), canonicalize_idempotent _⟩

theorem encode_realize {context : Ctx sig} (inventory : Inventory context) :
    encodeEquationClass (realize inventory) = collapseBag (ordered inventory) := by
  have same := congrArg Subtype.val (encode_decode
    (⟨canonicalize (.collection .hashBag (ordered inventory) none),
      Sorted.canonicalize (MeTTaIL.DerivedPresentationSyntax.ProcWellSorted.parallel
        (ordered_typed inventory)), canonicalize_idempotent _⟩ : CanonicalPattern context Srt.pr))
  change encodeEquationClass (realize inventory) =
    canonicalize (.collection .hashBag (ordered inventory) none) at same
  rw [same]
  change collapseBag (normalizeBagElements (canonicalizeList (ordered inventory))) = _
  rw [canonicalizeList_eq_of_isCanonical (ordered_canonical inventory), ordered_normalize]

theorem ordered_decompose {context : Ctx sig} (process : Process context) :
    ordered (decompose process) = contents process := by
  change sortPatterns (contents process) = contents process
  exact normalizeBagElements_sorted _

theorem realize_decompose {context : Ctx sig} (process : Process context) :
    realize (decompose process) = process := by
  apply canonical_encoding_injective context Srt.pr
  rw [encode_realize, ordered_decompose]
  exact collapse_normalize_singleton_of_isCanonical (encoded_isCanonical process)

theorem decompose_realize {context : Ctx sig} (inventory : Inventory context) :
    decompose (realize inventory) = inventory := by
  apply Subtype.ext
  change (normalizeBagElements [encodeEquationClass (realize inventory)] : Multiset Pattern) = inventory.val
  rw [encode_realize, normalizeBagElements_eq_sort_bagContents]
  have collapsed := bagContents_collapse_normalized (ordered_canonical inventory)
  rw [ordered_normalize] at collapsed
  rw [collapsed, ordered_sorted]
  exact ordered_multiset inventory

def processInventoryEquiv (context : Ctx sig) : Process context ≃ Inventory context where
  toFun := decompose
  invFun := realize
  left_inv := realize_decompose
  right_inv := decompose_realize

def components {context : Ctx sig} (process : Process context) : Multiset Pattern :=
  (decompose process).val

theorem components_injective (context : Ctx sig) :
    Function.Injective (components (context := context)) := by
  intro first second same
  apply (processInventoryEquiv context).injective
  exact Subtype.ext same

theorem components_bagContents {context : Ctx sig} (process : Process context) :
    components process = (bagContents [encodeEquationClass process] : Multiset Pattern) :=
  CanonicalBag.normalize_multiset _

theorem zero_components (context : Ctx sig) : components (zero context) = 0 := by
  rw [components_bagContents]
  change (bagContents [canonicalize (.apply "PZero" [])] : Multiset Pattern) = 0
  rw [canonicalize_apply_general "PZero" [] (by simp)]
  simp [canonicalizeList, bagContents, bagSplice]

theorem drop_components {context : Ctx sig} (name : Name context) :
    components (drop name) = {Pattern.apply "PDrop" [encodeEquationClass name]} := by
  rw [components_bagContents, encode_drop]
  rfl

theorem drop_not_zero {context : Ctx sig} (name : Name context) : drop name ≠ zero context := by
  intro same
  have inventory := congrArg components same
  rw [drop_components, zero_components] at inventory
  have impossible := congrArg Multiset.card inventory
  exact Nat.one_ne_zero impossible

theorem join_components {context : Ctx sig} (first second : Process context) :
    components (join first second) = components first + components second := by
  rw [components_bagContents, encode_join,
    bagContents_collapse_normalized (show IsCanonicalList
      [encodeEquationClass first, encodeEquationClass second] from
      ⟨encoded_isCanonical first, encoded_isCanonical second, trivial⟩),
    CanonicalBag.normalize_multiset]
  change (bagContents ([encodeEquationClass first] ++ [encodeEquationClass second]) : Multiset Pattern) = _
  rw [bagContents_append, ← Multiset.coe_add, ← components_bagContents, ← components_bagContents]

end Mettapedia.OSLF.Binding.RhoIntrinsicCanonicalBag
