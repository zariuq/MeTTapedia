import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationScope
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeRenaming
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupply

/-!
# Variable support and coordinate symmetry of type normalization

The existing normalizer is used unchanged. Each actually licensed primitive
owes its own support and permutation laws. Resource-free output alone does
not supply either law: a primitive could fabricate a fixed variable name.
Boolean results and selection of an existing operand have direct support
proofs; their coordinate symmetry follows from the comparator's symmetry.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationNames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open InertTypeDependencies (normalize normalizeList normalizeHead)
open TypeNormalizationScope (Primitive booleanResult chooseResult)

def ResultsSupported (active : String → Bool) (primitive : Primitive) : Prop :=
  ∀ head args, active head = true → ∀ result, primitive head args = some result →
    atomVariables result ⊆ atomListVariables args

def Equivariant (active : String → Bool) (primitive : Primitive) : Prop :=
  ∀ (permutation : Equiv.Perm String) head args, active head = true →
    primitive head (renameAtomList permutation args) =
      (primitive head args).map (renameAtom permutation)

theorem head_support (active : String → Bool) (primitive : Primitive)
    (supported : ResultsSupported active primitive) (atom : Atom) :
    atomVariables (normalizeHead active primitive atom) ⊆ atomVariables atom := by
  unfold normalizeHead
  split
  next head first second rest =>
    split
    next licensed =>
      cases returned : primitive head (first :: second :: rest) with
      | none => exact fun _ member => member
      | some result =>
          simpa only [Option.getD_some, atomVariables, atomListVariables, List.nil_append] using
            supported head (first :: second :: rest) licensed result returned
    next _ => exact fun _ member => member
  next _ => exact fun _ member => member

mutual
theorem normalize_support (active : String → Bool) (primitive : Primitive)
    (supported : ResultsSupported active primitive) : ∀ atom,
    atomVariables (normalize active primitive atom) ⊆ atomVariables atom
  | .symbol _ => fun _ member => member
  | .var _ => fun _ member => member
  | .grounded _ => fun _ member => member
  | .expression children => by
      rw [InertTypeDependencies.normalize]
      split
      · exact fun _ member => member
      · exact fun name member => normalizeList_support active primitive supported children
          (head_support active primitive supported _ member)
theorem normalizeList_support (active : String → Bool) (primitive : Primitive)
    (supported : ResultsSupported active primitive) : ∀ atoms,
    atomListVariables (normalizeList active primitive atoms) ⊆ atomListVariables atoms
  | [] => fun _ member => member
  | atom :: atoms => by
      intro name member
      rcases List.mem_append.mp member with first | later
      · exact List.mem_append_left _ (normalize_support active primitive supported atom first)
      · exact List.mem_append_right _ (normalizeList_support active primitive supported atoms later)
end

theorem normalize_remains_allocated (active : String → Bool) (primitive : Primitive)
    (supported : ResultsSupported active primitive) (atom : Atom) (supply : TypeReadSupply.Supply)
    (allocated : atomVariables atom ⊆ supply.used) :
    atomVariables (normalize active primitive atom) ⊆ supply.used :=
  fun _ member => allocated (normalize_support active primitive supported atom member)

theorem head_equivariant (active : String → Bool) (primitive : Primitive)
    (equivariant : Equivariant active primitive) (permutation : Equiv.Perm String) (atom : Atom) :
    normalizeHead active primitive (renameAtom permutation atom) =
      renameAtom permutation (normalizeHead active primitive atom) := by
  cases atom with
  | symbol _ | var _ | grounded _ => rfl
  | expression children =>
      cases children with
      | nil => rfl
      | cons head rest =>
          cases head with
          | var _ | grounded _ | expression _ => rfl
          | symbol name =>
              cases rest with
              | nil => rfl
              | cons first rest =>
                  cases rest with
                  | nil => rfl
                  | cons second rest =>
                      simp only [renameAtom, renameAtomList, normalizeHead]
                      split
                      next licensed =>
                        have operation := equivariant permutation name (first :: second :: rest) licensed
                        simp only [renameAtomList] at operation
                        rw [operation]
                        cases primitive name (first :: second :: rest) <;> rfl
                      next _ => rfl

mutual
theorem normalize_equivariant (active : String → Bool) (primitive : Primitive)
    (equivariant : Equivariant active primitive) (permutation : Equiv.Perm String) : ∀ atom,
    normalize active primitive (renameAtom permutation atom) =
      renameAtom permutation (normalize active primitive atom)
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl
  | .expression children => by
      simp only [renameAtom, InertTypeDependencies.normalize,
        show (renameAtomList permutation children).length = children.length by
          simp [renameAtomList_eq_map]]
      split
      · rfl
      · rw [normalizeList_equivariant active primitive equivariant permutation children]
        simpa only [renameAtom] using head_equivariant active primitive equivariant permutation
          (.expression (normalizeList active primitive children))
theorem normalizeList_equivariant (active : String → Bool) (primitive : Primitive)
    (equivariant : Equivariant active primitive) (permutation : Equiv.Perm String) : ∀ atoms,
    normalizeList active primitive (renameAtomList permutation atoms) =
      renameAtomList permutation (normalizeList active primitive atoms)
  | [] => rfl
  | atom :: atoms => by
      rw [renameAtomList, normalizeList, normalizeList, renameAtomList,
        normalize_equivariant active primitive equivariant permutation atom,
        normalizeList_equivariant active primitive equivariant permutation atoms]
end

theorem booleanResult_support (compare : Atom → Atom → Bool) (args : List Atom)
    (result : Atom) (returned : booleanResult compare args = some result) :
    atomVariables result ⊆ atomListVariables args := by
  unfold booleanResult at returned
  split at returned
  · cases Option.some.inj returned
    intro name member
    cases member
  · contradiction

theorem chooseResult_support (compare : Atom → Atom → Bool) (args : List Atom)
    (result : Atom) (returned : chooseResult compare args = some result) :
    atomVariables result ⊆ atomListVariables args := by
  unfold chooseResult at returned
  split at returned
  · cases Option.some.inj returned
    split <;> intro name member <;> simp [atomListVariables, member]
  · contradiction

def ComparisonEquivariant (compare : Atom → Atom → Bool) : Prop :=
  ∀ (permutation : Equiv.Perm String) left right,
    compare (renameAtom permutation left) (renameAtom permutation right) = compare left right

theorem booleanResult_equivariant (compare : Atom → Atom → Bool)
    (symmetricNames : ComparisonEquivariant compare) (permutation : Equiv.Perm String) (args : List Atom) :
    booleanResult compare (renameAtomList permutation args) =
      (booleanResult compare args).map (renameAtom permutation) := by
  cases args with
  | nil => rfl
  | cons left rest =>
      cases rest with
      | nil => rfl
      | cons right rest =>
          cases rest with
          | nil => simp [booleanResult, renameAtomList, renameAtom, symmetricNames permutation left right]
          | cons _ _ => rfl

theorem chooseResult_equivariant (compare : Atom → Atom → Bool)
    (symmetricNames : ComparisonEquivariant compare) (permutation : Equiv.Perm String) (args : List Atom) :
    chooseResult compare (renameAtomList permutation args) =
      (chooseResult compare args).map (renameAtom permutation) := by
  cases args with
  | nil => rfl
  | cons left rest =>
      cases rest with
      | nil => rfl
      | cons right rest =>
          cases rest with
          | nil => rfl
          | cons yes rest =>
              cases rest with
              | nil => rfl
              | cons no rest =>
                  cases rest with
                  | nil =>
                      simp only [chooseResult, renameAtomList, symmetricNames permutation left right, Option.map_some]
                      split <;> rfl
                  | cons _ _ => rfl

theorem renameAtom_injective (permutation : Equiv.Perm String) : Function.Injective (renameAtom permutation) := by
  intro left right same
  have encoded := congrArg UnifyAtoms.encode same
  rw [TypeScopeRenaming.encode_rename, TypeScopeRenaming.encode_rename] at encoded
  have equal := Mettapedia.Logic.LP.UnificationRenaming.rename_injective
    (σ := UnifyAtoms.sig) permutation permutation.symm permutation.left_inv encoded
  have decoded := congrArg UnifyAtoms.decode equal
  simpa only [UnifyAtoms.decode_encode] using decoded

theorem equality_equivariant : ComparisonEquivariant (· == ·) := by
  intro permutation left right
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact (renameAtom_injective permutation).eq_iff

/-- The observed-argument dispatcher equals the primitive itself at every
reached resource-free head. It is not globally equal on resource operands. -/
theorem head_observed (active : String → Bool) (primitive : Primitive)
    (world : RetainedTypePayloads.ExternalView) (atom : Atom)
    (safe : TypeDependencyAdmission.resourceFree atom = true) :
    normalizeHead active (TypeNormalizationScope.observed world primitive) atom =
      normalizeHead active primitive atom := by
  unfold normalizeHead
  split
  next head first second rest =>
    have argsSafe : TypeDependencyAdmission.resourceFreeList (first :: second :: rest) = true := by
      simpa [TypeDependencyAdmission.resourceFree, TypeDependencyAdmission.resourceFreeList] using safe
    simp only [TypeNormalizationScope.observed, TypeDependencyAdmission.observeList_resourceFree world _ argsSafe]
  next _ => rfl

mutual
theorem normalize_observed (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (world : RetainedTypePayloads.ExternalView) : ∀ atom,
    TypeDependencyAdmission.resourceFree atom = true →
      normalize active (TypeNormalizationScope.observed world primitive) atom = normalize active primitive atom
  | .symbol _, _ => rfl
  | .var _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, safe => by
      rw [InertTypeDependencies.normalize, InertTypeDependencies.normalize]
      split
      · rfl
      · rw [normalizeList_observed active primitive closed world children safe]
        exact head_observed active primitive world _
          (TypeNormalizationScope.normalizeList_preserves active primitive closed children safe)
theorem normalizeList_observed (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (world : RetainedTypePayloads.ExternalView) : ∀ atoms,
    TypeDependencyAdmission.resourceFreeList atoms = true →
      normalizeList active (TypeNormalizationScope.observed world primitive) atoms = normalizeList active primitive atoms
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [TypeDependencyAdmission.resourceFreeList, Bool.and_eq_true] at safe
      rw [normalizeList, normalizeList, normalize_observed active primitive closed world atom safe.1,
        normalizeList_observed active primitive closed world atoms safe.2]
end

theorem normalize_observed_support (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive) (supported : ResultsSupported active primitive)
    (world : RetainedTypePayloads.ExternalView) (atom : Atom)
    (safe : TypeDependencyAdmission.resourceFree atom = true) :
    atomVariables (normalize active (TypeNormalizationScope.observed world primitive) atom) ⊆ atomVariables atom := by
  rw [normalize_observed active primitive closed world atom safe]
  exact normalize_support active primitive supported atom

theorem normalize_observed_equivariant (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive) (equivariant : Equivariant active primitive)
    (world : RetainedTypePayloads.ExternalView) (permutation : Equiv.Perm String) (atom : Atom)
    (safe : TypeDependencyAdmission.resourceFree atom = true) :
    normalize active (TypeNormalizationScope.observed world primitive) (renameAtom permutation atom) =
      renameAtom permutation (normalize active (TypeNormalizationScope.observed world primitive) atom) := by
  rw [normalize_observed active primitive closed world atom safe,
    normalize_observed active primitive closed world (renameAtom permutation atom)
      (by simpa only [TypeDependencyAdmission.rename_resourceFree] using safe)]
  exact normalize_equivariant active primitive equivariant permutation atom

/-- A supported normalization cannot introduce a name that a subsequent
fresh read might accidentally capture. The actual allocated supply is used. -/
theorem normalized_before_later_read (active : String → Bool) (primitive : Primitive)
    (supported : ResultsSupported active primitive) (supply : TypeReadSupply.Supply)
    (first second : Atom) (name : String)
    (member : name ∈ atomVariables (normalize active primitive (TypeReadSupply.fresh supply first).1)) :
    name ∉ atomVariables (TypeReadSupply.fresh (TypeReadSupply.fresh supply first).2 second).1 :=
  TypeReadSupply.later_read_is_apart supply first second name
    (normalize_support active primitive supported _ member)

theorem observed_normalized_before_later_read (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive) (supported : ResultsSupported active primitive)
    (world : RetainedTypePayloads.ExternalView) (supply : TypeReadSupply.Supply)
    (first second : Atom) (firstSafe : TypeDependencyAdmission.resourceFree first = true) (name : String)
    (member : name ∈ atomVariables
      (normalize active (TypeNormalizationScope.observed world primitive) (TypeReadSupply.fresh supply first).1)) :
    name ∉ atomVariables (TypeReadSupply.fresh (TypeReadSupply.fresh supply first).2 second).1 := by
  apply TypeReadSupply.later_read_is_apart supply first second name
  exact normalize_observed_support active primitive closed supported world _
    (by simpa only [TypeReadSupply.fresh_resourceFree] using firstSafe) member

namespace Controls

/-- A structural-equality example of the source combinators. Native alpha
comparison retains its separate comparator and codec obligation. -/
def active (head : String) : Bool := head == "==" || head == "choose-equal"

def comparisons : Primitive := fun head args =>
  if head = "==" then booleanResult (· == ·) args
  else if head = "choose-equal" then chooseResult (· == ·) args else none

theorem comparisons_supported : ResultsSupported active comparisons := by
  intro head args _ result returned
  unfold comparisons at returned
  split at returned
  · exact booleanResult_support _ args result returned
  · split at returned
    · exact chooseResult_support _ args result returned
    · contradiction

theorem comparisons_equivariant : Equivariant active comparisons := by
  intro permutation head args _
  unfold comparisons
  split
  · exact booleanResult_equivariant _ equality_equivariant permutation args
  · split
    · exact chooseResult_equivariant _ equality_equivariant permutation args
    · rfl

theorem comparisons_closed : TypeNormalizationScope.ResultsClosed active comparisons := by
  intro head args _ safe result returned
  unfold comparisons at returned
  split at returned
  · exact TypeNormalizationScope.booleanResult_closed _ args result returned
  · split at returned
    · exact TypeNormalizationScope.chooseResult_closed _ args safe result returned
    · contradiction

def selector : Atom := .expression [.symbol "choose-equal", .var "a", .var "a", .var "chosen", .var "other"]

theorem selector_returns_existing_variable : normalize active comparisons selector = .var "chosen" := by cbv

theorem selector_renames_its_result :
    normalize active comparisons (renameAtom (Equiv.swap "chosen" "renamed") selector) = .var "renamed" := by
  rw [normalize_equivariant active comparisons comparisons_equivariant, selector_returns_existing_variable]
  simp [renameAtom]

def fabricated : Primitive := fun _ _ => some (.var "invented")

theorem fabricated_is_resource_closed : TypeNormalizationScope.ResultsClosed (fun _ => true) fabricated := by
  intro head args _ _ result returned
  cases Option.some.inj returned
  rfl

theorem fabricated_is_not_supported : ¬ResultsSupported (fun _ => true) fabricated := by
  intro supported
  have impossible : "invented" ∈ atomListVariables ([] : List Atom) :=
    supported "make" [] rfl (.var "invented") rfl (by simp [atomVariables])
  cases impossible

theorem fabricated_is_not_equivariant : ¬Equivariant (fun _ => true) fabricated := by
  intro symmetricNames
  have impossible := symmetricNames (Equiv.swap "invented" "renamed") "make" [] rfl
  simp [fabricated, renameAtom] at impossible

theorem resource_free_normalization_can_fabricate_a_variable :
    let input : Atom := .expression [.symbol "make", .symbol "A", .symbol "B"]
    TypeDependencyAdmission.resourceFree input = true ∧ atomVariables input = [] ∧
      normalize (fun _ => true) fabricated input = .var "invented" := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationNames
