import Mettapedia.Machines.ReadOnlyQueryWorldRelation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeClosureReadWorlds

/-!
# Growing private-coordinate worlds for the actual type-query plans

The world is proof metadata: a variable permutation and the names whose
meaning must already be preserved. It is not another runtime binding store.
Original source-value inquiries remain fixed; generated closure seeds may
contain freshly allocated type variables and are transported by the world.
Returned type families keep order, duplicates and shared variables.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryWorlds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph TypeDependencyAdmission
open TypeReadSupply (Supply)
open private atomVariables_eq_typeVars from Mettapedia.Languages.MeTTa.HE.EquationFreshening

structure Coordinates where
  names : Equiv.Perm String
  live : List String

def Grows (before after : Coordinates) : Prop :=
  before.live ⊆ after.live ∧ ∀ name ∈ before.live, after.names name = before.names name

theorem grows_refl (world : Coordinates) : Grows world world := ⟨fun _ member => member, fun _ _ => rfl⟩

theorem grows_trans {first middle last : Coordinates} (before : Grows first middle) (after : Grows middle last) :
    Grows first last :=
  ⟨fun _ member => after.1 (before.1 member), fun name member =>
    (after.2 name (before.1 member)).trans (before.2 name member)⟩

def Protected (world : Coordinates) (first second : Supply) : Prop :=
  world.live ⊆ first.used ∧ world.live.map world.names ⊆ second.used

def TypesRelated (world : Coordinates) (first second : List Atom) : Prop :=
  resourceFreeList first = true ∧ atomListVariables first ⊆ world.live ∧
    second = first.map (renameAtom world.names)

theorem types_mono {before after : Coordinates} (grown : Grows before after) {first second : List Atom}
    (related : TypesRelated before first second) : TypesRelated after first second := by
  refine ⟨related.1, fun _ member => grown.1 (related.2.1 member), ?_⟩
  rw [related.2.2]
  exact (TypeReadWorlds.list_rename_agrees after.names before.names first
    (fun name member => grown.2 name (related.2.1 member))).symm

def BindingRelated (world : Coordinates) (first second : TypeScopeMatcher.State) : Prop :=
  TypeScopeMatcher.SafeState first ∧ TypeReadWorlds.Supported world.live first ∧
    second = TypeScopeRenaming.renameState world.names first

theorem binding_mono {before after : Coordinates} (grown : Grows before after)
    {first second : TypeScopeMatcher.State} (related : BindingRelated before first second) :
    BindingRelated after first second := by
  refine ⟨related.1, TypeReadWorlds.supported_mono related.2.1 grown.1, ?_⟩
  rw [related.2.2]
  exact (TypeReadWorlds.supported_readout before.live first related.2.1 before.names after.names grown.2).symm

def Fixed (world : Coordinates) (names : List String) : Prop :=
  names ⊆ world.live ∧ ∀ name ∈ names, world.names name = name

theorem fixed_mono {before after : Coordinates} (grown : Grows before after) {names : List String}
    (fixed : Fixed before names) : Fixed after names :=
  ⟨fun _ member => grown.1 (fixed.1 member), fun name member =>
    (grown.2 name (fixed.1 member)).trans (fixed.2 name member)⟩

theorem fixed_subset {world : Coordinates} {names smaller : List String}
    (fixed : Fixed world names) (included : smaller ⊆ names) : Fixed world smaller :=
  ⟨fun _ member => fixed.1 (included member), fun name member => fixed.2 name (included member)⟩

def AtomRelated (world : Coordinates) (first second : Atom) : Prop :=
  resourceFree first = true ∧ atomVariables first ⊆ world.live ∧ second = renameAtom world.names first

theorem atom_mono {before after : Coordinates} (grown : Grows before after) {first second : Atom}
    (related : AtomRelated before first second) : AtomRelated after first second := by
  refine ⟨related.1, fun _ member => grown.1 (related.2.1 member), ?_⟩
  rw [related.2.2]
  exact (TypeReadWorlds.retained_term_unchanged before.names after.names before.live grown.2 first
    (by simpa only [atomVariables_eq_typeVars] using related.2.1)).symm

theorem types_member {world : Coordinates} {first second : List Atom}
    (related : TypesRelated world first second) {atom : Atom} (present : atom ∈ first) :
    AtomRelated world atom (renameAtom world.names atom) := by
  refine ⟨(resourceFreeList_iff _).mp related.1 atom present, ?_, rfl⟩
  intro name member
  apply related.2.1
  rw [atomListVariables_eq_flatMap]
  exact List.mem_flatMap.mpr ⟨atom, present, member⟩

theorem types_tail {world : Coordinates} {head : Atom} {tail second : List Atom}
    (related : TypesRelated world (head :: tail) second) :
    TypesRelated world tail (tail.map (renameAtom world.names)) := by
  have safe := (Bool.and_eq_true_iff.mp related.1).2
  refine ⟨safe, ?_, rfl⟩
  intro name member
  exact related.2.1 (List.mem_append_right _ member)

theorem types_cons {world : Coordinates} {firstHead secondHead : Atom} {firstTail secondTail : List Atom}
    (head : AtomRelated world firstHead secondHead) (tail : TypesRelated world firstTail secondTail) :
    TypesRelated world (firstHead :: firstTail) (secondHead :: secondTail) := by
  refine ⟨Bool.and_eq_true_iff.mpr ⟨head.1, tail.1⟩, ?_, ?_⟩
  · intro name member
    rcases List.mem_append.mp member with first | rest
    · exact head.2.1 first
    · exact tail.2.1 rest
  · simp only [List.map_cons, ← head.2.2, ← tail.2.2]

theorem fixed_head {world : Coordinates} {head : Atom} {tail : List Atom}
    (fixed : Fixed world (atomListVariables (head :: tail))) : Fixed world (atomVariables head) :=
  fixed_subset fixed (fun _ member => List.mem_append_left _ member)

theorem fixed_tail {world : Coordinates} {head : Atom} {tail : List Atom}
    (fixed : Fixed world (atomListVariables (head :: tail))) : Fixed world (atomListVariables tail) :=
  fixed_subset fixed (fun _ member => List.mem_append_right _ member)

theorem fixed_member {world : Coordinates} {values : List Atom}
    (fixed : Fixed world (atomListVariables values)) {value : Atom} (present : value ∈ values) :
    Fixed world (atomVariables value) := by
  apply fixed_subset fixed
  intro name member
  rw [atomListVariables_eq_flatMap]
  exact List.mem_flatMap.mpr ⟨value, present, member⟩

def questionNames : Question → List String
  | .inl (.annotations atom) | .inl (.intrinsic atom) | .inl (.kind atom) => atomVariables atom
  | .inl (.classify head values) => atomVariables head ++ atomListVariables values
  | .inl (.closure seeds) => atomListVariables seeds
  | .inr (.infer _ atom) | .inr (.tuplePart _ atom) | .inr (.operatorRows atom) => atomVariables atom

/-- Only closure inquiries contain generated type syntax. Other keys are
the fixed source operands of this invocation, not independently renamed code. -/
def KeysRelated (world : Coordinates) (first second : Question) : Prop :=
  match first with
  | .inl (.closure seeds) => ∃ other, second = .inl (.closure other) ∧ TypesRelated world seeds other
  | _ => second = first ∧ Fixed world (questionNames first)

theorem keys_mono {before after : Coordinates} (grown : Grows before after) {first second : Question}
    (related : KeysRelated before first second) : KeysRelated after first second := by
  cases first with
  | inr call => exact ⟨related.1, fixed_mono grown related.2⟩
  | inl key =>
      cases key with
      | closure seeds =>
          obtain ⟨other, same, carried⟩ := related
          exact ⟨other, same, types_mono grown carried⟩
      | annotations _ | intrinsic _ | kind _ | classify _ _ => exact ⟨related.1, fixed_mono grown related.2⟩

inductive RepliesRelated (world : Coordinates) : Reply → Reply → Prop where
  | types {first second} : TypesRelated world first second → RepliesRelated world (.types first) (.types second)
  | kind (kind : Atom) : RepliesRelated world (.kind kind) (.kind kind)
  | class_ (kind : NativeTypeViews.HeadClass) : RepliesRelated world (.class_ kind) (.class_ kind)

theorem replies_mono {before after : Coordinates} (grown : Grows before after) {first second : Reply}
    (related : RepliesRelated before first second) : RepliesRelated after first second := by
  cases related with
  | types types => exact .types (types_mono grown types)
  | kind kind => exact .kind kind
  | class_ kind => exact .class_ kind

def worlds : Mettapedia.Machines.ReadOnlyQueryWorldRelation.Worlds Coordinates Question Reply where
  grows := Grows
  grows_refl := grows_refl
  grows_trans := grows_trans
  keys := KeysRelated
  replies := RepliesRelated
  keys_mono := keys_mono
  replies_mono := replies_mono

def viewWorlds : Mettapedia.Machines.ReadOnlyQueryWorldRelation.Worlds Coordinates
    (NativeTypeDemand.Question Atom) Reply where
  grows := Grows
  grows_refl := grows_refl
  grows_trans := grows_trans
  keys world first second := KeysRelated world (viewQuestion first) (viewQuestion second)
  replies := RepliesRelated
  keys_mono := fun {_ _} grown {_ _} related => keys_mono grown related
  replies_mono := replies_mono

inductive CheckedRelated {Value : Type} (related : Value → Value → Prop) :
    Except Unit Value → Except Unit Value → Prop where
  | error : CheckedRelated related (.error ()) (.error ())
  | ok {first second} : related first second → CheckedRelated related (.ok first) (.ok second)

def BindingAnswers (world : Coordinates) : Except Unit (Option TypeScopeMatcher.State) →
    Except Unit (Option TypeScopeMatcher.State) → Prop :=
  CheckedRelated (Option.Rel (BindingRelated world))

def TypeAnswers (world : Coordinates) : Except Unit (List Atom) → Except Unit (List Atom) → Prop :=
  CheckedRelated (TypesRelated world)

theorem atom_fixed (world : Coordinates) (atom : Atom) (fixed : Fixed world (atomVariables atom)) :
    renameAtom world.names atom = atom :=
  TypeFreshReadEquivalence.expected_fixed world.names (atomVariables atom) fixed.2
    atom (by simp only [atomVariables_eq_typeVars]; exact fun _ member => member)

/-- The actual occurrence-read relation supplies a valid larger world.
Unused private allocations in either supply are deliberately not identified. -/
theorem world_of_type_read (before : Coordinates) (first second : List Atom × Supply)
    (safe : resourceFreeList first.1 = true)
    (related : TypeReadWorlds.ResultRelated before.names before.live first second) :
    ∃ after : Coordinates, Grows before after ∧ Protected after first.2 second.2 ∧
      TypesRelated after first.1 second.1 := by
  obtain ⟨names, agrees, carried, firstKeeps, secondKeeps⟩ := related
  exact ⟨⟨names, before.live ++ atomListVariables first.1⟩,
    ⟨fun _ member => List.mem_append_left _ member, agrees⟩, ⟨firstKeeps, secondKeeps⟩,
    ⟨safe, fun _ member => List.mem_append_right _ member, carried⟩⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryWorlds
