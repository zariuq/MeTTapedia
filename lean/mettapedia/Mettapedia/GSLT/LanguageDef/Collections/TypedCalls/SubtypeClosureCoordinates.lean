import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadWorlds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeAlphaComparison

/-!
# Private coordinates of subtype-closure states

Renaming changes type-variable coordinates, not occurrence order, parent
indices, error flags or the frontier. The pre-round membership and ancestor
tests commute with a common permutation. This is the structural boundary
needed to compose freshly instantiated queries across closure rounds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SubtypeClosureCoordinates

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open SubtypeClosureRounds
open TypeReadSupply (Supply)
open private atomVariables_eq_typeVars from Mettapedia.Languages.MeTTa.HE.EquationFreshening

def renameEntry (names : Equiv.Perm String) (entry : Entry) : Entry :=
  { entry with type_ := renameAtom names entry.type_ }

def renameState (names : Equiv.Perm String) (state : State) : State :=
  { state with known := state.known.map (renameEntry names) }

def entryNames (entries : List Entry) : List String := atomListVariables (entries.map Entry.type_)

theorem variables_member {entry : Entry} {entries : List Entry} (present : entry ∈ entries) :
    atomVariables entry.type_ ⊆ entryNames entries := by
  intro name occurs
  simp only [entryNames, atomListVariables_eq_flatMap, List.mem_flatMap]
  exact ⟨entry.type_, List.mem_map.mpr ⟨entry, present, rfl⟩, occurs⟩

theorem variables_mono {first second : List Entry} (included : first ⊆ second) :
    entryNames first ⊆ entryNames second := by
  intro name occurs
  simp only [entryNames, atomListVariables_eq_flatMap, List.mem_flatMap, List.mem_map] at occurs
  obtain ⟨_, ⟨entry, present, rfl⟩, here⟩ := occurs
  exact variables_member (included present) here

theorem variables_append (first second : List Entry) :
    entryNames (first ++ second) = entryNames first ++ entryNames second := by
  simp only [entryNames, List.map_append, atomListVariables_append]

theorem variables_rename (names : Equiv.Perm String) (entries : List Entry) :
    entryNames (entries.map (renameEntry names)) = (entryNames entries).map names := by
  change atomListVariables (entries.map (renameEntry names) |>.map Entry.type_) = _
  have values : (entries.map (renameEntry names)).map Entry.type_ =
      (entries.map Entry.type_).map (renameAtom names) := by simp [List.map_map, renameEntry]
  rw [values, ← renameAtomList_eq_map, TypeReadSupply.variablesList_rename]
  rfl

theorem entry_rename_agrees (first second : Equiv.Perm String) (live : List String)
    (agrees : ∀ name ∈ live, first name = second name) (entry : Entry)
    (covered : atomVariables entry.type_ ⊆ live) : renameEntry first entry = renameEntry second entry := by
  have same := TypeReadWorlds.retained_term_unchanged second first live agrees entry.type_
    (by simpa only [atomVariables_eq_typeVars] using covered)
  simp only [renameEntry, same]

theorem entries_rename_agrees (first second : Equiv.Perm String) (live : List String)
    (agrees : ∀ name ∈ live, first name = second name) (entries : List Entry)
    (covered : entryNames entries ⊆ live) :
    entries.map (renameEntry first) = entries.map (renameEntry second) := by
  apply List.map_congr_left
  intro entry present
  exact entry_rename_agrees first second live agrees entry
    (fun _ member => covered (variables_member present member))

theorem state_rename_agrees (first second : Equiv.Perm String) (live : List String)
    (agrees : ∀ name ∈ live, first name = second name) (state : State)
    (covered : entryNames state.known ⊆ live) : renameState first state = renameState second state := by
  simp only [renameState, entries_rename_agrees first second live agrees state.known covered]

def AlphaEquivariant (alpha : Atom → Atom → Bool) : Prop :=
  ∀ (names : Equiv.Perm String) left right,
    alpha (renameAtom names left) (renameAtom names right) = alpha left right

theorem actual_alpha_equivariant : AlphaEquivariant TypeAlphaComparison.check :=
  TypeAlphaComparison.equivariant

theorem repeatsAncestor_rename (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (names : Equiv.Perm String) (known : List Entry) (type_ : Atom) (fuel : Nat) : ∀ index,
    repeatsAncestor alpha (known.map (renameEntry names)) (renameAtom names type_) fuel index =
      repeatsAncestor alpha known type_ fuel index := by
  induction fuel with
  | zero => intro index; rfl
  | succ fuel ih =>
      intro index
      simp only [repeatsAncestor, List.getElem?_map]
      cases found : known[index]? with
      | none => rfl
      | some entry =>
          simp only [Option.map_some, renameEntry, equivariant names]
          cases entry.parent <;> simp only [ih]

theorem accept_rename (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (names : Equiv.Perm String) (state : State) (parent : Nat) (type_ : Atom) :
    accept alpha (renameState names state) parent (renameAtom names type_) = accept alpha state parent type_ := by
  simp only [accept, renameState, List.any_map, Function.comp_def, renameEntry,
    TypeNormalizationNames.equality_equivariant names, List.length_map,
    repeatsAncestor_rename alpha equivariant]

def attachParent (parent : Nat) (types : List Atom) : List Entry :=
  types.map fun type_ => ⟨type_, some parent, false⟩

theorem attachParent_names (parent : Nat) (types : List Atom) :
    entryNames (attachParent parent types) = atomListVariables types := by
  simp [entryNames, attachParent, List.map_map, Function.comp_def]

theorem filtered_names (parent : Nat) (types : List Atom) (keep : Atom → Bool) :
    entryNames (attachParent parent (types.filter keep)) ⊆ atomListVariables types := by
  rw [attachParent_names]
  intro name member
  simp only [atomListVariables_eq_flatMap, List.mem_flatMap] at member ⊢
  obtain ⟨type_, present, occurs⟩ := member
  exact ⟨type_, List.mem_of_mem_filter present, occurs⟩

theorem accepted_rename (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (names : Equiv.Perm String) (state : State) (parent : Nat) (types : List Atom) :
    attachParent parent ((types.map (renameAtom names)).filter
      (accept alpha (renameState names state) parent)) =
      (attachParent parent (types.filter (accept alpha state parent))).map (renameEntry names) := by
  simp only [List.filter_map, Function.comp_def, accept_rename alpha equivariant]
  simp [attachParent, List.map_map, renameEntry]

/-- The ordered returned entries and their protected names share one map.
Private allocations not exposed by the result need not be paired. -/
def EntriesRelated (previous : Equiv.Perm String) (live : List String)
    (first second : List Entry × Supply) : Prop :=
  ∃ next : Equiv.Perm String,
    (∀ name ∈ live, next name = previous name) ∧
    second.1 = first.1.map (renameEntry next) ∧
    (live ++ entryNames first.1) ⊆ first.2.used ∧
    (live ++ entryNames first.1).map next ⊆ second.2.used

theorem empty_related (previous : Equiv.Perm String) (live : List String)
    (first second : Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) :
    EntriesRelated previous live ([], first) ([], second) := by
  exact ⟨previous, fun _ _ => rfl, rfl,
    by simpa only [entryNames, List.map_nil, atomListVariables, List.append_nil] using firstProtected,
    by simpa only [entryNames, List.map_nil, atomListVariables, List.append_nil] using secondProtected⟩

theorem accepted_related (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (previous : Equiv.Perm String) (live : List String) (before : State)
    (covered : entryNames before.known ⊆ live) (parent : Nat)
    (first second : List Atom × Supply) (related : TypeReadWorlds.ResultRelated previous live first second) :
    EntriesRelated previous live
      (attachParent parent (first.1.filter (accept alpha before parent)), first.2)
      (attachParent parent (second.1.filter (accept alpha (renameState previous before) parent)), second.2) := by
  obtain ⟨next, agrees, carried, firstProtected, secondProtected⟩ := related
  have fixed := state_rename_agrees next previous live agrees before covered
  have acceptedNames := filtered_names parent first.1 (accept alpha before parent)
  refine ⟨next, agrees, ?_, ?_, ?_⟩
  · rw [carried, ← fixed]
    exact accepted_rename alpha equivariant next before parent first.1
  · intro name member
    apply firstProtected
    rcases List.mem_append.mp member with old | added
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (acceptedNames added)
  · intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    apply secondProtected
    apply List.mem_map.mpr
    refine ⟨original, ?_, rfl⟩
    rcases List.mem_append.mp present with old | added
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (acceptedNames added)

theorem append_related (previous middle : Equiv.Perm String) (live : List String)
    (firstPrefix secondPrefix : List Entry) (firstTail secondTail : List Entry × Supply)
    (firstAgrees : ∀ name ∈ live, middle name = previous name)
    (prefixCarried : secondPrefix = firstPrefix.map (renameEntry middle))
    (later : EntriesRelated middle (live ++ entryNames firstPrefix) firstTail secondTail) :
    EntriesRelated previous live (firstPrefix ++ firstTail.1, firstTail.2)
      (secondPrefix ++ secondTail.1, secondTail.2) := by
  obtain ⟨next, agrees, carried, firstProtected, secondProtected⟩ := later
  have prefixSame : firstPrefix.map (renameEntry next) = firstPrefix.map (renameEntry middle) :=
    entries_rename_agrees next middle (live ++ entryNames firstPrefix) agrees firstPrefix
      (fun _ member => List.mem_append_right _ member)
  refine ⟨next, fun name member => (agrees name (List.mem_append_left _ member)).trans (firstAgrees name member), ?_, ?_, ?_⟩
  · simp only [List.map_append, prefixSame, ← prefixCarried, carried]
  · simpa only [variables_append, List.append_assoc] using firstProtected
  · simpa only [variables_append, List.append_assoc] using secondProtected

def renameOutcome (names : Equiv.Perm String) : Outcome → Outcome
  | .complete state => .complete (renameState names state)
  | .unfinished state => .unfinished (renameState names state)

/-- Completion status is part of the observation, not an erased flag. -/
def OutcomeRelated (previous : Equiv.Perm String) (live : List String)
    (first second : Outcome × Supply) : Prop :=
  ∃ next : Equiv.Perm String,
    (∀ name ∈ live, next name = previous name) ∧
    second.1 = renameOutcome next first.1 ∧
    (live ++ entryNames first.1.state.known) ⊆ first.2.used ∧
    (live ++ entryNames first.1.state.known).map next ⊆ second.2.used

theorem OutcomeRelated.restrict_base {previous middle : Equiv.Perm String} {live larger : List String}
    {first second : Outcome × Supply}
    (related : OutcomeRelated middle larger first second)
    (included : live ⊆ larger) (agrees : ∀ name ∈ live, middle name = previous name) :
    OutcomeRelated previous live first second := by
  obtain ⟨next, nextAgrees, carried, firstProtected, secondProtected⟩ := related
  have smaller : live ++ entryNames first.1.state.known ⊆ larger ++ entryNames first.1.state.known := by
    intro name member
    rcases List.mem_append.mp member with old | current
    · exact List.mem_append_left _ (included old)
    · exact List.mem_append_right _ current
  refine ⟨next, fun name member => (nextAgrees name (included member)).trans (agrees name member),
    carried, fun _ member => firstProtected (smaller member), ?_⟩
  intro name member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact secondProtected (List.mem_map.mpr ⟨original, smaller present, rfl⟩)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SubtypeClosureCoordinates
