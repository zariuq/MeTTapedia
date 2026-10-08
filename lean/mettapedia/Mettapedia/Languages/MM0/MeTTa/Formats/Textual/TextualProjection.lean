import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualData
import Mettapedia.Languages.MM0.MeTTa.Admission.SpecificationMatching

/-!
# Ordered MM0 frontend projection

Source names are resolved against their preceding ordered environments.
Sort namespace IDs are dense list positions, independently of source trace
positions. Projection produces the existing kernel specification entries,
binders and contexts. Kernel declaration admission remains separate.

These are structural data laws. Correspondence with an authored MeTTa
projection program requires an additional execution proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TextualProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Kernel (SortInfo Binder Context SpecificationEntry)
open TextualData (SortEntry)

def sortIndex? (entries : List SortEntry) (name : String) : Option Nat :=
  entries.findIdx? (fun entry => entry.name == name)

def sortRows (entries : List SortEntry) : List (Nat × SortInfo) :=
  entries.zipIdx.map (fun row => (row.2, row.1.info))

def sortSpecification (entries : List SortEntry) : List SpecificationEntry :=
  entries.zipIdx.map (fun row => .sort row.2 row.1.info)

/-- A canonical sort environment contains one row per admitted source name. -/
def projectSorts (entries : List SortEntry) : Option (List SpecificationEntry) :=
  if (entries.map SortEntry.name).Nodup then some (sortSpecification entries) else none

/-- A full environment lookup retains its dense ID while checking source scope. -/
def sortIndexBefore? (entries : List SortEntry) (sourcePosition : Nat) (name : String) : Option Nat := do
  let index ← sortIndex? entries name
  let entry ← entries[index]?
  if entry.sourcePosition < sourcePosition then some index else none

theorem sortIndex_sound {entries : List SortEntry} {name : String} {index : Nat}
    (found : sortIndex? entries name = some index) :
    ∃ entry, entries[index]? = some entry ∧ entry.name = name := by
  obtain ⟨bound, matched, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  exact ⟨entries[index], List.getElem?_eq_getElem bound, by simpa using matched⟩

theorem sortIndex_complete {entries : List SortEntry}
    (unique : (entries.map SortEntry.name).Nodup) {entry : SortEntry} {index : Nat}
    (found : entries[index]? = some entry) : sortIndex? entries entry.name = some index := by
  obtain ⟨bound, atIndex⟩ := List.getElem?_eq_some_iff.mp found
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨bound, by simp [atIndex], ?_⟩
  intro previous earlier
  simp only [beq_iff_eq]
  intro same
  have previousBound : previous < (entries.map SortEntry.name).length := by
    simpa using Nat.lt_trans earlier bound
  have indexBound : index < (entries.map SortEntry.name).length := by simpa using bound
  have equalNames : (entries.map SortEntry.name)[previous]'previousBound =
      (entries.map SortEntry.name)[index]'indexBound := by
    simp [List.getElem_map, atIndex, same]
  have equalIndices : previous = index := unique.getElem_inj_iff.mp equalNames
  omega

theorem sortIndex_iff {entries : List SortEntry}
    (unique : (entries.map SortEntry.name).Nodup) (name : String) (index : Nat) :
    sortIndex? entries name = some index ↔
      ∃ entry, entries[index]? = some entry ∧ entry.name = name := by
  constructor
  · exact sortIndex_sound
  · rintro ⟨entry, found, rfl⟩
    exact sortIndex_complete unique found

theorem sortIndexBefore_sound {entries : List SortEntry} {sourcePosition index : Nat} {name : String}
    (found : sortIndexBefore? entries sourcePosition name = some index) :
    sortIndex? entries name = some index ∧
      ∃ entry, entries[index]? = some entry ∧ entry.name = name ∧ entry.sourcePosition < sourcePosition := by
  obtain ⟨denseIndex, indexFound, afterIndex⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨entry, entryFound, afterEntry⟩ := Option.bind_eq_some_iff.mp afterIndex
  split at afterEntry
  · rename_i earlier
    have sameIndex : denseIndex = index := by simpa using afterEntry
    subst index
    obtain ⟨stored, storedFound, named⟩ := sortIndex_sound indexFound
    have sameEntry : stored = entry := Option.some.inj (storedFound.symm.trans entryFound)
    subst stored
    exact ⟨indexFound, entry, entryFound, named, earlier⟩
  · simp at afterEntry

theorem sortIndexBefore_iff (entries : List SortEntry) (sourcePosition : Nat) (name : String) (index : Nat) :
    sortIndexBefore? entries sourcePosition name = some index ↔
      sortIndex? entries name = some index ∧
        ∃ entry, entries[index]? = some entry ∧ entry.sourcePosition < sourcePosition := by
  constructor
  · intro found
    obtain ⟨resolved, entry, row, _, earlier⟩ := sortIndexBefore_sound found
    exact ⟨resolved, entry, row, earlier⟩
  · rintro ⟨resolved, entry, row, earlier⟩
    simp [sortIndexBefore?, resolved, row, earlier]

theorem sortIndex_missing_iff (entries : List SortEntry) (name : String) :
    sortIndex? entries name = none ↔ ∀ entry ∈ entries, entry.name ≠ name := by
  simp [sortIndex?, List.findIdx?_eq_none_iff]

@[simp] theorem sortSpecification_getElem? (entries : List SortEntry) (index : Nat) :
    (sortSpecification entries)[index]? =
      (entries[index]?).map (fun entry => .sort index entry.info) := by
  simp [sortSpecification, List.getElem?_zipIdx, Option.map_map, Function.comp_def]

@[simp] theorem sortRows_getElem? (entries : List SortEntry) (index : Nat) :
    (sortRows entries)[index]? = (entries[index]?).map (fun entry => (index, entry.info)) := by
  simp [sortRows, List.getElem?_zipIdx, Option.map_map, Function.comp_def]

theorem sortIndex_specification_alignment {entries : List SortEntry} {name : String} {index : Nat}
    (found : sortIndex? entries name = some index) :
    ∃ entry, entries[index]? = some entry ∧ entry.name = name ∧
      (sortSpecification entries)[index]? = some (.sort index entry.info) := by
  obtain ⟨entry, atIndex, named⟩ := sortIndex_sound found
  exact ⟨entry, atIndex, named, by simp [atIndex]⟩

theorem sortRows_dense_ids (entries : List SortEntry) :
    (sortRows entries).map Prod.fst = List.range entries.length := by
  simp [sortRows, List.map_map, Function.comp_def, List.range_eq_range']

theorem sortRows_unique_ids (entries : List SortEntry) :
    ((sortRows entries).map Prod.fst).Nodup := by
  rw [sortRows_dense_ids]
  exact List.nodup_range

theorem sortRows_no_skipped_ids (entries : List SortEntry) (index : Nat) :
    index ∈ (sortRows entries).map Prod.fst ↔ index < entries.length := by
  rw [sortRows_dense_ids]
  exact List.mem_range

theorem projectSorts_iff (entries : List SortEntry) (specification : List SpecificationEntry) :
    projectSorts entries = some specification ↔
      (entries.map SortEntry.name).Nodup ∧ sortSpecification entries = specification := by
  by_cases unique : (entries.map SortEntry.name).Nodup <;> simp [projectSorts, unique]

/-- Appending future declarations cannot change an already resolved name. -/
theorem sortIndex_prefix {preceding : List SortEntry} (suffix : List SortEntry) {name : String} {index : Nat}
    (found : sortIndex? preceding name = some index) :
    sortIndex? (preceding ++ suffix) name = some index := by
  change preceding.findIdx? (fun entry => entry.name == name) = some index at found
  simp [sortIndex?, List.findIdx?_append, found]

/-- The ordered sort-row prefix contains exactly its earlier dense IDs. -/
theorem sortIndex_take (entries : List SortEntry) (position : Nat) (name : String) :
    sortIndex? (entries.take position) name =
      (sortIndex? entries name).bind (Option.guard (fun index => index < position)) := by
  exact List.findIdx?_take

theorem sortIndex_before_iff (entries : List SortEntry) (position : Nat) (name : String) (index : Nat) :
    sortIndex? (entries.take position) name = some index ↔
      sortIndex? entries name = some index ∧ index < position := by
  rw [sortIndex_take]
  simp [Option.bind_eq_some_iff, Option.guard]

def sortEnvironmentValue : List SortEntry → Atom
  | [] => .symbol "MM0SortEntriesNilV1"
  | entry :: remaining => .expression [.symbol "MM0SortEntriesConsV1",
      TextualData.sortEntryValue entry, sortEnvironmentValue remaining]

def decodeSortEnvironment : Atom → Option (List SortEntry)
  | .symbol "MM0SortEntriesNilV1" => some []
  | .expression [.symbol "MM0SortEntriesConsV1", entry, remaining] => do
      let first ← TextualData.decodeSortEntry entry
      let rest ← decodeSortEnvironment remaining
      pure (first :: rest)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeSortEnvironment_sortEnvironmentValue (entries : List SortEntry) :
    decodeSortEnvironment (sortEnvironmentValue entries) = some entries := by
  induction entries with
  | nil => simp [sortEnvironmentValue, decodeSortEnvironment]
  | cons first remaining ih => simp [sortEnvironmentValue, decodeSortEnvironment, ih]

theorem decodeSortEnvironment_reflects (atom : Atom) (entries : List SortEntry)
    (decoded : decodeSortEnvironment atom = some entries) : atom = sortEnvironmentValue entries := by
  unfold decodeSortEnvironment at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i entry remaining
    obtain ⟨first, firstDecoded, afterFirst⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨rest, restDecoded, output⟩ := Option.bind_eq_some_iff.mp afterFirst
    have same : first :: rest = entries := by simpa using output
    subst entries
    rw [TextualData.decodeSortEntry_reflects entry first firstDecoded,
      decodeSortEnvironment_reflects remaining rest restDecoded]
    rfl
  · simp at decoded
termination_by sizeOf atom

/-- Source environment decoding composes with the existing specification codec. -/
theorem decoded_sorts_project_to_existing_codec (entries : List SortEntry)
    (specification : List SpecificationEntry) (projected : projectSorts entries = some specification) :
    ((decodeSortEnvironment (sortEnvironmentValue entries)).bind projectSorts).map
      SpecificationMatching.pendingValue = some (SpecificationMatching.pendingValue specification) := by
  simp [projected]

/-! ## Raw normalized binder data -/

def namesValue : List String → Atom
  | [] => .symbol "nil"
  | name :: rest =>
      .expression [.symbol "cons", TextualData.nameValue name, namesValue rest]

def decodeNames : Atom → Option (List String)
  | .symbol "nil" => some []
  | .expression [.symbol "cons", name, rest] => do
      let first ← TextualData.decodeName name
      let remaining ← decodeNames rest
      pure (first :: remaining)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeNames_namesValue (names : List String) :
    decodeNames (namesValue names) = some names := by
  induction names with
  | nil => simp [namesValue, decodeNames]
  | cons first rest ih => simp [namesValue, decodeNames, ih]

theorem decodeNames_reflects (atom : Atom) (names : List String)
    (decoded : decodeNames atom = some names) : atom = namesValue names := by
  unfold decodeNames at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i name rest
    obtain ⟨first, firstDecoded, afterFirst⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨remaining, restDecoded, output⟩ := Option.bind_eq_some_iff.mp afterFirst
    have same : first :: remaining = names := by simpa using output
    subst names
    rw [TextualData.decodeName_reflects name first firstDecoded,
      decodeNames_reflects rest remaining restDecoded]
    rfl
  · simp at decoded
termination_by sizeOf atom

/-- Named source metadata retained by the normalized `MM0TypeV1` value. -/
structure SourceType where
  sortName : String
  dependencies : List String
  deriving DecidableEq, Repr

def typeValue (typeInfo : SourceType) : Atom :=
  .expression [.symbol "MM0TypeV1", TextualData.nameValue typeInfo.sortName,
    namesValue typeInfo.dependencies]

def decodeType : Atom → Option SourceType
  | .expression [.symbol "MM0TypeV1", sortName, dependencies] => do
      let name ← TextualData.decodeName sortName
      let decodedDependencies ← decodeNames dependencies
      pure ⟨name, decodedDependencies⟩
  | _ => none

@[simp] theorem decodeType_typeValue (typeInfo : SourceType) :
    decodeType (typeValue typeInfo) = some typeInfo := by
  cases typeInfo
  simp [typeValue, decodeType]

theorem decodeType_reflects (atom : Atom) (typeInfo : SourceType)
    (decoded : decodeType atom = some typeInfo) : atom = typeValue typeInfo := by
  unfold decodeType at decoded
  split at decoded
  · rename_i sortName dependencies
    obtain ⟨name, nameDecoded, afterName⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨names, namesDecoded, output⟩ := Option.bind_eq_some_iff.mp afterName
    have same : (⟨name, names⟩ : SourceType) = typeInfo := by simpa using output
    subst typeInfo
    rw [TextualData.decodeName_reflects sortName name nameDecoded,
      decodeNames_reflects dependencies names namesDecoded]
    rfl
  · simp at decoded

/-- A source binder retains its name, without adding a kernel binder carrier. -/
structure SourceBinder where
  isBound : Bool
  name : Option String
  typeInfo : SourceType
  deriving DecidableEq, Repr

def binderKindValue : Bool → Atom
  | true => .symbol "MM0BoundBinderKindV1"
  | false => .symbol "MM0RegularBinderKindV1"

def decodeBinderKind : Atom → Option Bool
  | .symbol "MM0BoundBinderKindV1" => some true
  | .symbol "MM0RegularBinderKindV1" => some false
  | _ => none

def binderNameValue : Option String → Atom
  | none => .symbol "MM0AnonymousBinderV1"
  | some name => .expression [.symbol "MM0NamedBinderV1", TextualData.nameValue name]

def decodeBinderName : Atom → Option (Option String)
  | .symbol "MM0AnonymousBinderV1" => some none
  | .expression [.symbol "MM0NamedBinderV1", name] => (TextualData.decodeName name).map some
  | _ => none

@[simp] theorem decodeBinderKind_binderKindValue (isBound : Bool) :
    decodeBinderKind (binderKindValue isBound) = some isBound := by
  cases isBound <;> simp [binderKindValue, decodeBinderKind]

@[simp] theorem decodeBinderName_binderNameValue (name : Option String) :
    decodeBinderName (binderNameValue name) = some name := by
  cases name <;> simp [binderNameValue, decodeBinderName]

theorem decodeBinderKind_reflects (atom : Atom) (isBound : Bool)
    (decoded : decodeBinderKind atom = some isBound) : atom = binderKindValue isBound := by
  unfold decodeBinderKind at decoded
  split at decoded <;> simp_all [binderKindValue]

theorem decodeBinderName_reflects (atom : Atom) (name : Option String)
    (decoded : decodeBinderName atom = some name) : atom = binderNameValue name := by
  unfold decodeBinderName at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i sourceName
    obtain ⟨decodedName, found, same⟩ := Option.map_eq_some_iff.mp decoded
    rw [TextualData.decodeName_reflects sourceName decodedName found, ← same]
    rfl
  · simp at decoded

def binderValue (binder : SourceBinder) : Atom :=
  .expression [.symbol "MM0BinderV1", binderKindValue binder.isBound,
    binderNameValue binder.name, typeValue binder.typeInfo]

def decodeBinder : Atom → Option SourceBinder
  | .expression [.symbol "MM0BinderV1", kind, name, typeInfo] => do
      let isBound ← decodeBinderKind kind
      let decodedName ← decodeBinderName name
      let decodedType ← decodeType typeInfo
      pure ⟨isBound, decodedName, decodedType⟩
  | _ => none

@[simp] theorem decodeBinder_binderValue (binder : SourceBinder) :
    decodeBinder (binderValue binder) = some binder := by
  cases binder
  simp [binderValue, decodeBinder]

theorem decodeBinder_reflects (atom : Atom) (binder : SourceBinder)
    (decoded : decodeBinder atom = some binder) : atom = binderValue binder := by
  unfold decodeBinder at decoded
  split at decoded
  · rename_i kind name typeInfo
    obtain ⟨isBound, kindDecoded, afterKind⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨decodedName, nameDecoded, afterName⟩ := Option.bind_eq_some_iff.mp afterKind
    obtain ⟨decodedType, typeDecoded, output⟩ := Option.bind_eq_some_iff.mp afterName
    have same : (⟨isBound, decodedName, decodedType⟩ : SourceBinder) = binder := by
      simpa using output
    subst binder
    rw [decodeBinderKind_reflects kind isBound kindDecoded,
      decodeBinderName_reflects name decodedName nameDecoded,
      decodeType_reflects typeInfo decodedType typeDecoded]
    rfl
  · simp at decoded

theorem decodeBinder_iff (atom : Atom) (binder : SourceBinder) :
    decodeBinder atom = some binder ↔ atom = binderValue binder := by
  constructor
  · exact decodeBinder_reflects atom binder
  · rintro rfl
    exact decodeBinder_binderValue binder

theorem binderValue_injective : Function.Injective binderValue := by
  intro first second same
  have decoded := congrArg decodeBinder same
  simpa using decoded

/-! ## Dependency names use full preceding-context positions -/

def binderIndex? (preceding : List SourceBinder) (name : String) : Option Nat :=
  preceding.findIdx? (fun binder => binder.name == some name)

theorem binderIndex_sound {preceding : List SourceBinder} {name : String} {index : Nat}
    (found : binderIndex? preceding name = some index) :
    ∃ binder, preceding[index]? = some binder ∧ binder.name = some name := by
  obtain ⟨bound, matched, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  exact ⟨preceding[index], List.getElem?_eq_getElem bound, by simpa using matched⟩

theorem binderIndex_prefix {preceding : List SourceBinder} (suffix : List SourceBinder)
    {name : String} {index : Nat} (found : binderIndex? preceding name = some index) :
    binderIndex? (preceding ++ suffix) name = some index := by
  change preceding.findIdx? (fun binder => binder.name == some name) = some index at found
  simp [binderIndex?, List.findIdx?_append, found]

theorem binderIndex_take (binders : List SourceBinder) (position : Nat) (name : String) :
    binderIndex? (binders.take position) name =
      (binderIndex? binders name).bind (Option.guard (fun index => index < position)) := by
  exact List.findIdx?_take

/-- Kind checking follows first-name lookup, so an earlier regular binder is
never skipped in favor of a later bound binder with the same source name. -/
def boundIndex? (preceding : List SourceBinder) (name : String) : Option Nat := do
  let index ← binderIndex? preceding name
  let binder ← preceding[index]?
  if binder.isBound then some index else none

theorem boundIndex_sound {preceding : List SourceBinder} {name : String} {index : Nat}
    (found : boundIndex? preceding name = some index) :
    ∃ binder, preceding[index]? = some binder ∧ binder.isBound = true ∧ binder.name = some name := by
  obtain ⟨denseIndex, indexFound, afterIndex⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨binder, binderFound, afterBinder⟩ := Option.bind_eq_some_iff.mp afterIndex
  split at afterBinder
  · rename_i isBound
    have sameIndex : denseIndex = index := by simpa using afterBinder
    subst index
    obtain ⟨stored, storedFound, named⟩ := binderIndex_sound indexFound
    have sameBinder : stored = binder := Option.some.inj (storedFound.symm.trans binderFound)
    subst stored
    exact ⟨binder, binderFound, isBound, named⟩
  · simp at afterBinder

theorem boundIndex_take (binders : List SourceBinder) (position : Nat) (name : String) :
    boundIndex? (binders.take position) name =
      (boundIndex? binders name).bind (Option.guard (fun index => index < position)) := by
  unfold boundIndex?
  rw [binderIndex_take]
  cases resolved : binderIndex? binders name with
  | none => simp
  | some index =>
      obtain ⟨binder, atIndex, _⟩ := binderIndex_sound resolved
      by_cases earlier : index < position
      · have atTake : (binders.take position)[index]? = some binder := by
          rw [List.getElem?_take_of_lt earlier, atIndex]
        cases kind : binder.isBound <;> simp [Option.guard, earlier, atIndex, atTake, kind]
      · cases kind : binder.isBound <;> simp [Option.guard, earlier, atIndex, kind]

theorem boundIndex_before_iff (binders : List SourceBinder) (position : Nat) (name : String) (index : Nat) :
    boundIndex? (binders.take position) name = some index ↔
      boundIndex? binders name = some index ∧ index < position := by
  rw [boundIndex_take]
  simp [Option.bind_eq_some_iff, Option.guard]

def dependencyIndices? (preceding : List SourceBinder) : List String → Option (List Nat)
  | [] => some []
  | name :: remaining => do
      let index ← boundIndex? preceding name
      let rest ← dependencyIndices? preceding remaining
      pure (index :: rest)

def dependencies? (preceding : List SourceBinder) (names : List String) : Option (Finset Nat) :=
  (dependencyIndices? preceding names).map List.toFinset

theorem dependencyIndices_length {preceding : List SourceBinder} {names : List String} {indices : List Nat}
    (resolved : dependencyIndices? preceding names = some indices) : indices.length = names.length := by
  induction names generalizing indices with
  | nil => simp [dependencyIndices?] at resolved; subst indices; rfl
  | cons name remaining ih =>
      obtain ⟨index, _, afterIndex⟩ := Option.bind_eq_some_iff.mp resolved
      obtain ⟨rest, restResolved, output⟩ := Option.bind_eq_some_iff.mp afterIndex
      have same : index :: rest = indices := by simpa using output
      subst indices
      simp [ih restResolved]

theorem dependencyIndices_bound {preceding : List SourceBinder} {names : List String} {indices : List Nat}
    (resolved : dependencyIndices? preceding names = some indices) {index : Nat} (member : index ∈ indices) :
    ∃ name ∈ names, ∃ binder, preceding[index]? = some binder ∧
      binder.isBound = true ∧ binder.name = some name := by
  induction names generalizing indices with
  | nil => simp [dependencyIndices?] at resolved; subst indices; simp at member
  | cons name remaining ih =>
      obtain ⟨first, firstFound, afterFirst⟩ := Option.bind_eq_some_iff.mp resolved
      obtain ⟨rest, restResolved, output⟩ := Option.bind_eq_some_iff.mp afterFirst
      have same : first :: rest = indices := by simpa using output
      subst indices
      rcases List.mem_cons.mp member with equal | inRest
      · subst index
        obtain ⟨binder, atIndex, bound, named⟩ := boundIndex_sound firstFound
        exact ⟨name, by simp, binder, atIndex, bound, named⟩
      · obtain ⟨dependency, present, binder, atIndex, bound, named⟩ := ih restResolved inRest
        exact ⟨dependency, by simp [present], binder, atIndex, bound, named⟩

theorem dependencies_bound {preceding : List SourceBinder} {names : List String} {dependencies : Finset Nat}
    (resolved : dependencies? preceding names = some dependencies) {index : Nat}
    (member : index ∈ dependencies) :
    ∃ name ∈ names, ∃ binder, preceding[index]? = some binder ∧
      binder.isBound = true ∧ binder.name = some name := by
  obtain ⟨indices, found, same⟩ := Option.map_eq_some_iff.mp resolved
  subst dependencies
  exact dependencyIndices_bound found (by simpa using member)

def projectBinder (sorts : List SortEntry) (preceding : List SourceBinder)
    (binder : SourceBinder) : Option Binder := do
  let sort ← sortIndex? sorts binder.typeInfo.sortName
  if binder.isBound then
    if binder.typeInfo.dependencies.isEmpty then some (.bound sort) else none
  else do
    let dependencies ← dependencies? preceding binder.typeInfo.dependencies
    pure (.regular sort dependencies)

theorem projectBinder_kind {sorts : List SortEntry} {preceding : List SourceBinder}
    {source : SourceBinder} {target : Binder} (projected : projectBinder sorts preceding source = some target) :
    (match target with | .bound _ => true | .regular _ _ => false) = source.isBound := by
  obtain ⟨sort, _, afterSort⟩ := Option.bind_eq_some_iff.mp projected
  cases kind : source.isBound with
  | true =>
      simp [kind] at afterSort
      obtain ⟨_, same⟩ := afterSort
      subst target
      rfl
  | false =>
      simp only [kind, Bool.false_eq_true, ↓reduceIte] at afterSort
      obtain ⟨dependencies, _, output⟩ := Option.bind_eq_some_iff.mp afterSort
      have same : Binder.regular sort dependencies = target := by simpa using output
      subst target
      rfl

theorem projectBinder_regular_dependencies {sorts : List SortEntry} {preceding : List SourceBinder}
    {source : SourceBinder} {sort : Nat} {dependencies : Finset Nat}
    (projected : projectBinder sorts preceding source = some (.regular sort dependencies)) :
    dependencies? preceding source.typeInfo.dependencies = some dependencies := by
  obtain ⟨resolvedSort, _, afterSort⟩ := Option.bind_eq_some_iff.mp projected
  cases kind : source.isBound with
  | true => simp [kind] at afterSort
  | false =>
      simp only [kind, Bool.false_eq_true, ↓reduceIte] at afterSort
      obtain ⟨resolvedDependencies, resolved, output⟩ := Option.bind_eq_some_iff.mp afterSort
      have parts : resolvedSort = sort ∧ resolvedDependencies = dependencies := by
        simpa using output
      exact parts.2 ▸ resolved

theorem dependencies_before {preceding : List SourceBinder} {names : List String} {dependencies : Finset Nat}
    (resolved : dependencies? preceding names = some dependencies) {index : Nat} (member : index ∈ dependencies) :
    index < preceding.length := by
  obtain ⟨_, _, _, atIndex, _, _⟩ := dependencies_bound resolved member
  exact (List.getElem?_eq_some_iff.mp atIndex).1

def projectContextFrom (sorts : List SortEntry) :
    List SourceBinder → List SourceBinder → Option Context
  | _, [] => some []
  | preceding, binder :: remaining => do
      let target ← projectBinder sorts preceding binder
      let rest ← projectContextFrom sorts (preceding ++ [binder]) remaining
      pure (target :: rest)

def projectContext (sorts : List SortEntry) (binders : List SourceBinder) : Option Context :=
  if (binders.filterMap SourceBinder.name).Nodup then projectContextFrom sorts [] binders else none

theorem projectContextFrom_length {sorts : List SortEntry} {preceding binders : List SourceBinder}
    {context : Context} (projected : projectContextFrom sorts preceding binders = some context) :
    context.length = binders.length := by
  induction binders generalizing preceding context with
  | nil => simp [projectContextFrom] at projected; subst context; rfl
  | cons binder remaining ih =>
      obtain ⟨target, _, afterTarget⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨rest, restProjected, output⟩ := Option.bind_eq_some_iff.mp afterTarget
      have same : target :: rest = context := by simpa using output
      subst context
      simp [ih restProjected]

theorem projectContextFrom_getElem {sorts : List SortEntry} {preceding binders : List SourceBinder}
    {context : Context} (projected : projectContextFrom sorts preceding binders = some context)
    {index : Nat} {source : SourceBinder} (found : binders[index]? = some source) :
    ∃ target, context[index]? = some target ∧
      projectBinder sorts (preceding ++ binders.take index) source = some target := by
  induction binders generalizing preceding context index with
  | nil => simp at found
  | cons binder remaining ih =>
      obtain ⟨target, targetProjected, afterTarget⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨rest, restProjected, output⟩ := Option.bind_eq_some_iff.mp afterTarget
      have same : target :: rest = context := by simpa using output
      subst context
      cases index with
      | zero =>
          have sameSource : binder = source := by simpa using found
          subst source
          exact ⟨target, rfl, by simpa using targetProjected⟩
      | succ index =>
          obtain ⟨next, atIndex, nextProjected⟩ := ih restProjected (by simpa using found)
          refine ⟨next, by simpa using atIndex, ?_⟩
          simpa [List.take_succ_cons, List.append_assoc] using nextProjected

theorem projectContext_length {sorts : List SortEntry} {binders : List SourceBinder} {context : Context}
    (projected : projectContext sorts binders = some context) : context.length = binders.length := by
  unfold projectContext at projected
  split at projected
  · exact projectContextFrom_length projected
  · simp at projected

/-- Successful dependency projection points to actual existing kernel bound binders. -/
theorem dependencies_in_projected_context {sorts : List SortEntry} {binders : List SourceBinder}
    {context : Context} (projected : projectContext sorts binders = some context)
    {names : List String} {dependencies : Finset Nat} (resolved : dependencies? binders names = some dependencies)
    {index : Nat} (member : index ∈ dependencies) : ∃ sort, context[index]? = some (.bound sort) := by
  unfold projectContext at projected
  split at projected
  · obtain ⟨_, _, source, atIndex, bound, _⟩ := dependencies_bound resolved member
    obtain ⟨target, targetAtIndex, binderProjected⟩ := projectContextFrom_getElem projected atIndex
    have preserved := projectBinder_kind binderProjected
    cases target with
    | bound sort => exact ⟨sort, targetAtIndex⟩
    | regular sort dependencies => simp [bound] at preserved
  · simp at projected

/-- Every dependency of an actually projected regular binder names an earlier
bound binder in that same kernel context. -/
theorem regular_dependencies_bound_preceding {sorts : List SortEntry} {binders : List SourceBinder}
    {context : Context} (projected : projectContext sorts binders = some context)
    {position sort index : Nat} {dependencies : Finset Nat}
    (regularAt : context[position]? = some (.regular sort dependencies)) (member : index ∈ dependencies) :
    ∃ boundSort, context[index]? = some (.bound boundSort) ∧ index < position := by
  have positionBound : position < binders.length := by
    have bound := (List.getElem?_eq_some_iff.mp regularAt).1
    rwa [projectContext_length projected] at bound
  have sourceAt : binders[position]? = some binders[position] := List.getElem?_eq_getElem positionBound
  unfold projectContext at projected
  split at projected
  · obtain ⟨target, targetAt, targetProjected⟩ := projectContextFrom_getElem projected sourceAt
    have sameTarget : target = .regular sort dependencies :=
      Option.some.inj (targetAt.symm.trans regularAt)
    subst target
    have resolved := projectBinder_regular_dependencies targetProjected
    have earlier : index < position := by
      have bound := dependencies_before resolved member
      simp only [List.nil_append, List.length_take] at bound
      omega
    obtain ⟨_, _, dependency, dependencyAt, dependencyBound, _⟩ := dependencies_bound resolved member
    have dependencySource : binders[index]? = some dependency := by
      simpa [List.getElem?_take_of_lt earlier] using dependencyAt
    obtain ⟨kernelBinder, kernelAt, kernelProjected⟩ :=
      projectContextFrom_getElem projected dependencySource
    have kind := projectBinder_kind kernelProjected
    cases kernelBinder with
    | bound boundSort => exact ⟨boundSort, kernelAt, earlier⟩
    | regular _ _ => simp [dependencyBound] at kind
  · simp at projected

def bindersValue : List SourceBinder → Atom
  | [] => .symbol "nil"
  | binder :: remaining => .expression [.symbol "cons", binderValue binder, bindersValue remaining]

def decodeBinders : Atom → Option (List SourceBinder)
  | .symbol "nil" => some []
  | .expression [.symbol "cons", binder, remaining] => do
      let first ← decodeBinder binder
      let rest ← decodeBinders remaining
      pure (first :: rest)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeBinders_bindersValue (binders : List SourceBinder) :
    decodeBinders (bindersValue binders) = some binders := by
  induction binders with
  | nil => simp [bindersValue, decodeBinders]
  | cons first remaining ih => simp [bindersValue, decodeBinders, ih]

theorem decodeBinders_reflects (atom : Atom) (binders : List SourceBinder)
    (decoded : decodeBinders atom = some binders) : atom = bindersValue binders := by
  unfold decodeBinders at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i binder remaining
    obtain ⟨first, firstDecoded, afterFirst⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨rest, restDecoded, output⟩ := Option.bind_eq_some_iff.mp afterFirst
    have same : first :: rest = binders := by simpa using output
    subst binders
    rw [decodeBinder_reflects binder first firstDecoded,
      decodeBinders_reflects remaining rest restDecoded]
    rfl
  · simp at decoded
termination_by sizeOf atom

/-- Decoding source constructors and projecting them uses the existing target codec. -/
theorem decoded_binder_projects_to_existing_codec (sorts : List SortEntry) (preceding : List SourceBinder)
    (source : SourceBinder) (target : Binder) (projected : projectBinder sorts preceding source = some target) :
    ((decodeBinder (binderValue source)).bind (projectBinder sorts preceding)).map Data.binder =
      some (Data.binder target) := by simp [projected]

theorem decoded_context_projects_to_existing_codec (sorts : List SortEntry) (binders : List SourceBinder)
    (context : Context) (projected : projectContext sorts binders = some context) :
    ((decodeBinders (bindersValue binders)).bind (projectContext sorts)).map Data.context =
      some (Data.context context) := by simp [projected]

/-! ## Dense namespace and scope controls -/

private def setSort : SortEntry := ⟨"set", {}, 4⟩
private def propositionSort : SortEntry := ⟨"prop", ⟨false, false, true, false⟩, 17⟩

theorem trace_positions_do_not_become_sort_ids :
    sortIndex? [setSort, propositionSort] "set" = some 0 ∧
      sortIndex? [setSort, propositionSort] "prop" = some 1 ∧
      sortRows [setSort, propositionSort] = [(0, {}), (1, ⟨false, false, true, false⟩)] := by
  decide +kernel

theorem missing_sort_is_refused : sortIndex? [setSort] "unknown" = none := by decide +kernel

theorem duplicate_sort_names_are_refused : projectSorts [setSort, setSort] = none := by
  simp [projectSorts, setSort]

theorem future_sort_is_out_of_scope :
    sortIndex? ([setSort, propositionSort].take 1) "prop" = none ∧
      sortIndex? [setSort, propositionSort] "prop" = some 1 := by decide +kernel

theorem source_trace_scope_preserves_dense_sort_id :
    sortIndexBefore? [setSort, propositionSort] 6 "prop" = none ∧
      sortIndexBefore? [setSort, propositionSort] 17 "prop" = none ∧
      sortIndexBefore? [setSort, propositionSort] 18 "prop" = some 1 := by decide +kernel

private def anonymousRegular : SourceBinder := ⟨false, none, ⟨"set", []⟩⟩
private def namedBoundX : SourceBinder := ⟨true, some "x", ⟨"set", []⟩⟩
private def namedRegularU : SourceBinder := ⟨false, some "u", ⟨"set", ["x"]⟩⟩
private def namedBoundY : SourceBinder := ⟨true, some "y", ⟨"set", []⟩⟩
private def dependentAnonymous : SourceBinder := ⟨false, none, ⟨"set", ["y", "x", "y"]⟩⟩

theorem mixed_context_dependencies_use_full_positions :
    dependencyIndices? [anonymousRegular, namedBoundX, namedRegularU, namedBoundY] ["y", "x", "y"] =
      some [3, 1, 3] ∧
      dependencies? [anonymousRegular, namedBoundX, namedRegularU, namedBoundY] ["y", "x", "y"] =
        some {1, 3} := by decide +kernel

theorem mixed_context_projects_to_existing_binders :
    projectContext [setSort]
      [anonymousRegular, namedBoundX, namedRegularU, namedBoundY, dependentAnonymous] =
      some [.regular 0 ∅, .bound 0, .regular 0 {1}, .bound 0, .regular 0 {1, 3}] := by
  decide +kernel

theorem projected_dependencies_use_sorted_existing_codec :
    Data.dependencies ({3, 1} : Finset Nat) = ListAccess.listValue [Store.natural 1, Store.natural 3] := by
  have reordered : ({3, 1} : Finset Nat) = {1, 3} := by ext; simp [or_comm]
  have sorted : ({3, 1} : Finset Nat).sort (· ≤ ·) = [1, 3] := by
    rw [reordered, Finset.sort_insert (· ≤ ·) (by simp) (by decide)]
    simp
  simp [Data.dependencies, sorted]

theorem regular_names_are_not_bound_dependencies :
    dependencies? [anonymousRegular, namedBoundX, namedRegularU] ["u"] = none := by decide +kernel

theorem first_regular_name_is_not_skipped :
    let regularX : SourceBinder := ⟨false, some "x", ⟨"set", []⟩⟩
    binderIndex? [regularX, namedBoundX] "x" = some 0 ∧
      boundIndex? [regularX, namedBoundX] "x" = none ∧
      dependencies? [regularX, namedBoundX] ["x"] = none := by
  decide +kernel

theorem future_bound_name_is_refused :
    projectContext [setSort] [namedRegularU, namedBoundX] = none := by decide +kernel

theorem anonymous_positions_are_not_named_dependencies :
    dependencies? [anonymousRegular] ["x"] = none := by decide +kernel

theorem duplicate_binder_names_are_refused :
    projectContext [setSort] [namedBoundX, namedBoundX] = none := by decide +kernel

theorem bound_dependencies_are_not_discarded :
    projectBinder [setSort] [namedBoundX] ⟨true, some "y", ⟨"set", ["x"]⟩⟩ = none := by
  decide +kernel

theorem unknown_binder_sort_is_refused :
    projectBinder [setSort] [] ⟨false, none, ⟨"unknown", []⟩⟩ = none := by decide +kernel

theorem native_binder_container_is_refused :
    decodeBinders (.expression [binderValue namedBoundX]) = none ∧
      decodeBinders (bindersValue [namedBoundX]) = some [namedBoundX] := by
  constructor
  · simp [decodeBinders]
  · simp

theorem malformed_binder_fields_are_refused :
    decodeBinder (.expression [.symbol "MM0BinderV1", .symbol "MM0BoundBinderKindV1",
      .symbol "MM0NamedBinderV1", typeValue ⟨"set", []⟩]) = none ∧
      decodeType (.expression [.symbol "MM0TypeV1", TextualData.nameValue "set", .expression []]) = none := by
  simp [decodeBinder, decodeBinderName, decodeType, decodeNames]

end Mettapedia.Languages.MM0.MeTTa.TextualProjection
