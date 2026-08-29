import Mathlib.Data.List.Sigma
import Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT

/-!
# Occurrence-preserving source projection for mainline PeTTa call guards

The existing mainline `Snapshot` is already the resolved, finite query
environment: declaration semantic keys and occurrence identifiers are unique.
This module supplies the preceding source boundary.  It records the owning
space instance, permits repeated semantic declaration keys, and resolves them
by stable first occurrence without changing annotations or registered heads.

The projection is deliberately independent of a runtime representation.  A
later correspondence may relate `SpaceOwner` to a live space read token.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection

open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT

set_option autoImplicit false

/-! ## Owner-indexed source snapshots -/

/-- Logical identity of the space instance that owns a snapshot. -/
structure SpaceOwner where
  token : Nat
deriving DecidableEq, Repr

/-- Raw ordered declaration and annotation occurrences at one space revision.
Declaration semantic keys may repeat here; occurrence identifiers may not. -/
structure SourceSnapshot where
  owner : SpaceOwner
  revision : Nat
  declarations : List ArrowDeclaration
  annotations : List TypeAnnotation
  registeredFunctions : List String
deriving DecidableEq, Repr

namespace SourceSnapshot

def WellFormed (source : SourceSnapshot) : Prop :=
  (source.declarations.map ArrowDeclaration.occurrence).Nodup ∧
    (source.annotations.map TypeAnnotation.occurrence).Nodup ∧
      source.registeredFunctions.Nodup

instance (source : SourceSnapshot) : Decidable source.WellFormed := by
  unfold WellFormed
  infer_instance

end SourceSnapshot

/-- The existing resolved mainline snapshot paired with its owning space. -/
structure OwnedSnapshot where
  owner : SpaceOwner
  snapshot : Snapshot
deriving DecidableEq, Repr

/-! ## Stable first-key resolution -/

abbrev SemanticKey := String × List Term × Term

/-- A declaration whose semantic key is recorded in its dependent index. -/
abbrev DeclarationAt (key : SemanticKey) :=
  { declaration : ArrowDeclaration // declaration.semanticKey = key }

def keyDeclaration (declaration : ArrowDeclaration) : Sigma DeclarationAt :=
  ⟨declaration.semanticKey, declaration, rfl⟩

def unkeyDeclaration (entry : Sigma DeclarationAt) : ArrowDeclaration :=
  entry.2.1

@[simp]
theorem unkey_keyDeclaration (declaration : ArrowDeclaration) :
    unkeyDeclaration (keyDeclaration declaration) = declaration := rfl

@[simp]
theorem semanticKey_unkeyDeclaration (entry : Sigma DeclarationAt) :
    (unkeyDeclaration entry).semanticKey = entry.1 :=
  entry.2.2

/-- Stable semantic-key deduplication.  `List.dedupKeys` retains the first
value returned by `dlookup`, so the retained declaration includes the exact
first source occurrence rather than merely an equal semantic key. -/
def stableFirstDeclarations
    (declarations : List ArrowDeclaration) : List ArrowDeclaration :=
  ((declarations.map keyDeclaration).dedupKeys).map unkeyDeclaration

private theorem dedupKeys_sublist
    (entries : List (Sigma DeclarationAt)) :
    List.Sublist entries.dedupKeys entries := by
  induction entries with
  | nil => simp [List.dedupKeys]
  | cons entry entries ih =>
      rw [List.dedupKeys_cons, List.kinsert_def]
      exact List.Sublist.cons_cons entry
        ((List.kerase_sublist entry.1 entries.dedupKeys).trans ih)

theorem stableFirstDeclarations_sublist
    (declarations : List ArrowDeclaration) :
    List.Sublist (stableFirstDeclarations declarations) declarations := by
  have keyedSublist :=
    (dedupKeys_sublist (declarations.map keyDeclaration)).map
      unkeyDeclaration
  have unkeyedSource :
      (declarations.map keyDeclaration).map unkeyDeclaration =
        declarations := by
    simp [Function.comp_def, keyDeclaration, unkeyDeclaration]
  rw [unkeyedSource] at keyedSublist
  exact keyedSublist

theorem stableFirstDeclarations_no_invention
    {declarations : List ArrowDeclaration} {declaration : ArrowDeclaration}
    (member : declaration ∈ stableFirstDeclarations declarations) :
    declaration ∈ declarations :=
  (stableFirstDeclarations_sublist declarations).subset member

theorem stableFirstDeclarations_semanticKeys_nodup
    (declarations : List ArrowDeclaration) :
    ((stableFirstDeclarations declarations).map
      ArrowDeclaration.semanticKey).Nodup := by
  have keysNodup :=
    List.nodupKeys_dedupKeys (declarations.map keyDeclaration)
  simpa [stableFirstDeclarations, List.NodupKeys, List.keys,
    Function.comp_def] using keysNodup

/-- Exact provenance predicate: the dependent value returned by the standard
first-key lookup is the specified declaration occurrence itself. -/
def IsFirstSemanticOccurrence
    (declarations : List ArrowDeclaration)
    (declaration : ArrowDeclaration) : Prop :=
  ∃ (key : SemanticKey) (selected : DeclarationAt key),
    key = declaration.semanticKey ∧
      selected.1 = declaration ∧
        selected ∈ List.dlookup key (declarations.map keyDeclaration)

theorem mem_stableFirstDeclarations_iff_first_occurrence
    (declarations : List ArrowDeclaration)
    (declaration : ArrowDeclaration) :
    declaration ∈ stableFirstDeclarations declarations ↔
      IsFirstSemanticOccurrence declarations declaration := by
  let entries := (declarations.map keyDeclaration).dedupKeys
  have entriesNodup : entries.NodupKeys := by
    exact List.nodupKeys_dedupKeys _
  constructor
  · intro member
    simp only [stableFirstDeclarations, List.mem_map] at member
    obtain ⟨entry, entryMember, unkeyed⟩ := member
    cases entry with
    | mk key selected =>
        dsimp [unkeyDeclaration] at unkeyed
        have selectedMember :
            selected ∈ List.dlookup key entries :=
          (List.mem_dlookup_iff entriesNodup).2 entryMember
        rw [List.dlookup_dedupKeys] at selectedMember
        have keyExact : key = declaration.semanticKey := by
          rw [← unkeyed]
          exact selected.2.symm
        exact ⟨key, selected, keyExact, unkeyed, selectedMember⟩
  · rintro ⟨key, selected, _keyExact, selectedExact, selectedMember⟩
    have selectedMember' :
        selected ∈ List.dlookup key
          ((declarations.map keyDeclaration).dedupKeys) := by
      rw [List.dlookup_dedupKeys]
      exact selectedMember
    have entryMember :
        Sigma.mk key selected ∈
          (declarations.map keyDeclaration).dedupKeys :=
      (List.mem_dlookup_iff entriesNodup).1 selectedMember'
    exact List.mem_map.2 ⟨_, entryMember, selectedExact⟩

/-! ## Resolution and its exactness laws -/

def SourceSnapshot.resolve (source : SourceSnapshot) : OwnedSnapshot :=
  { owner := source.owner
    snapshot :=
      { revision := source.revision
        declarations := stableFirstDeclarations source.declarations
        annotations := source.annotations
        registeredFunctions := source.registeredFunctions } }

@[simp]
theorem resolve_owner_exact (source : SourceSnapshot) :
    source.resolve.owner = source.owner := rfl

@[simp]
theorem resolve_revision_exact (source : SourceSnapshot) :
    source.resolve.snapshot.revision = source.revision := rfl

theorem resolve_declarations_subsequence (source : SourceSnapshot) :
    List.Sublist source.resolve.snapshot.declarations source.declarations :=
  stableFirstDeclarations_sublist source.declarations

/-- The resolved semantic-key sequence is duplicate-free while retaining the
source list order through the sublist relation. -/
theorem resolve_declaration_order_exact (source : SourceSnapshot) :
    List.Sublist source.resolve.snapshot.declarations source.declarations ∧
      (source.resolve.snapshot.declarations.map
        ArrowDeclaration.semanticKey).Nodup :=
  ⟨resolve_declarations_subsequence source,
    stableFirstDeclarations_semanticKeys_nodup source.declarations⟩

theorem resolve_semanticKeys_nodup (source : SourceSnapshot) :
    (source.resolve.snapshot.declarations.map
      ArrowDeclaration.semanticKey).Nodup :=
  stableFirstDeclarations_semanticKeys_nodup source.declarations

theorem resolve_first_occurrence_exact
    (source : SourceSnapshot) (declaration : ArrowDeclaration) :
    declaration ∈ source.resolve.snapshot.declarations ↔
      IsFirstSemanticOccurrence source.declarations declaration :=
  mem_stableFirstDeclarations_iff_first_occurrence _ _

@[simp]
theorem resolve_annotations_exact (source : SourceSnapshot) :
    source.resolve.snapshot.annotations = source.annotations := rfl

@[simp]
theorem resolve_registeredFunctions_exact (source : SourceSnapshot) :
    source.resolve.snapshot.registeredFunctions =
      source.registeredFunctions := rfl

theorem resolve_wellFormed
    {source : SourceSnapshot} (wellFormed : source.WellFormed) :
    source.resolve.snapshot.WellFormed := by
  rcases wellFormed with
    ⟨declarationOccurrences, annotationOccurrences, registeredFunctions⟩
  refine ⟨?_, resolve_semanticKeys_nodup source, ?_, ?_⟩
  · exact declarationOccurrences.sublist
      ((resolve_declarations_subsequence source).map
        ArrowDeclaration.occurrence)
  · simpa using annotationOccurrences
  · simpa using registeredFunctions

theorem resolve_no_invention
    {source : SourceSnapshot} {declaration : ArrowDeclaration}
    (member : declaration ∈ source.resolve.snapshot.declarations) :
    declaration ∈ source.declarations :=
  stableFirstDeclarations_no_invention member

/-! ## Discriminating projection canaries -/

namespace Canary

def owner : SpaceOwner := ⟨41⟩

def numberDeclaration : ArrowDeclaration :=
  ⟨10, "f", [numberType], numberType⟩

def duplicateNumberDeclaration : ArrowDeclaration :=
  { numberDeclaration with occurrence := 12 }

def stringDeclaration : ArrowDeclaration :=
  ⟨11, "f", [stringType], stringType⟩

def annotationA : TypeAnnotation :=
  ⟨20, .atom "a", numberType⟩

def annotationB : TypeAnnotation :=
  ⟨21, .atom "b", stringType⟩

def source : SourceSnapshot :=
  ⟨owner, 7,
    [numberDeclaration, duplicateNumberDeclaration, stringDeclaration],
    [annotationA, annotationB], ["f"]⟩

theorem duplicate_key_retains_first_occurrence :
    source.resolve.snapshot.declarations =
      [numberDeclaration, stringDeclaration] := by
  decide

theorem owner_revision_annotations_and_heads_are_exact :
    source.resolve.owner = owner ∧
      source.resolve.snapshot.revision = 7 ∧
      source.resolve.snapshot.annotations = [annotationA, annotationB] ∧
      source.resolve.snapshot.registeredFunctions = ["f"] := by
  decide

def swappedSource : SourceSnapshot :=
  { source with
    declarations := [stringDeclaration, numberDeclaration] }

theorem swapping_distinct_declarations_changes_order :
    swappedSource.resolve.snapshot.declarations =
        [stringDeclaration, numberDeclaration] ∧
      swappedSource.resolve.snapshot.declarations ≠
        [numberDeclaration, stringDeclaration] := by
  decide

def duplicateFirstSource : SourceSnapshot :=
  { source with
    declarations := [duplicateNumberDeclaration, numberDeclaration] }

theorem changing_first_duplicate_changes_provenance :
    duplicateFirstSource.resolve.snapshot.declarations =
      [duplicateNumberDeclaration] := by
  decide

theorem absent_declaration_cannot_be_resolved
    {declaration : ArrowDeclaration}
    (absent : declaration ∉ source.declarations) :
    declaration ∉ source.resolve.snapshot.declarations := by
  exact fun member => absent (resolve_no_invention member)

def duplicateOccurrenceSource : SourceSnapshot :=
  { source with
    declarations :=
      [numberDeclaration, { stringDeclaration with occurrence := 10 }] }

theorem duplicate_source_occurrences_are_not_wellFormed :
    ¬ duplicateOccurrenceSource.WellFormed := by
  decide

theorem source_with_duplicate_semantic_key_is_wellFormed :
    source.WellFormed := by
  decide

theorem resolved_source_is_wellFormed :
    source.resolve.snapshot.WellFormed :=
  resolve_wellFormed source_with_duplicate_semantic_key_is_wellFormed

end Canary

#print axioms stableFirstDeclarations_sublist
#print axioms stableFirstDeclarations_semanticKeys_nodup
#print axioms mem_stableFirstDeclarations_iff_first_occurrence
#print axioms resolve_owner_exact
#print axioms resolve_revision_exact
#print axioms resolve_declarations_subsequence
#print axioms resolve_declaration_order_exact
#print axioms resolve_semanticKeys_nodup
#print axioms resolve_first_occurrence_exact
#print axioms resolve_annotations_exact
#print axioms resolve_registeredFunctions_exact
#print axioms resolve_wellFormed
#print axioms resolve_no_invention
#print axioms Canary.duplicate_key_retains_first_occurrence
#print axioms Canary.owner_revision_annotations_and_heads_are_exact
#print axioms Canary.swapping_distinct_declarations_changes_order
#print axioms Canary.changing_first_duplicate_changes_provenance
#print axioms Canary.absent_declaration_cannot_be_resolved
#print axioms Canary.duplicate_source_occurrences_are_not_wellFormed

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
