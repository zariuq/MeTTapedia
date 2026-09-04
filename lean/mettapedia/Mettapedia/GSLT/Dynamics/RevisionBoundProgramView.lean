import Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex

/-!
# Revision-bound programs over stable occurrence families

An executable program view is derived from an ordered family of authored
occurrences at one exact store revision.  Compilation is partial: an absent
compiled payload means that the source occurrence remains executable through
the generic realization.  A view may be transported to another physical
presentation only by mapping occurrence identity and payload together.

The naturality theorem states that compiling and then transporting is the
same as transporting and then compiling, provided the compiler commutes with
the presentation map.  Execution remains total: stale revision keys and
declined compiled payloads select the generic realization.  The negative
controls show why neither revision nor store identity may be omitted from the
key, and why occurrence identities must not be conflated with payloads.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RevisionBoundProgramView

open StableOccurrenceIdentityIndex

universe uStore uRevision uId uRow uCode uInput uOutput
universe uStore' uRevision' uId' uRow' uCode'

/-- The complete authority key for a derived program presentation. -/
structure RevisionKey (Store : Type uStore) (Revision : Type uRevision) where
  store : Store
  revision : Revision
deriving DecidableEq, Repr

/-- An ordered source presentation at one exact authority key. -/
structure Snapshot
    (Store : Type uStore) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow) where
  key : RevisionKey Store Revision
  occurrences : List (Occurrence Id Row)
deriving DecidableEq, Repr

/-- One occurrence paired with an optional derived program. -/
structure ProgramEntry
    (Id : Type uId) (Row : Type uRow) (Code : Type uCode) where
  id : Id
  source : Row
  code : Option Code
deriving DecidableEq, Repr

/-- An immutable program presentation derived at one exact authority key. -/
structure ProgramView
    (Store : Type uStore) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow) (Code : Type uCode) where
  key : RevisionKey Store Revision
  entries : List (ProgramEntry Id Row Code)
deriving DecidableEq, Repr

/-- Compile one occurrence without removing the generic source payload. -/
def compileEntry {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    (compile : Row → Option Code) (occurrence : Occurrence Id Row) :
    ProgramEntry Id Row Code :=
  ⟨occurrence.id, occurrence.payload, compile occurrence.payload⟩

/-- Compile an ordered occurrence snapshot.  Declines remain explicit. -/
def build {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    (compile : Row → Option Code)
    (snapshot : Snapshot Store Revision Id Row) :
    ProgramView Store Revision Id Row Code where
  key := snapshot.key
  entries := snapshot.occurrences.map (compileEntry compile)

/-- Erase derived code from one program entry. -/
def eraseEntry {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    (entry : ProgramEntry Id Row Code) : Occurrence Id Row :=
  ⟨entry.id, entry.source⟩

@[simp] theorem erase_compileEntry
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    (compile : Row → Option Code) (occurrence : Occurrence Id Row) :
    eraseEntry (compileEntry compile occurrence) = occurrence := by
  cases occurrence
  rfl

/-- Code erasure recovers the exact authored occurrence presentation. -/
theorem erase_build
    {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    (compile : Row → Option Code)
    (snapshot : Snapshot Store Revision Id Row) :
    (build compile snapshot).entries.map eraseEntry = snapshot.occurrences := by
  cases snapshot
  simp [build, Function.comp_def, compileEntry, eraseEntry]

/-! ## Presentation transport and its naturality square -/

/-- A map between occurrence presentations changes identity and payload as
independent coordinates. -/
structure OccurrenceMap
    (Id : Type uId) (Row : Type uRow)
    (Id' : Type uId') (Row' : Type uRow') where
  mapId : Id → Id'
  mapPayload : Row → Row'

namespace OccurrenceMap

/-- Identity presentation map. -/
def id (Id : Type uId) (Row : Type uRow) : OccurrenceMap Id Row Id Row where
  mapId := _root_.id
  mapPayload := _root_.id

/-- Composition in execution order. -/
def comp
    {Id : Type uId} {Row : Type uRow}
    {Id' : Type uId'} {Row' : Type uRow'}
    {Id'' : Type} {Row'' : Type}
    (earlier : OccurrenceMap Id Row Id' Row')
    (later : OccurrenceMap Id' Row' Id'' Row'') :
    OccurrenceMap Id Row Id'' Row'' where
  mapId := later.mapId ∘ earlier.mapId
  mapPayload := later.mapPayload ∘ earlier.mapPayload

/-- Map one occurrence without conflating its two coordinates. -/
def mapOccurrence
    {Id : Type uId} {Row : Type uRow}
    {Id' : Type uId'} {Row' : Type uRow'}
    (mapping : OccurrenceMap Id Row Id' Row')
    (occurrence : Occurrence Id Row) : Occurrence Id' Row' :=
  ⟨mapping.mapId occurrence.id, mapping.mapPayload occurrence.payload⟩

@[simp] theorem mapOccurrence_id
    {Id : Type uId} {Row : Type uRow} (occurrence : Occurrence Id Row) :
    (id Id Row).mapOccurrence occurrence = occurrence := by
  cases occurrence
  rfl

theorem mapOccurrence_comp
    {Id : Type uId} {Row : Type uRow}
    {Id' : Type uId'} {Row' : Type uRow'}
    {Id'' : Type} {Row'' : Type}
    (earlier : OccurrenceMap Id Row Id' Row')
    (later : OccurrenceMap Id' Row' Id'' Row'')
    (occurrence : Occurrence Id Row) :
    (earlier.comp later).mapOccurrence occurrence =
      later.mapOccurrence (earlier.mapOccurrence occurrence) := by
  cases occurrence
  rfl

end OccurrenceMap

/-- A revision transport identifies both source and target authority keys. -/
structure RevisionTransport
    (Store : Type uStore) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow)
    (Store' : Type uStore') (Revision' : Type uRevision')
    (Id' : Type uId') (Row' : Type uRow')
    extends OccurrenceMap Id Row Id' Row' where
  sourceKey : RevisionKey Store Revision
  targetKey : RevisionKey Store' Revision'

/-- Transport the complete ordered source presentation. -/
def transportSnapshot
    {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow}
    {Store' : Type uStore'} {Revision' : Type uRevision'}
    {Id' : Type uId'} {Row' : Type uRow'}
    (transport : RevisionTransport Store Revision Id Row
      Store' Revision' Id' Row')
    (snapshot : Snapshot Store Revision Id Row) :
    Snapshot Store' Revision' Id' Row' where
  key := transport.targetKey
  occurrences := snapshot.occurrences.map
    transport.toOccurrenceMap.mapOccurrence

/-- Transport one compiled occurrence and its code representation. -/
def transportEntry
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (mapping : OccurrenceMap Id Row Id' Row') (mapCode : Code → Code')
    (entry : ProgramEntry Id Row Code) : ProgramEntry Id' Row' Code' where
  id := mapping.mapId entry.id
  source := mapping.mapPayload entry.source
  code := entry.code.map mapCode

/-- Transport a complete immutable program presentation. -/
def transportView
    {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Store' : Type uStore'} {Revision' : Type uRevision'}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (transport : RevisionTransport Store Revision Id Row
      Store' Revision' Id' Row')
    (mapCode : Code → Code')
    (view : ProgramView Store Revision Id Row Code) :
    ProgramView Store' Revision' Id' Row' Code' where
  key := transport.targetKey
  entries := view.entries.map
    (transportEntry transport.toOccurrenceMap mapCode)

@[simp] theorem erase_transportEntry
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (mapping : OccurrenceMap Id Row Id' Row') (mapCode : Code → Code')
    (entry : ProgramEntry Id Row Code) :
    eraseEntry (transportEntry mapping mapCode entry) =
      mapping.mapOccurrence (eraseEntry entry) := by
  cases entry
  rfl

/-- Erasure commutes with transporting an immutable program view. -/
theorem erase_transportView
    {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Store' : Type uStore'} {Revision' : Type uRevision'}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (transport : RevisionTransport Store Revision Id Row
      Store' Revision' Id' Row')
    (mapCode : Code → Code')
    (view : ProgramView Store Revision Id Row Code) :
    (transportView transport mapCode view).entries.map eraseEntry =
      view.entries.map
        (transport.toOccurrenceMap.mapOccurrence ∘ eraseEntry) := by
  simp [transportView, Function.comp_def]

/-! ## Selection transport when no code morphism is available -/

/-- Transport occurrence-selection evidence while explicitly declining the
derived code payload.  This is the maximal transport available from an
occurrence map alone: source and identity move, while execution returns to the
generic target realization. -/
def transportSelectionEntry
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (mapping : OccurrenceMap Id Row Id' Row')
    (entry : ProgramEntry Id Row Code) : ProgramEntry Id' Row' Code' where
  id := mapping.mapId entry.id
  source := mapping.mapPayload entry.source
  code := none

/-- Transport an immutable occurrence-selection view without claiming a map
between source-owned and target-owned executable representations. -/
def transportSelectionView
    {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Store' : Type uStore'} {Revision' : Type uRevision'}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (transport : RevisionTransport Store Revision Id Row
      Store' Revision' Id' Row')
    (view : ProgramView Store Revision Id Row Code) :
    ProgramView Store' Revision' Id' Row' Code' where
  key := transport.targetKey
  entries := view.entries.map
    (transportSelectionEntry transport.toOccurrenceMap)

@[simp] theorem erase_transportSelectionEntry
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (mapping : OccurrenceMap Id Row Id' Row')
    (entry : ProgramEntry Id Row Code) :
    eraseEntry (transportSelectionEntry mapping entry :
      ProgramEntry Id' Row' Code') =
      mapping.mapOccurrence (eraseEntry entry) := by
  cases entry
  rfl

/-- Selection transport commutes with compilation without a code-naturality
hypothesis because every derived payload is honestly declined at the target.
This is strictly weaker than `build_natural`, and therefore requires only the
occurrence-presentation map. -/
theorem transportSelectionView_build
    {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Store' : Type uStore'} {Revision' : Type uRevision'}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (transport : RevisionTransport Store Revision Id Row
      Store' Revision' Id' Row')
    (sourceCompile : Row → Option Code)
    (snapshot : Snapshot Store Revision Id Row) :
    (transportSelectionView transport (build sourceCompile snapshot) :
      ProgramView Store' Revision' Id' Row' Code') =
      build (fun _ : Row' => (none : Option Code'))
        (transportSnapshot transport snapshot) := by
  cases snapshot with
  | mk key occurrences =>
      simp only [transportSelectionView, build, transportSnapshot]
      congr 1
      induction occurrences with
      | nil => rfl
      | cons occurrence occurrences inductionHypothesis =>
          simp only [List.map_cons]
          rw [inductionHypothesis]
          congr 1

/-- The program construction is natural in the occurrence presentation.
This is the compile/transport commuting square. -/
theorem build_natural
    {Store : Type uStore} {Revision : Type uRevision}
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Store' : Type uStore'} {Revision' : Type uRevision'}
    {Id' : Type uId'} {Row' : Type uRow'} {Code' : Type uCode'}
    (transport : RevisionTransport Store Revision Id Row
      Store' Revision' Id' Row')
    (sourceCompile : Row → Option Code)
    (targetCompile : Row' → Option Code')
    (mapCode : Code → Code')
    (natural : ∀ row,
      targetCompile (transport.mapPayload row) =
        (sourceCompile row).map mapCode)
    (snapshot : Snapshot Store Revision Id Row) :
    transportView transport mapCode (build sourceCompile snapshot) =
      build targetCompile (transportSnapshot transport snapshot) := by
  cases snapshot with
  | mk key occurrences =>
      simp only [transportView, build, transportSnapshot]
      congr 1
      induction occurrences with
      | nil => rfl
      | cons occurrence occurrences inductionHypothesis =>
          simp only [List.map_cons]
          rw [inductionHypothesis]
          congr 1
          cases occurrence
          simp [compileEntry, transportEntry,
            OccurrenceMap.mapOccurrence, natural]

/-! ## Total execution: compiled when current, generic otherwise -/

/-- Execute one entry.  Current compiled code is an optimization; every
decline or stale key takes the generic realization of the retained source. -/
def runEntry
    {Store : Type uStore} {Revision : Type uRevision}
    [DecidableEq Store] [DecidableEq Revision]
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Input : Type uInput} {Output : Type uOutput}
    (viewKey liveKey : RevisionKey Store Revision)
    (runSource : Row → Input → Output)
    (runCode : Code → Input → Output)
    (entry : ProgramEntry Id Row Code) (input : Input) : Output :=
  if viewKey = liveKey then
    match entry.code with
    | some code => runCode code input
    | none => runSource entry.source input
  else
    runSource entry.source input

/-- A sound compiled entry is observationally equal to its source on every
current, stale, and declined route. -/
theorem runEntry_exact
    {Store : Type uStore} {Revision : Type uRevision}
    [DecidableEq Store] [DecidableEq Revision]
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Input : Type uInput} {Output : Type uOutput}
    (viewKey liveKey : RevisionKey Store Revision)
    (runSource : Row → Input → Output)
    (runCode : Code → Input → Output)
    (entry : ProgramEntry Id Row Code) (input : Input)
    (sound : ∀ code, entry.code = some code →
      runCode code input = runSource entry.source input) :
    runEntry viewKey liveKey runSource runCode entry input =
      runSource entry.source input := by
  by_cases current : viewKey = liveKey
  · simp only [runEntry, current, if_true]
    cases codeEquation : entry.code with
    | none => rfl
    | some code =>
        simpa [codeEquation] using sound code codeEquation
  · simp [runEntry, current]

/-- Staleness alone selects the generic realization. -/
theorem runEntry_stale
    {Store : Type uStore} {Revision : Type uRevision}
    [DecidableEq Store] [DecidableEq Revision]
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Input : Type uInput} {Output : Type uOutput}
    (viewKey liveKey : RevisionKey Store Revision)
    (runSource : Row → Input → Output)
    (runCode : Code → Input → Output)
    (entry : ProgramEntry Id Row Code) (input : Input)
    (stale : viewKey ≠ liveKey) :
    runEntry viewKey liveKey runSource runCode entry input =
      runSource entry.source input := by
  simp [runEntry, stale]

/-- A compilation decline selects the generic realization even at the exact
current key. -/
theorem runEntry_declined
    {Store : Type uStore} {Revision : Type uRevision}
    [DecidableEq Store] [DecidableEq Revision]
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    {Input : Type uInput} {Output : Type uOutput}
    (key : RevisionKey Store Revision)
    (runSource : Row → Input → Output)
    (runCode : Code → Input → Output)
    (entry : ProgramEntry Id Row Code) (input : Input)
    (declined : entry.code = none) :
    runEntry key key runSource runCode entry input =
      runSource entry.source input := by
  simp [runEntry, declined]

/-! ## Executable positive and negative controls -/

namespace Canary

inductive Store where
  | left
  | right
deriving DecidableEq, Repr

abbrev Key := RevisionKey Store Nat

def sourceKey : Key := ⟨.left, 4⟩
def targetKey : Key := ⟨.right, 9⟩

def source : Snapshot Store Nat Nat String where
  key := sourceKey
  occurrences := [⟨10, "same"⟩, ⟨11, "same"⟩, ⟨12, "tail"⟩]

def compiler (row : String) : Option Nat := some row.length

def transport : RevisionTransport Store Nat Nat String
    Store Nat Nat String where
  mapId := fun identity => identity + 100
  mapPayload := _root_.id
  sourceKey := sourceKey
  targetKey := targetKey

/-- Duplicate payloads remain distinct because their occurrence identities
are transported independently. -/
example :
    (transportSnapshot transport source).occurrences =
      [⟨110, "same"⟩, ⟨111, "same"⟩, ⟨112, "tail"⟩] := by
  decide

/-- The concrete clone transport commutes with program construction. -/
example :
    transportView transport _root_.id (build compiler source) =
      build compiler (transportSnapshot transport source) := by
  apply build_natural
  intro row
  rfl

def sourceRun (source input : Nat) : Nat := source + input
def codeRun (code input : Nat) : Nat := code + input
def compiledEntry : ProgramEntry Nat Nat Nat := ⟨1, 3, some 3⟩
def declinedEntry : ProgramEntry Nat Nat Nat := ⟨2, 5, none⟩

/-- Current compiled execution agrees with the generic source. -/
example :
    runEntry sourceKey sourceKey sourceRun codeRun compiledEntry 4 = 7 := by
  decide

/-- A different revision cannot reuse the compiled route. -/
example :
    runEntry sourceKey ⟨.left, 5⟩ sourceRun codeRun compiledEntry 4 = 7 := by
  decide

/-- A declined occurrence remains executable through the generic route. -/
example :
    runEntry sourceKey sourceKey sourceRun codeRun declinedEntry 4 = 9 := by
  decide

/-- An occurrence map alone transports selection but deliberately erases
compiled code.  Ordinary code transport remains a separate, stronger claim. -/
example :
    (transportSelectionEntry
        (OccurrenceMap.id Nat Nat) compiledEntry :
      ProgramEntry Nat Nat Nat).code = none ∧
    (transportEntry
        (OccurrenceMap.id Nat Nat) _root_.id compiledEntry).code = some 3 := by
  decide

/-- Erasing revision is unsound as a currentness key: distinct revisions of
one store then become indistinguishable. -/
example :
    sourceKey.store = (⟨.left, 5⟩ : Key).store ∧
      sourceKey ≠ (⟨.left, 5⟩ : Key) := by
  decide

/-- Erasing store identity is also unsound: equal revision numbers can name
different authorities. -/
example :
    sourceKey.revision = (⟨.right, 4⟩ : Key).revision ∧
      sourceKey ≠ (⟨.right, 4⟩ : Key) := by
  decide

/-- An identity-only lookup is deliberately exposed for the negative
control; it returns the first equal identity. -/
def firstCodeFor
    {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
    [DecidableEq Id]
    (identity : Id) : List (ProgramEntry Id Row Code) → Option Code
  | [] => none
  | entry :: entries =>
      if entry.id = identity then entry.code
      else firstCodeFor identity entries

def duplicateIdentityEntries : List (ProgramEntry Nat Nat Nat) :=
  [⟨7, 10, some 1⟩, ⟨7, 20, some 2⟩]

/-- Duplicate occurrence identities make an identity-only projection choose
the wrong program for the second source occurrence. -/
example :
    firstCodeFor 7 duplicateIdentityEntries = some 1 ∧
      firstCodeFor 7 duplicateIdentityEntries ≠ some 2 := by
  decide

/-- The same counterexample visibly violates occurrence-ID uniqueness. -/
example :
    ¬ (duplicateIdentityEntries.map ProgramEntry.id).Nodup := by
  decide

end Canary

#print axioms erase_build
#print axioms build_natural
#print axioms transportSelectionView_build
#print axioms runEntry_exact
#print axioms runEntry_stale
#print axioms runEntry_declined

end Mettapedia.GSLT.Dynamics.RevisionBoundProgramView
