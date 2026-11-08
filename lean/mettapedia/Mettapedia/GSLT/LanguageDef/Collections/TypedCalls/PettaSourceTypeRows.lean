import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay
import Mettapedia.Languages.MeTTa.HE.Space

/-!
# Typed-call rows read from the live PeTTa source world

Only the shared exact-subject annotation filter is reused from HE; the source
of its rows is PeTTa's actual `&self` store. Intrinsic declarations take
precedence when present. The mathematical source profile is symbol-subject,
plain finite type syntax, and saturated arrow calls. Unsupported annotations
and codecs produce an unserved boundary, never apparent absence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeRows

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PettaOccurrenceOverlay (Row RowLookup)

mutual
def typeAtom : Ty String → Atom
  | .var name => .var name
  | .sym name => .symbol name
  | .app children => .expression (typeAtoms children)

def typeAtoms : List (Ty String) → List Atom
  | [] => []
  | first :: rest => typeAtom first :: typeAtoms rest
end

mutual
def parseType : Atom → Option (Ty String)
  | .var name => some (.var name)
  | .symbol name => some (.sym name)
  | .expression children => (parseTypes children).map Ty.app
  | .grounded _ => none

def parseTypes : List Atom → Option (List (Ty String))
  | [] => some []
  | first :: rest => do
      let type ← parseType first
      let types ← parseTypes rest
      pure (type :: types)
end

mutual
theorem parse_typeAtom : ∀ type : Ty String, parseType (typeAtom type) = some type
  | .var _ => rfl
  | .sym _ => rfl
  | .app children => by simp only [typeAtom, parseType, parse_typeAtoms, Option.map_some]

theorem parse_typeAtoms : ∀ types : List (Ty String), parseTypes (typeAtoms types) = some types
  | [] => rfl
  | first :: rest => by
      simp only [typeAtoms, parseTypes, parse_typeAtom, parse_typeAtoms]
      rfl
end

theorem typeAtoms_map (types : List (Ty String)) : typeAtoms types = types.map typeAtom := by
  induction types with
  | nil => rfl
  | cons first rest ih => simp [typeAtoms, ih]

def annotations (atoms : List Atom) (subject : Atom) : List Atom :=
  Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes ⟨atoms⟩ subject

def rawTypes (intrinsicRows : List Atom) (world : EagerDFS.World) (head : String) : List Atom :=
  let intrinsic := annotations intrinsicRows (.symbol head)
  if intrinsic.isEmpty then annotations world.state.core (.symbol head) else intrinsic

def annotationSupported : Atom → Bool
  | .expression [.symbol ":", .symbol _, type] => (parseType type).isSome
  | .expression [.symbol ":", _, _] => false
  | _ => true

def supported (intrinsicRows : List Atom) (world : EagerDFS.World) : Bool :=
  intrinsicRows.all annotationSupported && world.state.core.all annotationSupported

/-- Total mathematical declarations. Services below expose them only after
the source syntax check, which prevents unsupported rows being dropped. -/
def declarations (intrinsicRows : List Atom) (world : EagerDFS.World) : Decls := fun head =>
  dedupAlpha ((rawTypes intrinsicRows world head).filterMap parseType)

def parseRows : List (Ty String) → Option (List Row)
  | [] => some []
  | first :: rest => do
      let row ← Row.ofType first
      let rows ← parseRows rest
      pure (row :: rows)

def lookup (intrinsicRows : List Atom) (world : EagerDFS.World)
    (head : String) (arguments : List Atom) : RowLookup :=
  if supported intrinsicRows world then
    match parseTypes (rawTypes intrinsicRows world head) with
    | none => .unserved
    | some [] => .untyped
    | some types =>
      match parseRows types with
      | none => .unserved
      | some rows =>
        if rows.all (fun row => row.parameters.length == arguments.length) then .typed rows
        else .unserved
  else .unserved

theorem reads_actual_self (world : EagerDFS.World) :
    world.state.read .self = some world.state.core := rfl

theorem annotations_append (first rest : List Atom) (subject : Atom) :
    annotations (first ++ rest) subject = annotations first subject ++ annotations rest subject := by
  simp [annotations, Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes, List.filterMap_append]

theorem no_intrinsic_reads_current_world (world : EagerDFS.World) (head : String) :
    rawTypes [] world head = annotations world.state.core (.symbol head) := rfl

theorem intrinsic_precedence (intrinsicRows : List Atom) (world : EagerDFS.World) (head : String)
    (present : annotations intrinsicRows (.symbol head) ≠ []) :
    rawTypes intrinsicRows world head = annotations intrinsicRows (.symbol head) := by
  simp [rawTypes, List.isEmpty_iff, present]

theorem unsupported_is_unserved (intrinsicRows : List Atom) (world : EagerDFS.World)
    (head : String) (arguments : List Atom) (unsupported : supported intrinsicRows world = false) :
    lookup intrinsicRows world head arguments = .unserved := by simp [lookup, unsupported]

theorem parseRows_encoded : ∀ rows : List Row, parseRows (rows.map Row.asType) = some rows
  | [] => rfl
  | first :: rest => by simp [parseRows, PettaOccurrenceOverlay.row_type_roundtrip, parseRows_encoded rest]

def declaration (head : String) (type : Ty String) : Atom :=
  .expression [.symbol ":", .symbol head, typeAtom type]

theorem written_declarations_order (head : String) (types : List (Ty String)) :
    annotations (types.map (declaration head)) (.symbol head) = typeAtoms types := by
  induction types with
  | nil => rfl
  | cons first rest ih =>
    simpa [annotations, Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes, declaration, typeAtoms]
      using congrArg (List.cons (typeAtom first)) ih

theorem declarations_supported (head : String) (types : List (Ty String)) :
    (types.map (declaration head)).all annotationSupported = true := by
  induction types with
  | nil => rfl
  | cons first rest ih => simp [declaration, annotationSupported, parse_typeAtom, ih]

theorem parseTypes_filterMap (atoms : List Atom) (types : List (Ty String))
    (parsed : parseTypes atoms = some types) : atoms.filterMap parseType = types := by
  induction atoms generalizing types with
  | nil => simpa [parseTypes] using parsed
  | cons first rest ih =>
    cases one : parseType first with
    | none => simp [parseTypes, one] at parsed
    | some type =>
      cases more : parseTypes rest with
      | none => simp [parseTypes, one, more] at parsed
      | some remaining =>
        simp only [parseTypes, one, more] at parsed
        have same : type :: remaining = types := Option.some.inj parsed
        rw [← same]
        simp [one, ih remaining more]

theorem parseTypes_exists (atoms : List Atom)
    (each : ∀ atom ∈ atoms, (parseType atom).isSome = true) :
    ∃ types, parseTypes atoms = some types := by
  induction atoms with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    obtain ⟨type, one⟩ := Option.isSome_iff_exists.mp (each first (by simp))
    obtain ⟨remaining, more⟩ := ih fun atom member => each atom (List.mem_cons_of_mem _ member)
    exact ⟨type :: remaining, by simp [parseTypes, one, more]⟩

theorem annotation_type_supported (atoms : List Atom) (subject type : Atom)
    (admitted : atoms.all annotationSupported = true)
    (member : type ∈ annotations atoms subject) : (parseType type).isSome = true := by
  simp only [annotations, Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes, List.mem_filterMap] at member
  obtain ⟨row, present, selected⟩ := member
  have safe := List.all_eq_true.mp admitted row present
  split at selected
  · rename_i annotationSubject annotationType
    split at selected
    · cases Option.some.inj selected
      cases annotationSubject with
      | symbol name => simpa [annotationSupported] using safe
      | var _ | grounded _ | expression _ => simp [annotationSupported] at safe
    · cases selected
  · cases selected

theorem raw_types_supported (intrinsicRows : List Atom) (world : EagerDFS.World) (head : String)
    (admitted : supported intrinsicRows world = true) :
    ∀ type ∈ rawTypes intrinsicRows world head, (parseType type).isSome = true := by
  have both : intrinsicRows.all annotationSupported = true ∧ world.state.core.all annotationSupported = true := by
    simpa [supported] using admitted
  intro type member
  dsimp only [rawTypes] at member
  split at member
  · exact annotation_type_supported _ _ type both.2 member
  · exact annotation_type_supported _ _ type both.1 member

/-- No type row is silently lost by the codec in an admitted live world. -/
theorem declarations_complete (intrinsicRows : List Atom) (world : EagerDFS.World) (head : String)
    (admitted : supported intrinsicRows world = true) :
    ∃ types, parseTypes (rawTypes intrinsicRows world head) = some types ∧
      declarations intrinsicRows world head = dedupAlpha types := by
  obtain ⟨types, parsed⟩ := parseTypes_exists _ (raw_types_supported intrinsicRows world head admitted)
  exact ⟨types, parsed, congrArg dedupAlpha (parseTypes_filterMap _ _ parsed)⟩

theorem lookup_written_rows (world : EagerDFS.World) (head : String) (rows : List Row)
    (arguments : List Atom) (nonempty : rows ≠ [])
    (sameArity : rows.all (fun row => row.parameters.length == arguments.length) = true)
    (written : world.state.core = (rows.map Row.asType).map (declaration head)) :
    lookup [] world head arguments = .typed rows := by
  have safe : supported [] world = true := by
    simpa only [supported, written, List.all_nil, Bool.true_and] using
      declarations_supported head (rows.map Row.asType)
  have parsed : parseTypes (rawTypes [] world head) = some (rows.map Row.asType) := by
    rw [no_intrinsic_reads_current_world, written, written_declarations_order, parse_typeAtoms]
  simp only [lookup, safe, ↓reduceIte, parsed]
  cases rows with
  | nil => contradiction
  | cons row rest =>
    have rowParse := parseRows_encoded (row :: rest)
    simp only [List.map_cons] at rowParse
    simp only [List.map_cons, rowParse, sameArity, ↓reduceIte]

theorem append_annotation_changes_live_read (world after : EagerDFS.World) (head : String) (type : Ty String)
    (inserted : Effects.insert world.state .self (declaration head type) = some after.state) :
    rawTypes [] after head = rawTypes [] world head ++ [typeAtom type] := by
  obtain ⟨before, read, written⟩ := Effects.insert_reads_back inserted
  have first : before = world.state.core := Option.some.inj read.symm
  have next : after.state.core = world.state.core ++ [declaration head type] := by
    exact Option.some.inj (by simpa only [NamedSpaces.Store.read, first] using written)
  simp [rawTypes, annotations, Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes, next,
    List.filterMap_append, declaration]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeRows
