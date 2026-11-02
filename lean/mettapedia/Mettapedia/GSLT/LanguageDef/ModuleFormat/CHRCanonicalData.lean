import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHROccurrenceEncoding
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mathlib.Data.List.Perm.Basic

/-! Canonical sorting preserves compact ground values and occurrence IDs.
The physical store's order can change, and its source reading changes by the
same permutation. Vectors used for tuple fields and environments keep order. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.CanonicalData

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags PatternLexOrder

theorem vector_canon (patterns : List Pattern) :
    canon (vector patterns) = vector (patterns.map canon) := by
  rw [vector, canon]
  rfl

private theorem traverse_canon {α : Type} (encode : α → Option Pattern)
    (sources : List α) (codes : List Pattern)
    (fixed : ∀ source ∈ sources, ∀ code, encode source = some code → canon code = code)
    (encoded : sources.mapM encode = some codes) : codes.map canon = codes := by
  induction sources generalizing codes with
  | nil =>
    have empty : codes = [] := by simpa using encoded.symm
    subst codes
    rfl
  | cons first rest ih =>
    obtain ⟨code, tail, firstRead, restRead, rfl⟩ := ValueInjectivity.traverse_cons encode first rest codes encoded
    simp only [List.map_cons, fixed first List.mem_cons_self code firstRead,
      ih tail (fun child member => fixed child (List.mem_cons_of_mem first member)) restRead]

theorem digits_canon (index : Nat) : canon (digits index) = digits index := by
  simp [digits, canon, arrange, List.map_map, Function.comp_def]

theorem integer_canon (number : Int) : canon (integer number) = integer number := by
  simp only [integer, canon_apply, List.map_cons, List.map_nil, digits_canon]

theorem occurrenceRef_canon (index : Nat) : canon (occurrenceRef index) = occurrenceRef index := by
  simp only [occurrenceRef, canon_apply, List.map_cons, List.map_nil, digits_canon]

theorem value_canon (vocabulary : Vocabulary) (source : Value) (code : Pattern)
    (encoded : value? vocabulary source = some code) : canon code = code := by
  cases source with
  | integer number =>
    have same : integer number = code := by simpa only [value?, Option.some.injEq] using encoded
    subst code
    exact integer_canon number
  | atom name =>
    cases found : vocabulary.scalars.idxOf? (.atom name) with
    | none => simp [value?, found] at encoded
    | some index =>
      have same : scalarRef index = code := by simpa [value?, found] using encoded
      subst code
      rw [scalarRef, canon]
  | tuple fields =>
    obtain ⟨codes, fieldsRead, rfl⟩ := ValueInjectivity.tuple_encoding vocabulary fields code encoded
    have fixed := traverse_canon (value? vocabulary) fields codes
      (fun field _ code read => value_canon vocabulary field code read) fieldsRead
    simp only [canon_apply, List.map_cons, List.map_nil, vector_canon, fixed]
termination_by sizeOf source

theorem environment_canon (vocabulary : Vocabulary) (environment : Environment)
    (indices : List Nat) (codes : List Pattern)
    (encoded : indices.mapM (fun index =>
      (Mettapedia.Languages.CHR.lookup environment index).bind (value? vocabulary)) = some codes) :
    codes.map canon = codes := by
  apply traverse_canon _ indices codes _ encoded
  intro index _ code read
  obtain ⟨value, _, encoded⟩ := Option.bind_eq_some_iff.mp read
  exact value_canon vocabulary value code encoded

theorem constraint_canon (vocabulary : Vocabulary) (source : Constraint) (code : Pattern)
    (encoded : constraint? vocabulary source = some code) : canon code = code := by
  simp only [constraint?, Option.bind_eq_bind, Option.bind_eq_some_iff] at encoded
  obtain ⟨predicate, _, codes, valuesRead, same⟩ := encoded
  change some (Pattern.apply "ChrConstraint" [predicateRef predicate, vector codes]) = some code at same
  cases Option.some.inj same
  have fixed := traverse_canon (value? vocabulary) source.arguments codes
    (fun value _ code read => value_canon vocabulary value code read) valuesRead
  simp only [canon_apply, List.map_cons, List.map_nil, predicateRef, canon, vector_canon, fixed]

theorem occurrence_canon (vocabulary : Vocabulary) (source : Occurrence) (code : Pattern)
    (encoded : OccurrenceEncoding.encode? vocabulary source = some code) : canon code = code := by
  obtain ⟨constraint, read, rfl⟩ := OccurrenceEncoding.readout vocabulary source code encoded
  simp only [occurrence, canon_apply, List.map_cons, List.map_nil, occurrenceRef_canon,
    constraint_canon vocabulary source.constraint constraint read]

theorem codes_canon (vocabulary : Vocabulary) (sources : List Occurrence) (codes : List Pattern)
    (encoded : sources.mapM (OccurrenceEncoding.encode? vocabulary) = some codes) : codes.map canon = codes :=
  traverse_canon _ sources codes (fun source _ code read => occurrence_canon vocabulary source code read) encoded

theorem store_canon (vocabulary : Vocabulary) (sources : List Occurrence) (codes : List Pattern)
    (encoded : sources.mapM (OccurrenceEncoding.encode? vocabulary) = some codes) :
    canon (store codes) = store (sortLex codes) := by
  simp only [store, canon_apply, List.map_cons, List.map_nil, canon_collection,
    codes_canon vocabulary sources codes encoded, arrange_bag]

theorem canonical_sources (vocabulary : Vocabulary) (sources : List Occurrence) (codes : List Pattern)
    (encoded : sources.mapM (OccurrenceEncoding.encode? vocabulary) = some codes) :
    ∃ (reordered : List Occurrence), reordered.Perm sources ∧
      reordered.mapM (OccurrenceEncoding.encode? vocabulary) = some (sortLex codes) := by
  have paired := OccurrenceEncoding.paired_of_mapM vocabulary sources codes encoded
  obtain ⟨reordered, related, permutation⟩ := List.perm_comp_forall₂ (sortLex_perm codes) paired.flip
  exact ⟨reordered, permutation, OccurrenceEncoding.paired_to_mapM vocabulary related.flip⟩

theorem request_canon (vocabulary : Vocabulary) (query active : Nat)
    (sources : List Occurrence) (codes : List Pattern)
    (encoded : sources.mapM (OccurrenceEncoding.encode? vocabulary) = some codes) :
    canon (request vocabulary query active codes) = request vocabulary query active (sortLex codes) := by
  have predicates : ((List.range vocabulary.predicates.length).map predicateRef).map canon =
      (List.range vocabulary.predicates.length).map predicateRef := by
    simp [predicateRef, List.map_map, Function.comp_def, canon]
  have scalars : (vocabulary.scalars.zipIdx.map (fun entry : Value × Nat =>
      match entry.1 with | .integer number => integer number | _ => scalarRef entry.2)).map canon =
      vocabulary.scalars.zipIdx.map (fun entry : Value × Nat =>
        match entry.1 with | .integer number => integer number | _ => scalarRef entry.2) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro entry _
    rcases entry with ⟨datum, index⟩
    cases datum <;> simp [integer_canon, scalarRef, canon]
  simp only [request, canon_apply, List.map_cons, List.map_nil, vector_canon, predicates,
    occurrenceRef_canon, store_canon vocabulary sources codes encoded]
  exact congrArg (fun slots => Pattern.apply (queryLabel query)
    [vector ((List.range vocabulary.predicates.length).map predicateRef), vector slots,
      occurrenceRef active, store (sortLex codes)]) scalars

#print axioms value_canon
#print axioms canonical_sources
#print axioms request_canon

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.CanonicalData
