import Mettapedia.GSLT.Parsing.CollectionLiteralPresentation
import Mettapedia.Algebra.Collections.CanonicalForm

/-!
# Reader modes for collection literals

A reader mode is one concrete syntax of collection values: an exact
presentation over the shared abstract syntax. A program may mix modules, or
blocks, written in different modes. Each is read once, by its own mode, into
the abstract syntax; after reading, nothing depends on the mode.

* **Reading once makes modes modular.** A module that declares its mode is read
  alike under every ambient mode (`readModule_declared`), and a program is read
  module by module (`readProgram_append`), so a program whose modules all
  declare their modes is read alike under every ambient mode
  (`readProgram_declared`).
* **Printing is safe when tagged or common.** A print tagged with its mode
  reads back exactly under every ambient mode (`readModule_tagged_view`). A
  presentation that every mode reads alike gives untagged prints that read back
  under every ambient mode (`readModule_common_view`).
* **What fails otherwise.** With braces for bags in one mode and for sets in
  another, the text `{ 1 1 }` is a two-element bag in the first, a one-element
  set in the second when it merges repetitions, and refused when it is strict
  (`Controls.ambient_changes_meaning`). A bag printed in the first mode and read
  untagged in the second silently becomes a set (`Controls.cross_mode_print`).
  A module that declares its mode is read alike whatever the ambient mode
  (`Controls.declared_mode_wins`). Quoted code is abstract syntax and is never
  read again; code kept as text and read again is an undeclared module, with
  the same hazards.
* **The untyped reader.** A literal of any kind, its kind chosen by its opening
  token, is an exact presentation of kinded values when openings are distinct
  and elements never print as closings (`anyKind`).
* **Nested values.** Nested collection terms with their printed tokens form an
  exact presentation (`nestedTerms`). Canonical terms, which are the collection
  values, form two (`canonicalValues`): the strict reader accepts only canonical
  prints, the lenient reader canonicalizes, every print of a value reads to that
  value (`canonicalValues_lenient_expand`, `lenient_reads_equal_values`), and
  strict acceptance implies lenient acceptance of the same value
  (`canonicalValues_strict_le_lenient`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CollectionReaderModes

open Mettapedia.GSLT.Parsing.ExactPresentation
open Mettapedia.GSLT.Parsing.CollectionLiteralPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax (CollType)

universe uSort uAst uSurface uMode

/-! ## Modules in modes -/

section Modes

variable {SortName : Type uSort} {Ast : SortName → Type uAst}
  {Surface : SortName → Type uSurface} {Mode : Type uMode}

/-- A module of a program, or a block of one: its text and the reader mode it
declares, if any. -/
structure Module (Mode : Type uMode) (Surface : SortName → Type uSurface) (sort : SortName) where
  declared : Option Mode
  text : Surface sort

variable (modes : Mode → Presentation Ast Surface)

/-- A module is read once, by the mode it declares, or else by the ambient
mode. -/
def readModule (ambient : Mode) {sort : SortName} (module : Module Mode Surface sort) :
    Option (Ast sort) :=
  (modes (module.declared.getD ambient)).expand module.text

/-- A program is read module by module. -/
def readProgram (ambient : Mode) {sort : SortName} (program : List (Module Mode Surface sort)) :
    Option (List (Ast sort)) :=
  program.mapM (readModule modes ambient)

theorem readModule_declared {sort : SortName} (module : Module Mode Surface sort) {mode : Mode}
    (declared : module.declared = some mode) (ambient ambient' : Mode) :
    readModule modes ambient module = readModule modes ambient' module := by
  simp [readModule, declared]

theorem readProgram_append (ambient : Mode) {sort : SortName}
    (first second : List (Module Mode Surface sort)) :
    readProgram modes ambient (first ++ second) =
      (readProgram modes ambient first).bind fun firstRead =>
        (readProgram modes ambient second).map fun secondRead => firstRead ++ secondRead := by
  unfold readProgram
  induction first with
  | nil => simp
  | cons module rest ih =>
      simp only [List.cons_append, List.mapM_cons, ih]
      cases readModule modes ambient module <;> simp
      cases List.mapM (readModule modes ambient) rest <;> simp
      cases List.mapM (readModule modes ambient) second <;> simp

theorem readProgram_declared {sort : SortName} (program : List (Module Mode Surface sort))
    (declared : ∀ module ∈ program, module.declared.isSome) (ambient ambient' : Mode) :
    readProgram modes ambient program = readProgram modes ambient' program := by
  unfold readProgram
  induction program with
  | nil => rfl
  | cons module rest ih =>
      obtain ⟨mode, hasMode⟩ := Option.isSome_iff_exists.mp (declared module (by simp))
      simp only [List.mapM_cons,
        readModule_declared modes module hasMode ambient ambient',
        ih fun other member => declared other (by simp [member])]

/-- **A print tagged with its mode reads back under every ambient mode.** -/
theorem readModule_tagged_view (mode ambient : Mode) {sort : SortName} (tree : Ast sort) :
    readModule modes ambient ⟨some mode, (modes mode).view tree⟩ = some tree := by
  simp [readModule, (modes mode).expand_view]

/-- A presentation that every mode reads alike. -/
def ReadAlike (core : Presentation Ast Surface) : Prop :=
  ∀ (mode : Mode) {sort : SortName} (surface : Surface sort) (tree : Ast sort),
    core.expand surface = some tree → (modes mode).expand surface = some tree

/-- **An untagged print in a common presentation reads back under every
ambient mode.** -/
theorem readModule_common_view (core : Presentation Ast Surface) (alike : ReadAlike modes core)
    (ambient : Mode) {sort : SortName} (tree : Ast sort) :
    readModule modes ambient ⟨none, core.view tree⟩ = some tree :=
  alike _ _ _ (core.expand_view tree)

end Modes

/-! ## Literals of any kind -/

section AnyKind

variable {α : Type*} {Tok : Type*} [DecidableEq Tok] [LinearOrder α]
  (elements : ElementSyntax α Tok) (delimiters : Delimiters Tok)

/-- A literal of any kind, its kind chosen by its opening token, as an exact
presentation of kinded values. -/
def anyKind (separated : Separated elements delimiters) (distinct : OpeningsDistinct delimiters)
    (strict : Bool) :
    Presentation (fun _ : Unit => (kind : CollType) × CollValue α kind)
      (fun _ : Unit => List Tok) where
  key := ⟨if strict then "collection-literal-any-strict" else "collection-literal-any", 1⟩
  expand := fun {_} surface =>
    match readAny elements delimiters strict surface with
    | some ⟨kind, value, []⟩ => some ⟨kind, value⟩
    | _ => none
  view := fun {_} literal => view elements delimiters literal.1 literal.2
  expand_view := by
    intro _ literal
    obtain ⟨kind, value⟩ := literal
    have reads := readAny_view elements delimiters separated distinct strict kind value []
    rw [List.append_nil] at reads
    simp only [reads]

end AnyKind

/-! ## Nested collection values -/

section Nested

open Mettapedia.Algebra.Collections.CanonicalForm

variable {K : Type*} {α : Type*}

/-- Nested collection terms and their printed tokens. -/
def nestedTerms [DecidableEq K] :
    Presentation (fun _ : Unit => Term K α) (fun _ : Unit => List (Token K α)) where
  key := ⟨"nested-collection-term", 1⟩
  expand := fun {_} tokens => Term.read tokens
  view := fun {_} t => t.serialize
  expand_view := fun t => Term.read_serialize t

variable [LinearOrder K] [LinearOrder α]

theorem canonical_canonical (laws : K → KindLaws) (t : Term K α) :
    canonical laws (canonical laws t) = canonical laws t :=
  normalize_normalize Term.serialize_injective t

/-- Collection values: the canonical terms. -/
abbrev CanonicalValue (laws : K → KindLaws) : Type _ :=
  {t : Term K α // canonical laws t = t}

/-- Collection values printed canonically. The strict reader accepts only
canonical prints; the lenient reader canonicalizes what it reads. -/
def canonicalValues (laws : K → KindLaws) (strict : Bool) :
    Presentation (fun _ : Unit => CanonicalValue (α := α) laws)
      (fun _ : Unit => List (Token K α)) where
  key := ⟨if strict then "collection-value-strict" else "collection-value", 1⟩
  expand := fun {_} tokens => (Term.read tokens).bind fun t =>
    if strict then (if canonicalT : canonical laws t = t then some ⟨t, canonicalT⟩ else none)
    else some ⟨canonical laws t, canonical_canonical laws t⟩
  view := fun {_} value => value.1.serialize
  expand_view := by
    intro _ value
    obtain ⟨t, canonicalT⟩ := value
    cases strict <;> simp [Term.read_serialize, canonicalT]

/-- **Every print of a term reads leniently to its value.** -/
theorem canonicalValues_lenient_expand (laws : K → KindLaws) (t : Term K α) :
    (canonicalValues laws false).expand (sort := ()) t.serialize =
      some ⟨canonical laws t, canonical_canonical laws t⟩ := by
  simp [canonicalValues, Term.read_serialize]

/-- Prints of equal values read to one value. -/
theorem lenient_reads_equal_values (laws : K → KindLaws) {s t : Term K α}
    (conv : Conv laws s t) :
    (canonicalValues laws false).expand (sort := ()) s.serialize =
      (canonicalValues laws false).expand (sort := ()) t.serialize := by
  rw [canonicalValues_lenient_expand, canonicalValues_lenient_expand]
  congr 2
  exact (canonical_eq_iff laws).mpr conv

theorem canonicalValues_strict_le_lenient (laws : K → KindLaws) (tokens : List (Token K α))
    (value : CanonicalValue (α := α) laws)
    (accepted : (canonicalValues laws true).expand (sort := ()) tokens = some value) :
    (canonicalValues laws false).expand (sort := ()) tokens = some value := by
  simp only [canonicalValues, if_true] at accepted ⊢
  cases reading : Term.read tokens with
  | none => simp [reading] at accepted
  | some t =>
      simp only [reading, Option.bind_some] at accepted ⊢
      split at accepted
      · next canonicalT =>
          simp only [Option.some.injEq] at accepted
          subst accepted
          simp [canonicalT]
      · simp at accepted

end Nested

/-! ## Controls -/

namespace Controls

/-- Concrete spellings of the controls. -/
inductive Spelling where
  | brace | closeBrace | barBrace | closeBarBrace | hashBrace | closeHashBrace
  | bracket | closeBracket
  | numeral (value : ℕ)
  deriving DecidableEq, Repr

/-- Numerals spell the natural-number elements. -/
def numerals : ElementSyntax ℕ Spelling where
  print := .numeral
  read := fun | .numeral value => some value | _ => none
  read_print := fun _ => rfl

/-- Braces for bags and bar braces for sets. -/
def bagBraces : Delimiters Spelling where
  opening := fun | .vec => .bracket | .hashBag => .brace | .hashSet => .barBrace
  closing := fun | .vec => .closeBracket | .hashBag => .closeBrace | .hashSet => .closeBarBrace

/-- Braces for sets and hash braces for bags. -/
def setBraces : Delimiters Spelling where
  opening := fun | .vec => .bracket | .hashBag => .hashBrace | .hashSet => .brace
  closing := fun | .vec => .closeBracket | .hashBag => .closeHashBrace | .hashSet => .closeBrace

theorem bagBraces_separated : Separated numerals bagBraces := by
  intro kind value
  cases kind <;> simp [numerals, bagBraces]

theorem setBraces_separated : Separated numerals setBraces := by
  intro kind value
  cases kind <;> simp [numerals, setBraces]

theorem bagBraces_distinct : OpeningsDistinct bagBraces := by
  intro first second same
  cases first <;> cases second <;> simp_all [bagBraces]

theorem setBraces_distinct : OpeningsDistinct setBraces := by
  intro first second same
  cases first <;> cases second <;> simp_all [setBraces]

/-- Three reader modes. -/
inductive Mode where
  | bagsInBraces | setsInBraces | setsInBracesStrict
  deriving DecidableEq, Repr

/-- The presentation of each mode. -/
def modes : Mode →
    Presentation (fun _ : Unit => (kind : CollType) × CollValue ℕ kind)
      (fun _ : Unit => List Spelling)
  | .bagsInBraces => anyKind numerals bagBraces bagBraces_separated bagBraces_distinct false
  | .setsInBraces => anyKind numerals setBraces setBraces_separated setBraces_distinct false
  | .setsInBracesStrict => anyKind numerals setBraces setBraces_separated setBraces_distinct true

/-- The text `{ 1 1 }`. -/
def twoOnes : List Spelling := [.brace, .numeral 1, .numeral 1, .closeBrace]

/-- **An undeclared module means different values under different ambient
modes.** -/
theorem ambient_changes_meaning :
    readModule modes .bagsInBraces (⟨none, twoOnes⟩ : Module Mode _ ()) =
        some ⟨.hashBag, ({1, 1} : Multiset ℕ)⟩ ∧
      readModule modes .setsInBraces (⟨none, twoOnes⟩ : Module Mode _ ()) =
        some ⟨.hashSet, ({1} : Finset ℕ)⟩ ∧
      readModule modes .setsInBracesStrict (⟨none, twoOnes⟩ : Module Mode _ ()) = none := by
  refine ⟨rfl, rfl, rfl⟩

/-- **A module that declares its mode is read alike under every ambient
mode.** -/
theorem declared_mode_wins :
    readModule modes .setsInBraces (⟨some .bagsInBraces, twoOnes⟩ : Module Mode _ ()) =
      some ⟨.hashBag, ({1, 1} : Multiset ℕ)⟩ := rfl

/-- **A bag printed in one mode and read untagged in another silently becomes
a set.** -/
theorem cross_mode_print :
    (modes .bagsInBraces).view (sort := ()) ⟨.hashBag, ({1, 1} : Multiset ℕ)⟩ = twoOnes ∧
      (modes .setsInBraces).expand (sort := ()) twoOnes = some ⟨.hashSet, ({1} : Finset ℕ)⟩ := by
  refine ⟨?_, rfl⟩
  have sorted : canonical (α := ℕ) .hashBag ({1, 1} : Multiset ℕ) = [1, 1] := by
    show Multiset.sort (({1, 1} : Multiset ℕ)) = [1, 1]
    rw [show ({1, 1} : Multiset ℕ) = (([1, 1] : List ℕ) : Multiset ℕ) from rfl, Multiset.coe_sort]
    exact List.mergeSort_of_pairwise (by decide)
  show view numerals bagBraces .hashBag ({1, 1} : Multiset ℕ) = twoOnes
  unfold view
  rw [sorted]
  rfl

end Controls

end Mettapedia.GSLT.Parsing.CollectionReaderModes
