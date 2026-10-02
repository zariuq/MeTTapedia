import Mettapedia.GSLT.LanguageDef.ConstructorSupport
import Mettapedia.OSLF.MeTTaIL.PatternCodeRecursion

/-!
# The action of a map of symbols, on codes

A map of symbols acts on a pattern by renaming its constructors.  The
renaming is an arbitrary function on strings, so nothing can be said about
its action on codes in general.  On the well-sorted patterns of one language
only the finitely many declared constructors occur.  There the action agrees
with that of a finite table, and the action of a finite table is primitive
recursive on codes.

So the term map of any map of declarations is tracked, on the terms of its
source, by a primitive recursive function on codes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open StructuralMorphism
open WellSorted

/-! ## The constructors of a well-sorted pattern are declared -/

/-- The label is that of a declared constructor. -/
def DeclaredLabel (language : LanguageDef) (label : String) : Prop :=
  label ∈ language.terms.map (·.label)

namespace WellSorted

mutual
  /-- **Every constructor of a well-sorted pattern is declared.** -/
  theorem HasType.constructorsDeclared {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      ConstructorsWithin (DeclaredLabel language) pattern := by
    cases typed with
    | bvar lookup => simp [ConstructorsWithin]
    | fvar lookup => simp [ConstructorsWithin]
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        exact ⟨List.mem_map_of_mem membership, argumentsTyped.constructorsDeclared⟩
    | lambda bodyTyped => exact bodyTyped.constructorsDeclared
    | multiLambda bodyTyped => exact bodyTyped.constructorsDeclared
    | subst bodyTyped replacementTyped =>
        exact ⟨bodyTyped.constructorsDeclared, replacementTyped.constructorsDeclared⟩
    | collection elementsTyped => exact elementsTyped.constructorsDeclared
    | collectionConstructor membership shape elementsTyped =>
        exact elementsTyped.constructorsDeclared

  /-- The constructors of well-sorted arguments are declared. -/
  theorem ArgumentsHaveTypes.constructorsDeclared {language : LanguageDef}
      {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      ConstructorListWithin (DeclaredLabel language) arguments := by
    cases typed with
    | nil => simp [ConstructorListWithin]
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact ⟨argumentTyped.constructorsDeclared, argumentsTyped.constructorsDeclared⟩

  /-- The constructors of well-sorted elements are declared. -/
  theorem ElementsHaveType.constructorsDeclared {language : LanguageDef}
      {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType) :
      ConstructorListWithin (DeclaredLabel language) elements := by
    cases typed with
    | nil => simp [ConstructorListWithin]
    | cons elementTyped elementsTyped =>
        exact ⟨elementTyped.constructorsDeclared, elementsTyped.constructorsDeclared⟩
end

end WellSorted

/-! ## Maps of symbols that agree on the constructors of a pattern -/

mutual
  /-- Two maps of symbols that agree on the constructors of a pattern act on
  it alike. -/
  theorem mapPattern_congr {first second : LanguageDefSymbolMap} :
      ∀ {pattern : Pattern},
        ConstructorsWithin (fun label => first.constructor label = second.constructor label)
          pattern →
        mapPattern first pattern = mapPattern second pattern
    | .bvar _, _ => rfl
    | .fvar _, _ => rfl
    | .apply _ arguments, agree => by
        simp only [mapPattern]
        rw [agree.1, mapPatternList_congr agree.2]
    | .lambda _ body, agree => by
        simp only [mapPattern]
        rw [mapPattern_congr (pattern := body) agree]
    | .multiLambda _ _ body, agree => by
        simp only [mapPattern]
        rw [mapPattern_congr (pattern := body) agree]
    | .subst body replacement, agree => by
        simp only [mapPattern]
        rw [mapPattern_congr (pattern := body) agree.1,
          mapPattern_congr (pattern := replacement) agree.2]
    | .collection _ elements _, agree => by
        simp only [mapPattern]
        rw [mapPatternList_congr (patterns := elements) agree]

  /-- List companion to `mapPattern_congr`. -/
  theorem mapPatternList_congr {first second : LanguageDefSymbolMap} :
      ∀ {patterns : List Pattern},
        ConstructorListWithin
          (fun label => first.constructor label = second.constructor label) patterns →
        mapPatternList first patterns = mapPatternList second patterns
    | [], _ => rfl
    | pattern :: patterns, agree => by
        simp only [mapPatternList]
        rw [mapPattern_congr (pattern := pattern) agree.1,
          mapPatternList_congr (patterns := patterns) agree.2]
end

/-! ## Renaming by a finite table -/

/-- A renaming given by a finite table: a listed label goes to its entry,
every other label to itself. -/
def tableRename (table : List (String × String)) (label : String) : String :=
  (table.lookup label).getD label

/-- The map of symbols that renames constructors by a finite table. -/
def tableSymbols (table : List (String × String)) : LanguageDefSymbolMap where
  sort := id
  constructor := tableRename table
  relation := id
  equation := id
  rewrite := id

/-- The table of the values of a renaming on a list of labels. -/
def valuesTable (rename : String → String) (labels : List String) : List (String × String) :=
  labels.map fun label => (label, rename label)

/-- The table of values renames a listed label as the renaming does. -/
theorem tableRename_valuesTable (rename : String → String) {labels : List String}
    {label : String} (listed : label ∈ labels) :
    tableRename (valuesTable rename labels) label = rename label := by
  induction labels with
  | nil => cases listed
  | cons head tail recurse =>
      by_cases same : label = head
      · subst same
        simp [tableRename, valuesTable]
      · have inTail : label ∈ tail := by
          rcases List.mem_cons.mp listed with isHead | inTail
          · exact absurd isHead same
          · exact inTail
        have differs : (label == head) = false := by simpa using same
        have step : tableRename (valuesTable rename (head :: tail)) label =
            tableRename (valuesTable rename tail) label := by
          simp [tableRename, valuesTable, List.lookup, differs]
        rw [step]
        exact recurse inTail

/-- **On a pattern whose constructors are all listed, a map of symbols acts
as the finite table of its values on the list.** -/
theorem mapPattern_eq_table (symbols : LanguageDefSymbolMap) (labels : List String)
    {pattern : Pattern} (listed : ConstructorsWithin (fun label => label ∈ labels) pattern) :
    mapPattern symbols pattern =
      mapPattern (tableSymbols (valuesTable symbols.constructor labels)) pattern :=
  mapPattern_congr (ConstructorsWithin.mono
    (fun _ member => (tableRename_valuesTable symbols.constructor member).symm) listed)

/-! ## A finite table on codes -/

/-- The renaming of a finite table, on the codes of labels. -/
def tableRenameCode : List (String × String) → ℕ → ℕ
  | [], code => code
  | entry :: table, code =>
      if code = stringCode entry.1 then stringCode entry.2 else tableRenameCode table code

/-- The function on codes tracks the renaming. -/
theorem tableRenameCode_stringCode (table : List (String × String)) (label : String) :
    tableRenameCode table (stringCode label) = stringCode (tableRename table label) := by
  induction table with
  | nil => rfl
  | cons entry table recurse =>
      by_cases same : label = entry.1
      · subst same
        simp [tableRenameCode, tableRename, List.lookup]
      · have codes : stringCode label ≠ stringCode entry.1 :=
          fun equal => same (stringCode_injective equal)
        have differs : (label == entry.1) = false := by simpa using same
        have step : tableRename (entry :: table) label = tableRename table label := by
          obtain ⟨key, value⟩ := entry
          simp only [tableRename, List.lookup]
          rw [show (label == key) = false from differs]
        rw [tableRenameCode, if_neg codes, step]
        exact recurse

/-- The renaming of a finite table is primitive recursive on codes. -/
theorem tableRenameCode_primrec (table : List (String × String)) :
    Primrec (tableRenameCode table) := by
  induction table with
  | nil => exact Primrec.id
  | cons entry table recurse =>
      exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const _)) (Primrec.const _) recurse

/-! ## Renaming the constructor at the root -/

/-- Rename the constructor at the root of a pattern. -/
def renameRoot (rename : String → String) : Pattern → Pattern
  | .apply label arguments => .apply (rename label) arguments
  | pattern => pattern

/-- **The action of a map of symbols rewrites a pattern from the leaves up**,
renaming the constructor at each node. -/
theorem mapPattern_eq_bottomUp (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    mapPattern symbols pattern = pattern.bottomUp (renameRoot symbols.constructor) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly label arguments recurse =>
      simp only [mapPattern, mapPatternList_eq_map, Pattern.bottomUp,
        Pattern.bottomUpList_eq_map, renameRoot]
      rw [List.map_congr_left recurse]
  | hlambda binder body recurse =>
      simp only [mapPattern, Pattern.bottomUp, renameRoot]
      rw [recurse]
  | hmultiLambda arity binders body recurse =>
      simp only [mapPattern, Pattern.bottomUp, renameRoot]
      rw [recurse]
  | hsubst body replacement recurseBody recurseReplacement =>
      simp only [mapPattern, Pattern.bottomUp, renameRoot]
      rw [recurseBody, recurseReplacement]
  | hcollection kind elements rest recurse =>
      simp only [mapPattern, mapPatternList_eq_map, Pattern.bottomUp,
        Pattern.bottomUpList_eq_map, renameRoot]
      rw [List.map_congr_left recurse]

/-- Rename, on codes, the constructor at the root. -/
def renameRootCode (renameCode : ℕ → ℕ) (code : ℕ) : ℕ :=
  if code.unpair.1 = 2 then
    Nat.pair 2 (Nat.pair (renameCode code.unpair.2.unpair.1) code.unpair.2.unpair.2)
  else code

/-- The function on codes tracks the renaming at the root. -/
theorem renameRootCode_patternCode {rename : String → String} {renameCode : ℕ → ℕ}
    (tracks : ∀ label, renameCode (stringCode label) = stringCode (rename label))
    (pattern : Pattern) :
    renameRootCode renameCode (patternCode pattern) =
      patternCode (renameRoot rename pattern) := by
  cases pattern with
  | apply label arguments =>
      simp [renameRootCode, patternCode, renameRoot, tracks]
  | bvar index => simp [renameRootCode, patternCode, renameRoot]
  | fvar name => simp [renameRootCode, patternCode, renameRoot]
  | lambda binder body => simp [renameRootCode, patternCode, renameRoot]
  | multiLambda arity binders body => simp [renameRootCode, patternCode, renameRoot]
  | subst body replacement => simp [renameRootCode, patternCode, renameRoot]
  | collection kind elements rest => simp [renameRootCode, patternCode, renameRoot]

/-- Renaming at the root is primitive recursive on codes when the renaming of
labels is. -/
theorem renameRootCode_primrec {renameCode : ℕ → ℕ} (primitive : Primrec renameCode) :
    Primrec (renameRootCode renameCode) := by
  have tag : Primrec fun code : ℕ => code.unpair.1 := Primrec.fst.comp Primrec.unpair
  have payload : Primrec fun code : ℕ => code.unpair.2 := Primrec.snd.comp Primrec.unpair
  have label : Primrec fun code : ℕ => code.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp payload)
  have rest : Primrec fun code : ℕ => code.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp payload)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
    (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (primitive.comp label) rest))
    Primrec.id

/-! ## The action on codes -/

/-- The function on codes that tracks the action of a finite table. -/
def tableMapCode (table : List (String × String)) : ℕ → ℕ :=
  bottomUpCode (renameRootCode (tableRenameCode table))

/-- **The action of a finite table is primitive recursive on codes.** -/
theorem tableMapCode_primrec (table : List (String × String)) : Primrec (tableMapCode table) :=
  bottomUpCode_primrec (renameRootCode_primrec (tableRenameCode_primrec table))

/-- The function on codes tracks the action of the table. -/
theorem tableMapCode_patternCode (table : List (String × String)) (pattern : Pattern) :
    tableMapCode table (patternCode pattern) =
      patternCode (mapPattern (tableSymbols table) pattern) := by
  rw [mapPattern_eq_bottomUp]
  exact bottomUpCode_patternCode
    (renameRootCode_patternCode (rename := tableRename table)
      (tableRenameCode_stringCode table)) pattern

/-- **The action of a map of symbols on the well-sorted patterns of a
language is tracked by a primitive recursive function on codes.** -/
theorem exists_primrec_mapPatternCode (symbols : LanguageDefSymbolMap) (language : LanguageDef) :
    ∃ track : ℕ → ℕ, Primrec track ∧
      ∀ {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
        HasType language free bound pattern type →
          track (patternCode pattern) = patternCode (mapPattern symbols pattern) := by
  refine ⟨tableMapCode (valuesTable symbols.constructor (language.terms.map (·.label))),
    tableMapCode_primrec _, ?_⟩
  intro free bound pattern type typed
  have listed : ConstructorsWithin (fun label => label ∈ language.terms.map (·.label)) pattern :=
    typed.constructorsDeclared
  rw [tableMapCode_patternCode, ← mapPattern_eq_table symbols _ listed]

end Mettapedia.GSLT.LanguageDef
