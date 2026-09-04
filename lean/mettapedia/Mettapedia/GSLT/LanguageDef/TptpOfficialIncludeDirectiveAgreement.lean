import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveLanguageDef
import Mettapedia.OSLF.MeTTaIL.ContextualRootDispatch

/-!
# Exact agreement for official TPTP include directives

This module connects the independent, total projection of the official
ParserPack include AST to contextual execution of the declared include
LanguageDef.  Successful projections produce an exact stable singleton; the
list encoding preserves source order and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveLanguageDef

private abbrev base : BasePremiseEvaluator :=
  engineBasePremises RelationEnv.empty

def encodeLexeme (value : String) : Pattern := .apply value []

/-- The official name-list grammar is nonempty.  The optional result makes
that invariant visible without inventing an empty target constructor. -/
def encodeNames? : List String → Option Pattern
  | [] => none
  | [name] => some (namesOne (encodeLexeme name))
  | name :: next :: rest => do
      let encodedRest <- encodeNames? (next :: rest)
      some (namesCons (encodeLexeme name) encodedRest)

def encodeSelection? : FormulaSelection → Option Pattern
  | .implicitAll => some implicitAll
  | .explicitAll => some explicitAll
  | .named names => namedSelection <$> encodeNames? names

def encodeSpace : Option String → Pattern
  | none => noSpace
  | some name => someSpace (encodeLexeme name)

def encodeDirectiveView? (view : IncludeDirectiveView) : Option Pattern := do
  let selection <- encodeSelection? view.selection
  some (decodedDirective (encodeLexeme view.requestedFile) selection
    (encodeSpace view.spaceName) view.raw)

/-- A source request has one exact result at every contextual fuel above a
finite structural threshold. -/
def EventuallyExact (source result : Pattern) : Prop :=
  ∃ requiredFuel, ∀ fuel, requiredFuel ≤ fuel →
    rewriteAt base language fuel source = [result]

private theorem nameRootRules :
    language.rewrites.filter (rootMatches "tptp-include:decode-name") =
      [nameWordRule "tptp-include:name-lower"
          "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word",
       nameWordRule "tptp-include:name-single-quoted"
          "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
       nameWordRule "tptp-include:name-back-quoted"
          "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted",
       nameIntegerRule] := by
  rfl

private theorem fileRootRules :
    language.rewrites.filter (rootMatches "tptp-include:decode-file-name") =
      [fileNameRule "tptp-include:file-lower"
          "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word",
       fileNameRule "tptp-include:file-single-quoted"
          "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
       fileNameRule "tptp-include:file-back-quoted"
          "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted"] := by
  rfl

private theorem nameListRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include:decode-name-list") =
      [nameListOneRule, nameListConsRule] := by
  rfl

private theorem selectionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include:decode-selection") =
      [selectionNamedRule, selectionExplicitAllRule] := by
  rfl

private theorem spaceRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include:decode-space-name") =
      [spaceNameRule] := by
  rfl

private theorem directiveRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include:decode-directive") =
      [directiveImplicitRule, directiveSelectionRule, directiveSpaceRule] := by
  rfl

private theorem eventuallyExact_of_one_step (source result : Pattern)
    (step : ∀ fuel, rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor

private theorem eventuallyExact_of_one_premise
    (premiseSource premiseResult source result : Pattern)
    (premiseExact : EventuallyExact premiseSource premiseResult)
    (step : ∀ fuel,
      rewriteAt base language fuel premiseSource = [premiseResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases premiseExact with ⟨requiredFuel, premiseExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using
        step predecessor (premiseExact predecessor (by omega))

private theorem eventuallyExact_of_two_premises
    (firstSource firstResult secondSource secondResult source result : Pattern)
    (firstExact : EventuallyExact firstSource firstResult)
    (secondExact : EventuallyExact secondSource secondResult)
    (step : ∀ fuel,
      rewriteAt base language fuel firstSource = [firstResult] →
      rewriteAt base language fuel secondSource = [secondResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases firstExact with ⟨firstFuel, firstExact⟩
  rcases secondExact with ⟨secondFuel, secondExact⟩
  refine ⟨max firstFuel secondFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor
        (firstExact predecessor (by omega))
        (secondExact predecessor (by omega))

private theorem eventuallyExact_of_three_premises
    (firstSource firstResult secondSource secondResult
      thirdSource thirdResult source result : Pattern)
    (firstExact : EventuallyExact firstSource firstResult)
    (secondExact : EventuallyExact secondSource secondResult)
    (thirdExact : EventuallyExact thirdSource thirdResult)
    (step : ∀ fuel,
      rewriteAt base language fuel firstSource = [firstResult] →
      rewriteAt base language fuel secondSource = [secondResult] →
      rewriteAt base language fuel thirdSource = [thirdResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases firstExact with ⟨firstFuel, firstExact⟩
  rcases secondExact with ⟨secondFuel, secondExact⟩
  rcases thirdExact with ⟨thirdFuel, thirdExact⟩
  refine ⟨max firstFuel (max secondFuel thirdFuel) + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor
        (firstExact predecessor (by omega))
        (secondExact predecessor (by omega))
        (thirdExact predecessor (by omega))

local macro "include_row_simp" : tactic =>
  `(tactic|
    simp [nameWordRule, nameIntegerRule, fileNameRule, nameListOneRule,
      nameListConsRule, selectionNamedRule, selectionExplicitAllRule,
      spaceNameRule, directiveImplicitRule, directiveSelectionRule,
      directiveSpaceRule, sourceNameWord, sourceIntegerName, sourceFileName,
      sourceAtomicWord, sourceToken, sourceDirective, decodeName, decodedName,
      decodeNameList, decodedNameList, namesOne, namesCons, decodeSelection,
      decodedSelection, implicitAll, explicitAll, namedSelection,
      decodeFileName, decodedFileName, decodeSpaceName, decodedSpaceName,
      noSpace, someSpace, decodeDirective, decodedDirective, mkRule,
      congruence, typed, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

theorem name_lower_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeName (sourceNameWord "tptp92-ast:atomic-word:alt-1"
        "tptp92-ast:token:lower-word" lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceNameWord, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  include_row_simp

theorem name_singleQuoted_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeName (sourceNameWord "tptp92-ast:atomic-word:alt-2"
        "tptp92-ast:token:single-quoted" lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceNameWord, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  include_row_simp

theorem name_backQuoted_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeName (sourceNameWord "tptp92-ast:atomic-word:alt-3"
        "tptp92-ast:token:back-quoted" lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceNameWord, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  include_row_simp

theorem name_integer_eventuallyExact (lexeme : Pattern) :
    EventuallyExact (decodeName (sourceIntegerName lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceIntegerName, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  include_row_simp

theorem file_lower_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeFileName (sourceFileName "tptp92-ast:atomic-word:alt-1"
        "tptp92-ast:token:lower-word" lexeme))
      (decodedFileName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeFileName, sourceFileName, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, fileRootRules]
  include_row_simp

theorem file_singleQuoted_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeFileName (sourceFileName "tptp92-ast:atomic-word:alt-2"
        "tptp92-ast:token:single-quoted" lexeme))
      (decodedFileName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeFileName, sourceFileName, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, fileRootRules]
  include_row_simp

theorem file_backQuoted_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeFileName (sourceFileName "tptp92-ast:atomic-word:alt-3"
        "tptp92-ast:token:back-quoted" lexeme))
      (decodedFileName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeFileName, sourceFileName, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, fileRootRules]
  include_row_simp

theorem nameList_one_rewriteAt_exact (fuel : Nat)
    (sourceName lexeme : Pattern)
    (nameStep : rewriteAt base language fuel (decodeName sourceName) =
      [decodedName lexeme]) :
    rewriteAt base language (fuel + 1)
        (decodeNameList
          (.apply "tptp92-ast:name-list:alt-1" [sourceName])) =
      [decodedNameList (namesOne lexeme)] := by
  simp only [decodeName, decodedName, a] at nameStep
  simp only [decodeNameList, a]
  rw [rewriteAt_eq_root_filter, nameListRootRules]
  include_row_simp
  simp [nameStep, matchPattern, matchArgs, mergeBindings]

theorem nameList_cons_rewriteAt_exact (fuel : Nat)
    (sourceName sourceRest lexeme encodedRest : Pattern)
    (nameStep : rewriteAt base language fuel (decodeName sourceName) =
      [decodedName lexeme])
    (restStep : rewriteAt base language fuel (decodeNameList sourceRest) =
      [decodedNameList encodedRest]) :
    rewriteAt base language (fuel + 1)
        (decodeNameList
          (.apply "tptp92-ast:name-list:alt-2" [sourceName, sourceRest])) =
      [decodedNameList (namesCons lexeme encodedRest)] := by
  simp only [decodeName, decodedName, decodeNameList, decodedNameList, a]
    at nameStep restStep
  simp only [decodeNameList, a]
  rw [rewriteAt_eq_root_filter, nameListRootRules]
  include_row_simp
  simp [nameStep, restStep, matchPattern, matchArgs, mergeBindings]

theorem nameList_one_eventuallyExact
    (sourceName lexeme : Pattern)
    (nameExact : EventuallyExact (decodeName sourceName)
      (decodedName lexeme)) :
    EventuallyExact
      (decodeNameList (.apply "tptp92-ast:name-list:alt-1" [sourceName]))
      (decodedNameList (namesOne lexeme)) := by
  exact eventuallyExact_of_one_premise _ _ _ _ nameExact
    (fun fuel nameStep => nameList_one_rewriteAt_exact fuel
      sourceName lexeme nameStep)

theorem nameList_cons_eventuallyExact
    (sourceName sourceRest lexeme encodedRest : Pattern)
    (nameExact : EventuallyExact (decodeName sourceName)
      (decodedName lexeme))
    (restExact : EventuallyExact (decodeNameList sourceRest)
      (decodedNameList encodedRest)) :
    EventuallyExact
      (decodeNameList
        (.apply "tptp92-ast:name-list:alt-2" [sourceName, sourceRest]))
      (decodedNameList (namesCons lexeme encodedRest)) := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _ nameExact restExact
    (fun fuel nameStep restStep => nameList_cons_rewriteAt_exact fuel
      sourceName sourceRest lexeme encodedRest nameStep restStep)

/-- Exact operational meaning of every name accepted by the independent
canonical include projection. -/
theorem decodeCanonicalName_eventuallyExact (source : Pattern)
    (result : String)
    (decoded : decodeCanonicalName? source = some result) :
    EventuallyExact (decodeName source) (decodedName (encodeLexeme result)) := by
  fun_cases decodeCanonicalName? source
  · rename_i word
    fun_cases decodeCanonicalAtomicWord? word
    · rename_i lexeme
      simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact name_lower_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact name_singleQuoted_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact name_backQuoted_eventuallyExact (.apply lexeme [])
    · simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
  · rename_i lexeme
    simp [decodeCanonicalName?] at decoded
    subst result
    exact name_integer_eventuallyExact (.apply lexeme [])
  · simp [decodeCanonicalName?] at decoded

/-- Exact operational meaning of every file name accepted by the independent
canonical include projection. -/
theorem decodeFileName_eventuallyExact (source : Pattern) (result : String)
    (decoded : decodeFileName? source = some result) :
    EventuallyExact (decodeFileName source)
      (decodedFileName (encodeLexeme result)) := by
  fun_cases decodeFileName? source
  · rename_i word
    fun_cases decodeCanonicalAtomicWord? word
    · rename_i lexeme
      simp [decodeFileName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact file_lower_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [decodeFileName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact file_singleQuoted_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [decodeFileName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact file_backQuoted_eventuallyExact (.apply lexeme [])
    · simp [decodeFileName?, decodeCanonicalAtomicWord?] at decoded
  · simp [decodeFileName?] at decoded

private theorem encodeNames_cons_of_tail {name : String}
    {names : List String} {encoded : Pattern}
    (tailEncoded : encodeNames? names = some encoded) :
    encodeNames? (name :: names) =
      some (namesCons (encodeLexeme name) encoded) := by
  cases names with
  | nil => simp [encodeNames?] at tailEncoded
  | cons next rest => simp [encodeNames?, tailEncoded]

/-- Recursive name-list agreement.  The target encoder has no empty-list
case because the official grammar cannot produce one. -/
theorem decodeNameList_eventuallyExact (source : Pattern)
    (names : List String)
    (decoded : decodeNameList? source = some names) :
    ∃ encoded,
      encodeNames? names = some encoded ∧
      EventuallyExact (decodeNameList source) (decodedNameList encoded) := by
  unfold decodeNameList? at decoded
  split at decoded
  · rename_i sourceShape sourceName
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨name, nameDecoded, resultEquality⟩
    cases resultEquality
    refine ⟨namesOne (encodeLexeme name), rfl, ?_⟩
    exact nameList_one_eventuallyExact sourceName (encodeLexeme name)
      (decodeCanonicalName_eventuallyExact sourceName name nameDecoded)
  · rename_i sourceShape sourceName sourceRest
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨name, nameDecoded, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨restNames, restDecoded, resultEquality⟩
    cases resultEquality
    rcases decodeNameList_eventuallyExact sourceRest restNames restDecoded with
      ⟨encodedRest, restEncoded, restExact⟩
    refine ⟨namesCons (encodeLexeme name) encodedRest,
      encodeNames_cons_of_tail restEncoded, ?_⟩
    exact nameList_cons_eventuallyExact sourceName sourceRest
      (encodeLexeme name) encodedRest
      (decodeCanonicalName_eventuallyExact sourceName name nameDecoded)
      restExact
  · contradiction
termination_by sizeOf source

theorem selection_named_rewriteAt_exact (fuel : Nat)
    (sourceNames encodedNames : Pattern)
    (namesStep : rewriteAt base language fuel
      (decodeNameList sourceNames) = [decodedNameList encodedNames]) :
    rewriteAt base language (fuel + 1)
        (decodeSelection
          (.apply "tptp92-ast:formula-selection:alt-1" [sourceNames])) =
      [decodedSelection (namedSelection encodedNames)] := by
  simp only [decodeNameList, decodedNameList, a] at namesStep
  simp only [decodeSelection, a]
  rw [rewriteAt_eq_root_filter, selectionRootRules]
  include_row_simp
  simp [namesStep, matchPattern, matchArgs, mergeBindings]

theorem selection_explicitAll_eventuallyExact :
    EventuallyExact
      (decodeSelection
        (.apply "tptp92-ast:formula-selection:alt-2" []))
      (decodedSelection explicitAll) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeSelection, a]
  rw [rewriteAt_eq_root_filter, selectionRootRules]
  include_row_simp

theorem selection_named_eventuallyExact
    (sourceNames encodedNames : Pattern)
    (namesExact : EventuallyExact (decodeNameList sourceNames)
      (decodedNameList encodedNames)) :
    EventuallyExact
      (decodeSelection
        (.apply "tptp92-ast:formula-selection:alt-1" [sourceNames]))
      (decodedSelection (namedSelection encodedNames)) := by
  exact eventuallyExact_of_one_premise _ _ _ _ namesExact
    (fun fuel namesStep => selection_named_rewriteAt_exact fuel
      sourceNames encodedNames namesStep)

theorem decodeFormulaSelection_eventuallyExact (source : Pattern)
    (selection : FormulaSelection)
    (decoded : decodeFormulaSelection? source = some selection) :
    ∃ encoded,
      encodeSelection? selection = some encoded ∧
      EventuallyExact (decodeSelection source) (decodedSelection encoded) := by
  unfold decodeFormulaSelection? at decoded
  split at decoded
  · rename_i sourceShape sourceNames
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨names, namesDecoded, resultEquality⟩
    cases resultEquality
    rcases decodeNameList_eventuallyExact sourceNames names namesDecoded with
      ⟨encodedNames, namesEncoded, namesExact⟩
    refine ⟨namedSelection encodedNames, ?_,
      selection_named_eventuallyExact sourceNames encodedNames namesExact⟩
    simp [encodeSelection?, namesEncoded]
  · cases decoded
    exact ⟨explicitAll, rfl, selection_explicitAll_eventuallyExact⟩
  · contradiction

theorem space_rewriteAt_exact (fuel : Nat)
    (sourceName lexeme : Pattern)
    (nameStep : rewriteAt base language fuel (decodeName sourceName) =
      [decodedName lexeme]) :
    rewriteAt base language (fuel + 1)
        (decodeSpaceName
          (.apply "tptp92-ast:space-name:alt-1" [sourceName])) =
      [decodedSpaceName lexeme] := by
  simp only [decodeName, decodedName, a] at nameStep
  simp only [decodeSpaceName, a]
  rw [rewriteAt_eq_root_filter, spaceRootRules]
  include_row_simp
  simp [nameStep, matchPattern, matchArgs, mergeBindings]

theorem space_eventuallyExact (sourceName lexeme : Pattern)
    (nameExact : EventuallyExact (decodeName sourceName)
      (decodedName lexeme)) :
    EventuallyExact
      (decodeSpaceName
        (.apply "tptp92-ast:space-name:alt-1" [sourceName]))
      (decodedSpaceName lexeme) := by
  exact eventuallyExact_of_one_premise _ _ _ _ nameExact
    (fun fuel nameStep => space_rewriteAt_exact fuel sourceName lexeme nameStep)

theorem decodeSpaceName_eventuallyExact (source : Pattern) (result : String)
    (decoded : decodeSpaceName? source = some result) :
    EventuallyExact (decodeSpaceName source)
      (decodedSpaceName (encodeLexeme result)) := by
  unfold decodeSpaceName? at decoded
  split at decoded
  · rename_i sourceShape sourceName
    exact space_eventuallyExact sourceName (encodeLexeme result)
      (decodeCanonicalName_eventuallyExact sourceName result decoded)
  · contradiction

theorem directive_implicit_rewriteAt_exact (fuel : Nat)
    (sourceFile file : Pattern)
    (fileStep : rewriteAt base language fuel (decodeFileName sourceFile) =
      [decodedFileName file]) :
    let optionals := .apply "tptp92-ast:include-optionals:alt-1" []
    let raw := sourceDirective sourceFile optionals
    rewriteAt base language (fuel + 1) (decodeDirective raw) =
      [decodedDirective file implicitAll noSpace raw] := by
  simp only [decodeFileName, decodedFileName, a] at fileStep
  simp only [decodeDirective, sourceDirective, a]
  rw [rewriteAt_eq_root_filter, directiveRootRules]
  include_row_simp
  simp [fileStep, matchPattern, matchArgs, mergeBindings]

theorem directive_selection_rewriteAt_exact (fuel : Nat)
    (sourceFile sourceSelection file selection : Pattern)
    (fileStep : rewriteAt base language fuel (decodeFileName sourceFile) =
      [decodedFileName file])
    (selectionStep : rewriteAt base language fuel
      (decodeSelection sourceSelection) = [decodedSelection selection]) :
    let optionals := .apply "tptp92-ast:include-optionals:alt-2"
      [sourceSelection]
    let raw := sourceDirective sourceFile optionals
    rewriteAt base language (fuel + 1) (decodeDirective raw) =
      [decodedDirective file selection noSpace raw] := by
  simp only [decodeFileName, decodedFileName, decodeSelection,
    decodedSelection, a] at fileStep selectionStep
  simp only [decodeDirective, sourceDirective, a]
  rw [rewriteAt_eq_root_filter, directiveRootRules]
  include_row_simp
  simp [fileStep, selectionStep, matchPattern, matchArgs, mergeBindings]

theorem directive_space_rewriteAt_exact (fuel : Nat)
    (sourceFile sourceSelection sourceSpace file selection space : Pattern)
    (fileStep : rewriteAt base language fuel (decodeFileName sourceFile) =
      [decodedFileName file])
    (selectionStep : rewriteAt base language fuel
      (decodeSelection sourceSelection) = [decodedSelection selection])
    (spaceStep : rewriteAt base language fuel (decodeSpaceName sourceSpace) =
      [decodedSpaceName space]) :
    let optionals := .apply "tptp92-ast:include-optionals:alt-3"
      [sourceSelection, sourceSpace]
    let raw := sourceDirective sourceFile optionals
    rewriteAt base language (fuel + 1) (decodeDirective raw) =
      [decodedDirective file selection (someSpace space) raw] := by
  simp only [decodeFileName, decodedFileName, decodeSelection,
    decodedSelection, decodeSpaceName, decodedSpaceName, a]
    at fileStep selectionStep spaceStep
  simp only [decodeDirective, sourceDirective, a]
  rw [rewriteAt_eq_root_filter, directiveRootRules]
  include_row_simp
  simp [fileStep, selectionStep, spaceStep, matchPattern, matchArgs,
    mergeBindings]

theorem directive_implicit_eventuallyExact
    (sourceFile file : Pattern)
    (fileExact : EventuallyExact (decodeFileName sourceFile)
      (decodedFileName file)) :
    let optionals := .apply "tptp92-ast:include-optionals:alt-1" []
    let raw := sourceDirective sourceFile optionals
    EventuallyExact (decodeDirective raw)
      (decodedDirective file implicitAll noSpace raw) := by
  exact eventuallyExact_of_one_premise _ _ _ _ fileExact
    (fun fuel fileStep => directive_implicit_rewriteAt_exact fuel
      sourceFile file fileStep)

theorem directive_selection_eventuallyExact
    (sourceFile sourceSelection file selection : Pattern)
    (fileExact : EventuallyExact (decodeFileName sourceFile)
      (decodedFileName file))
    (selectionExact : EventuallyExact (decodeSelection sourceSelection)
      (decodedSelection selection)) :
    let optionals := .apply "tptp92-ast:include-optionals:alt-2"
      [sourceSelection]
    let raw := sourceDirective sourceFile optionals
    EventuallyExact (decodeDirective raw)
      (decodedDirective file selection noSpace raw) := by
  exact eventuallyExact_of_two_premises _ _ _ _ _ _ fileExact selectionExact
    (fun fuel fileStep selectionStep =>
      directive_selection_rewriteAt_exact fuel sourceFile sourceSelection
        file selection fileStep selectionStep)

theorem directive_space_eventuallyExact
    (sourceFile sourceSelection sourceSpace file selection space : Pattern)
    (fileExact : EventuallyExact (decodeFileName sourceFile)
      (decodedFileName file))
    (selectionExact : EventuallyExact (decodeSelection sourceSelection)
      (decodedSelection selection))
    (spaceExact : EventuallyExact (decodeSpaceName sourceSpace)
      (decodedSpaceName space)) :
    let optionals := .apply "tptp92-ast:include-optionals:alt-3"
      [sourceSelection, sourceSpace]
    let raw := sourceDirective sourceFile optionals
    EventuallyExact (decodeDirective raw)
      (decodedDirective file selection (someSpace space) raw) := by
  exact eventuallyExact_of_three_premises _ _ _ _ _ _ _ _
    fileExact selectionExact spaceExact
    (fun fuel fileStep selectionStep spaceStep =>
      directive_space_rewriteAt_exact fuel sourceFile sourceSelection
        sourceSpace file selection space fileStep selectionStep spaceStep)

/-- The independent official include projection and contextual execution of
the declared LanguageDef agree for every accepted directive.  The result is
encoded without dropping the raw ParserPack node. -/
theorem decodeIncludeDirective_eventuallyExact (source : Pattern)
    (view : IncludeDirectiveView)
    (decoded : decodeIncludeDirective? source = some view) :
    ∃ encoded,
      encodeDirectiveView? view = some encoded ∧
      EventuallyExact (decodeDirective source) encoded := by
  unfold decodeIncludeDirective? at decoded
  split at decoded
  · rename_i sourceShape sourceFile optionals
    rcases Option.bind_eq_some_iff.mp decoded with
      ⟨file, fileDecoded, remaining⟩
    split at remaining
    · cases remaining
      let raw := sourceDirective sourceFile
        (.apply "tptp92-ast:include-optionals:alt-1" [])
      let target := decodedDirective (encodeLexeme file) implicitAll noSpace
        raw
      refine ⟨target, ?_, ?_⟩
      · simp [target, raw, encodeDirectiveView?, encodeSelection?, encodeSpace,
          sourceDirective, a]
      · simpa [target, raw, sourceDirective, a] using
          directive_implicit_eventuallyExact sourceFile (encodeLexeme file)
            (decodeFileName_eventuallyExact sourceFile file fileDecoded)
    · rename_i optionalShape sourceSelection
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨selection, selectionDecoded, resultEquality⟩
      cases resultEquality
      rcases decodeFormulaSelection_eventuallyExact sourceSelection selection
          selectionDecoded with
        ⟨encodedSelection, selectionEncoded, selectionExact⟩
      let raw := sourceDirective sourceFile
        (.apply "tptp92-ast:include-optionals:alt-2" [sourceSelection])
      let target := decodedDirective (encodeLexeme file) encodedSelection
        noSpace raw
      refine ⟨target, ?_, ?_⟩
      · simp [target, raw, encodeDirectiveView?, selectionEncoded, encodeSpace,
          sourceDirective, a]
      · simpa [target, raw, sourceDirective, a] using
          directive_selection_eventuallyExact sourceFile sourceSelection
            (encodeLexeme file) encodedSelection
            (decodeFileName_eventuallyExact sourceFile file fileDecoded)
            selectionExact
    · rename_i optionalShape sourceSelection sourceSpace
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨selection, selectionDecoded, afterSelection⟩
      rcases Option.bind_eq_some_iff.mp afterSelection with
        ⟨space, spaceDecoded, resultEquality⟩
      cases resultEquality
      rcases decodeFormulaSelection_eventuallyExact sourceSelection selection
          selectionDecoded with
        ⟨encodedSelection, selectionEncoded, selectionExact⟩
      let raw := sourceDirective sourceFile
        (.apply "tptp92-ast:include-optionals:alt-3"
          [sourceSelection, sourceSpace])
      let target := decodedDirective (encodeLexeme file) encodedSelection
        (someSpace (encodeLexeme space)) raw
      refine ⟨target, ?_, ?_⟩
      · simp [target, raw, encodeDirectiveView?, selectionEncoded, encodeSpace,
          sourceDirective, a]
      · simpa [target, raw, sourceDirective, a] using
          directive_space_eventuallyExact sourceFile sourceSelection
            sourceSpace (encodeLexeme file) encodedSelection
            (encodeLexeme space)
            (decodeFileName_eventuallyExact sourceFile file fileDecoded)
            selectionExact
            (decodeSpaceName_eventuallyExact sourceSpace space spaceDecoded)
    · contradiction
  · contradiction

namespace Canary

def lowerName (value : String) : Pattern :=
  sourceNameWord "tptp92-ast:atomic-word:alt-1"
    "tptp92-ast:token:lower-word" (encodeLexeme value)

def orderedDuplicateNames : Pattern :=
  .apply "tptp92-ast:name-list:alt-2" [lowerName "second",
    .apply "tptp92-ast:name-list:alt-2" [lowerName "first",
      .apply "tptp92-ast:name-list:alt-1" [lowerName "second"]]]

theorem ordered_duplicates_decode_exactly :
    decodeNameList? orderedDuplicateNames =
      some ["second", "first", "second"] := by
  rfl

theorem ordered_duplicates_execute_exactly :
    EventuallyExact (decodeNameList orderedDuplicateNames)
      (decodedNameList
        (namesCons (encodeLexeme "second")
          (namesCons (encodeLexeme "first")
            (namesOne (encodeLexeme "second"))))) := by
  rcases decodeNameList_eventuallyExact orderedDuplicateNames
      ["second", "first", "second"] ordered_duplicates_decode_exactly with
    ⟨encoded, encodedEquality, exactExecution⟩
  simp [encodeNames?] at encodedEquality
  subst encoded
  exact exactExecution

/-- This pattern has a canonical official constructor spine but puts a free
variable where the ParserPack carrier requires a builtin string. -/
def illSortedName : Pattern :=
  sourceNameWord "tptp92-ast:atomic-word:alt-1"
    "tptp92-ast:token:lower-word" (.fvar "not-a-string")

theorem ill_sorted_name_projection_rejected :
    decodeCanonicalName? illSortedName = none := by
  rfl

theorem ill_sorted_name_carrier_rejected :
    CarrierWellSorted.checkHasType language WellSorted.FreeTypeContext.empty
      [] illSortedName
      (.base "Tptp92Ast:name") = false := by
  decide +kernel

/-- Raw `Pattern` rewriting deliberately does not enforce a rule's type
context.  The public typed runner must therefore check the carrier before
calling the generic relation. -/
theorem unrestricted_raw_rewrite_binds_ill_sorted_lexeme :
    rewriteAt base language 1 (decodeName illSortedName) =
      [decodedName (.fvar "not-a-string")] := by
  decide +kernel

end Canary

#print axioms decodeCanonicalName_eventuallyExact
#print axioms decodeNameList_eventuallyExact
#print axioms decodeIncludeDirective_eventuallyExact
#print axioms Canary.ordered_duplicates_decode_exactly
#print axioms Canary.ordered_duplicates_execute_exactly
#print axioms Canary.ill_sorted_name_projection_rejected
#print axioms Canary.ill_sorted_name_carrier_rejected
#print axioms Canary.unrestricted_raw_rewrite_binds_ill_sorted_lexeme

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveAgreement
