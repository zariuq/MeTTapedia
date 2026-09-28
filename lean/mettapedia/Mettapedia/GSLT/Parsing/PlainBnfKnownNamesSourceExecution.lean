import Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution

/-!
# Authored discovery known-name history

The original lookup, append, observation and reversal rules operate on the
existing sparse trie and ordinary name history. Lookup returns the stored
payload; interpreting it as membership requires an explicit index invariant.
The source-contextual result is not a generated or native-runtime theorem.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfKnownNamesSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfGraphNameTrie (Trie lookup insertFirst)
open PlainBnfCollectorSourceExecution (NameScalarCodec name name_injective)
open PlainBnfTrieSourceExecution
  (scalarRelations trie value call result observedRule trie_injective result_injective
    lookupCall lookupHeight insertCall insertHeight)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match trieNames trie_closed)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (relation : String) : Option (Nat × Nat) :=
  match relation with
  | "BNFNameLookupV1" | "BNFAppendNameV1" | "BNFDiscoveryReverseNamesV1" => some (2, 1)
  | "BNFIndexedNamesObserveV1" | "BNFIndexedNameLookupResultV1" => some (1, 1)
  | _ => PlainBnfCollectorSourceExecution.mode? relation

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? : SExpr → Option Premise
  | .list [.atom "different", left, right] =>
      some (.relationQuery "different" [pattern left, pattern right])
  | source => do
      let (input, output) ← splitCall? source
      some (.congruence (pattern input) (pattern output))

def lowerRule? (source : Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← decodeList lowerPremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

def discoveryRows : List Rewrite := PlainBnfCollectorSourceAdmission.discoverySource.rewrites.take 5
def helperRows : List Rewrite := (PlainBnfCollectorSourceAdmission.indexSource.rewrites.drop 15).take 2
def knownRows : List Rewrite := discoveryRows ++ helperRows
def rows : List Rewrite := PlainBnfCollectorSourceAdmission.indexSource.rewrites.take 14 ++ knownRows
def rules? : Option (List RewriteRule) := rows.mapM lowerRule?
theorem rules_present : rules?.isSome = true := rfl
def knownRules : List RewriteRule := (knownRows.mapM lowerRule?).get (by rfl)
def language : LanguageDef :=
  { name := "PlainBnfAuthoredKnownNames", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl
theorem discovery_occurrences_exact : discoveryRows.zipIdx =
    (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).take 5 := rfl
theorem helper_occurrences_exact : helperRows.zipIdx 15 =
    ((PlainBnfCollectorSourceAdmission.indexSource.rewrites.zipIdx).drop 15).take 2 := rfl
theorem language_partition : language.rewrites =
    PlainBnfTrieSourceExecution.language.rewrites ++ knownRules := rfl
theorem exactly_twenty_one_rules : language.rewrites.length = 21 := rfl

/-- Displayed observations checked against the actual translated source rows. -/
private def observedRules : List RewriteRule := [
  observedRule "bnf-discovery-known-lookup-v1"
    (metta_sexpr% petta "(BNFNameLookupV1 ?name (BNFDiscoveryKnownV1 ?index ?reversed))")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?name ?index)"))
        (pattern (metta_sexpr% petta "(?lookup)")),
     .congruence (pattern (metta_sexpr% petta "(BNFIndexedNameLookupResultV1 ?lookup)"))
        (pattern (metta_sexpr% petta "(?result)"))],
  observedRule "bnf-discovery-known-append-v1"
    (metta_sexpr% petta "(BNFAppendNameV1 (BNFDiscoveryKnownV1 ?index ?reversed) ?name)")
    (metta_sexpr% petta "((BNFDiscoveryKnownV1 ?next (BNFNamesConsV1 ?name ?reversed)))")
    [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?name ?name ?index)"))
        (pattern (metta_sexpr% petta "(?next)"))],
  observedRule "bnf-discovery-known-observe-v1"
    (metta_sexpr% petta "(BNFIndexedNamesObserveV1 (BNFDiscoveryKnownV1 ?index ?reversed))")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryReverseNamesV1 ?reversed BNFNamesNilV1)"))
        (pattern (metta_sexpr% petta "(?result)"))],
  observedRule "bnf-discovery-reverse-names-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryReverseNamesV1 BNFNamesNilV1 ?result)")
    (metta_sexpr% petta "(?result)"),
  observedRule "bnf-discovery-reverse-names-cons-v1"
    (metta_sexpr% petta "(BNFDiscoveryReverseNamesV1 (BNFNamesConsV1 ?head ?tail) ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryReverseNamesV1 ?tail (BNFNamesConsV1 ?head ?before))"))
        (pattern (metta_sexpr% petta "(?after)"))],
  observedRule "bnf-indexed-name-lookup-missing-v1"
    (metta_sexpr% petta "(BNFIndexedNameLookupResultV1 BNFIndexMissingV1)")
    (metta_sexpr% petta "(BNFNameMissingV1)"),
  observedRule "bnf-indexed-name-lookup-found-v1"
    (metta_sexpr% petta "(BNFIndexedNameLookupResultV1 (BNFIndexFoundV1 ?name))")
    (metta_sexpr% petta "((BNFNameFoundV1 ?name))")]

private theorem known_rules_exact : knownRules = observedRules := rfl

def knownNames := ["BNFNameLookupV1", "BNFAppendNameV1", "BNFIndexedNamesObserveV1",
  "BNFDiscoveryReverseNamesV1", "BNFIndexedNameLookupResultV1"]

private theorem trie_heads : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => headedBy trieNames rule.left) = true := by
  simp [PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    observedRule, headedBy, trieNames, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem known_heads : knownRules.all (fun rule => headedBy knownNames rule.left) = true := by
  simp [known_rules_exact, observedRules, observedRule, headedBy, knownNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

private theorem names_disjoint : List.Disjoint knownNames trieNames := by
  simp [knownNames, trieNames]

def relationHeads := trieNames ++ knownNames

theorem family_heads : language.rewrites.all
    (fun rule => headedBy relationHeads rule.left) = true := by
  simp [language_partition, PlainBnfTrieSourceExecution.source_rules_exact,
    PlainBnfTrieSourceExecution.observedRules, known_rules_exact, observedRules,
    observedRule, headedBy, relationHeads, trieNames, knownNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [language_partition, PlainBnfTrieSourceExecution.source_rules_exact,
    PlainBnfTrieSourceExecution.observedRules, known_rules_exact, observedRules,
    observedRule, premiseClosed, headedBy, relationHeads, trieNames, knownNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem trie_conservative_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy trieNames source = true) :
    rewriteAt (engineBasePremises scalarRelations) language fuel source =
      rewriteAt (engineBasePremises scalarRelations) PlainBnfTrieSourceExecution.language fuel source := by
  apply closed_extension trieNames scalarRelations _ _ [] knownRules
  · exact language_partition
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp trie_closed rule member) premise present
  · intro rule member term termHead
    exact disjoint_heads_do_not_match knownNames trieNames names_disjoint _ _
      (List.all_eq_true.mp known_heads rule member) termHead
  · exact headed

private theorem known_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy knownNames source = true) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) source =
      knownRules.flatMap (fun rule => applyRuleUsing (engineBasePremises scalarRelations) language
        (rewriteAt (engineBasePremises scalarRelations) language fuel) rule source) := by
  rw [rewriteAt, language_partition, List.flatMap_append]
  have none : PlainBnfTrieSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises scalarRelations) language
        (rewriteAt (engineBasePremises scalarRelations) language fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    have absent := disjoint_heads_do_not_match trieNames knownNames names_disjoint.symm _ _
      (List.all_eq_true.mp trie_heads rule member) headed
    simp [applyRuleUsing, absent]
  rw [none, List.nil_append]

def namesCons (head tail : SExpr) : SExpr := .list [.atom "BNFNamesConsV1", head, tail]
def namesNil : SExpr := .atom "BNFNamesNilV1"
def names (history : List SExpr) : SExpr := history.foldr namesCons namesNil
def reverseOnto (history : List SExpr) (before : SExpr) : SExpr := history.foldl (fun acc head => namesCons head acc) before
def reverseCall (history : List SExpr) (before : SExpr) : Pattern :=
  call "BNFDiscoveryReverseNamesV1" [names history, before]
def nameResult : Option SExpr → SExpr
  | none => .atom "BNFNameMissingV1"
  | some payload => .list [.atom "BNFNameFoundV1", payload]
def resultCall (found : Option SExpr) : Pattern := call "BNFIndexedNameLookupResultV1" [value found]

theorem result_answers (fuel : Nat) (found : Option SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (resultCall found) =
      if 0 < fuel then [result (nameResult found)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [known_rewriteAt fuel _ (by
      simp [resultCall, call, encode, encodeList, headedBy, knownNames])]
    cases found <;>
      simp [known_rules_exact, observedRules, observedRule, applyRuleUsing, resultCall, call,
        applyRuleBindings_of_binderFree, binderFree, binderFreeList,
        value, nameResult, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
        encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
        premisesUsing, premiseStepUsing, applyBindings]

theorem reverse_answers (fuel : Nat) (history : List SExpr) (before : SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (reverseCall history before) =
      if history.length < fuel then [result (reverseOnto history before)] else [] := by
  induction fuel generalizing history before with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    rw [known_rewriteAt fuel _ (by
      simp [reverseCall, call, encode, encodeList, headedBy, knownNames])]
    cases history with
    | nil =>
      simp [known_rules_exact, observedRules, observedRule, applyRuleUsing, reverseCall, call,
        applyRuleBindings_of_binderFree, binderFree, binderFreeList,
        names, namesNil, reverseOnto, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
        encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
        premisesUsing, premiseStepUsing, applyBindings]
    | cons head tail =>
      have recursive := ih tail (namesCons head before)
      simp [known_rules_exact, observedRules, observedRule, applyRuleUsing, reverseCall, call,
        applyRuleBindings_of_binderFree, binderFree, binderFreeList,
        names, namesCons, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
        encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
        premisesUsing, premiseStepUsing, applyBindings]
      simp only [reverseCall, call, names, namesCons, encode, encodeList] at recursive
      rw [recursive]
      split <;> simp_all [reverseOnto, namesCons, result, encode, encodeList,
        matchPattern, matchArgs, mergeBindings, List.foldlM]

variable {Scalar : Type} [NameScalarCodec Scalar] [DecidableEq Scalar]

def known (index : Trie SExpr Scalar) (history : List SExpr) : SExpr :=
  .list [.atom "BNFDiscoveryKnownV1", trie index, names history]
def knownLookupCall (key : List Scalar) (index : Trie SExpr Scalar) (history : List SExpr) : Pattern :=
  call "BNFNameLookupV1" [name key, known index history]
def appendCall (key : List Scalar) (index : Trie SExpr Scalar) (history : List SExpr) : Pattern :=
  call "BNFAppendNameV1" [known index history, name key]
def observeCall (index : Trie SExpr Scalar) (history : List SExpr) : Pattern :=
  call "BNFIndexedNamesObserveV1" [known index history]

theorem trie_lookup_answers (fuel : Nat) (key : List Scalar) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key index) =
      if lookupHeight key index < fuel then [result (value (lookup key index))] else [] := by
  rw [trie_conservative_extension fuel _ (by
    simp [lookupCall, call, encode, encodeList, headedBy, trieNames])]
  exact (PlainBnfTrieSourceExecution.lookup_answers fuel).1 key index

theorem trie_insert_answers (fuel : Nat) (key : List Scalar) (payload : SExpr) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (insertCall key payload index) =
      if insertHeight key index < fuel then [result (trie (insertFirst key payload index))] else [] := by
  rw [trie_conservative_extension fuel _ (by
    simp [insertCall, call, encode, encodeList, headedBy, trieNames])]
  exact (PlainBnfTrieSourceExecution.insert_answers fuel).1 key payload index

theorem known_lookup_answers (fuel : Nat) (key : List Scalar) (index : Trie SExpr Scalar)
    (history : List SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (knownLookupCall key index history) =
      if lookupHeight key index + 1 < fuel then [result (nameResult (lookup key index))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [known_rewriteAt fuel _ (by
      simp [knownLookupCall, call, encode, encodeList, headedBy, knownNames])]
    have queried := trie_lookup_answers fuel key index
    have wrapped := result_answers fuel (lookup key index)
    simp [known_rules_exact, observedRules, observedRule, applyRuleUsing, knownLookupCall, known,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, premiseStepUsing, applyBindings]
    simp only [lookupCall, call, encode, encodeList] at queried
    rw [queried]
    split
    · rename_i enough
      simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
      simp only [resultCall, call, encode, encodeList] at wrapped
      rw [wrapped]
      have positive : 0 < fuel := Nat.lt_of_le_of_lt (Nat.zero_le _) enough
      simp [positive, result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
    · simp

theorem append_answers (fuel : Nat) (key : List Scalar) (index : Trie SExpr Scalar)
    (history : List SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (appendCall key index history) =
      if insertHeight key index + 1 < fuel then
        [result (known (insertFirst key (name key) index) (name key :: history))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [known_rewriteAt fuel _ (by
      simp [appendCall, call, encode, encodeList, headedBy, knownNames])]
    have inserted := trie_insert_answers fuel key (name key) index
    simp [known_rules_exact, observedRules, observedRule, applyRuleUsing, appendCall, known,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, premiseStepUsing, applyBindings]
    simp only [insertCall, call, encode, encodeList] at inserted
    rw [inserted]
    split <;> simp [result, names, namesCons, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM]

omit [DecidableEq Scalar] in
theorem observe_answers (fuel : Nat) (index : Trie SExpr Scalar) (history : List SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (observeCall index history) =
      if history.length + 1 < fuel then [result (reverseOnto history namesNil)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [known_rewriteAt fuel _ (by
      simp [observeCall, call, encode, encodeList, headedBy, knownNames])]
    have reversed := reverse_answers fuel history namesNil
    simp [known_rules_exact, observedRules, observedRule, applyRuleUsing, observeCall, known,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, premiseStepUsing, applyBindings]
    simp only [reverseCall, call, namesNil, encode, encodeList] at reversed
    rw [reversed]
    split <;> simp [result, namesNil, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem reverse_step_iff (history : List SExpr) (before : SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (reverseCall history before) target ↔
      target = result (reverseOnto history before) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [reverse_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨history.length + 1, by simp [reverse_answers]⟩

theorem known_lookup_step_iff (key : List Scalar) (index : Trie SExpr Scalar)
    (history : List SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (knownLookupCall key index history) target ↔
      target = result (nameResult (lookup key index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [known_lookup_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨lookupHeight key index + 2, by simp [known_lookup_answers]⟩

theorem append_step_iff (key : List Scalar) (index : Trie SExpr Scalar)
    (history : List SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (appendCall key index history) target ↔
      target = result (known (insertFirst key (name key) index) (name key :: history)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [append_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨insertHeight key index + 2, by simp [append_answers]⟩

omit [DecidableEq Scalar] in
theorem observe_step_iff (index : Trie SExpr Scalar) (history : List SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (observeCall index history) target ↔
      target = result (reverseOnto history namesNil) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [observe_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨history.length + 2, by simp [observe_answers]⟩

theorem names_injective : Function.Injective names := by
  intro left right same
  induction left generalizing right with
  | nil => cases right <;> simp_all [names, namesCons, namesNil]
  | cons head tail ih =>
    cases right with
    | nil => simp [names, namesCons, namesNil] at same
    | cons other rest =>
      have parts : head = other ∧ names tail = names rest := by
        simpa only [names, List.foldr_cons, namesCons, SExpr.list.injEq,
          List.cons.injEq, true_and, and_true] using same
      exact congrArg₂ List.cons parts.1 (ih parts.2)

omit [DecidableEq Scalar] in
theorem known_eq_iff (index index' : Trie SExpr Scalar) (history history' : List SExpr) :
    known index history = known index' history' ↔ index = index' ∧ history = history' := by
  constructor
  · intro same
    have parts : trie index = trie index' ∧ names history = names history' := by
      simpa only [known, SExpr.list.injEq, List.cons.injEq, true_and, and_true] using same
    exact ⟨trie_injective parts.1, names_injective parts.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem nameResult_injective : Function.Injective nameResult := by
  intro left right same
  cases left <;> cases right <;> simp_all [nameResult]

theorem lookup_decoded_step_iff (key : List Scalar) (index : Trie SExpr Scalar)
    (history : List SExpr) (output : Option SExpr) :
    Step (engineBasePremises scalarRelations) language (knownLookupCall key index history)
      (result (nameResult output)) ↔ output = lookup key index := by
  rw [known_lookup_step_iff, result_injective.eq_iff, nameResult_injective.eq_iff]

theorem append_decoded_step_iff (key : List Scalar) (index index' : Trie SExpr Scalar)
    (history history' : List SExpr) :
    Step (engineBasePremises scalarRelations) language (appendCall key index history)
      (result (known index' history')) ↔
        index' = insertFirst key (name key) index ∧ history' = name key :: history := by
  rw [append_step_iff, result_injective.eq_iff, known_eq_iff]

theorem reverse_onto_names (history before : List SExpr) :
    reverseOnto history (names before) = names (history.reverse ++ before) := by
  simp only [reverseOnto, names, List.foldr_append]
  rw [List.foldr_reverse]

theorem reverse_nil_observation (history : List SExpr) :
    reverseOnto history namesNil = names history.reverse := by
  simpa [names] using reverse_onto_names history []

theorem reverse_decoded_step_iff (history before output : List SExpr) :
    Step (engineBasePremises scalarRelations) language (reverseCall history (names before))
      (result (names output)) ↔ output = history.reverse ++ before := by
  rw [reverse_step_iff, reverse_onto_names, result_injective.eq_iff, names_injective.eq_iff]

omit [DecidableEq Scalar] in
theorem observe_decoded_step_iff (index : Trie SExpr Scalar) (history output : List SExpr) :
    Step (engineBasePremises scalarRelations) language (observeCall index history)
      (result (names output)) ↔ output = history.reverse := by
  rw [observe_step_iff, reverse_nil_observation, result_injective.eq_iff, names_injective.eq_iff]

omit [DecidableEq Scalar] in
theorem observed_append_order (key : List Scalar) (index : Trie SExpr Scalar) (history : List SExpr) :
    Step (engineBasePremises scalarRelations) language (observeCall index (name key :: history))
      (result (names (history.reverse ++ [name key]))) := by
  apply (observe_decoded_step_iff _ _ _).mpr
  simp

/-- Exact membership-and-payload consistency; a stale history or a wrong
stored payload does not satisfy this invariant. Duplicates are permitted. -/
def Valid (index : Trie SExpr Scalar) (history : List SExpr) : Prop :=
  ∀ key, lookup key index = if name key ∈ history then some (name key) else none

theorem valid_empty : Valid (.empty : Trie SExpr Scalar) [] := by
  intro key
  cases key <;> simp [lookup, PlainBnfGraphNameTrie.valueAt, PlainBnfGraphNameTrie.childFor,
    PlainBnfGraphNameTrie.edgesOf]

theorem valid_append (key : List Scalar) (index : Trie SExpr Scalar) (history : List SExpr)
    (valid : Valid index history) :
    Valid (insertFirst key (name key) index) (name key :: history) := by
  intro query
  rw [PlainBnfGraphNameTrie.lookup_insertFirst]
  by_cases same : query = key
  · subst query
    rw [if_pos rfl, valid key]
    by_cases present : name key ∈ history <;> simp [present]
  · have namesDifferent : name query ≠ name key := fun equal => same (name_injective equal)
    rw [if_neg same, valid query]
    simp [namesDifferent]

theorem source_append_preserves_valid (key : List Scalar) (index index' : Trie SExpr Scalar)
    (history history' : List SExpr) (valid : Valid index history)
    (returned : Step (engineBasePremises scalarRelations) language (appendCall key index history)
      (result (known index' history'))) : Valid index' history' := by
  obtain ⟨rfl, rfl⟩ := (append_decoded_step_iff _ _ _ _ _).mp returned
  exact valid_append key index history valid

theorem valid_lookup_step_iff (key : List Scalar) (index : Trie SExpr Scalar)
    (history : List SExpr) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (knownLookupCall key index history) target ↔
      target = result (nameResult (if name key ∈ history then some (name key) else none)) := by
  rw [known_lookup_step_iff, valid]

theorem valid_membership_iff (key : List Scalar) (index : Trie SExpr Scalar)
    (history : List SExpr) (valid : Valid index history) :
    Step (engineBasePremises scalarRelations) language (knownLookupCall key index history)
      (result (nameResult (some (name key)))) ↔ name key ∈ history := by
  rw [lookup_decoded_step_iff, valid]
  split <;> simp_all

/-- Fold the chronological append sequence using the actual first-binding
operation. This is an ordinary trie construction, not a second source state. -/
def historyIndex (history : List (List Scalar)) : Trie SExpr Scalar :=
  history.foldl (fun index key => insertFirst key (name key) index) .empty

theorem valid_fold (history : List (List Scalar)) (index : Trie SExpr Scalar)
    (reversed : List SExpr) (valid : Valid index reversed) :
    Valid (history.foldl (fun index key => insertFirst key (name key) index) index)
      ((history.map name).reverse ++ reversed) := by
  induction history generalizing index reversed with
  | nil => simpa using valid
  | cons key tail ih =>
    simpa [List.reverse_cons, List.append_assoc] using
      ih (insertFirst key (name key) index) (name key :: reversed) (valid_append key index reversed valid)

theorem historyIndex_valid (history : List (List Scalar)) :
    Valid (historyIndex history) (history.map name).reverse := by
  simpa [historyIndex] using valid_fold history .empty [] valid_empty

theorem historyIndex_lookup (history : List (List Scalar)) (key : List Scalar) :
    lookup key (historyIndex history) = if key ∈ history then some (name key) else none := by
  rw [historyIndex_valid history key]
  simp only [List.mem_reverse, List.mem_map]
  have member : (∃ item, item ∈ history ∧ name item = name key) ↔ key ∈ history := by
    constructor
    · rintro ⟨item, present, same⟩
      exact name_injective same ▸ present
    · intro present
      exact ⟨key, present, rfl⟩
  simp only [member]

theorem constructed_history_observation (history : List (List Scalar)) :
    Step (engineBasePremises scalarRelations) language
      (observeCall (historyIndex history) (history.map name).reverse)
      (result (names (history.map name))) := by
  apply (observe_decoded_step_iff _ _ _).mpr
  simp

theorem helper_step_iff (found : Option SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (resultCall found) target ↔
      target = result (nameResult found) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [result_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨1, by simp [result_answers]⟩

theorem source_append_observation (key : List Scalar) (index index' : Trie SExpr Scalar)
    (history history' : List SExpr)
    (returned : Step (engineBasePremises scalarRelations) language (appendCall key index history)
      (result (known index' history'))) :
    Step (engineBasePremises scalarRelations) language (observeCall index' history')
      (result (names (history.reverse ++ [name key]))) := by
  obtain ⟨rfl, rfl⟩ := (append_decoded_step_iff _ _ _ _ _).mp returned
  exact observed_append_order key _ history

theorem source_append_keeps_old_payload (key : List Scalar) (payload : SExpr)
    (index index' : Trie SExpr Scalar) (history history' : List SExpr)
    (old : lookup key index = some payload)
    (returned : Step (engineBasePremises scalarRelations) language (appendCall key index history)
      (result (known index' history'))) :
    Step (engineBasePremises scalarRelations) language (knownLookupCall key index' history')
      (result (nameResult (some payload))) := by
  obtain ⟨rfl, rfl⟩ := (append_decoded_step_iff _ _ _ _ _).mp returned
  apply (lookup_decoded_step_iff _ _ _ _).mpr
  rw [PlainBnfGraphNameTrie.lookup_inserted, old]
  rfl

/-- A stale history does not make the source consult that list for lookup. -/
theorem stale_history_lookup_is_missing (key : List Scalar) :
    Step (engineBasePremises scalarRelations) language
      (knownLookupCall key (.empty : Trie SExpr Scalar) [name key])
      (result (nameResult none)) := by
  apply (lookup_decoded_step_iff _ _ _ _).mpr
  simp

theorem stale_history_is_invalid (key : List Scalar) :
    ¬ Valid (.empty : Trie SExpr Scalar) [name key] := by
  intro valid
  have claimed := valid key
  simp at claimed

/-- Wrong stored data is returned as-is, not repaired into the query name. -/
theorem wrong_payload_returned (key : List Scalar) (payload : SExpr) :
    Step (engineBasePremises scalarRelations) language
      (knownLookupCall key (insertFirst key payload (.empty : Trie SExpr Scalar)) [name key])
      (result (nameResult (some payload))) := by
  apply (lookup_decoded_step_iff _ _ _ _).mpr
  rw [PlainBnfGraphNameTrie.lookup_inserted, valid_empty (Scalar := Scalar) key]
  simp

theorem wrong_payload_is_invalid (key : List Scalar) (payload : SExpr)
    (wrong : payload ≠ name key) :
    ¬ Valid (insertFirst key payload (.empty : Trie SExpr Scalar)) [name key] := by
  intro valid
  have claimed := valid key
  rw [PlainBnfGraphNameTrie.lookup_inserted, valid_empty (Scalar := Scalar) key] at claimed
  simp only [List.not_mem_nil, ↓reduceIte, List.mem_cons_self] at claimed
  exact wrong (Option.some.inj claimed)

theorem wrong_payload_cannot_answer_query_name (key : List Scalar) (payload : SExpr)
    (wrong : payload ≠ name key) :
    ¬ Step (engineBasePremises scalarRelations) language
      (knownLookupCall key (insertFirst key payload (.empty : Trie SExpr Scalar)) [name key])
      (result (nameResult (some (name key)))) := by
  rw [lookup_decoded_step_iff, PlainBnfGraphNameTrie.lookup_inserted,
    valid_empty (Scalar := Scalar) key]
  simpa [eq_comm] using wrong

omit [DecidableEq Scalar] in
theorem duplicate_history_occurrences (index : Trie SExpr Scalar) (entry : SExpr) :
    Step (engineBasePremises scalarRelations) language (observeCall index [entry, entry])
      (result (names [entry, entry])) ∧
    ¬ Step (engineBasePremises scalarRelations) language (observeCall index [entry, entry])
      (result (names [entry])) := by
  simp [observe_decoded_step_iff]

omit [DecidableEq Scalar] in
theorem reverse_order_is_observable (index : Trie SExpr Scalar) (first second : SExpr)
    (different : first ≠ second) :
    Step (engineBasePremises scalarRelations) language (observeCall index [second, first])
      (result (names [first, second])) ∧
    ¬ Step (engineBasePremises scalarRelations) language (observeCall index [second, first])
      (result (names [second, first])) := by
  simp [observe_decoded_step_iff, different, Ne.symm different]

theorem signed_history_lookup_control :
    let input : List (List Int) := [[-3, 0], [-3, 0]]
    let index := historyIndex input
    let history := (input.map name).reverse
    Step (engineBasePremises scalarRelations) language (knownLookupCall [-3, 0] index history)
      (result (nameResult (some (name ([-3, 0] : List Int))))) ∧
    Step (engineBasePremises scalarRelations) language (knownLookupCall [3, 0] index history)
      (result (nameResult none)) ∧
    Step (engineBasePremises scalarRelations) language (observeCall index history)
      (result (names [name ([-3, 0] : List Int), name ([-3, 0] : List Int)])) := by
  dsimp
  constructor
  · rw [lookup_decoded_step_iff, historyIndex_lookup]
    simp
  constructor
  · rw [lookup_decoded_step_iff, historyIndex_lookup]
    simp
  · exact constructed_history_observation [[-3, 0], [-3, 0]]

end Mettapedia.GSLT.Parsing.PlainBnfKnownNamesSourceExecution
