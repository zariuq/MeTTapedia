import Mettapedia.GSLT.Parsing.PlainBnfWakeSourceFamily

/-!
# Authored Wake contextual execution

Wake uses the actual readiness, trie-lookup, and scheduling source families.
The mathematical observation is the existing ordered Wake fold. Its known
index/history is consistent; the scheduled trie may contain arbitrary ground
payloads, since any found payload suppresses scheduling in the authored rules.
Inputs use the existing String/Nat source-spanned carrier. Physical execution
and the discovery controller's initialization/progress laws are separate.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfWakeContextualExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfSourceRank (Rank)
open PlainBnfReverseIndexSourceExecution (Item key node nodes)
open PlainBnfWakeSourceExecution (Queues heapItem enqueue wake encodeQueues)
open PlainBnfStructuredDenotation (Expression LexicalDeclaration)
open PlainBnfKnownNamesSourceExecution (known Valid)
open PlainBnfReferenceCollectionSourceExecution (expression declarations span)
open PlainBnfTrieSourceExecution (call result result_injective trie)
open PlainBnfLexicalMatcherSourceExecution (relations answer)
open PlainBnfWakeSourceFamily (observedRules rules_exact)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev NameIndex := PlainBnfReadinessSourceExecution.NameIndex

/-- The two authored mode tags, without a new runtime mode carrier. -/
def modeTag (productive : Bool) : SExpr :=
  .atom (if productive then "BNFDiscoveryProductiveV1" else "BNFDiscoveryNullableV1")

def meaning (productive : Bool) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (input : Expression) : Bool :=
  if productive then PlainBnfProductiveSourceExecution.expressionMeaning history lexicals input
  else PlainBnfNullableSourceExecution.expressionMeaning history input

def readyHeight (productive : Bool) (input : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Nat :=
  (if productive then PlainBnfProductiveSourceExecution.expressionHeight index history lexicals input
   else PlainBnfNullableSourceExecution.expressionHeight input index history lexicals) + 1

def readyCall (productive : Bool) (input : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Pattern :=
  PlainBnfReadinessSourceExecution.readyCall (modeTag productive) input index history lexicals

def wakeCall (productive : Bool) (input : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues) : Pattern :=
  call "BNFDiscoveryWakeV1" [modeTag productive, nodes input,
    PlainBnfScheduleSourceExecution.position origin, known index history,
    declarations lexicals, encodeQueues queues]

def afterScheduledCall (found : Option SExpr) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) : Pattern :=
  call "BNFDiscoveryAfterScheduledV1" [PlainBnfTrieSourceExecution.value found,
    modeTag productive, node item, nodes rest, PlainBnfScheduleSourceExecution.position origin,
    known index history, declarations lexicals, encodeQueues queues]

def afterReadyCall (available : Bool) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) : Pattern :=
  call "BNFDiscoveryAfterReadyV1" [answer available,
    modeTag productive, node item, nodes rest, PlainBnfScheduleSourceExecution.position origin,
    known index history, declarations lexicals, encodeQueues queues]

def scheduleCall (item : Item) (origin : Option Rank) (queues : Queues) : Pattern :=
  PlainBnfScheduleSourceExecution.scheduleCall origin (heapItem item) queues.1 queues.2.1 queues.2.2

def scheduleHeight (item : Item) (origin : Option Rank) (queues : Queues) : Nat :=
  PlainBnfScheduleSourceExecution.scheduleHeight item.1 (key item.2.name)
    (expression item.2.expression) (span item.2.span) queues.1 queues.2.1 queues.2.2 origin

/-- Contextual depth, not time or work. Marked candidates do not contribute
a readiness depth; short-circuited calls are omitted exactly as in the source. -/
def wakeHeight (productive : Bool) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : List Item → Queues → Nat
  | [], _ => 0
  | item :: rest, queues =>
      max (PlainBnfTrieSourceExecution.lookupHeight (key item.2.name) queues.2.2)
        (match PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2 with
         | some _ => wakeHeight productive origin index history lexicals rest queues + 1
         | none => max (readyHeight productive item.2.expression index history lexicals)
             (if meaning productive history lexicals item.2.expression then
                max (scheduleHeight item origin queues)
                  (wakeHeight productive origin index history lexicals rest (enqueue origin item queues)) + 1
              else wakeHeight productive origin index history lexicals rest queues + 1) + 1) + 1

def afterReadyHeight (available : Bool) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) : Nat :=
  if available then max (scheduleHeight item origin queues)
      (wakeHeight productive origin index history lexicals rest (enqueue origin item queues)) + 1
  else wakeHeight productive origin index history lexicals rest queues + 1

def afterScheduledHeight (found : Option SExpr) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) : Nat :=
  match found with
  | some _ => wakeHeight productive origin index history lexicals rest queues + 1
  | none => max (readyHeight productive item.2.expression index history lexicals)
      (afterReadyHeight (meaning productive history lexicals item.2.expression)
        productive item rest origin index history lexicals queues) + 1

def afterReady (available : Bool) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) : Queues :=
  wake (meaning productive history lexicals) origin rest
    (if available then enqueue origin item queues else queues)

def afterScheduled (found : Option SExpr) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) : Queues :=
  match found with
  | some _ => wake (meaning productive history lexicals) origin rest queues
  | none => afterReady (meaning productive history lexicals item.2.expression)
      productive item rest origin history lexicals queues

theorem wakeHeight_cons (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) :
    wakeHeight productive origin index history lexicals (item :: rest) queues =
      max (PlainBnfTrieSourceExecution.lookupHeight (key item.2.name) queues.2.2)
        (afterScheduledHeight (PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2)
          productive item rest origin index history lexicals queues) + 1 := by
  rw [wakeHeight]
  cases PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2 <;> rfl

theorem wake_cons_observation (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) :
    wake (meaning productive history lexicals) origin (item :: rest) queues =
      afterScheduled (PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2)
        productive item rest origin history lexicals queues := by
  rw [PlainBnfWakeSourceExecution.wake_cons]
  cases lookup : PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2 <;>
    simp [afterScheduled, afterReady, PlainBnfWakeSourceExecution.wakeStep, lookup]


theorem ready_component_answers (productive : Bool) (fuel : Nat) (input : Expression)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) PlainBnfReadinessSourceExecution.language fuel
        (readyCall productive input index history lexicals) =
      if readyHeight productive input index history lexicals < fuel then
        [result (answer (meaning productive history lexicals input))] else [] := by
  cases productive with
  | false =>
      simpa [readyCall, readyHeight, meaning, modeTag,
        PlainBnfReadinessSourceExecution.nullableCall] using
        PlainBnfReadinessSourceExecution.nullable_answers fuel input index history lexicals valid
  | true =>
      simpa [readyCall, readyHeight, meaning, modeTag,
        PlainBnfReadinessSourceExecution.productiveCall] using
        PlainBnfReadinessSourceExecution.productive_answers fuel input index history lexicals valid

theorem queues_injective : Function.Injective encodeQueues := by
  rintro ⟨leftCurrent, leftFollowing, leftScheduled⟩ ⟨rightCurrent, rightFollowing, rightScheduled⟩ same
  have parts := (PlainBnfScheduleSourceExecution.queues_eq_iff _ _ _ _ _ _).mp same
  rcases parts with ⟨rfl, rfl, rfl⟩
  rfl

theorem result_queues_injective : Function.Injective (fun queues => result (encodeQueues queues)) :=
  result_injective.comp queues_injective

section ClauseEvaluation

variable (language : LanguageDef)

private theorem nil_rows (fuel : Nat) (productive : Bool) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (wakeCall productive [] origin index history lexicals queues)) =
      [result (encodeQueues queues)] := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, wakeCall, nodes, call, result, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem found_rows (fuel : Nat) (payload : SExpr) (productive : Bool)
    (item : Item) (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (wakeCall productive rest origin index history lexicals queues) = answers.map result) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (afterScheduledCall (some payload) productive item rest origin index history lexicals queues)) =
      answers.map result := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, afterScheduledCall, PlainBnfTrieSourceExecution.value, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [wakeCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem unready_rows (fuel : Nat) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (wakeCall productive rest origin index history lexicals queues) = answers.map result) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (afterReadyCall false productive item rest origin index history lexicals queues)) =
      answers.map result := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, afterReadyCall, answer, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [wakeCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private def consRule : RewriteRule := PlainBnfWakeSourceExecution.rules[1]'(by rw [rules_exact]; decide)
private def missingRule : RewriteRule := PlainBnfWakeSourceExecution.rules[3]'(by rw [rules_exact]; decide)
private theorem consRule_exact : consRule = observedRules[1]'(by decide) := rfl
private theorem missingRule_exact : missingRule = observedRules[3]'(by decide) := rfl

private def consBindings (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) : Bindings :=
  [("?mode", encode (modeTag productive)), ("?origin", encode (PlainBnfScheduleSourceExecution.position origin)),
   ("?lexicals", encode (declarations lexicals)),
   ("?current", encode (PlainBnfHeapSourceExecution.heap queues.1)),
   ("?scheduled", encode (trie queues.2.2)),
   ("?following", encode (PlainBnfHeapSourceExecution.heap queues.2.1)),
   ("?known", encode (known index history)),
   ("?name", encode (PlainBnfReferenceCollectionSourceExecution.text item.2.name)),
   ("?span", encode (span item.2.span)), ("?expression", encode (expression item.2.expression)),
   ("?rank", encode (PlainBnfRankSourceExecution.rank item.1)), ("?rest", encode (nodes rest))]

private def missingBindings (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) : Bindings :=
  [("?name", encode (PlainBnfReferenceCollectionSourceExecution.text item.2.name)),
   ("?span", encode (span item.2.span)), ("?expression", encode (expression item.2.expression)),
   ("?rank", encode (PlainBnfRankSourceExecution.rank item.1)),
   ("?origin", encode (PlainBnfScheduleSourceExecution.position origin)),
   ("?lexicals", encode (declarations lexicals)), ("?before", encode (encodeQueues queues)),
   ("?known", encode (known index history)), ("?rest", encode (nodes rest)),
   ("?mode", encode (modeTag productive))]

theorem node_match (item : Item) :
    matchPattern (pattern (metta_sexpr% petta "(BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span)"))
      (encode (node item)) = [[
        ("?rank", encode (PlainBnfRankSourceExecution.rank item.1)),
        ("?expression", encode (expression item.2.expression)), ("?span", encode (span item.2.span)),
        ("?name", encode (PlainBnfReferenceCollectionSourceExecution.text item.2.name))]] := by
  simp [node, PlainBnfHeapSourceExecution.rankedDefinition, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem queues_match (queues : Queues) :
    matchPattern (pattern (metta_sexpr% petta "(BNFDiscoveryQueuesV1 ?current ?following ?scheduled)"))
      (encode (encodeQueues queues)) = [[
        ("?current", encode (PlainBnfHeapSourceExecution.heap queues.1)),
        ("?scheduled", encode (trie queues.2.2)),
        ("?following", encode (PlainBnfHeapSourceExecution.heap queues.2.1))]] := by
  simp [encodeQueues, PlainBnfScheduleSourceExecution.queues, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem cons_match (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) :
    matchPattern consRule.left (wakeCall productive (item :: rest) origin index history lexicals queues) =
      [consBindings productive item rest origin index history lexicals queues] := by
  simp [consRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    consBindings, wakeCall, nodes,
    PlainBnfReverseReferencesSourceExecution.bucketCons,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

  have nm := node_match item
  have qm := queues_match queues
  simp [pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode] at nm qm
  rw [nm, qm]
  simp [List.foldlM]

private theorem missing_match (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) :
    matchPattern missingRule.left
      (afterScheduledCall none productive item rest origin index history lexicals queues) =
      [missingBindings productive item rest origin index history lexicals queues] := by
  simp [missingRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    missingBindings, afterScheduledCall,
    PlainBnfTrieSourceExecution.value, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

  have nm := node_match item
  simp [pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode] at nm
  rw [nm]
  simp [List.foldlM]

private theorem cons_only (fuel : Nat) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (wakeCall productive (item :: rest) origin index history lexicals queues)) =
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) consRule
        (wakeCall productive (item :: rest) origin index history lexicals queues) := by
  rw [rules_exact, consRule_exact]
  simp only [observedRules, List.flatMap_cons, List.flatMap_nil]
  simp [PlainBnfTrieSourceExecution.observedRule, applyRuleUsing,
    wakeCall, nodes, PlainBnfReverseReferencesSourceExecution.bucketCons,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem missing_only (fuel : Nat) (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (afterScheduledCall none productive item rest origin index history lexicals queues)) =
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) missingRule
        (afterScheduledCall none productive item rest origin index history lexicals queues) := by
  rw [rules_exact, missingRule_exact]
  simp only [observedRules, List.flatMap_cons, List.flatMap_nil]
  simp [PlainBnfTrieSourceExecution.observedRule, applyRuleUsing, afterScheduledCall,
    PlainBnfTrieSourceExecution.value, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem cons_lookup_none_rows (fuel : Nat) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (first : rewriteAt (engineBasePremises relations) language fuel
      (PlainBnfTrieSourceExecution.lookupCall (key item.2.name) queues.2.2) = []) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (wakeCall productive (item :: rest) origin index history lexicals queues)) = [] := by

  rw [cons_only, applyRuleUsing, matchPatternForRule_eq_syntactic, cons_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [consRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    consBindings, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode,
    mergeBindings, premisesUsing, premiseStepUsing, applyBindings, PlainBnfReverseIndexSourceExecution.text_wire]
  simp only [PlainBnfTrieSourceExecution.lookupCall, call, encode, encodeList] at first
  rw [first]
  simp

private theorem cons_lookup_rows (fuel : Nat) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (found : Option SExpr) (answers : List SExpr)
    (first : rewriteAt (engineBasePremises relations) language fuel
      (PlainBnfTrieSourceExecution.lookupCall (key item.2.name) queues.2.2) =
        [result (PlainBnfTrieSourceExecution.value found)])
    (following : rewriteAt (engineBasePremises relations) language fuel
      (afterScheduledCall found productive item rest origin index history lexicals queues) = answers.map result) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (wakeCall productive (item :: rest) origin index history lexicals queues)) = answers.map result := by

  rw [cons_only, applyRuleUsing, matchPatternForRule_eq_syntactic, cons_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [consRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    consBindings, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode,
    mergeBindings, premisesUsing, premiseStepUsing, applyBindings, PlainBnfReverseIndexSourceExecution.text_wire]
  simp only [PlainBnfTrieSourceExecution.lookupCall, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [afterScheduledCall, node, PlainBnfHeapSourceExecution.rankedDefinition, encodeQueues,
    PlainBnfScheduleSourceExecution.queues, PlainBnfReverseIndexSourceExecution.text_wire,
    call, encode, encodeList] at following
  rw [following]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem missing_ready_none_rows (fuel : Nat) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (first : rewriteAt (engineBasePremises relations) language fuel
      (readyCall productive item.2.expression index history lexicals) = []) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (afterScheduledCall none productive item rest origin index history lexicals queues)) = [] := by

  rw [missing_only, applyRuleUsing, matchPatternForRule_eq_syntactic, missing_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [missingRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    missingBindings, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode,
    mergeBindings, premisesUsing, premiseStepUsing, applyBindings]
  simp only [readyCall, PlainBnfReadinessSourceExecution.readyCall, call, encode, encodeList] at first
  rw [first]
  simp

private theorem missing_ready_rows (fuel : Nat) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (available : Bool) (answers : List SExpr)
    (first : rewriteAt (engineBasePremises relations) language fuel
      (readyCall productive item.2.expression index history lexicals) = [result (answer available)])
    (following : rewriteAt (engineBasePremises relations) language fuel
      (afterReadyCall available productive item rest origin index history lexicals queues) = answers.map result) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (afterScheduledCall none productive item rest origin index history lexicals queues)) = answers.map result := by

  rw [missing_only, applyRuleUsing, matchPatternForRule_eq_syntactic, missing_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [missingRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    missingBindings, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode,
    mergeBindings, premisesUsing, premiseStepUsing, applyBindings]
  simp only [readyCall, PlainBnfReadinessSourceExecution.readyCall, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [afterReadyCall, node, PlainBnfHeapSourceExecution.rankedDefinition, call, encode, encodeList] at following
  rw [following]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem ready_schedule_none_rows (fuel : Nat) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (first : rewriteAt (engineBasePremises relations) language fuel (scheduleCall item origin queues) = []) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (afterReadyCall true productive item rest origin index history lexicals queues)) = [] := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, afterReadyCall, answer, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [scheduleCall, PlainBnfScheduleSourceExecution.scheduleCall,
    PlainBnfWakeSourceExecution.node_wire] at first
  change rewriteAt (engineBasePremises relations) language fuel
    (call "BNFDiscoveryScheduleV1" [node item, PlainBnfScheduleSourceExecution.position origin,
      encodeQueues queues]) = [] at first
  simp only [call, encode, encodeList] at first
  rw [first]
  simp

private theorem ready_schedule_rows (fuel : Nat) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues next : Queues)
    (answers : List SExpr)
    (first : rewriteAt (engineBasePremises relations) language fuel
      (scheduleCall item origin queues) = [result (encodeQueues next)])
    (following : rewriteAt (engineBasePremises relations) language fuel
      (wakeCall productive rest origin index history lexicals next) = answers.map result) :
    PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule
        (afterReadyCall true productive item rest origin index history lexicals queues)) = answers.map result := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, afterReadyCall, answer, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [scheduleCall, PlainBnfScheduleSourceExecution.scheduleCall,
    PlainBnfWakeSourceExecution.node_wire] at first
  change rewriteAt (engineBasePremises relations) language fuel
    (call "BNFDiscoveryScheduleV1" [node item, PlainBnfScheduleSourceExecution.position origin,
      encodeQueues queues]) = [result (encodeQueues next)] at first
  simp only [call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [wakeCall, call, encode, encodeList] at following
  rw [following]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

end ClauseEvaluation

open PlainBnfWakeSourceFamily (language)
open PlainBnfIndexedCollectorSourceExecution (headedBy)

private theorem wake_head (productive : Bool) (input : List Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues) :
    headedBy PlainBnfWakeSourceFamily.wakeHeads
      (wakeCall productive input origin index history lexicals queues) = true := by
  simp [headedBy, PlainBnfWakeSourceFamily.wakeHeads, wakeCall, call, encode, encodeList]

private theorem afterScheduled_head (found : Option SExpr) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) :
    headedBy PlainBnfWakeSourceFamily.wakeHeads
      (afterScheduledCall found productive item rest origin index history lexicals queues) = true := by
  simp [headedBy, PlainBnfWakeSourceFamily.wakeHeads, afterScheduledCall, call, encode, encodeList]

private theorem afterReady_head (available : Bool) (productive : Bool) (item : Item)
    (rest : List Item) (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) :
    headedBy PlainBnfWakeSourceFamily.wakeHeads
      (afterReadyCall available productive item rest origin index history lexicals queues) = true := by
  simp [headedBy, PlainBnfWakeSourceFamily.wakeHeads, afterReadyCall, call, encode, encodeList]

private theorem ready_answers (productive : Bool) (fuel : Nat) (input : Expression)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (readyCall productive input index history lexicals) =
      if readyHeight productive input index history lexicals < fuel then
        [result (answer (meaning productive history lexicals input))] else [] := by
  rw [PlainBnfWakeSourceFamily.ready_extension fuel _ (by
    simp [headedBy, readyCall, PlainBnfReadinessSourceExecution.readyCall,
      PlainBnfReadinessSourceExecution.relationHeads, PlainBnfReadinessSourceExecution.readyHeads,
      call, encode, encodeList])]
  exact ready_component_answers productive fuel input index history lexicals valid

private theorem lookup_answers (fuel : Nat) (name : List Nat) (index : NameIndex) :
    rewriteAt (engineBasePremises relations) language fuel (PlainBnfTrieSourceExecution.lookupCall name index) =
      if PlainBnfTrieSourceExecution.lookupHeight name index < fuel then
        [result (PlainBnfTrieSourceExecution.value (PlainBnfGraphNameTrie.lookup name index))] else [] := by
  rw [PlainBnfWakeSourceFamily.trie_extension fuel _ (by
    simp [headedBy, PlainBnfIndexedCollectorSourceExecution.trieNames,
      PlainBnfTrieSourceExecution.lookupCall, call, encode, encodeList])]
  exact (PlainBnfTrieSourceExecution.lookup_answers fuel).1 name index

private theorem schedule_answers (fuel : Nat) (item : Item) (origin : Option Rank) (queues : Queues) :
    rewriteAt (engineBasePremises relations) language fuel (scheduleCall item origin queues) =
      if scheduleHeight item origin queues < fuel then
        [result (encodeQueues (enqueue origin item queues))] else [] := by
  rw [PlainBnfWakeSourceFamily.schedule_extension fuel _ (by
    simp [headedBy, scheduleCall, PlainBnfScheduleSourceExecution.scheduleCall,
      PlainBnfScheduleSourceExecution.relationHeads, PlainBnfScheduleSourceExecution.scheduleNames,
      PlainBnfRankSourceExecution.call, encode, encodeList])]
  exact PlainBnfScheduleSourceExecution.schedule_answers fuel origin item.1 (key item.2.name)
    (expression item.2.expression) (span item.2.span) queues.1 queues.2.1 queues.2.2

/-- All ordered answers at every contextual depth, for all three actual Wake
entry heads. Neither the finite bound nor the independent fold is an execution
provider. A bound too small produces no derived answer, not a refutation. -/
theorem all_answers (productive : Bool) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) (fuel : Nat) :
    (∀ (input : List Item) (queues : Queues),
      rewriteAt (engineBasePremises relations) language fuel
        (wakeCall productive input origin index history lexicals queues) =
        if wakeHeight productive origin index history lexicals input queues < fuel then
          [result (encodeQueues (wake (meaning productive history lexicals) origin input queues))] else []) ∧
    (∀ (found : Option SExpr) (item : Item) (rest : List Item) (queues : Queues),
      rewriteAt (engineBasePremises relations) language fuel
        (afterScheduledCall found productive item rest origin index history lexicals queues) =
        if afterScheduledHeight found productive item rest origin index history lexicals queues < fuel then
          [result (encodeQueues (afterScheduled found productive item rest origin history lexicals queues))] else []) ∧
    (∀ (available : Bool) (item : Item) (rest : List Item) (queues : Queues),
      rewriteAt (engineBasePremises relations) language fuel
        (afterReadyCall available productive item rest origin index history lexicals queues) =
        if afterReadyHeight available productive item rest origin index history lexicals queues < fuel then
          [result (encodeQueues (afterReady available productive item rest origin history lexicals queues))] else []) := by
  induction fuel with
  | zero => constructor <;> (try constructor) <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro input queues
        rw [PlainBnfWakeSourceFamily.wake_rewriteAt fuel _ (wake_head _ _ _ _ _ _ _)]
        cases input with
        | nil => simpa [wakeHeight, PlainBnfWakeSourceExecution.wake_nil] using
            nil_rows language fuel productive origin index history lexicals queues
        | cons item rest =>
            rw [wakeHeight_cons, wake_cons_observation]
            by_cases enough : PlainBnfTrieSourceExecution.lookupHeight (key item.2.name) queues.2.2 < fuel
            · have first := lookup_answers fuel (key item.2.name) queues.2.2
              rw [if_pos enough] at first
              have next := ih.2.1 (PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2) item rest queues
              have run := cons_lookup_rows language fuel productive item rest origin index history lexicals queues
                (PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2)
                (if afterScheduledHeight (PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2)
                    productive item rest origin index history lexicals queues < fuel then
                  [encodeQueues (afterScheduled (PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2)
                    productive item rest origin history lexicals queues)] else []) first
                (by split <;> simp_all only [List.map_cons, List.map_nil, ↓reduceIte])
              rw [run]
              simp only [Nat.add_lt_add_iff_right, max_lt_iff, enough, true_and]
              split <;> rfl
            · have first := lookup_answers fuel (key item.2.name) queues.2.2
              rw [if_neg enough] at first
              rw [cons_lookup_none_rows language fuel productive item rest origin index history lexicals queues first,
                if_neg (by omega)]
      · intro found item rest queues
        rw [PlainBnfWakeSourceFamily.wake_rewriteAt fuel _ (afterScheduled_head _ _ _ _ _ _ _ _ _)]
        cases found with
        | some payload =>
            have run := found_rows language fuel payload productive item rest origin index history lexicals queues
              (if wakeHeight productive origin index history lexicals rest queues < fuel then
                [encodeQueues (wake (meaning productive history lexicals) origin rest queues)] else [])
              (by split <;> simp_all only [List.map_cons, List.map_nil, ↓reduceIte])
            rw [run]
            simp only [afterScheduledHeight, afterScheduled]
            simp only [Nat.add_lt_add_iff_right]
            split <;> rfl
        | none =>
            by_cases enough : readyHeight productive item.2.expression index history lexicals < fuel
            · have first := ready_answers productive fuel item.2.expression index history lexicals valid
              rw [if_pos enough] at first
              have next := ih.2.2 (meaning productive history lexicals item.2.expression) item rest queues
              have run := missing_ready_rows language fuel productive item rest origin index history lexicals queues
                (meaning productive history lexicals item.2.expression)
                (if afterReadyHeight (meaning productive history lexicals item.2.expression)
                    productive item rest origin index history lexicals queues < fuel then
                  [encodeQueues (afterReady (meaning productive history lexicals item.2.expression)
                    productive item rest origin history lexicals queues)] else []) first
                (by split <;> simp_all only [List.map_cons, List.map_nil, ↓reduceIte])
              rw [run]
              simp only [afterScheduledHeight, afterScheduled]
              simp only [Nat.add_lt_add_iff_right, max_lt_iff, enough, true_and]
              split <;> rfl
            · have first := ready_answers productive fuel item.2.expression index history lexicals valid
              rw [if_neg enough] at first
              rw [missing_ready_none_rows language fuel productive item rest origin index history lexicals queues first,
                if_neg (by simp only [afterScheduledHeight]; omega)]
      · intro available item rest queues
        rw [PlainBnfWakeSourceFamily.wake_rewriteAt fuel _ (afterReady_head _ _ _ _ _ _ _ _ _)]
        cases available with
        | false =>
            have run := unready_rows language fuel productive item rest origin index history lexicals queues
              (if wakeHeight productive origin index history lexicals rest queues < fuel then
                [encodeQueues (wake (meaning productive history lexicals) origin rest queues)] else [])
              (by split <;> simp_all only [List.map_cons, List.map_nil, ↓reduceIte])
            rw [run]
            simp only [afterReadyHeight, afterReady, Bool.false_eq_true, ↓reduceIte]
            simp only [Nat.add_lt_add_iff_right]
            split <;> rfl
        | true =>
            by_cases enough : scheduleHeight item origin queues < fuel
            · have first := schedule_answers fuel item origin queues
              rw [if_pos enough] at first
              have next := ih.1 rest (enqueue origin item queues)
              have run := ready_schedule_rows language fuel productive item rest origin index history lexicals queues
                (enqueue origin item queues)
                (if wakeHeight productive origin index history lexicals rest (enqueue origin item queues) < fuel then
                  [encodeQueues (wake (meaning productive history lexicals) origin rest (enqueue origin item queues))] else [])
                first (by split <;> simp_all only [List.map_cons, List.map_nil, ↓reduceIte])
              rw [run]
              simp only [afterReadyHeight, afterReady, ↓reduceIte]
              simp only [Nat.add_lt_add_iff_right, max_lt_iff, enough, true_and]
              split <;> rfl
            · have first := schedule_answers fuel item origin queues
              rw [if_neg enough] at first
              rw [ready_schedule_none_rows language fuel productive item rest origin index history lexicals queues first,
                if_neg (by simp only [afterReadyHeight, ↓reduceIte]; omega)]

theorem wake_answers (productive : Bool) (fuel : Nat) (input : List Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel
      (wakeCall productive input origin index history lexicals queues) =
      if wakeHeight productive origin index history lexicals input queues < fuel then
        [result (encodeQueues (wake (meaning productive history lexicals) origin input queues))] else [] :=
  (all_answers productive origin index history lexicals valid fuel).1 input queues

theorem afterScheduled_answers (productive : Bool) (fuel : Nat) (found : Option SExpr)
    (item : Item) (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel
      (afterScheduledCall found productive item rest origin index history lexicals queues) =
      if afterScheduledHeight found productive item rest origin index history lexicals queues < fuel then
        [result (encodeQueues (afterScheduled found productive item rest origin history lexicals queues))] else [] :=
  (all_answers productive origin index history lexicals valid fuel).2.1 found item rest queues

theorem afterReady_answers (productive : Bool) (fuel : Nat) (available : Bool)
    (item : Item) (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel
      (afterReadyCall available productive item rest origin index history lexicals queues) =
      if afterReadyHeight available productive item rest origin index history lexicals queues < fuel then
        [result (encodeQueues (afterReady available productive item rest origin history lexicals queues))] else [] :=
  (all_answers productive origin index history lexicals valid fuel).2.2 available item rest queues

/-- Arbitrary-target no-invention as well as existence: every successful source
execution returns exactly the complete ordered-fold queue encoding. -/
theorem wake_step_iff (productive : Bool) (input : List Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) (valid : Valid index history) (output : Pattern) :
    Step (engineBasePremises relations) language
      (wakeCall productive input origin index history lexicals queues) output ↔
      output = result (encodeQueues (wake (meaning productive history lexicals) origin input queues)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [wake_answers productive fuel input origin index history lexicals queues valid] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨wakeHeight productive origin index history lexicals input queues + 1,
      by simp [wake_answers productive _ input origin index history lexicals queues valid]⟩

theorem wake_queues_step_iff (productive : Bool) (input : List Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) (valid : Valid index history) (after : Queues) :
    Step (engineBasePremises relations) language
      (wakeCall productive input origin index history lexicals queues) (result (encodeQueues after)) ↔
      after = wake (meaning productive history lexicals) origin input queues := by
  rw [wake_step_iff productive input origin index history lexicals queues valid,
    result_queues_injective.eq_iff]

theorem afterScheduled_step_iff (productive : Bool) (found : Option SExpr)
    (item : Item) (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (valid : Valid index history) (output : Pattern) :
    Step (engineBasePremises relations) language
      (afterScheduledCall found productive item rest origin index history lexicals queues) output ↔
      output = result (encodeQueues (afterScheduled found productive item rest origin history lexicals queues)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [afterScheduled_answers productive fuel found item rest origin index history lexicals queues valid] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨afterScheduledHeight found productive item rest origin index history lexicals queues + 1,
      by simp [afterScheduled_answers productive _ found item rest origin index history lexicals queues valid]⟩

theorem afterReady_step_iff (productive : Bool) (available : Bool)
    (item : Item) (rest : List Item) (origin : Option Rank) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (queues : Queues)
    (valid : Valid index history) (output : Pattern) :
    Step (engineBasePremises relations) language
      (afterReadyCall available productive item rest origin index history lexicals queues) output ↔
      output = result (encodeQueues (afterReady available productive item rest origin history lexicals queues)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [afterReady_answers productive fuel available item rest origin index history lexicals queues valid] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨afterReadyHeight available productive item rest origin index history lexicals queues + 1,
      by simp [afterReady_answers productive _ available item rest origin index history lexicals queues valid]⟩

/-- The stored payload is opaque: a found non-name payload also suppresses
this occurrence. The source never tests payload equality with the node name. -/
theorem found_payload_skips_execution (productive : Bool) (item : Item) (rest : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) (valid : Valid index history)
    (payload : SExpr) (found : PlainBnfGraphNameTrie.lookup (key item.2.name) queues.2.2 = some payload)
    (output : Pattern) :
    Step (engineBasePremises relations) language
      (wakeCall productive (item :: rest) origin index history lexicals queues) output ↔
    Step (engineBasePremises relations) language
      (wakeCall productive rest origin index history lexicals queues) output := by
  rw [wake_step_iff productive (item :: rest) origin index history lexicals queues valid,
    wake_step_iff productive rest origin index history lexicals queues valid,
    PlainBnfWakeSourceExecution.found_payload_skips _ _ _ _ _ _ found]

/-- Repeated reference occurrences remain input occurrences but cannot create
a second queue entry after the first ready occurrence marks the name. -/
theorem repeated_name_step_iff (productive : Bool) (first second : Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) (valid : Valid index history)
    (sameName : first.2.name = second.2.name)
    (missing : PlainBnfGraphNameTrie.lookup (key first.2.name) queues.2.2 = none)
    (available : meaning productive history lexicals first.2.expression = true) (output : Pattern) :
    Step (engineBasePremises relations) language
      (wakeCall productive [first, second] origin index history lexicals queues) output ↔
      output = result (encodeQueues (enqueue origin first queues)) := by
  rw [wake_step_iff productive [first, second] origin index history lexicals queues valid,
    (PlainBnfWakeSourceExecution.repeated_name_suppressed _ origin first second queues
      sameName missing available).2]

theorem changed_queue_is_not_an_answer (productive : Bool) (input : List Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) (valid : Valid index history) (after : Queues)
    (different : after ≠ wake (meaning productive history lexicals) origin input queues) :
    ¬ Step (engineBasePremises relations) language
      (wakeCall productive input origin index history lexicals queues) (result (encodeQueues after)) := by
  rw [wake_queues_step_iff productive input origin index history lexicals queues valid]
  exact different

#print axioms all_answers
#print axioms wake_step_iff
#print axioms wake_queues_step_iff
#print axioms afterScheduled_step_iff
#print axioms afterReady_step_iff
#print axioms found_payload_skips_execution
#print axioms repeated_name_step_iff
#print axioms changed_queue_is_not_an_answer

end Mettapedia.GSLT.Parsing.PlainBnfWakeContextualExecution
