import Mettapedia.GSLT.Parsing.PlainBnfKnownNamesSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfLexicalMatcherSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfScheduleSourceExecution

/-!
# Primitive-environment transport for plain-BNF readiness

Adding the lexical arithmetic predicates does not change a source family that
queries only structural disequality. The proof preserves entire ordered
answer lists in the existing contextual evaluator; no new evaluator or
readiness-answer primitive is introduced. Family inventories below are
checked against the actual translated source rules.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfReadinessEnvironment

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open PlainBnfIndexedCollectorSourceExecution (headedBy premiseClosed trieNames)

/-- A relation-query inventory, not a provider of answers. -/
def queriesOnly (allowed : List String) : Premise → Bool
  | .relationQuery relation _ => allowed.contains relation
  | _ => true

theorem base_transport (allowed : List String) (left right : RelationEnv)
    (agree : ∀ relation ∈ allowed, ∀ arguments,
      left.tuples relation arguments = right.tuples relation arguments)
    (lang : LanguageDef) (bindings : Bindings) (premise : Premise)
    (licensed : queriesOnly allowed premise = true) :
    engineBasePremises left lang bindings premise = engineBasePremises right lang bindings premise := by
  cases premise with
  | congruence _ _ => rfl
  | freshness _ => rfl
  | forAll _ _ _ => rfl
  | relationQuery relation arguments =>
    have member : relation ∈ allowed := by simpa [queriesOnly] using licensed
    simp only [engineBasePremises, premiseStepWithEnv, relationQueryStep, agree relation member]

private theorem premises_transport (allowed : List String) (left right : RelationEnv)
    (agree : ∀ relation ∈ allowed, ∀ arguments,
      left.tuples relation arguments = right.tuples relation arguments)
    (lang : LanguageDef) (executeLeft executeRight : Pattern → List Pattern)
    (recursive : ∀ source, executeLeft source = executeRight source)
    (premises : List Premise) (licensed : ∀ premise ∈ premises, queriesOnly allowed premise = true)
    (bindings : Bindings) :
    premisesUsing (engineBasePremises left) lang executeLeft premises bindings =
      premisesUsing (engineBasePremises right) lang executeRight premises bindings := by
  induction premises generalizing bindings with
  | nil => rfl
  | cons premise rest ih =>
    have first : premiseStepUsing (engineBasePremises left) lang executeLeft bindings premise =
        premiseStepUsing (engineBasePremises right) lang executeRight bindings premise := by
      cases premise with
      | congruence source target => simp only [premiseStepUsing, recursive]
      | freshness condition =>
        exact base_transport allowed left right agree lang bindings (.freshness condition)
          (licensed _ (by simp))
      | relationQuery relation arguments =>
        exact base_transport allowed left right agree lang bindings (.relationQuery relation arguments)
          (licensed _ (by simp))
      | forAll collection parameter body =>
        exact base_transport allowed left right agree lang bindings (.forAll collection parameter body)
          (licensed _ (by simp))
    simp only [premisesUsing, first]
    apply List.flatMap_congr
    intro next _
    exact ih (fun premise member => licensed premise (List.mem_cons_of_mem _ member)) next

/-- Agreement on the predicates actually queried preserves every answer
occurrence, its position, and its bindings through all contextual depths. -/
theorem rewriteAt_transport (allowed : List String) (left right : RelationEnv)
    (agree : ∀ relation ∈ allowed, ∀ arguments,
      left.tuples relation arguments = right.tuples relation arguments)
    (lang : LanguageDef)
    (licensed : ∀ rule ∈ lang.rewrites, ∀ premise ∈ rule.premises,
      queriesOnly allowed premise = true)
    (fuel : Nat) (source : Pattern) :
    rewriteAt (engineBasePremises left) lang fuel source =
      rewriteAt (engineBasePremises right) lang fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    rw [rewriteAt, rewriteAt]
    apply List.flatMap_congr
    intro rule member
    simp only [applyRuleUsing]
    apply List.flatMap_congr
    intro bindings _
    rw [premises_transport allowed left right agree lang _ _ ih rule.premises (licensed rule member)]

private theorem flatMap_filter_of_empty {α β : Type} (keep : α → Bool) (run : α → List β)
    (items : List α) (excluded : ∀ item ∈ items, keep item = false → run item = []) :
    items.flatMap run = (items.filter keep).flatMap run := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have tail := ih (fun value member => excluded value (List.mem_cons_of_mem _ member))
    cases test : keep item with
    | false => simp [test, excluded item (by simp) test, tail]
    | true => simp [test, tail]

/-- Shared dependencies may be interleaved with other closed families. Selection
retains their original order and multiplicity; it is not set union or a new
runtime dispatch mechanism. -/
theorem filtered_extension (names : List String) (env : RelationEnv)
    (small large : LanguageDef)
    (selected : large.rewrites.filter (fun rule => headedBy names rule.left) = small.rewrites)
    (closed : ∀ rule ∈ small.rewrites, ∀ premise ∈ rule.premises,
      premiseClosed names premise = true)
    (excluded : ∀ rule ∈ large.rewrites, headedBy names rule.left = false →
      ∀ source, headedBy names source = true → matchPattern rule.left source = [])
    (fuel : Nat) (source : Pattern) (headed : headedBy names source = true) :
    rewriteAt (engineBasePremises env) large fuel source =
      rewriteAt (engineBasePremises env) small fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    rw [rewriteAt, rewriteAt]
    rw [flatMap_filter_of_empty (fun rule => headedBy names rule.left)
      (fun rule => applyRuleUsing (engineBasePremises env) large
        (rewriteAt (engineBasePremises env) large fuel) rule source) large.rewrites (by
          intro rule member foreign
          simp [applyRuleUsing, excluded rule member foreign source headed]), selected]
    apply List.flatMap_congr
    intro rule member
    exact PlainBnfIndexedCollectorSourceExecution.applyRule_congr names env large small
      _ _ ih rule (closed rule member) source

theorem foreign_head_does_not_match (names allNames : List String) (left right : Pattern)
    (formed : headedBy allNames left = true) (foreign : headedBy names left = false)
    (headed : headedBy names right = true) : matchPattern left right = [] := by
  unfold headedBy at formed
  split at formed
  · rename_i _ leftName leftArgs
    unfold headedBy at headed
    split at headed
    · rename_i _ rightName rightArgs
      have different : leftName ≠ rightName := by
        intro same
        subst rightName
        simp only [headedBy] at foreign
        rw [headed] at foreign
        contradiction
      simp [matchPattern, matchArgs, different]
    · contradiction
  · contradiction

theorem headedBy_mono (small large : List String) (included : small ⊆ large)
    (source : Pattern) (headed : headedBy small source = true) :
    headedBy large source = true := by
  unfold headedBy at headed
  split at headed
  · rename_i _ name arguments
    change large.contains name = true
    simpa using included (by simpa using headed)
  · contradiction

theorem headedBy_disjoint (names other : List String) (disjoint : List.Disjoint names other)
    (source : Pattern) (headed : headedBy other source = true) :
    headedBy names source = false := by
  unfold headedBy at headed
  split at headed
  · rename_i _ name arguments
    change names.contains name = false
    have absent : name ∉ names := fun present => disjoint present (by simpa using headed)
    simpa using absent
  · contradiction

theorem filter_included (names other : List String) (included : other ⊆ names)
    (rules : List RewriteRule) (formed : rules.all (fun rule => headedBy other rule.left) = true) :
    rules.filter (fun rule => headedBy names rule.left) = rules := by
  apply List.filter_eq_self.mpr
  intro rule member
  exact headedBy_mono other names included _ (List.all_eq_true.mp formed rule member)

theorem filter_disjoint (names other : List String) (disjoint : List.Disjoint names other)
    (rules : List RewriteRule) (formed : rules.all (fun rule => headedBy other rule.left) = true) :
    rules.filter (fun rule => headedBy names rule.left) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro rule member
  simpa using headedBy_disjoint names other disjoint _ (List.all_eq_true.mp formed rule member)

def knownHeads := trieNames ++ PlainBnfKnownNamesSourceExecution.knownNames
def lexicalLookupHeads := ["BNFLexicalReferenceLookupV1"]
def lexicalMatcherHeads :=
  ["BNFLexicalMatcherInhabitedV1", "BNFExclusionTailInhabitedV1", "BNFExclusionGapInhabitedV1"]

theorem known_heads : PlainBnfKnownNamesSourceExecution.language.rewrites.all
    (fun rule => headedBy knownHeads rule.left) = true :=
  PlainBnfKnownNamesSourceExecution.family_heads

theorem known_closed : PlainBnfKnownNamesSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed knownHeads)) = true :=
  PlainBnfKnownNamesSourceExecution.family_closed

theorem known_queries : PlainBnfKnownNamesSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (queriesOnly ["different"])) = true := rfl

theorem lexical_lookup_heads : PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites.all
    (fun rule => headedBy lexicalLookupHeads rule.left) = true :=
  PlainBnfReferenceCollectionSourceExecution.lookup_heads

theorem lexical_lookup_closed : PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites.all
    (fun rule => rule.premises.all (premiseClosed lexicalLookupHeads)) = true :=
  PlainBnfReferenceCollectionSourceExecution.lookup_closed

theorem lexical_lookup_queries : PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites.all
    (fun rule => rule.premises.all (queriesOnly ["different"])) = true := rfl

theorem lexical_matcher_heads : PlainBnfLexicalMatcherSourceExecution.language.rewrites.all
    (fun rule => headedBy lexicalMatcherHeads rule.left) = true :=
  PlainBnfLexicalMatcherSourceExecution.family_heads

theorem lexical_matcher_closed : PlainBnfLexicalMatcherSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed lexicalMatcherHeads)) = true :=
  PlainBnfLexicalMatcherSourceExecution.family_closed

theorem trie_queries : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (queriesOnly ["different"])) = true := rfl

theorem schedule_queries : PlainBnfScheduleSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (queriesOnly ["different"])) = true := rfl

theorem lexical_agrees_on_different (relation : String) (member : relation ∈ ["different"])
    (arguments : List Pattern) :
    PlainBnfLexicalMatcherSourceExecution.relations.tuples relation arguments =
      PlainBnfTrieSourceExecution.scalarRelations.tuples relation arguments := by
  simp only [List.mem_singleton] at member
  subst relation
  rfl

theorem different_only_environment (lang : LanguageDef)
    (licensed : lang.rewrites.all (fun rule => rule.premises.all (queriesOnly ["different"])) = true)
    (fuel : Nat) (source : Pattern) :
    rewriteAt (engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations) lang fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations) lang fuel source := by
  apply rewriteAt_transport ["different"] _ _ lexical_agrees_on_different lang ?_ fuel source
  intro rule member premise present
  exact List.all_eq_true.mp (List.all_eq_true.mp licensed rule member) premise present

theorem known_environment (fuel : Nat) (source : Pattern) :
    rewriteAt (engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations)
      PlainBnfKnownNamesSourceExecution.language fuel source =
    rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
      PlainBnfKnownNamesSourceExecution.language fuel source :=
  different_only_environment _ known_queries fuel source

theorem lexical_lookup_environment (fuel : Nat) (source : Pattern) :
    rewriteAt (engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations)
      PlainBnfReferenceCollectionSourceExecution.lookupLanguage fuel source =
    rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
      PlainBnfReferenceCollectionSourceExecution.lookupLanguage fuel source :=
  different_only_environment _ lexical_lookup_queries fuel source

theorem trie_environment (fuel : Nat) (source : Pattern) :
    rewriteAt (engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations)
      PlainBnfTrieSourceExecution.language fuel source =
    rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
      PlainBnfTrieSourceExecution.language fuel source :=
  different_only_environment _ trie_queries fuel source

theorem schedule_environment (fuel : Nat) (source : Pattern) :
    rewriteAt (engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations)
      PlainBnfScheduleSourceExecution.language fuel source =
    rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
      PlainBnfScheduleSourceExecution.language fuel source :=
  different_only_environment _ schedule_queries fuel source

#print axioms rewriteAt_transport
#print axioms filtered_extension
#print axioms known_environment
#print axioms lexical_lookup_environment
#print axioms schedule_environment

end Mettapedia.GSLT.Parsing.PlainBnfReadinessEnvironment
