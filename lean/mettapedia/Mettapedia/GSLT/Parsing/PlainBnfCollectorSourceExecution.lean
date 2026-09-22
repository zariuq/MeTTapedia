import Mettapedia.GSLT.Parsing.SourceSExprPatternMatching
import Mettapedia.GSLT.Parsing.PlainBnfTrieDeclarationCollector
import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Authored declaration-collector execution in the existing contextual relation

The selected clauses are read from the live authored discovery source. Their
heads and ordered bodies are translated by an explicit checked input/output
mode into the existing Pattern/RewriteRule carrier. This is a finite selected
source translation, not a new evaluator or a native compiler correctness claim.

Source quotation remains an executable reader boundary. The kernel checks the
quoted structured data and the theorems below, not the reader's byte semantics.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList applyBindings_encode)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

private def discoverySyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/plain_bnf_graph_discovery_v1.metta"

/-- Input and output arities of the selected declaration/trie call family. -/
def mode? : String → Option (Nat × Nat)
  | "BNFDiscoveryCollectDefinitionsV1" => some (1, 3)
  | "BNFDiscoveryCollectLoopV1" => some (3, 3)
  | "BNFDiscoveryCollectAfterLookupV1" => some (5, 3)
  | "BNFDiscoveryReverseDefinitionsV1" => some (2, 1)
  | "BNFGraphTrieLookupV1" => some (2, 1)
  | "BNFGraphTrieEdgeLookupV1" => some (3, 1)
  | "BNFGraphTrieInsertFirstV1" => some (3, 1)
  | "BNFGraphTrieEdgeInsertV1" => some (4, 1)
  | "BNFGraphTrieFirstValueV1" => some (2, 1)
  | _ => none

/-- Keep the relation name in the input call; return all outputs as one tuple.
Arity mismatch and unknown relations fail rather than silently truncating data. -/
def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs),
          .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? (source : SExpr) : Option Premise := do
  let (input, output) ← splitCall? source
  some (.congruence (pattern input) (pattern output))

/-- Every target component is computed from the actual source head/body. -/
def lowerRule? (source : Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decodeList lowerPremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

private def sourceRule? (index : Nat) : Option Rewrite :=
  Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt? discoverySyntax index

/-- Actual occurrence positions 47 and 48, not hand-written target rules. -/
def reversalRules? : Option (List RewriteRule) := do
  let nilRule ← sourceRule? 47 >>= lowerRule?
  let consRule ← sourceRule? 48 >>= lowerRule?
  some [nilRule, consRule]

def reversalLanguage : LanguageDef :=
  { name := "PlainBnfAuthoredDefinitionReversal", types := [], terms := [],
    equations := [], rewrites := reversalRules?.getD [] }

def definitions : List SExpr → SExpr
  | [] => .atom "BNFDefinitionsNilV1"
  | head :: tail => .list [.atom "BNFDefinitionsConsV1", head, definitions tail]

def reverseCall (reversed before : List SExpr) : SExpr :=
  .list [.atom "BNFDiscoveryReverseDefinitionsV1", definitions reversed, definitions before]

def resultTuple (result : List SExpr) : SExpr := .list [definitions result]

/-- The scalar spelling used by the existing source text constructors. This
parametrizes their codec, not the grammar, source language, or evaluator. -/
class NameScalarCodec (Scalar : Type) where
  decimal : Scalar → String
  injective : Function.Injective decimal

instance : NameScalarCodec Nat where
  decimal := Nat.repr
  injective := fun _ _ same => Nat.repr_injective same

theorem integer_decimal_injective : Function.Injective Int.repr := by
  intro left right same
  have decoded := congrArg SourceIntegerProvider.integerValue? same
  simpa only [← Int.toString_eq_repr, SourceIntegerProvider.integerValue?_repr,
    Option.some.injEq] using decoded

instance : NameScalarCodec Int where
  decimal := Int.repr
  injective := integer_decimal_injective

section ScalarCodec

variable {Scalar : Type} [NameScalarCodec Scalar]

@[simp] theorem scalar_decimal_eq_iff (left right : Scalar) :
    NameScalarCodec.decimal left = NameScalarCodec.decimal right ↔ left = right :=
  ⟨fun same => NameScalarCodec.injective same, congrArg NameScalarCodec.decimal⟩

/-- The existing name carrier, encoded in the actual source text constructors. -/
def name : List Scalar → SExpr
  | [] => .list [.atom "metta-nullary", .atom "bnf-v1:text-nil"]
  | scalar :: tail => .list [.atom "bnf-v1:text-cons", .atom (NameScalarCodec.decimal scalar), name tail]

def definition (value : PlainBnfDeclarationSemantics.Definition
    (List Scalar) SExpr SExpr) : SExpr :=
  .list [.atom "BNFDefinitionV1", name value.name, value.expression, value.span]

def diagnostic : PlainBnfDeclarationSemantics.Diagnostic (List Scalar) SExpr → SExpr
  | .duplicate key firstSpan laterSpan =>
      .list [.atom "BNFDuplicateDefinitionV1", name key, firstSpan, laterSpan]

def diagnostics : List (PlainBnfDeclarationSemantics.Diagnostic
    (List Scalar) SExpr) → SExpr
  | [] => .atom "BNFDiagnosticsNilV1"
  | head :: tail => .list [.atom "BNFDiagnosticsConsV1", diagnostic head, diagnostics tail]

def entry : PlainBnfDeclarationSemantics.Entry
    (List Scalar) SExpr SExpr SExpr → SExpr
  | .rule key expression span => .list [.atom "bnf-v1:rule", name key, expression, span]
  | .comment text span => .list [.atom "bnf-v1:comment", text, span]
  | .blank span => .list [.atom "bnf-v1:blank", span]

def entries : List (PlainBnfDeclarationSemantics.Entry
    (List Scalar) SExpr SExpr SExpr) → SExpr
  | [] => .list [.atom "metta-nullary", .atom "bnf-v1:entries-nil"]
  | head :: tail => .list [.atom "bnf-v1:entries-cons", entry head, entries tail]

theorem name_injective : Function.Injective (name (Scalar := Scalar)) := by
  intro left right same
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons scalar tail => simp [name] at same
  | cons scalar tail ih =>
    cases right with
    | nil => simp [name] at same
    | cons other rest =>
      simp only [name, SExpr.list.injEq, List.cons.injEq, SExpr.atom.injEq,
        and_true, true_and] at same
      exact congrArg₂ List.cons (NameScalarCodec.injective same.1) (ih same.2)

theorem definition_injective : Function.Injective (definition (Scalar := Scalar)) := by
  rintro ⟨key, expression, span⟩ ⟨key', expression', span'⟩ same
  simp only [definition, SExpr.list.injEq, List.cons.injEq, and_true, true_and] at same
  have keys := name_injective same.1
  cases keys
  cases same.2.1
  cases same.2.2
  rfl

theorem entry_injective : Function.Injective (entry (Scalar := Scalar)) := by
  intro left right same
  cases left <;> cases right <;>
    simp [entry] at same
  · have keys := name_injective same.1
    cases keys
    cases same.2.1
    cases same.2.2
    rfl
  · cases same.1
    cases same.2
    rfl
  · cases same
    rfl

theorem entries_injective : Function.Injective (entries (Scalar := Scalar)) := by
  intro left right same
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons head tail => simp [entries] at same
  | cons head tail ih =>
    cases right with
    | nil => simp [entries] at same
    | cons other rest =>
      simp only [entries, SExpr.list.injEq, List.cons.injEq,
        and_true, true_and] at same
      exact congrArg₂ List.cons (entry_injective same.1) (ih same.2)

theorem definitions_injective : Function.Injective definitions := by
  intro left right same
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons head tail => simp [definitions] at same
  | cons head tail ih =>
    cases right with
    | nil => simp [definitions] at same
    | cons other rest =>
      simp only [definitions, SExpr.list.injEq, List.cons.injEq,
        and_true, true_and] at same
      exact congrArg₂ List.cons same.1 (ih same.2)

theorem diagnostic_injective : Function.Injective (diagnostic (Scalar := Scalar)) := by
  intro left right same
  cases left with
  | duplicate key first last =>
    cases right with
    | duplicate key' first' last' =>
      simp only [diagnostic, SExpr.list.injEq, List.cons.injEq,
        and_true, true_and] at same
      have keys := name_injective same.1
      cases keys
      cases same.2.1
      cases same.2.2
      rfl

theorem diagnostics_injective : Function.Injective (diagnostics (Scalar := Scalar)) := by
  intro left right same
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons head tail => simp [diagnostics] at same
  | cons head tail ih =>
    cases right with
    | nil => simp [diagnostics] at same
    | cons other rest =>
      simp only [diagnostics, SExpr.list.injEq, List.cons.injEq,
        and_true, true_and] at same
      exact congrArg₂ List.cons (diagnostic_injective same.1) (ih same.2)

end ScalarCodec

/-- Nonnegative Integer names retain exactly the existing Nat wire. -/
theorem name_nat_integer_transport (input : List Nat) :
    name (input.map Int.ofNat) = name input := by
  induction input with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, name, ih]; rfl

/-- All mathematical Integers, including negative values, have canonical
source atoms under the existing Integer provider. -/
theorem integer_decimal_roundtrip (input : Int) :
    SourceIntegerProvider.integerValue? (NameScalarCodec.decimal input) = some input := by
  simpa only [NameScalarCodec.decimal, ← Int.toString_eq_repr] using
    SourceIntegerProvider.integerValue?_repr input

theorem signed_name_retains_negative_atom :
    name ([-3, 0, 7] : List Int) = .list [.atom "bnf-v1:text-cons", .atom "-3",
      .list [.atom "bnf-v1:text-cons", .atom "0",
        .list [.atom "bnf-v1:text-cons", .atom "7",
          .list [.atom "metta-nullary", .atom "bnf-v1:text-nil"]]]] := rfl

theorem opposite_signed_names_are_distinct :
    name ([-3, 0] : List Int) ≠ name ([3, 0] : List Int) := by
  intro same
  have decoded := name_injective same
  simp at decoded

private def nilLeft : SExpr :=
  .list [.atom "BNFDiscoveryReverseDefinitionsV1", .atom "BNFDefinitionsNilV1", .atom "?result"]

private def consLeft : SExpr :=
  .list [.atom "BNFDiscoveryReverseDefinitionsV1",
    .list [.atom "BNFDefinitionsConsV1", .atom "?head", .atom "?tail"], .atom "?before"]

private def recursiveCall : SExpr :=
  .list [.atom "BNFDiscoveryReverseDefinitionsV1", .atom "?tail",
    .list [.atom "BNFDefinitionsConsV1", .atom "?head", .atom "?before"]]

/-- Kernel computation checks the translation result, including the recursive
body and its output binding. These displayed shapes are observations only. -/
theorem reversalRules_exact : reversalRules? = some
    [{ name := "bnf-discovery-reverse-definitions-nil-v1", typeContext := [], premises := [],
       left := pattern nilLeft, right := pattern (.list [.atom "?result"]) },
     { name := "bnf-discovery-reverse-definitions-cons-v1", typeContext := [],
       premises := [.congruence (pattern recursiveCall) (pattern (.list [.atom "?after"]))],
       left := pattern consLeft, right := pattern (.list [.atom "?after"]) }] := by
  rfl

theorem wrong_arity_refused :
    splitCall? (.list [.atom "BNFDiscoveryReverseDefinitionsV1", .atom "?x", .atom "?y"]) = none := rfl

theorem unknown_relation_refused : splitCall? (.list [.atom "unlisted", .atom "?x"]) = none := rfl

private theorem match_nil (before : List SExpr) :
    matchPattern (pattern nilLeft) (encode (reverseCall [] before)) =
      [[("?result", encode (definitions before))]] := by
  simp [nilLeft, reverseCall, definitions, pattern, patternList, encode, encodeList,
    SourceIntegerProvider.sourceVariableToken, matchPattern, matchArgs, mergeBindings,
    List.foldlM]

private theorem match_nil_cons (head : SExpr) (tail before : List SExpr) :
    matchPattern (pattern nilLeft) (encode (reverseCall (head :: tail) before)) = [] := by
  simp [nilLeft, reverseCall, definitions, pattern, patternList, encode, encodeList,
    SourceIntegerProvider.sourceVariableToken, matchPattern, matchArgs]

private theorem match_cons_nil (before : List SExpr) :
    matchPattern (pattern consLeft) (encode (reverseCall [] before)) = [] := by
  simp [consLeft, reverseCall, definitions, pattern, patternList, encode, encodeList,
    SourceIntegerProvider.sourceVariableToken, matchPattern, matchArgs]

private theorem match_cons (head : SExpr) (tail before : List SExpr) :
    matchPattern (pattern consLeft) (encode (reverseCall (head :: tail) before)) =
      [[("?tail", encode (definitions tail)), ("?head", encode head),
        ("?before", encode (definitions before))]] := by
  simp [consLeft, reverseCall, definitions, pattern, patternList, encode, encodeList,
    SourceIntegerProvider.sourceVariableToken, matchPattern, matchArgs, mergeBindings,
    List.foldlM]

private theorem rewrite_nil (base : BasePremiseEvaluator) (fuel : Nat) (before : List SExpr) :
    rewriteAt base reversalLanguage (fuel + 1) (encode (reverseCall [] before)) =
      [encode (resultTuple before)] := by
  simp only [rewriteAt, reversalLanguage, reversalRules_exact, Option.getD_some,
    List.flatMap_cons, List.flatMap_nil, applyRuleUsing,
    matchPatternForRule_eq_syntactic, match_nil, match_cons_nil,
    List.flatMap_nil, premisesUsing,
    applyBindingsForRule_eq_syntactic, List.map_cons, List.map_nil, List.append_nil]
  simp [pattern, patternList, SourceIntegerProvider.sourceVariableToken, applyBindings,
    resultTuple, encode, encodeList]

private theorem recursive_substitution (head : SExpr) (tail before : List SExpr) :
    applyBindings [("?tail", encode (definitions tail)), ("?head", encode head),
      ("?before", encode (definitions before))] (pattern recursiveCall) =
        encode (reverseCall tail (head :: before)) := by
  simp [recursiveCall, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    applyBindings, reverseCall, definitions, encode, encodeList]

private theorem match_output (value : SExpr) :
    matchPattern (pattern (.list [.atom "?after"])) (encode (.list [value])) =
      [[("?after", encode value)]] := by
  simp [pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- The complete answer list of the existing executable contextual semantics:
insufficient depth returns no result; sufficient depth returns exactly one
ordered result. No provider can supply an answer for these clauses. -/
theorem reversal_rewriteAt (base : BasePremiseEvaluator) (fuel : Nat)
    (reversed before : List SExpr) :
    rewriteAt base reversalLanguage fuel (encode (reverseCall reversed before)) =
      if reversed.length < fuel then
        [encode (resultTuple (List.reverseAux reversed before))] else [] := by
  induction fuel generalizing reversed before with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    cases reversed with
    | nil => simpa using rewrite_nil base fuel before
    | cons head tail =>
      simp only [rewriteAt, reversalLanguage, reversalRules_exact, Option.getD_some,
        List.flatMap_cons, List.flatMap_nil, applyRuleUsing,
        matchPatternForRule_eq_syntactic, match_nil_cons, match_cons,
        List.flatMap_nil, List.nil_append,
        premisesUsing, premiseStepUsing, recursive_substitution,
        applyBindingsForRule_eq_syntactic, List.append_nil]
      change List.map
        (fun bindings => applyBindings bindings (pattern (.list [.atom "?after"])))
        (List.flatMap (fun bindings => [bindings])
          ((rewriteAt base reversalLanguage fuel
            (encode (reverseCall tail (head :: before)))).flatMap fun candidate =>
              (matchPattern (pattern (.list [.atom "?after"])) candidate).filterMap
                (fun premiseBindings => mergeBindings
                  [("?tail", encode (definitions tail)), ("?head", encode head),
                    ("?before", encode (definitions before))] premiseBindings))) = _
      rw [ih]
      split
      · simp only [resultTuple, List.flatMap_cons, List.flatMap_nil, match_output]
        simp [mergeBindings, List.foldlM,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          applyBindings, List.reverseAux, encode, encodeList, *]
      · simp_all [List.reverseAux]

/-- Two-sided execution for an arbitrary target, including outputs outside the
source-data image. No extra contextual answer is admitted. -/
theorem reversal_step_iff (base : BasePremiseEvaluator) (reversed before : List SExpr)
    (target : Pattern) :
    Step base reversalLanguage (encode (reverseCall reversed before)) target ↔
      target = encode (resultTuple (reversed.reverse ++ before)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [reversal_rewriteAt] at member
    split at member
    · simpa [List.reverseAux_eq] using member
    · cases member
  · intro same
    subst target
    refine ⟨reversed.length + 1, ?_⟩
    simp [reversal_rewriteAt, List.reverseAux_eq]

/-- Specialization to the existing independent declaration carrier, including
all expression/span payloads and an arbitrary nonempty output tail. -/
theorem declaration_reversal_step_iff (base : BasePremiseEvaluator)
    (reversed before : List (PlainBnfDeclarationSemantics.Definition
      PlainBnfGraphNameTrie.Name SExpr SExpr)) (target : Pattern) :
    Step base reversalLanguage
        (encode (reverseCall (reversed.map definition) (before.map definition))) target ↔
      target = encode (resultTuple ((List.reverseAux reversed before).map definition)) := by
  rw [reversal_step_iff]
  simp [List.reverseAux_eq]

theorem reversal_preserves_duplicate_occurrences (base : BasePremiseEvaluator)
    (value : SExpr) :
    rewriteAt base reversalLanguage 3 (encode (reverseCall [value, value] [])) =
      [encode (resultTuple [value, value])] := by
  simp [reversal_rewriteAt, List.reverseAux]

theorem reversal_does_not_collapse_duplicates (base : BasePremiseEvaluator)
    (value : SExpr) :
    ¬ Step base reversalLanguage (encode (reverseCall [value, value] []))
      (encode (resultTuple [value])) := by
  rw [reversal_step_iff]
  intro same
  have lists := SourceSExprPatternCodec.encode_injective same
  simp only [resultTuple, SExpr.list.injEq, List.cons.injEq, and_true] at lists
  have lengths := congrArg List.length (definitions_injective lists)
  simp at lengths

theorem reversal_does_not_retain_accumulator_order (base : BasePremiseEvaluator)
    (first second : SExpr) (different : first ≠ second) :
    ¬ Step base reversalLanguage (encode (reverseCall [first, second] []))
      (encode (resultTuple [first, second])) := by
  rw [reversal_step_iff]
  intro same
  have lists := SourceSExprPatternCodec.encode_injective same
  simp only [resultTuple, SExpr.list.injEq, List.cons.injEq, and_true] at lists
  have ordered := definitions_injective lists
  exact different (List.cons.inj ordered).1

theorem duplicate_diagnostics_are_not_one
    (value : PlainBnfDeclarationSemantics.Diagnostic PlainBnfGraphNameTrie.Name SExpr) :
    diagnostics [value, value] ≠ diagnostics [value] := by
  intro same
  have lengths := congrArg List.length (diagnostics_injective same)
  simp at lengths

/-- The actual collector-nil occurrence added to the actual reversal family. -/
def collectorBaseLanguage : LanguageDef :=
  { reversalLanguage with
    name := "PlainBnfAuthoredCollectorBase"
    rewrites := (sourceRule? 41 >>= lowerRule?).toList ++ reversalLanguage.rewrites }

private def collectorNilLeft : SExpr :=
  .list [.atom "BNFDiscoveryCollectLoopV1",
    .list [.atom "metta-nullary", .atom "bnf-v1:entries-nil"],
    .atom "?index", .atom "?reversed"]

private def collectorNilRight : SExpr :=
  .list [.atom "?definitions", .atom "BNFDiagnosticsNilV1", .atom "?index"]

private def collectorNilPremise : SExpr :=
  .list [.atom "BNFDiscoveryReverseDefinitionsV1", .atom "?reversed",
    .atom "BNFDefinitionsNilV1"]

theorem collector_nil_rule_exact : (sourceRule? 41 >>= lowerRule?) = some
    { name := "bnf-discovery-collect-nil-v1", typeContext := [],
      premises := [.congruence (pattern collectorNilPremise)
        (pattern (.list [.atom "?definitions"]))],
      left := pattern collectorNilLeft, right := pattern collectorNilRight } := by
  rfl

def collectorNilCall (index : SExpr) (reversed : List SExpr) : SExpr :=
  .list [.atom "BNFDiscoveryCollectLoopV1",
    .list [.atom "metta-nullary", .atom "bnf-v1:entries-nil"], index, definitions reversed]

def collectorNilResult (index : SExpr) (ordered : List SExpr) : SExpr :=
  .list [definitions ordered, .atom "BNFDiagnosticsNilV1", index]

private theorem match_collector_nil (index : SExpr) (reversed : List SExpr) :
    matchPattern (pattern collectorNilLeft) (encode (collectorNilCall index reversed)) =
      [[("?reversed", encode (definitions reversed)), ("?index", encode index)]] := by
  simp [collectorNilLeft, collectorNilCall, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- The authored nil collector calls the proved authored reversal. This is an
actual contextual execution, not merely equality with the finite host function.
Only this base case is connected here, not the whole collector/trie family. -/
theorem collector_nil_step (index : SExpr) (reversed : List SExpr) :
    Step (engineBasePremises RelationEnv.empty) collectorBaseLanguage
      (encode (collectorNilCall index reversed))
      (encode (collectorNilResult index reversed.reverse)) := by
  have reverseStep := (reversal_step_iff (engineBasePremises RelationEnv.empty)
    reversed [] (encode (resultTuple reversed.reverse))).mpr (by simp)
  have lifted := reverseStep.mono_rules (lang₂ := collectorBaseLanguage)
    (fun rule member => by
      exact List.mem_append_right _ member)
  apply step_of_single_congruence_rule
    (rule := {
      name := "bnf-discovery-collect-nil-v1"
      typeContext := []
      premises := [.congruence (pattern collectorNilPremise)
        (pattern (.list [.atom "?definitions"]))],
      left := pattern collectorNilLeft, right := pattern collectorNilRight })
    (initialBindings := [("?reversed", encode (definitions reversed)), ("?index", encode index)])
    (premiseBindings := [("?definitions", encode (definitions reversed.reverse))])
    (finalBindings := [("?definitions", encode (definitions reversed.reverse)),
      ("?reversed", encode (definitions reversed)), ("?index", encode index)])
    (candidate := encode (resultTuple reversed.reverse))
  · simp [collectorBaseLanguage, collector_nil_rule_exact]
  · simp [matchPatternForRule_eq_syntactic, match_collector_nil]
  · rfl
  · convert lifted using 1
    simp [collectorNilPremise, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      applyBindings, reverseCall, definitions, encode, encodeList]
  · simp [resultTuple, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  · simp [mergeBindings, List.foldlM]
  · simp [applyBindingsForRule_eq_syntactic, collectorNilRight, collectorNilResult,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      applyBindings, encode, encodeList]

/-- The independent collector's reverseAux observation is now reached by the
actual nil/reversal clauses. The index is unchanged opaque source data here;
its trie interpretation belongs to the remaining full-collector connection. -/
theorem collector_nil_restores_declaration_order (index : SExpr)
    (reversed : List (PlainBnfDeclarationSemantics.Definition
      PlainBnfGraphNameTrie.Name SExpr SExpr)) :
    Step (engineBasePremises RelationEnv.empty) collectorBaseLanguage
      (encode (collectorNilCall index (reversed.map definition)))
      (encode (collectorNilResult index
        ((List.reverseAux reversed []).map definition))) := by
  simpa [List.reverseAux_eq] using collector_nil_step index (reversed.map definition)

#print axioms reversal_rewriteAt
#print axioms reversal_step_iff
#print axioms declaration_reversal_step_iff
#print axioms collector_nil_step
#print axioms diagnostics_injective

end Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceExecution
