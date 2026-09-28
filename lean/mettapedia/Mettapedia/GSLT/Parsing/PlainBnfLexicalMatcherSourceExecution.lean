import Mettapedia.GSLT.Parsing.PlainBnfReferenceCollectionSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfLexicalInhabitation

/-!
# Authored lexical-matcher inhabitation in contextual execution

The actual eleven source rules execute using the existing Pattern relation.
Integer premises run the already defined actual-source provider observation;
ground structural disequality only echoes an unequal input pair. Neither
primitive computes a matcher answer.

The exact execution theorems concern canonical natural-number scalar lists,
including unvalidated ones. Equivalence with nonemptiness separately requires
valid, strictly increasing Unicode scalars. This is not malformed-input
admission, a physical integer implementation, or generated PeTTa adequacy.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfLexicalMatcherSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfReferenceSourceAdmission (graphSource)
open PlainBnfReferenceCollectionSourceExecution (scalars matcher)
open PlainBnfStructuredDenotation (LexicalMatcher)
open PlainBnfTrieSourceExecution (call result scalarRelations)
open PlainBnfScalarOrderSource (providerAnswers? integerEnv matchingProviders)
open PlainBnfLexicalInhabitation (gapAfter exceptGapCheck)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

private def providerRow (index : Fin 4) : Rewrite :=
  PlainBnfScalarOrderSource.providerRows[index.val]'(by
    rw [PlainBnfScalarOrderSource.providerRows_count]; omega)

private def providerName (index : Fin 4) : String :=
  if index.val = 0 then "ground-integer-less"
  else if index.val = 1 then "ground-integer-not-less"
  else if index.val = 2 then "ground-integer-gap"
  else "ground-integer-no-gap"

private theorem providers_exact (index : Fin 4) :
    matchingProviders (providerName index) = [providerRow index] := by
  fin_cases index <;> rfl

private theorem provider_sides (index : Fin 4) :
    SourceIntegerProviderNativeType.equationSides? (providerRow index) =
      some (SourceIntegerProviderNativeType.binaryShape (providerName index)
        ("?left", "?right") (index.val % 2 == 1) (2 ≤ index.val)) := by
  fin_cases index <;> rfl

theorem provider_gap (left right : Int) :
    providerAnswers? (.list [.atom "ground-integer-gap", .atom (toString left),
      .atom (toString right)]) = some (if left + 1 < right then
        [.list [.atom "ground-integer-gap", .atom (toString left), .atom (toString right)]]
        else []) := by
  unfold providerAnswers?
  simp only [SourceIntegerProvider.integerValue?_repr]
  rw [show matchingProviders "ground-integer-gap" = [providerRow 2] from providers_exact 2]
  simp only [List.mapM_cons, List.mapM_nil, pure_bind]
  rw [provider_sides 2]
  simp [providerName, SourceIntegerProviderNativeType.binaryShape,
    SourceIntegerProvider.closeTerm?, SourceIntegerProvider.closeTerms?,
    SourceIntegerProvider.sourceVariableToken, SourceIntegerProvider.lookup?, integerEnv,
    SourceIntegerProvider.evalAnswers?, SourceIntegerProvider.evalBoolean?,
    SourceIntegerProvider.evalInteger?, SourceIntegerProvider.integerValue?_one]
  split <;> rfl

theorem provider_no_gap (left right : Int) :
    providerAnswers? (.list [.atom "ground-integer-no-gap", .atom (toString left),
      .atom (toString right)]) = some (if right ≤ left + 1 then
        [.list [.atom "ground-integer-no-gap", .atom (toString left), .atom (toString right)]]
        else []) := by
  unfold providerAnswers?
  simp only [SourceIntegerProvider.integerValue?_repr]
  rw [show matchingProviders "ground-integer-no-gap" = [providerRow 3] from providers_exact 3]
  simp only [List.mapM_cons, List.mapM_nil, pure_bind]
  rw [provider_sides 3]
  simp [providerName, SourceIntegerProviderNativeType.binaryShape,
    SourceIntegerProvider.closeTerm?, SourceIntegerProvider.closeTerms?,
    SourceIntegerProvider.sourceVariableToken, SourceIntegerProvider.lookup?, integerEnv,
    SourceIntegerProvider.evalAnswers?, SourceIntegerProvider.evalBoolean?,
    SourceIntegerProvider.evalInteger?, SourceIntegerProvider.integerValue?_one]
  split <;> rfl

def selectedInteger (relation : String) : Bool :=
  relation == "ground-integer-less" || relation == "ground-integer-not-less" ||
  relation == "ground-integer-gap" || relation == "ground-integer-no-gap"

/-- Transport exact echoed provider arguments into the existing relation
interface. Unsupported input is outside the proven primitive domain. -/
def integerTuples? (relation : String) (arguments : List Pattern) : Option (List (List Pattern)) := do
  let input ← SourceSExprPatternCodec.decodeList arguments
  let answers ← providerAnswers? (.list (.atom relation :: input))
  answers.mapM (fun answer => do
    let .list (.atom head :: output) := answer | none
    if head = relation then some (encodeList output) else none)

def relations : RelationEnv where
  tuples relation arguments :=
    if relation = "different" then scalarRelations.tuples relation arguments
    else if selectedInteger relation then (integerTuples? relation arguments).getD []
    else []

/-- The adapter uses the provider's decoded, ordered source rows. The complete
provider envelope and signature are also admitted by the canonical decoder. -/
theorem provider_source_admitted :
    (Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decode
      PlainBnfScalarOrderSource.providerSyntax).isSome = true := by
  have one : "1".toNat? = some 1 := Nat.toNat?_repr 1
  have two : "2".toNat? = some 2 := Nat.toNat?_repr 2
  have three : "3".toNat? = some 3 := Nat.toNat?_repr 3
  simp [PlainBnfScalarOrderSource.providerSyntax,
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decode,
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decodeList,
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decodeOperator,
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decodeRewrite,
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.atomToken?, one, two, three]

def scalar (value : Nat) : SExpr := .atom (toString value)

theorem natural_integer_spelling (value : Nat) : toString (value : Int) = toString value := rfl

private theorem tuples_less (left right : Nat) :
    relations.tuples "ground-integer-less" [encode (scalar left), encode (scalar right)] =
      if left < right then [[encode (scalar left), encode (scalar right)]] else [] := by
  have source := PlainBnfScalarOrderSource.provider_less (left : Int) (right : Int)
  simp only [natural_integer_spelling, Int.ofNat_lt] at source
  change providerAnswers? (.list [.atom "ground-integer-less", .atom left.repr, .atom right.repr]) = _ at source
  simp [relations, selectedInteger, integerTuples?, scalar,
    SourceSExprPatternCodec.decodeList, source]
  split <;> rfl

private theorem tuples_not_less (left right : Nat) :
    relations.tuples "ground-integer-not-less" [encode (scalar left), encode (scalar right)] =
      if right ≤ left then [[encode (scalar left), encode (scalar right)]] else [] := by
  have source := PlainBnfScalarOrderSource.provider_not_less (left : Int) (right : Int)
  simp only [natural_integer_spelling, Int.ofNat_le] at source
  change providerAnswers? (.list [.atom "ground-integer-not-less", .atom left.repr, .atom right.repr]) = _ at source
  simp [relations, selectedInteger, integerTuples?, scalar,
    SourceSExprPatternCodec.decodeList, source]
  split <;> rfl

private theorem tuples_gap (left right : Nat) :
    relations.tuples "ground-integer-gap" [encode (scalar left), encode (scalar right)] =
      if left + 1 < right then [[encode (scalar left), encode (scalar right)]] else [] := by
  have source := provider_gap (left : Int) (right : Int)
  have comparison : ((left : Int) + 1 < right) ↔ left + 1 < right := by omega
  simp only [natural_integer_spelling, comparison] at source
  change providerAnswers? (.list [.atom "ground-integer-gap", .atom left.repr, .atom right.repr]) = _ at source
  simp [relations, selectedInteger, integerTuples?, scalar,
    SourceSExprPatternCodec.decodeList, source]
  split <;> rfl

private theorem tuples_no_gap (left right : Nat) :
    relations.tuples "ground-integer-no-gap" [encode (scalar left), encode (scalar right)] =
      if right ≤ left + 1 then [[encode (scalar left), encode (scalar right)]] else [] := by
  have source := provider_no_gap (left : Int) (right : Int)
  have comparison : ((right : Int) ≤ (left : Int) + 1) ↔ right ≤ left + 1 := by omega
  simp only [natural_integer_spelling, comparison] at source
  change providerAnswers? (.list [.atom "ground-integer-no-gap", .atom left.repr, .atom right.repr]) = _ at source
  simp [relations, selectedInteger, integerTuples?, scalar,
    SourceSExprPatternCodec.decodeList, source]
  split <;> rfl

theorem different_tuples (left right : Pattern) :
    relations.tuples "different" [left, right] = if left = right then [] else [[left, right]] := by
  simp [relations, scalarRelations]

def mode? : String → Option (Nat × Nat)
  | "BNFLexicalMatcherInhabitedV1" => some (1, 1)
  | "BNFExclusionTailInhabitedV1" => some (2, 1)
  | "BNFExclusionGapInhabitedV1" => some (3, 1)
  | _ => none

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? : SExpr → Option Premise
  | .list [.atom relation, left, right] =>
    if relation = "different" || selectedInteger relation then
      some (.relationQuery relation [pattern left, pattern right])
    else do
      let (input, output) ← splitCall? (.list [.atom relation, left, right])
      some (.congruence (pattern input) (pattern output))
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

def rows : List Rewrite := (graphSource.rewrites.drop 40).take 11
def rules : List RewriteRule := (rows.mapM lowerRule?).get (by rfl)
def language : LanguageDef :=
  { name := "PlainBnfAuthoredLexicalMatcherInhabitation",
    types := [], terms := [], equations := [], rewrites := rules }

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl
theorem source_occurrences_exact : rows.zipIdx 40 = ((graphSource.rewrites.zipIdx).drop 40).take 11 := rfl
theorem source_family_exhaustive :
    graphSource.rewrites.filter (fun row => (splitCall? row.head).isSome) = rows := rfl

def answer (value : Bool) : SExpr := .atom (if value then "BNFYesV1" else "BNFNoV1")
def matcherCall (value : LexicalMatcher) : Pattern := call "BNFLexicalMatcherInhabitedV1" [matcher value]
def tailCall (left : Nat) (tail : List Nat) : Pattern :=
  call "BNFExclusionTailInhabitedV1" [scalar left, scalars tail]
def gapCall (left right : Nat) (tail : List Nat) : Pattern :=
  call "BNFExclusionGapInhabitedV1" [scalar left, scalar right, scalars tail]

theorem scalar_injective : Function.Injective scalar := by
  intro left right same
  exact Nat.repr_injective (SExpr.atom.inj same)

theorem encoded_scalar_eq_iff (left right : Nat) :
    encode (scalar left) = encode (scalar right) ↔ left = right :=
  ⟨fun same => scalar_injective (SourceSExprPatternCodec.encode_injective same),
    fun same => congrArg (fun value => encode (scalar value)) same⟩

private def observed (name : String) (input output : SExpr) (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }

/- Checked observations of the source-derived rules, never their authority. -/
private def observedRules : List RewriteRule :=
  [observed "bnf-points-empty-uninhabited-v1"
    (metta_sexpr% petta "(BNFLexicalMatcherInhabitedV1 (bnf-v1:lexical-points (metta-nullary bnf-v1:scalars-nil)))")
    (metta_sexpr% petta "(BNFNoV1)"),
   observed "bnf-points-cons-inhabited-v1"
    (metta_sexpr% petta "(BNFLexicalMatcherInhabitedV1 (bnf-v1:lexical-points (bnf-v1:scalars-cons ?first ?tail)))")
    (metta_sexpr% petta "(BNFYesV1)"),
   observed "bnf-exclusion-empty-inhabited-v1"
    (metta_sexpr% petta "(BNFLexicalMatcherInhabitedV1 (bnf-v1:lexical-except (metta-nullary bnf-v1:scalars-nil)))")
    (metta_sexpr% petta "(BNFYesV1)"),
   observed "bnf-exclusion-zero-inhabited-v1"
    (metta_sexpr% petta "(BNFLexicalMatcherInhabitedV1 (bnf-v1:lexical-except (bnf-v1:scalars-cons 0 ?tail)))")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFExclusionTailInhabitedV1 0 ?tail ?result)"],
   observed "bnf-exclusion-missing-zero-inhabited-v1"
    (metta_sexpr% petta "(BNFLexicalMatcherInhabitedV1 (bnf-v1:lexical-except (bnf-v1:scalars-cons ?first ?tail)))")
    (metta_sexpr% petta "(BNFYesV1)")
    [metta_sexpr% petta "(different ?first 0)"],
   observed "bnf-exclusion-tail-missing-last-v1"
    (metta_sexpr% petta "(BNFExclusionTailInhabitedV1 ?last (metta-nullary bnf-v1:scalars-nil))")
    (metta_sexpr% petta "(BNFYesV1)")
    [metta_sexpr% petta "(ground-integer-less ?last 1114111)"],
   observed "bnf-exclusion-tail-complete-v1"
    (metta_sexpr% petta "(BNFExclusionTailInhabitedV1 ?last (metta-nullary bnf-v1:scalars-nil))")
    (metta_sexpr% petta "(BNFNoV1)")
    [metta_sexpr% petta "(ground-integer-not-less ?last 1114111)"],
   observed "bnf-exclusion-tail-cons-v1"
    (metta_sexpr% petta "(BNFExclusionTailInhabitedV1 ?left (bnf-v1:scalars-cons ?right ?tail))")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFExclusionGapInhabitedV1 ?left ?right ?tail ?result)"],
   observed "bnf-exclusion-surrogate-interval-v1"
    (metta_sexpr% petta "(BNFExclusionGapInhabitedV1 55295 57344 ?tail)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFExclusionTailInhabitedV1 57344 ?tail ?result)"],
   observed "bnf-exclusion-gap-v1"
    (metta_sexpr% petta "(BNFExclusionGapInhabitedV1 ?left ?right ?tail)")
    (metta_sexpr% petta "(BNFYesV1)")
    [metta_sexpr% petta "(different (BNFScalarPairV1 ?left ?right) (BNFScalarPairV1 55295 57344))",
     metta_sexpr% petta "(ground-integer-gap ?left ?right)"],
   observed "bnf-exclusion-no-gap-v1"
    (metta_sexpr% petta "(BNFExclusionGapInhabitedV1 ?left ?right ?tail)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(different (BNFScalarPairV1 ?left ?right) (BNFScalarPairV1 55295 57344))",
     metta_sexpr% petta "(ground-integer-no-gap ?left ?right)",
     metta_sexpr% petta "(BNFExclusionTailInhabitedV1 ?right ?tail ?result)"]]

private theorem rules_exact : language.rewrites = observedRules := rfl

def relationHeads :=
  ["BNFLexicalMatcherInhabitedV1", "BNFExclusionTailInhabitedV1", "BNFExclusionGapInhabitedV1"]

theorem family_heads : language.rewrites.all
    (fun rule => PlainBnfIndexedCollectorSourceExecution.headedBy relationHeads rule.left) = true := by
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, PlainBnfIndexedCollectorSourceExecution.headedBy, relationHeads,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (PlainBnfIndexedCollectorSourceExecution.premiseClosed relationHeads)) = true := by
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, PlainBnfIndexedCollectorSourceExecution.premiseClosed,
    PlainBnfIndexedCollectorSourceExecution.headedBy, relationHeads,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

@[local simp] private theorem numeral_zero : Nat.repr 0 = "0" := by decide
@[local simp] private theorem numeral_before_hole : Nat.repr 55295 = "55295" := by decide
@[local simp] private theorem numeral_after_hole : Nat.repr 57344 = "57344" := by decide
@[local simp] private theorem numeral_last : Nat.repr 1114111 = "1114111" := by decide

private theorem points_nil (fuel : Nat) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (matcherCall (.points [])) =
      [result (answer false)] := by
  simp [rewriteAt, rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, matcherCall, call, result, matcher, scalars, answer,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem points_cons (fuel : Nat) (head : Nat) (tail : List Nat) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (matcherCall (.points (head :: tail))) =
      [result (answer true)] := by
  simp [rewriteAt, rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, matcherCall, call, result, matcher, scalars, answer,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem exclusion_nil (fuel : Nat) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (matcherCall (.except [])) =
      [result (answer true)] := by
  simp [rewriteAt, rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, matcherCall, call, result, matcher, scalars, answer,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem tail_nil (fuel : Nat) (left : Nat) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (tailCall left []) =
      [result (answer (decide (left < 1114111)))] := by
  rw [rewriteAt]
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, tailCall, call, scalars, scalar,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep, builtinRelationTuples]
  have less := tuples_less left 1114111
  have notLess := tuples_not_less left 1114111
  simp [scalar, encode] at less notLess
  rw [less, notLess]
  by_cases before : left < 1114111
  · have later : ¬ 1114111 ≤ left := by omega
    simp [before, later, result, answer, encode, encodeList,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs, mergeBindings, List.foldlM,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      Bindings.lookup, applyBindings]
  · have later : 1114111 ≤ left := by omega
    simp [before, later, result, answer, encode, encodeList,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs, mergeBindings, List.foldlM,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      Bindings.lookup, applyBindings]

@[local simp] private theorem repr_eq_zero (value : Nat) : value.repr = "0" ↔ value = 0 :=
  ⟨fun same => Nat.repr_injective (same.trans numeral_zero.symm), fun same => same ▸ numeral_zero⟩
@[local simp] private theorem zero_eq_repr (value : Nat) : "0" = value.repr ↔ 0 = value :=
  ⟨fun same => (Nat.repr_injective (same.symm.trans numeral_zero.symm)).symm,
    fun same => same ▸ numeral_zero.symm⟩
@[local simp] private theorem repr_eq_before_hole (value : Nat) : value.repr = "55295" ↔ value = 55295 :=
  ⟨fun same => Nat.repr_injective (same.trans numeral_before_hole.symm), fun same => same ▸ numeral_before_hole⟩
@[local simp] private theorem before_hole_eq_repr (value : Nat) : "55295" = value.repr ↔ 55295 = value :=
  ⟨fun same => (Nat.repr_injective (same.symm.trans numeral_before_hole.symm)).symm,
    fun same => same ▸ numeral_before_hole.symm⟩
@[local simp] private theorem repr_eq_after_hole (value : Nat) : value.repr = "57344" ↔ value = 57344 :=
  ⟨fun same => Nat.repr_injective (same.trans numeral_after_hole.symm), fun same => same ▸ numeral_after_hole⟩
@[local simp] private theorem after_hole_eq_repr (value : Nat) : "57344" = value.repr ↔ 57344 = value :=
  ⟨fun same => (Nat.repr_injective (same.symm.trans numeral_after_hole.symm)).symm,
    fun same => same ▸ numeral_after_hole.symm⟩

private theorem tail_cons (fuel : Nat) (left right : Nat) (tail : List Nat) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises relations) language fuel (gapCall left right tail) =
      answers.map result) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (tailCall left (right :: tail)) =
      answers.map result := by
  rw [rewriteAt]
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, tailCall, call, scalars,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp [gapCall, call, scalar, encode, encodeList] at recursive
  simp [scalar, encode]
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings, ← List.map_eq_flatMap]

private theorem gap_hole (fuel : Nat) (tail : List Nat) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises relations) language fuel (tailCall 57344 tail) =
      answers.map result) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (gapCall 55295 57344 tail) =
      answers.map result := by
  rw [rewriteAt]
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, gapCall, call, scalar,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    different_tuples]
  simp [tailCall, call, scalar, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings, ← List.map_eq_flatMap]

private theorem gap_ordinary (fuel : Nat) (left right : Nat) (tail : List Nat)
    (notHole : ¬ (left = 55295 ∧ right = 57344)) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises relations) language fuel (tailCall right tail) =
      answers.map result) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (gapCall left right tail) =
      if left + 1 < right then [result (answer true)] else answers.map result := by
  rw [rewriteAt]
  have reversedHole : ¬ (55295 = left ∧ 57344 = right) := by omega
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, gapCall, call, scalar,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    different_tuples, notHole, matchRelationArgs, matchRelationArgument]
  have gap := tuples_gap left right
  have noGap := tuples_no_gap left right
  simp [scalar, encode] at gap noGap
  rw [gap, noGap]
  by_cases separated : left + 1 < right
  · have adjacent : ¬ right ≤ left + 1 := by omega
    by_cases leftEdge : 55295 = left <;> by_cases rightEdge : 57344 = right <;>
      simp_all [result, answer, encode, encodeList,
      matchRelationArgs, matchRelationArgument, mergeBindings, List.foldlM,
      Bindings.lookup]
  · have adjacent : right ≤ left + 1 := by omega
    simp [separated, adjacent, matchRelationArgs, matchRelationArgument,
      mergeBindings, List.foldlM, Bindings.lookup]
    simp [tailCall, call, scalar, encode, encodeList] at recursive
    rw [recursive]
    by_cases leftEdge : 55295 = left <;> by_cases rightEdge : 57344 = right <;>
      simp_all [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
      List.foldlM, mergeBindings, ← List.map_eq_flatMap]

def tailHeight (left : Nat) : List Nat → Nat
  | [] => 0
  | right :: rest =>
      if left = 55295 ∧ right = 57344 then 2 + tailHeight right rest
      else if left + 1 < right then 1 else 2 + tailHeight right rest

def gapHeight (left right : Nat) (tail : List Nat) : Nat :=
  if left = 55295 ∧ right = 57344 then 1 + tailHeight right tail
  else if left + 1 < right then 0 else 1 + tailHeight right tail

private theorem tailHeight_cons (left right : Nat) (tail : List Nat) :
    tailHeight left (right :: tail) = 1 + gapHeight left right tail := by
  simp only [tailHeight, gapHeight]
  split_ifs <;> omega

theorem scan_answers (fuel : Nat) :
    (∀ left tail, rewriteAt (engineBasePremises relations) language fuel (tailCall left tail) =
      if tailHeight left tail < fuel then [result (answer (gapAfter left tail))] else []) ∧
    (∀ left right tail, rewriteAt (engineBasePremises relations) language fuel (gapCall left right tail) =
      if gapHeight left right tail < fuel then [result (answer (gapAfter left (right :: tail)))] else []) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
    constructor
    · intro left tail
      cases tail with
      | nil => simpa [tailHeight, gapAfter] using tail_nil fuel left
      | cons right rest =>
        by_cases enough : gapHeight left right rest < fuel
        · have step := tail_cons fuel left right rest [answer (gapAfter left (right :: rest))]
            (by simpa [enough] using ih.2 left right rest)
          have bound : tailHeight left (right :: rest) < fuel + 1 := by rw [tailHeight_cons]; omega
          simpa [bound] using step
        · have step := tail_cons fuel left right rest [] (by simpa [enough] using ih.2 left right rest)
          have bound : ¬ tailHeight left (right :: rest) < fuel + 1 := by rw [tailHeight_cons]; omega
          simpa [bound] using step
    · intro left right tail
      by_cases hole : left = 55295 ∧ right = 57344
      · rcases hole with ⟨rfl, rfl⟩
        by_cases enough : tailHeight 57344 tail < fuel
        · have step := gap_hole fuel tail [answer (gapAfter 57344 tail)]
            (by simpa [enough] using ih.1 57344 tail)
          have bound : gapHeight 55295 57344 tail < fuel + 1 := by simp [gapHeight]; omega
          simpa [bound, gapAfter] using step
        · have step := gap_hole fuel tail [] (by simpa [enough] using ih.1 57344 tail)
          have bound : ¬ gapHeight 55295 57344 tail < fuel + 1 := by simp [gapHeight]; omega
          simpa [bound] using step
      · have recursive : rewriteAt (engineBasePremises relations) language fuel (tailCall right tail) =
            (if tailHeight right tail < fuel then [answer (gapAfter right tail)] else []).map result := by
          split_ifs with enough <;> simpa [enough] using ih.1 right tail
        have step := gap_ordinary fuel left right tail hole _ recursive
        by_cases separated : left + 1 < right
        · simpa [gapHeight, gapAfter, hole, separated] using step
        · by_cases enough : tailHeight right tail < fuel
          · have bound : gapHeight left right tail < fuel + 1 := by
              simp only [gapHeight, if_neg hole, if_neg separated]; omega
            simpa [gapAfter, hole, separated, enough, bound] using step
          · have bound : ¬ gapHeight left right tail < fuel + 1 := by
              simp only [gapHeight, if_neg hole, if_neg separated]; omega
            simpa [gapAfter, hole, separated, enough, bound] using step

private theorem exclusion_zero (fuel : Nat) (tail : List Nat) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises relations) language fuel (tailCall 0 tail) =
      answers.map result) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (matcherCall (.except (0 :: tail))) =
      answers.map result := by
  rw [rewriteAt]
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, matcherCall, call, matcher, scalars,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    different_tuples]
  simp [tailCall, call, scalar, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings, ← List.map_eq_flatMap]

private theorem exclusion_nonzero (fuel : Nat) (head : Nat) (tail : List Nat) (nonzero : head ≠ 0) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (matcherCall (.except (head :: tail))) =
      [result (answer true)] := by
  have other : 0 ≠ head := Ne.symm nonzero
  simp [rewriteAt, rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    selectedInteger, applyRuleUsing, matcherCall, call, matcher, scalars, result, answer,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    different_tuples, nonzero, other, matchRelationArgs, matchRelationArgument, Bindings.lookup]

def matcherHeight : LexicalMatcher → Nat
  | .points _ => 0
  | .except [] => 0
  | .except (head :: tail) => if head = 0 then 1 + tailHeight head tail else 0

def matcherMeaning : LexicalMatcher → Bool
  | .points values => !values.isEmpty
  | .except values => exceptGapCheck values

theorem matcher_answers (fuel : Nat) (value : LexicalMatcher) :
    rewriteAt (engineBasePremises relations) language fuel (matcherCall value) =
      if matcherHeight value < fuel then [result (answer (matcherMeaning value))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    cases value with
    | points values =>
      cases values with
      | nil => simpa [matcherHeight, matcherMeaning] using points_nil fuel
      | cons head tail => simpa [matcherHeight, matcherMeaning] using points_cons fuel head tail
    | except values =>
      cases values with
      | nil => simpa [matcherHeight, matcherMeaning, exceptGapCheck] using exclusion_nil fuel
      | cons head tail =>
        by_cases zero : head = 0
        · subst head
          by_cases enough : tailHeight 0 tail < fuel
          · have step := exclusion_zero fuel tail [answer (gapAfter 0 tail)]
              (by simpa [enough] using (scan_answers fuel).1 0 tail)
            have bound : matcherHeight (.except (0 :: tail)) < fuel + 1 := by
              simp [matcherHeight]; omega
            simpa [bound, matcherMeaning, exceptGapCheck] using step
          · have step := exclusion_zero fuel tail [] (by simpa [enough] using (scan_answers fuel).1 0 tail)
            have bound : ¬ matcherHeight (.except (0 :: tail)) < fuel + 1 := by
              simp [matcherHeight]; omega
            simpa [bound] using step
        · simpa [matcherHeight, matcherMeaning, exceptGapCheck, zero] using exclusion_nonzero fuel head tail zero

theorem matcher_step_iff (value : LexicalMatcher) (target : Pattern) :
    Step (engineBasePremises relations) language (matcherCall value) target ↔
      target = result (answer (matcherMeaning value)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [matcher_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨matcherHeight value + 1, by simp [matcher_answers]⟩

theorem tail_step_iff (left : Nat) (tail : List Nat) (target : Pattern) :
    Step (engineBasePremises relations) language (tailCall left tail) target ↔
      target = result (answer (gapAfter left tail)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(scan_answers fuel).1] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨tailHeight left tail + 1, by simp [(scan_answers _).1]⟩

theorem gap_step_iff (left right : Nat) (tail : List Nat) (target : Pattern) :
    Step (engineBasePremises relations) language (gapCall left right tail) target ↔
      target = result (answer (gapAfter left (right :: tail))) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(scan_answers fuel).2] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨gapHeight left right tail + 1, by simp [(scan_answers _).2]⟩

theorem result_answer_injective : Function.Injective (fun value => result (answer value)) := by
  intro left right same
  cases left <;> cases right <;> simp_all [result, answer, encode, encodeList]

theorem matcher_decoded_step_iff (value : LexicalMatcher) (output : Bool) :
    Step (engineBasePremises relations) language (matcherCall value) (result (answer output)) ↔
      output = matcherMeaning value := by
  rw [matcher_step_iff, result_answer_injective.eq_iff]

def lexicalClass : LexicalMatcher → ParserProfileSemantics.LexicalClassKind
  | .points values => .points values
  | .except values => .except values

theorem lexicalClass_agrees_with_denotation (declaration : PlainBnfStructuredDenotation.LexicalDeclaration) :
    lexicalClass declaration.matcher = (PlainBnfStructuredDenotation.denoteLexicalClass declaration).kind := rfl

/-- Nonemptiness requires the source caller's validity and strict-order
license. The source computation by itself does not establish either fact. -/
theorem matcher_yes_iff_inhabited (value : LexicalMatcher)
    (valid : match value with
      | .points values | .except values => ∀ scalar ∈ values,
          ParserProfileSemantics.isUnicodeScalar scalar = true)
    (ordered : match value with
      | .points values | .except values => values.Pairwise (· < ·)) :
    Step (engineBasePremises relations) language (matcherCall value) (result (answer true)) ↔
      PlainBnfLexicalInhabitation.InhabitedClass (lexicalClass value) := by
  rw [matcher_decoded_step_iff, eq_comm]
  have inventory : PlainBnfLexicalInhabitation.ClassInventoryValid (lexicalClass value) := by
    cases value with
    | points values => exact ⟨ordered.imp Nat.ne_of_lt, valid⟩
    | except values => exact ⟨ordered.imp Nat.ne_of_lt, valid⟩
  cases value with
  | points values =>
    exact PlainBnfLexicalInhabitation.checkInhabitedByGaps_iff (.points values) inventory ordered
  | except values =>
    exact PlainBnfLexicalInhabitation.checkInhabitedByGaps_iff (.except values) inventory ordered

theorem matcher_no_iff_uninhabited (value : LexicalMatcher)
    (valid : match value with
      | .points values | .except values => ∀ scalar ∈ values,
          ParserProfileSemantics.isUnicodeScalar scalar = true)
    (ordered : match value with
      | .points values | .except values => values.Pairwise (· < ·)) :
    Step (engineBasePremises relations) language (matcherCall value) (result (answer false)) ↔
      ¬ PlainBnfLexicalInhabitation.InhabitedClass (lexicalClass value) := by
  have positive := matcher_yes_iff_inhabited value valid ordered
  rw [matcher_decoded_step_iff] at positive ⊢
  cases meaning : matcherMeaning value <;> simp_all

theorem surrogate_skip_exact (fuel : Nat) (tail : List Nat) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (gapCall 55295 57344 tail) =
      rewriteAt (engineBasePremises relations) language fuel (tailCall 57344 tail) := by
  by_cases enough : tailHeight 57344 tail < fuel
  · have recursive := (scan_answers fuel).1 57344 tail
    have step := gap_hole fuel tail [answer (gapAfter 57344 tail)] (by simpa [enough] using recursive)
    simpa [recursive, enough] using step
  · have recursive := (scan_answers fuel).1 57344 tail
    have step := gap_hole fuel tail [] (by simpa [enough] using recursive)
    simpa [recursive, enough] using step

theorem surrogate_gap_not_an_immediate_yes :
    rewriteAt (engineBasePremises relations) language 1 (gapCall 55295 57344 []) = [] := by
  rw [surrogate_skip_exact 0]
  rfl

theorem endpoint_and_interior_controls :
    rewriteAt (engineBasePremises relations) language 1 (tailCall 1114110 []) = [result (answer true)] ∧
    rewriteAt (engineBasePremises relations) language 1 (tailCall 1114111 []) = [result (answer false)] ∧
    rewriteAt (engineBasePremises relations) language 1 (gapCall 7 9 []) = [result (answer true)] ∧
    rewriteAt (engineBasePremises relations) language 2 (gapCall 1114110 1114111 []) = [result (answer false)] := by
  simp [(scan_answers _).1, (scan_answers _).2, tailHeight, gapHeight, gapAfter]

theorem empty_and_positive_controls :
    rewriteAt (engineBasePremises relations) language 1 (matcherCall (.points [])) = [result (answer false)] ∧
    rewriteAt (engineBasePremises relations) language 1 (matcherCall (.points [65])) = [result (answer true)] ∧
    rewriteAt (engineBasePremises relations) language 1 (matcherCall (.except [])) = [result (answer true)] := by
  simp [matcher_answers, matcherHeight, matcherMeaning, exceptGapCheck]

theorem excluding_all_scalars_returns_no :
    Step (engineBasePremises relations) language
      (matcherCall (.except PlainBnfLexicalInhabitation.allScalars)) (result (answer false)) := by
  rw [matcher_decoded_step_iff]
  exact PlainBnfLexicalInhabitation.full_exclusion_gap_check_is_false.symm

theorem excluding_all_scalars_cannot_return_yes :
    ¬ Step (engineBasePremises relations) language
      (matcherCall (.except PlainBnfLexicalInhabitation.allScalars)) (result (answer true)) := by
  rw [matcher_decoded_step_iff]
  simp [matcherMeaning, PlainBnfLexicalInhabitation.full_exclusion_gap_check_is_false]

/-- A positive source result is not scalar validity: the points-cons rule
does not inspect its elements. -/
theorem invalid_positive_list_needs_separate_admission :
    rewriteAt (engineBasePremises relations) language 1 (matcherCall (.points [55296])) = [result (answer true)] ∧
      ¬ PlainBnfLexicalInhabitation.InhabitedClass (.points [55296]) := by
  exact ⟨points_cons 0 55296 [], PlainBnfLexicalInhabitation.invalid_positive_scalar_is_not_productive⟩

theorem reversed_list_is_not_normalized :
    rewriteAt (engineBasePremises relations) language 1 (matcherCall (.except [1, 0])) = [result (answer true)] ∧
      ¬ ([1, 0] : List Nat).Pairwise (· < ·) := by
  constructor
  · exact exclusion_nonzero 0 1 [0] (by decide)
  · decide

/-- Prepending a nonzero scalar to a complete exclusion inventory violates
the ordering license. The source returns yes while the class remains empty. -/
theorem unordered_complete_exclusion_is_a_false_positive :
    rewriteAt (engineBasePremises relations) language 1
      (matcherCall (.except (1 :: PlainBnfLexicalInhabitation.allScalars))) = [result (answer true)] ∧
      ¬ PlainBnfLexicalInhabitation.InhabitedClass (.except (1 :: PlainBnfLexicalInhabitation.allScalars)) := by
  constructor
  · exact exclusion_nonzero 0 1 _ (by decide)
  · rintro ⟨value, accepted⟩
    have facts : ParserProfileSemantics.isUnicodeScalar value = true ∧
        value ∉ 1 :: PlainBnfLexicalInhabitation.allScalars := by
      simpa [ParserProfileSemantics.LexicalClassKind.accepts] using accepted
    exact facts.2 (List.mem_cons_of_mem _ ((PlainBnfLexicalInhabitation.mem_allScalars value).mpr facts.1))

theorem insufficient_depth_has_no_answer (value : LexicalMatcher) :
    rewriteAt (engineBasePremises relations) language (matcherHeight value) (matcherCall value) = [] := by
  simp [matcher_answers]

theorem matcher_answer_hook_absent (arguments : List Pattern) :
    relations.tuples "BNFLexicalMatcherInhabitedV1" arguments = [] := by
  simp [relations, selectedInteger]

/-- Unsupported spelling remains unsupported at the source adapter. Its
relation-view fallback is not an assertion of Boolean falsity or admission. -/
theorem noncanonical_integer_query_unsupported :
    integerTuples? "ground-integer-less" [encode (.atom "01"), encode (.atom "2")] = none := by
  simp [integerTuples?, SourceSExprPatternCodec.decodeList,
    PlainBnfScalarOrderSource.noncanonical_integer_guard_refused]

theorem wrong_arity_not_selected (input extra : SExpr) :
    splitCall? (.list [.atom "BNFLexicalMatcherInhabitedV1", input, .atom "?result", extra]) = none := by
  simp [splitCall?, mode?]

#print axioms scan_answers
#print axioms matcher_answers
#print axioms matcher_step_iff
#print axioms matcher_yes_iff_inhabited
#print axioms excluding_all_scalars_returns_no
#print axioms unordered_complete_exclusion_is_a_false_positive

end Mettapedia.GSLT.Parsing.PlainBnfLexicalMatcherSourceExecution
