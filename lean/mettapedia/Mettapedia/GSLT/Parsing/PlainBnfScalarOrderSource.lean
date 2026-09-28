import Mettapedia.GSLT.Parsing.SourceIntegerProviderNativeType
import Mettapedia.GSLT.Parsing.SourceSExprPatternInstantiation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Exact source answers of the selected lexical scalar-order rules

The canonical source reader retrieves the actual two scalar-order rows and
their actual Integer-provider equations. The finite computation below closes
each source head and its single premise, evaluates the retrieved provider
expression, then returns the instantiated source output once per provider
answer occurrence. It is not a grammar evaluator or a target runtime.

The theorem concerns mathematical Integer operands before Unicode/order
validation and arbitrary inert origin data. Native structural admission,
machine representation, target dispatch and target binding are separate
connections. Raw row quotation does not prove the byte reader correct.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfScalarOrderSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open SourceIntegerProvider (evalAnswers? closeTerm?)
open SourceIntegerProviderNativeType (equationSides?)
open SourceSExprPatternInstantiation (instantiate? instantiateList?)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def sourceSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/plain_bnf_semantic_admission_v1.metta"

def providerSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/experiments/gslt2parse_foundation/presentations/shared/cetta_petta_ground_integer_relations_v1.metta"

private def rawRows : SExpr → List SExpr
  | .list [.atom "gslt-presentation-v1", _, .list (.atom "signature" :: _),
      .list (.atom "equations" :: _), .list (.atom "rewrites" :: rows)] => rows
  | _ => []

def sourceRows : List Rewrite := (rawRows sourceSyntax).filterMap decodeRewrite

def providerRows : List Rewrite := (rawRows providerSyntax).filterMap decodeRewrite

/-- No malformed row was silently discarded by the finite projections. -/
theorem sourceRows_decoded :
    decodeList decodeRewrite (rawRows sourceSyntax) = some sourceRows := rfl

theorem providerRows_decoded :
    decodeList decodeRewrite (rawRows providerSyntax) = some providerRows := rfl

/-- The full source contains no variable-headed rule hidden by literal-head
selection. This concerns these quoted rows, not later source extensions. -/
theorem source_heads_literal : sourceRows.all (fun row => match row.head with
    | .list (.atom head :: _) => !SourceIntegerProvider.sourceVariableToken head
    | _ => false) = true := by
  simp [sourceRows, rawRows, sourceSyntax, decodeRewrite, atomToken?,
    SourceIntegerProvider.sourceVariableToken]

def relation : String := "BNFScalarOrderDiagnosticV1"

def hasHead (symbol : String) : Rewrite → Bool
  | ⟨_, .list (.atom head :: _), _⟩ => head == symbol
  | _ => false

/-- All source occurrences with this literal head, retaining their order. -/
def scalarRows : List Rewrite := sourceRows.filter (hasHead relation)

theorem scalarRows_count : scalarRows.length = 2 := rfl

def scalarRow (index : Fin 2) : Rewrite :=
  scalarRows[index.val]'(by rw [scalarRows_count]; exact index.isLt)

theorem scalarRows_exact : scalarRows = [scalarRow 0, scalarRow 1] := rfl

theorem scalarRow_occurrence (index : Fin 2) :
    rawRewriteAt? sourceSyntax (32 + index.val) = some (scalarRow index) := by
  fin_cases index <;> rfl

theorem scalarRow_name (index : Fin 2) : (scalarRow index).name =
    (if index.val = 0 then "bnf-increasing-lexical-scalars-v1"
      else "bnf-nonincreasing-lexical-scalars-v1") := by
  fin_cases index <;> rfl

theorem scalarRow_head (index : Fin 2) :
    (scalarRow index).head = .list [.atom relation, .atom "?left", .atom "?right",
      .atom "?origin", if index.val = 0 then .atom "BNFDiagnosticsNilV1" else
        .list [.atom "BNFDiagnosticsConsV1",
          .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom "?left", .atom "?right",
            .atom "?origin"], .atom "BNFDiagnosticsNilV1"]] := by
  fin_cases index <;> rfl

theorem scalarRow_body (index : Fin 2) :
    (scalarRow index).body = [.list [.atom (if index.val = 0 then
      "ground-integer-less" else "ground-integer-not-less"),
      .atom "?left", .atom "?right"]] := by
  fin_cases index <;> rfl

def sourceEnv (left right : Int) (origin : SExpr) : SourceSExprPatternInstantiation.Env :=
  [("?left", .atom (toString left)), ("?right", .atom (toString right)), ("?origin", origin)]

def integerEnv (left right : Int) : SourceIntegerProvider.Env :=
  [("?left", left), ("?right", right)]

/-- Select by the actual provider's literal wrapper head, not a separate
provider registry. All matching occurrences are retained. -/
def providerMatches (symbol : String) (row : Rewrite) : Bool :=
  match equationSides? row with
  | some (.list [.atom wrapper, _], _) => wrapper == "gslt:" ++ symbol
  | _ => false

def matchingProviders (symbol : String) : List Rewrite :=
  providerRows.filter (providerMatches symbol)

theorem providerRows_count : providerRows.length = 6 := rfl

def providerRow (index : Fin 2) : Rewrite :=
  providerRows[index.val]'(by rw [providerRows_count]; omega)

theorem providers_exact (index : Fin 2) :
    matchingProviders (if index.val = 0 then "ground-integer-less" else "ground-integer-not-less") =
      [providerRow index] := by
  fin_cases index <;> rfl

theorem provider_sides (index : Fin 2) :
    equationSides? (providerRow index) =
      some (SourceIntegerProviderNativeType.binaryShape
        (if index.val = 0 then "ground-integer-less" else "ground-integer-not-less")
        ("?left", "?right") (index.val != 0) false) := by
  fin_cases index <;> rfl

/-- Interpret one already ground binary query using the retrieved source
equations. Ill-formed queries and unsupported source bodies return `none`.
Repeated matching equations contribute repeated answer occurrences. -/
def providerAnswers? : SExpr → Option (List SExpr)
  | query@(.list [.atom symbol, .atom leftToken, .atom rightToken]) => do
      let left ← SourceIntegerProvider.integerValue? leftToken
      let right ← SourceIntegerProvider.integerValue? rightToken
      let answers ← (matchingProviders symbol).mapM (fun row => do
        let (head, body) ← equationSides? row
        let closedHead ← closeTerm? (integerEnv left right) head
        if closedHead = .list [.atom ("gslt:" ++ symbol), query] then
          evalAnswers? (integerEnv left right) body
        else none)
      return answers.flatten
  | _ => none

/-- A finite, single-premise source-rule observation. The output is read
from the instantiated authored head, not supplied by a result provider. -/
def ruleAnswers? (row : Rewrite) (left right : Int) (origin : SExpr) : Option (List SExpr) := do
  let head ← instantiate? (sourceEnv left right origin) row.head
  let premises ← instantiateList? (sourceEnv left right origin) row.body
  let .list [.atom symbol, first, second, location, output] := head | none
  if symbol != relation || first != .atom (toString left) ||
      second != .atom (toString right) || location != origin then none else do
    let [query] := premises | none
    let answers ← providerAnswers? query
    return answers.map (fun _ => output)

def sourceAnswers? (left right : Int) (origin : SExpr) : Option (List SExpr) := do
  let answers ← scalarRows.mapM (fun row => ruleAnswers? row left right origin)
  return answers.flatten

/-- Independent scalar-order diagnostic meaning. It is compared with the
computed source result; the source computation does not call this function. -/
def diagnostic (left right : Int) (origin : SExpr) : SExpr :=
  if left < right then .atom "BNFDiagnosticsNilV1"
  else .list [.atom "BNFDiagnosticsConsV1",
    .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom (toString left),
      .atom (toString right), origin], .atom "BNFDiagnosticsNilV1"]

theorem provider_less (left right : Int) :
    providerAnswers? (.list [.atom "ground-integer-less", .atom (toString left),
      .atom (toString right)]) = some (if left < right then
        [.list [.atom "ground-integer-less", .atom (toString left), .atom (toString right)]]
        else []) := by
  unfold providerAnswers?
  simp only [SourceIntegerProvider.integerValue?_repr]
  rw [show matchingProviders "ground-integer-less" = [providerRow 0] from
    providers_exact 0]
  simp only [List.mapM_cons, List.mapM_nil, pure_bind]
  rw [provider_sides 0]
  simp [SourceIntegerProviderNativeType.binaryShape,
    closeTerm?, SourceIntegerProvider.closeTerms?, SourceIntegerProvider.sourceVariableToken,
    SourceIntegerProvider.lookup?, integerEnv, evalAnswers?, SourceIntegerProvider.evalBoolean?,
    SourceIntegerProvider.evalInteger?]
  split <;> rfl

theorem provider_not_less (left right : Int) :
    providerAnswers? (.list [.atom "ground-integer-not-less", .atom (toString left),
      .atom (toString right)]) = some (if right ≤ left then
        [.list [.atom "ground-integer-not-less", .atom (toString left), .atom (toString right)]]
        else []) := by
  unfold providerAnswers?
  simp only [SourceIntegerProvider.integerValue?_repr]
  rw [show matchingProviders "ground-integer-not-less" = [providerRow 1] from
    providers_exact 1]
  simp only [List.mapM_cons, List.mapM_nil, pure_bind]
  rw [provider_sides 1]
  simp [SourceIntegerProviderNativeType.binaryShape,
    closeTerm?, SourceIntegerProvider.closeTerms?, SourceIntegerProvider.sourceVariableToken,
    SourceIntegerProvider.lookup?, integerEnv, evalAnswers?, SourceIntegerProvider.evalBoolean?,
    SourceIntegerProvider.evalInteger?]
  split <;> rfl

theorem first_rule_answers (left right : Int) (origin : SExpr) :
    ruleAnswers? (scalarRow 0) left right origin =
      some (if left < right then [.atom "BNFDiagnosticsNilV1"] else []) := by
  unfold ruleAnswers?
  rw [scalarRow_head, scalarRow_body]
  simp only [Fin.val_zero, ↓reduceIte]
  have provider := provider_less left right
  simp only [Int.toString_eq_repr] at provider
  simp [instantiate?, instantiateList?, sourceEnv, SourceIntegerProvider.sourceVariableToken,
    relation, provider]
  split <;> rfl

theorem second_rule_answers (left right : Int) (origin : SExpr) :
    ruleAnswers? (scalarRow 1) left right origin =
      some (if right ≤ left then [.list [.atom "BNFDiagnosticsConsV1",
        .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom (toString left),
          .atom (toString right), origin], .atom "BNFDiagnosticsNilV1"]] else []) := by
  unfold ruleAnswers?
  rw [scalarRow_head, scalarRow_body]
  simp only [Fin.val_one, Nat.one_ne_zero, ↓reduceIte]
  have provider := provider_not_less left right
  simp only [Int.toString_eq_repr] at provider
  simp [instantiate?, instantiateList?, sourceEnv, SourceIntegerProvider.sourceVariableToken,
    relation, provider]
  split <;> rfl

/-- Exactly one diagnostic-result packet is returned. The packet itself is
empty on increasing operands and contains one diagnostic otherwise. -/
theorem sourceAnswers_eq (left right : Int) (origin : SExpr) :
    sourceAnswers? left right origin = some [diagnostic left right origin] := by
  unfold sourceAnswers?
  rw [scalarRows_exact]
  simp only [List.mapM_cons, List.mapM_nil, first_rule_answers, second_rule_answers]
  by_cases increasing : left < right
  · have notReversed : ¬ right ≤ left := by omega
    simp [increasing, notReversed, diagnostic]
  · have reversed : right ≤ left := by omega
    simp [increasing, reversed, diagnostic]

theorem sourceAnswers_iff (left right : Int) (origin : SExpr) (answers : List SExpr) :
    sourceAnswers? left right origin = some answers ↔
      answers = [diagnostic left right origin] := by
  rw [sourceAnswers_eq]
  simp only [Option.some.injEq, eq_comm]

theorem sourceAnswers_single_occurrence (left right : Int) (origin : SExpr)
    (answers : List SExpr) (completed : sourceAnswers? left right origin = some answers) :
    answers.length = 1 := by
  rw [(sourceAnswers_iff left right origin answers).mp completed]
  rfl

/-- Repeating a successful authored rule repeats the result occurrence.
The finite source fold does not deduplicate equal diagnostic packets. -/
theorem repeated_rule_not_semidet (left right : Int) (origin : SExpr)
    (increasing : left < right) :
    (do let answers ← [scalarRow 0, scalarRow 0].mapM
          (fun row => ruleAnswers? row left right origin)
        pure answers.flatten : Option (List SExpr)) =
      some [.atom "BNFDiagnosticsNilV1", .atom "BNFDiagnosticsNilV1"] := by
  simp [first_rule_answers, increasing]

theorem equal_operands_diagnosed (value : Int) (origin : SExpr) :
    sourceAnswers? value value origin = some [.list [.atom "BNFDiagnosticsConsV1",
      .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom (toString value),
        .atom (toString value), origin], .atom "BNFDiagnosticsNilV1"]] := by
  simp [sourceAnswers_eq, diagnostic]

theorem negative_operands_accepted (origin : SExpr) :
    sourceAnswers? (-2) (-1) origin = some [.atom "BNFDiagnosticsNilV1"] := by
  simp [sourceAnswers_eq, diagnostic]

theorem invalid_unicode_still_ordered (origin : SExpr) :
    sourceAnswers? 1114112 1114113 origin = some [.atom "BNFDiagnosticsNilV1"] := by
  simp [sourceAnswers_eq, diagnostic]

theorem variable_looking_origin_preserved :
    sourceAnswers? 2 1 (.atom "?left") = some [.list [.atom "BNFDiagnosticsConsV1",
      .list [.atom "BNFNonIncreasingLexicalScalarsV1", .atom "2", .atom "1", .atom "?left"],
      .atom "BNFDiagnosticsNilV1"]] := by
  rw [sourceAnswers_eq]
  rfl

theorem malformed_integer_guard_refused :
    providerAnswers? (.list [.atom "ground-integer-less", .atom "word", .atom "1"]) = none := by
  have notNat : "word".isNat = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have character := (String.isNat_iff.mp accepted).2.1 'w' (by decide)
    simp [Char.isDigit] at character
  have refused : "word".toInt? = none := by
    rw [String.toInt?_eq_toNat?_of_startsWith_eq_false (by decide),
      String.toNat?_eq_none notNat]
    rfl
  have rejected : SourceIntegerProvider.integerValue? "word" = none := by
    simp [SourceIntegerProvider.integerValue?, refused]
  simp only [providerAnswers?, rejected]
  rfl

theorem noncanonical_integer_guard_refused :
    providerAnswers? (.list [.atom "ground-integer-less", .atom "01", .atom "2"]) = none := by
  have numeric : "01".isNat = true := String.isNat_iff.mpr (by decide)
  have parsed : "01".toNat? = some 1 := by
    rw [String.toNat?_eq_some_ofDigitChars numeric]
    rfl
  have integer : "01".toInt? = some (1 : Int) :=
    String.toInt?_eq_some_of_toNat?_eq_some parsed
  have spelling : toString (1 : Int) = "1" := by
    rw [Int.toString_eq_repr, Int.repr_eq_if]
    decide
  have rejected : SourceIntegerProvider.integerValue? "01" = none := by
    unfold SourceIntegerProvider.integerValue?
    rw [integer]
    change (if toString (1 : Int) = "01" then some (1 : Int) else none) = none
    rw [spelling]
    rfl
  simp only [providerAnswers?, rejected]
  rfl

#print axioms sourceAnswers_eq
#print axioms sourceAnswers_iff
#print axioms sourceAnswers_single_occurrence

end Mettapedia.GSLT.Parsing.PlainBnfScalarOrderSource
