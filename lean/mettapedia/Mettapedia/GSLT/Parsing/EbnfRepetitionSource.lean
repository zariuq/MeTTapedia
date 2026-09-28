import Mettapedia.GSLT.Parsing.SourceSExprPatternInstantiation
import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

/-!
# Source-selected EBNF repetition orientation

The two helper productions and the iteration accumulator are read from the
actual authored transformations. The local lowering equations are checked for
arbitrary body, name and span payloads. The accumulator executes the existing
Pattern matcher and substitution, not a second rule interpreter.

The order theorem concerns the selected accumulator with body projections
left as explicit calls. It does not prove the complete CST projector, freshness,
native parser completeness or generated-C correspondence. Nullable iteration
payloads and duplicate occurrences are not quotiented by these laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.EbnfRepetitionSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList instantiate? instantiateList? Env)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def loweringSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/ebnf_lowering_v1.metta"

def projectionSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/ebnf_derivation_projection_v1.metta"

/-! Selection retains the concrete source occurrence. It is not a search over
names, and it makes no admission claim about unselected source rules. -/
def equation? (authored : SExpr) (occurrence : Nat) : Option (SExpr × SExpr) := do
  let row ← Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt? authored occurrence
  match row.head, row.body with
  | .list [.atom "metta-equation", left, right], [] => some (left, right)
  | _, _ => none

def closeEquation? (authored : SExpr) (occurrence : Nat) (env : Env) :
    Option (SExpr × SExpr) := do
  let (left, right) ← equation? authored occurrence
  return (← instantiate? env left, ← instantiate? env right)

def app (head : String) (args : List SExpr) : SExpr := .list (.atom head :: args)

def elements : List SExpr → SExpr
  | [] => app "bnf-v1:elements-nil" []
  | head :: tail => app "bnf-v1:elements-cons" [head, elements tail]

def alternatives (span : SExpr) : List (List SExpr) → SExpr
  | [] => app "bnf-v1:alternatives-nil" []
  | head :: tail => app "bnf-v1:alternatives-cons"
      [app "bnf-v1:alternative" [elements head, span], alternatives span tail]

def helperExpression (span : SExpr) (bodies : List (List SExpr)) : SExpr :=
  app "bnf-v1:expression" [alternatives span bodies, span]

private theorem star_equation : equation? loweringSyntax 67 =
    some (app "ebnf-v1:unary-expression"
      [.atom "zero-or-more", .atom "?body", .atom "?name", .atom "?span"],
      helperExpression (.atom "?span") [[],
        [app "bnf-v1:reference" [.atom "?name", .atom "?span"], .atom "?body"]]) := rfl

private theorem plus_equation : equation? loweringSyntax 68 =
    some (app "ebnf-v1:unary-expression"
      [.atom "one-or-more", .atom "?body", .atom "?name", .atom "?span"],
      helperExpression (.atom "?span") [[.atom "?body"],
        [app "bnf-v1:reference" [.atom "?name", .atom "?span"], .atom "?body"]]) := rfl

/-- Independently stated emitted alternatives, checked against the source
equation for every payload. Recursion precedes the body; epsilon is retained. -/
theorem star_source_exact (body name span : SExpr) :
    closeEquation? loweringSyntax 67
      [("?body", body), ("?name", name), ("?span", span)] =
    some (app "ebnf-v1:unary-expression" [.atom "zero-or-more", body, name, span],
      helperExpression span [[], [app "bnf-v1:reference" [name, span], body]]) := by
  unfold closeEquation?
  rw [star_equation]
  simp [instantiate?, instantiateList?, app, helperExpression, alternatives, elements,
    SourceIntegerProvider.sourceVariableToken]

theorem plus_source_exact (body name span : SExpr) :
    closeEquation? loweringSyntax 68
      [("?body", body), ("?name", name), ("?span", span)] =
    some (app "ebnf-v1:unary-expression" [.atom "one-or-more", body, name, span],
      helperExpression span [[body], [app "bnf-v1:reference" [name, span], body]]) := by
  unfold closeEquation?
  rw [plus_equation]
  simp [instantiate?, instantiateList?, app, helperExpression, alternatives, elements,
    SourceIntegerProvider.sourceVariableToken]

def translatedEquation? (authored : SExpr) (occurrence : Nat) : Option RewriteRule := do
  let row ← Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt? authored occurrence
  let (left, right) ← equation? authored occurrence
  return { name := row.name, typeContext := [], premises := [], left := pattern left, right := pattern right }

def accumulatorRules? : Option (List RewriteRule) :=
  [53, 54].mapM
    (translatedEquation? projectionSyntax)

theorem accumulator_present : accumulatorRules?.isSome = true := rfl

def accumulator : LanguageDef :=
  { name := "EbnfSourceIterationAccumulator", types := [], terms := [], equations := [],
    rewrites := accumulatorRules?.get accumulator_present }

def iterations : List SExpr → SExpr
  | [] => app "EBNF:IterationsNil" []
  | head :: tail => app "EBNF:IterationsCons" [head, iterations tail]

def sourceOrder (body : SExpr) : SExpr := app "ebnf-v1:source-order" [body]

def orderCall (reverse tail : List SExpr) : SExpr :=
  app "ebnf-v1:iterations-source-order" [iterations reverse, iterations tail]

private theorem repeat_equation : equation? projectionSyntax 42 =
    some (app "ebnf-v1:repeat-step"
      [.atom "LangDef:SameValue", .atom "LangDef:SameValue", .atom "?kind",
        .atom "?occurrence", .atom "?span", .atom "?input", .atom "?body", .atom "?tail"],
      app "ebnf-v1:repetition-reversed"
        [.atom "?kind", .atom "?occurrence", .atom "?span", .atom "?input",
          app "EBNF:IterationsCons" [.atom "?body", .atom "?tail"]]) := rfl

/-- The concrete source rule really performs the cons update used by the
spine law. Occurrence, source span and whole input extent remain opaque. -/
theorem repeat_step_source_exact (kind occurrence span input body tail : SExpr) :
    closeEquation? projectionSyntax 42
      [("?kind", kind), ("?occurrence", occurrence), ("?span", span),
        ("?input", input), ("?body", body), ("?tail", tail)] =
    some (app "ebnf-v1:repeat-step"
      [.atom "LangDef:SameValue", .atom "LangDef:SameValue", kind, occurrence,
        span, input, body, tail],
      app "ebnf-v1:repetition-reversed" [kind, occurrence, span, input,
        app "EBNF:IterationsCons" [body, tail]]) := by
  unfold closeEquation?
  rw [repeat_equation]
  simp [instantiate?, instantiateList?, app, SourceIntegerProvider.sourceVariableToken]

private def observedRules : List RewriteRule := [
  { name := "iterations-source-order-empty", typeContext := [], premises := [],
    left := pattern (app "ebnf-v1:iterations-source-order"
      [iterations [], .atom "?tail"]), right := pattern (.atom "?tail") },
  { name := "iterations-source-order-cons", typeContext := [], premises := [],
    left := pattern (app "ebnf-v1:iterations-source-order"
      [app "EBNF:IterationsCons" [.atom "?head", .atom "?rest"], .atom "?tail"]),
    right := pattern (app "ebnf-v1:iterations-source-order"
      [.atom "?rest", app "EBNF:IterationsCons" [sourceOrder (.atom "?head"), .atom "?tail"]]) }]

/-- The operational rules come from the file, not this displayed observation. -/
private theorem accumulator_rules_exact : accumulator.rewrites = observedRules := rfl

theorem accumulator_empty (tail : List SExpr) :
    rewriteStep accumulator (encode (orderCall [] tail)) = [encode (iterations tail)] := by
  simp [rewriteStep, accumulator_rules_exact, observedRules, applyRule, applyRuleBindings, orderCall,
    iterations, app, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, applyBindings]

theorem accumulator_cons (head : SExpr) (rest tail : List SExpr) :
    rewriteStep accumulator (encode (orderCall (head :: rest) tail)) =
      [encode (orderCall rest (sourceOrder head :: tail))] := by
  simp [rewriteStep, accumulator_rules_exact, observedRules, applyRule, applyRuleBindings, orderCall,
    iterations, sourceOrder, app, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, applyBindings]

abbrev Step (before after : Pattern) : Prop := after ∈ rewriteStep accumulator before

/-- A selected all-input source path. The final list is stated by ordinary
reverse/map/append, independently of the executed rules. -/
theorem accumulator_path (reverse tail : List SExpr) :
    Relation.ReflTransGen Step (encode (orderCall reverse tail))
      (encode (iterations (reverse.reverse.map sourceOrder ++ tail))) := by
  induction reverse generalizing tail with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [Step, accumulator_empty]
  | cons head rest ih =>
      have step : Step (encode (orderCall (head :: rest) tail))
          (encode (orderCall rest (sourceOrder head :: tail))) := by
        simp [Step, accumulator_cons]
      simpa using (Relation.ReflTransGen.single step).trans (ih (sourceOrder head :: tail))

/-- A proof-level view of the actual left-recursive helper spine. The payload
can contain source/input spans and the complete body derivation; it is never
identified with another payload merely because both consume the same bytes. -/
inductive PrefixSpine (α : Type) where
  | empty
  | extend (prior : PrefixSpine α) (body : α)
  deriving Repr, DecidableEq

namespace PrefixSpine

variable {α : Type}

/-- Independent ordered denotation of a left-recursive spine. -/
def ordered : PrefixSpine α → List α
  | .empty => []
  | .extend prior body => ordered prior ++ [body]

/-- The cons accumulator used by the authored repeat-step rule. -/
def reversed : PrefixSpine α → List α
  | .empty => []
  | .extend prior body => body :: reversed prior

theorem restore_order (spine : PrefixSpine α) : spine.reversed.reverse = spine.ordered := by
  induction spine with
  | empty => rfl
  | extend prior body ih => simp [reversed, ordered, ih]

def fromReversed : List α → PrefixSpine α
  | [] => .empty
  | head :: tail => .extend (fromReversed tail) head

@[simp] theorem fromReversed_reversed (spine : PrefixSpine α) :
    fromReversed spine.reversed = spine := by
  induction spine <;> simp_all [fromReversed, reversed]

@[simp] theorem reversed_fromReversed (items : List α) :
    (fromReversed items).reversed = items := by
  induction items <;> simp_all [fromReversed, reversed]

theorem ordered_injective : Function.Injective (@ordered α) := by
  intro first second equal
  have reversedEqual := congrArg List.reverse equal
  rw [← restore_order first, ← restore_order second] at reversedEqual
  simpa using congrArg fromReversed reversedEqual

/-- No nullable or duplicate body is removed by changing the fold direction. -/
theorem restores_duplicate (body : α) :
    (PrefixSpine.extend (.extend .empty body) body).reversed.reverse = [body, body] := rfl

end PrefixSpine

theorem source_accumulator_preserves_spine (spine : PrefixSpine SExpr) :
    Relation.ReflTransGen Step (encode (orderCall spine.reversed []))
      (encode (iterations (spine.ordered.map sourceOrder))) := by
  simpa [PrefixSpine.restore_order] using accumulator_path spine.reversed []

/-- Forgetting the final reversal is observably wrong even without ambiguity. -/
theorem uncorrected_order_changes_result :
    (PrefixSpine.extend (.extend .empty (0 : Nat)) 1).reversed ≠ [0, 1] := by decide

#print axioms star_source_exact
#print axioms plus_source_exact
#print axioms repeat_step_source_exact
#print axioms accumulator_empty
#print axioms accumulator_cons
#print axioms accumulator_path
#print axioms PrefixSpine.ordered_injective
#print axioms source_accumulator_preserves_spine

end Mettapedia.GSLT.Parsing.EbnfRepetitionSource
