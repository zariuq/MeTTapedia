import Mettapedia.OSLF.MeTTaIL.PatternCode
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-!
# Canonical matching compiled from reflective presentation data

`ReflectivePresentationDecl` already names the quote/drop equation, parallel
collection, and parallel unit of a reflective calculus.  This module compiles
that authored data into a canonical representative and uses it only for
repeated metavariable checks in the declaration's selected rewrite rule.

Languages and rules without a unique matching declaration continue to call
the original structural matcher directly.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- Splice a normalized occurrence of the declared parallel collection into
its parent parallel collection. -/
def parallelSplice (declaration : ReflectivePresentationDecl) : Pattern → List Pattern
  | pattern@(.collection collectionType elements none) =>
      if collectionType == declaration.parallelCollection then elements else [pattern]
  | pattern => [pattern]

/-- Normalize an already-recursively-normalized parallel element list. -/
def normalizeParallelElements
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) : List Pattern :=
  PatternCode.sortPatterns
    ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
      pattern ≠ .apply declaration.parallelUnitConstructor [])

/-- Rebuild the declared parallel composition without representation-only
empty and singleton wrappers. -/
def collapseParallel (declaration : ReflectivePresentationDecl) : List Pattern → Pattern
  | [] => .apply declaration.parallelUnitConstructor []
  | [pattern] => pattern
  | patterns => .collection declaration.parallelCollection patterns none

mutual
  /-- Canonical representative compiled solely from a reflective declaration.

  It recursively orients the declaration's quote/drop equation and presents
  its parallel collection as a flattened, unit-free, structurally sorted bag.
  No executable drop step is introduced. -/
  def canonicalize
      (declaration : ReflectivePresentationDecl) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        finishNormalizeReflectiveApply declaration constructor
          (canonicalizeList declaration arguments)
    | .lambda binderName body =>
        .lambda binderName (canonicalize declaration body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames (canonicalize declaration body)
    | .subst body replacement =>
        .subst (canonicalize declaration body) (canonicalize declaration replacement)
    | .collection collectionType elements none =>
        let normalizedElements := canonicalizeList declaration elements
        if collectionType == declaration.parallelCollection then
          collapseParallel declaration
            (normalizeParallelElements declaration normalizedElements)
        else
          .collection collectionType normalizedElements none
    | .collection collectionType elements rest =>
        .collection collectionType (canonicalizeList declaration elements) rest

  def canonicalizeList
      (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        canonicalize declaration pattern :: canonicalizeList declaration patterns
end

/-- Boolean equality of representatives compiled from one declaration. -/
def canonicalEquivalent
    (declaration : ReflectivePresentationDecl) (left right : Pattern) : Bool :=
  decide (canonicalize declaration left = canonicalize declaration right)

theorem canonicalEquivalent_eq_true_iff
    {declaration : ReflectivePresentationDecl} {left right : Pattern} :
    canonicalEquivalent declaration left right = true ↔
      canonicalize declaration left = canonicalize declaration right := by
  simp [canonicalEquivalent]

/-- Rule-aware matching compiled from the authored `LanguageDef`.

Only repeated metavariable consistency changes for the selected reflective
rule.  Constructor matching, binder handling, and collection search remain
the generic matcher. -/
def matchPatternForRule
    (lang : LanguageDef) (rule : RewriteRule) (term : Pattern) : List Bindings :=
  match declarationForRule? lang rule with
  | some declaration =>
      matchPatternWith (canonicalEquivalent declaration) rule.left term
  | none => matchPattern rule.left term

/-- Rule-aware matching is unchanged when two languages share the same
authored reflective presentations. -/
theorem matchPatternForRule_eq_of_presentations_eq
    {lang₁ lang₂ : LanguageDef}
    (same : lang₁.reflectivePresentations = lang₂.reflectivePresentations)
    (rule : RewriteRule) (term : Pattern) :
    matchPatternForRule lang₁ rule term = matchPatternForRule lang₂ rule term := by
  simp only [matchPatternForRule]
  rw [declarationForRule?_eq_of_presentations_eq same rule]

/-- Missing or ambiguous reflective data is definitionally backward
compatible with structural matching. -/
theorem matchPatternForRule_eq_syntactic_of_no_declaration
    {lang : LanguageDef} {rule : RewriteRule}
    (missing : declarationForRule? lang rule = none) (term : Pattern) :
    matchPatternForRule lang rule term = matchPattern rule.left term := by
  simp [matchPatternForRule, missing]

@[simp] theorem matchPatternForRule_eq_syntactic_of_no_presentations
    {lang : LanguageDef} (empty : lang.reflectivePresentations = [])
    (rule : RewriteRule) (term : Pattern) :
    matchPatternForRule lang rule term = matchPattern rule.left term := by
  apply matchPatternForRule_eq_syntactic_of_no_declaration
  exact declarationForRule?_eq_none_of_no_presentations empty rule

/-! ## Executable boundary examples -/

private def canonicalChannel : Pattern :=
  .apply "NQuote" [.apply "PZero" []]

private def unitExpandedChannel : Pattern :=
  .apply "NQuote"
    [.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none]

private def distinctChannel : Pattern :=
  .apply "NQuote"
    [.apply "POutput" [canonicalChannel, .apply "PZero" []]]

private def commCandidate (outputChannel : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "PInput" [unitExpandedChannel, .lambda none (.bvar 0)],
      .apply "POutput" [outputChannel, .apply "PZero" []]]
    none

-- The declaration-derived matcher admits two presentations of one channel.
#guard !(matchPatternForRule rhoCalc rhoCommRewrite
  (commCandidate canonicalChannel)).isEmpty

-- It still rejects a genuinely distinct channel.
#guard (matchPatternForRule rhoCalc rhoCommRewrite
  (commCandidate distinctChannel)).isEmpty

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
