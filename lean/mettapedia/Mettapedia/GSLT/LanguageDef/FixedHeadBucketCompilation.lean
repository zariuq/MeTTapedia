import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.RigidCoordinateIndexCompilation

/-!
# Fixed outer-head bucket compilation

A relation-and-arity index proves the outer constructor of every selected rule
head before matching begins.  The inner matcher may therefore consume only
the argument payload.  This module makes that staged fact explicit: admission
checks equality of an outer key, compilation erases the duplicated head, and
the realization theorem recovers the complete rigid-compatibility result.
-/

namespace Mettapedia.GSLT.LanguageDef.FixedHeadBucketCompilation

open Mettapedia.GSLT.Parsing.HornCertificate
open Mettapedia.GSLT.LanguageDef.RigidHeadPrefilter
open Mettapedia.GSLT.LanguageDef.RigidCoordinateIndexCompilation

/-- Relation identity and immediate arity carried by an outer dispatch
bucket. -/
structure OuterKey where
  relation : String
  arity : Nat
  deriving DecidableEq, Repr

/-- Recover the generated outer-bucket key from a first-order atom. -/
def outerKey (atom : Atom) : OuterKey :=
  { relation := atom.relation
    arity := termsLength atom.arguments }

/-- Rigid argument compatibility is false when immediate arities differ. -/
theorem compatibleTerms_eq_false_of_length_ne
    (left right : Terms)
    (different : termsLength left ≠ termsLength right) :
    compatibleTerms left right = false := by
  cases compatibleEq : compatibleTerms left right with
  | false => rfl
  | true =>
      exfalso
      exact different <| termsLength_eq_of_compatible
        left right compatibleEq

/-- An outer-key mismatch is already a complete rigid rejection. -/
theorem compatibleAtom_eq_false_of_outerKey_ne
    (left right : Atom)
    (different : outerKey left ≠ outerKey right) :
    compatibleAtom left right = false := by
  by_cases relationEq : left.relation = right.relation
  · have lengthNe :
        termsLength left.arguments ≠ termsLength right.arguments := by
      intro lengthEq
      apply different
      cases left
      cases right
      simp_all [outerKey]
    have argumentsFalse := compatibleTerms_eq_false_of_length_ne
      left.arguments right.arguments lengthNe
    simp [compatibleAtom, relationEq, argumentsFalse]
  · simp [compatibleAtom, relationEq]

/-- Source comparison admitted by the preceding relation-and-arity index. -/
structure BucketedComparison where
  source : Atom
  query : Atom
  sameBucket : outerKey source = outerKey query

/-- Decidable local admission at the stage boundary. -/
def admit? (source query : Atom) : Option BucketedComparison :=
  if same : outerKey source = outerKey query then
    some { source, query, sameBucket := same }
  else
    none

/-- Admission succeeds exactly for a shared generated outer bucket. -/
theorem admit?_isSome_iff (source query : Atom) :
    (admit? source query).isSome = true ↔
      outerKey source = outerKey query := by
  simp [admit?]

/-- Compact payload left after the fixed outer head is stored out of band. -/
structure ArgumentComparisonPlan where
  sourceArguments : Terms
  queryArguments : Terms
  deriving DecidableEq, Repr

/-- Erase the duplicated outer relation and arity from one admitted match. -/
def compile (comparison : BucketedComparison) : ArgumentComparisonPlan :=
  { sourceArguments := comparison.source.arguments
    queryArguments := comparison.query.arguments }

/-- Execute only the residual rigid argument comparison. -/
def execute (plan : ArgumentComparisonPlan) : Bool :=
  compatibleTerms plan.sourceArguments plan.queryArguments

/-- Once the outer bucket is certified, comparing only argument payloads is
exactly the complete rigid-head prefilter. -/
theorem execute_compile_eq_compatibleAtom
    (comparison : BucketedComparison) :
    execute (compile comparison) =
      compatibleAtom comparison.source comparison.query := by
  have relationEq :
      comparison.source.relation = comparison.query.relation :=
    congrArg OuterKey.relation comparison.sameBucket
  simp [execute, compile, compatibleAtom, relationEq]

/-- Fixed-head elimination as a composable certified realization. -/
def fixedHeadBucketRealization :
    Mettapedia.GSLT.SimpleRealization
      BucketedComparison ArgumentComparisonPlan Bool where
  compile := fun _ comparison => compile comparison
  observeSource := fun _ comparison =>
    compatibleAtom comparison.source comparison.query
  observeArtifact := fun _ plan => execute plan
  adequate := by
    intro _ comparison
    exact execute_compile_eq_compatibleAtom comparison

/-! ## Independent positive and negative canaries -/

private def clauseHead : Atom := {
  relation := "literal"
  arguments := .ofList [
    .app "positive" (.ofList [.var 0]), .atom "selected"] }

private def clauseQuery : Atom := {
  relation := "literal"
  arguments := .ofList [
    .app "positive" (.ofList [.atom "p"]), .atom "selected"] }

private def evaluatorHead : Atom := {
  relation := "evaluate"
  arguments := .ofList [.var 0, .var 1, .var 2] }

private def evaluatorQuery : Atom := {
  relation := "evaluate"
  arguments := .ofList [
    .app "call" (.ofList [.atom "f"]), .atom "space", .atom "result"] }

/-- A first-order literal comparison erases its already-dispatched head. -/
example :
    (admit? clauseHead clauseQuery).map (execute ∘ compile) = some true := by
  decide

/-- A differently shaped evaluator relation independently uses the same
head-elision realization. -/
example :
    (admit? evaluatorHead evaluatorQuery).map (execute ∘ compile) =
      some true := by
  decide

/-- Wrong arity fails admission instead of reaching the argument matcher. -/
example :
    (admit? evaluatorHead {
      relation := "evaluate"
      arguments := .ofList [.atom "subject", .atom "result"] }).isSome =
        false := by
  decide

/-- Wrong relation identity is rejected even when arity happens to agree. -/
example :
    compatibleAtom evaluatorHead {
      relation := "reduce"
      arguments := evaluatorQuery.arguments } = false := by
  decide

end Mettapedia.GSLT.LanguageDef.FixedHeadBucketCompilation
