import Mettapedia.GraphTheory.Representation.EdgeListToMatrixGSLT
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Rewrite-bearing LanguageDef for edge-list materialization

This is the operational graph `LanguageDef` missing from the earlier paper.
It does not name an opaque `convert` operation.  Its `Write` rule consumes one
authored edge occurrence and adds one persistent symmetric-update constructor;
its `Finish` rule exposes the completed matrix expression.  The generic
`LanguageDef` executor therefore determines the construction trace.

An independent typed interpretation maps persistent matrix expressions to the
existing lawful adjacency-matrix carrier.  The commuting theorem below shows
that every typed source step is both an actual `LanguageDef` reduction and the
corresponding step of the detailed matrix materializer.

`MatrixSetSymmetric` is still an algebraic update constructor, not a claim
about mutable row-major memory.  Refining it into physical cell writes is a
separate lower-level obligation.
-/

namespace Mettapedia.GraphTheory.Representation.EdgeListToMatrixLanguageDef

open Mettapedia.GraphTheory.Representation
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

def types : List TypeDecl :=
  ["Vertex", "Edge", "Edges", "Matrix", "State"].map TypeDecl.plain

def parameter (name typeName : String) : TermParam :=
  .simple name (.base typeName)

def constructor (label category : String) (params : List TermParam) :
    GrammarRule :=
  GrammarRule.mk label category params [] none none

/-- Sorted constructors are the syntax consumed by the generic executor.
There is deliberately no opaque route or conversion constructor. -/
def terms : List GrammarRule :=
  [ constructor "VertexZero" "Vertex" []
  , constructor "VertexSucc" "Vertex" [parameter "vertex" "Vertex"]
  , constructor "EdgeValue" "Edge"
      [parameter "source" "Vertex", parameter "target" "Vertex"]
  , constructor "EdgesNil" "Edges" []
  , constructor "EdgesCons" "Edges"
      [parameter "edge" "Edge", parameter "rest" "Edges"]
  , constructor "MatrixEmpty" "Matrix" []
  , constructor "MatrixSetSymmetric" "Matrix"
      [parameter "matrix" "Matrix", parameter "source" "Vertex",
        parameter "target" "Vertex"]
  , constructor "Active" "State"
      [parameter "remaining" "Edges", parameter "matrix" "Matrix"]
  , constructor "Done" "State" [parameter "matrix" "Matrix"]
  ]

def writeRule : RewriteRule :=
  RewriteRule.mk "Write" [] []
    (.apply "Active"
      [.apply "EdgesCons"
        [.apply "EdgeValue" [.fvar "Source", .fvar "Target"], .fvar "Rest"],
       .fvar "Matrix"])
    (.apply "Active"
      [.fvar "Rest",
       .apply "MatrixSetSymmetric"
        [.fvar "Matrix", .fvar "Source", .fvar "Target"]])

def finishRule : RewriteRule :=
  RewriteRule.mk "Finish" [] []
    (.apply "Active" [.apply "EdgesNil" [], .fvar "Matrix"])
    (.apply "Done" [.fvar "Matrix"])

/-- The complete authored syntax and operational rules for persistent
edge-list-to-matrix construction. -/
def language : LanguageDef :=
  LanguageDef.ofCore "EdgeListToMatrix" types terms []
    [writeRule, finishRule]

theorem language_rewrites : language.rewrites = [writeRule, finishRule] := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem rewrites_validate :
    ∀ rule ∈ language.rewrites,
      LanguageDef.validateRewrite language rule = [] := by
  intro rule membership
  rw [language_rewrites] at membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  all_goals
    simp +decide [LanguageDef.validateRewrite, language, types, terms,
      constructor, parameter, writeRule, finishRule,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      LanguageDef.typeNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem language_validates : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  exact rewrites_validate

/-! ## Typed algebraic construction and independent denotation -/

/-- Persistent matrix-building expressions.  Every `setSymmetric` node records
one source occurrence explicitly. -/
inductive MatrixExpr (n : Nat) where
  | empty
  | setSymmetric (previous : MatrixExpr n) (edge : EdgeList.Edge n)
deriving DecidableEq, Repr

namespace MatrixExpr

/-- Interpret the algebraic update tree as the existing lawful matrix value. -/
def denote {n : Nat} : MatrixExpr n → AdjacencyMatrix.Rep n
  | .empty => AdjacencyMatrix.empty n
  | .setSymmetric previous edge =>
      EdgeListToMatrixGSLT.insertOccurrence previous.denote edge

end MatrixExpr

/-- Typed states corresponding to the two declared `State` constructors. -/
inductive State (n : Nat) where
  | active (remaining : List (EdgeList.Edge n)) (matrix : MatrixExpr n)
  | done (matrix : MatrixExpr n)
deriving DecidableEq, Repr

/-- Executable typed presentation of the two authored rules. -/
def step? {n : Nat} : State n → Option (State n)
  | .active (edge :: rest) matrix =>
      some (.active rest (.setSymmetric matrix edge))
  | .active [] matrix => some (.done matrix)
  | .done _ => none

/-- Interpret a typed algebraic state as a state of the independently defined
detailed materializer. -/
def State.denote {n : Nat} : State n → EdgeListToMatrixGSLT.State n
  | .active remaining matrix => .active remaining matrix.denote
  | .done matrix => .done matrix.denote

/-- The typed executable step commutes exactly with the detailed materializer,
including the concrete symmetric matrix update. -/
theorem step?_denote {n : Nat} {source target : State n}
    (step : step? source = some target) :
    EdgeListToMatrixGSLT.step? source.denote = some target.denote := by
  cases source with
  | active remaining matrix =>
      cases remaining with
      | nil =>
          simp only [step?, Option.some.injEq] at step
          subst target
          rfl
      | cons edge rest =>
          simp only [step?, Option.some.injEq] at step
          subst target
          rfl
  | done matrix =>
      simp only [step?, reduceCtorEq] at step

/-! ## Canonical encoding into the LanguageDef -/

def vertexPattern : Nat → Pattern
  | 0 => .apply "VertexZero" []
  | vertex + 1 => .apply "VertexSucc" [vertexPattern vertex]

def finPattern {n : Nat} (vertex : Fin n) : Pattern :=
  vertexPattern vertex.val

def edgePattern {n : Nat} (edge : EdgeList.Edge n) : Pattern :=
  .apply "EdgeValue" [finPattern edge.source, finPattern edge.target]

def edgesPattern {n : Nat} : List (EdgeList.Edge n) → Pattern
  | [] => .apply "EdgesNil" []
  | edge :: rest => .apply "EdgesCons" [edgePattern edge, edgesPattern rest]

def matrixPattern {n : Nat} : MatrixExpr n → Pattern
  | .empty => .apply "MatrixEmpty" []
  | .setSymmetric previous edge =>
      .apply "MatrixSetSymmetric"
        [matrixPattern previous, finPattern edge.source, finPattern edge.target]

def statePattern {n : Nat} : State n → Pattern
  | .active remaining matrix =>
      .apply "Active" [edgesPattern remaining, matrixPattern matrix]
  | .done matrix => .apply "Done" [matrixPattern matrix]

/-- One root-level execution of the actual authored rewrite table. -/
def rewriteOnce (source : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) language 1 source

/-- The generic LanguageDef engine executes the `Write` rule exactly: one
canonical source state has one canonical successor. -/
theorem rewriteOnce_active_cons {n : Nat} (edge : EdgeList.Edge n)
    (rest : List (EdgeList.Edge n)) (matrix : MatrixExpr n) :
    rewriteOnce (statePattern (.active (edge :: rest) matrix)) =
      [statePattern (.active rest (.setSymmetric matrix edge))] := by
  simp [rewriteOnce, rewriteAt, language_rewrites, writeRule, finishRule,
    statePattern, edgesPattern, edgePattern, matrixPattern, applyRuleUsing,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, premisesUsing,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
    Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

/-- The generic LanguageDef engine executes finalization exactly. -/
theorem rewriteOnce_active_nil {n : Nat} (matrix : MatrixExpr n) :
    rewriteOnce (statePattern (.active [] matrix)) =
      [statePattern (.done matrix)] := by
  simp [rewriteOnce, rewriteAt, language_rewrites, writeRule, finishRule,
    statePattern, edgesPattern, applyRuleUsing,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, premisesUsing,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
    Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

/-- Negative control: the declared terminal constructor has no successor. -/
theorem rewriteOnce_done {n : Nat} (matrix : MatrixExpr n) :
    rewriteOnce (statePattern (.done matrix)) = [] := by
  simp [rewriteOnce, rewriteAt, language_rewrites, writeRule, finishRule,
    statePattern, applyRuleUsing, matchPatternForRule,
    matchPatternForRuleUsing,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern]

/-- The executable typed action and the generic LanguageDef executor agree on
every canonical state.  This is an exact result-list equality, not merely a
shared positive example. -/
theorem rewriteOnce_state {n : Nat} (source : State n) :
    rewriteOnce (statePattern source) =
      (step? source).toList.map statePattern := by
  cases source with
  | active remaining matrix =>
      cases remaining with
      | nil => exact rewriteOnce_active_nil matrix
      | cons edge rest => exact rewriteOnce_active_cons edge rest matrix
  | done matrix => exact rewriteOnce_done matrix

/-- Every successful typed step is a reduction generated by the authored
LanguageDef itself. -/
theorem language_reduces_of_step? {n : Nat} {source target : State n}
    (step : step? source = some target) :
    langReduces language (statePattern source) (statePattern target) := by
  apply (langReducesUsing_iff_execUsing RelationEnv.empty language _ _).2
  refine ⟨1, ?_⟩
  change statePattern target ∈ rewriteOnce (statePattern source)
  rw [rewriteOnce_state source, step]
  simp

/-- Source-language execution and concrete matrix execution form a commuting
square for every typed step. -/
theorem language_step_semantic_square {n : Nat} {source target : State n}
    (step : step? source = some target) :
    langReduces language (statePattern source) (statePattern target) ∧
      EdgeListToMatrixGSLT.step? source.denote = some target.denote :=
  ⟨language_reduces_of_step? step, step?_denote step⟩

/-! ## Complete construction -/

def buildExpr {n : Nat} :
    MatrixExpr n → List (EdgeList.Edge n) → MatrixExpr n
  | matrix, [] => matrix
  | matrix, edge :: rest => buildExpr (.setSymmetric matrix edge) rest

theorem buildExpr_denote {n : Nat} (matrix : MatrixExpr n)
    (remaining : List (EdgeList.Edge n)) :
    (buildExpr matrix remaining).denote =
      EdgeListToMatrixGSLT.buildFrom matrix.denote remaining := by
  induction remaining generalizing matrix with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      exact inductionHypothesis (.setSymmetric matrix edge)

/-- Symbolic execution reaches a matrix expression whose independent
denotation is exactly the extensional edge-list-to-matrix refinement. -/
theorem complete_denotes_refinement {n : Nat} (graph : EdgeList.Rep n) :
    (buildExpr .empty graph.entries).denote =
      Transformations.toMatrix (EdgeList.presentation n) graph := by
  rw [buildExpr_denote]
  exact EdgeListToMatrixGSLT.materialize_eq_refinement graph

namespace Canary

open EdgeList.Canary

def initialPath3 : State 3 := .active path3.entries .empty

/-- Positive control: the real LanguageDef consumes the first authored path
edge and records its endpoints in the persistent matrix expression. -/
theorem path3_first_language_rewrite :
    rewriteOnce (statePattern initialPath3) =
      [statePattern (.active [⟨v1, v2⟩]
        (.setSymmetric .empty ⟨v0, v1⟩))] := by
  simpa [initialPath3, path3] using
    (rewriteOnce_active_cons (n := 3) (EdgeList.Edge.mk v0 v1)
      [EdgeList.Edge.mk v1 v2] MatrixExpr.empty)

/-- Negative control: a completed path matrix cannot be rewritten again. -/
theorem path3_done_is_stuck :
    rewriteOnce (statePattern
      (.done (buildExpr .empty path3.entries))) = [] := by
  exact rewriteOnce_done _

/-- Semantic endpoint canary: the generated expression contains `0--1` but
does not invent `0--2`. -/
theorem path3_endpoint_positive_and_negative :
    (buildExpr .empty path3.entries).denote.cell v0 v1 = true ∧
      (buildExpr .empty path3.entries).denote.cell v0 v2 = false := by
  decide

end Canary

#print axioms language_validates
#print axioms step?_denote
#print axioms rewriteOnce_state
#print axioms language_reduces_of_step?
#print axioms language_step_semantic_square
#print axioms complete_denotes_refinement
#print axioms Canary.path3_first_language_rewrite
#print axioms Canary.path3_done_is_stuck
#print axioms Canary.path3_endpoint_positive_and_negative

end Mettapedia.GraphTheory.Representation.EdgeListToMatrixLanguageDef
