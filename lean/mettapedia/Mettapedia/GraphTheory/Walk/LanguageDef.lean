import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GraphTheory.Basic
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

/-!
# Operational LanguageDef for finite-graph walks

This module gives three ordinary operations on graph walks an explicit
small-step semantics:

* appending endpoint-compatible walks;
* reversing a walk by scanning its edges into an accumulator;
* mapping a walk along a graph homomorphism, one vertex and edge at a time.

The authored rewrite rows perform the recursion.  External relations expose
only the mathematical data that an operation is allowed to consult:
adjacency in the source and target graphs, and the vertex action of the
selected graph homomorphism.  No relation computes a complete walk operation.

Walk values repeat their endpoints at every recursive node.  Consequently
the rewrite patterns make endpoint compatibility load-bearing instead of
leaving it to an informal convention.  Adjacency premises separately prevent
malformed non-edges from advancing through the machine.
-/

namespace Mettapedia.GraphTheory.Walk.LanguageDef

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

/-! ## Authored syntax -/

def types : List TypeDecl :=
  ["Vertex", "WalkNode", "Walk", "Frames", "State"].map TypeDecl.plain

def parameter (name typeName : String) : TermParam :=
  .simple name (.base typeName)

def constructor (label category : String) (params : List TermParam) :
    GrammarRule :=
  GrammarRule.mk label category params [] none none

/-- The complete sorted constructor inventory.  `WalkValue` records the
endpoints of its recursive node, while `FramesCons` stores one reversed edge
of a continuation. -/
def terms : List GrammarRule :=
  [ constructor "VertexZero" "Vertex" []
  , constructor "VertexSucc" "Vertex" [parameter "vertex" "Vertex"]
  , constructor "WalkNil" "WalkNode" [parameter "vertex" "Vertex"]
  , constructor "WalkCons" "WalkNode"
      [parameter "source" "Vertex", parameter "next" "Vertex",
        parameter "target" "Vertex", parameter "tail" "Walk"]
  , constructor "WalkValue" "Walk"
      [parameter "source" "Vertex", parameter "target" "Vertex",
        parameter "node" "WalkNode"]
  , constructor "FramesNil" "Frames" [parameter "origin" "Vertex"]
  , constructor "FramesCons" "Frames"
      [parameter "current" "Vertex", parameter "previous" "Vertex",
        parameter "rest" "Frames"]
  , constructor "AppendRequest" "State"
      [parameter "left" "Walk", parameter "right" "Walk"]
  , constructor "AppendScan" "State"
      [parameter "current" "Vertex", parameter "middle" "Vertex",
        parameter "target" "Vertex", parameter "leftNode" "WalkNode",
        parameter "right" "Walk", parameter "frames" "Frames"]
  , constructor "AppendRebuild" "State"
      [parameter "current" "Vertex", parameter "target" "Vertex",
        parameter "frames" "Frames", parameter "result" "Walk"]
  , constructor "ReverseRequest" "State" [parameter "walk" "Walk"]
  , constructor "ReverseScan" "State"
      [parameter "current" "Vertex", parameter "target" "Vertex",
        parameter "origin" "Vertex", parameter "node" "WalkNode",
        parameter "accumulator" "Walk"]
  , constructor "MapRequest" "State" [parameter "walk" "Walk"]
  , constructor "MapScan" "State"
      [parameter "sourceCurrent" "Vertex", parameter "sourceTarget" "Vertex",
        parameter "mappedOrigin" "Vertex", parameter "mappedCurrent" "Vertex",
        parameter "node" "WalkNode", parameter "frames" "Frames"]
  , constructor "MapRebuild" "State"
      [parameter "current" "Vertex", parameter "target" "Vertex",
        parameter "frames" "Frames", parameter "result" "Walk"]
  , constructor "WalkDone" "State" [parameter "walk" "Walk"]
  ]

private def vertexContext (names : List String) : List (String × TypeExpr) :=
  names.map (fun name => (name, .base "Vertex"))

private def context
    (vertices : List String) (others : List (String × String)) :
    List (String × TypeExpr) :=
  vertexContext vertices ++ others.map (fun item => (item.1, .base item.2))

def sourceAdjacent (source target : String) : Premise :=
  .relationQuery "SourceAdjacent" [.fvar source, .fvar target]

def targetAdjacent (source target : String) : Premise :=
  .relationQuery "TargetAdjacent" [.fvar source, .fvar target]

def mapVertex (source target : String) : Premise :=
  .relationQuery "MapVertex" [.fvar source, .fvar target]

/-- Endpoint-compatible walks enter the append scanner with an empty
continuation.  Repeated metavariables enforce equality of the middle vertex. -/
def appendStartRule : RewriteRule :=
  RewriteRule.mk "AppendStart"
    (context ["Start", "Middle", "Target"]
      [("Left", "WalkNode"), ("Right", "WalkNode")]) []
    (.apply "AppendRequest"
      [.apply "WalkValue" [.fvar "Start", .fvar "Middle", .fvar "Left"],
       .apply "WalkValue" [.fvar "Middle", .fvar "Target", .fvar "Right"]])
    (.apply "AppendScan"
      [.fvar "Start", .fvar "Middle", .fvar "Target", .fvar "Left",
       .apply "WalkValue" [.fvar "Middle", .fvar "Target", .fvar "Right"],
       .apply "FramesNil" [.fvar "Start"]])

/-- Consume one edge of the left walk and push its reverse into the
continuation.  The adjacency premise is part of the executable rule. -/
def appendScanConsRule : RewriteRule :=
  RewriteRule.mk "AppendScanCons"
    (context ["Current", "Next", "Middle", "Target"]
      [("Tail", "WalkNode"), ("Right", "Walk"), ("Frames", "Frames")])
    [sourceAdjacent "Current" "Next"]
    (.apply "AppendScan"
      [.fvar "Current", .fvar "Middle", .fvar "Target",
       .apply "WalkCons"
        [.fvar "Current", .fvar "Next", .fvar "Middle",
         .apply "WalkValue" [.fvar "Next", .fvar "Middle", .fvar "Tail"]],
       .fvar "Right", .fvar "Frames"])
    (.apply "AppendScan"
      [.fvar "Next", .fvar "Middle", .fvar "Target", .fvar "Tail",
       .fvar "Right",
       .apply "FramesCons"
        [.fvar "Next", .fvar "Current", .fvar "Frames"]])

/-- A nil node is accepted only when its two recorded endpoints coincide. -/
def appendScanNilRule : RewriteRule :=
  RewriteRule.mk "AppendScanNil"
    (context ["Middle", "Target"]
      [("Right", "WalkNode"), ("Frames", "Frames")]) []
    (.apply "AppendScan"
      [.fvar "Middle", .fvar "Middle", .fvar "Target",
       .apply "WalkNil" [.fvar "Middle"],
       .apply "WalkValue" [.fvar "Middle", .fvar "Target", .fvar "Right"],
       .fvar "Frames"])
    (.apply "AppendRebuild"
      [.fvar "Middle", .fvar "Target", .fvar "Frames",
       .apply "WalkValue" [.fvar "Middle", .fvar "Target", .fvar "Right"]])

/-- Pop one reversed source edge and prepend its symmetric edge to the
result. -/
def appendRebuildConsRule : RewriteRule :=
  RewriteRule.mk "AppendRebuildCons"
    (context ["Current", "Previous", "Target"]
      [("Rest", "Frames"), ("Result", "WalkNode")])
    [sourceAdjacent "Previous" "Current"]
    (.apply "AppendRebuild"
      [.fvar "Current", .fvar "Target",
       .apply "FramesCons"
        [.fvar "Current", .fvar "Previous", .fvar "Rest"],
       .apply "WalkValue"
        [.fvar "Current", .fvar "Target", .fvar "Result"]])
    (.apply "AppendRebuild"
      [.fvar "Previous", .fvar "Target", .fvar "Rest",
       .apply "WalkValue"
        [.fvar "Previous", .fvar "Target",
         .apply "WalkCons"
          [.fvar "Previous", .fvar "Current", .fvar "Target",
           .apply "WalkValue"
            [.fvar "Current", .fvar "Target", .fvar "Result"]]]])

def appendRebuildNilRule : RewriteRule :=
  RewriteRule.mk "AppendRebuildNil"
    (context ["Start", "Target"] [("Result", "WalkNode")]) []
    (.apply "AppendRebuild"
      [.fvar "Start", .fvar "Target", .apply "FramesNil" [.fvar "Start"],
       .apply "WalkValue" [.fvar "Start", .fvar "Target", .fvar "Result"]])
    (.apply "WalkDone"
      [.apply "WalkValue" [.fvar "Start", .fvar "Target", .fvar "Result"]])

def reverseStartRule : RewriteRule :=
  RewriteRule.mk "ReverseStart"
    (context ["Start", "Target"] [("Node", "WalkNode")]) []
    (.apply "ReverseRequest"
      [.apply "WalkValue" [.fvar "Start", .fvar "Target", .fvar "Node"]])
    (.apply "ReverseScan"
      [.fvar "Start", .fvar "Target", .fvar "Start", .fvar "Node",
       .apply "WalkValue"
        [.fvar "Start", .fvar "Start", .apply "WalkNil" [.fvar "Start"]]])

/-- Reverse one edge by using symmetry of the source graph explicitly. -/
def reverseScanConsRule : RewriteRule :=
  RewriteRule.mk "ReverseScanCons"
    (context ["Current", "Next", "Target", "Origin"]
      [("Tail", "WalkNode"), ("Accumulator", "WalkNode")])
    [sourceAdjacent "Next" "Current"]
    (.apply "ReverseScan"
      [.fvar "Current", .fvar "Target", .fvar "Origin",
       .apply "WalkCons"
        [.fvar "Current", .fvar "Next", .fvar "Target",
         .apply "WalkValue" [.fvar "Next", .fvar "Target", .fvar "Tail"]],
       .apply "WalkValue"
        [.fvar "Current", .fvar "Origin", .fvar "Accumulator"]])
    (.apply "ReverseScan"
      [.fvar "Next", .fvar "Target", .fvar "Origin", .fvar "Tail",
       .apply "WalkValue"
        [.fvar "Next", .fvar "Origin",
         .apply "WalkCons"
          [.fvar "Next", .fvar "Current", .fvar "Origin",
           .apply "WalkValue"
            [.fvar "Current", .fvar "Origin", .fvar "Accumulator"]]]])

def reverseScanNilRule : RewriteRule :=
  RewriteRule.mk "ReverseScanNil"
    (context ["Target", "Origin"] [("Accumulator", "WalkNode")]) []
    (.apply "ReverseScan"
      [.fvar "Target", .fvar "Target", .fvar "Origin",
       .apply "WalkNil" [.fvar "Target"],
       .apply "WalkValue"
        [.fvar "Target", .fvar "Origin", .fvar "Accumulator"]])
    (.apply "WalkDone"
      [.apply "WalkValue"
        [.fvar "Target", .fvar "Origin", .fvar "Accumulator"]])

/-- Mapping begins by obtaining the image of the initial vertex. -/
def mapStartRule : RewriteRule :=
  RewriteRule.mk "MapStart"
    (context ["SourceStart", "SourceTarget", "MappedStart"]
      [("Node", "WalkNode")])
    [mapVertex "SourceStart" "MappedStart"]
    (.apply "MapRequest"
      [.apply "WalkValue"
        [.fvar "SourceStart", .fvar "SourceTarget", .fvar "Node"]])
    (.apply "MapScan"
      [.fvar "SourceStart", .fvar "SourceTarget", .fvar "MappedStart",
       .fvar "MappedStart", .fvar "Node",
       .apply "FramesNil" [.fvar "MappedStart"]])

/-- Map one source edge.  The rule obtains the image of the next vertex and
checks the resulting edge in the target graph before advancing. -/
def mapScanConsRule : RewriteRule :=
  RewriteRule.mk "MapScanCons"
    (context
      ["SourceCurrent", "SourceNext", "SourceTarget", "MappedOrigin",
        "MappedCurrent", "MappedNext"]
      [("Tail", "WalkNode"), ("Frames", "Frames")])
    [sourceAdjacent "SourceCurrent" "SourceNext",
      mapVertex "SourceNext" "MappedNext",
      targetAdjacent "MappedCurrent" "MappedNext"]
    (.apply "MapScan"
      [.fvar "SourceCurrent", .fvar "SourceTarget", .fvar "MappedOrigin",
       .fvar "MappedCurrent",
       .apply "WalkCons"
        [.fvar "SourceCurrent", .fvar "SourceNext", .fvar "SourceTarget",
         .apply "WalkValue"
          [.fvar "SourceNext", .fvar "SourceTarget", .fvar "Tail"]],
       .fvar "Frames"])
    (.apply "MapScan"
      [.fvar "SourceNext", .fvar "SourceTarget", .fvar "MappedOrigin",
       .fvar "MappedNext", .fvar "Tail",
       .apply "FramesCons"
        [.fvar "MappedNext", .fvar "MappedCurrent", .fvar "Frames"]])

def mapScanNilRule : RewriteRule :=
  RewriteRule.mk "MapScanNil"
    (context ["SourceTarget", "MappedOrigin", "MappedTarget"]
      [("Frames", "Frames")]) []
    (.apply "MapScan"
      [.fvar "SourceTarget", .fvar "SourceTarget", .fvar "MappedOrigin",
       .fvar "MappedTarget", .apply "WalkNil" [.fvar "SourceTarget"],
       .fvar "Frames"])
    (.apply "MapRebuild"
      [.fvar "MappedTarget", .fvar "MappedTarget", .fvar "Frames",
       .apply "WalkValue"
        [.fvar "MappedTarget", .fvar "MappedTarget",
         .apply "WalkNil" [.fvar "MappedTarget"]]])

def mapRebuildConsRule : RewriteRule :=
  RewriteRule.mk "MapRebuildCons"
    (context ["Current", "Previous", "Target"]
      [("Rest", "Frames"), ("Result", "WalkNode")])
    [targetAdjacent "Previous" "Current"]
    (.apply "MapRebuild"
      [.fvar "Current", .fvar "Target",
       .apply "FramesCons"
        [.fvar "Current", .fvar "Previous", .fvar "Rest"],
       .apply "WalkValue"
        [.fvar "Current", .fvar "Target", .fvar "Result"]])
    (.apply "MapRebuild"
      [.fvar "Previous", .fvar "Target", .fvar "Rest",
       .apply "WalkValue"
        [.fvar "Previous", .fvar "Target",
         .apply "WalkCons"
          [.fvar "Previous", .fvar "Current", .fvar "Target",
           .apply "WalkValue"
            [.fvar "Current", .fvar "Target", .fvar "Result"]]]])

def mapRebuildNilRule : RewriteRule :=
  RewriteRule.mk "MapRebuildNil"
    (context ["Start", "Target"] [("Result", "WalkNode")]) []
    (.apply "MapRebuild"
      [.fvar "Start", .fvar "Target", .apply "FramesNil" [.fvar "Start"],
       .apply "WalkValue" [.fvar "Start", .fvar "Target", .fvar "Result"]])
    (.apply "WalkDone"
      [.apply "WalkValue" [.fvar "Start", .fvar "Target", .fvar "Result"]])

def rewrites : List RewriteRule :=
  [appendStartRule, appendScanConsRule, appendScanNilRule,
    appendRebuildConsRule, appendRebuildNilRule,
    reverseStartRule, reverseScanConsRule, reverseScanNilRule,
    mapStartRule, mapScanConsRule, mapScanNilRule,
    mapRebuildConsRule, mapRebuildNilRule]

/-- The walk LanguageDef has actual operational content: thirteen recursive
rows, including six relation-guarded rows. -/
def language : LanguageDef :=
  LanguageDef.ofCore "FiniteGraphWalkOperations" types terms [] rewrites

theorem language_rewrites : language.rewrites = rewrites := rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
private theorem rewrites_validate :
    ∀ rule ∈ language.rewrites,
      LanguageDef.validateRewrite language rule = [] := by
  intro rule membership
  simp only [language_rewrites, rewrites, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals
    simp +decide [LanguageDef.validateRewrite, language, types, terms,
      constructor, parameter, context, vertexContext,
      appendStartRule, appendScanConsRule, appendScanNilRule,
      appendRebuildConsRule, appendRebuildNilRule,
      reverseStartRule, reverseScanConsRule, reverseScanNilRule,
      mapStartRule, mapScanConsRule, mapScanNilRule,
      mapRebuildConsRule, mapRebuildNilRule, sourceAdjacent,
      targetAdjacent, mapVertex,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
      LanguageDef.premiseForAllParams,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      LanguageDef.typeNames]

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
theorem language_validates : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  exact rewrites_validate

/-! ## Finite graph relation environment -/

def vertexPattern : Nat → Pattern
  | 0 => .apply "VertexZero" []
  | vertex + 1 => .apply "VertexSucc" [vertexPattern vertex]

def finPattern {n : Nat} (vertex : Fin n) : Pattern :=
  vertexPattern vertex.val

def decodeVertex? : Pattern → Option Nat
  | .apply "VertexZero" [] => some 0
  | .apply "VertexSucc" [vertex] => decodeVertex? vertex |>.map Nat.succ
  | _ => none

@[simp] theorem decodeVertex?_vertexPattern (vertex : Nat) :
    decodeVertex? (vertexPattern vertex) = some vertex := by
  induction vertex with
  | zero => rfl
  | succ vertex inductionHypothesis =>
      simp [vertexPattern, decodeVertex?, inductionHypothesis]

def decodeFin? (n : Nat) (pattern : Pattern) : Option (Fin n) := do
  let vertex ← decodeVertex? pattern
  if within : vertex < n then
    some ⟨vertex, within⟩
  else
    none

@[simp] theorem decodeFin?_finPattern {n : Nat} (vertex : Fin n) :
    decodeFin? n (finPattern vertex) = some vertex := by
  simp [decodeFin?, finPattern]

theorem finPattern_injective {n : Nat} :
    Function.Injective (@finPattern n) := by
  intro left right encoded
  have decoded := congrArg (decodeFin? n) encoded
  simpa using decoded

theorem finPattern_ne {n : Nat} {left right : Fin n}
    (different : left ≠ right) : finPattern left ≠ finPattern right :=
  fun encoded => different (finPattern_injective encoded)

/-- Relation rows for a source graph, target graph, and selected graph
homomorphism.  Queries inspect at most one edge or one vertex image. -/
def relationTuples {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (relation : String) (arguments : List Pattern) :
    List (List Pattern) :=
  match relation, arguments with
  | "SourceAdjacent", [left, right] =>
      match decodeFin? n left, decodeFin? n right with
      | some u, some v => if source.Adj u v then [[left, right]] else []
      | _, _ => []
  | "TargetAdjacent", [left, right] =>
      match decodeFin? m left, decodeFin? m right with
      | some u, some v => if target.Adj u v then [[left, right]] else []
      | _, _ => []
  | "MapVertex", [input, _output] =>
      match decodeFin? n input with
      | some vertex => [[input, finPattern (hom vertex)]]
      | none => []
  | _, _ => []

def relationEnv {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) : RelationEnv where
  tuples := relationTuples source target hom

theorem sourceAdjacent_exact {n m : Nat}
    {source : SimpleGraph (Fin n)} {target : SimpleGraph (Fin m)}
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {u v : Fin n} (edge : source.Adj u v) :
    relationTuples source target hom "SourceAdjacent"
      [finPattern u, finPattern v] = [[finPattern u, finPattern v]] := by
  simp [relationTuples, edge]

theorem sourceNonadjacent_exact {n m : Nat}
    {source : SimpleGraph (Fin n)} {target : SimpleGraph (Fin m)}
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {u v : Fin n} (nonedge : ¬ source.Adj u v) :
    relationTuples source target hom "SourceAdjacent"
      [finPattern u, finPattern v] = [] := by
  simp [relationTuples, nonedge]

theorem targetAdjacent_exact {n m : Nat}
    {source : SimpleGraph (Fin n)} {target : SimpleGraph (Fin m)}
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {u v : Fin m} (edge : target.Adj u v) :
    relationTuples source target hom "TargetAdjacent"
      [finPattern u, finPattern v] = [[finPattern u, finPattern v]] := by
  simp [relationTuples, edge]

theorem mapVertex_exact {n m : Nat}
    {source : SimpleGraph (Fin n)} {target : SimpleGraph (Fin m)}
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (vertex : Fin n) (output : Pattern) :
    relationTuples source target hom "MapVertex"
      [finPattern vertex, output] =
        [[finPattern vertex, finPattern (hom vertex)]] := by
  simp [relationTuples]

/-! ## Canonical walk encodings -/

mutual

  def walkPattern {n : Nat} {graph : SimpleGraph (Fin n)} :
      {source target : Fin n} → graph.Walk source target → Pattern
    | source, target, walk =>
        .apply "WalkValue"
          [finPattern source, finPattern target, walkNodePattern walk]

  def walkNodePattern {n : Nat} {graph : SimpleGraph (Fin n)} :
      {source target : Fin n} → graph.Walk source target → Pattern
    | source, _, .nil => .apply "WalkNil" [finPattern source]
    | source, target, .cons (v := next) _edge tail =>
        .apply "WalkCons"
          [finPattern source, finPattern next, finPattern target,
           walkPattern tail]

end

def framesPattern {n : Nat} {graph : SimpleGraph (Fin n)} :
    {current origin : Fin n} → graph.Walk current origin → Pattern
  | current, _, .nil => .apply "FramesNil" [finPattern current]
  | current, _, .cons (v := previous) _ rest =>
      .apply "FramesCons"
        [finPattern current, finPattern previous, framesPattern rest]

def appendRequestPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {source middle target : Fin n} (left : graph.Walk source middle)
    (right : graph.Walk middle target) : Pattern :=
  .apply "AppendRequest" [walkPattern left, walkPattern right]

def reverseRequestPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {source target : Fin n} (walk : graph.Walk source target) : Pattern :=
  .apply "ReverseRequest" [walkPattern walk]

def mapRequestPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {source target : Fin n} (walk : graph.Walk source target) : Pattern :=
  .apply "MapRequest" [walkPattern walk]

def donePattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {source target : Fin n} (walk : graph.Walk source target) : Pattern :=
  .apply "WalkDone" [walkPattern walk]

/-- One root-level use of the actual authored rewrite table. -/
def rewriteOnce {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (term : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises (relationEnv source target hom)) language 1 term

/-- The relation-aware GSLT denoted by the authored walk language. -/
def theory {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) : GSLT :=
  languageGSLTUsing (relationEnv source target hom) language
    (ReductionRespectsEquationsUsing.of_equation_free _ rfl)

/-- The walk presentation has no equation generators, so the equation relation
of its GSLT is exactly equality. This is the checked discrete specialization
used when raw walk predicates enter equation-respecting semantic interfaces. -/
theorem theory_equiv_iff_eq {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (left right : Pattern) :
    (theory source target hom).Equiv left right ↔ left = right :=
  Mettapedia.GSLT.LanguageDef.EquationSemantics.equationEquiv_iff_eq_of_no_generators
    rfl left right

#print axioms language_validates
#print axioms decodeVertex?_vertexPattern
#print axioms decodeFin?_finPattern
#print axioms finPattern_injective
#print axioms sourceAdjacent_exact
#print axioms sourceNonadjacent_exact
#print axioms targetAdjacent_exact
#print axioms mapVertex_exact

end Mettapedia.GraphTheory.Walk.LanguageDef
