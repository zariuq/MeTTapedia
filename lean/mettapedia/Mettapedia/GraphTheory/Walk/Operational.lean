import Mettapedia.GraphTheory.Walk.LanguageDef
import Mettapedia.GSLT.Dynamics.PathIntegral

/-!
# Exact execution of the finite-graph walk LanguageDef

This module connects the authored walk rewrites to Mathlib's dependent
`SimpleGraph.Walk` operations.  Each machine phase has an exact executable
one-step theorem.  Those theorems are then assembled into proof-relevant GSLT
paths for append, reverse, and homomorphic map.

The construction deliberately retains the intermediate scan and rebuild
states.  The correspondence therefore establishes that the LanguageDef
performs the operations, rather than merely comparing a hidden implementation
with the final answer.
-/

namespace Mettapedia.GraphTheory.Walk.Operational

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Walk.LanguageDef
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open SimpleGraph

set_option autoImplicit false

/-! ## Canonical machine states -/

def appendScanPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {current middle target origin : Fin n}
    (left : graph.Walk current middle) (right : graph.Walk middle target)
    (frames : graph.Walk current origin) : Pattern :=
  .apply "AppendScan"
    [finPattern current, finPattern middle, finPattern target,
      walkNodePattern left, walkPattern right, framesPattern frames]

def appendRebuildPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {current origin target : Fin n} (frames : graph.Walk current origin)
    (result : graph.Walk current target) : Pattern :=
  .apply "AppendRebuild"
    [finPattern current, finPattern target, framesPattern frames,
      walkPattern result]

def reverseScanPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {current target origin : Fin n} (remaining : graph.Walk current target)
    (accumulator : graph.Walk current origin) : Pattern :=
  .apply "ReverseScan"
    [finPattern current, finPattern target, finPattern origin,
      walkNodePattern remaining, walkPattern accumulator]

def mapScanPattern {n m : Nat} {source : SimpleGraph (Fin n)}
    {target : SimpleGraph (Fin m)}
    {sourceCurrent sourceTarget : Fin n} {mappedOrigin mappedCurrent : Fin m}
    (remaining : source.Walk sourceCurrent sourceTarget)
    (frames : target.Walk mappedCurrent mappedOrigin) : Pattern :=
  .apply "MapScan"
    [finPattern sourceCurrent, finPattern sourceTarget,
      finPattern mappedOrigin, finPattern mappedCurrent,
      walkNodePattern remaining, framesPattern frames]

def mapRebuildPattern {m : Nat} {target : SimpleGraph (Fin m)}
    {current origin targetVertex : Fin m}
    (frames : target.Walk current origin)
    (result : target.Walk current targetVertex) : Pattern :=
  .apply "MapRebuild"
    [finPattern current, finPattern targetVertex, framesPattern frames,
      walkPattern result]

/-! A fully bound adjacency query is an exact echo: it neither invents nor
changes bindings.  This reusable lemma keeps the public relation-query
admission boundary visible in the executable step proofs below. -/

theorem sourceAdjacent_premise_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) (bindings : Bindings)
    (sourceName targetName : String) {source target : Fin n}
    (sourceBound : bindings.lookup sourceName = some (finPattern source))
    (targetBound : bindings.lookup targetName = some (finPattern target))
    (edge : graph.Adj source target) :
    premiseStepUsing (engineBasePremises (relationEnv graph other hom))
        language (fun _ => []) bindings
        (sourceAdjacent sourceName targetName) = [bindings] := by
  change relationQueryStep (relationEnv graph other hom) language bindings
    "SourceAdjacent" [Pattern.fvar sourceName, Pattern.fvar targetName] =
      [bindings]
  have exactEcho := relationQueryStep_boundVariables_echo_eq
    (relEnv := relationEnv graph other hom) (language := language)
    (bindings := bindings) (relation := "SourceAdjacent")
    (names := [sourceName, targetName])
    (values := [finPattern source, finPattern target])
    (condition := true)
    (.cons sourceBound (.cons targetBound .nil)) (by rfl)
    (by simp [relationEnv, relationTuples, edge])
  simpa using exactEcho

theorem sourceAdjacent_premise_empty {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) (bindings : Bindings)
    (sourceName targetName : String) {source target : Fin n}
    (sourceBound : bindings.lookup sourceName = some (finPattern source))
    (targetBound : bindings.lookup targetName = some (finPattern target))
    (nonedge : ¬ graph.Adj source target) :
    premiseStepUsing (engineBasePremises (relationEnv graph other hom))
        language (fun _ => []) bindings
        (sourceAdjacent sourceName targetName) = [] := by
  change relationQueryStep (relationEnv graph other hom) language bindings
    "SourceAdjacent" [Pattern.fvar sourceName, Pattern.fvar targetName] = []
  have exactEcho := relationQueryStep_boundVariables_echo_eq
    (relEnv := relationEnv graph other hom) (language := language)
    (bindings := bindings) (relation := "SourceAdjacent")
    (names := [sourceName, targetName])
    (values := [finPattern source, finPattern target])
    (condition := false)
    (.cons sourceBound (.cons targetBound .nil)) (by rfl)
    (by simp [relationEnv, relationTuples, nonedge])
  simpa using exactEcho

theorem targetAdjacent_premise_exact {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (bindings : Bindings)
    (sourceName targetName : String) {u v : Fin m}
    (sourceBound : bindings.lookup sourceName = some (finPattern u))
    (targetBound : bindings.lookup targetName = some (finPattern v))
    (edge : target.Adj u v) :
    premiseStepUsing (engineBasePremises (relationEnv source target hom))
        language (fun _ => []) bindings
        (targetAdjacent sourceName targetName) = [bindings] := by
  change relationQueryStep (relationEnv source target hom) language bindings
    "TargetAdjacent" [Pattern.fvar sourceName, Pattern.fvar targetName] =
      [bindings]
  have exactEcho := relationQueryStep_boundVariables_echo_eq
    (relEnv := relationEnv source target hom) (language := language)
    (bindings := bindings) (relation := "TargetAdjacent")
    (names := [sourceName, targetName])
    (values := [finPattern u, finPattern v])
    (condition := true)
    (.cons sourceBound (.cons targetBound .nil)) (by rfl)
    (by simp [relationEnv, relationTuples, edge])
  simpa using exactEcho

macro "walk_rewrite" : tactic =>
  `(tactic|
    (simp only [rewriteOnce, rewriteAt, language_rewrites, rewrites,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
     simp [appendRequestPattern, reverseRequestPattern, mapRequestPattern,
       appendScanPattern, appendRebuildPattern, reverseScanPattern,
       mapScanPattern, mapRebuildPattern, donePattern,
       appendStartRule, appendScanConsRule, appendScanNilRule,
       appendRebuildConsRule, appendRebuildNilRule,
       reverseStartRule, reverseScanConsRule, reverseScanNilRule,
       mapStartRule, mapScanConsRule, mapScanNilRule,
       mapRebuildConsRule, mapRebuildNilRule,
       sourceAdjacent, targetAdjacent, mapVertex,
       applyRuleUsing, matchPatternForRule, matchPatternForRuleUsing,
       applyBindingsForRule, applyBindingsForRuleUsing, premisesUsing,
       matchPattern, matchArgs, mergeBindings, applyBindings,
       relationEnv, relationTuples, walkPattern, walkNodePattern,
       framesPattern, SimpleGraph.adj_comm]))

/-! ## Exact executable steps -/

theorem append_start_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source middle target : Fin n}
    (left : graph.Walk source middle) (right : graph.Walk middle target) :
    rewriteOnce graph other hom (appendRequestPattern left right) =
      [appendScanPattern left right (Walk.nil : graph.Walk source source)] := by
  walk_rewrite

theorem append_scan_cons_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current next middle target origin : Fin n}
    (edge : graph.Adj current next) (tail : graph.Walk next middle)
    (right : graph.Walk middle target) (frames : graph.Walk current origin) :
    rewriteOnce graph other hom
        (appendScanPattern (Walk.cons edge tail) right frames) =
      [appendScanPattern tail right (Walk.cons edge.symm frames)] := by
  have adjacency := sourceAdjacent_premise_exact graph other hom
    [("Middle", finPattern middle), ("Tail", walkNodePattern tail),
      ("Next", finPattern next), ("Frames", framesPattern frames),
      ("Right", walkPattern right), ("Target", finPattern target),
      ("Current", finPattern current)]
    "Current" "Next" (source := current) (target := next)
    (by simp [Bindings.lookup]) (by simp [Bindings.lookup]) edge
  have adjacency' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples graph other hom })
          language (fun _ => [])
          [("Middle", finPattern middle), ("Tail", walkNodePattern tail),
            ("Next", finPattern next), ("Frames", framesPattern frames),
            ("Right", .apply "WalkValue"
              [finPattern middle, finPattern target, walkNodePattern right]),
            ("Target", finPattern target),
            ("Current", finPattern current)]
          (.relationQuery "SourceAdjacent"
            [.fvar "Current", .fvar "Next"]) =
        [[("Middle", finPattern middle), ("Tail", walkNodePattern tail),
          ("Next", finPattern next), ("Frames", framesPattern frames),
          ("Right", .apply "WalkValue"
            [finPattern middle, finPattern target, walkNodePattern right]),
          ("Target", finPattern target),
          ("Current", finPattern current)]] := by
    simpa [relationEnv, sourceAdjacent, walkPattern] using adjacency
  walk_rewrite
  simp [adjacency']

theorem append_scan_nil_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {middle target origin : Fin n}
    (right : graph.Walk middle target) (frames : graph.Walk middle origin) :
    rewriteOnce graph other hom
        (appendScanPattern (Walk.nil : graph.Walk middle middle) right frames) =
      [appendRebuildPattern frames right] := by
  walk_rewrite

theorem append_rebuild_cons_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current previous origin target : Fin n}
    (edge : graph.Adj current previous) (rest : graph.Walk previous origin)
    (result : graph.Walk current target) :
    rewriteOnce graph other hom
        (appendRebuildPattern (Walk.cons edge rest) result) =
      [appendRebuildPattern rest (Walk.cons edge.symm result)] := by
  have adjacency := sourceAdjacent_premise_exact graph other hom
    [("Target", finPattern target), ("Result", walkNodePattern result),
      ("Previous", finPattern previous), ("Rest", framesPattern rest),
      ("Current", finPattern current)]
    "Previous" "Current" (source := previous) (target := current)
    (by simp [Bindings.lookup]) (by simp [Bindings.lookup]) edge.symm
  have adjacency' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples graph other hom })
          language (fun _ => [])
          [("Target", finPattern target), ("Result", walkNodePattern result),
            ("Previous", finPattern previous), ("Rest", framesPattern rest),
            ("Current", finPattern current)]
          (.relationQuery "SourceAdjacent"
            [.fvar "Previous", .fvar "Current"]) =
        [[("Target", finPattern target), ("Result", walkNodePattern result),
          ("Previous", finPattern previous), ("Rest", framesPattern rest),
          ("Current", finPattern current)]] := by
    simpa [relationEnv, sourceAdjacent] using adjacency
  walk_rewrite
  simp [adjacency']

theorem append_rebuild_nil_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source target : Fin n}
    (result : graph.Walk source target) :
    rewriteOnce graph other hom
        (appendRebuildPattern (Walk.nil : graph.Walk source source) result) =
      [donePattern result] := by
  walk_rewrite

theorem reverse_start_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source target : Fin n}
    (walk : graph.Walk source target) :
    rewriteOnce graph other hom (reverseRequestPattern walk) =
      [reverseScanPattern walk (Walk.nil : graph.Walk source source)] := by
  walk_rewrite

/-- The initial reversal row is exact for every syntactically indexed walk
node.  This theorem exposes the first inversion step needed by native-type
no-junk arguments without assuming that the node already came from Mathlib. -/
theorem reverse_raw_start_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) (start finish : Fin n) (node : Pattern) :
    rewriteOnce graph other hom
      (.apply "ReverseRequest"
        [.apply "WalkValue" [finPattern start, finPattern finish, node]]) =
      [.apply "ReverseScan"
        [finPattern start, finPattern finish, finPattern start, node,
          .apply "WalkValue"
            [finPattern start, finPattern start,
              .apply "WalkNil" [finPattern start]]]] := by
  walk_rewrite

theorem reverse_scan_cons_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current next target origin : Fin n}
    (edge : graph.Adj current next) (tail : graph.Walk next target)
    (accumulator : graph.Walk current origin) :
    rewriteOnce graph other hom
        (reverseScanPattern (Walk.cons edge tail) accumulator) =
      [reverseScanPattern tail (Walk.cons edge.symm accumulator)] := by
  have adjacency := sourceAdjacent_premise_exact graph other hom
    [("Target", finPattern target), ("Tail", walkNodePattern tail),
      ("Next", finPattern next),
      ("Accumulator", walkNodePattern accumulator),
      ("Origin", finPattern origin), ("Current", finPattern current)]
    "Next" "Current" (source := next) (target := current)
    (by simp [Bindings.lookup]) (by simp [Bindings.lookup]) edge.symm
  have adjacency' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples graph other hom })
          language (fun _ => [])
          [("Target", finPattern target), ("Tail", walkNodePattern tail),
            ("Next", finPattern next),
            ("Accumulator", walkNodePattern accumulator),
            ("Origin", finPattern origin), ("Current", finPattern current)]
          (.relationQuery "SourceAdjacent"
            [.fvar "Next", .fvar "Current"]) =
        [[("Target", finPattern target), ("Tail", walkNodePattern tail),
          ("Next", finPattern next),
          ("Accumulator", walkNodePattern accumulator),
          ("Origin", finPattern origin), ("Current", finPattern current)]] := by
    simpa [relationEnv, sourceAdjacent] using adjacency
  walk_rewrite
  simp [adjacency']

theorem reverse_scan_nil_exact {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {target origin : Fin n}
    (accumulator : graph.Walk target origin) :
    rewriteOnce graph other hom
        (reverseScanPattern (Walk.nil : graph.Walk target target)
          accumulator) =
      [donePattern accumulator] := by
  walk_rewrite

theorem map_start_exact {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {start finish : Fin n}
    (walk : source.Walk start finish) :
    rewriteOnce source target hom (mapRequestPattern walk) =
      [mapScanPattern walk
        (Walk.nil : target.Walk (hom start) (hom start))] := by
  have mapping :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples source target hom })
          language (fun _ => [])
          [("SourceTarget", finPattern finish), ("Node", walkNodePattern walk),
            ("SourceStart", finPattern start)]
          (.relationQuery "MapVertex"
            [.fvar "SourceStart", .fvar "MappedStart"]) =
        [[("MappedStart", finPattern (hom start)),
          ("SourceTarget", finPattern finish), ("Node", walkNodePattern walk),
          ("SourceStart", finPattern start)]] := by
    simp [premiseStepUsing, engineBasePremises, premiseStepWithEnv,
      relationQueryStep, builtinRelationTuples, relationTuples,
      matchRelationArgs, matchRelationArgument, mergeBindings,
      applyBindings, Bindings.lookup]
  walk_rewrite
  simp [mapping]

theorem map_scan_cons_exact {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target)
    {sourceCurrent sourceNext sourceTarget : Fin n}
    {mappedOrigin : Fin m}
    (edge : source.Adj sourceCurrent sourceNext)
    (tail : source.Walk sourceNext sourceTarget)
    (frames : target.Walk (hom sourceCurrent) mappedOrigin) :
    rewriteOnce source target hom
        (mapScanPattern (Walk.cons edge tail) frames) =
      [mapScanPattern tail (Walk.cons (hom.map_adj edge).symm frames)] := by
  let bindings : Bindings :=
    [("SourceTarget", finPattern sourceTarget),
      ("MappedCurrent", finPattern (hom sourceCurrent)),
      ("Frames", framesPattern frames), ("SourceNext", finPattern sourceNext),
      ("Tail", walkNodePattern tail), ("MappedOrigin", finPattern mappedOrigin),
      ("SourceCurrent", finPattern sourceCurrent)]
  let mappedBindings : Bindings :=
    ("MappedNext", finPattern (hom sourceNext)) :: bindings
  have sourceEdge := sourceAdjacent_premise_exact source target hom bindings
    "SourceCurrent" "SourceNext" (source := sourceCurrent)
    (target := sourceNext)
    (by simp [bindings, Bindings.lookup])
    (by simp [bindings, Bindings.lookup]) edge
  have mappedVertex :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples source target hom })
          language (fun _ => []) bindings
          (.relationQuery "MapVertex"
            [.fvar "SourceNext", .fvar "MappedNext"]) =
        [mappedBindings] := by
    simp [bindings, mappedBindings, premiseStepUsing, engineBasePremises,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationTuples, matchRelationArgs, matchRelationArgument,
      mergeBindings, applyBindings, Bindings.lookup]
  have targetEdge := targetAdjacent_premise_exact source target hom
    mappedBindings "MappedCurrent" "MappedNext"
    (u := hom sourceCurrent) (v := hom sourceNext)
    (by simp [bindings, mappedBindings, Bindings.lookup])
    (by simp [bindings, mappedBindings, Bindings.lookup]) (hom.map_adj edge)
  have sourceEdge' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples source target hom })
          language (fun _ => []) bindings
          (.relationQuery "SourceAdjacent"
            [.fvar "SourceCurrent", .fvar "SourceNext"]) = [bindings] := by
    simpa [relationEnv, sourceAdjacent] using sourceEdge
  have targetEdge' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples source target hom })
          language (fun _ => []) mappedBindings
          (.relationQuery "TargetAdjacent"
            [.fvar "MappedCurrent", .fvar "MappedNext"]) =
        [mappedBindings] := by
    simpa [relationEnv, targetAdjacent] using targetEdge
  walk_rewrite
  simp [bindings, mappedBindings, sourceEdge', mappedVertex, targetEdge']

theorem map_scan_nil_exact {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {sourceTarget : Fin n} {mappedOrigin : Fin m}
    (frames : target.Walk (hom sourceTarget) mappedOrigin) :
    rewriteOnce source target hom
        (mapScanPattern (Walk.nil : source.Walk sourceTarget sourceTarget)
          frames) =
      [mapRebuildPattern frames
        (Walk.nil : target.Walk (hom sourceTarget) (hom sourceTarget))] := by
  walk_rewrite

theorem map_rebuild_cons_exact {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {current previous origin finish : Fin m}
    (edge : target.Adj current previous) (rest : target.Walk previous origin)
    (result : target.Walk current finish) :
    rewriteOnce source target hom
        (mapRebuildPattern (Walk.cons edge rest) result) =
      [mapRebuildPattern rest (Walk.cons edge.symm result)] := by
  have adjacency := targetAdjacent_premise_exact source target hom
    [("Target", finPattern finish), ("Result", walkNodePattern result),
      ("Previous", finPattern previous), ("Rest", framesPattern rest),
      ("Current", finPattern current)]
    "Previous" "Current" (u := previous) (v := current)
    (by simp [Bindings.lookup]) (by simp [Bindings.lookup]) edge.symm
  have adjacency' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples source target hom })
          language (fun _ => [])
          [("Target", finPattern finish), ("Result", walkNodePattern result),
            ("Previous", finPattern previous), ("Rest", framesPattern rest),
            ("Current", finPattern current)]
          (.relationQuery "TargetAdjacent"
            [.fvar "Previous", .fvar "Current"]) =
        [[("Target", finPattern finish), ("Result", walkNodePattern result),
          ("Previous", finPattern previous), ("Rest", framesPattern rest),
          ("Current", finPattern current)]] := by
    simpa [relationEnv, targetAdjacent] using adjacency
  walk_rewrite
  simp [adjacency']

theorem map_rebuild_nil_exact {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {start finish : Fin m}
    (result : target.Walk start finish) :
    rewriteOnce source target hom
        (mapRebuildPattern (Walk.nil : target.Walk start start) result) =
      [donePattern result] := by
  walk_rewrite

/-! ## Fail-closed malformed inputs -/

def endpointMismatchedAppendPattern {n : Nat}
    {graph : SimpleGraph (Fin n)}
    {leftStart leftEnd rightStart rightEnd : Fin n}
    (left : graph.Walk leftStart leftEnd)
    (right : graph.Walk rightStart rightEnd) : Pattern :=
  .apply "AppendRequest" [walkPattern left, walkPattern right]

theorem endpoint_mismatch_rejected {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other)
    {leftStart leftEnd rightStart rightEnd : Fin n}
    (left : graph.Walk leftStart leftEnd)
    (right : graph.Walk rightStart rightEnd)
    (mismatch : leftEnd ≠ rightStart) :
    rewriteOnce graph other hom
      (endpointMismatchedAppendPattern left right) = [] := by
  simp only [endpointMismatchedAppendPattern]
  walk_rewrite
  exact finPattern_ne mismatch

def uncheckedAppendScanPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {current next middle target origin : Fin n}
    (tail : graph.Walk next middle) (right : graph.Walk middle target)
    (frames : graph.Walk current origin) : Pattern :=
  .apply "AppendScan"
    [finPattern current, finPattern middle, finPattern target,
      .apply "WalkCons"
        [finPattern current, finPattern next, finPattern middle,
          walkPattern tail],
      walkPattern right, framesPattern frames]

theorem nonedge_scan_rejected {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current next middle target origin : Fin n}
    (tail : graph.Walk next middle) (right : graph.Walk middle target)
    (frames : graph.Walk current origin)
    (nonedge : ¬ graph.Adj current next) :
    rewriteOnce graph other hom
      (uncheckedAppendScanPattern tail right frames) = [] := by
  have rejected := sourceAdjacent_premise_empty graph other hom
    [("Middle", finPattern middle), ("Tail", walkNodePattern tail),
      ("Next", finPattern next), ("Frames", framesPattern frames),
      ("Right", walkPattern right), ("Target", finPattern target),
      ("Current", finPattern current)]
    "Current" "Next" (source := current) (target := next)
    (by simp [Bindings.lookup]) (by simp [Bindings.lookup]) nonedge
  have rejected' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples graph other hom })
          language (fun _ => [])
          [("Middle", finPattern middle), ("Tail", walkNodePattern tail),
            ("Next", finPattern next), ("Frames", framesPattern frames),
            ("Right", .apply "WalkValue"
              [finPattern middle, finPattern target, walkNodePattern right]),
            ("Target", finPattern target), ("Current", finPattern current)]
          (.relationQuery "SourceAdjacent"
            [.fvar "Current", .fvar "Next"]) = [] := by
    simpa [relationEnv, sourceAdjacent, walkPattern] using rejected
  simp only [uncheckedAppendScanPattern]
  walk_rewrite
  simp [rejected']

/-- A reverse scanner state whose next recursive edge is absent from the
source graph.  The syntax is intentionally constructible so that the
relation premise, rather than a host-side walk constructor, bears the
rejection obligation. -/
def uncheckedReverseScanPattern {n : Nat} {graph : SimpleGraph (Fin n)}
    {current next target origin : Fin n}
    (tail : graph.Walk next target)
    (accumulator : graph.Walk current origin) : Pattern :=
  .apply "ReverseScan"
    [finPattern current, finPattern target, finPattern origin,
      .apply "WalkCons"
        [finPattern current, finPattern next, finPattern target,
          walkPattern tail],
      walkPattern accumulator]

/-- The guarded reverse rule also fails closed on a forged non-edge. -/
theorem reverse_nonedge_scan_rejected {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current next target origin : Fin n}
    (tail : graph.Walk next target)
    (accumulator : graph.Walk current origin)
    (nonedge : ¬ graph.Adj current next) :
    rewriteOnce graph other hom
      (uncheckedReverseScanPattern tail accumulator) = [] := by
  have reversedNonedge : ¬ graph.Adj next current := by
    simpa [SimpleGraph.adj_comm] using nonedge
  have rejected := sourceAdjacent_premise_empty graph other hom
    [("Target", finPattern target), ("Tail", walkNodePattern tail),
      ("Next", finPattern next),
      ("Accumulator", walkNodePattern accumulator),
      ("Origin", finPattern origin), ("Current", finPattern current)]
    "Next" "Current" (source := next) (target := current)
    (by simp [Bindings.lookup]) (by simp [Bindings.lookup]) reversedNonedge
  have rejected' :
      premiseStepUsing
          (engineBasePremises { tuples := relationTuples graph other hom })
          language (fun _ => [])
          [("Target", finPattern target), ("Tail", walkNodePattern tail),
            ("Next", finPattern next),
            ("Accumulator", walkNodePattern accumulator),
            ("Origin", finPattern origin), ("Current", finPattern current)]
          (.relationQuery "SourceAdjacent"
            [.fvar "Next", .fvar "Current"]) = [] := by
    simpa [relationEnv, sourceAdjacent] using rejected
  simp only [uncheckedReverseScanPattern]
  walk_rewrite
  simp [rejected']

/-! ## Proof-relevant GSLT executions -/

theorem step_of_rewriteOnce_eq_singleton {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (before after : Pattern)
    (exact : rewriteOnce source target hom before = [after]) :
    (theory source target hom).Step before after := by
  apply (Mettapedia.GSLT.LanguageDef.TotalGSLT.languageGSLTUsing_step
    (relationEnv source target hom) language
    (Mettapedia.GSLT.LanguageDef.TotalGSLT.ReductionRespectsEquationsUsing.of_equation_free _ rfl)
    before after).2
  apply (langReducesUsing_iff_execUsing
    (relationEnv source target hom) language before after).2
  refine ⟨1, ?_⟩
  change after ∈ rewriteOnce source target hom before
  rw [exact]
  simp

noncomputable def appendRebuildPath {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current origin target : Fin n}
    (frames : graph.Walk current origin) (result : graph.Walk current target) :
    (theory graph other hom).RewritePath
      (appendRebuildPattern frames result)
      (donePattern (frames.reverseAux result)) := by
  induction frames generalizing target with
  | nil =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton graph other hom _ _
          (append_rebuild_nil_exact graph other hom result))
        (.nil _)
  | cons edge rest inductionHypothesis =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton graph other hom _ _
          (append_rebuild_cons_exact graph other hom edge rest result))
        (inductionHypothesis (Walk.cons edge.symm result))

@[simp] theorem appendRebuildPath_length {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current origin target : Fin n}
    (frames : graph.Walk current origin) (result : graph.Walk current target) :
    (appendRebuildPath graph other hom frames result).length =
      frames.length + 1 := by
  induction frames generalizing target with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      change 1 + (appendRebuildPath graph other hom rest
        (Walk.cons edge.symm result)).length = rest.length + 1 + 1
      rw [inductionHypothesis]
      omega

noncomputable def appendScanPath {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current middle target origin : Fin n}
    (left : graph.Walk current middle) (right : graph.Walk middle target)
    (frames : graph.Walk current origin) :
    (theory graph other hom).RewritePath
      (appendScanPattern left right frames)
      (donePattern ((left.reverseAux frames).reverseAux right)) := by
  induction left generalizing origin with
  | nil =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton graph other hom _ _
          (append_scan_nil_exact graph other hom right frames))
        (appendRebuildPath graph other hom frames right)
  | cons edge tail inductionHypothesis =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton graph other hom _ _
          (append_scan_cons_exact graph other hom edge tail right frames))
        (inductionHypothesis right (Walk.cons edge.symm frames))

@[simp] theorem appendScanPath_length {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current middle target origin : Fin n}
    (left : graph.Walk current middle) (right : graph.Walk middle target)
    (frames : graph.Walk current origin) :
    (appendScanPath graph other hom left right frames).length =
      2 * left.length + frames.length + 2 := by
  induction left generalizing origin with
  | nil =>
      simp only [appendScanPath, GSLT.RewritePath.length,
        Walk.length_nil, Nat.mul_zero, Nat.zero_add]
      have rebuildLength := appendRebuildPath_length graph other hom frames right
      calc
        1 + (appendRebuildPath graph other hom frames right).length =
            1 + (frames.length + 1) := congrArg (fun steps => 1 + steps)
              rebuildLength
        _ = frames.length + 2 := by omega
  | cons edge tail inductionHypothesis =>
      change 1 + (appendScanPath graph other hom tail right
        (Walk.cons edge.symm frames)).length =
          2 * (tail.length + 1) + frames.length + 2
      rw [inductionHypothesis]
      simp
      omega

private theorem append_scan_endpoint {n : Nat}
    {graph : SimpleGraph (Fin n)} {source middle target : Fin n}
    (left : graph.Walk source middle) (right : graph.Walk middle target) :
    ((left.reverseAux (Walk.nil : graph.Walk source source)).reverseAux
      right) = left.append right := by
  simp [Walk.reverseAux_eq_reverse_append]

private theorem rewritePath_length_cast_endpoint
    {S : GSLT} {start finish otherFinish : S.Term}
    (endpoint : finish = otherFinish) (path : S.RewritePath start finish) :
    (cast (congrArg (S.RewritePath start) endpoint) path).length =
      path.length := by
  cases endpoint
  rfl

noncomputable def appendExecution {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source middle target : Fin n}
    (left : graph.Walk source middle) (right : graph.Walk middle target) :
    { path : (theory graph other hom).RewritePath
        (appendRequestPattern left right) (donePattern (left.append right)) //
      path.length = 2 * left.length + 3 } := by
  let scan := appendScanPath graph other hom left right
    (Walk.nil : graph.Walk source source)
  let path := GSLT.RewritePath.cons
    (step_of_rewriteOnce_eq_singleton graph other hom _ _
      (append_start_exact graph other hom left right)) scan
  have endpoint :
      donePattern
          ((left.reverseAux (Walk.nil : graph.Walk source source)).reverseAux
            right) =
        donePattern (left.append right) := by
    simp [Walk.reverseAux_eq_reverse_append]
  let finalPath := cast
    (congrArg
      ((theory graph other hom).RewritePath (appendRequestPattern left right))
      endpoint)
    path
  refine ⟨finalPath, ?_⟩
  have scanLength := appendScanPath_length graph other hom left right
    (Walk.nil : graph.Walk source source)
  have pathLength : path.length = 2 * left.length + 3 := by
    dsimp only [path]
    simp only [GSLT.RewritePath.length]
    dsimp only [scan]
    rw [scanLength]
    simp
    omega
  have finalToPath : finalPath.length = path.length := by
    dsimp only [finalPath]
    exact rewritePath_length_cast_endpoint endpoint path
  exact finalToPath.trans pathLength

noncomputable def appendPath {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source middle target : Fin n}
    (left : graph.Walk source middle) (right : graph.Walk middle target) :
    (theory graph other hom).RewritePath
      (appendRequestPattern left right) (donePattern (left.append right)) :=
  (appendExecution graph other hom left right).1

@[simp] theorem appendPath_length {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source middle target : Fin n}
    (left : graph.Walk source middle) (right : graph.Walk middle target) :
    (appendPath graph other hom left right).length = 2 * left.length + 3 := by
  exact (appendExecution graph other hom left right).2

noncomputable def reverseScanPath {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current target origin : Fin n}
    (remaining : graph.Walk current target)
    (accumulator : graph.Walk current origin) :
    (theory graph other hom).RewritePath
      (reverseScanPattern remaining accumulator)
      (donePattern (remaining.reverseAux accumulator)) := by
  induction remaining generalizing origin with
  | nil =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton graph other hom _ _
          (reverse_scan_nil_exact graph other hom accumulator))
        (.nil _)
  | cons edge tail inductionHypothesis =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton graph other hom _ _
          (reverse_scan_cons_exact graph other hom edge tail accumulator))
        (inductionHypothesis (Walk.cons edge.symm accumulator))

@[simp] theorem reverseScanPath_length {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {current target origin : Fin n}
    (remaining : graph.Walk current target)
    (accumulator : graph.Walk current origin) :
    (reverseScanPath graph other hom remaining accumulator).length =
      remaining.length + 1 := by
  induction remaining generalizing origin with
  | nil => rfl
  | cons edge tail inductionHypothesis =>
      change 1 + (reverseScanPath graph other hom tail
        (Walk.cons edge.symm accumulator)).length = tail.length + 1 + 1
      rw [inductionHypothesis]
      omega

noncomputable def reversePath {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source target : Fin n}
    (walk : graph.Walk source target) :
    (theory graph other hom).RewritePath
      (reverseRequestPattern walk) (donePattern walk.reverse) := by
  exact .cons
    (step_of_rewriteOnce_eq_singleton graph other hom _ _
      (reverse_start_exact graph other hom walk))
    (reverseScanPath graph other hom walk
      (Walk.nil : graph.Walk source source))

@[simp] theorem reversePath_length {n m : Nat}
    (graph : SimpleGraph (Fin n)) (other : SimpleGraph (Fin m))
    [DecidableRel graph.Adj] [DecidableRel other.Adj]
    (hom : graph →g other) {source target : Fin n}
    (walk : graph.Walk source target) :
    (reversePath graph other hom walk).length = walk.length + 2 := by
  change 1 + (reverseScanPath graph other hom walk
    (Walk.nil : graph.Walk source source)).length = walk.length + 2
  rw [reverseScanPath_length]
  omega

noncomputable def mapRebuildPath {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {current origin finish : Fin m}
    (frames : target.Walk current origin)
    (result : target.Walk current finish) :
    (theory source target hom).RewritePath
      (mapRebuildPattern frames result)
      (donePattern (frames.reverseAux result)) := by
  induction frames generalizing finish with
  | nil =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton source target hom _ _
          (map_rebuild_nil_exact source target hom result))
        (.nil _)
  | cons edge rest inductionHypothesis =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton source target hom _ _
          (map_rebuild_cons_exact source target hom edge rest result))
        (inductionHypothesis (Walk.cons edge.symm result))

@[simp] theorem mapRebuildPath_length {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {current origin finish : Fin m}
    (frames : target.Walk current origin)
    (result : target.Walk current finish) :
    (mapRebuildPath source target hom frames result).length =
      frames.length + 1 := by
  induction frames generalizing finish with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      change 1 + (mapRebuildPath source target hom rest
        (Walk.cons edge.symm result)).length = rest.length + 1 + 1
      rw [inductionHypothesis]
      omega

noncomputable def mapScanPath {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {sourceCurrent sourceTarget : Fin n}
    {mappedOrigin : Fin m}
    (remaining : source.Walk sourceCurrent sourceTarget)
    (frames : target.Walk (hom sourceCurrent) mappedOrigin) :
    (theory source target hom).RewritePath
      (mapScanPattern remaining frames)
      (donePattern (((remaining.map hom).reverseAux frames).reverse)) := by
  induction remaining generalizing mappedOrigin with
  | nil =>
      rename_i vertex
      exact .cons
        (step_of_rewriteOnce_eq_singleton source target hom _ _
          (map_scan_nil_exact source target hom frames))
        (mapRebuildPath source target hom frames
          (Walk.nil : target.Walk (hom vertex) (hom vertex)))
  | cons edge tail inductionHypothesis =>
      exact .cons
        (step_of_rewriteOnce_eq_singleton source target hom _ _
          (map_scan_cons_exact source target hom edge tail frames))
        (inductionHypothesis
          (Walk.cons (hom.map_adj edge).symm frames))

@[simp] theorem mapScanPath_length {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {sourceCurrent sourceTarget : Fin n}
    {mappedOrigin : Fin m}
    (remaining : source.Walk sourceCurrent sourceTarget)
    (frames : target.Walk (hom sourceCurrent) mappedOrigin) :
    (mapScanPath source target hom remaining frames).length =
      2 * remaining.length + frames.length + 2 := by
  induction remaining generalizing mappedOrigin with
  | nil =>
      rename_i vertex
      simp only [mapScanPath, GSLT.RewritePath.length,
        Walk.length_nil, Nat.mul_zero, Nat.zero_add]
      have rebuildLength := mapRebuildPath_length source target hom frames
        (Walk.nil : target.Walk (hom vertex) (hom vertex))
      calc
        1 + (mapRebuildPath source target hom frames
              (Walk.nil : target.Walk (hom vertex)
                (hom vertex))).length =
            1 + (frames.length + 1) := congrArg (fun steps => 1 + steps)
              rebuildLength
        _ = frames.length + 2 := by omega
  | cons edge tail inductionHypothesis =>
      change 1 + (mapScanPath source target hom tail
        (Walk.cons (hom.map_adj edge).symm frames)).length =
          2 * (tail.length + 1) + frames.length + 2
      rw [inductionHypothesis]
      simp
      omega

private theorem map_scan_endpoint {n m : Nat}
    {source : SimpleGraph (Fin n)} {target : SimpleGraph (Fin m)}
    (hom : source →g target) {start finish : Fin n}
    (walk : source.Walk start finish) :
    (((walk.map hom).reverseAux
      (Walk.nil : target.Walk (hom start) (hom start))).reverse) =
        walk.map hom := by
  simp [Walk.reverseAux_eq_reverse_append]

noncomputable def mapExecution {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {start finish : Fin n}
    (walk : source.Walk start finish) :
    { path : (theory source target hom).RewritePath
        (mapRequestPattern walk) (donePattern (walk.map hom)) //
      path.length = 2 * walk.length + 3 } := by
  let scan := mapScanPath source target hom walk
    (Walk.nil : target.Walk (hom start) (hom start))
  let path := GSLT.RewritePath.cons
    (step_of_rewriteOnce_eq_singleton source target hom _ _
      (map_start_exact source target hom walk)) scan
  have endpoint :
      donePattern
          (((walk.map hom).reverseAux
            (Walk.nil : target.Walk (hom start) (hom start))).reverse) =
        donePattern (walk.map hom) := by
    simp [Walk.reverseAux_eq_reverse_append]
  let finalPath := cast
    (congrArg
      ((theory source target hom).RewritePath (mapRequestPattern walk))
      endpoint)
    path
  refine ⟨finalPath, ?_⟩
  have scanLength := mapScanPath_length source target hom walk
    (Walk.nil : target.Walk (hom start) (hom start))
  have pathLength : path.length = 2 * walk.length + 3 := by
    dsimp only [path]
    simp only [GSLT.RewritePath.length]
    dsimp only [scan]
    rw [scanLength]
    simp
    omega
  have finalToPath : finalPath.length = path.length := by
    dsimp only [finalPath]
    exact rewritePath_length_cast_endpoint endpoint path
  exact finalToPath.trans pathLength

noncomputable def mapPath {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {start finish : Fin n}
    (walk : source.Walk start finish) :
    (theory source target hom).RewritePath
      (mapRequestPattern walk) (donePattern (walk.map hom)) :=
  (mapExecution source target hom walk).1

@[simp] theorem mapPath_length {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) {start finish : Fin n}
    (walk : source.Walk start finish) :
    (mapPath source target hom walk).length = 2 * walk.length + 3 := by
  exact (mapExecution source target hom walk).2

#print axioms appendPath_length
#print axioms reversePath_length
#print axioms mapPath_length
#print axioms reverse_raw_start_exact
#print axioms reverse_nonedge_scan_rejected

end Mettapedia.GraphTheory.Walk.Operational
