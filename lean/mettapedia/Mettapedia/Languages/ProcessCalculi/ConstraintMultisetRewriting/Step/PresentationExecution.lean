import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Presentation
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

/-!
# Executing the authored event boundary

Preparation is queried for one specified source and firing. It returns at
most one target; permission is a separate query. This interface needs neither
a finite state space nor enumeration of all firings. Interpretation of these
queries against effects is supplied in `PresentationInterpretation`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

structure Queries where
  prepare : Pattern → Pattern → Option Pattern
  permit : Pattern → Pattern → Bool

def Queries.relations (q : Queries) : RelationEnv where
  tuples relation arguments :=
    match relation, arguments with
    | "prepared", [s, f, _] =>
        match q.prepare s f with
        | none => []
        | some t => [[s, f, t]]
    | "permitted", [s, f] => if q.permit s f then [[s, f]] else []
    | _, _ => []

private def executeRule : RewriteRule := language.rewrites[0]

private theorem matched_request (s f : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule language
      executeRule (request s f) = [[("f", f), ("s", s)]] := by
  change matchPattern (.apply "Request" [.fvar "s", .fvar "f"])
    (.apply "Request" [s, f]) = _
  simp [matchPattern, matchArgs, mergeBindings]

private theorem prepared_query (q : Queries) (s f : Pattern) :
    relationQueryStep q.relations language [("f", f), ("s", s)] "prepared"
      [.fvar "s", .fvar "f", .fvar "t"] =
      (q.prepare s f).toList.map (fun t => [("t", t), ("f", f), ("s", s)]) := by
  cases found : q.prepare s f <;>
    simp [relationQueryStep, Queries.relations, builtinRelationTuples,
      matchRelationArgs, matchRelationArgument, Bindings.lookup, applyBindings,
      mergeBindings, found]

private theorem permitted_query (q : Queries) (s f t : Pattern) :
    relationQueryStep q.relations language [("t", t), ("f", f), ("s", s)] "permitted"
      [.fvar "s", .fvar "f"] =
      if q.permit s f then [[("t", t), ("f", f), ("s", s)]] else [] := by
  cases found : q.permit s f <;>
    simp [relationQueryStep, Queries.relations, builtinRelationTuples,
      matchRelationArgs, matchRelationArgument, Bindings.lookup, applyBindings,
      mergeBindings, found]

/-- The actual authored rule executes exactly the two queries in sequence. -/
theorem execution (q : Queries) (s f : Pattern) :
    rewriteStepWithPremisesUsing q.relations language (request s f) =
      match q.prepare s f with
      | none => []
      | some t => if q.permit s f then [atState t] else [] := by
  have rules : language.rewrites = [executeRule] := rfl
  have applied (bs : Bindings) :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language executeRule bs = applyBindings bs (.apply "At" [.fvar "t"]) :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings
      language executeRule bs (by decide +kernel)
  simp only [rewriteStepWithPremisesUsing, rules, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, applyRuleWithPremisesUsing, matched_request,
    applied]
  change ((applyPremisesWithEnv q.relations language
    [.relationQuery "prepared" [.fvar "s", .fvar "f", .fvar "t"],
     .relationQuery "permitted" [.fvar "s", .fvar "f"]] [("f", f), ("s", s)]).map
       (fun bs => applyBindings bs (.apply "At" [.fvar "t"]))) = _
  simp only [applyPremisesWithEnv, List.foldl_cons, List.flatMap_singleton,
    premiseStepWithEnv, prepared_query, List.foldl_nil]
  cases prepared : q.prepare s f <;> cases permitted : q.permit s f <;>
    simp [permitted, permitted_query, atState, applyBindings]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
