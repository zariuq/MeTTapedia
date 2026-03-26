import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.Rules

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Match pattern against term with binding consistency. -/
partial def matchPatternWith (bindings : List (String × Pattern)) :
    Pattern → Pattern → Option (List (String × Pattern))
  | .fvar name, t =>
      match bindings.find? (fun (n, _) => n == name) with
      | some (_, existing) => if existing == t then some bindings else none
      | none => some ((name, t) :: bindings)
  | .apply c1 args1, .apply c2 args2 =>
      if c1 == c2 && args1.length == args2.length then
        (args1.zip args2).foldlM (fun acc (p, t) =>
          matchPatternWith acc p t) bindings
      else none
  | _, _ => none

def matchPattern (pattern term : Pattern) : Option (List (String × Pattern)) :=
  matchPatternWith [] pattern term

partial def applyBindings (bindings : List (String × Pattern)) : Pattern → Pattern
  | .fvar name =>
      match bindings.find? (fun (n, _) => n == name) with
      | some (_, val) => val
      | none => .fvar name
  | .apply ctor args => .apply ctor (args.map (applyBindings bindings))
  | .lambda body => .lambda (applyBindings bindings body)
  | other => other

private partial def specificity : Pattern → Nat
  | .fvar _ => 0
  | .apply _ args => 1 + args.foldl (fun acc a => acc + specificity a) 0
  | _ => 1

/-- Check if pattern has free variables (is a guard/constraint). -/
partial def hasFreeVars : Pattern → Bool
  | .fvar _ => true
  | .apply _ args => args.any hasFreeVars
  | _ => false

/-- Simple rule step for headStep? (no guard evaluation). -/
def ruleStep (s : Session) (term : Pattern) : Option (List Pattern) :=
  let hits := s.rules.filterMap fun rule =>
    match matchPattern rule.left term with
    | some bindings => some (specificity rule.left, applyBindings bindings rule.right)
    | none => none
  if hits.isEmpty then none
  else
    let maxSpec := hits.foldl (fun best (spec, _) => max best spec) 0
    let results := hits.filter (fun (spec, _) => spec == maxSpec) |>.map Prod.snd
    some results

end Algorithms.MeTTa.Eval.Step.Rules
