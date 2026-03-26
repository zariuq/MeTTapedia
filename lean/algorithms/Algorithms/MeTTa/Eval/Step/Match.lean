import Algorithms.MeTTa.Eval.Core
import Algorithms.MeTTa.Eval.Step.Rules

namespace Algorithms.MeTTa.Eval.Step.Match

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Unification: try to match two patterns bidirectionally.
    Returns bindings on success. Simplified: uses one-directional match
    from pattern to term. Full unification would need occurs-check etc. -/
private def unify (a b : Pattern) : Option (List (String × Pattern)) :=
  -- Try matching a against b, then b against a, merge bindings
  match Rules.matchPattern a b with
  | some binds => some binds
  | none => Rules.matchPattern b a

/-- Match and unify operators.

    `match` (3-arg): match pattern against space atoms, apply template
    `match` (2-arg): match pattern against space, return matched atom
    `unify`: structural unification with if-found/if-not-found branches -/
def evalMatch (s : Session) (ctor : String) (args : List Pattern) :
    Option (List Pattern) :=
  match ctor, args with
  -- match (3-arg): (match space pattern template)
  -- For &self space: match pattern against each atom in s.space
  | "match", [_space, pat, tmpl] =>
      let results := s.space.filterMap fun atom =>
        match Rules.matchPattern pat atom with
        | some bindings => some (Rules.applyBindings bindings tmpl)
        | none => none
      if results.isEmpty then none else some results

  -- match (2-arg): (match pattern template) — match against rules
  | "match", [pat, tmpl] =>
      let results := s.space.filterMap fun atom =>
        match Rules.matchPattern pat atom with
        | some bindings => some (Rules.applyBindings bindings tmpl)
        | none => none
      if results.isEmpty then none else some results

  -- unify: (unify atom pattern if-found if-not-found)
  | "unify", [_space, atom, pat, ifFound, ifNotFound] =>
      match unify atom pat with
      | some bindings => some [Rules.applyBindings bindings ifFound]
      | none => some [ifNotFound]

  -- unify (4-arg without space): (unify atom pattern if-found if-not-found)
  | "unify", [atom, pat, ifFound, ifNotFound] =>
      match unify atom pat with
      | some bindings => some [Rules.applyBindings bindings ifFound]
      | none => some [ifNotFound]

  | _, _ => none

end Algorithms.MeTTa.Eval.Step.Match
