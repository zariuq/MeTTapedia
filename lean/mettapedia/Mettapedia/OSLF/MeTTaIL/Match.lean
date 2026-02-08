import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Generic Pattern Matching for MeTTaIL (Locally Nameless)

Pattern matching engine that matches concrete terms against rule LHS patterns,
producing variable bindings. Uses locally nameless representation: α-equivalence
is syntactic equality, so NO alpha-renaming is needed.

## Key Design Decisions

- **Non-deterministic**: Bag matching returns a `List Bindings` (all possible matches),
  since multiset matching can have multiple solutions.
- **No alpha-renaming**: Locally nameless makes α-equivalent patterns identical.
  Lambda matching is purely structural: `lambda bodyPat` vs `lambda bodyConcrete`.
- **Rest variables**: Collection patterns with `some restVar` capture remaining unmatched
  elements as a collection bound to `restVar`.

## References

- mettail-rust: `macros/src/logic/rules.rs` (Ascent Datalog pattern matching)
- Williams & Stay, "Native Type Theory" (ACT 2021)
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
-/

namespace Mettapedia.OSLF.MeTTaIL.Match

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Bindings -/

/-- Variable bindings: maps pattern variable names to concrete terms. -/
abbrev Bindings := List (String × Pattern)

/-- Look up a variable in bindings. -/
def Bindings.lookup (b : Bindings) (name : String) : Option Pattern :=
  b.find? (·.1 == name) |>.map (·.2)

/-- Merge two binding sets. Fails (returns `none`) if they assign
    different values to the same variable. -/
def mergeBindings (b1 b2 : Bindings) : Option Bindings :=
  b2.foldlM (init := b1) fun acc (name, val) =>
    match acc.find? (·.1 == name) with
    | none => some ((name, val) :: acc)
    | some (_, existing) => if existing == val then some acc else none

/-! ## Pattern Matching

The three mutually-dependent functions: matchPattern (single term),
matchArgs (argument list), matchBag (multiset).

In locally nameless, lambda matching is purely structural — no renaming
needed. FVars (metavariables) match anything and produce bindings.
BVars must match structurally (same index). -/

mutual
/-- Match argument lists pairwise, merging bindings. -/
def matchArgs : List Pattern → List Pattern → List Bindings
  | [], [] => [[]]
  | p :: ps, t :: ts =>
    (matchPattern p t).flatMap fun hb =>
      (matchArgs ps ts).filterMap fun tb =>
        mergeBindings hb tb
  | _, _ => []
termination_by pats => sizeOf pats

/-- Multiset matching: find all ways to match pattern elements against term elements.
    If `restVar` is `some v`, unmatched term elements are bound to `v` as a collection.
    This generalizes `findAllComm` from `RhoCalculus/Engine.lean`. -/
def matchBag : List Pattern → Option String → CollType → List Pattern → List Bindings
  | [], restVar, ct, termElems =>
    match restVar with
    | none => if termElems.isEmpty then [[]] else []
    | some rv => [[(rv, .collection ct termElems none)]]
  | ppat :: prest, restVar, ct, termElems =>
    termElems.zipIdx.flatMap fun (telem, i) =>
      (matchPattern ppat telem).flatMap fun hb =>
        let remaining := termElems.eraseIdx i
        (matchBag prest restVar ct remaining).filterMap fun restB =>
          mergeBindings hb restB
termination_by ppats => sizeOf ppats

/-- Match a concrete term against a pattern, producing all valid binding sets.

    Returns `[]` if the match fails, or a list of possible bindings (usually
    singleton for non-collection patterns, multiple for bag matching).

    - `FVar x` (metavariable) matches any term, binding `x` to it.
    - `BVar n` matches only `BVar n` (structural).
    - `lambda bodyPat` matches `lambda bodyConcrete` by matching bodies.
      No alpha-renaming needed — locally nameless makes this structural. -/
def matchPattern (pat term : Pattern) : List Bindings :=
  match pat, term with
  | .fvar x, t => [[(x, t)]]
  | .bvar n, .bvar m => if n == m then [[]] else []
  | .apply c1 pargs, .apply c2 targs =>
    if c1 == c2 && pargs.length == targs.length then
      matchArgs pargs targs
    else []
  | .lambda bodyPat, .lambda bodyConcrete =>
    matchPattern bodyPat bodyConcrete
  | .multiLambda npat bodyPat, .multiLambda nconc bodyConcrete =>
    if npat == nconc then matchPattern bodyPat bodyConcrete
    else []
  | .collection ct1 pelems rest1, .collection ct2 telems _rest2 =>
    if ct1 == ct2 then matchBag pelems rest1 ct1 telems
    else []
  | .subst pbody prepl, .subst tbody trepl =>
    (matchPattern pbody tbody).flatMap fun b1 =>
      (matchPattern prepl trepl).filterMap fun b2 =>
        mergeBindings b1 b2
  | _, _ => []
termination_by sizeOf pat
end

/-! ## Applying Bindings to RHS -/

/-- Apply variable bindings to a pattern (the RHS of a rule).
    Replaces free variables (metavariables) with their bound values.
    Evaluates `subst` nodes by calling `openBVar`. -/
def applyBindings (bindings : Bindings) (rhs : Pattern) : Pattern :=
  match rhs with
  | .fvar x =>
    match bindings.find? (·.1 == x) with
    | some (_, val) => val
    | none => .fvar x
  | .bvar n => .bvar n
  | .apply c args =>
    .apply c (args.map (applyBindings bindings))
  | .lambda body =>
    .lambda (applyBindings bindings body)
  | .multiLambda n body =>
    .multiLambda n (applyBindings bindings body)
  | .subst body repl =>
    -- Apply bindings to both parts, then substitute via openBVar
    let body' := applyBindings bindings body
    let repl' := applyBindings bindings repl
    openBVar 0 repl' body'
  | .collection ct elems rest =>
    let elems' := elems.map (applyBindings bindings)
    let restElems := match rest with
      | some rv =>
        match bindings.find? (·.1 == rv) with
        | some (_, .collection _ relems _) => relems
        | _ => []
      | none => []
    .collection ct (elems' ++ restElems) none
termination_by sizeOf rhs

/-! ## Rule Application -/

/-- Apply a single rewrite rule to a term (top-level match only).
    Returns all possible reducts. Skips rules with premises (congruence
    premises require recursive reduction, handled by the full engine). -/
def applyRule (rule : RewriteRule) (term : Pattern) : List Pattern :=
  if rule.premises.isEmpty then
    (matchPattern rule.left term).map fun b => applyBindings b rule.right
  else []

/-- Apply all rewrite rules from a LanguageDef to a term (top-level).
    Returns all possible reducts from all applicable rules. -/
def rewriteStep (lang : LanguageDef) (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRule rule term

/-- Reduce to normal form (deterministic: pick first reduct, with fuel). -/
def rewriteToNormalForm (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteStep lang term with
    | [] => term
    | q :: _ => rewriteToNormalForm lang q fuel

end Mettapedia.OSLF.MeTTaIL.Match
