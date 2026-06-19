import Mettapedia.Languages.MeTTa.HE.Space

/-!
# HE MeTTa Matching

Bidirectional atom matching and bindings operations for the HE interpreter.
Follows metta.md sections "Match atoms", "Merge bindings", "Add variable binding",
"Add variable equality" (lines 577-683).

## Source Precedence
1. `interpreter.rs` (ground truth)
2. `metta.md` lines 577-683 (spec)

## Main Definitions
* `matchAtoms` - Bidirectional atom unification (metta.md lines 577-617)
* `mergeBindings` - Merge two binding sets (metta.md lines 619-636)
* `addVarBinding` - Add variable assignment (metta.md lines 638-658)
* `addVarEquality` - Add variable equality (metta.md lines 661-683)
* `matchTypes` - Type matching with %Undefined%/Atom wildcards (metta.md lines 298-314)
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Match Atoms and Bindings Operations

These four functions are mutually recursive (match_atoms calls merge_bindings
via add_var_binding, and merge_bindings iterates add_var_binding/add_var_equality).
We implement them as a `mutual` block with shared fuel. -/

mutual

/-- Bidirectional atom matching (unification).
    Ref: metta.md lines 577-617 "Match atoms (match_atoms)".

    Returns a list of binding sets (multiple possible when grounded custom
    matching is involved). Empty list = match failure. -/
def matchAtoms (left right : Atom) (fuel : Nat) : List Bindings :=
  match fuel with
  | 0 => []
  | n + 1 =>
    let ml := getMetaType left
    let mr := getMetaType right
    let result :=
      if ml == .symbol "Symbol" && mr == .symbol "Symbol" && left == right then
        -- Both symbols, same value → match with empty bindings
        [Bindings.empty]
      else if ml == .symbol "Variable" && mr == .symbol "Variable" then
        -- Both variables → record equality
        match left, right with
        | .var a, .var b => [Bindings.empty.addEquality a b]
        | _, _ => []  -- impossible given metatype check
      else if ml == .symbol "Variable" then
        -- Left is variable → assign right to left
        match left with
        | .var v => [Bindings.empty.assign v right]
        | _ => []
      else if mr == .symbol "Variable" then
        -- Right is variable → assign left to right
        match right with
        | .var v => [Bindings.empty.assign v left]
        | _ => []
      else if ml == .symbol "Expression" && mr == .symbol "Expression" then
        -- Both expressions → match element-wise
        match left, right with
        | .expression ls, .expression rs =>
          if ls.length == rs.length then
            matchAtomsList ls rs [Bindings.empty] n
          else []
        | _, _ => []
      else if ml == .symbol "Grounded" && mr == .symbol "Grounded" then
        -- Spec vs implementation divergence (author question):
        -- The published spec (metta.md) returns `[{}]` here (always succeeds),
        -- but this fallback is unreachable in practice because all grounded
        -- atoms in interpreter.rs have custom matchers that use equality.
        -- We follow the implementation behavior (structural equality) since
        -- it matches `metta` CLI conformance testing. The spec's `[{}]`
        -- fallback would make `(match 42 43)` succeed, which no user expects.
        if left == right then [Bindings.empty] else []
      else
        -- All other cases → no match
        []
    -- Filter out bindings with variable loops (metta.md line 616)
    result.filter fun b => !b.hasLoop

/-- Match lists of atoms element-wise, threading bindings through merges.
    Helper for matchAtoms on expressions.
    Ref: metta.md lines 599-606. -/
def matchAtomsList (lefts rights : List Atom) (acc : List Bindings) (fuel : Nat) : List Bindings :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match lefts, rights with
    | [], [] => acc
    | l :: ls, r :: rs =>
      let sub := matchAtoms l r n
      let next := acc.flatMap fun a =>
        sub.flatMap fun b =>
          mergeBindings a b n
      matchAtomsList ls rs next n
    | _, _ => []  -- length mismatch (shouldn't happen, checked by caller)

/-- Merge two binding sets.
    Ref: metta.md lines 619-636 "Merge bindings (merge_bindings)".

    Iterates over relations in `right`, applying each to `left` via
    `addVarBinding` (for assignments) or `addVarEquality` (for equalities). -/
def mergeBindings (left right : Bindings) (fuel : Nat) : List Bindings :=
  match fuel with
  | 0 => []
  | n + 1 =>
    -- First process assignments from right
    let afterAssignments := right.assignments.foldl (fun acc (v, val) =>
      acc.flatMap fun b => addVarBinding b v val n
    ) [left]
    -- Then process equalities from right
    right.equalities.foldl (fun acc (a, b) =>
      acc.flatMap fun binds => addVarEquality binds a b n
    ) afterAssignments

/-- Add a variable binding to a binding set.
    Ref: metta.md lines 638-658 "Add variable binding (add_var_binding)".

    If variable already has a value:
    - If same value → keep unchanged
    - If different → match old and new values, merge results -/
def addVarBinding (b : Bindings) (v : String) (val : Atom) (fuel : Nat) : List Bindings :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match b.lookup v with
    | none =>
      -- Variable not bound → simple assignment
      [b.assign v val]
    | some prev =>
      if prev == val then
        -- Same value → no change
        [b]
      else
        -- Different value → match old and new, merge results
        let matched := matchAtoms prev val n
        matched.flatMap fun mb =>
          mergeBindings b mb n

/-- Add a variable equality to a binding set.
    Ref: metta.md lines 661-683 "Add variable equality (add_var_equality)".

    If both variables have values:
    - If same value → record equality
    - If different → match values, merge results
    If at most one has a value → record equality directly. -/
def addVarEquality (b : Bindings) (a c : String) (fuel : Nat) : List Bindings :=
  match fuel with
  | 0 => []
  | n + 1 =>
    let aVal := b.lookup a
    let cVal := b.lookup c
    match aVal, cVal with
    | none, _ | _, none =>
      -- At most one has a value → record equality
      -- Remove c's binding if it exists, add equality a = c
      [b.removeAssignment c |>.addEquality a c]
    | some av, some cv =>
      if av == cv then
        -- Same value → record equality
        [b.removeAssignment c |>.addEquality a c]
      else
        -- Different values → match them, merge results
        let matched := matchAtoms av cv n
        matched.flatMap fun mb =>
          mergeBindings b mb n

end

/-! ## Match Types

Ref: metta.md lines 298-314 "Match types (match_types)".
Special handling for `%Undefined%` and `Atom` which match anything. -/

/-- Match two types, returning resulting bindings on success.
    Ref: metta.md lines 298-314.

    Special cases:
    - `%Undefined%` on either side → always matches
    - `Atom` on either side → always matches
    - Otherwise → delegate to `matchAtoms` -/
def matchTypes (type1 type2 : Atom) (b : Bindings) (fuel : Nat := 100) : List Bindings :=
  if type1 == Atom.undefinedType || type1 == Atom.atomType
     || type2 == Atom.undefinedType || type2 == Atom.atomType then
    [b]
  else
    let matched := matchAtoms type1 type2 fuel
    matched.flatMap fun mb =>
      mergeBindings b mb fuel

/-! ## Primitive `unify` result lane

This is the raw success-side payload computed by upstream HE's primitive
`unify`: structural matcher results merged with the incoming bindings, with
loopy merged bindings filtered, and the surviving merged bindings substituted
into the success branch.

The caller is responsible for the final else-branch fallback when this list is
empty; upstream does that after the merge/filter pass, not before. -/

/-- Raw success results for the primitive `unify` lane, before the caller's
    final else-branch fallback. -/
def unifySuccessResults
    (target pattern thenBranch : Atom) (seed : Bindings) (fuel : Nat) :
    ResultSet :=
  (matchAtoms target pattern fuel).flatMap fun matchBindings =>
    (mergeBindings matchBindings seed fuel).filterMap fun merged =>
      if merged.hasLoop then none
      else some (merged.applyDefault thenBranch, merged)

/-! ## Control-form structural helpers

These helpers factor the purely structural parts of HE control builtins so the
contracts, premise tables, and proof bridge can all point at the same small
kernel.  They intentionally stop before evaluation. -/

/-- Parse either `(switch <scrutinee> <rawCases>)` or
    `(switch-minimal <scrutinee> <rawCases>)`, returning the packed pair
    `(<scrutinee> <rawCases>)` expected by the HE premise layer. -/
def parseSwitchMinimalCallArgs : Atom → Option Atom
  | .expression [.symbol "switch-minimal", scrutinee, rawCases] =>
      some (.expression [scrutinee, rawCases])
  | .expression [.symbol "switch", scrutinee, rawCases] =>
      some (.expression [scrutinee, rawCases])
  | _ => none

/-- Predicate helper for the explicit `NotReducible` sentinel returned by the
    structural switch selector when no branch matches. -/
def checkIsNotReducible (atom : Atom) : Bool :=
  atom == Atom.notReducible

/-- Positive complement of `checkIsNotReducible`. -/
def checkIsReducible (atom : Atom) : Bool :=
  !(checkIsNotReducible atom)

/-- First successful `switch-minimal` branch together with the branch-local
    bindings that selected it.  Unlike the coarse `NotReducible`-sentinel
    selector below, this helper keeps genuine "matched template is literally
    NotReducible" distinct from "no branch matched". -/
def selectSwitchResultPair?
    (scrut : Atom) (branches : List Atom) (fuel : Nat) : Option ResultPair :=
  match branches with
  | [] => none
  | .expression [pt, template] :: rest =>
      match simpleMatch pt scrut Bindings.empty fuel with
      | some mb => some (mb.applyDefault template, mb)
      | none => selectSwitchResultPair? scrut rest fuel
  | _ :: rest => selectSwitchResultPair? scrut rest fuel

/-- Coarse first-match selector for `switch-minimal` on the raw structural
    fragment: scan the branch list left-to-right, skip malformed branches, and
    return the substituted template from the first well-formed matching branch.
    If no branch matches, return the explicit `NotReducible` sentinel.

    This is intentionally a selector, not an evaluator: it chooses a branch
    result but does not continue evaluating that chosen template. -/
def selectSwitchTemplateCoarse
    (scrut : Atom) (branches : List Atom) (fuel : Nat) : Atom :=
  match selectSwitchResultPair? scrut branches fuel with
  | some (result, _) => result
  | none => Atom.notReducible

/-- Raw result set for `switch-minimal` before the outer stdlib
    `if-equal ... NotReducible Empty ...` post-processing.

    The scan is left-to-right over the branch list:
    - malformed branches are skipped;
    - on the first well-formed branch whose coarse match succeeds,
      the branch-local matcher bindings are merged with the incoming seed;
    - if that merge/filter lane yields no surviving results, the scan
      continues with the remaining branches, exactly like upstream
      `switch-internal` following `unify`'s else branch.

    This is still a raw branch-and-bind helper: it does not collapse
    `NotReducible` to `Empty`. -/
def switchMinimalRawResults
    (scrut : Atom) (branches : List Atom) (seed : Bindings) (fuel : Nat) :
    ResultSet :=
  match branches with
  | [] => []
  | .expression [pt, template] :: rest =>
      match simpleMatch pt scrut Bindings.empty fuel with
      | some mb =>
          let hits :=
            (mergeBindings mb seed fuel).filterMap fun merged =>
              if merged.hasLoop then none
              else some (merged.applyDefault template, merged)
          if hits.isEmpty then
            switchMinimalRawResults scrut rest seed fuel
          else
            hits
      | none => switchMinimalRawResults scrut rest seed fuel
  | _ :: rest => switchMinimalRawResults scrut rest seed fuel

/-- Final observable result set for `switch-minimal`, after the stdlib's
    outer `if-equal` converts a raw `NotReducible` witness into `Empty`.

    If no branch produces any surviving raw result, upstream `switch-minimal`
    also yields `Empty` under the original seed. -/
def switchMinimalResults
    (scrut : Atom) (branches : List Atom) (seed : Bindings) (fuel : Nat) :
    ResultSet :=
  let raw := switchMinimalRawResults scrut branches seed fuel
  if raw.isEmpty then
    [(Atom.empty, seed)]
  else
    raw.map fun (result, rb) =>
      (if result == Atom.notReducible then Atom.empty else result, rb)

/-! ## Theorems -/

/-- matchTypes with %Undefined% on left always succeeds.
    Ref: metta.md line 309. -/
theorem matchTypes_undefined_left (t : Atom) (b : Bindings) :
    matchTypes Atom.undefinedType t b = [b] := by
  unfold matchTypes Atom.undefinedType
  simp [BEq.beq, Atom.beq]

/-- matchTypes with Atom on right always succeeds.
    Ref: metta.md line 310. -/
theorem matchTypes_atom_right (t : Atom) (b : Bindings) :
    matchTypes t Atom.atomType b = [b] := by
  unfold matchTypes Atom.atomType
  simp [BEq.beq, Atom.beq]

/-! ## Unit Tests -/

section Tests

-- matchAtoms basics
example : matchAtoms (.symbol "a") (.symbol "a") 10 = [Bindings.empty] := rfl
example : matchAtoms (.symbol "a") (.symbol "b") 10 = [] := rfl
example : matchAtoms (.var "x") (.symbol "a") 10 =
    [Bindings.empty.assign "x" (.symbol "a")] := rfl

-- matchAtoms with two variables → equality
example : matchAtoms (.var "x") (.var "y") 10 =
    [Bindings.empty.addEquality "x" "y"] := rfl

-- matchAtoms with expressions
example : matchAtoms (.expression [.symbol "a", .symbol "b"])
                     (.expression [.symbol "a", .symbol "b"]) 10 =
    [Bindings.empty] := rfl
example : matchAtoms (.expression [.symbol "a"])
                     (.expression [.symbol "a", .symbol "b"]) 10 = [] := rfl

-- matchTypes
example : matchTypes Atom.undefinedType (.symbol "Int") Bindings.empty = [Bindings.empty] := rfl
example : matchTypes (.symbol "Int") Atom.atomType Bindings.empty = [Bindings.empty] := rfl
example : matchTypes (.symbol "Int") (.symbol "Int") Bindings.empty = [Bindings.empty] := rfl
example : matchTypes (.symbol "Int") (.symbol "Bool") Bindings.empty = [] := rfl

-- switch-minimal selector
example : parseSwitchMinimalCallArgs
    (.expression [.symbol "switch-minimal", .symbol "A", .expression []]) =
      some (.expression [.symbol "A", .expression []]) := rfl
example : parseSwitchMinimalCallArgs
    (.expression [.symbol "switch", .symbol "A", .expression []]) =
      some (.expression [.symbol "A", .expression []]) := rfl
example : parseSwitchMinimalCallArgs (.expression [.symbol "switch", .symbol "A"]) = none := rfl
example : checkIsNotReducible Atom.notReducible = true := rfl
example : checkIsReducible Atom.notReducible = false := rfl
example : selectSwitchResultPair? (.symbol "z")
    [.expression [.var "x", .expression [.symbol "tag", .var "x"]]] 10 =
      some (.expression [.symbol "tag", .symbol "z"],
        Bindings.empty.assign "x" (.symbol "z")) := rfl
example : selectSwitchResultPair? (.symbol "A")
    [.expression [.symbol "B", .symbol "miss"]] 10 = none := rfl
example : selectSwitchTemplateCoarse (.symbol "A")
    [.expression [.symbol "A", .symbol "ok"]] 10 = .symbol "ok" := rfl
example : selectSwitchTemplateCoarse (.symbol "A")
    [.symbol "bogus", .expression [.symbol "A", .symbol "ok"]] 10 = .symbol "ok" := rfl
example : selectSwitchTemplateCoarse (.symbol "A")
    [.expression [.symbol "B", .symbol "miss"]] 10 = Atom.notReducible := rfl

-- mergeBindings
example : mergeBindings Bindings.empty Bindings.empty 10 = [Bindings.empty] := rfl
example : mergeBindings Bindings.empty (Bindings.empty.assign "x" (.symbol "a")) 10 =
    [Bindings.empty.assign "x" (.symbol "a")] := rfl

-- addVarBinding: new variable
example : addVarBinding Bindings.empty "x" (.symbol "a") 10 =
    [Bindings.empty.assign "x" (.symbol "a")] := rfl

-- addVarBinding: same value
example : addVarBinding (Bindings.empty.assign "x" (.symbol "a")) "x" (.symbol "a") 10 =
    [Bindings.empty.assign "x" (.symbol "a")] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
