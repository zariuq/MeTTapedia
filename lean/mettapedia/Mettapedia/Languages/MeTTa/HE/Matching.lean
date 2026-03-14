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
