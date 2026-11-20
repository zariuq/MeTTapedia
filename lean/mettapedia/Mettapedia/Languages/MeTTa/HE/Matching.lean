import Mettapedia.Languages.MeTTa.HE.SimpleMatch
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
import Mettapedia.Machines.ReadOnlyQuery

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

    Every proposed value is checked against all values carried by the
    variable's equality class; unequal but unifiable values retain every
    reconciliation constraint. Matcher-produced variable/variable relations
    reach this layer as explicit equalities, not assignments. -/
def addVarBinding (b : Bindings) (v : String) (val : Atom) (fuel : Nat) : List Bindings :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match b.classValues v with
    | [] => [b.assign v val]
    | first :: rest =>
      if Bindings.valuesConsistent (first :: rest) then
        if first == val then [b]
        else
          let matched := matchAtoms first val n
          matched.flatMap fun mb => mergeBindings b mb n
      else
        let allValues := first :: rest ++ [val]
        match allValues with
        | [] => []
        | representative :: others =>
          let matched :=
            matchAtomsList (List.replicate others.length representative) others
              [Bindings.empty] n
          matched.flatMap fun mb => mergeBindings b mb n

/-- Add a variable equality to a binding set.
    Ref: metta.md lines 661-683 "Add variable equality (add_var_equality)".

    Existing values remain attached to the joined equality class. Every class
    value is checked; unequal but unifiable values retain every reconciliation
    constraint in the equality-bearing candidate. This is the record-model
    counterpart of upstream's binding-group merge. -/
def addVarEquality (b : Bindings) (a c : String) (fuel : Nat) : List Bindings :=
  match fuel with
  | 0 => []
  | n + 1 =>
    let candidate := b.addEquality a c
    let values := candidate.classValues a
    if Bindings.valuesConsistent values then [candidate]
    else
      match values with
      | [] => []
      | first :: [second] =>
        let matched := matchAtoms first second n
        matched.flatMap fun mb => mergeBindings candidate mb n
      | first :: rest =>
        let matched := matchAtomsList (List.replicate rest.length first) rest
          [Bindings.empty] n
        matched.flatMap fun mb => mergeBindings candidate mb n

end


/-! ## Checked recursion depth

These dependency programs expose one layer of the existing matcher. A coverage
check visits every recursive call that produced the answer, including empty
answers. Its stability theorem applies to all larger depths, so the caller can
distinguish completed failure from a search truncated by fuel.
-/

inductive MatchRequest where
  | atoms (left right : Atom)
  | lists (lefts rights : List Atom) (acc : List Bindings)
  | merge (left right : Bindings)
  | binding (bindings : Bindings) (name : String) (value : Atom)
  | equality (bindings : Bindings) (left right : String)

def evalMatch (depth : Nat) : MatchRequest → List Bindings
  | .atoms left right => matchAtoms left right depth
  | .lists lefts rights acc => matchAtomsList lefts rights acc depth
  | .merge left right => mergeBindings left right depth
  | .binding bindings name value => addVarBinding bindings name value depth
  | .equality bindings left right => addVarEquality bindings left right depth

/-! ## Unitary equality matching -/

/-- Equality-based unification does not introduce alternatives. List matching
may receive several existing seeds, each of which contributes at most one
result. Custom grounded matching is a separate source profile. -/
def MatchRequest.branchBound : MatchRequest → Nat
  | .lists _ _ seeds => seeds.length
  | _ => 1

private theorem flatMap_length_le (rows : List α) (next : α → List β)
    (each : ∀ row ∈ rows, (next row).length ≤ 1) :
    (rows.flatMap next).length ≤ rows.length := by
  induction rows with
  | nil => simp
  | cons head tail ih =>
      have first := each head List.mem_cons_self
      have rest := ih (fun row member => each row (List.mem_cons_of_mem _ member))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega

private theorem foldl_length_le (items : List α) (initial : List β)
    (step : List β → α → List β)
    (each : ∀ rows item, (step rows item).length ≤ rows.length) :
    (items.foldl step initial).length ≤ initial.length := by
  induction items generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact (ih (step initial head)).trans (each initial head)

/-- A complete or depth-truncated equality matcher can remove a seed but
cannot duplicate it. The bound holds for arbitrary incoming aliases and
relation-list presentations, without assuming successful unification. -/
theorem evalMatch_length_le (depth : Nat) (request : MatchRequest) :
    (evalMatch depth request).length ≤ request.branchBound := by
  induction depth generalizing request with
  | zero => cases request <;> simp [evalMatch,matchAtoms,matchAtomsList,mergeBindings,
      addVarBinding,addVarEquality,MatchRequest.branchBound]
  | succ depth ih =>
      have flatten (rows : List Bindings) (next : Bindings → MatchRequest)
          (bound : ∀ row, (next row).branchBound ≤ 1) :
          (rows.flatMap fun row => evalMatch depth (next row)).length ≤ rows.length :=
        flatMap_length_le rows _ (fun row _ => (ih (next row)).trans (bound row))
      cases request with
      | atoms left right =>
          change (matchAtoms left right (depth+1)).length ≤ 1
          conv_lhs => unfold matchAtoms
          apply Nat.le_trans (List.length_filter_le ..)
          repeat' first
            | exact ih (.lists _ _ [Bindings.empty])
            | (simp only [List.length_nil,List.length_cons]; omega)
            | split
      | lists left right seeds =>
          change (matchAtomsList left right seeds (depth+1)).length ≤ seeds.length
          cases left with
          | nil => cases right <;> simp [matchAtomsList]
          | cons head left =>
              cases right with
              | nil => simp [matchAtomsList]
              | cons other right =>
                  conv_lhs => unfold matchAtomsList
                  apply (ih (.lists left right _)).trans
                  apply flatMap_length_le
                  intro seed _
                  exact (flatten (matchAtoms head other depth) (fun matched => .merge seed matched)
                    (fun _ => Nat.le_refl _)).trans (ih (.atoms head other))
      | merge left right =>
          change (mergeBindings left right (depth+1)).length ≤ 1
          conv_lhs => unfold mergeBindings
          apply Nat.le_trans (foldl_length_le right.equalities _ _ ?_)
          · exact foldl_length_le right.assignments [left] _ (by
              intro rows item
              exact flatten rows (fun row => .binding row item.1 item.2) (fun _ => Nat.le_refl _))
          · intro rows item
            exact flatten rows (fun row => .equality row item.1 item.2) (fun _ => Nat.le_refl _)
      | binding bindings name value =>
          change (addVarBinding bindings name value (depth+1)).length ≤ 1
          conv_lhs => unfold addVarBinding
          split
          · simp
          · split
            · split
              · simp
              · exact (flatten _ (fun row => .merge bindings row) (fun _ => Nat.le_refl _)).trans
                  (ih (.atoms _ _))
            · exact (flatten _ (fun row => .merge bindings row) (fun _ => Nat.le_refl _)).trans
                (ih (.lists _ _ [Bindings.empty]))
      | equality bindings left right =>
          change (addVarEquality bindings left right (depth+1)).length ≤ 1
          conv_lhs => unfold addVarEquality
          dsimp only
          split
          · simp
          · split
            · simp
            · exact (flatten _ (fun row => .merge (bindings.addEquality left right) row)
                (fun _ => Nat.le_refl _)).trans (ih (.atoms _ _))
            · exact (flatten _ (fun row => .merge (bindings.addEquality left right) row)
                (fun _ => Nat.le_refl _)).trans (ih (.lists _ _ [Bindings.empty]))

theorem matchAtoms_length_le_one (left right : Atom) (depth : Nat) :
    (matchAtoms left right depth).length ≤ 1 := evalMatch_length_le depth (.atoms left right)

theorem mergeBindings_length_le_one (left right : Bindings) (depth : Nat) :
    (mergeBindings left right depth).length ≤ 1 := evalMatch_length_le depth (.merge left right)

namespace MatchDepth

private abbrev Q := Mettapedia.Machines.ReadOnlyQuery.Program MatchRequest (List Bindings)
private abbrev read (request : MatchRequest) : Q (List Bindings) := .read request .pure
private abbrev bind := @Mettapedia.Machines.ReadOnlyQuery.bind
private abbrev map := @Mettapedia.Machines.ReadOnlyQuery.map
private abbrev flatTraverse := @Mettapedia.Machines.ReadOnlyQuery.flatTraverse
private abbrev foldQueries := @Mettapedia.Machines.ReadOnlyQuery.foldQueries

/-- Matcher candidates before the actual fixed-depth cycle filter. -/
def rawAtoms (left right : Atom) : Q (List Bindings) :=
  let ml := getMetaType left
  let mr := getMetaType right
  if ml == .symbol "Symbol" && mr == .symbol "Symbol" && left == right then
    .pure [Bindings.empty]
  else if ml == .symbol "Variable" && mr == .symbol "Variable" then
    match left, right with
    | .var a, .var b => .pure [Bindings.empty.addEquality a b]
    | _, _ => .pure []
  else if ml == .symbol "Variable" then
    match left with
    | .var v => .pure [Bindings.empty.assign v right]
    | _ => .pure []
  else if mr == .symbol "Variable" then
    match right with
    | .var v => .pure [Bindings.empty.assign v left]
    | _ => .pure []
  else if ml == .symbol "Expression" && mr == .symbol "Expression" then
    match left, right with
    | .expression ls, .expression rs =>
        if ls.length == rs.length then read (.lists ls rs [Bindings.empty])
        else .pure []
    | _, _ => .pure []
  else if ml == .symbol "Grounded" && mr == .symbol "Grounded" then
    .pure (if left == right then [Bindings.empty] else [])
  else .pure []

/-- A structural exposure of actual recursive calls, not a second matcher. -/
def body : MatchRequest → Q (List Bindings)
  | .atoms left right => map (List.filter fun b => !b.hasLoop) (rawAtoms left right)
  | .lists lefts rights acc =>
      match lefts, rights with
      | [], [] => .pure acc
      | l :: ls, r :: rs =>
          bind (read (.atoms l r)) fun sub =>
          bind (flatTraverse acc fun a =>
            flatTraverse sub fun b => read (.merge a b)) fun next =>
          read (.lists ls rs next)
      | _, _ => .pure []
  | .merge left right =>
      bind (foldQueries right.assignments [left] fun acc (v, val) =>
        flatTraverse acc fun b => read (.binding b v val)) fun afterAssignments =>
      foldQueries right.equalities afterAssignments fun acc (a, b) =>
        flatTraverse acc fun binds => read (.equality binds a b)
  | .binding b v val =>
      match b.classValues v with
      | [] => .pure [b.assign v val]
      | first :: rest =>
          if Bindings.valuesConsistent (first :: rest) then
            if first == val then .pure [b]
            else bind (read (.atoms first val)) fun matched =>
              flatTraverse matched fun mb => read (.merge b mb)
          else
            match first :: rest ++ [val] with
            | [] => .pure []
            | representative :: others =>
                bind (read (.lists (List.replicate others.length representative) others
                  [Bindings.empty])) fun matched =>
                flatTraverse matched fun mb => read (.merge b mb)
  | .equality b a c =>
      let candidate := b.addEquality a c
      let values := candidate.classValues a
      if Bindings.valuesConsistent values then .pure [candidate]
      else
        match values with
        | [] => .pure []
        | first :: [second] =>
            bind (read (.atoms first second)) fun matched =>
            flatTraverse matched fun mb => read (.merge candidate mb)
        | first :: rest =>
            bind (read (.lists (List.replicate rest.length first) rest
              [Bindings.empty])) fun matched =>
            flatTraverse matched fun mb => read (.merge candidate mb)

open Mettapedia.Machines.ReadOnlyQuery in
/-- The exposed dependencies execute exactly one layer of the original code. -/
theorem unfold_eval (depth : Nat) (request : MatchRequest) :
    evalMatch (depth + 1) request = (run (evalMatch depth) (body request)).answer := by
  cases request with
  | atoms left right =>
      conv_lhs => unfold evalMatch; unfold matchAtoms
      simp only [body, rawAtoms, map, run_map]
      split <;> try rfl
      all_goals split <;> try rfl
      all_goals split <;> try rfl
      all_goals split <;> try rfl
      all_goals split <;> try rfl
      all_goals split <;> try rfl
      all_goals split <;> rfl
  | lists lefts rights acc =>
      conv_lhs => unfold evalMatch; unfold matchAtomsList
      cases lefts <;> cases rights <;>
        simp [body, bind, read, flatTraverse, run_bind, run_flatTraverse, run, evalMatch]
  | merge left right =>
      conv_lhs => unfold evalMatch; unfold mergeBindings
      simp [body, bind, read, foldQueries, flatTraverse, run_bind,
        run_foldQueries, run_flatTraverse, run, evalMatch]
  | binding bindings name value =>
      conv_lhs => unfold evalMatch; unfold addVarBinding
      simp only [body]
      split <;> try rfl
      split <;> try rfl
      · split <;> try rfl
        simp [bind, read, flatTraverse, run_bind, run_flatTraverse, run, evalMatch]
      · simp [bind, read, flatTraverse, run_bind, run_flatTraverse, run, evalMatch]
  | equality bindings left right =>
      conv_lhs => unfold evalMatch; unfold addVarEquality
      simp only [body]
      split <;> try rfl
      split <;> try rfl
      all_goals simp [bind, read, flatTraverse, run_bind, run_flatTraverse, run, evalMatch]

end MatchDepth

/-- Executable evidence that no recursive matcher invocation hit depth zero. -/
def matchCovered (depth : Nat) (request : MatchRequest) : Bool :=
  Mettapedia.Machines.ReadOnlyQuery.depthCovered MatchDepth.body evalMatch depth request

theorem matchCovered_stable (depth extra : Nat) (request : MatchRequest)
    (covered : matchCovered depth request = true) :
    evalMatch (depth + extra) request = evalMatch depth request :=
  Mettapedia.Machines.ReadOnlyQuery.depthCovered_stable
    MatchDepth.body evalMatch MatchDepth.unfold_eval depth extra request covered

theorem matchCovered_mono (depth extra : Nat) (request : MatchRequest)
    (covered : matchCovered depth request = true) :
    matchCovered (depth + extra) request = true :=
  Mettapedia.Machines.ReadOnlyQuery.depthCovered_mono
    MatchDepth.body evalMatch MatchDepth.unfold_eval depth extra request covered

namespace MatchDepth.Controls

/-- A completed mismatch is licensed even though its answer is empty. -/
theorem mismatch_covered : matchCovered 1 (.atoms (.symbol "a") (.symbol "b")) = true := by
  decide +kernel

/-- The same empty answer at depth zero is not a completed mismatch. -/
theorem exhausted_not_covered :
    evalMatch 0 (.atoms (.symbol "a") (.symbol "a")) = [] ∧
      matchCovered 0 (.atoms (.symbol "a") (.symbol "a")) = false := by
  decide +kernel

/-- A failed child cannot license a completed answer in its parent. -/
theorem truncated_expression_not_covered :
    matchCovered 1 (.atoms (.expression [.symbol "a"])
      (.expression [.symbol "a"])) = false := by decide +kernel

theorem expression_covered :
    matchCovered 5 (.atoms (.expression [.symbol "a"])
      (.expression [.symbol "a"])) = true := by decide +kernel

end MatchDepth.Controls

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



namespace MatchDepth

abbrev Query (Answer : Type) :=
  Mettapedia.Machines.ReadOnlyQuery.Program MatchRequest (List Bindings) Answer

def queryCovered {Answer : Type} (depth : Nat) (query : Query Answer) : Bool :=
  (Mettapedia.Machines.ReadOnlyQuery.run (evalMatch depth) query).reads.all
    fun read => matchCovered depth read.1

open Mettapedia.Machines.ReadOnlyQuery in
 theorem queryCovered_stable {Answer : Type} (depth extra : Nat) (query : Query Answer)
    (covered : queryCovered depth query = true) :
    run (evalMatch (depth + extra)) query = run (evalMatch depth) query := by
  apply run_eq_of_agrees
  intro read member
  exact (matchCovered_stable depth extra read.1
    (List.all_eq_true.mp covered read member)).trans
      (run_agrees (evalMatch depth) query read member)

def typesQuery (type1 type2 : Atom) (b : Bindings) : Query (List Bindings) :=
  if type1 == Atom.undefinedType || type1 == Atom.atomType
     || type2 == Atom.undefinedType || type2 == Atom.atomType then
    .pure [b]
  else .read (.atoms type1 type2) fun matched =>
    Mettapedia.Machines.ReadOnlyQuery.flatTraverse matched fun mb =>
      .read (.merge b mb) .pure

open Mettapedia.Machines.ReadOnlyQuery in
 theorem run_typesQuery (depth : Nat) (type1 type2 : Atom) (b : Bindings) :
    (run (evalMatch depth) (typesQuery type1 type2 b)).answer =
      matchTypes type1 type2 b depth := by
  simp only [typesQuery, matchTypes]
  split <;> simp [run, run_flatTraverse, evalMatch]

end MatchDepth

def matchTypesCovered (type1 type2 : Atom) (b : Bindings) (depth : Nat) : Bool :=
  MatchDepth.queryCovered depth (MatchDepth.typesQuery type1 type2 b)

theorem matchTypesCovered_stable (type1 type2 : Atom) (b : Bindings)
    (depth extra : Nat) (covered : matchTypesCovered type1 type2 b depth = true) :
    matchTypes type1 type2 b (depth + extra) = matchTypes type1 type2 b depth := by
  rw [← MatchDepth.run_typesQuery, ← MatchDepth.run_typesQuery]
  exact congrArg Mettapedia.Machines.ReadOnlyQuery.Observation.answer
    (MatchDepth.queryCovered_stable depth extra _ covered)

/-! ## Primitive `unify` result lane

This model exposes bare aliases in the incoming record as equality constraints
before structural matcher results are merged into it. The structural cycle
filter and the ordered representative selection remain unchanged. Surviving
merged bindings are applied structurally to the success branch. This repairs
the crossed-alias representation obstruction without asserting literal-name
agreement with a different implementation's representative policy.

The caller is responsible for the final else-branch fallback when this list is
empty; upstream does that after the merge/filter pass, not before. -/

open Spec.Type.Presentation.BindingTheory (aliasConstraints)

/-- Success results for primitive `unify`, after alias exposure and before
    the caller's final else-branch fallback. -/
def unifySuccessResults
    (target pattern thenBranch : Atom) (seed : Bindings) (fuel : Nat) :
    ResultSet :=
  (matchAtoms target pattern fuel).flatMap fun matchBindings =>
    (mergeBindings matchBindings (aliasConstraints seed) fuel).filterMap fun merged =>
      if merged.hasLoop then none
      else some (merged.applyFull thenBranch (merged.resolutionFuel thenBranch), merged)

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


/-! ## Coverage of control-form matching -/

/-- Coverage of all matches used by primitive `unify`, before its else choice. -/
def unifyMatchesCovered (target pattern : Atom) (seed : Bindings) (depth : Nat) : Bool :=
  matchCovered depth (.atoms target pattern) &&
    (matchAtoms target pattern depth).all fun mb => matchCovered depth (.merge mb (aliasConstraints seed))

theorem unifyMatchesCovered_stable (target pattern thenBranch : Atom) (seed : Bindings)
    (depth extra : Nat) (covered : unifyMatchesCovered target pattern seed depth = true) :
    unifySuccessResults target pattern thenBranch seed (depth + extra) =
      unifySuccessResults target pattern thenBranch seed depth := by
  obtain ⟨matched, merged⟩ := Bool.and_eq_true_iff.mp covered
  have hm := matchCovered_stable depth extra (.atoms target pattern) matched
  change matchAtoms target pattern (depth + extra) = matchAtoms target pattern depth at hm
  simp only [unifySuccessResults, hm]
  apply List.flatMap_congr
  intro mb member
  have hb := matchCovered_stable depth extra (.merge mb (aliasConstraints seed))
    (List.all_eq_true.mp merged mb member)
  change mergeBindings mb (aliasConstraints seed) (depth + extra) =
    mergeBindings mb (aliasConstraints seed) depth at hb
  rw [hb]

/-- Coverage includes failed earlier branches, since they determine which branch
is selected. It does not demand unreachable later branches. -/
def switchMatchesCovered (scrut : Atom) (branches : List Atom)
    (seed : Bindings) (depth : Nat) : Bool :=
  match branches with
  | [] => true
  | .expression [pt, template] :: rest =>
      simpleMatchCovered pt scrut Bindings.empty depth &&
        match simpleMatch pt scrut Bindings.empty depth with
        | none => switchMatchesCovered scrut rest seed depth
        | some mb =>
            matchCovered depth (.merge mb seed) &&
              let hits := (mergeBindings mb seed depth).filterMap fun merged =>
                if merged.hasLoop then none else some (merged.applyDefault template, merged)
              if hits.isEmpty then switchMatchesCovered scrut rest seed depth else true
  | _ :: rest => switchMatchesCovered scrut rest seed depth

theorem switchMatchesCovered_raw_stable (scrut : Atom) (branches : List Atom)
    (seed : Bindings) (depth extra : Nat)
    (covered : switchMatchesCovered scrut branches seed depth = true) :
    switchMinimalRawResults scrut branches seed (depth + extra) =
      switchMinimalRawResults scrut branches seed depth := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      cases branch with
      | symbol _ => exact ih covered
      | var _ => exact ih covered
      | grounded _ => exact ih covered
      | expression parts =>
          cases parts with
          | nil => exact ih covered
          | cons pattern tail =>
              cases tail with
              | nil => exact ih covered
              | cons template tail =>
                  cases tail with
                  | cons _ _ => exact ih covered
                  | nil =>
                      change (_ && _) = true at covered
                      obtain ⟨simple, tail⟩ := Bool.and_eq_true_iff.mp covered
                      have hs := simpleMatchCovered_stable pattern scrut Bindings.empty
                        depth extra simple
                      simp only [switchMinimalRawResults, hs]
                      cases hmatch : simpleMatch pattern scrut Bindings.empty depth with
                      | none =>
                          simp only [hmatch] at tail ⊢
                          exact ih tail
                      | some mb =>
                          simp only [hmatch] at tail ⊢
                          obtain ⟨merge, continuation⟩ := Bool.and_eq_true_iff.mp tail
                          have hm := matchCovered_stable depth extra (.merge mb seed) merge
                          change mergeBindings mb seed (depth + extra) =
                            mergeBindings mb seed depth at hm
                          rw [hm]
                          split <;> rename_i selected
                          · exact ih (by simpa only [selected, ite_true] using continuation)
                          · rfl

theorem switchMatchesCovered_stable (scrut : Atom) (branches : List Atom)
    (seed : Bindings) (depth extra : Nat)
    (covered : switchMatchesCovered scrut branches seed depth = true) :
    switchMinimalResults scrut branches seed (depth + extra) =
      switchMinimalResults scrut branches seed depth := by
  simp only [switchMinimalResults,
    switchMatchesCovered_raw_stable scrut branches seed depth extra covered]


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

-- Equality merging retains a value already attached to one endpoint.
example :
    matchAtoms
        (.expression [.symbol "g", .symbol "a", .var "q"])
        (.expression [.symbol "g", .var "p", .var "p"]) 10 =
      [{ assignments := [("p", .symbol "a")]
       , equalities := [("q", "p")] }] := by
  decide

example :
    ({ assignments := [("p", .symbol "a")]
     , equalities := [("q", "p")] } : Bindings).applyFull (.var "p") 10 =
      .symbol "a" := by
  decide

-- NEGATIVE: a later value cannot disagree with an already-valued alias.
example :
    matchAtoms
        (.expression [.symbol "g", .var "q", .symbol "A", .var "q"])
        (.expression [.symbol "g", .var "p", .var "p", .symbol "B"]) 40 = [] := by
  decide

-- NEGATIVE: equality checks values carried indirectly by both joined classes.
set_option maxRecDepth 2000 in
example :
    addVarEquality
        (((Bindings.empty.addEquality "x" "z").assign "z" (.symbol "A"))
          |>.addEquality "y" "w" |>.assign "w" (.symbol "B"))
        "x" "y" 3 = [] := by
  decide

-- POSITIVE: a consistent value can be reasserted through an alias.
example :
    addVarBinding
        ((Bindings.empty.addEquality "x" "y").assign "x" (.symbol "A"))
        "y" (.symbol "A") 10 =
      [(Bindings.empty.addEquality "x" "y").assign "x" (.symbol "A")] := by
  decide

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
