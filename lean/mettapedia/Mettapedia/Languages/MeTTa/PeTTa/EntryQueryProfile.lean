import Mettapedia.Machines.Cursor.EntryQueryTree
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec

/-!
# Literal and query readings of nested comma and union atoms

This adapter uses the existing Atom carrier and finite one-way matcher.
It covers binary query trees over ordinary ground stored atoms. Unsupported
query arities or insufficient lowering fuel decline explicitly; they do not
silently become literal patterns. Open cells, bidirectional unification,
native head-index coverage and allocation failures are separate obligations.

Nested conjunction is a grammar choice. Associativity of the independently
defined relational query algebra does not force every comma-shaped datum to
be parsed as a query. Union syntax likewise depends on the profile.
Root union branches retain their root-query role; unions inside conjunction
legs retain the leg role. These grammar controls do not impose one global
entry view on distinct conjunction calls made by a root union.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EntryQueryProfile

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom applySubst)
open Mettapedia.Machines.Cursor.EntryQueryTree
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)

structure Profile where
  nestedConjunctions : Bool
  unions : Bool
  deriving DecidableEq, Repr

def headKey : Atom → Option String
  | .symbol name => some name
  | .expression (.symbol name :: _) => some name
  | _ => none

def literal (pattern : Atom) : Query (Option String) Atom := .atom (headKey pattern) pattern

/-- Each lowering node consumes fuel. A caller may increase the
bound after a decline, without reinterpreting the source under another grammar. -/
def lower (profile : Profile) : Nat → Bool → Atom → Option (Query (Option String) Atom)
  | 0, _, _ => none
  | fuel + 1, atRoot, pattern =>
      match pattern with
      | .expression (.symbol name :: arguments) =>
          if name = "," ∧ (atRoot || profile.nestedConjunctions) then
            match arguments with
            | [first, second] => do
                let left ← lower profile fuel false first
                let right ← lower profile fuel false second
                pure (.seq left right)
            | _ => none
          else if name = "|" ∧ profile.unions then
            match arguments with
            | [first, second] => do
                let left ← lower profile fuel atRoot first
                let right ← lower profile fuel atRoot second
                pure (.union left right)
            | _ => none
          else some (literal pattern)
      | _ => some (literal pattern)

/-- The all-rows coordinate is required for patterns without a rigid head.
For an ordinary ground row store, a rigid pattern head selects its bucket. -/
def rows (facts : List Atom) (key : Option String) : List Atom :=
  match key with
  | none => facts
  | some head => facts.filter fun fact => headKey fact == some head

def matchRow (pattern fact : Atom) (bindings : Subst) : List Subst :=
  (matchAtom bindings pattern fact).toList

theorem atomic_answer_sound (pattern fact : Atom) (before after : Subst)
    (answer : after ∈ matchRow pattern fact before) :
    Mettapedia.Languages.ProcessCalculi.MORK.MatchAtomRel before pattern fact after := by
  exact Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound
    (by simpa [matchRow] using answer)

theorem matching_rigid_head {pattern fact : Atom} {before after : Subst} {head : String}
    (matched : Mettapedia.Languages.ProcessCalculi.MORK.MatchAtomRel before pattern fact after)
    (rigid : headKey pattern = some head) : headKey fact = some head := by
  cases matched with
  | var_fresh => simp [headKey] at rigid
  | var_bound => simp [headKey] at rigid
  | symbol => exact rigid
  | grounded => simp [headKey] at rigid
  | expr_nil => simp [headKey] at rigid
  | @expr_cons before middle after first concrete rest concreteRest firstMatch _ =>
      cases first with
      | var => simp [headKey] at rigid
      | grounded => simp [headKey] at rigid
      | expression => simp [headKey] at rigid
      | symbol name =>
          cases firstMatch
          exact rigid

/-- In this ordinary Atom matcher, head filtering loses no answer occurrence;
headless patterns use the full source. This does not cover native cell views. -/
theorem atomic_bucket_complete (facts : List Atom) (pattern : Atom) (bindings : Subst) :
    (rows facts (headKey pattern)).flatMap (fun fact => matchRow pattern fact bindings) =
      facts.flatMap (fun fact => matchRow pattern fact bindings) := by
  cases key : headKey pattern with
  | none => simp [rows]
  | some head =>
      induction facts with
      | nil => rfl
      | cons fact facts ih =>
          simp only [rows] at ih
          by_cases selected : headKey fact = some head
          · simp [rows, selected, ih]
          · have absent : matchRow pattern fact bindings = [] := by
              cases found : matchAtom bindings pattern fact with
              | none => simp [matchRow, found]
              | some after =>
                  exact False.elim (selected (matching_rigid_head
                    (Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound found) key))
            simp [rows, selected, absent, ih]

theorem literal_union (nested : Bool) (fuel : Nat) (atRoot : Bool) (first second : Atom) :
    lower ⟨nested, false⟩ (fuel + 1) atRoot
      (.expression [.symbol "|", first, second]) =
      some (literal (.expression [.symbol "|", first, second])) := by
  simp [lower]

theorem shallow_nested_comma (unions : Bool) (fuel : Nat) (first second : Atom) :
    lower ⟨false, unions⟩ (fuel + 1) false
      (.expression [.symbol ",", first, second]) =
      some (literal (.expression [.symbol ",", first, second])) := by
  simp [lower]

theorem lower_union (nested : Bool) (fuel : Nat) (atRoot : Bool)
    (first second : Atom) (left right : Query (Option String) Atom)
    (firstLowered : lower ⟨nested, true⟩ fuel atRoot first = some left)
    (secondLowered : lower ⟨nested, true⟩ fuel atRoot second = some right) :
    lower ⟨nested, true⟩ (fuel + 1) atRoot (.expression [.symbol "|", first, second]) =
      some (.union left right) := by
  simp [lower, firstLowered, secondLowered]

theorem lower_conjunction (profile : Profile) (fuel : Nat) (atRoot : Bool)
    (first second : Atom) (left right : Query (Option String) Atom)
    (queryRole : (atRoot || profile.nestedConjunctions) = true)
    (firstLowered : lower profile fuel false first = some left)
    (secondLowered : lower profile fuel false second = some right) :
    lower profile (fuel + 1) atRoot (.expression [.symbol ",", first, second]) =
      some (.seq left right) := by
  simp [lower, queryRole, firstLowered, secondLowered]

namespace Controls

def p : Atom := .expression [.symbol "p", .var "z", .var "y"]
def r : Atom := .expression [.symbol "r", .var "y", .var "z"]
def diagonal : Atom := .expression [.symbol "p", .var "y", .var "y"]
def unionAtom : Atom := .expression [.symbol "|", p, r]
def source : Atom := .expression [.symbol ",", unionAtom, diagonal]
def initial : List Atom := [.expression [.symbol "p", .symbol "a", .symbol "a"]]
def added : Atom := .expression [.symbol "r", .symbol "a", .symbol "a"]

def unionQuery : Query (Option String) Atom :=
  .seq (.union (literal p) (literal r)) (literal diagonal)

def literalQuery : Query (Option String) Atom :=
  .seq (literal unionAtom) (literal diagonal)

theorem extended_lowering : lower ⟨false, true⟩ 4 true source = some unionQuery := by decide
theorem stable_lowering : lower ⟨false, false⟩ 4 true source = some literalQuery := by decide

theorem extended_dependencies :
    dependencies unionQuery = [some "p", some "r", some "p"] := rfl

theorem stable_dependencies :
    dependencies literalQuery = [some "|", some "p"] := rfl

theorem first_union_later_dependencies :
    laterDependencies unionQuery = [some "r", some "p"] := rfl

theorem first_literal_later_dependencies :
    laterDependencies literalQuery = [some "p"] := rfl

def publish (bindings : Subst) : Search (List Atom) Atom := fun world =>
  .answer (applySubst bindings (.expression [.var "y", .var "z"]))
    (world ++ [added]) .done

def withWrites (watched : List (Option String)) (query : Query (Option String) Atom) :
    List Atom :=
  ((Search.bind (stream matchRow (fun world => journal watched (rows initial) (rows world))
    query []) publish) initial).drain.1

def answer : Atom := .expression [.symbol "a", .symbol "a"]

/-- The late branch sees a newly added row when only the later outer leg is
watched. The duplicate is observable even though answer support is unchanged. -/
theorem unwatched_first_union_changes_bag :
    withWrites [some "p"] unionQuery = [answer, answer] := by decide

theorem whole_first_union_keeps_entry_bag :
    withWrites [some "p", some "r"] unionQuery = [answer] := by decide

theorem omission_is_not_detected_by_answer_support :
    (withWrites [some "p"] unionQuery).toFinset =
      (withWrites [some "p", some "r"] unionQuery).toFinset := by decide

theorem literal_union_is_not_its_branches :
    withWrites [some "|", some "p"] literalQuery = [] := by decide

/-- Stable union syntax is still a real literal pattern: a matching stored
union-shaped datum is not forbidden or silently expanded. -/
theorem literal_union_can_match_stored_data :
    (evaluate matchRow (rows [applySubst [("y", .symbol "a"), ("z", .symbol "a")] unionAtom])
      (literal unionAtom) []).length = 1 := by decide

def nestedSource : Atom := .expression [.symbol ",", .expression [.symbol ",", p, r], diagonal]
def nestedFacts : List Atom := initial ++ [added]
def shallow : Query (Option String) Atom :=
  .seq (literal (.expression [.symbol ",", p, r])) (literal diagonal)
def recursive : Query (Option String) Atom :=
  .seq (.seq (literal p) (literal r)) (literal diagonal)

theorem shallow_lowering : lower ⟨false, false⟩ 4 true nestedSource = some shallow := by decide
theorem recursive_lowering : lower ⟨true, false⟩ 4 true nestedSource = some recursive := by decide

theorem nested_grammars_are_observably_distinct :
    evaluate matchRow (rows nestedFacts) shallow [] = [] ∧
      (evaluate matchRow (rows nestedFacts) recursive []).length = 1 := by decide

def commaDatum : Atom :=
  applySubst [("y", .symbol "a"), ("z", .symbol "a")] (.expression [.symbol ",", p, r])

theorem literal_data_distinguishes_in_the_other_direction :
    (evaluate matchRow (rows (initial ++ [commaDatum])) shallow []).length = 1 ∧
      evaluate matchRow (rows (initial ++ [commaDatum])) recursive [] = [] := by decide

def commaPattern : Atom := .expression [.symbol ",", r,
  .expression [.symbol "q", .var "y", .var "z"]]
def commaQuery : Query (Option String) Atom := .seq (literal p) (literal commaPattern)
def commaInitial : List Atom := initial ++
  [.expression [.symbol "p", .symbol "b", .symbol "b"],
   applySubst [("y", .symbol "a"), ("z", .symbol "a")] commaPattern]
def commaAdded : Atom :=
  applySubst [("y", .symbol "b"), ("z", .symbol "b")] commaPattern

def commaWithWrites (watched : List (Option String)) : List Atom :=
  ((Search.bind (stream matchRow (fun world => journal watched (rows commaInitial) (rows world))
    commaQuery []) (fun bindings world =>
      Trace.answer (applySubst bindings (.expression [.var "y", .var "z"]))
        (world ++ [commaAdded]) .done)) commaInitial).drain.1

theorem literal_comma_later_dependency : laterDependencies commaQuery = [some ","] := rfl

theorem watching_parts_of_a_literal_is_insufficient :
    commaWithWrites [some "p", some "r", some "q"] =
      [answer, .expression [.symbol "b", .symbol "b"]] := by decide

theorem watching_the_literal_head_preserves_entry :
    commaWithWrites [some ","] = [answer] := by decide

def unmatched : Atom := .expression [.symbol "none", .var "y", .var "z"]
def rootUnion : Atom := .expression [.symbol "|", .expression [.symbol ",", p, r], unmatched]
def rootUnionQuery : Query (Option String) Atom :=
  .union (.seq (literal p) (literal r)) (literal unmatched)
def legUnionQuery : Query (Option String) Atom :=
  .seq (literal diagonal)
    (.union (literal (.expression [.symbol ",", p, r])) (literal unmatched))

theorem root_union_branch_keeps_query_role :
    lower ⟨false, true⟩ 4 true rootUnion = some rootUnionQuery := by decide

theorem union_inside_conjunction_keeps_literal_comma_role :
    lower ⟨false, true⟩ 5 true (.expression [.symbol ",", diagonal, rootUnion]) =
      some legUnionQuery := by decide

theorem query_placement_changes_answers :
    (evaluate matchRow (rows nestedFacts) rootUnionQuery []).length = 1 ∧
      evaluate matchRow (rows nestedFacts) legUnionQuery [] = [] := by decide

theorem literal_placement_can_answer_in_the_other_direction :
    evaluate matchRow (rows (initial ++ [commaDatum])) rootUnionQuery [] = [] ∧
      (evaluate matchRow (rows (initial ++ [commaDatum])) legUnionQuery []).length = 1 := by decide

theorem insufficient_lowering_declines : lower ⟨true, true⟩ 1 true source = none := by decide

theorem unsupported_query_arity_declines :
    lower ⟨true, true⟩ 4 true (.expression [.symbol ",", p, r, diagonal]) = none := by decide

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.EntryQueryProfile
