import Mettapedia.GSLT.Parsing.KeyedParserDispatch
import Mettapedia.GSLT.Parsing.TokenReadDependencies
import Mettapedia.GSLT.Parsing.ParserAttemptSelection
import Mettapedia.GSLT.Parsing.GrammarCacheReuseControls

/-!
# Front-end evolution controls

The controls separate token-table reads, candidate dispatch, attempt selection
and nesting fuel. They do not identify this portable model with Lean's whole
parser. Host-specific correspondence is a separate adapter obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.FrontendEvolutionControls

namespace Dispatch
open KeyedParserDispatch

def profile : Profile := ⟨1, "4.33.1", "parser-profile-v1"⟩
def request : Request String := ⟨"term", .leading, .atom "+", .default, "ident"⟩

def store : Store String Nat := fun key =>
  match key.token with
  | none => some [10]
  | some "+" => some [1, 2]
  | some "ident" => some [7]
  | _ => none

def unrelated : Store String Nat := fun key =>
  if key.token = some "!" then some [99] else store key

theorem leading_and_trailing_order :
    dispatch store request = [10, 1, 2] ∧
    dispatch store { request with phase := .trailing } = [1, 2, 10] := by decide

theorem unrelated_token_reuses :
    (reuse profile unrelated request (capture profile store request)).2 = 0 ∧
    (reuse profile unrelated request (capture profile store request)).1 = [10, 1, 2] := by decide

def identifier : Request String := { request with token := .ident "new", behavior := .symbol }
def emptyNamed : Store String Nat := fun key =>
  if key.token = some "new" then some [] else store key

/-- Missing and present-empty named buckets have different fallback behavior. -/
theorem absence_is_a_dependency :
    dispatch store identifier = [10, 7] ∧
    dispatch emptyNamed identifier = [10] ∧
    (reuse profile emptyNamed identifier (capture profile store identifier)).2 = 1 := by decide

theorem coincident_identifier_key_is_not_duplicated :
    dispatch store { request with token := .ident "ident", behavior := .both } = [10, 7] := by decide

theorem release_change_recomputes :
    (reuse { profile with release := "4.35.0" } store request
      (capture profile store request)).2 = 1 := by decide

theorem duplicate_candidate_occurrences_survive_indexing :
    let entries := [(request.key (some "+"), 1), (request.key (some "+"), 1)]
    find (request.key (some "+")) (build entries) = some [1, 1] := by decide
end Dispatch

namespace Tokens
open TokenReadDependencies

def old : TrieLiteralSelection.Table Nat Nat := [([61, 62], 0)]
def grown : TrieLiteralSelection.Table Nat Nat := ([61, 62, 62], 1) :: old
def input : List Nat := [61, 62, 62]

theorem longer_token_changes_selection :
    longest (TrieLiteralSelection.prefixQuery (TrieLiteralSelection.build old) input) = [(2, 0)] ∧
    longest (TrieLiteralSelection.prefixQuery (TrieLiteralSelection.build grown) input) = [(3, 1)] ∧
    validates old grown input = false := by decide

/-- Retaining only accepting prefixes misses the newly longer token. -/
theorem accepting_prefixes_are_insufficient :
    Mettapedia.Machines.ReadOnlyQuery.checkReads (TrieLiteralSelection.bucket grown)
      ((Mettapedia.Machines.ReadOnlyQuery.run (TrieLiteralSelection.bucket old) (query input)).reads.filter
        fun read => !read.2.isEmpty) = true := by decide

theorem off_path_keyword_keeps_certificate :
    validates old (([43], 2) :: old) input = true := by decide

theorem new_keyword_changes_lexical_candidates :
    (TrieLiteralSelection.prefixQuery (TrieLiteralSelection.build
      ([] : TrieLiteralSelection.Table Nat Nat)) [108, 101, 116]) = [] ∧
    longest (TrieLiteralSelection.prefixQuery (TrieLiteralSelection.build
      [([108, 101, 116], 4)]) [108, 101, 116]) = [(3, 4)] := by decide
end Tokens

namespace Selection
open ParserAttemptSelection

def shortSuccess : Attempt String := ⟨4, true, 100, "short-success"⟩
def farFailure : Attempt String := ⟨5, false, 0, "far-failure"⟩

theorem farther_failure_is_observable :
    (select [shortSuccess, farFailure]).map Attempt.payload = ["far-failure"] := by decide

theorem same_endpoint_prefers_success :
    (select [farFailure, { shortSuccess with stop := 5 }]).map Attempt.payload = ["short-success"] := by decide

theorem exact_ties_keep_both_occurrences :
    (select [shortSuccess, { shortSuccess with payload := "second" }]).map Attempt.payload =
      ["short-success", "second"] := by decide

theorem priority_breaks_equal_endpoint_success_tie :
    (select [shortSuccess, { shortSuccess with priority := 101, payload := "higher" }]).map Attempt.payload =
      ["higher"] := by decide
end Selection

namespace Fuel
open CompilerCorrespondence (Category Codepoint ParseTree)
open GuardCorrespondence (CompiledGrammar)
open GrammarCacheReuse.Controls (rule)

def grammar : CompiledGrammar :=
  { start := "S", productions := [rule "S" "S" [.nonterminal "A"],
      rule "A" "A" [.nonterminal "B"], rule "B" "B" [.terminal 97]] }

/-- Every successful category consumes input, yet wrapper depth exceeds the
one-token input length. Consumption on return is not progress before recursion. -/
theorem token_length_is_not_nesting_fuel :
    (BoundedScheduler.scheduleRoot grammar [97] [97].length).length = 0 ∧
    (BoundedScheduler.scheduleRoot grammar [97] 3).length = 1 := by decide

theorem every_success_consumes (input : List Codepoint) (fuel : Nat) :
    ∀ {category : Category} {start stop : Nat} {tree : ParseTree},
      BoundedScheduler.DerivesWithin grammar input fuel category start stop tree → start < stop := by
  induction fuel with
  | zero => intro category start stop tree derived; cases derived
  | succ fuel ih =>
      intro category start stop tree derived
      cases derived with
      | apply production member body guards =>
          simp only [grammar, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · cases body with
            | nonterminal head rest =>
                cases rest
                exact ih head
          · cases body with
            | nonterminal head rest =>
                cases rest
                exact ih head
          · cases body with
            | terminal lookup rest =>
                cases rest
                exact Nat.lt_succ_self _
end Fuel

end Mettapedia.GSLT.Parsing.FrontendEvolutionControls
