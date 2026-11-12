import Mettapedia.Languages.MeTTa.PeTTa.ScopedSource
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingAllocation
import Lean.Elab.Tactic.Cbv

/-!
# Source variables and imported syntax use distinct activation identities

These controls execute the actual unifying machine through scoped admission.
The companion source fixtures independently exercise parse, stored-row
enumeration, non-backtrackable assignment and input in SWI-PeTTa.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying

def registry : SpaceSemantics.Program := {equations := [],declarations := []}
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def bind (pattern value body : Atom) : Atom := call "let" [pattern,value,body]

def forceImported (expression : Atom) : Atom :=
  bind (.var "x") (.symbol "a")
    (bind (.var "p") expression (bind (.var "p") (.symbol "b") (.var "p")))

def parsed : Atom := forceImported (call "parse" [.grounded (.string "$x#0")])

theorem parsed_variables_are_not_caller_variables :
    observed (run registry 100 (ScopedSource.enter 0 [] Effects.empty parsed)) = .answers [.symbol "b"] := by
  cbv

def rowState : Effects.State :=
  {Effects.empty with core := [call "row" [.var "x#0"]]}

def enumerated : Atom :=
  bind (.var "x") (.symbol "a")
    (bind (call "row" [.var "p"]) (call "get-atoms" [.symbol "&self"])
      (bind (.var "p") (.symbol "b") (.var "p")))

theorem enumerated_rows_are_fresh_occurrences :
    observed (run registry 100 (ScopedSource.enter 0 [] rowState enumerated)) = .answers [.symbol "b"] := by
  cbv

def assigned : Atom :=
  bind (.var "_") (call "change-state!" [.symbol "scope-cell",call "row" [.var "x"]])
    (bind (.var "x") (.symbol "a")
      (bind (call "row" [.var "p"]) (call "get-state" [.symbol "scope-cell"])
        (bind (.var "p") (.symbol "b") (.var "p"))))

theorem assignment_copies_before_the_caller_is_bound :
    observed (run registry 150 (ScopedSource.enter 0 [] Effects.empty assigned)) = .answers [.symbol "b"] := by
  cbv

def inputRequest : Atom := forceImported (call "readln!" [])

theorem input_syntax_receives_a_new_scope :
    observed (run registry 100
      {ScopedSource.enter 0 [] Effects.empty inputRequest with input := [.var "x#0"]}) =
      .answers [.symbol "b"] := by
  cbv

theorem arbitrary_suffix_spellings_are_apart (first later : Nat) (ordered : first < later)
    (sourceName clauseName : String) :
    freshName later clauseName ∉
      Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars (rename first (.var sourceName)) :=
  ScopedSource.entry_and_later_clause_are_apart first later (.var sourceName) ordered clauseName

/-- Returning two equal open rows does not make their residual variables equal. -/
theorem separate_copy_occurrences_do_not_alias (scope : Nat) (name : String) :
    copyTerms scope [.var name,.var name] =
      [.var (freshName scope name),.var (freshName (scope + 1) name)] ∧
      freshName scope name ≠ freshName (scope + 1) name := by
  refine ⟨rfl,?_⟩
  intro same
  have := ((ScopedSource.freshName_equal_iff _ _ _ _).mp same).1
  omega

def laterClause : SpaceSemantics.Equation :=
  ⟨"pick",[.var "x#0"],
    bind (call "row" [.var "p"]) (call "get-state" [.symbol "scope-cell"])
      (bind (.var "p") (.symbol "b") (.var "p"))⟩

def sessionState : Effects.State := {Effects.empty with core := [laterClause.toAtom]}

def storeOpen : Atom := call "change-state!" [.symbol "scope-cell",call "row" [.var "x"]]

def sessionResults : List Outcome :=
  ScopedSource.requests registry 100 {state := sessionState,control := .returned []}
    [storeOpen,call "pick" [.symbol "a"]]

theorem retained_supply_preserves_later_requests :
    sessionResults.map observed = [.answers [Effects.boolean true],.answers [.symbol "b"]] := by
  cbv

def savedCell : Effects.State :=
  sessionState.putCell "scope-cell" (call "row" [rename 1 (rename 0 (.var "x"))])

/-- Resetting the allocation counter would let the second call's formal
alias the open value retained by the first request. -/
theorem resetting_the_supply_can_capture_a_retained_value :
    observed (run (LiveEquations.atState registry savedCell) 100
      (ScopedSource.enter 0 [] savedCell (call "pick" [.symbol "a"]))) = .answers [] := by
  cbv

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopeControls
