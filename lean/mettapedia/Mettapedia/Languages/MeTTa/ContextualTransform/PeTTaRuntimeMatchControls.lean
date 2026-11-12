import Mettapedia.Languages.MeTTa.PeTTa.ScopedSource
import Lean.Elab.Tactic.Cbv

/-!
# Runtime match preserves bindings without repeating template evaluation

Written matching schedules its body after selection. Runtime dispatch has
already evaluated the template argument, so it returns that value under each
row's unifier. The independent SWI fixture distinguishes those boundaries.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaRuntimeMatchControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying

def registry : SpaceSemantics.Program := {equations := [],declarations := []}
def call (head : String) (values : List Atom) : Atom := .expression (.symbol head :: values)
def bind (name : String) (value body : Atom) : Atom := call "let" [.var name,value,body]

def state : Effects.State :=
  {Effects.empty with core := [call "row" [.symbol "a"],call "open" [.var "z"]]}

def escaping : Atom :=
  bind "m" (.symbol "match")
    (bind "v" (.expression [.var "m",.symbol "&self",call "row" [.var "x"],.var "x"])
      (call "pair" [.var "v",.var "x"]))

theorem runtime_match_binds_the_caller :
    observed (run registry 100 (ScopedSource.enter 0 [] state escaping)) =
      .answers [call "pair" [.symbol "a",.symbol "a"]] := by cbv

def held : Atom :=
  bind "m" (.symbol "match")
    (.expression [.var "m",.symbol "&self",call "row" [.symbol "a"],
      call "quote" [call "println!" [.grounded (.int 9)]]])

theorem runtime_template_is_not_evaluated_twice :
    shown (run registry 100 (ScopedSource.enter 0 [] state held)) =
      .printed [] [call "println!" [.grounded (.int 9)]] := by cbv

theorem written_match_still_evaluates_its_body :
    shown (run registry 100 (ScopedSource.enter 0 [] state
      (call "match" [.symbol "&self",call "row" [.symbol "a"],call "println!" [.grounded (.int 9)]]))) =
      .printed [.grounded (.int 9)] [Effects.boolean true] := by cbv

def openRow : Atom :=
  bind "m" (.symbol "match")
    (.expression [.var "m",.symbol "&self",call "open" [.symbol "b"],.symbol "yes"])

theorem runtime_match_unifies_open_stored_rows :
    observed (run registry 100 (ScopedSource.enter 0 [] state openRow)) = .answers [.symbol "yes"] := by cbv

/-- The ground primitive table remains useful within its declared profile;
it cannot substitute for the scoped two-way matcher on this open-row input. -/
theorem ground_table_is_not_the_open_row_adapter :
    StdLib.apply state "match" [.symbol "&self",call "open" [.symbol "b"],.symbol "yes"] =
      .ok (state,[]) := by cbv

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaRuntimeMatchControls
