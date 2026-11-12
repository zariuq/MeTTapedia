import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanCompiler
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeRows

/-!
# Source-arity locality of equation-body entry policy

The existing result-passing compiler decides raw equation bodies by source
head and source arity. Adding an Atom declaration for another source arity
must not change that decision. A head-wide arity-erased selector is a
countermodel, not a substitute source policy or a native implementation proof.

This concerns body entry, independently of the result guard. Explicit native
execution escapes and complete native body-mode realization remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyEntryPolicy

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PettaSourceTypeRows (declaration typeAtom)

theorem rawOutput_append (program : SpaceSemantics.Program) (head : String) (arity : Nat) (rows : List Atom) :
    OutputPlan.rawOutput {program with declarations := program.declarations ++ rows} head arity =
      (OutputPlan.rawOutput program head arity || OutputPlan.rawOutput {program with declarations := rows} head arity) := by
  simp only [OutputPlan.rawOutput, List.any_append]

theorem written_arrow (head : String) (parameters : List (Ty String)) (range : Ty String) :
    declaration head (arrow parameters range) = .expression [.symbol ":", .symbol head,
      .expression (.symbol "->" :: (parameters ++ [range]).map typeAtom)] := by
  simp only [declaration, arrow, PettaSourceTypeRows.typeAtom, PettaSourceTypeRows.typeAtoms,
    PettaSourceTypeRows.typeAtoms_map]

theorem other_head_is_irrelevant (program : SpaceSemantics.Program) (head other : String)
    (arity : Nat) (parameters : List (Ty String)) (range : Ty String) (different : other ≠ head) :
    OutputPlan.rawOutput {program with declarations := program.declarations ++ [declaration other (arrow parameters range)]}
      head arity = OutputPlan.rawOutput program head arity := by
  rw [rawOutput_append]
  simp [OutputPlan.rawOutput, written_arrow, different]

theorem other_arity_is_irrelevant (program : SpaceSemantics.Program) (head : String)
    (arity : Nat) (parameters : List (Ty String)) (range : Ty String) (different : parameters.length ≠ arity) :
    OutputPlan.rawOutput {program with declarations := program.declarations ++ [declaration head (arrow parameters range)]}
      head arity = OutputPlan.rawOutput program head arity := by
  rw [rawOutput_append]
  simp [OutputPlan.rawOutput, written_arrow, different]

theorem source_arity_is_preserved_when_adding_an_Atom_result
    (program : SpaceSemantics.Program) (head : String) (arity : Nat) (parameters : List (Ty String))
    (different : parameters.length ≠ arity) :
    OutputPlan.rawOutput {program with declarations := program.declarations ++ [declaration head (arrow parameters (.sym "Atom"))]}
      head arity = OutputPlan.rawOutput program head arity :=
  other_arity_is_irrelevant program head arity parameters (.sym "Atom") different

/-- Deliberately discards source arity. It is used only to refute erasing
the coordinate from the body-policy lookup. -/
def arityErased (program : SpaceSemantics.Program) (head : String) : Bool :=
  program.declarations.any fun row =>
    match row with
    | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)] =>
        name == head && types.getLast? == some (.symbol "Atom")
    | _ => false

namespace Controls

private def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private def num (value : Int) : Atom := .grounded (.int value)

private def baseline : SpaceSemantics.Program :=
  {equations := [⟨"f", [], .grounded (.string "zero")⟩,
      ⟨"f", [.var "n"], call "+" [.var "n", num 1]⟩],
    declarations := [declaration "f" (arrow [.sym "Number"] (.sym "Number"))]}

private def overloaded : SpaceSemantics.Program :=
  {baseline with declarations := baseline.declarations ++ [declaration "f" (arrow [] (.sym "Atom"))]}

theorem unary_body_is_evaluated : OutputPlan.rawOutput baseline "f" 1 = false := by cbv

theorem nullary_Atom_holds_only_the_nullary_body :
    OutputPlan.rawOutput overloaded "f" 0 = true ∧ OutputPlan.rawOutput overloaded "f" 1 = false := by cbv

theorem the_actual_foreign_arity_declaration_cannot_change_the_unary_policy :
    OutputPlan.rawOutput overloaded "f" 1 = OutputPlan.rawOutput baseline "f" 1 :=
  source_arity_is_preserved_when_adding_an_Atom_result baseline "f" 1 [] (by decide)

theorem erasing_arity_selects_the_wrong_unary_policy :
    arityErased overloaded "f" = true ∧ OutputPlan.rawOutput overloaded "f" 1 = false := by cbv

theorem a_cache_key_of_only_the_head_is_insufficient :
    OutputPlan.rawOutput overloaded "f" 0 ≠ OutputPlan.rawOutput overloaded "f" 1 := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyEntryPolicy
