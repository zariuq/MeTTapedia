import Mettapedia.Languages.MM0.OnTheStep.TermDeclarations
import Mettapedia.GSLT.Readers.MM0.SpecCorrespondence

/-!
# The step's input, read by the grammar of `MM0Syntax.module`

The rows the program of `DeclarationProgram` reads are the trees of the `.mm0` grammar presented in
`metta/gslt/module/readers/mm0/MM0Syntax.module`. This module connects them to the existing reader of that module
(`GSLT.Readers.MM0.SpecCorrespondence`): a tree there is checked against the module's grammar for a list of tokens
(`check`, with `reader_sound`: a checked tree is a derivation of the module's rows).

* `treeRow`: the row of a tree, a node as its production's label beside its children, a leaf as its token sort
  beside its text; it is `DeclarationProgram.node` and `leaf` (`treeRow_node`).
* **Read, then run** (`provableWff_read_and_run`): the tree that `SpecCorrespondence.control_sort` checks against
  the module's grammar for the tokens `provable sort wff ;` is the row of the sort statement of the examples, a
  derivation of the module's rows, and the file of that one statement is accepted on the step.
* **Refused before the step** (`badSort32_unread`): the tokens `provable strict sort wff ;` (modifiers out of MM0's
  order, upstream `tests/mm0_mmu/fail/bad-sort32.mm0`) do not check with the tree of those modifiers
  (`SpecCorrespondence.control_modifier_order`); the grammar is where MM0 refuses them.

The trees of the other examples are written by hand as the module's rows prescribe; checking each against tokens
asks the kernel to elaborate the module, which the reader's own file does with a raised heartbeat budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.GrammarLink

open Mettapedia.GSLT.Readers.TreeCheck (Tree check)
open Mettapedia.GSLT.Readers.GrammarCorrespondence (GDerives toPattern)
open Mettapedia.GSLT.Readers.MM0.SpecCorrespondence (setting control_sort control_modifier_order reader_sound)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open DeclarationProgram (node leaf textRow listRow)
open SortDeclarations.Examples (sortStmt)
open TermDeclarations (Statement)
open TermDeclarations.Examples (AcceptedOnTheStep accepted_on_the_step_iff)

mutual
/-- **The row of a tree of the `.mm0` grammar**: a node is its production's label beside its children, a leaf
its token sort beside its text. -/
def treeRow : Tree → Expr
  | .leaf sort text => leaf sort text
  | .node label kids => .app (.app (.sym 2) (textRow label)) (treesRow kids)

/-- The rows of a list of trees, as one row. -/
def treesRow : List Tree → Expr
  | [] => .sym 0
  | t :: ts => .app (treeRow t) (treesRow ts)
end

theorem treesRow_eq : ∀ kids : List Tree, treesRow kids = listRow (kids.map treeRow)
  | [] => rfl
  | t :: ts => by
      show Expr.app (treeRow t) (treesRow ts) = Expr.app (treeRow t) (listRow (ts.map treeRow))
      rw [treesRow_eq ts]

/-- **The row of a node is the program's node.** -/
theorem treeRow_node (label : String) (kids : List Tree) :
    treeRow (.node label kids) = node label (kids.map treeRow) := by
  show Expr.app (Expr.app (.sym 2) (textRow label)) (treesRow kids) = _
  rw [treesRow_eq]
  rfl

/-- The tree that `SpecCorrespondence.control_sort` checks for the tokens `provable sort wff ;`. -/
def provableWffTree : Tree :=
  .node "statement_sort" [.node "pure_no" [], .node "strict_no" [], .node "provable_yes" [], .node "free_no" [],
    .leaf "id_tok" "wff"]

theorem provableWff_row :
    treeRow provableWffTree = (Statement.sort (sortStmt false false true false "wff")).tree := by decide

/-- **Read, then run**: the module's grammar reads `provable sort wff ;` as this tree (a derivation of the
module's rows), the tree is the row of the statement, and the file of that one statement is accepted on the
step. -/
theorem provableWff_read_and_run :
    check setting.grammar "statement" ["provable", "sort", "wff", ";"] provableWffTree = true ∧
      GDerives (setting.leaves ["provable", "sort", "wff", ";"]) "statement" ["provable", "sort", "wff", ";"]
        (toPattern provableWffTree) ∧
      treeRow provableWffTree = (Statement.sort (sortStmt false false true false "wff")).tree ∧
      AcceptedOnTheStep [.sort (sortStmt false false true false "wff")] :=
  ⟨control_sort, reader_sound _ _ _ control_sort, provableWff_row,
    (accepted_on_the_step_iff _).mpr (by decide +kernel)⟩

/-- **Refused before the step**: the tokens `provable strict sort wff ;` do not check with the tree of those
modifiers. -/
theorem badSort32_unread :
    check setting.grammar "statement" ["provable", "strict", "sort", "wff", ";"]
      (.node "statement_sort" [.node "pure_no" [], .node "strict_yes" [], .node "provable_yes" [],
        .node "free_no" [], .leaf "id_tok" "wff"]) = false :=
  control_modifier_order

#print axioms treeRow_node
#print axioms provableWff_read_and_run
#print axioms badSort32_unread

end Mettapedia.Languages.MM0.OnTheStep.GrammarLink
