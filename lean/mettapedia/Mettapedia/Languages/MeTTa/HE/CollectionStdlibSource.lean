import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Source terms for the standard collection path

These are the authored collapse, foldl-atom and let equations and the
registered signatures reached by their collection path. Native helper rows
record effective signatures; they are kept separate from authored rows.
The definitions specify source terms, not a text-parser or native-code
correspondence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.CollectionStdlibSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Type Spec.Type.RuntimeRefinement
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.Presentation.BindingTheory

def app (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def arrow (arguments : List Atom) (returned : Atom) : Atom := app "->" (arguments ++ [returned])
def declaration (head : String) (type : Atom) : Atom := app ":" [.symbol head, type]
def equation (pattern body : Atom) : Atom := app "=" [pattern, body]

def appendName : String := "_collapse-add-next-atom-from-collapse-bind-result"
def foldName : String := "_minimal-foldl-atom"

def squarePattern : Atom := app "sq" [.var "x"]
def squareBody : Atom := app "*" [.var "x", .var "x"]
def squareType : Atom := arrow [.symbol "Number"] (.symbol "Number")

def foldPattern : Atom := app "foldl-atom" [.var "list", .var "init", .var "a", .var "b", .var "op"]
def foldBody : Atom :=
  app "function" [app "chain" [app "context-space" [], .var "space",
    app "eval" [app foldName [.var "list", .var "init", .var "a", .var "b", .var "op", .var "space"]]]]
def foldType : Atom := arrow
  [Atom.expressionType, Atom.atomType, Atom.variableType, Atom.variableType, Atom.atomType] Atom.undefinedType

def collapsePattern : Atom := app "collapse" [.var "atom"]
def collapseBody : Atom :=
  app "function" [app "chain" [app "context-space" [], .var "space",
    app "chain" [app "collapse-bind" [app "metta" [.var "atom", Atom.undefinedType, .var "space"]], .var "eval",
      app "chain" [app "eval" [app "foldl-atom"
        [.var "eval", .expression [], .var "res", .var "item", app appendName [.var "res", .var "item"]]],
        .var "result", app "return" [.var "result"]]]]]
def collapseType : Atom := arrow [Atom.atomType] Atom.atomType

def letPattern : Atom := app "let" [.var "pattern", .var "atom", .var "template"]
def letBody : Atom := app "unify" [.var "atom", .var "pattern", .var "template", Atom.empty]
def letType : Atom := arrow [Atom.atomType, Atom.undefinedType, Atom.atomType] Atom.undefinedType
def unifyType : Atom := arrow [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType] Atom.undefinedType

def authoredRows : List Atom :=
  [declaration "sq" squareType, equation squarePattern squareBody,
   declaration "collapse" collapseType, equation collapsePattern collapseBody,
   declaration "foldl-atom" foldType, equation foldPattern foldBody,
   declaration "let" letType, equation letPattern letBody]

def nativeTypeRows : List Atom :=
  [declaration "*" (arrow [.symbol "Number", .symbol "Number"] (.symbol "Number")),
   declaration appendName (arrow [Atom.expressionType, Atom.expressionType] Atom.atomType),
   declaration foldName (arrow
     [Atom.expressionType, Atom.atomType, Atom.variableType, Atom.variableType, Atom.atomType, .symbol "SpaceType"]
     Atom.undefinedType)]

def instructionTypeRows : List Atom :=
  [declaration "function" (arrow [Atom.atomType] Atom.atomType),
   declaration "eval" (arrow [Atom.atomType] Atom.atomType),
   declaration "chain" (arrow [Atom.atomType, Atom.variableType, Atom.atomType] Atom.undefinedType),
   declaration "context-space" (arrow [] (.symbol "SpaceType")),
   declaration "collapse-bind" (arrow [Atom.atomType] Atom.expressionType),
   declaration "metta" (arrow [Atom.atomType, .symbol "Type", .symbol "SpaceType"] Atom.atomType),
   declaration "unify" unifyType]

def extensionRows : List Atom := authoredRows ++ nativeTypeRows ++ instructionTypeRows

/-- The actual ndcol probe has a consumer after collection; collapse alone
is not the whole probe. The bound is left symbolic for the source proof. -/
def collection (lower upper : Int) : Atom :=
  app "collapse" [app "sq" [app "range" [.grounded (.int lower), .grounded (.int upper)]]]

def probe (upper : Int) : Atom :=
  app "let" [.var "l", collection 0 upper,
    app "foldl-atom" [.var "l", .grounded (.int 0), .var "a", .var "b", app "+" [.var "a", .var "b"]]]

theorem collapse_holds_its_operand : FunctionTypeRel collapseType [Atom.atomType] Atom.atomType := rfl
theorem let_declared_arguments :
    FunctionTypeRel letType [Atom.atomType, Atom.undefinedType, Atom.atomType] Atom.undefinedType := rfl

/-- Selecting the authored let row puts the forced operand first in unify.
The actual activation may still contain caller variables; the order and
sharing are independent of the chosen fresh names and residual solution. -/
theorem let_row_body_under_solution
    {live : List Atom} {pattern forced template : Atom} {incoming : Bindings}
    {position : Nat} {work : EquationWork}
    (selected : EquationRowResultsRel live (app "let" [pattern, forced, template]) incoming
      position (equation letPattern letBody) [work])
    (valuation : String → Atom) (model : TypeBindingSatisfied valuation work.bindings) :
    applyTypeValuation valuation work.body =
      app "unify" [applyTypeValuation valuation forced, applyTypeValuation valuation pattern,
        applyTypeValuation valuation template, Atom.empty] := by
  cases selected with
  | hit _ _ renamedPattern renamedBody matched output fresh matchedBy merged =>
    have input := ((UnifyCandidateRel.solutions
      (show UnifyCandidateRel (app "let" [pattern, forced, template]) renamedPattern incoming output
        from ⟨matched, matchedBy, merged⟩) valuation).mp model).1
    obtain ⟨rename, _, lhs, rhs, _⟩ := fresh
    rw [EquationFreshening.alphaRename_eq lhs] at input
    simp [letPattern, app, renameTypeVars, applyTypeValuation] at input
    change applyTypeValuation valuation renamedBody = _
    rw [EquationFreshening.alphaRename_eq rhs]
    simp [letBody, app, renameTypeVars, applyTypeValuation, Atom.empty,
      ← input.1, ← input.2.1, ← input.2.2]

/-- The retained normal table reads that same RHS without choosing a
ground solution. Pending caller-variable aliases use its actual readout. -/
theorem let_row_body_readout
    {live : List Atom} {pattern forced template : Atom} {incoming : Bindings}
    {position : Nat} {work : EquationWork} {table : TypeSubst}
    (selected : EquationRowResultsRel live (app "let" [pattern, forced, template]) incoming
      position (equation letPattern letBody) [work])
    (retained : ReadoutCertificate work.bindings table) :
    table.apply work.body =
      app "unify" [table.apply forced, table.apply pattern, table.apply template, Atom.empty] := by
  have model := (retained.theory (presentedValuation table)).mp
    (normal_presentedValuation_satisfied retained.normal)
  simpa only [applyTypeValuation_presented_eq_apply] using
    let_row_body_under_solution selected (presentedValuation table) model

theorem fold_declared_arguments : FunctionTypeRel foldType
    [Atom.expressionType, Atom.atomType, Atom.variableType, Atom.variableType, Atom.atomType] Atom.undefinedType := rfl
theorem collapse_body_enters_function : Minimal.IsFunction collapseBody := by
  refine ⟨_, rfl⟩
theorem fold_body_enters_function : Minimal.IsFunction foldBody := by
  refine ⟨_, rfl⟩

end Mettapedia.Languages.MeTTa.HE.CollectionStdlibSource
