import Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
import Lean.Elab.Term
import Mettapedia.Tools.KernelReflexivity

/-!
# Closed programs as literal data

`program_literal% p` evaluates the closed program `p` and elaborates to its value as ordinary constructor
data. Long lists become balanced appends of auxiliary definitions holding at most eight items each, so no
single term is a long constructor chain.

The literal supplies no fact by itself. Each use is tied to the program it was read from by one equation that
the kernel checks.

`sealed_program name := p` is the definition-site form: `name` is the literal value of `p`, and the theorem
`name.selected : name = p` is checked once, by kernel reduction. Kernel checks that mention `name` then read
the literal instead of deriving `p` again; a proof that needs the derivation rewrites with `name.selected`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ProgramLiteral

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open BridgeKit (atomToExpr)
open SpaceSemantics (Program Equation FormKind)
open Lean Elab Term Meta

private def consList (type : Expr) (items : List Expr) : Expr :=
  items.foldr (fun item rest => mkApp3 (mkConst ``List.cons [.zero]) type item rest)
    (mkApp (mkConst ``List.nil [.zero]) type)

/-- A literal list as balanced appends of auxiliary definitions holding at most eight items each. -/
private partial def literalList (type : Expr) (items : List Expr) : TermElabM Expr := do
  if items.length ≤ 8 then
    mkAuxDefinition (← mkAuxName `literalRows) (mkApp (mkConst ``List [.zero]) type) (consList type items)
  else
    let (first, rest) := items.splitAt (items.length / 2)
    return mkApp3 (mkConst ``List.append [.zero]) type (← literalList type first) (← literalList type rest)

private def equationExpr (row : Equation) : Expr :=
  mkApp3 (mkConst ``Equation.mk) (toExpr row.head) (consList (mkConst ``Atom) (row.arguments.map atomToExpr))
    (atomToExpr row.body)

private def formKindExpr : FormKind → Expr
  | .equation => mkConst ``FormKind.equation
  | .declaration => mkConst ``FormKind.declaration
  | .fact => mkConst ``FormKind.fact

/-- The program as constructor data. -/
def programExpr (program : Program) : TermElabM Expr := do
  let atoms (values : List Atom) : TermElabM Expr := literalList (mkConst ``Atom) (values.map atomToExpr)
  return mkApp5 (mkConst ``Program.mk)
    (← literalList (mkConst ``Equation) (program.equations.map equationExpr))
    (← atoms program.declarations) (← atoms program.initializers) (← atoms program.facts)
    (← literalList (mkConst ``FormKind) (program.layout.map formKindExpr))

/-- `program_literal% p` is the value of the closed program `p` as literal data. -/
syntax (name := programLiteral) "program_literal% " term : term

@[term_elab programLiteral] def elabProgramLiteral : TermElab := fun stx _ => do
  let source := stx[1]
  let value ← instantiateMVars (← elabTermEnsuringType source (mkConst ``Program))
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasFVar || value.hasMVar || value.hasLevelParam then
    throwErrorAt source "program_literal% expects a closed program"
  let program ← unsafe evalExpr Program (mkConst ``Program) value
  programExpr program

/-- `sealed_program name := p` defines `name` as the literal value of the closed program `p` and proves
`name.selected : name = p` by kernel reduction. -/
syntax (name := sealedProgram) (docComment)? "sealed_program " ident " := " term : command

macro_rules
  | `($[$doc?:docComment]? sealed_program $name:ident := $selection:term) => do
    let selected := mkIdentFrom name (name.getId ++ `selected)
    let definition ← `($[$doc?:docComment]? def $name : $(mkCIdent ``Program) := program_literal% $selection)
    let equation ← `(theorem $selected : $name = $selection := by kernel_reflexivity)
    return mkNullNode #[definition, equation]

/-! ## Controls -/

private def control : Program :=
  { equations := [⟨"twice", [.var "x"], .expression [.symbol "Pair", .var "x", .var "x"]⟩]
    declarations := [.expression [.symbol ":", .symbol "twice", .expression [.symbol "->", .symbol "Atom",
      .symbol "%Undefined%"]]]
    layout := [.equation, .declaration] }

/-- The literal is the constant's value. -/
example : control = program_literal% control := rfl

/-- A closed program term is read the same way. -/
example : control.append control = program_literal% control.append control := rfl

/-- The sealed definition is the literal; its equation names the program it was read from. -/
sealed_program Controls.doubled := control.append control

example : Controls.doubled.equations.length = 2 := by decide +kernel

example : Controls.doubled = control.append control := Controls.doubled.selected

/-- error: program_literal% expects a closed program -/
#guard_msgs in
example (program : Program) : Program := program_literal% program

end Mettapedia.Languages.MeTTa.PeTTa.ProgramLiteral
