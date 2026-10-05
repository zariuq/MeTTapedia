import Mettapedia.Languages.MeTTa.PeTTa.SourceProgram
import MeTTailCore.Crypto.SHA256
import Lean.Elab.Term

/-!
# Literal source packages for PeTTa program proofs

A quotation reads an existing program file and retains its exact source text,
digest and parsed program. The digest must match the supplied pin. Expansion
contains only ordinary data constructors; it introduces no checking primitive
and does not produce a MeTTa program.

The text reader remains a named boundary. Kernel checking establishes the
theorems about the retained constructor data, not byte-level parser adequacy.
The quoting module must register its source files as Lake inputs so changed
text cannot silently reuse an earlier quoted program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourceQuotation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open SourceProgram (Program Equation)

structure SourcePackage where
  text : String
  digest : String
  program : Program

meta section

open Lean Elab Term

private def groundedExpr : GroundedValue → Expr
  | .int value => mkApp (mkConst ``GroundedValue.int) (toExpr value)
  | .string value => mkApp (mkConst ``GroundedValue.string) (toExpr value)
  | .bool value => mkApp (mkConst ``GroundedValue.bool) (toExpr value)
  | .custom name value => mkApp2 (mkConst ``GroundedValue.custom) (toExpr name) (toExpr value)

private partial def listExpr (elementType : Expr) (elements : List Expr) : Expr :=
  match elements with
  | [] => mkApp (mkConst ``List.nil [.zero]) elementType
  | [element] => mkApp3 (mkConst ``List.cons [.zero]) elementType element
      (mkApp (mkConst ``List.nil [.zero]) elementType)
  | _ =>
      let (first, rest) := elements.splitAt (elements.length / 2)
      mkApp3 (mkConst ``List.append [.zero]) elementType
        (listExpr elementType first) (listExpr elementType rest)

private partial def atomExpr : Atom → Expr
  | .symbol value => mkApp (mkConst ``Atom.symbol) (toExpr value)
  | .var value => mkApp (mkConst ``Atom.var) (toExpr value)
  | .grounded value => mkApp (mkConst ``Atom.grounded) (groundedExpr value)
  | .expression values => mkApp (mkConst ``Atom.expression)
      (listExpr (mkConst ``Atom) (values.map atomExpr))

private def atomsExpr (values : List Atom) : Expr :=
  listExpr (mkConst ``Atom) (values.map atomExpr)

private def equationExpr (equation : Equation) : Expr :=
  mkApp3 (mkConst ``Equation.mk) (toExpr equation.head)
    (atomsExpr equation.arguments) (atomExpr equation.body)

private partial def equationChunksExpr (equations : List Equation) : TermElabM Expr := do
  let listType := mkApp (mkConst ``List [.zero]) (mkConst ``Equation)
  if equations.length ≤ 8 then
    Lean.Meta.mkAuxDefinition (← mkAuxName `sourceEquations) listType
      (listExpr (mkConst ``Equation) (equations.map equationExpr))
  else
    let (first, rest) := equations.splitAt (equations.length / 2)
    return mkApp3 (mkConst ``List.append [.zero]) (mkConst ``Equation)
      (← equationChunksExpr first) (← equationChunksExpr rest)

private def programExpr (program : Program) : TermElabM Expr := do
  return mkApp3 (mkConst ``Program.mk)
    (← equationChunksExpr program.equations)
    (atomsExpr program.declarations) (atomsExpr program.initializers)

scoped syntax "petta_source_file% " str " sha256 " str : term

elab_rules : term
  | `(petta_source_file% $path:str sha256 $pin:str) => do
      let context ← readThe Lean.Core.Context
      let some parent := (System.FilePath.mk context.fileName).parent
        | throwErrorAt path "cannot locate the quoting module"
      let text ← IO.FS.readFile (parent / path.getString)
      let digest := MeTTailCore.Crypto.SHA256.sha256Hex text
      unless digest = pin.getString do
        throwErrorAt pin "source digest differs from the pinned artifact"
      let .ok program := SourceProgram.readProgram text
        | throwErrorAt path "source program reading failed"
      return mkApp3 (mkConst ``SourcePackage.mk) (toExpr text) (toExpr digest) (← programExpr program)

end

end Mettapedia.Languages.MeTTa.PeTTa.SourceQuotation
