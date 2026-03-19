import Mettapedia.Languages.GF.HandCrafted.Abstract
import GFCore

namespace Mettapedia.Languages.GF.PGFWitnessIR

open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.HandCrafted.Core (Category)

instance : Nonempty AbstractNode := ⟨.leaf "" (.base "")⟩

inductive ExportedTree where
  | node : String → List ExportedTree → ExportedTree
  deriving Repr

instance : Inhabited ExportedTree := ⟨.node "" []⟩
instance : Nonempty ExportedTree := ⟨.node "" []⟩

-- ============================================================
-- Bridge: GFCore.CheckedExpr → AbstractNode
-- ============================================================

/-- Build a Category arrow type from a GFCore.FunDecl. -/
private def arrowTypeOfDecl (d : GFCore.FunDecl) : Category :=
  d.argCats.foldr (init := Category.base d.resultCat) fun argCat acc =>
    Category.arrow (Category.base argCat) acc

/-- Convert a GFCore.CheckedExpr (verified against GrammarSig) into
    the mettapedia AbstractNode encoding. Since CheckedExpr is already
    type-checked, this conversion is total (no Option needed). -/
partial def checkedExprToAbstractNode (e : GFCore.CheckedExpr) : AbstractNode :=
  let name := e.funName
  if e.isLeaf then
    let cat := match FunctionSig.findByName? name with
      | some f => FunctionSig.resultCategory f.type
      | none => Category.base e.resultCat
    .leaf name cat
  else
    let sig := match FunctionSig.findByName? name with
      | some f => f
      | none => ⟨name, arrowTypeOfDecl e.decl⟩
    .apply sig (e.args.toList.map checkedExprToAbstractNode)

/-- Convert a GFCore.RawTerm to ExportedTree (legacy format). -/
partial def rawTreeToExported (t : GFCore.RawTerm) : ExportedTree :=
  .node t.funName (t.args.toList.map rawTreeToExported)

structure SurfaceWitness where
  label : String
  language : String
  surface : String
  parses : List ExportedTree
  deriving Repr

structure WitnessBundle where
  grammar : String
  usedFunctions : List String
  witnesses : List SurfaceWitness
  deriving Repr

namespace ExportedTree

mutual
  def buildApply? (f : FunctionSig) (args : List ExportedTree) : Option AbstractNode := do
    let converted ← args.mapM toAbstractNode?
    if converted.length = FunctionSig.arity f then
      some (.apply f converted)
    else
      none

  /-- Convert a GF/PGF-exported application tree into the mettapedia abstract-node encoding. -/
  def toAbstractNode? : ExportedTree → Option AbstractNode
    | .node name args => do
        let f ← FunctionSig.findByName? name
        if args.isEmpty then
          if FunctionSig.arity f = 0 then
            some (.leaf name (FunctionSig.resultCategory f.type))
          else
            none
        else
          buildApply? f args
end

/-- Collect all abstract function names appearing in the exported tree. -/
def functionNames : ExportedTree → List String
  | .node name args =>
      name :: (args.foldr (fun arg acc => functionNames arg ++ acc) [])

end ExportedTree

namespace SurfaceWitness

/-- Successfully recovered abstract trees from the exported parse list. -/
def recoveredParses (w : SurfaceWitness) : List AbstractNode :=
  w.parses.filterMap ExportedTree.toAbstractNode?

end SurfaceWitness

namespace WitnessBundle

/-- Successfully recovered abstract trees from all witnesses in the bundle. -/
def recoveredParses (b : WitnessBundle) : List (String × String × String × List AbstractNode) :=
  b.witnesses.map fun w => (w.label, w.language, w.surface, w.recoveredParses)

end WitnessBundle

end Mettapedia.Languages.GF.PGFWitnessIR
