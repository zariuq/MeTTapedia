import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic

/-!
# MeTTa Tensor DSL Syntax

Foundational syntax for an optional tensor/index profile that is portable
across HE MeTTa, PeTTa, and MeTTa-Compiler.

Provenance:
- Original implementation in this repository.
- Index-variance UX direction inspired by RelativityToolkit v1.5.1 notes:
  https://github.com/rebcabin/RelativityToolkit/releases/tag/v1.5.1
-/

namespace Mettapedia.Languages.MeTTa.TensorDSL

inductive Variance where
  | up
  | down
deriving DecidableEq, Repr, Inhabited, BEq

structure Index where
  variance : Variance
  name : String
deriving DecidableEq, Repr, Inhabited, BEq

namespace Index

def up (name : String) : Index := ⟨.up, name⟩

def down (name : String) : Index := ⟨.down, name⟩

def isUp (ix : Index) : Bool :=
  ix.variance == .up

def isDown (ix : Index) : Bool :=
  ix.variance == .down

end Index

inductive Expr where
  | tensor : String → List Index → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | contract : String → Expr → Expr
  | partialD : Expr → Index → Expr
  | covD : Expr → Index → String → Expr
  | metric : Index → Index → Expr
  | invMetric : Index → Index → Expr
  | delta : Index → Index → Expr
deriving DecidableEq, Repr, Inhabited, BEq

namespace Expr

/-- Map an index transformation through an expression. -/
def mapIndices (f : Index → Index) : Expr → Expr
  | .tensor head idxs => .tensor head (idxs.map f)
  | .add lhs rhs => .add (mapIndices f lhs) (mapIndices f rhs)
  | .mul lhs rhs => .mul (mapIndices f lhs) (mapIndices f rhs)
  | .contract name body => .contract name (mapIndices f body)
  | .partialD body ix => .partialD (mapIndices f body) (f ix)
  | .covD body ix conn => .covD (mapIndices f body) (f ix) conn
  | .metric i j => .metric (f i) (f j)
  | .invMetric i j => .invMetric (f i) (f j)
  | .delta i j => .delta (f i) (f j)

/-- Collect all indices occurring in an expression. -/
def collectIndices : Expr → List Index
  | .tensor _ idxs => idxs
  | .add lhs rhs => collectIndices lhs ++ collectIndices rhs
  | .mul lhs rhs => collectIndices lhs ++ collectIndices rhs
  | .contract _ body => collectIndices body
  | .partialD body ix => ix :: collectIndices body
  | .covD body ix _ => ix :: collectIndices body
  | .metric i j => [i, j]
  | .invMetric i j => [i, j]
  | .delta i j => [i, j]

end Expr

end Mettapedia.Languages.MeTTa.TensorDSL
