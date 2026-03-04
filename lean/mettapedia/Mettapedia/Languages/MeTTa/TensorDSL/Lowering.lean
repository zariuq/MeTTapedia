import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.Languages.MeTTa.TensorDSL.Reduction

/-!
# MeTTa Tensor DSL Lowering to MeTTaIL

Lowering bridge from TensorDSL expressions into `MeTTaIL.Syntax.Pattern`.
-/

namespace Mettapedia.Languages.MeTTa.TensorDSL

open Mettapedia.OSLF.MeTTaIL.Syntax

def varianceCtor : Variance → String
  | .up => "U"
  | .down => "D"

def indexToPattern (ix : Index) : Pattern :=
  .apply (varianceCtor ix.variance) [.fvar ix.name]

def exprToPattern : Expr → Pattern
  | .tensor head idxs => .apply "T" (.fvar head :: idxs.map indexToPattern)
  | .add lhs rhs => .apply "t+" [exprToPattern lhs, exprToPattern rhs]
  | .mul lhs rhs => .apply "t*" [exprToPattern lhs, exprToPattern rhs]
  | .contract name body => .apply "contract" [.fvar name, exprToPattern body]
  | .partialD body ix => .apply "partial" [exprToPattern body, indexToPattern ix]
  | .covD body ix conn => .apply "covD" [exprToPattern body, indexToPattern ix, .fvar conn]
  | .metric i j => .apply "metric" [indexToPattern i, indexToPattern j]
  | .invMetric i j => .apply "invMetric" [indexToPattern i, indexToPattern j]
  | .delta i j => .apply "delta" [indexToPattern i, indexToPattern j]

def valenceToPattern (v : Valence) : Pattern :=
  .apply "Valence"
    [ .apply "Up" (v.up.map Pattern.fvar)
    , .apply "Down" (v.down.map Pattern.fvar)
    ]

def lowerAsEquation (lhs rhs : Expr) : Pattern :=
  .apply "=" [exprToPattern lhs, exprToPattern rhs]

theorem exprToPattern_tensor_shape (head : String) (idxs : List Index) :
    exprToPattern (.tensor head idxs) = .apply "T" (.fvar head :: idxs.map indexToPattern) := by
  rfl

theorem valenceToPattern_shape (v : Valence) :
    ∃ ups downs,
      valenceToPattern v = .apply "Valence" [ .apply "Up" ups, .apply "Down" downs ] := by
  refine ⟨v.up.map Pattern.fvar, v.down.map Pattern.fvar, ?_⟩
  rfl

end Mettapedia.Languages.MeTTa.TensorDSL
