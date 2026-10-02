import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Raw retained Cost boundary data

The boundary keeps all source/target type and support coordinates and its
content. Occurrence contexts remain separate traversal evidence. These are
the shared data types of both finite profiles and their continued specialization.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- A boundary is identified by its canonical content together with the
authored result type and the reflective binder support at which it may be
filled.  Content alone is insufficient: the same raw pattern at two sorts or
across two quotation supports is not one typed structural parameter. -/
structure CostRegionBoundary where
  /-- Type of the rigid placeholder presented to the source canonicalizer. -/
  type : TypeExpr
  /-- Binder support of that placeholder in the source open fiber. -/
  support : List TypeExpr
  /-- Exact type of the restored content in the generated Cost fiber.  This
  need not be the uniform static image of `type`: a boundary at a selected
  continuation is retyped by the authored interaction cut. -/
  targetType : TypeExpr
  /-- Exact binder support of the restored content in the Cost fiber. -/
  targetSupport : List TypeExpr
  content : Pattern
deriving Repr, DecidableEq

/-- One occurrence of a maximal foreign region in a Cost static stratum.
`context` is traversal evidence only: filling it with `content` reconstructs
the surrounding root for occurrences emitted by the certified collector
below.  It is deliberately absent from `CostRegionBoundary`, whose semantic
identity remains type, reflective support, and canonical content. -/
structure CostRegionOccurrence where
  context : OneHoleContext
  content : Pattern
deriving Repr, DecidableEq

end Mettapedia.GSLT.LanguageDef
