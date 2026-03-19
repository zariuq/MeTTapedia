/-
# GFCore.Export — Erase CheckedExpr back to RawTerm

For the linearization direction: Lean produces a CheckedExpr,
erases it to RawTerm, serializes to JSON, and GF linearizes it.
-/

import GFCore.Syntax

namespace GFCore

/-- Erase a CheckedExpr back to an untyped RawTerm (with category hints).
    Used for the Lean → GF linearization direction. -/
partial def erase (e : CheckedExpr) : RawTerm :=
  .app e.funName (some e.resultCat) (e.args.map erase)

/-- Erase without category hints (minimal JSON output). -/
partial def eraseMinimal (e : CheckedExpr) : RawTerm :=
  .app e.funName none (e.args.map eraseMinimal)

end GFCore
