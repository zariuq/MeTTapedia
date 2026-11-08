import Init.Data.List.Sort.Basic
import Mettapedia.Languages.Lean.Recursion.Derive

/-!
# The general well-founded relation used by merge

Lean's merge implementation orders its packed pair of lists by a general
well-founded relation. The interface preserves that relation and its proof;
it does not invent a scalar measure that the source fixpoint did not supply.
-/

namespace Mettapedia.Languages.Lean.Recursion.RelationalCore

open Derive

derive_recursion_interface List.merge as Merge

end Mettapedia.Languages.Lean.Recursion.RelationalCore
