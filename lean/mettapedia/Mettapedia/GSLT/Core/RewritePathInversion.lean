import Mettapedia.GSLT.Core.GSLT

namespace Mettapedia.GSLT.GSLT


/-- Every path is empty or has an initial rewrite and a remaining path. -/
theorem rewritePath_eq_or_first (system : GSLT)
    {source target : system.Term} (path : system.RewritePath source target) :
    source = target ∨
      ∃ next, system.Step source next ∧ Nonempty (system.RewritePath next target) := by
  cases path with
  | nil => exact Or.inl rfl
  | cons step rest => exact Or.inr ⟨_, step, ⟨rest⟩⟩

end Mettapedia.GSLT.GSLT
