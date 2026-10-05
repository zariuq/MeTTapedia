import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep

/-!
# Structural transport of positive rho reduction paths

Structural congruence transports both endpoints of a positive path without
changing its communication count. Positivity matters: a zero-step path uses
literal endpoint equality, whereas structural congruence need not be equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Reduction

namespace ReducesN

/-- A positive execution exposes a first communication, so its source is
not a normal form. -/
theorem not_normal {count : Nat} {source target : Pattern}
    (path : ReducesN (count + 1) source target) : ¬ NormalForm source := by
  cases path with
  | succ first _ => exact fun quiet => quiet ⟨_, ⟨first⟩⟩

noncomputable def transport {count : Nat} {source target source' target' : Pattern}
    (path : ReducesN (count + 1) source target)
    (before : StructuralCongruence source' source)
    (after : StructuralCongruence target target') : ReducesN (count + 1) source' target' := by
  induction count generalizing source target source' target' with
  | zero =>
      cases path with
      | succ first rest =>
          cases rest
          exact .succ (.equiv before first after) (.zero _)
  | succ count ih =>
      cases path with
      | succ first rest =>
          exact .succ (.equiv before first (.refl _)) (ih rest (.refl _) after)

end ReducesN
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
