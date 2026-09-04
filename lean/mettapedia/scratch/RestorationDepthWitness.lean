import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# One-depth restoration equality does not propagate

A frame whose atom value mentions an available binder agrees with a literal
bvar frame at exactly one restoration depth and diverges at the next.  So the
pair middle of the reached/reached member apex cannot be discharged from any
single-depth equality (in particular, from the compact pair normal), and must
come from per-leaf value pairing or from the measure recursion.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace RestorationDepthWitness

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
/-- The phenomenon is profile-independent; the empty profile suffices. -/
def emptyProfile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile :=
  ⟨[], []⟩

/-- One atom name, supported by one binder, valued at that binder. -/
def support : ContextSupport.Support :=
  fun _ => [.base "Name"]

def assignment : ContextSupport.Assignment :=
  fun _ => .bvar 0

/-- The two frames: an atom leaf versus the literal bound variable. -/
def atomFrame : Pattern := .fvar "a"
def bvarFrame : Pattern := .bvar 0

/-- **They restore equal at depth 1.** -/
theorem restore_eq_at_depth_one :
    ReflectiveContextSupport.substituteAt
        emptyProfile support assignment 1 atomFrame =
      ReflectiveContextSupport.substituteAt
        emptyProfile support assignment 1 bvarFrame := by
  simp [ReflectiveContextSupport.substituteAt, support, assignment,
    atomFrame, bvarFrame, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- **They diverge at depth 2**: the atom's value lifts, the bvar does not. -/
theorem restore_ne_at_depth_two :
    ReflectiveContextSupport.substituteAt
        emptyProfile support assignment 2 atomFrame ≠
      ReflectiveContextSupport.substituteAt
        emptyProfile support assignment 2 bvarFrame := by
  simp [ReflectiveContextSupport.substituteAt, support, assignment,
    atomFrame, bvarFrame, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

end RestorationDepthWitness
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
