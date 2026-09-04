import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

/-!
# Depth zero is blind to support differences

`substituteAt` lifts an atom value by `depth - support.length`, truncated in
`Nat`.  At depth zero every support length is therefore erased, so two common
atoms with different supports can restore equally at depth zero and diverge at
the next depth.  Any pairing of parallel frontier leaves justified by a single
restoration depth is unsound at the remaining depths.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace MixedSupportDepthZeroBlindness

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The phenomenon is profile-independent; the empty profile suffices. -/
def emptyProfile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile :=
  ⟨[], []⟩

/-- Two common atoms with *different* supports: `"a"` is sealed at the empty
support, `"b"` is exposed over one binder. -/
def mixedSupport : ContextSupport.Support
  | "a" => []
  | _ => [.base "Name"]

/-- Both atoms carry the same value. -/
def sharedAssignment : ContextSupport.Assignment :=
  fun _ => .bvar 0

def sealedAtom : Pattern := .fvar "a"
def exposedAtom : Pattern := .fvar "b"

/-- **Depth zero identifies them.**  The truncation of `0 - 1` to `0` erases
the support difference. -/
theorem restore_eq_at_depth_zero :
    ReflectiveContextSupport.substituteAt
        emptyProfile mixedSupport sharedAssignment 0 sealedAtom =
      ReflectiveContextSupport.substituteAt
        emptyProfile mixedSupport sharedAssignment 0 exposedAtom := by
  simp [ReflectiveContextSupport.substituteAt, mixedSupport, sharedAssignment,
    sealedAtom, exposedAtom, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- **Depth one separates them.**  The sealed atom lifts by one, the exposed
atom by none. -/
theorem restore_ne_at_depth_one :
    ReflectiveContextSupport.substituteAt
        emptyProfile mixedSupport sharedAssignment 1 sealedAtom ≠
      ReflectiveContextSupport.substituteAt
        emptyProfile mixedSupport sharedAssignment 1 exposedAtom := by
  simp [ReflectiveContextSupport.substituteAt, mixedSupport, sharedAssignment,
    sealedAtom, exposedAtom, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- The same separation inside a parallel frame: a one-element parallel whose
sole leaf is the sealed atom agrees with the exposed one at depth zero. -/
theorem parallelFrame_eq_at_depth_zero (collectionType : CollType) :
    ReflectiveContextSupport.substituteAt emptyProfile mixedSupport
        sharedAssignment 0 (.collection collectionType [sealedAtom] none) =
      ReflectiveContextSupport.substituteAt emptyProfile mixedSupport
        sharedAssignment 0 (.collection collectionType [exposedAtom] none) := by
  simp [ReflectiveContextSupport.substituteAt, mixedSupport, sharedAssignment,
    sealedAtom, exposedAtom, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- **and diverges at depth one.**  A leaf pairing certified only at depth
zero therefore fails to be a depth-uniform restoration. -/
theorem parallelFrame_ne_at_depth_one (collectionType : CollType) :
    ReflectiveContextSupport.substituteAt emptyProfile mixedSupport
        sharedAssignment 1 (.collection collectionType [sealedAtom] none) ≠
      ReflectiveContextSupport.substituteAt emptyProfile mixedSupport
        sharedAssignment 1 (.collection collectionType [exposedAtom] none) := by
  simp [ReflectiveContextSupport.substituteAt, mixedSupport, sharedAssignment,
    sealedAtom, exposedAtom, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- **The packaging premise is strictly stronger than depth-zero agreement.**
`RestoresTogether` fails for a pair that a depth-zero key tie identifies. -/
theorem not_restoresTogether_of_mixedSupport (collectionType : CollType) :
    ¬ Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.RestoresTogether emptyProfile mixedSupport
        sharedAssignment (.collection collectionType [sealedAtom] none)
        (.collection collectionType [exposedAtom] none) := by
  intro uniform
  exact parallelFrame_ne_at_depth_one collectionType (uniform 1)

end MixedSupportDepthZeroBlindness
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
