import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointOperational
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native observations of the canonical communication comparison

The existing endpoint comparison identifies every actual canonical rho
successor of a qualified named network. Consequently, the generated native
diamond commutes with reading predicates along the maintained compiler.
Universal obligations over the same successors commute as well.

These are observations of the explicit canonical runtime and the
occurrence-bearing source fragment. They do not identify arbitrary named pi
equation representatives, quoted observers, or dependent type families. The
universal-successor theorem is distinct from OSLF's predecessor box.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint

/-- A rho native predicate read along the actual network compiler. -/
def compiledPredicate (namespaceName valueName : String)
    (predicate : EquationPredicate canonicalRhoSystem) : EquationPredicate networkSystem :=
  ⟨fun source => predicate.1 (canonicalNetwork source.val namespaceName valueName),
    by intro first second equal; change first = second at equal; cases equal; rfl⟩

/-- Both directions use actual supplied successors: target reflection comes
from `canonical_zigzag`, and source replay uses the authored rho firing. -/
theorem canonicalDiamond_iff (source : QualifiedNetwork) (namespaceName valueName : String)
    (predicate : EquationPredicate canonicalRhoSystem) :
    (semanticDiamond canonicalRhoSystem predicate).1
      (canonicalNetwork source.val namespaceName valueName) ↔
    (semanticDiamond networkSystem (compiledPredicate namespaceName valueName predicate)).1 source := by
  rw [show (semanticDiamond canonicalRhoSystem predicate).1
      (canonicalNetwork source.val namespaceName valueName) ↔
      ∃ target, canonicalRhoSystem.Step (canonicalNetwork source.val namespaceName valueName) target ∧
        predicate.1 target from gsltDiamond_spec _ _ _]
  rw [show (semanticDiamond networkSystem (compiledPredicate namespaceName valueName predicate)).1 source ↔
      ∃ target, networkSystem.Step source target ∧
        (compiledPredicate namespaceName valueName predicate).1 target from gsltDiamond_spec _ _ _]
  constructor
  · rintro ⟨target, firing, holds⟩
    obtain ⟨next, selected, rfl⟩ := canonical_zigzag source namespaceName valueName firing
    exact ⟨next, selected, holds⟩
  · rintro ⟨next, selected, holds⟩
    exact ⟨canonicalNetwork next.val namespaceName valueName,
      selected.canonical_firing source.property.1 source.property.2.current namespaceName valueName,
      holds⟩

/-- An obligation for every actual runtime successor is equivalent to the
corresponding obligation over every qualified named communication. -/
theorem canonicalAllSuccessors_iff (source : QualifiedNetwork) (namespaceName valueName : String)
    (predicate : Pattern → Prop) :
    (∀ target, canonicalRhoSystem.Step (canonicalNetwork source.val namespaceName valueName) target →
      predicate target) ↔
    (∀ next, networkSystem.Step source next →
      predicate (canonicalNetwork next.val namespaceName valueName)) := by
  constructor
  · intro all next selected
    exact all _ (selected.canonical_firing source.property.1 source.property.2.current
      namespaceName valueName)
  · intro all target firing
    obtain ⟨next, selected, rfl⟩ := canonical_zigzag source namespaceName valueName firing
    exact all next selected

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransport
