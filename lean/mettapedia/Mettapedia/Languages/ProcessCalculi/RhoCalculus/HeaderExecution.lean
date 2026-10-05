import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem

/-!
# Actual authored execution receipts for sorted rho headers

Header formation and the selected occurrence's concrete matcher/application
proof generate a step in the existing parameterized authored theory. Both
supplied endpoints may use other sorted structural representatives. This
conversion is independent of any source compiler or scheduling invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderExecution

open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion

def headerProcess {free : FreeSortContext} (heads : List Header)
    (typed : ∀ head ∈ heads, head.Typed free) (safe : ∀ head ∈ heads, head.Safe) :
    ParameterizedRewriteSystem.Process free :=
  ⟨parallel heads, (ParameterizedRewriteSystem.process_iff _ _).mpr
    ⟨parallel_typed typed, parallel_safe safe⟩⟩

def contractumProcess {free : FreeSortContext} (heads : List Header)
    (typed : ∀ head ∈ heads, head.Typed free) (safe : ∀ head ∈ heads, head.Safe)
    (selected : Selection heads) : ParameterizedRewriteSystem.Process free :=
  ⟨selected.contractum, (ParameterizedRewriteSystem.process_iff _ _).mpr
    (selected.contractum_preserves typed safe)⟩

/-- The authored COMM is constructed without a source execution premise. -/
theorem selection_step {free : FreeSortContext} (heads : List Header)
    (typed : ∀ head ∈ heads, head.Typed free) (safe : ∀ head ∈ heads, head.Safe)
    (selected : Selection heads) :
    (ParameterizedRewriteSystem.theory free).Step (headerProcess heads typed safe)
      (contractumProcess heads typed safe selected) :=
  ParameterizedRewriteSystem.of_step ⟨1, selected.authored typed⟩

/-- Structural saturation keeps the independently supplied literal
endpoints around the selected primitive receipt. -/
theorem supplied_selection_step {free : FreeSortContext} (heads : List Header)
    (typed : ∀ head ∈ heads, head.Typed free) (safe : ∀ head ∈ heads, head.Safe)
    (selected : Selection heads) (before after : ParameterizedRewriteSystem.Process free)
    (sourceEquation : StructuralCongruence before.1 (parallel heads))
    (targetEquation : StructuralCongruence selected.contractum after.1) :
    (ParameterizedRewriteSystem.theory free).Step before after := by
  apply ParameterizedRewriteSystem.step_iff.mpr
  refine ⟨headerProcess heads typed safe, contractumProcess heads typed safe selected,
    ?_, ⟨1, selected.authored typed⟩, ?_⟩
  · exact (ParameterizedRewriteSystem.equations_iff_structuralCongruence _ _).mpr sourceEquation
  · exact (ParameterizedRewriteSystem.equations_iff_structuralCongruence _ _).mpr targetEquation

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderExecution
