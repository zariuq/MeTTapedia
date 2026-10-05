import Mettapedia.GSLT.Topos.PresheafPosetRestriction
import Mettapedia.OSLF.PresheafNativeType.TheoryTranslationCounterexample

/-!
# Positive and negative controls for native theory restriction

The same two-context example distinguishes cartesian closed theory change
from preservation of predicate implication. A proper context subset closed
under restriction preserves implication; a different singleton subset does not.
The counterexample is reused from `TheoryTranslationCounterexample`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.PresheafNativeType.TheoryRestriction

open _root_.CategoryTheory Opposite Mettapedia.GSLT.Topos
open LogicalTransport

namespace Example

open TheoryTranslationCounterexample

/-- The previously established failure is witnessed by the generic
restriction functor, rather than a different predicate interpretation. -/
theorem restriction_loses_implication :
    LogicalTransport.restrictPredicate selectTerminal
        (supportedAtSource ⇨ (⊥ : Subfunctor terminalPresheaf)) ≠
      LogicalTransport.restrictPredicate selectTerminal supportedAtSource ⇨
        LogicalTransport.restrictPredicate selectTerminal (⊥ : Subfunctor terminalPresheaf) :=
  actual_precomposition_does_not_preserve_implication

theorem selectTerminal_not_lifts : ¬ LiftsRestrictions selectTerminal := by
  intro lifting
  exact restriction_loses_implication
    (restrict_implication_eq lifting supportedAtSource ⊥)

/-- Selecting the bottom context gives a proper, restriction-closed part of
the same two-object context category. -/
def selectSource : PUnit.{1} ⥤ Bool := (Functor.const PUnit).obj false

theorem selectSource_lifts : LiftsRestrictions selectSource := by
  intro U V i
  have below : V.unop ≤ false := le_of_op_hom i
  have equal : selectSource.op.obj U = V :=
    Opposite.unop_injective (le_antisymm below bot_le).symm
  exact ⟨U, 𝟙 U, eqToIso equal, Subsingleton.elim _ _⟩

theorem selectSource_misses_context :
    ¬ ∃ U : PUnit.{1}, selectSource.obj U = true := by
  rintro ⟨U, equal⟩
  change false = true at equal
  cases equal

theorem source_restriction_preserves_implication
    {P : Boolᵒᵖ ⥤ Type} (φ ψ : Subfunctor P) :
    LogicalTransport.restrictPredicate selectSource (φ ⇨ ψ) =
      LogicalTransport.restrictPredicate selectSource φ ⇨
        LogicalTransport.restrictPredicate selectSource ψ :=
  restrict_implication_eq selectSource_lifts φ ψ

/-- Exact logical transport does not require reaching every target context.
The positive and negative functors differ in closure under restriction. -/
theorem context_closure_discriminates :
    LiftsRestrictions selectSource ∧ ¬ LiftsRestrictions selectTerminal ∧
      (¬ ∃ U : PUnit.{1}, selectSource.obj U = true) :=
  ⟨selectSource_lifts, selectTerminal_not_lifts, selectSource_misses_context⟩

end Example

end Mettapedia.OSLF.PresheafNativeType.TheoryRestriction
