import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.OccurrenceKey
import Mathlib.Data.Fintype.Card

/-!
# A bounded global occurrence codec cannot cover all origins

This forbids silent truncation, not bounded native implementations. A finite
live context may use a checked namespace or explicit fallback, and retired
regions may recycle slots under a new generation. The impossibility concerns
one total injective encoding of every unbounded origin into a fixed finite type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BoundedCodec

theorem no_total_injective_code (capacity : Nat) (encode : OccurrenceKey → Fin capacity) :
    ¬ Function.Injective encode := by
  intro injective
  let keys : Fin (capacity + 1) → OccurrenceKey := fun slot => ⟨0, 0, 0, slot.val⟩
  have keyInjective : Function.Injective keys := by
    intro first second same
    apply Fin.ext
    exact congrArg OccurrenceKey.slot same
  have crowded := Fintype.card_le_of_injective (encode ∘ keys) (injective.comp keyInjective)
  simp only [Fintype.card_fin] at crowded
  omega

#print axioms no_total_injective_code

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BoundedCodec
