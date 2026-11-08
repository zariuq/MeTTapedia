import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# A resolved value does not determine the retained-cell update

Scoped payload exposure preserves marks. The final update of retained raw
binding cells uses substitution which may reopen a changed ancestor. These
two traversals must not be collapsed into a function of the already-resolved
value alone. Raw cell syntax and its provenance remain a separate boundary.

This obstruction does not assert that the full certified Frame lacks enough
information: its raw constraints and a native representation relation may
retain more than the resolved value used in the counterexample.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPublicationProvenance

open Mettapedia.Languages.MeTTa.HE.Spec.Eval

def privateValue : String → Entry.Value :=
  fun name => if name = "private" then .symbol "Number" else .var name

def unresolvedCell : Entry.Value := .expression .held [.symbol "Box", .var "private"]
def resolvedCell : Entry.Value := .expression .held [.symbol "Box", .symbol "Number"]
def reopenedCell : Entry.Value := .expression .active [.symbol "Box", .symbol "Number"]

theorem same_resolved_value :
    Entry.Value.substitute .preserve privateValue unresolvedCell = resolvedCell ∧
      Entry.Value.substitute .preserve privateValue resolvedCell = resolvedCell := by
  simp [Entry.Value.substitute, Entry.Value.rebuildStatus, privateValue, unresolvedCell, resolvedCell]

theorem different_retained_cell_updates :
    Entry.Value.substitute .reopenChanged privateValue unresolvedCell = reopenedCell ∧
      Entry.Value.substitute .reopenChanged privateValue resolvedCell = resolvedCell ∧
      reopenedCell ≠ resolvedCell := by
  simp [Entry.Value.substitute, Entry.Value.rebuildStatus, privateValue,
    unresolvedCell, resolvedCell, reopenedCell, Entry.Value.erase]

/-- A replacement for the retained-cell pass cannot consume only the
preserving resolver's output. The two real cell updates refute that loss of
input information. -/
theorem no_resolved_value_only_update :
    ¬ ∃ update : Entry.Value → Entry.Value,
      ∀ cell, update (Entry.Value.substitute .preserve privateValue cell) =
        Entry.Value.substitute .reopenChanged privateValue cell := by
  rintro ⟨update, exactUpdate⟩
  have first := exactUpdate unresolvedCell
  have second := exactUpdate resolvedCell
  rw [same_resolved_value.1, different_retained_cell_updates.1] at first
  rw [same_resolved_value.2, different_retained_cell_updates.2.1] at second
  exact different_retained_cell_updates.2.2 (first.symm.trans second)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPublicationProvenance
