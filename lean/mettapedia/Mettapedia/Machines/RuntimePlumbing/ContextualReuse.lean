import Mettapedia.Machines.RuntimePlumbing.DependencyStamps
import Mettapedia.Machines.RootPrefixSubstitution

/-!
# Reusing a contextual root without freezing its descendants

The stamp adapter is applied to the existing cell-root reader. A validated
root is still interpreted in the current store. Descendant bindings not read
by the root observer may legitimately change its full image. This permits
root sharing without confusing a contextual syntax view with a frozen value.

Lexical frames are inherited from ContextualSequenceObservation; its field
projection laws keep the entered frame. The single-frame cell adapter here
does not identify native frame handles or prove syntax-owner lifetime.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.ContextualReuse

open ContextualSequenceObservation CellRootObservation ReadOnlyQuery
open DependencyStamps

variable {Literal : Type}

theorem stamped_root_reuse
    (before after : Memory Nat (Option (Term Nat Literal))) (fuel : Nat)
    (source target : Term Nat Literal) (sound : Advances before after)
    (current : check before after (run before.value (query fuel source)).reads = true)
    (found : (run before.value (query fuel source)).answer = some target) :
    (run after.value (query fuel source)).answer = some target ∧
      ∀ result, Image (lexicalStore after.value) ⟨source, ()⟩ result ↔
        Image (lexicalStore after.value) ⟨target, ()⟩ result := by
  have same := checked_observation before after (query fuel source) sound current
  have now : (run after.value (query fuel source)).answer = some target := by
    rw [same]
    exact found
  exact ⟨now, fun result => successful_query_preserves_full_image after.value fuel
    source target now result⟩

/-- Untouched root dependencies suffice; there is no whole-builder version test. -/
theorem unrelated_binding_keeps_root_readout
    (before : Memory Nat (Option (Term Nat Literal))) (fuel : Nat)
    (source : Term Nat Literal) (cell : Nat) (value : Option (Term Nat Literal))
    (untouched : ∀ observed ∈ (run before.value (query fuel source)).reads, observed.1 ≠ cell) :
    run (write before cell value).value (query fuel source) =
      run before.value (query fuel source) :=
  unrelated_write_reuses before (query fuel source) cell value untouched

namespace Controls

def before : Memory Nat (Option (Term Nat Nat)) :=
  ⟨fun cell => if cell = 0 then some (.expr [.var 1])
    else if cell = 1 then some (.leaf 10) else none, fun _ => 0⟩

def after : Memory Nat (Option (Term Nat Nat)) := write before 1 (some (.leaf 20))

theorem changing_a_child_keeps_the_cached_root :
    (run before.value (query 3 (.var 0))).reads = [(0, some (.expr [.var 1]))] ∧
      check before after (run before.value (query 3 (.var 0))).reads = true ∧
      (run after.value (query 3 (.var 0))).answer = some (.expr [.var 1]) :=
  ⟨rfl, rfl, rfl⟩

theorem current_child_has_the_new_image :
    Image (lexicalStore after.value) ⟨.var 1, ()⟩ (.leaf 20) := by
  exact .binding (entered := ⟨.leaf 20, ()⟩) (by rfl) .leaf

theorem freezing_the_old_child_is_wrong :
    ¬ Image (lexicalStore after.value) ⟨.var 1, ()⟩ (.leaf 10) := by
  intro image
  cases image with
  | @binding _ _ entered _ present child =>
    have same : entered = ⟨.leaf 20, ()⟩ := by simpa [lexicalStore, after, write] using present.symm
    subst entered
    cases child

/-- Actual scope separation from the multi-frame model remains essential. -/
theorem entered_scope_is_not_the_caller_scope :
    Image separatingStore ⟨.var 1, 1⟩ (.leaf 23) ∧
      ¬ Image separatingStore ⟨.var 1, 2⟩ (.leaf 23) :=
  ⟨preserved_child_scope, wrong_scope_cannot_return_selected_child⟩

end Controls

end Mettapedia.Machines.RuntimePlumbing.ContextualReuse
