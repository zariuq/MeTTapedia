import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationCaptures

/-!
# Scoped capture compilation controls

These raw syntax controls exercise partial reconstruction and capture
avoidance. The generic typing theorem is separate; no typing profile is
postulated for the Boolean head parameters used here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedComputation.Captures.Examples

/-- Three older coordinates exist, but only the oldest is used, repeatedly
and beneath both a computation binder and a native lambda. -/
abbrev nested : Template Bool Bool where
  arity := 3
  input := .head false
  result := .head true
  body := .sequence (.call true (.var 3))
    (.returnValue (.pair (.var 1)
      (.pair (.var 4) (.lam (.pair (.var 0) (.var 5))))))

abbrev typeOnly : Template Bool Bool where
  arity := 3
  input := .var 0
  result := .var 2
  body := .returnValue (.var 0)

abbrev table : Program Bool Bool :=
  ⟨2, fun label => if label = 0 then nested else typeOnly⟩

def environment : Sub Bool 3 1 :=
  Fin.cases (.head false) (Fin.cases (.head true) fun _ => .var 0)

def expected : Code Bool Bool 1 :=
  .sequence (.call true (.var 0))
    (.returnValue (.pair (.head true)
      (.pair (.var 1) (.lam (.pair (.var 0) (.var 2))))))

theorem stores_one_of_three_slots :
    (compile table 0 environment).values = ([(2, .var 0)] : Environment Bool 3 1) := by
  change capture nested.slots environment = _
  decide +kernel

theorem nested_binders_preserve_capture :
    (compile table 0 environment).resume? (.head true) = some (expected, .head true) := by
  decide +kernel

theorem missing_used_slot_rejects :
    (Packet.mk (program := table) 0 ([] : Environment Bool 3 1)).resume? (.head true) = none := by
  decide +kernel

def capturedByInnerLambda : Code Bool Bool 1 :=
  .sequence (.call true (.var 0))
    (.returnValue (.pair (.head true)
      (.pair (.var 1) (.lam (.pair (.var 0) (.var 0))))))

theorem inner_binder_cannot_replace_outer_capture :
    (compile table 0 environment).resume? (.head true) ≠
      some (capturedByInnerLambda, .head true) := by
  decide +kernel

theorem type_dependencies_remain_captured :
    (compile table 1 environment).values =
      ([(0, .head false), (1, .head true)] : Environment Bool 3 1) := by
  change capture typeOnly.slots environment = _
  have supported : typeOnly.support = ({0, 1} : Finset (Fin 3)) := by
    decide +kernel
  have sorted : typeOnly.slots = [0, 1] := by
    rw [Template.slots, supported, Finset.sort_insert]
    · simp
    · intro value present
      simp only [Finset.mem_singleton] at present
      subst value
      decide
    · decide
  rw [sorted]
  rfl

/-- The body and output alone can reconstruct, but the input interface cannot. -/
theorem missing_input_type_dependency_rejects :
    (Packet.mk (program := table) 1 ([(1, .head true)] : Environment Bool 3 1)).resume?
      (.head false) = none := by
  decide +kernel

theorem same_label_different_capture_different_resumption :
    (Packet.mk (program := table) 0 ([(2, .head false)] : Environment Bool 3 1)).resume?
        (.head true) ≠
      (Packet.mk (program := table) 0 ([(2, .head true)] : Environment Bool 3 1)).resume?
        (.head true) := by
  decide +kernel

end ScopedComputation.Captures.Examples
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
