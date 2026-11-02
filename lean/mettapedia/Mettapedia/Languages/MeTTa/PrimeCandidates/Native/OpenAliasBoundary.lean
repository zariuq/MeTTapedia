import Mettapedia.GSLT.LanguageDef.GroundStoreAliasBoundary
import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirection
import Mettapedia.Machines.ShapeScopedUnification

/-!
# The open-alias boundary between existing source owners

TemplateScope's both-sided matcher uses a ground store. The general first-order
solver already handles equations between two unknowns. The discrepancy below
is intentional evidence for a missing shared open-store representation, not a
claim that a whole `let` cannot locally substitute a non-ground body value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.OpenAliasBoundary

open Mettapedia.GSLT.LanguageDef
open TemplateScope

def left : Nm Nat := .src 0
def right : Nm Nat := .src 1

theorem ground_matcher_does_not_create_an_alias :
    matchT2 (S := Nat) SequentialBindingDiscipline.Store.empty
      (.var left) (.var right) = none := by
  decide +kernel

/-- Both future common symbols remain possible in an open equality. No
ground TemplateScope store preserves exactly all those joint possibilities. -/
theorem no_template_ground_store_represents_open_equality :
    ¬ ∃ store : GStore Nat Nat, ∀ assignment : Nm Nat → GVal Nat Nat,
      SequentialBindingDiscipline.Store.CompletedBy store assignment ↔
        assignment left = assignment right :=
  SequentialBindingDiscipline.Store.no_open_alias left right (by decide)
    (.sym 0) (.sym 1) (by decide)

open Mettapedia.Machines

/-- The existing total unifier accepts the corresponding two open variable
occurrences; the solvability witness itself remains open. -/
theorem first_order_solver_accepts_open_alias :
    (ShapeScopedUnification.solve
      (Empty.elim : Empty → ShapeScopedUnification.OpenTerm Nat Nat) 0 0
      (.atom (.inr 0)) (.atom (.inr 1))).isSome = true := by
  obtain ⟨answer, accepted⟩ := ShapeScopedUnification.solve_complete
    (Empty.elim : Empty → ShapeScopedUnification.OpenTerm Nat Nat) 0 0
    (.atom (.inr 0)) (.atom (.inr 1))
    ⟨fun _ => .var ⟨0, 1⟩, rfl⟩
  rw [accepted]
  rfl

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.OpenAliasBoundary
