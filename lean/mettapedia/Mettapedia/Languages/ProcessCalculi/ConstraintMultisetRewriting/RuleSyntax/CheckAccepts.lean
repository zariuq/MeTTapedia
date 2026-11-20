import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# A predicate check reads only the rows its pattern matches

At a solution, the predicate query `Check.predicate q p` holds exactly when its quantifier accepts the
set of present rows that the solution equates with `p` (`checkHolds_predicate_iff`). So every law that
transports the matched rows (renaming of identities, rows equivalent at the solution, shared rows read
as regions) transports every predicate query at once.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

open Interface (Frames)

universe uO uT uH uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
variable (X : Frames Tm Hom) {O : Type uOcc}

/-- **A predicate check is its quantifier on the matched rows.** -/
theorem checkHolds_predicate_iff {a b : Obj} (σ : Hom a b) (row : O → Tm a) (present : Finset O)
    (quantifier : Quantifier) (pattern : Tm a) :
    checkHolds X σ row present (.predicate quantifier pattern) ↔
      quantifier.Accepts (matchesAt X σ row present pattern) := by
  cases quantifier with
  | any =>
      constructor
      · rintro ⟨o, present', equated⟩
        exact ⟨o, (mem_matchesAt X σ row present pattern o).mpr ⟨present', equated⟩⟩
      · rintro ⟨o, inside⟩
        obtain ⟨present', equated⟩ := (mem_matchesAt X σ row present pattern o).mp inside
        exact ⟨o, present', equated⟩
  | none =>
      exact (none_iff_count_zero X σ row present pattern).trans Finset.card_eq_zero

#print axioms checkHolds_predicate_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
