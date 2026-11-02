import Mettapedia.GSLT.LanguageDef.SingleSortABT

/-!
# Simultaneous ABT substitutions fixing a declared ambient interface

The protected prefix names the ambient parameters of one judgment. Loose
indices beyond that prefix remain substitutable. Composition uses the
existing capture-avoiding simultaneous substitution, including field binders;
the term carrier and its application operation are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ProtectedSubstitution

variable {Head : Type}

abbrev Assignment (Head : Type) (width : Nat) :=
  {assignment : Nat → Term Head // ∀ index < width, assignment index = .idx index}

def identity (width : Nat) : Assignment Head width := ⟨Term.idx, fun _ _ => rfl⟩

def compose (width : Nat) (outer inner : Assignment Head width) : Assignment Head width := by
  refine ⟨fun index => Term.substituteMany outer.val (inner.val index), ?_⟩
  intro index inside
  change Term.substituteMany outer.val (inner.val index) = .idx index
  rw [inner.property index inside, Term.substituteMany_idx]
  exact outer.property index inside

theorem parameter_fixed (width : Nat) (assignment : Assignment Head width)
    (index : Nat) (inside : index < width) :
    Term.substituteMany assignment.val (.idx index) = .idx index := by
  rw [Term.substituteMany_idx]
  exact assignment.property index inside

theorem supported_term_fixed (width : Nat) (assignment : Assignment Head width)
    (term : Term Head) (supported : Term.supportedAt width term = true) :
    Term.substituteMany assignment.val term = term := by
  calc
    Term.substituteMany assignment.val term = Term.substituteMany Term.idx term :=
      Term.substituteMany_congr_scoped assignment.property term supported
    _ = term := Term.substituteMany_ids term

theorem compose_apply (width : Nat) (outer inner : Assignment Head width) (term : Term Head) :
    Term.substituteMany (compose width outer inner).val term =
      Term.substituteMany outer.val (Term.substituteMany inner.val term) :=
  (Term.substituteMany_comp outer.val inner.val term).symm

/-- A loose index at the boundary remains a real substitution port. -/
def atBoundary (width : Nat) (replacement : Term Head) : Assignment Head width :=
  ⟨fun index => if index = width then replacement else .idx index,
    fun _index inside => if_neg (Nat.ne_of_lt inside)⟩

theorem atBoundary_apply (width : Nat) (replacement : Term Head) :
    Term.substituteMany (atBoundary width replacement).val (.idx width) = replacement := by
  simp [Term.substituteMany_idx, atBoundary]

theorem boundary_can_change (width : Nat) :
    Term.substituteMany (atBoundary width (.idx (width + 1) : Term Head)).val (.idx width) ≠ .idx width := by
  rw [atBoundary_apply]
  intro same
  have indices := Term.idx.inj same
  omega

end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ProtectedSubstitution
