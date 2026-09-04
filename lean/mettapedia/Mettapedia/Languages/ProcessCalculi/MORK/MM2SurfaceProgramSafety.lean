import Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-!
# Compositional ordinary-MM2 renderer-domain safety

The renderer domain is a conjunction of recursive atom spelling safety and a
per-top-level variable budget.  These lemmas expose its list structure so a
large compiler program can be certified by its named construction stages
instead of normalizing one monolithic Boolean expression.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Renderer-domain safety is preserved and reflected by list concatenation. -/
theorem programSafe_append_iff (left right : List Atom) :
    programSafe (left ++ right) = true ↔
      programSafe left = true ∧ programSafe right = true := by
  simp only [programSafe, programVariableBudget, List.all_append,
    Bool.and_eq_true, List.all_eq_true]
  aesop

/-- Renderer-domain safety exposes exactly the head atom checks and the
recursive tail program check. -/
theorem programSafe_cons_iff (atom : Atom) (atoms : List Atom) :
    programSafe (atom :: atoms) = true ↔
      atomSafe atom = true ∧ atomVariableBudget atom = true ∧
        programSafe atoms = true := by
  simp [programSafe, programVariableBudget, Bool.and_eq_true,
    and_assoc, and_left_comm]

/-- Mapping a list through an atom transform preserves renderer-domain safety
when that transform preserves both exact atom checks. -/
theorem programSafe_map
    (transform : Atom → Atom) (atoms : List Atom)
    (preservesAtomSafe : ∀ atom,
      atomSafe atom = true → atomSafe (transform atom) = true)
    (preservesVariableBudget : ∀ atom,
      atomVariableBudget atom = true → atomVariableBudget (transform atom) = true)
    (safe : programSafe atoms = true) :
    programSafe (atoms.map transform) = true := by
  induction atoms with
  | nil => simpa using safe
  | cons atom atoms induction =>
      rcases (programSafe_cons_iff atom atoms).mp safe with
        ⟨atomSafe, atomBudget, atomsSafe⟩
      apply (programSafe_cons_iff (transform atom) (atoms.map transform)).mpr
      exact ⟨preservesAtomSafe atom atomSafe,
        preservesVariableBudget atom atomBudget,
        induction atomsSafe⟩

section AxiomAudit

#print axioms programSafe_append_iff
#print axioms programSafe_cons_iff
#print axioms programSafe_map

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
