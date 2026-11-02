import Mettapedia.Logic.LinearLogic.TensorSequent

/-!
# Resource-preserving tensor packaging and exchange

Changing the parenthesization, order or unit packaging of a tensor uses only
the sequent calculus's structural tensor/unit rules. These derivations add no
transition uses. They do not delete or duplicate atom occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.TensorSequent

universe uAtom uRule
variable {Atom : Type uAtom} {Rule : Type uRule} {premises conclusions : Rule → Multiset Atom}

@[simp] theorem atomContext_add (left right : Multiset Atom) :
    atomContext (left + right) = atomContext left + atomContext right := Multiset.map_add _ _ _

namespace Derives

def castContext {context other : Multiset (Formula Atom)} {goal : Formula Atom}
    (same : context = other) (proof : Derives premises conclusions context goal) :
    Derives premises conclusions other goal := same ▸ proof

@[simp] theorem uses_castContext {context other : Multiset (Formula Atom)} {goal : Formula Atom}
    (same : context = other) (proof : Derives premises conclusions context goal) :
    (castContext same proof).uses = proof.uses := by cases same; rfl

theorem fromAtoms : ∀ goal : Formula Atom,
    ∃ proof : Derives premises conclusions (atomContext goal.atoms) goal, proof.uses = []
  | .atom name => ⟨.atomId name, rfl⟩
  | .one => ⟨.oneR, rfl⟩
  | .tensor left right => by
      obtain ⟨first, firstUses⟩ := fromAtoms left
      obtain ⟨second, secondUses⟩ := fromAtoms right
      have source : atomContext left.atoms + atomContext right.atoms =
          atomContext (Formula.tensor left right).atoms := (atomContext_add _ _).symm
      refine ⟨castContext source (.tensorR first second), ?_⟩
      simp only [uses_castContext, uses, firstUses, secondUses, List.nil_append]

/-- Introduce one tensor formula on the left, without changing the selected
transition leaves. This includes exchange inside its atom bundle. -/
theorem condenseLeft : ∀ (formula : Formula Atom) (context : Multiset (Formula Atom)) (goal : Formula Atom)
    (proof : Derives premises conclusions (atomContext formula.atoms + context) goal),
    ∃ packed : Derives premises conclusions (formula ::ₘ context) goal, packed.uses = proof.uses
  | .atom _name, _context, _goal, proof => ⟨proof, rfl⟩
  | .one, context, _goal, proof => by
      have same : atomContext (Formula.one (Atom := Atom)).atoms + context = context := by
        simp [atomContext, Formula.atoms]
      exact ⟨.oneL (castContext same proof), uses_castContext _ _⟩
  | .tensor left right, context, goal, proof => by
      have firstContext : atomContext (Formula.tensor left right).atoms + context =
          atomContext left.atoms + (atomContext right.atoms + context) := by
        simp only [Formula.atoms, atomContext_add, add_assoc]
      obtain ⟨first, firstUses⟩ := condenseLeft left (atomContext right.atoms + context) goal
        (castContext firstContext proof)
      have secondContext : left ::ₘ (atomContext right.atoms + context) =
          atomContext right.atoms + (left ::ₘ context) := by
        simp only [← Multiset.singleton_add]
        ac_rfl
      obtain ⟨second, secondUses⟩ := condenseLeft right (left ::ₘ context) goal (castContext secondContext first)
      refine ⟨.tensorL (castContext (Multiset.cons_swap _ _ _) second), ?_⟩
      simp only [uses, uses_castContext, secondUses, firstUses]

/-- A tensor-only presentation change is derived with no declared transition
uses. Equality of atom multisets retains duplicates and the empty boundary. -/
theorem repackage (left right : Formula Atom) (same : left.atoms = right.atoms) :
    ∃ proof : Derives premises conclusions {left} right, proof.uses = [] := by
  obtain ⟨raw, noUses⟩ := fromAtoms (premises := premises) (conclusions := conclusions) right
  have source : atomContext right.atoms = atomContext left.atoms + 0 := by rw [same]; simp
  obtain ⟨packed, packedUses⟩ := condenseLeft left 0 right (castContext source raw)
  exact ⟨packed, by simpa only [uses_castContext, noUses] using packedUses⟩

theorem repackageGoal {context : Multiset (Formula Atom)} {left right : Formula Atom}
    (proof : Derives premises conclusions context left) (same : left.atoms = right.atoms) :
    ∃ packed : Derives premises conclusions context right, packed.uses = proof.uses := by
  obtain ⟨conversion, noUses⟩ := repackage (premises := premises) (conclusions := conclusions) left right same
  refine ⟨castContext (add_zero _) (.cut proof conversion), ?_⟩
  simp only [uses_castContext, uses, noUses, List.append_nil]

/-- All hypotheses can be packaged into one tensor, preserving each linear
occurrence. No transition declaration is invoked to do so. -/
theorem contextBundle (context : Multiset (Formula Atom)) :
    ∃ proof : Derives premises conclusions context (Formula.ofMultiset (contextAtoms context)), proof.uses = [] := by
  induction context using Multiset.induction_on with
  | empty =>
      obtain ⟨proof, sameUses⟩ := repackageGoal (.oneR (premises := premises) (conclusions := conclusions))
        (right := Formula.ofMultiset (contextAtoms 0)) (by simp [Formula.atoms])
      exact ⟨proof, sameUses⟩
  | @cons formula context ih =>
      obtain ⟨tail, tailUses⟩ := ih
      obtain ⟨packed, packedUses⟩ := repackageGoal (.tensorR (identity formula) tail)
        (right := Formula.ofMultiset (contextAtoms (formula ::ₘ context))) (by simp [Formula.atoms])
      refine ⟨castContext (Multiset.singleton_add _ _) packed, ?_⟩
      simp only [uses_castContext, packedUses, uses, uses_identity, tailUses, List.nil_append]

end Derives

end Mettapedia.Logic.LinearLogic.TensorSequent
