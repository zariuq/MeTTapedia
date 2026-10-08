import Mettapedia.OSLF.Framework.InstrumentTestDecision

/-!
# Decidable equality of actual finite-arity instrument trees

Complete constructor equality compares the root and every finite child.
It is independent of the observational policy: unopened constructors do not
erase distinctions from the received payload or the retained event receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations

universe u

variable {Symbols : Type u} {arity : Symbols → Nat} [DecidableEq Symbols]

def treeEqual : Tree Symbols arity → Tree Symbols arity → Bool
  | .node constructor first, .node second next =>
    if same : second = constructor then
      decide (∀ position : Fin (arity constructor),
        treeEqual (first position)
          (next (cast (congrArg (fun symbol => Fin (arity symbol)) same.symm) position)) = true)
    else false

theorem treeEqual_iff (first second : Tree Symbols arity) :
    treeEqual first second = true ↔ first = second := by
  induction first generalizing second with
  | node constructor arguments inductionHypothesis =>
    cases second with
    | node other compared =>
      by_cases same : other = constructor
      · subst other
        unfold treeEqual
        rw [dif_pos rfl]
        change (decide (∀ position, treeEqual (arguments position) (compared position) = true) = true) ↔ _
        rw [decide_eq_true_eq]
        constructor
        · intro checked
          congr 1
          funext position
          exact (inductionHypothesis position (compared position)).1 (checked position)
        · intro equalTree
          have equalArguments : arguments = compared := eq_of_heq (Tree.node.inj equalTree).2
          subst compared
          exact fun position => (inductionHypothesis position (arguments position)).2 rfl
      · change (if identical : other = constructor then _ else false) = true ↔ _
        rw [dif_neg same]
        constructor
        · intro impossible; cases impossible
        · intro equalTree
          exact False.elim (same (Tree.node.inj equalTree).1.symm)

instance treeDecidableEq : DecidableEq (Tree Symbols arity) := fun first second =>
  if checked : treeEqual first second = true then
    .isTrue ((treeEqual_iff first second).1 checked)
  else .isFalse (fun same => checked ((treeEqual_iff first second).2 same))

end Mettapedia.OSLF.Framework.InstrumentObservations
