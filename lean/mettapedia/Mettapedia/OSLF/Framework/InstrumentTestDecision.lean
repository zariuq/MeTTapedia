import Mettapedia.OSLF.Framework.PartialStructuralObservers

/-!
# Executable structural tests at a finite-arity instrument interface

Boolean evaluation is defined independently of structural satisfaction.
It inspects each requested constructor and every supplied finite argument.
The comparison proves both truth and falsehood readouts, and admitted tests
respect the already earned partial view and equation admission conditions.
The recorded work counts the complete traversal of this procedure; it is
not inferred from structural depth.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations

open scoped BigOperators

universe u

variable {Symbols : Type u} {arity : Symbols → Nat} [DecidableEq Symbols]

def evaluate : Formula Symbols arity → Tree Symbols arity → Bool
  | .top, _ => true
  | .neg body, tree => !(evaluate body tree)
  | .conj first second, tree => evaluate first tree && evaluate second tree
  | .headed constructor formulas, .node second arguments =>
      if same : second = constructor then
        decide (∀ position : Fin (arity constructor),
          evaluate (formulas position)
            (arguments (cast (congrArg (fun symbol => Fin (arity symbol)) same.symm) position)) = true)
      else false

theorem evaluate_iff (formula : Formula Symbols arity) (tree : Tree Symbols arity) :
    evaluate formula tree = true ↔ Satisfies formula tree := by
  induction formula generalizing tree with
  | top => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | neg body inductionHypothesis =>
    change (!(evaluate body tree)) = true ↔ ¬ Satisfies body tree
    rw [← inductionHypothesis tree]
    cases evaluate body tree <;> decide
  | conj first second firstIH secondIH =>
    change (evaluate first tree && evaluate second tree) = true ↔
      Satisfies first tree ∧ Satisfies second tree
    rw [Bool.and_eq_true, firstIH tree, secondIH tree]
  | headed constructor formulas inductionHypothesis =>
    cases tree with
    | node second arguments =>
      by_cases same : second = constructor
      · subst second
        simp only [evaluate, Satisfies]
        change (decide (∀ position, evaluate (formulas position) (arguments position) = true) = true) ↔
          ∃ compared, Tree.node constructor arguments = Tree.node constructor compared ∧
            ∀ position, Satisfies (formulas position) (compared position)
        rw [decide_eq_true_eq]
        constructor
        · intro tested
          exact ⟨arguments, rfl, fun position =>
            (inductionHypothesis position (arguments position)).1 (tested position)⟩
        · rintro ⟨compared, equalTree, holds⟩
          have equalArguments : arguments = compared := eq_of_heq (Tree.node.inj equalTree).2
          subst compared
          exact fun position => (inductionHypothesis position (arguments position)).2 (holds position)
      · change (if identical : second = constructor then _ else false) = true ↔ _
        rw [dif_neg same]
        constructor
        · intro falseTrue; cases falseTrue
        · rintro ⟨_, equalTree, _⟩
          exact False.elim (same (Tree.node.inj equalTree).1)

theorem evaluate_false_iff (formula : Formula Symbols arity) (tree : Tree Symbols arity) :
    evaluate formula tree = false ↔ ¬ Satisfies formula tree := by
  rw [← evaluate_iff formula tree]
  cases evaluate formula tree <;> decide

theorem evaluate_same_view (opened : Policy Symbols) (formula : Formula Symbols arity)
    (admitted : AdmittedFormula opened formula) {first second : Tree Symbols arity}
    (same : view opened first = view opened second) :
    evaluate formula first = evaluate formula second := by
  have truth := (evaluate_iff formula first).trans
    ((satisfies_of_same_view opened formula admitted same).trans (evaluate_iff formula second).symm)
  cases firstValue : evaluate formula first <;> cases secondValue : evaluate formula second <;>
    simp_all

def traversalWork : Formula Symbols arity → Tree Symbols arity → Nat
  | .top, _ => 1
  | .neg body, tree => 1 + traversalWork body tree
  | .conj first second, tree => 1 + traversalWork first tree + traversalWork second tree
  | .headed constructor formulas, .node second arguments =>
      if same : second = constructor then
        1 + ∑ position : Fin (arity constructor),
          traversalWork (formulas position)
            (arguments (cast (congrArg (fun symbol => Fin (arity symbol)) same.symm) position))
      else 1

def structuralDepth : Formula Symbols arity → Nat
  | .top => 0
  | .neg body => structuralDepth body
  | .conj first second => max (structuralDepth first) (structuralDepth second)
  | .headed constructor formulas =>
      1 + Finset.univ.sup (fun position : Fin (arity constructor) => structuralDepth (formulas position))

def repeatedTruth : Nat → Formula Symbols arity
  | 0 => .top
  | count + 1 => .conj .top (repeatedTruth count)

theorem repeatedTruth_holds (count : Nat) (tree : Tree Symbols arity) :
    evaluate (repeatedTruth count) tree = true := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis => simp only [repeatedTruth, evaluate, inductionHypothesis]; rfl

omit [DecidableEq Symbols] in
theorem repeatedTruth_depth (count : Nat) :
    structuralDepth (repeatedTruth (Symbols := Symbols) (arity := arity) count) = 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis => simp only [repeatedTruth, structuralDepth, inductionHypothesis, max_self]

theorem repeatedTruth_work (count : Nat) (tree : Tree Symbols arity) :
    traversalWork (repeatedTruth count) tree = 2 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
    simp only [repeatedTruth, traversalWork, inductionHypothesis]
    omega

theorem fixed_depth_has_unbounded_work (ceiling : Nat) (tree : Tree Symbols arity) :
    ∃ formula : Formula Symbols arity,
      structuralDepth formula = 0 ∧ evaluate formula tree = true ∧
        ceiling < traversalWork formula tree := by
  refine ⟨repeatedTruth ceiling, repeatedTruth_depth ceiling, repeatedTruth_holds ceiling tree, ?_⟩
  rw [repeatedTruth_work]
  omega

end Mettapedia.OSLF.Framework.InstrumentObservations
