import Mettapedia.Languages.MeTTa.PureKernel.Universe.AlgebraicParallel

/-!
# The repeated-metavariable boundary of elementary parallel reduction

This module gives a minimal negative control for algebraic parallel
reduction.  A rule whose left side duplicates a metavariable can contract a
coherent redex immediately, while a congruence step can develop only one of
the two occurrences.  The resulting peak need not close in one parallel
step.  A tiny term algebra keeps the counterexample independent of beta,
typing, universes, and any particular native family.

The example does not say that every non-left-linear rewrite system is
nonconfluent.  It says that a left-linearity-free one-step diamond theorem is
false: a richer residual/coherence argument is genuinely required.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace AlgebraicParallel
namespace NonlinearBoundary

open AlgebraicSchema

/-- A minimal term algebra with one reducible atom, one rigid result, and a
binary context in which metavariables can be duplicated. -/
inductive ToyTerm where
  | redex
  | atom
  | result
  | node : ToyTerm → ToyTerm → ToyTerm
  deriving DecidableEq, Repr

/-- Parallel development for the toy algebra.  `collapse` is the single
non-left-linear algebraic rule: its argument occurs in both source slots. -/
inductive ToyParallel : ToyTerm → ToyTerm → Prop where
  | refl (term : ToyTerm) : ToyParallel term term
  | redex : ToyParallel .redex .atom
  | node {left left' right right'} :
      ToyParallel left left' →
      ToyParallel right right' →
        ToyParallel (.node left right) (.node left' right')
  | collapse (term : ToyTerm) :
      ToyParallel (.node term term) .result

/-- The open `node x x` pattern has the same repeated-variable geometry as
the toy collapse rule. -/
def duplicatedPattern : Tm Unit 1 :=
  .pair (.var 0) (.var 0)

theorem duplicatedPattern_not_leftLinear :
    ¬ LeftLinear duplicatedPattern :=
  not_leftLinear_of_repeatedAt (index := (0 : Fin 1)) (by
    change 2 ≤ 2
    exact Nat.le_refl 2)

/-- The coherent source contracts at the duplicated-variable root. -/
theorem rootBranch :
    ToyParallel (.node .redex .redex) .result :=
  .collapse .redex

/-- Congruence may instead develop just the first copy. -/
theorem splitBranch :
    ToyParallel (.node .redex .redex) (.node .atom .redex) :=
  .node .redex (.refl .redex)

private theorem result_rigid
    {target : ToyTerm} (reduction : ToyParallel .result target) :
    target = .result := by
  cases reduction
  rfl

private theorem split_not_to_result :
    ¬ ToyParallel (.node .atom .redex) .result := by
  intro reduction
  cases reduction

/-- The elementary parallel relation for a duplicated-variable schema does
not satisfy the one-step diamond law. -/
theorem duplicateParallel_not_diamond :
    ¬ (∀ {source left right : ToyTerm},
      ToyParallel source left →
      ToyParallel source right →
        ∃ common,
          ToyParallel left common ∧ ToyParallel right common) := by
  intro diamond
  rcases diamond rootBranch splitBranch with
    ⟨common, resultToCommon, splitToCommon⟩
  have commonEquation := result_rigid resultToCommon
  subst common
  exact split_not_to_result splitToCommon

/-! ## Axiom audit -/

#print axioms rootBranch
#print axioms splitBranch
#print axioms duplicatedPattern_not_leftLinear
#print axioms duplicateParallel_not_diamond

end NonlinearBoundary
end AlgebraicParallel
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
