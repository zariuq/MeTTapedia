import Mettapedia.Enactive.Razor
import Mettapedia.InformationTheory.CodebookRelativity

/-!
# Ockham profiles and the exact scope of codebook-relativity no-go results

The expression "Ockham's razor" names several distinct methodological
principles.  This module separates two which are especially easy to conflate:

* Ockham's historical ontological principle rejects entities not needed by the
  accepted explanatory obligations;
* a description-length selector strictly prefers the shorter representation in
  a declared codebook.

Michael Timothy Bennett's recoding argument applies to the second principle
when it is proposed as a representation-invariant ideal.  It does not refute
the first, nor does it show that a fixed-codebook MDL method lacks local
statistical value.  Theorems below make that scope exact: the historical
criterion is codebook-invariant because it does not inspect the codebook,
whereas strict description-length selection reverses under a two-codeword
swap, both on a finite class and on the countably infinite class constructed in
`CodebookRelativity`.

This distinction also matches modern learning-theoretic cautions.  Sterkenburg
derives a model-relative means–ends justification for class-level capacity and
regularization only when a reliability theorem connects the selected
complexity to generalization.  Sterkenburg, Herrmann, and Romeijn warn that
calling an individual-model property "simplicity" cannot replace such a
theorem.

References:

* William of Ockham, *Summa Logicae*, Part I, selected chapters, especially
  the necessity-qualified economy principle.
* K. T. Kelly, *Justification as Truth-Finding Efficiency: How Ockham's Razor
  Works* (2004), for mind-change/truth-finding efficiency rather than a coding
  prior.
* P. Grünwald, *A Tutorial Introduction to the Minimum Description Length
  Principle* (2004), for code-relative model-and-data selection.
* T. F. Sterkenburg, *Statistical Learning Theory and Occam's Razor: The Core
  Argument* (2024/2025) and *Regularization* (2026).
* T. F. Sterkenburg, D. A. Herrmann, and J.-W. Romeijn, *Benign
  Interpolation and Occam's Razor* (2026).
* M. T. Bennett, *The Wrong Razor*, Corollary A.9 and Remark A.10 in the
  complete-proofs appendix (2026).
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.OckhamSteelman

open Mettapedia.Enactive.Razor
open Mettapedia.InformationTheory.CodebookRelativity

universe uCandidate

/-! ## Criteria which do and do not depend on codebooks -/

/-- Regard an existing constrained criterion as a codebook-indexed selector
without changing its semantics. -/
def criterionSelector {Candidate : Type uCandidate}
    (criterion : Criterion Candidate) : Selector Candidate :=
  liftRelation criterion.atLeastAsGood

/-- Every criterion whose preference relation is already defined independently
of coding is invariant under codebook reindexing. -/
theorem criterionSelector_invariant
    {Candidate : Type uCandidate} (criterion : Criterion Candidate) :
    CodebookInvariant (criterionSelector criterion) :=
  liftRelation_codebookInvariant criterion.atLeastAsGood

/-- The ordinary fixed-codebook description-length preference. -/
def codeLengthSelector {Candidate : Type uCandidate} : Selector Candidate :=
  fun codebook left right ↦ codebook.length left ≤ codebook.length right

/-- This selector genuinely uses shorter-is-better: a strict length inequality
produces a strict preference. -/
theorem codeLengthSelector_strictlyPrefersShorter
    {Candidate : Type uCandidate} :
    StrictlyPrefersShorter (codeLengthSelector (Candidate := Candidate)) := by
  intro codebook shorter longer less
  exact ⟨less.le, not_le_of_gt less⟩

/-! ## Ockham's historical necessity-qualified profile -/

namespace OntologicalCanary

inductive Theory where
  | sufficient
  | redundantEntity
  | insufficient
deriving DecidableEq, Fintype

/-- Both explanatory theories meet the declared obligation.  The third is not
eligible merely because it mentions fewer entities. -/
def necessary : Theory → Prop
  | .sufficient | .redundantEntity => True
  | .insufficient => False

def entityCount : Theory → Nat
  | .sufficient => 1
  | .redundantEntity => 2
  | .insufficient => 0

def criterion : Criterion Theory :=
  ontologicalParsimony necessary entityCount

/-- The sufficient theory is globally optimal: it satisfies the necessity
proviso and adds no redundant entity. -/
theorem sufficient_isOptimal : criterion.IsOptimal .sufficient := by
  constructor
  · simp [criterion, ontologicalParsimony, Criterion.ofCost, necessary]
  · intro other admissible
    cases other <;>
      simp [criterion, ontologicalParsimony, Criterion.ofCost, necessary,
        entityCount] at admissible ⊢

/-- Fewer entities never rescues a theory that fails the explanatory
obligation. -/
theorem insufficient_not_admissible : ¬ criterion.admissible .insufficient := by
  simp [criterion, ontologicalParsimony, Criterion.ofCost, necessary]

/-- Ontological parsimony is unaffected by arbitrary codebook changes. -/
theorem criterion_codebookInvariant :
    CodebookInvariant (criterionSelector criterion) :=
  criterionSelector_invariant criterion

end OntologicalCanary

/-! ## Finite and infinite ranking reversals -/

/-- A source-faithful two-hypothesis codebook: the codewords have lengths one
and two and neither is a prefix of the other. -/
def boolCodebook : PrefixCodebook Bool where
  encode
    | false => [false]
    | true => [true, false]
  prefixFree := by decide

@[simp] theorem boolCodebook_length_false : boolCodebook.length false = 1 := rfl
@[simp] theorem boolCodebook_length_true : boolCodebook.length true = 2 := rfl

/-- Corollary A.9, in its exact nontrivial form: the finite strict
description-length selector is not codebook-invariant. -/
theorem finite_codeLengthSelector_not_invariant :
    ¬ CodebookInvariant (codeLengthSelector (Candidate := Bool)) :=
  not_codebookInvariant_of_unequal_lengths
    codeLengthSelector codeLengthSelector_strictlyPrefersShorter boolCodebook
    (by decide : boolCodebook.length false < boolCodebook.length true)

/-- Within the original fixed codebook the shorter candidate is strictly
preferred.  The no-go does not deny that this local comparison is defined. -/
theorem boolCodebook_prefers_false :
    codeLengthSelector boolCodebook false true ∧
      ¬ codeLengthSelector boolCodebook true false := by
  norm_num [codeLengthSelector, PrefixCodebook.length, boolCodebook]

/-- Reindexing by the transposition reverses that same pairwise ranking. -/
theorem swappedBoolCodebook_prefers_true :
    let swapped := boolCodebook.reindex (Equiv.swap false true)
    codeLengthSelector swapped true false ∧
      ¬ codeLengthSelector swapped false true := by
  classical
  norm_num [codeLengthSelector, PrefixCodebook.length,
    PrefixCodebook.reindex, boolCodebook]

/-- The same obstruction holds on an actually infinite hypothesis class, not
merely on an infinite-looking finite approximation. -/
theorem countablyInfinite_codeLengthSelector_not_invariant :
    ¬ CodebookInvariant (codeLengthSelector (Candidate := Nat)) :=
  nat_not_codebookInvariant codeLengthSelector
    codeLengthSelector_strictlyPrefersShorter

end Mettapedia.Enactive.OckhamSteelman

#print axioms Mettapedia.Enactive.OckhamSteelman.OntologicalCanary.sufficient_isOptimal
#print axioms Mettapedia.Enactive.OckhamSteelman.OntologicalCanary.criterion_codebookInvariant
#print axioms Mettapedia.Enactive.OckhamSteelman.finite_codeLengthSelector_not_invariant
#print axioms Mettapedia.Enactive.OckhamSteelman.countablyInfinite_codeLengthSelector_not_invariant
