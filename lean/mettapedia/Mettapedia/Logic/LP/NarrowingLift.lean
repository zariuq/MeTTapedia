import Mettapedia.Logic.LP.Narrowing
import Mettapedia.Logic.LP.UnificationComplete

/-!
# Lifting a rewrite of an instance back to a narrowing

A rewrite of an instantiated query, taken at a subterm that is already present
in the query and is not a variable, is the instance of a narrowing of the query.
The narrowing substitution is a most general unifier returned by the kernel.
The rule is given already renamed apart from the query, for the same reason as
in the narrowing step: the variable type need not contain a fresh name.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.NarrowingLift

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FirstOrderRewriting
open Mettapedia.Logic.LP.Narrowing

variable {σ : LPSignature} [DecidableEq σ.vars]

/-- The substitution that follows `onDomain` on `domain` and `offDomain` outside it. -/
def splice (domain : Finset σ.vars) (onDomain offDomain : Subst σ) : Subst σ :=
  fun name => if name ∈ domain then onDomain name else offDomain name

/-- On a term whose variables lie in `domain`, splicing agrees with `onDomain`. -/
theorem apply_onDomain {term : Term σ} {domain : Finset σ.vars}
    {onDomain offDomain : Subst σ} (covered : term.freeVars ⊆ domain) :
    (splice domain onDomain offDomain).applyTerm term = onDomain.applyTerm term := by
  apply Subst.applyTerm_congr
  intro name member
  have present : name ∈ domain := covered member
  simp [splice, present]

/-- On a term whose variables avoid `domain`, splicing agrees with `offDomain`. -/
theorem apply_offDomain {term : Term σ} {domain : Finset σ.vars}
    {onDomain offDomain : Subst σ} (avoided : ∀ name ∈ term.freeVars, name ∉ domain) :
    (splice domain onDomain offDomain).applyTerm term = offDomain.applyTerm term := by
  apply Subst.applyTerm_congr
  intro name member
  have absent : name ∉ domain := avoided name member
  simp [splice, absent]

/-- Splicing pushes into a context: the hole follows `onDomain`, and the context follows `offDomain`. -/
theorem splice_fill (context : Context σ) (hole : Term σ) (domain : Finset σ.vars)
    (onDomain offDomain : Subst σ)
    (covered : hole.freeVars ⊆ domain)
    (avoided : ∀ name ∈ outsideVars context, name ∉ domain) :
    (splice domain onDomain offDomain).applyTerm (context.fill hole) =
      (mapContext offDomain context).fill (onDomain.applyTerm hole) := by
  induction context with
  | hole =>
      simpa [Context.fill, mapContext] using apply_onDomain covered
  | app _ arguments position inner ih =>
      simp only [Context.fill, Subst.applyTerm_app, mapContext]
      congr 1
      funext index
      by_cases same : index = position
      · subst same
        simp only [Function.update_self]
        apply ih
        intro name member
        apply avoided
        simp only [outsideVars, Finset.mem_union]
        exact Or.inr member
      · simp only [Function.update_of_ne same]
        apply apply_offDomain
        intro name member
        apply avoided
        simp only [outsideVars, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact Or.inl ⟨index, same, member⟩

/-- A rewrite of an instance, at a non-variable subterm of the query, is an instance of a narrowing. -/
theorem lift_step {rules : Set (Equation σ)}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {equation : Equation σ} (member : equation ∈ rules)
    {context : Context σ} {subterm : Term σ}
    {querySubst ruleSubst : Subst σ}
    (notVariable : ∀ name, subterm ≠ Term.var name)
    (separated : apart equation (context.fill subterm))
    (matched : querySubst.applyTerm subterm = ruleSubst.applyTerm equation.left) :
    let source := context.fill subterm
    let domain := equation.left.freeVars ∪ equation.right.freeVars
    let combined := splice domain ruleSubst querySubst
    ∃ narrowingSubst : Subst σ, ∃ later : Subst σ,
      Narrow rules source narrowingSubst
        (narrowingSubst.applyTerm (context.fill equation.right)) ∧
      MostGeneralUnifier narrowingSubst equation.left subterm ∧
      (∀ name, combined name = later.applyTerm (narrowingSubst name)) ∧
      later.applyTerm (narrowingSubst.applyTerm source) = querySubst.applyTerm source ∧
      later.applyTerm (narrowingSubst.applyTerm (context.fill equation.right)) =
        (mapContext querySubst context).fill (ruleSubst.applyTerm equation.right) ∧
      Rewrite rules (querySubst.applyTerm source)
        ((mapContext querySubst context).fill (ruleSubst.applyTerm equation.right)) := by
  let source := context.fill subterm
  let domain := equation.left.freeVars ∪ equation.right.freeVars
  let combined := splice domain ruleSubst querySubst
  have subtermVars : subterm.freeVars ⊆ source.freeVars := freeVars_hole_subset context subterm
  have avoidedSubterm : ∀ name ∈ subterm.freeVars, name ∉ domain := by
    intro name memberVar memDomain
    exact separated name memDomain (subtermVars memberVar)
  have unified : combined.applyTerm equation.left = combined.applyTerm subterm := by
    rw [apply_onDomain (term := equation.left) (domain := domain)
        (covered := fun name memberVar => Finset.mem_union_left _ memberVar),
      apply_offDomain (term := subterm) avoidedSubterm]
    exact matched.symm
  obtain ⟨fuel, narrowingSubst, found⟩ :=
    unifyFuel_exists_of_unifies
      (hunif := ⟨combined, by
        intro pair membership
        have pairEq : pair = (equation.left, subterm) := List.mem_singleton.mp membership
        subst pairEq
        exact unified⟩)
  have foundTerms : unifyTerms equation.left subterm fuel = some narrowingSubst := found
  obtain ⟨narrowed, mostGeneral⟩ :=
    narrow_of_unifyTerms member notVariable rfl separated foundTerms
  obtain ⟨later, laterEq⟩ := mostGeneral.2 combined unified
  have combinedEq : combined = later ∘ₛ narrowingSubst := by
    funext name
    exact laterEq name
  have sourceCombined : combined.applyTerm source = querySubst.applyTerm source := by
    apply apply_offDomain
    intro name memberVar memDomain
    exact separated name memDomain memberVar
  have targetCombined :
      combined.applyTerm (context.fill equation.right) =
        (mapContext querySubst context).fill (ruleSubst.applyTerm equation.right) := by
    apply splice_fill
    · intro name memberVar
      exact Finset.mem_union_right _ memberVar
    · intro name memberVar memDomain
      exact separated name memDomain (outsideVars_subset_fill context subterm memberVar)
  have sourceInst :
      later.applyTerm (narrowingSubst.applyTerm source) = querySubst.applyTerm source := by
    rw [← Subst.applyTerm_comp, ← combinedEq, sourceCombined]
  have targetInst :
      later.applyTerm (narrowingSubst.applyTerm (context.fill equation.right)) =
        (mapContext querySubst context).fill (ruleSubst.applyTerm equation.right) := by
    rw [← Subst.applyTerm_comp, ← combinedEq, targetCombined]
  refine ⟨narrowingSubst, later, narrowed, mostGeneral, laterEq, sourceInst, targetInst, ?_⟩
  have rewritten := rewrite_subst (narrow_sound narrowed) later
  rw [sourceInst, targetInst] at rewritten
  exact rewritten

end Mettapedia.Logic.LP.NarrowingLift
