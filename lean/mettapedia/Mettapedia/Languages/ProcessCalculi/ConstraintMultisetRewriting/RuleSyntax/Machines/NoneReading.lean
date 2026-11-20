import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Rewriting

/-!
# Outside the fragment, `Rewrites` is not the step

`Machines.Rewrites` reads a rule's takes, reads, tells and equation guards. It does not read none checks,
count checks or collect patterns. So for a rule with a none check it is not the step of that rule:

* `noneRule`: take `sym 0`, ask that no row is `sym 1`, make `sym 2`;
* `rewrites_but_refused`: `Rewrites [noneRule]` rewrites the bag `{sym 0, sym 1}` to `{sym 2, sym 1}`, and at
  the state of that list of rows, which reads as the bag (`listState_reads`), the step admits no firing.

For range-restricted positive programs `Rewrites` is the step read on bags, one rewrite for one firing
(`readsBag_backward`, `readsBag_forward`). The statements that quantify over every list of rules through
`Rewrites` (`Representation.allAtOnce_not_finite`, `Representation.rewrites_equivariant`,
`Representation.oracle_evens_not_finite`, `Representation.successors_finite`,
`Representation.infinitely_branching_not_finite`, `Representation.UnaryEvens.unaryEvens_not_finite`,
`Machines.RootOnly.contextual_not_finite`, `Machines.Separations.evenToZero_not_oneStep`) are statements about
rewriting as `Rewrites` reads it. They are statements about the step for range-restricted positive programs;
for rules with none checks, count checks or collect patterns they say nothing about the step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.NoneReading

open Mettapedia.Logic.LP
open Interface (Frames)
open NamesOnTheStep (Expr)
open Presentation.Schematic

/-- **Take `sym 0`, ask that no row is `sym 1`, make `sym 2`.** -/
def noneRule : SRule :=
  ⟨PUnit.unit, ⟨[toTerm (.sym 0)], [], [], [.predicate .none (toTerm (.sym 1))], [toTerm (.sym 2)]⟩, []⟩

/-- The state of the rows `sym 0, sym 1`. -/
abbrev twoRows : SState ℕ := listState [.sym 0, .sym 1]

/-- **`Rewrites` rewrites the bag, and the step admits no firing at a state that reads as it.** -/
theorem rewrites_but_refused :
    Rewrites [noneRule] (([.sym 0, .sym 1] : List Expr) : Multiset Expr)
        (([.sym 2, .sym 1] : List Expr) : Multiset Expr) ∧
      ReadsBag twoRows (([.sym 0, .sym 1] : List Expr) : Multiset Expr) ∧
      ∀ g : Firing ℕ E {r | r ∈ [noneRule]} twoRows.frame,
        ¬ (schematicStep ℕ [noneRule]).Admits (s := twoRows) g := by
  refine ⟨⟨noneRule, List.mem_singleton_self _, fun _ => .sym 0, {.sym 1}, rfl,
    fun q member => absurd member List.not_mem_nil,
    fun e member => by simp [equationsOf, noneRule, guardOf] at member, rfl⟩, listState_reads _, ?_⟩
  intro g admitted
  obtain ⟨-, -, -, solvable, checks, -⟩ := (admits_iff g).mp admitted
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have isRule : g.rule = noneRule := List.mem_singleton.mp g.member
  have inRule : Check.predicate .none (toTerm (.sym 1)) ∈ g.rule.body.checks := by
    rw [isRule]
    exact List.mem_singleton_self _
  have holds : checkHolds X σ (g.row X twoRows) twoRows.present
      (Check.map g.opening.applyTerm (.predicate .none (toTerm (.sym 1)))) :=
    checks _ (List.mem_map_of_mem inRule) PUnit.unit σ solved
  apply holds 1 (Finset.mem_range.mpr (by norm_num))
  show Subst.applyTerm σ (Subst.applyTerm g.opening (toTerm (.sym 1))) = Subst.applyTerm σ (g.row X twoRows 1)
  rw [row_eq]
  show Subst.applyTerm σ (Subst.applyTerm g.opening (toTerm (.sym 1))) = Subst.applyTerm σ (toTerm (.sym 1))
  rw [applyTerm_toTerm, applyTerm_toTerm]

#print axioms rewrites_but_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.NoneReading
