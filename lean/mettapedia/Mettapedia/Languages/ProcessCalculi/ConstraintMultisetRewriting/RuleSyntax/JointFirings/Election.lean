import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OccurrenceRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Clashes

/-!
# Anonymous choice and a unique-token race

An equivariant deterministic selector must return a fixed point of every
symmetry of the input. Two identical live tokens can be exchanged, so no
selector can choose one of their real firings equivariantly. A take race can
instead offer both outcomes and enforce single consumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Election

open Examples (Tm X E)
open EveryControls (twoTokens tokens tokensAt takeAt firing_shape takeAt_admitted)

private def flip : Equiv.Perm ℕ := Equiv.swap 0 1

theorem both_tokens_offer :
    ((takeAt 0 10).firing.Admits X twoTokens ∧ (takeAt 1 10).firing.Admits X twoTokens) ∧
      Equivalence.renameState flip twoTokens = twoTokens := by
  refine ⟨⟨takeAt_admitted (by decide) (by decide), takeAt_admitted (by decide) (by decide)⟩, ?_⟩
  simp [flip, Equivalence.renameState, tokensAt, twoTokens, Finset.map_insert, Finset.pair_comm]

/-- On this symmetric source there are two legal answers, and equivariance
excludes a deterministic choice of either one. -/
theorem no_equivariant_election (choose : State Tm ℕ → ℕ)
    (equivariant : ∀ (π : Equiv.Perm ℕ) (state : State Tm ℕ),
      choose (Equivalence.renameState π state) = π (choose state)) :
    ¬ ∃ f : Firing ℕ E tokens PUnit.unit, f.Admits X twoTokens ∧
      f.selection.taken = [choose twoTokens] := by
  rintro ⟨f, admitted, chose⟩
  obtain ⟨token, _, present, _, selection⟩ := firing_shape f admitted
  have same : token = choose twoTokens := by
    rw [selection] at chose
    exact List.singleton_inj.mp chose
  have choices : token = 0 ∨ token = 1 := by simpa [twoTokens, tokensAt] using present
  have fixed := equivariant flip twoTokens
  rw [both_tokens_offer.2, ← same] at fixed
  rcases choices with rfl | rfl <;> simp [flip] at fixed

/-- A unique coin allows either request to win. Its exclusive take excludes
a joint firing that awards the same coin twice. -/
theorem unique_coin_race :
    (Shop.buyFor 1 10).firing.Admits X Shop.market ∧
    (Shop.buyFor 2 11).firing.Admits X Shop.market ∧
    ¬ Shop.both.Admits X Shop.market :=
  ⟨Shop.first_admitted, Shop.second_admitted, Shop.both_refused⟩

/-- With one offered token the admissible selection is fixed by every
renaming preserving the entry store. -/
theorem single_token_forces_choice (token fresh : ℕ) (different : fresh ≠ token) :
    ((takeAt token fresh).firing.Admits X (tokensAt {token})) ∧
      ∀ f : Firing ℕ E tokens PUnit.unit, f.Admits X (tokensAt {token}) →
        f.selection.taken = [token] := by
  constructor
  · exact takeAt_admitted (Finset.mem_singleton_self _) (by simpa using different)
  · intro f admitted
    obtain ⟨only, _, present, _, picked⟩ := firing_shape f admitted
    have equals : only = token := Finset.mem_singleton.mp present
    rw [picked, equals]

#print axioms both_tokens_offer
#print axioms no_equivariant_election
#print axioms unique_coin_race
#print axioms single_token_forces_choice

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Election
