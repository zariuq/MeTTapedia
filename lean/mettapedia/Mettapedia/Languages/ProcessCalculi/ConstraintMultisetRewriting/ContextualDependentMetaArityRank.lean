import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRankRound

/-!
# The metavariable-arity rank, and why the rounds keep the weight rank

The classical termination measure for pattern unification with pruning is lexicographic in three
components: the number of declarations, the **total metavariable arity** (the leading Π binders of every
declaration, `totalArity`), and the size of the constraints. Solving removes a declaration; pruning and
intersection replace a metavariable by one of smaller arity and keep the declarations; decompositions keep
both and lower the size. The triple is well founded (`arityTriple_wf`).

A round of the worklist driver carries its decrease in its type, at a rank in `ℕ × ℕ` ordered
lexicographically (`ContextualDependentWorklist.Round`, `ContextualDependentDecisiveDriver.Family`). The
triple order does not fit there: **no map from triples to pairs is strictly monotone** for the lexicographic
orders (`no_pair_rank_of_triple`). Between two consecutive arities at fixed declarations the triple order has
infinitely many weights, and between two consecutive declaration counts infinitely many arities; a pair
order has room for only one of these two infinities.

So the rounds keep R97's `weightRank` (declarations, then normal weight), unchanged, and each new rule is
chosen so that its progress lowers that rank:

* **a composite that removes a declaration** lowers the first component, whatever happens to the weight
  (`below_of_arity`): prune and solve, reorder and solve, recognition up to cumulativity followed by solving;
* **intersection** keeps the declarations, and lowers the normal weight where the pruned metavariable occurs
  in no other equation and no later declaration.

What remains of the classical argument is the decrease of the normal weight under a pruning instantiation at
every occurrence of the pruned metavariable; this file does not assume it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMetaArityRank

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedContextual
open ContextualDependentWorklist ContextualDependentDynamicFragment

/-! ## The triple order -/

/-- The lexicographic order on triples of natural numbers. -/
def Lex3 (first second : Nat × Nat × Nat) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) first second

/-- **The triple order is well founded.** -/
theorem lex3_wf : WellFounded Lex3 :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

/-! ## No pair rank carries the triple order -/

/-- The first component never decreases along a sequence increasing for the pair order. -/
theorem first_mono {s : Nat → Nat × Nat} (increasing : ∀ k, Below (s k) (s (k + 1))) :
    ∀ k, (s 0).1 ≤ (s k).1
  | 0 => le_rfl
  | k + 1 => by
      have step := Prod.lex_def.mp (increasing k)
      have before := first_mono increasing k
      rcases step with lower | ⟨same, _⟩
      · omega
      · omega

/-- **A bounded increasing sequence of pairs climbs in the first component**: its first entry has a first
component below the bound's. -/
theorem first_lt_of_bounded {s : Nat → Nat × Nat} {bound : Nat × Nat}
    (increasing : ∀ k, Below (s k) (s (k + 1))) (bounded : ∀ k, Below (s k) bound) : (s 0).1 < bound.1 := by
  have below : ∀ k, (s k).1 ≤ bound.1 := fun k => by
    rcases Prod.lex_def.mp (bounded k) with lower | ⟨same, _⟩
    · omega
    · omega
  by_contra climbing
  have equal : ∀ k, (s k).1 = bound.1 := fun k => by
    have := first_mono increasing k
    have := below k
    omega
  have second : ∀ k, k ≤ (s k).2 := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        have e₁ := equal k
        have e₂ := equal (k + 1)
        rcases Prod.lex_def.mp (increasing k) with lower | ⟨_, larger⟩
        · omega
        · omega
  have last := bounded bound.2
  have e := equal bound.2
  have := second bound.2
  rcases Prod.lex_def.mp last with lower | ⟨_, smaller⟩
  · omega
  · omega

/-- **No pair rank is strictly monotone for the triple order.** A map `φ` from triples to pairs that lowers
the pair rank at every lexicographic decrease of triples does not exist. -/
theorem no_pair_rank_of_triple :
    ¬ ∃ φ : Nat × Nat × Nat → Nat × Nat, ∀ first second, Lex3 first second → Below (φ first) (φ second) := by
  rintro ⟨φ, monotone⟩
  have climbs : ∀ j, (φ (0, j, 0)).1 < (φ (0, j + 1, 0)).1 := fun j =>
    first_lt_of_bounded (s := fun k => φ (0, j, k))
      (fun k => monotone _ _ (Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self k))))
      (fun k => monotone _ _ (Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.lt_succ_self j))))
  have grows : ∀ j, j ≤ (φ (0, j, 0)).1 := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
        have := climbs j
        omega
  have capped : ∀ j, (φ (0, j, 0)).1 ≤ (φ (1, 0, 0)).1 := fun j => by
    rcases Prod.lex_def.mp (monotone (0, j, 0) (1, 0, 0) (Prod.Lex.left _ _ Nat.zero_lt_one)) with lower | ⟨same, _⟩
    · omega
    · omega
  have := grows ((φ (1, 0, 0)).1 + 1)
  have := capped ((φ (1, 0, 0)).1 + 1)
  omega

/-! ## The arity of a context -/

variable {Head : Type}

/-- **The total metavariable arity** of a context: the leading Π binders of every declaration. -/
def totalArity : {n : Nat} → Ctx Head n → Nat
  | _, .nil => 0
  | _, .snoc context declaration => totalArity context + piCount declaration

@[simp] theorem totalArity_nil : totalArity (.nil : Ctx Head 0) = 0 := rfl

@[simp] theorem totalArity_snoc {n : Nat} (context : Ctx Head n) (declaration : Tm Head n) :
    totalArity (.snoc context declaration) = totalArity context + piCount declaration := rfl

section Triple

variable {rules : Rules Head}

/-- **The classical triple** of a store: declarations, total metavariable arity, and a size of the store. -/
def arityTriple {Θ : Context rules} (size : EquationStore (TotalTerm Θ) → Nat)
    (problem : EquationStore (TotalTerm Θ)) : Nat × Nat × Nat :=
  (Θ.arity, totalArity Θ.raw, size problem)

/-- **The classical triple is well founded**, at any size. -/
theorem arityTriple_wf : WellFounded Lex3 := lex3_wf

/-- A step that keeps the declarations and lowers the total arity lowers the triple, whatever the size. -/
theorem arityTriple_of_arity {Θ Θ' : Context rules} (size : EquationStore (TotalTerm Θ) → Nat)
    (size' : EquationStore (TotalTerm Θ') → Nat) (problem : EquationStore (TotalTerm Θ))
    (problem' : EquationStore (TotalTerm Θ')) (same : Θ'.arity = Θ.arity)
    (lower : totalArity Θ'.raw < totalArity Θ.raw) :
    Lex3 (arityTriple size' problem') (arityTriple size problem) := by
  unfold arityTriple Lex3
  exact Prod.lex_def.mpr (.inr ⟨same, Prod.Lex.left _ _ lower⟩)

end Triple

end ContextualDependentMetaArityRank
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
