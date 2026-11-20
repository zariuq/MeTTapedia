import Mettapedia.Logic.LP.TotalUnification
import Mettapedia.Tools.KernelReflexivity

/-!
# Total unification by structural recursion

`unifyTotal` is defined by well-founded recursion on the lexicographic
Martelli--Montanari measure, so the kernel cannot evaluate it on closed
equations. `unifyTotalStructural` runs the same rules by structural recursion
on two fuel bounds: eliminations consume one round (each removes a variable),
and every other rule consumes one unit of the size bound, which restarts after
each elimination. The bounds never run out, so the two functions are equal.
-/

namespace Mettapedia.Logic.LP

/-- The rule loop of `unifyTotal`. Eliminations continue with `eliminate`;
deletion and decomposition consume `fuel`. -/
def unifyStructuralSteps {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (eliminate : List (Term σ × Term σ) → Option (Subst σ)) :
    Nat → List (Term σ × Term σ) → Option (Subst σ)
  | _, [] => some (Subst.id σ)
  | 0, _ :: _ => none
  | fuel + 1, (source, target) :: rest =>
      match source with
      | .var v =>
          match target with
          | .var other =>
              if v = other then
                unifyStructuralSteps eliminate fuel rest
              else
                match eliminate
                    ((Subst.single v (.var other)).applyEqs rest) with
                | none => none
                | some substitution =>
                    some (substitution ∘ₛ Subst.single v (.var other))
          | term =>
              if term.occursIn v then none
              else
                match eliminate ((Subst.single v term).applyEqs rest) with
                | none => none
                | some substitution =>
                    some (substitution ∘ₛ Subst.single v term)
      | .const constant =>
          match target with
          | .var v =>
              match eliminate
                  ((Subst.single v (.const constant)).applyEqs rest) with
              | none => none
              | some substitution =>
                  some (substitution ∘ₛ Subst.single v (.const constant))
          | .const other =>
              if constant = other then unifyStructuralSteps eliminate fuel rest else none
          | .app _ _ => none
      | .app function arguments =>
          match target with
          | .var v =>
              if (Term.app function arguments).occursIn v then none
              else
                match eliminate
                    ((Subst.single v (.app function arguments)).applyEqs rest) with
                | none => none
                | some substitution =>
                    some (substitution ∘ₛ
                      Subst.single v (.app function arguments))
          | .const _ => none
          | .app other otherArguments =>
              if equal : function = other then
                unifyStructuralSteps eliminate fuel (finPairsToList arguments
                  (equal ▸ otherArguments) ++ rest)
              else none

/-- Each round runs the rule loop with a fresh size bound; an elimination
continues in the next round. -/
def unifyStructuralRounds {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    Nat → List (Term σ × Term σ) → Option (Subst σ)
  | 0, _ => none
  | rounds + 1, equations =>
      unifyStructuralSteps (unifyStructuralRounds rounds) (mmSize equations + 1) equations

/-- `unifyTotal` by structural recursion: the size of the equations bounds both
the number of eliminations and the rules between two eliminations. -/
def unifyTotalStructural {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) : Option (Subst σ) :=
  unifyStructuralRounds (mmSize equations + 1) equations

section Agreement

variable {σ : LPSignature} [DecidableEq σ.vars]

private theorem freeVars_card_le_size (term : Term σ) : term.freeVars.card ≤ term.size := by
  induction term with
  | var v => simp [Term.freeVars, Term.size]
  | const c => simp [Term.freeVars, Term.size]
  | app f ts ih =>
      simp only [Term.freeVars, Term.size]
      calc (Finset.univ.biUnion fun i => (ts i).freeVars).card
          ≤ ∑ i, ((ts i).freeVars).card := Finset.card_biUnion_le
        _ ≤ ∑ i, (ts i).size := Finset.sum_le_sum fun i _ => ih i
        _ ≤ 1 + ∑ i, (ts i).size := Nat.le_add_left _ _

/-- The number of distinct variables never exceeds the size of the equations. -/
theorem mmVarCount_le_mmSize (equations : List (Term σ × Term σ)) :
    mmVarCount equations ≤ mmSize equations := by
  induction equations with
  | nil => simp [mmVarCount, eqVars, mmSize]
  | cons pair rest ih =>
      obtain ⟨left, right⟩ := pair
      simp only [mmVarCount, eqVars, mmSize] at ih ⊢
      calc (left.freeVars ∪ right.freeVars ∪ eqVars rest).card
          ≤ (left.freeVars ∪ right.freeVars).card + (eqVars rest).card := Finset.card_union_le _ _
        _ ≤ left.freeVars.card + right.freeVars.card + (eqVars rest).card := by
            gcongr; exact Finset.card_union_le _ _
        _ ≤ left.size + right.size + mmSize rest := by
            have := freeVars_card_le_size left
            have := freeVars_card_le_size right
            omega

private theorem eliminate_bound {rounds : Nat} (v : σ.vars) (term : Term σ)
    (rest : List (Term σ × Term σ)) (notOccurs : term.occursIn v = false)
    (vars : mmVarCount ((.var v, term) :: rest) < rounds + 1) :
    mmVarCount ((Subst.single v term).applyEqs rest) < rounds := by
  have := mmVarCount_eliminate_lt v term rest notOccurs
  omega

private theorem eliminate_swapped_bound {rounds : Nat} (v : σ.vars) (term : Term σ)
    (rest : List (Term σ × Term σ)) (notOccurs : term.occursIn v = false)
    (vars : mmVarCount ((term, .var v) :: rest) < rounds + 1) :
    mmVarCount ((Subst.single v term).applyEqs rest) < rounds := by
  have swap : mmVarCount ((term, .var v) :: rest) = mmVarCount ((.var v, term) :: rest) := by
    simp [mmVarCount, eqVars, Finset.union_comm]
  exact eliminate_bound v term rest notOccurs (swap ▸ vars)

variable [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

private theorem steps_eq (rounds : Nat)
    (outer : ∀ equations : List (Term σ × Term σ), mmVarCount equations < rounds →
      unifyStructuralRounds rounds equations = unifyTotal equations)
    (equations : List (Term σ × Term σ)) :
    ∀ fuel, mmVarCount equations < rounds + 1 → mmSize equations < fuel →
      unifyStructuralSteps (unifyStructuralRounds rounds) fuel equations = unifyTotal equations := by
  fun_induction unifyTotal equations
  · intro fuel _ _
    cases fuel <;> simp [unifyStructuralSteps]
  all_goals
    intro fuel vars size
    cases fuel with
    | zero => exact absurd size (Nat.not_lt_zero _)
    | succ fuel => ?_
  · rename_i rest v ih
    simp only [unifyStructuralSteps]
    rw [if_pos trivial]
    exact ih fuel (lt_of_le_of_lt (mmVarCount_cons_ge _ _ _) vars)
      (by have := mmSize_var_eq_lt v rest; omega)
  · rename_i rest v other different child _
    simp only [unifyStructuralSteps]
    rw [if_neg different, outer _ (eliminate_bound v _ rest (by simp [Term.occursIn, different]) vars),
      child]
  · rename_i rest v other different substitution child _
    simp only [unifyStructuralSteps]
    rw [if_neg different, outer _ (eliminate_bound v _ rest (by simp [Term.occursIn, different]) vars),
      child]
  · rename_i rest v term notVariable occurs
    cases term with
    | var other => exact absurd rfl (notVariable other)
    | const constant => simp [Term.occursIn] at occurs
    | app function arguments =>
        simp only [unifyStructuralSteps]
        rw [if_pos occurs]
  · rename_i rest v term notVariable notOccurs child _
    have occursFalse : term.occursIn v = false := by simpa using notOccurs
    have bound := eliminate_bound v term rest occursFalse vars
    cases term with
    | var other => exact absurd rfl (notVariable other)
    | const constant =>
        simp only [unifyStructuralSteps]
        rw [if_neg notOccurs, outer _ bound, child]
    | app function arguments =>
        simp only [unifyStructuralSteps]
        rw [if_neg notOccurs, outer _ bound, child]
  · rename_i rest v term notVariable notOccurs substitution child _
    have occursFalse : term.occursIn v = false := by simpa using notOccurs
    have bound := eliminate_bound v term rest occursFalse vars
    cases term with
    | var other => exact absurd rfl (notVariable other)
    | const constant =>
        simp only [unifyStructuralSteps]
        rw [if_neg notOccurs, outer _ bound, child]
    | app function arguments =>
        simp only [unifyStructuralSteps]
        rw [if_neg notOccurs, outer _ bound, child]
  · rename_i rest constant v child _
    simp only [unifyStructuralSteps]
    rw [outer _ (eliminate_swapped_bound v _ rest (by simp [Term.occursIn]) vars), child]
  · rename_i rest constant v substitution child _
    simp only [unifyStructuralSteps]
    rw [outer _ (eliminate_swapped_bound v _ rest (by simp [Term.occursIn]) vars), child]
  · rename_i rest constant ih
    simp only [unifyStructuralSteps]
    rw [if_pos trivial]
    exact ih fuel (lt_of_le_of_lt (mmVarCount_cons_ge _ _ _) vars)
      (by have := mmSize_const_eq_lt constant rest; omega)
  · rename_i rest constant other different
    simp only [unifyStructuralSteps]
    rw [if_neg different]
  · simp only [unifyStructuralSteps]
  · rename_i rest function arguments v occurs
    simp only [unifyStructuralSteps]
    rw [if_pos occurs]
  · rename_i rest function arguments v notOccurs child _
    have occursFalse : (Term.app function arguments).occursIn v = false := by simpa using notOccurs
    simp only [unifyStructuralSteps]
    rw [if_neg notOccurs, outer _ (eliminate_swapped_bound v _ rest occursFalse vars), child]
  · rename_i rest function arguments v notOccurs substitution child _
    have occursFalse : (Term.app function arguments).occursIn v = false := by simpa using notOccurs
    simp only [unifyStructuralSteps]
    rw [if_neg notOccurs, outer _ (eliminate_swapped_bound v _ rest occursFalse vars), child]
  · simp only [unifyStructuralSteps]
  · rename_i rest function otherArguments arguments ih
    simp only [unifyStructuralSteps]
    rw [dif_pos trivial]
    exact ih fuel
      (lt_of_le_of_lt (mmVarCount_app_eq_decompose_le function arguments otherArguments rest) vars)
      (lt_of_lt_of_le (mmSize_app_eq_decompose_lt function arguments otherArguments rest)
        (Nat.lt_succ_iff.mp size))
  · rename_i rest function arguments other otherArguments different
    simp only [unifyStructuralSteps]
    rw [dif_neg different]

private theorem rounds_eq : ∀ (rounds : Nat) (equations : List (Term σ × Term σ)),
    mmVarCount equations < rounds → unifyStructuralRounds rounds equations = unifyTotal equations
  | 0, _, bound => absurd bound (Nat.not_lt_zero _)
  | rounds + 1, equations, bound => by
      rw [unifyStructuralRounds]
      exact steps_eq rounds (rounds_eq rounds) equations _ bound (Nat.lt_succ_self _)

theorem unifyTotalStructural_eq_unifyTotal (equations : List (Term σ × Term σ)) :
    unifyTotalStructural equations = unifyTotal equations :=
  rounds_eq _ _ (Nat.lt_succ_of_le (mmVarCount_le_mmSize equations))

end Agreement

/-- The structural implementation is the total unifier itself. -/
theorem unifyTotalStructural_eq : @unifyTotalStructural = @unifyTotal := by
  funext σ variableEq constantEq functionEq equations
  exact unifyTotalStructural_eq_unifyTotal equations

/-! ## Kernel evaluation on a closed problem -/

/-- Variables, constants and function symbols are numbers; a function symbol is
its own arity. -/
private abbrev exampleSignature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity := id

/-- `f(x0, 7) = f(3, x1)` for the binary symbol `f = 2` binds `x0` to `3` and `x1` to `7`. -/
private def exampleEquations : List (Term exampleSignature × Term exampleSignature) :=
  [(Term.app (σ := exampleSignature) 2 ![Term.var 0, Term.const 7],
    Term.app (σ := exampleSignature) 2 ![Term.const 3, Term.var 1])]

example : (unifyTotalStructural exampleEquations).map (fun θ => (θ 0, θ 1)) =
    some (.const 3, .const 7) := by
  kernel_reflexivity

/-- The well-founded definition does not reduce in the kernel. -/
example : True := by
  fail_if_success
    have : (unifyTotal exampleEquations).map (fun θ => (θ 0, θ 1)) =
        some (.const 3, .const 7) := by kernel_reflexivity
  trivial

/-- A clash is a genuine failure, also in the kernel. -/
example : unifyTotalStructural
    [((.const (3 : Nat) : Term exampleSignature), .const (4 : Nat))] = none := by
  kernel_reflexivity

end Mettapedia.Logic.LP
