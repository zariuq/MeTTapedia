import Lean
import Mettapedia.OSLF.PiCalculus.RhoEncoding

/-!
# Custom Tactic for rhoPar + rhoSubstitute Commutativity

This tactic automates the proof that `rhoSubstitute (rhoPar P Q) x n = rhoPar (rhoSubstitute P x n) (rhoSubstitute Q x n)`
for non-variable patterns.

## Strategy

After `cases P <;> cases Q`, we have 36 combinations. For each non-var case:
1. Unfold `rhoPar` and `rhoSubstitute`
2. Apply structural preservation lemmas
3. Reduce the pattern match in rhoPar by examining the shapes of P and Q
4. Show both sides are definitionally equal

The key insight: rhoPar's pattern match has 4 branches:
- (collection, collection) → append lists
- (collection, other) → cons to list
- (other, collection) → cons to list
- (other, other) → make new 2-element list

Since we know P and Q's constructors after casing, we can determine which branch applies.
-/

open Lean Meta Elab Tactic

namespace Mettapedia.OSLF.PiCalculus

/-- Tactic to solve rhoPar + rhoSubstitute commutativity goals.

    Usage: `rhoPar_substitute_comm`

    Works on goals of form:
    `rhoSubstitute (rhoPar P Q) x n = rhoPar (rhoSubstitute P x n) (rhoSubstitute Q x n)`
    where P and Q are known non-variable constructors.
-/
elab "rhoPar_substitute_comm" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    -- Step 1: Check if goal matches expected form
    let goalType ← goal.getType
    trace[Meta.Tactic.rhoPar] "Goal type: {goalType}"

    -- Step 2: Unfold definitions and apply structural lemmas
    evalTactic (← `(tactic| simp only [rhoPar, rhoSubstitute_collection_is_collection]))

    -- Step 3: Expand List.map on explicit lists
    evalTactic (← `(tactic| simp only [List.map_cons, List.map_nil, List.map_append]))

    -- Step 4: Apply structural preservation for apply constructor
    evalTactic (← `(tactic| simp only [rhoSubstitute_apply_is_apply]))

    -- Step 5: Try reflexivity (works for simple cases)
    let _ ← tryTactic do evalTactic (← `(tactic| rfl))

/-- Alternative approach: prove each constructor combination separately -/
def proveRhoParCase (p q : String) : TacticM Unit := do
  logInfo m!"Proving case: {p} × {q}"
  -- Unfold and simplify based on specific constructors
  evalTactic (← `(tactic| simp only [rhoPar, rhoSubstitute_collection_is_collection,
                                      List.map_cons, List.map_nil, List.map_append,
                                      rhoSubstitute_apply_is_apply]))
  -- Try reflexivity
  let _ ← tryTactic do evalTactic (← `(tactic| rfl))

end Mettapedia.OSLF.PiCalculus
