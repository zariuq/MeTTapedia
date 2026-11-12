import Mettapedia.TypeTheory.ConversionStoreCore

/-!
# The cost of conversion evidence: a lower bound, and what a store changes

When conversion is witnessed by a run, a checker that follows the run does no computation of its
own, and the run is as long as the computation it stands for. This module measures that on the
dependent comparison core with the recursion equations of addition.

`zeros k t` is `t + 0 + … + 0` with `k` zeros. The two types `Vec (zeros k t)` and `Vec t` are
convertible in the bubble.

* **Evidence exists with `k` firings** (`evidence_exists`).
* **No evidence is shorter** (`evidence_lower_bound`): every run of the conversion step from
  `Vec (zeros k t)` that ends at `Vec t` has at least `k` firings, from any ledger. The invariant
  is the number of occurrences of addition, which one rewrite step changes by at most one, in
  either direction (`rewrite_addCount`, `zigzag_addCount`).
* **With a store that has learnt the equation, one move** (`one_lookup`): the lookup from
  `Vec (zeros k t)` to `Vec t` is admitted at the store whose ledger holds `zeros k t ≐ t`.

So the first establishment of a conversion costs its computation, written out; every later use,
under any context, costs one move. A checker that decides conversion by normalization keeps no
evidence for it; how often it repeats the reduction depends on its own caches, which are outside
this comparison.

Scope: this bubble and this family of types; the lower bound is for the conversion step of
`ConversionRuns` (rewrite steps only), and the single move is for the store of
`ConversionStoreCore`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ConversionCost

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.ConversionRuns
open Mettapedia.TypeTheory.ConversionRuns.Controls
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.ConversionStoreCore
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr
open Mettapedia.TypeTheory.BubbleConversion.Arith

universe uIndex uState uBubble uStep

/-! ## Lengths of runs and zigzags -/

section Lengths

variable {Index : Type uIndex} {B : Bubbles.{uIndex, uState, uBubble, uStep} Index}
  {bubble : B.Bubble} {index : Index}

/-- The zigzag of a run has one step for each firing. -/
theorem length_zigzagOfRun : ∀ {goal : Goal B index}
    (run : (conversionStep B bubble index).Run goal),
    (zigzagOfRun run).length = run.word.length
  | _, .nil _ => rfl
  | _, .cons (.forward _ _) _ rest => congrArg (· + 1) (length_zigzagOfRun rest)
  | _, .cons (.backward _ _) _ rest => congrArg (· + 1) (length_zigzagOfRun rest)
  | _, .cons (.asserted target) admitted _ =>
      False.elim ((admits_iff B bubble index (Claim.asserted target)).mp admitted)

/-- The run of a zigzag has one firing for each step. -/
theorem length_runOfZigzag : ∀ {source target : B.State index}
    (path : Zigzag B bubble source target) (ledger : EquationStore (B.State index)) (clock : Nat),
    (runOfZigzag path ledger clock).word.length = path.length
  | _, _, .nil _, _, _ => rfl
  | _, _, .forward _ rest, _, _ => congrArg (· + 1) (length_runOfZigzag rest _ _)
  | _, _, .backward _ rest, _, _ => congrArg (· + 1) (length_runOfZigzag rest _ _)

end Lengths

/-! ## The invariant: occurrences of addition -/

/-- The number of occurrences of the addition constant. -/
def addCount : AExpr → Nat
  | .bvar _ => 0
  | .univ => 0
  | .prop => 0
  | .base _ => 0
  | .pi A B => addCount A + addCount B
  | .lam A b => addCount A + addCount b
  | .app f a => addCount f + addCount a
  | .const _ .add => 1
  | .const _ .zero => 0
  | .const _ .succ => 0
  | .tyFam _ => 0
  | .top => 0
  | .bot => 0
  | .and p q => addCount p + addCount q
  | .or p q => addCount p + addCount q
  | .imp p q => addCount p + addCount q
  | .not p => addCount p
  | .eq a b => addCount a + addCount b
  | .all A b => addCount A + addCount b
  | .ex A b => addCount A + addCount b

theorem bump_left {a a' b : Nat} (changed : a = a' ∨ a = a' + 1) :
    a + b = a' + b ∨ a + b = a' + b + 1 := by omega

theorem bump_right {a b b' : Nat} (changed : b = b' ∨ b = b' + 1) :
    a + b = a + b' ∨ a + b = a + b' + 1 := by omega

/-- A recursion equation keeps the number of additions or removes one. -/
theorem rule_addCount {left right : AExpr} (rule : Rule left right) :
    addCount left = addCount right ∨ addCount left = addCount right + 1 := by
  cases rule with
  | addZero _ =>
      exact Or.inr (by
        show 1 + addCount _ + 0 = addCount _ + 1
        omega)
  | addSucc t u =>
      exact Or.inl (by
        show 1 + addCount t + (0 + addCount u) = 0 + (1 + addCount t + addCount u)
        omega)

/-- **One rewrite step changes the number of additions by at most one.** -/
theorem rewrite_addCount {e e' : AExpr} (step : Rewrite Rule e e') :
    addCount e = addCount e' ∨ addCount e = addCount e' + 1 := by
  induction step with
  | root rule => exact rule_addCount rule
  | piDomain _ ih => exact bump_left ih
  | piBody _ ih => exact bump_right ih
  | lamDomain _ ih => exact bump_left ih
  | lamBody _ ih => exact bump_right ih
  | appFunction _ ih => exact bump_left ih
  | appArgument _ ih => exact bump_right ih
  | andLeft _ ih => exact bump_left ih
  | andRight _ ih => exact bump_right ih
  | orLeft _ ih => exact bump_left ih
  | orRight _ ih => exact bump_right ih
  | impLeft _ ih => exact bump_left ih
  | impRight _ ih => exact bump_right ih
  | notBody _ ih => exact ih
  | eqLeft _ ih => exact bump_left ih
  | eqRight _ ih => exact bump_right ih
  | allDomain _ ih => exact bump_left ih
  | allBody _ ih => exact bump_right ih
  | exDomain _ ih => exact bump_left ih
  | exBody _ ih => exact bump_right ih

/-- Along a zigzag the number of additions moves by at most the length, in both directions. -/
theorem zigzag_addCount : ∀ {a b : AExpr} (path : Zigzag arithBubbles Rule (index := ()) a b),
    addCount a ≤ addCount b + path.length ∧ addCount b ≤ addCount a + path.length
  | _, _, .nil _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | _, _, .forward step rest => by
      have here := rewrite_addCount (PLift.down step)
      have later := zigzag_addCount rest
      show _ ≤ _ + (rest.length + 1) ∧ _ ≤ _ + (rest.length + 1)
      omega
  | _, _, .backward step rest => by
      have here := rewrite_addCount (PLift.down step)
      have later := zigzag_addCount rest
      show _ ≤ _ + (rest.length + 1) ∧ _ ≤ _ + (rest.length + 1)
      omega

/-! ## The family `t + 0 + … + 0` -/

/-- `t` followed by `k` additions of zero. -/
def zeros : Nat → AExpr → AExpr
  | 0, t => t
  | k + 1, t => addE (zeros k t) zeroE

theorem addCount_zeros (k : Nat) (t : AExpr) : addCount (zeros k t) = addCount t + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show 1 + addCount (zeros k t) + 0 = addCount t + (k + 1)
      omega

theorem addCount_vec (t : AExpr) : addCount (vec t) = addCount t := Nat.zero_add _

/-- The zigzag that removes the zeros under `Vec`, one step each. -/
def vecZerosZigzag : (k : Nat) → (t : AExpr) →
    Zigzag arithBubbles Rule (index := ()) (vec (zeros k t)) (vec t)
  | 0, t => Zigzag.nil (B := arithBubbles) (bubble := Rule) (index := ()) (vec t)
  | k + 1, t =>
      Zigzag.forward (B := arithBubbles) (bubble := Rule) (index := ())
        (source := vec (zeros (k + 1) t)) (middle := vec (zeros k t)) (target := vec t)
        (PLift.up (Rewrite.appArgument (Rewrite.root (Rule.addZero (zeros k t)))))
        (vecZerosZigzag k t)

theorem vecZerosZigzag_length : ∀ (k : Nat) (t : AExpr), (vecZerosZigzag k t).length = k
  | 0, _ => rfl
  | k + 1, t => congrArg (· + 1) (vecZerosZigzag_length k t)

/-- **Evidence exists with `k` firings.** -/
theorem evidence_exists (k : Nat) (t : AExpr) :
    ∃ run : (conversionStep arithBubbles Rule ()).Run ⟨vec (zeros k t), [], 0⟩,
      run.last.cursor = vec t ∧ run.word.length = k :=
  ⟨runOfZigzag (vecZerosZigzag k t) [] 0, last_runOfZigzag _ _ _,
    (length_runOfZigzag (vecZerosZigzag k t) [] 0).trans (vecZerosZigzag_length k t)⟩

/-- **No evidence is shorter.** Every run of the conversion step from `Vec (zeros k t)` that ends
at `Vec t` has at least `k` firings. -/
theorem evidence_lower_bound (k : Nat) (t : AExpr) (ledger : EquationStore AExpr) (clock : Nat)
    (run : (conversionStep arithBubbles Rule ()).Run ⟨vec (zeros k t), ledger, clock⟩)
    (ends : run.last.cursor = vec t) : k ≤ run.word.length := by
  have bound := (zigzag_addCount (zigzagOfRun run)).1
  have target : addCount run.last.cursor = addCount (vec t) := congrArg addCount ends
  have source : addCount (vec (zeros k t)) = addCount t + k :=
    (addCount_vec (zeros k t)).trans (addCount_zeros k t)
  have atTarget := addCount_vec t
  have firings := length_zigzagOfRun run
  have bound' : addCount (vec (zeros k t)) ≤ addCount run.last.cursor + (zigzagOfRun run).length :=
    bound
  omega

/-- **With a store that has learnt the equation, one move.** -/
theorem one_lookup (k : Nat) (t : AExpr) (clock : Nat) :
    (storeStep Rule).Admits
      (Move.lookup (vec t) : Move Rule (Store.mk (vec (zeros k t)) [(zeros k t, t)] clock).cursor) :=
  lookup_admitted_under (ledger := [(zeros k t, t)]) (fun x => vec x)
    (fun step => Rewrite.appArgument step)
    (Relation.EqvGen.rel _ _
      (Rewrite.root (show assumed [(zeros k t, t)] (zeros k t) t from List.mem_singleton_self _)))
    clock

/-! ## Axiom audit -/

#print axioms length_zigzagOfRun
#print axioms rewrite_addCount
#print axioms zigzag_addCount
#print axioms evidence_exists
#print axioms evidence_lower_bound
#print axioms one_lookup

end Mettapedia.TypeTheory.ConversionCost
