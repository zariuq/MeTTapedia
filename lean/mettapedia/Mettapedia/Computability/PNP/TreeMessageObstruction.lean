import Mettapedia.Computability.PNP.HypothesisClass
import Mathlib.Tactic

/-!
# P vs NP crux: tree structure alone does not force a small message class

One natural rescue route is:

> "The local neighborhoods are tree-like, so the witness-bit rule should come
> from a tiny message-passing or dynamic-program class."

This file shows that tree structure by itself is far too weak.  Even a *fixed
perfect binary tree architecture* of depth `n` realizes every Boolean rule on
`n` visible bits, just by choosing the leaf labels appropriately.  So no exact
compression theorem can follow from tree-likeness alone.
-/

namespace Mettapedia.Computability.PNP

/-- Perfect binary decision trees of depth `n`, with only the leaves carrying
data. Internal nodes just branch on the next visible input bit. -/
inductive DecisionTree : ℕ → Type
  | leaf : Bool → DecisionTree 0
  | node : DecisionTree n → DecisionTree n → DecisionTree (n + 1)

/-- The unique width-`0` visible input. -/
def emptyBits : VisibleBits 0 := fun i => Fin.elim0 i

/-- Drop the first visible bit. -/
def tailBits {n : ℕ} (x : VisibleBits (n + 1)) : VisibleBits n :=
  fun i => x i.succ

/-- Prepend one visible bit. -/
def consBits {n : ℕ} (b : Bool) (x : VisibleBits n) : VisibleBits (n + 1) :=
  Fin.cases b x

lemma tailBits_consBits {n : ℕ} (b : Bool) (x : VisibleBits n) :
    tailBits (consBits b x) = x := by
  funext i
  simp [tailBits, consBits]

lemma consBits_head_tail {n : ℕ} (x : VisibleBits (n + 1)) :
    consBits (x 0) (tailBits x) = x := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [consBits]
  · intro j
    simp [consBits, tailBits]

/-- Evaluate a depth-`n` decision tree on `n` visible bits. -/
def DecisionTree.eval : {n : ℕ} → DecisionTree n → LocalRule n
  | 0, .leaf b => fun _ => b
  | _ + 1, .node left right => fun x =>
      if x 0 then DecisionTree.eval right (tailBits x) else DecisionTree.eval left (tailBits x)

/-- Encode any Boolean rule as a leaf-labeled perfect binary decision tree. -/
def encodeDecisionTree : {n : ℕ} → LocalRule n → DecisionTree n
  | 0, rule => .leaf (rule emptyBits)
  | _ + 1, rule =>
      .node
        (encodeDecisionTree fun x => rule (consBits false x))
        (encodeDecisionTree fun x => rule (consBits true x))

theorem eval_encodeDecisionTree : ∀ {n : ℕ} (rule : LocalRule n),
    DecisionTree.eval (encodeDecisionTree rule) = rule
  | 0, rule => by
      funext x
      have hx : x = emptyBits := by
        funext i
        exact Fin.elim0 i
      simp [encodeDecisionTree, DecisionTree.eval, hx]
  | n + 1, rule => by
      funext x
      by_cases hx : x 0
      · have ih :=
          congrFun (eval_encodeDecisionTree (rule := fun y => rule (consBits true y))) (tailBits x)
        have hcons : consBits true (tailBits x) = x := by
          simpa [hx] using consBits_head_tail x
        simpa [DecisionTree.eval, encodeDecisionTree, hx, hcons] using ih
      · have ih :=
          congrFun (eval_encodeDecisionTree (rule := fun y => rule (consBits false y))) (tailBits x)
        have hcons : consBits false (tailBits x) = x := by
          simpa [hx] using consBits_head_tail x
        simpa [DecisionTree.eval, encodeDecisionTree, hx, hcons] using ih

/-- The fixed-depth perfect-tree architecture realizes the full local-rule class. -/
theorem evalDecisionTree_surjective (n : ℕ) :
    Function.Surjective (@DecisionTree.eval n) := by
  intro rule
  exact ⟨encodeDecisionTree rule, eval_encodeDecisionTree rule⟩

/-- Equivalently, the semantics realized by depth-`n` decision trees is all of
`LocalRule n`. -/
theorem decisionTreeSemantics_eq_univ (n : ℕ) :
    Set.range (@DecisionTree.eval n) = Set.univ := by
  ext rule
  constructor
  · intro _
    trivial
  · intro _
    rcases evalDecisionTree_surjective n rule with ⟨tree, rfl⟩
    exact ⟨tree, rfl⟩

/-- Therefore no `s`-bit exact code can cover the semantics of all depth-`n`
perfect decision trees once `s < 2^n`. -/
theorem no_surjective_bitCode_to_decisionTreeSemantics_of_lt {n s : ℕ}
    (decode : BitCode s → DecisionTree n) (hs : s < 2 ^ n) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (decode code)) := by
  exact not_surjective_decode_to_fullLocalRule_of_lt (decode := fun code => DecisionTree.eval (decode code)) hs

/-- Binary-log specialization: even exact semantics of depth-`log₂ m + 1`
perfect trees cannot be coded below `m` bits. -/
theorem no_small_exact_treeQuotient_binaryLogWidth {m s : ℕ}
    (decode : BitCode s → DecisionTree (Nat.log 2 m + 1)) (hs : s < m) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (decode code)) := by
  apply no_surjective_bitCode_to_decisionTreeSemantics_of_lt decode
  exact Nat.lt_trans hs (Nat.lt_pow_succ_log_self Nat.one_lt_two m)

end Mettapedia.Computability.PNP
