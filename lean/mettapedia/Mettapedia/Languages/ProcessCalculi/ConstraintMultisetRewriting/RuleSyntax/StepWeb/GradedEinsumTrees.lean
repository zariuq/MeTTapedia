import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedEinsum

/-!
# Contraction trees: two contractions in sequence are one fused contraction

A contraction whose output feeds one operand of a second contraction can be fused: the fused rule binds the
pairs of bindings that agree on the intermediate row, and multiplies the second rule's operands before the
intermediate one, the first rule's operands, and the second rule's operands after it, in that order
(`fuse`). Firing the first contraction and then the second gives, at every row the first one does not make, what
firing the fused contraction once gives (`fireOn_fireOn_eq_fuse`), provided:
* the intermediate rows start empty, and
* the first contraction makes none of the rows the second one reads through its other operands.

The proof is distributivity on both sides of the intermediate factor, so it holds over every semiring, with the
factor order kept. Read from right to left it licenses evaluating a multiway contraction through any binary
contraction tree that materializes its intermediate rows: the choice of contraction order.

Controls: without empty intermediate rows, the stored intermediate annotation contributes on its own
(`Controls.intermediate_must_start_empty`); with them, the hypotheses hold in an instance and the two
evaluations agree (`Controls.two_steps_fuse_when_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedEinsumTrees

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra (Space)
open GradedStore (KeepRule)
open GradedEinsum (Contraction)

universe uB uB' uG uK

variable {B₁ : Type uB} {B₂ : Type uB'} {G : Type uG}

/-- **The fused contraction** of a first contraction `c₁` into the operand `x` of a second one, whose other
operands are `pre` before `x` and `post` after it, and whose output is `out₂`. It binds pairs of bindings. -/
def fuse (pre : List (B₂ → G)) (post : List (B₂ → G)) (out₂ : B₂ → G) (c₁ : Contraction B₁ G) :
    Contraction (B₂ × B₁) G :=
  ⟨pre.map (· ∘ Prod.fst) ++ c₁.operands.map (· ∘ Prod.snd) ++ post.map (· ∘ Prod.fst), out₂ ∘ Prod.fst⟩

/-- The pairs of catalogued bindings that agree on the intermediate row. -/
def fuseCat [DecidableEq G] (x : B₂ → G) (c₁ : Contraction B₁ G) (cat₂ : Finset B₂) (cat₁ : Finset B₁) :
    Finset (B₂ × B₁) :=
  (cat₂ ×ˢ cat₁).filter fun p => c₁.output p.2 = x p.1

variable {K : Type uK} [Semiring K] [DecidableEq G]

omit [DecidableEq G] in
theorem prod_operands_append (pre post : List (B₂ → G)) (x : B₂ → G) (T : Space K G) (b : B₂) :
    (((pre ++ [x] ++ post).map fun f => f b).map T).prod =
      ((pre.map fun f => f b).map T).prod * T (x b) * ((post.map fun f => f b).map T).prod := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]

omit [DecidableEq G] in
theorem prod_fuse (pre post : List (B₂ → G)) (out₂ : B₂ → G) (c₁ : Contraction B₁ G) (S : Space K G)
    (p : B₂ × B₁) :
    (((fuse pre post out₂ c₁).operands.map fun f => f p).map S).prod =
      ((pre.map fun f => f p.1).map S).prod * ((c₁.operands.map fun f => f p.2).map S).prod *
        ((post.map fun f => f p.1).map S).prod := by
  simp only [fuse, List.map_append, List.map_map, List.prod_append, Function.comp_def]

/-- **Two contractions in sequence are one fused contraction.** The second contraction reads the first one's
output through its operand `x`. At a row `g` that the first contraction does not make, firing the first and then
the second gives what firing the fused contraction once gives, when the intermediate rows start empty and the
first contraction makes none of the rows read through `pre` and `post`. -/
theorem fireOn_fireOn_eq_fuse (c₁ : Contraction B₁ G) (pre post : List (B₂ → G)) (x out₂ : B₂ → G)
    (cat₁ : Finset B₁) (cat₂ : Finset B₂) (S : Space K G) (g : G)
    (empty : ∀ b₂ ∈ cat₂, S (x b₂) = 0)
    (apart : ∀ b₂ ∈ cat₂, ∀ y ∈ pre ++ post, ∀ b₁ ∈ cat₁, c₁.output b₁ ≠ y b₂)
    (notMade : ∀ b₁ ∈ cat₁, c₁.output b₁ ≠ g) :
    (Contraction.toRule ⟨pre ++ [x] ++ post, out₂⟩).fireOn cat₂ (c₁.toRule.fireOn cat₁ S) g =
      (fuse pre post out₂ c₁).toRule.fireOn (fuseCat x c₁ cat₂ cat₁) S g := by
  -- the first firing changes neither `g` nor the rows read through `pre` and `post`
  have kept : ∀ h : G, (∀ b₁ ∈ cat₁, c₁.output b₁ ≠ h) → c₁.toRule.fireOn cat₁ S h = S h := by
    intro h notOut
    rw [Contraction.fireOn_apply, Finset.sum_eq_zero, add_zero]
    intro b₁ member
    exact absurd (Finset.mem_filter.mp member).2 (notOut b₁ (Finset.mem_filter.mp member).1)
  -- at an intermediate row the first firing holds the sum over the first contraction's bindings
  have intermediate : ∀ b₂ ∈ cat₂, c₁.toRule.fireOn cat₁ S (x b₂) =
      ∑ b₁ ∈ cat₁ with c₁.output b₁ = x b₂, ((c₁.operands.map fun f => f b₁).map S).prod := by
    intro b₂ member
    rw [Contraction.fireOn_apply, empty b₂ member, zero_add]
  have sameSide : ∀ b₂ ∈ cat₂, ∀ ys : List (B₂ → G), (∀ y ∈ ys, y ∈ pre ++ post) →
      ((ys.map fun f => f b₂).map (c₁.toRule.fireOn cat₁ S)).prod = ((ys.map fun f => f b₂).map S).prod := by
    intro b₂ member ys inside
    rw [List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y yIn
    exact kept _ fun b₁ b₁In => apart b₂ member y (inside y yIn) b₁ b₁In
  rw [Contraction.fireOn_apply (⟨pre ++ [x] ++ post, out₂⟩ : Contraction B₂ G), kept g notMade,
    Contraction.fireOn_apply (fuse pre post out₂ c₁)]
  congr 1
  rw [fuseCat, Finset.filter_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b₂ member
  dsimp only
  rw [prod_operands_append, sameSide b₂ member pre (fun y yIn => List.mem_append_left _ yIn),
    sameSide b₂ member post (fun y yIn => List.mem_append_right _ yIn), intermediate b₂ member,
    Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  by_cases out : out₂ b₂ = g
  · rw [if_pos out]
    apply Finset.sum_congr rfl
    intro b₁ _
    rw [prod_fuse]
    by_cases agree : c₁.output b₁ = x b₂
    · simp [fuse, out, agree]
    · simp [fuse, out, agree]
  · rw [if_neg out]
    symm
    apply Finset.sum_eq_zero
    intro b₁ _
    simp [fuse, out]

namespace Controls

/-- The first contraction reads row `0` and makes row `1`, the intermediate row. -/
def first : Contraction Unit (Fin 3) :=
  ⟨[fun _ => 0], fun _ => 1⟩

/-- A store whose intermediate row already holds one. -/
noncomputable def heldStore : Space ℕ (Fin 3) :=
  Finsupp.single 0 1 + Finsupp.single 1 1

/-- **The intermediate rows must start empty**: an annotation already held by the intermediate row contributes to
the evaluation in two steps and not to the fused contraction. -/
theorem intermediate_must_start_empty :
    (Contraction.toRule (⟨[] ++ [fun _ => 1] ++ [], fun _ => 2⟩ : Contraction Unit (Fin 3))).fireOn
        Finset.univ (first.toRule.fireOn Finset.univ heldStore) 2 = 2 ∧
      (fuse [] [] (fun _ : Unit => (2 : Fin 3)) first).toRule.fireOn
        (fuseCat (fun _ : Unit => (1 : Fin 3)) first Finset.univ Finset.univ) heldStore 2 = 1 := by
  constructor
  · simp [Contraction.fireOn_apply, first, heldStore]
  · simp [Contraction.fireOn_apply, fuse, fuseCat, first, heldStore]

/-- A store whose intermediate row is empty. -/
noncomputable def emptyStore : Space ℕ (Fin 3) :=
  Finsupp.single 0 1

/-- **The hypotheses hold in an instance**: with the intermediate row empty, the evaluation in two steps is the
fused contraction. -/
theorem two_steps_fuse_when_empty :
    (Contraction.toRule (⟨[] ++ [fun _ => 1] ++ [], fun _ => 2⟩ : Contraction Unit (Fin 3))).fireOn
        Finset.univ (first.toRule.fireOn Finset.univ emptyStore) 2 =
      (fuse [] [] (fun _ : Unit => (2 : Fin 3)) first).toRule.fireOn
        (fuseCat (fun _ : Unit => (1 : Fin 3)) first Finset.univ Finset.univ) emptyStore 2 :=
  fireOn_fireOn_eq_fuse first [] [] (fun _ => 1) (fun _ => 2) Finset.univ Finset.univ emptyStore 2
    (fun _ _ => by simp [emptyStore]) (fun _ _ y member => by simp at member)
    (fun _ _ => by simp [first])

end Controls

#print axioms fireOn_fireOn_eq_fuse
#print axioms Controls.intermediate_must_start_empty
#print axioms Controls.two_steps_fuse_when_empty

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedEinsumTrees
