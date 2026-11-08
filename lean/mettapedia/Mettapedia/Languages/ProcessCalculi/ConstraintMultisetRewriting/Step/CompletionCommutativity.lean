import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CompletionCorrectness
import Mathlib.Data.Fin.VecNotation

/-!
# Control: commutativity cannot be oriented, so completion fails

The signature has one binary function `·` and two constants `a`, `b`. The order compares sizes: a
ground simplification order that is not total, since `a·b` and `b·a` have the same size.

* **No order invariant under exchanging `a` and `b` orients `a·b ≈ b·a`**
  (`no_symmetric_order_orients`). This is the ground shadow of the non-ground fact that no order
  stable under substitution orients `x·y ≈ y·x`. The size order is such an order (`size_swap`).
* **From `a·b ≈ b·a` no rule applies** (`stuck`): Orient is refused both ways, Delete is refused
  since the sides differ, and every other rule needs a rule to read.
* **So completion fails** (`commutativity_fails`): every derivation from it is constant, the
  equation persists, the completion readout never commits, and every word problem is suspended.

With a total order the same ground equation would be oriented (`stuck_needs_partial`): failure here
is a property of the partial order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion.Commutativity

open Mettapedia.Logic.LP
open Superposition (Ctx)
open _root_.Relation (EqvGen)

/-- One binary function and the constants `a = 0`, `b = 1`. -/
abbrev sig : LPSignature where
  constants := Fin 2
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity _ := 2

/-- The size of a ground term. -/
def size : GroundTerm sig → ℕ
  | .const _ => 1
  | .app _ args => size (args 0) + size (args 1) + 1

instance : Preorder (GroundTerm sig) := Preorder.lift size

instance : WellFoundedLT (GroundTerm sig) := ⟨InvImage.wf size wellFounded_lt⟩

theorem lt_iff_size {s t : GroundTerm sig} : s < t ↔ size s < size t := Iff.rfl

theorem fin_two (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨_ | _ | _, h⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- **The size order is a simplification order.** -/
instance : SimplificationOrder sig where
  monotone f args i x lt := by
    rw [lt_iff_size] at lt ⊢
    show size (Function.update args i x 0) + size (Function.update args i x 1) + 1 <
      size (args 0) + size (args 1) + 1
    rcases fin_two i with rfl | rfl
    · rw [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      omega
    · rw [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      omega
  subterm f args i := by
    rw [lt_iff_size]
    show size (args i) < size (args 0) + size (args 1) + 1
    rcases fin_two i with rfl | rfl <;> omega

/-- `a`, `b` and `x·y`. -/
def a : GroundTerm sig := .const 0
def b : GroundTerm sig := .const 1
def mul (x y : GroundTerm sig) : GroundTerm sig := .app () ![x, y]

theorem size_mul (x y : GroundTerm sig) : size (mul x y) = size x + size y + 1 := rfl

/-- `a·b` and `b·a` differ. -/
theorem ab_ne_ba : mul a b ≠ mul b a := by
  intro same
  have args := eq_of_heq (GroundTerm.app.inj same).2
  have first := congrFun args 0
  have : (0 : Fin 2) = 1 := GroundTerm.const.inj first
  exact absurd this (by decide)

/-! ## No symmetric order orients commutativity -/

/-- Exchange `a` and `b`. -/
def swap : GroundTerm sig → GroundTerm sig
  | .const c => .const c.rev
  | .app f args => .app f fun i => swap (args i)

theorem swap_mul (x y : GroundTerm sig) : swap (mul x y) = mul (swap x) (swap y) := by
  show GroundTerm.app () (fun i => swap (![x, y] i)) = GroundTerm.app () ![swap x, swap y]
  congr 1
  funext i
  rcases fin_two i with rfl | rfl <;> rfl

theorem swap_ab : swap (mul a b) = mul b a := by
  rw [swap_mul]
  rfl

theorem swap_ba : swap (mul b a) = mul a b := by
  rw [swap_mul]
  rfl

/-- **No strict order invariant under exchanging `a` and `b` orients `a·b ≈ b·a`.** -/
theorem no_symmetric_order_orients (lt : GroundTerm sig → GroundTerm sig → Prop)
    (asymm : ∀ x y, lt x y → ¬ lt y x) (invariant : ∀ x y, lt x y → lt (swap x) (swap y)) :
    ¬ lt (mul b a) (mul a b) ∧ ¬ lt (mul a b) (mul b a) := by
  constructor
  · intro below
    have swapped := invariant _ _ below
    rw [swap_ab, swap_ba] at swapped
    exact asymm _ _ below swapped
  · intro below
    have swapped := invariant _ _ below
    rw [swap_ab, swap_ba] at swapped
    exact asymm _ _ below swapped

theorem size_swap (x : GroundTerm sig) : size (swap x) = size x := by
  induction x with
  | const c => rfl
  | app f args ih =>
      show size (swap (args 0)) + size (swap (args 1)) + 1 = size (args 0) + size (args 1) + 1
      rw [ih 0, ih 1]

/-- **The size order is invariant under the exchange**, so it orients neither side. -/
theorem size_unorientable : ¬ mul b a < mul a b ∧ ¬ mul a b < mul b a :=
  no_symmetric_order_orients (· < ·) (fun _ _ lt => lt_asymm lt) fun x y lt => by
    rw [lt_iff_size, size_swap, size_swap]
    exact lt

/-! ## Completion is stuck -/

/-- The start: `a·b ≈ b·a`. -/
def E₀ : Set (Item sig) := {Item.eqn s(mul a b, mul b a)}

/-- **No rule applies to `a·b ≈ b·a`.** -/
theorem stuck (ρ : Rule sig) (N' : Set (Item sig)) : ¬ Transition ρ E₀ N' := by
  intro t
  have noRule : ∀ l r, Item.rule l r ∉ E₀ := fun l r member => by simp [E₀] at member
  cases ρ with
  | deduce l₁ r₁ l₂ r₂ d => exact noRule l₁ r₁ (t.premise (by simp [Rule.reads]))
  | orient s t' =>
      have member : Item.eqn s(s, t') ∈ E₀ := t.taken (by simp [Rule.takes])
      have guard : t' < s := t.guard
      simp only [E₀, Set.mem_singleton_iff, Item.eqn.injEq, Sym2.eq_iff] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact size_unorientable.1 guard
      · exact size_unorientable.2 guard
  | delete s t' =>
      have member : Item.eqn s(s, t') ∈ E₀ := t.taken (by simp [Rule.takes])
      have same : s = t' := t.guard
      simp only [E₀, Set.mem_singleton_iff, Item.eqn.injEq, Sym2.eq_iff] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ab_ne_ba same
      · exact ab_ne_ba same.symm
  | simplify s t' l r c => exact noRule l r (t.premise (by simp [Rule.reads]))
  | compose s t' l r c => exact noRule l r (t.premise (by simp [Rule.reads]))
  | collapse s t' l r c => exact noRule l r (t.premise (by simp [Rule.reads]))

/-- **Completion of `a·b ≈ b·a` fails**: every derivation from it is constant, so the equation
persists; the completion readout never commits and every word problem is suspended. -/
theorem commutativity_fails {N : ℕ → Set (Item sig)} (derivation : Derivation N) (start : N 0 = E₀) :
    (∀ i, N i = E₀) ∧ Item.eqn s(mul a b, mul b a) ∈ limit N ∧
      (∀ finished, (completionReadout (limit N) finished).verdict ≠ .commit) ∧
      ∀ finished s t, (wordReadout (limit N) finished s t).verdict = .suspended := by
  have constant : ∀ i, N i = E₀ := by
    intro i
    induction i with
    | zero => exact start
    | succ i ih =>
        rcases derivation.step i with same | ⟨ρ, t⟩
        · rw [same, ih]
        · rw [ih] at t
          exact absurd t (stuck ρ _)
  have persists : Item.eqn s(mul a b, mul b a) ∈ limit N :=
    ⟨0, fun j _ => by rw [constant j]; exact Set.mem_singleton _⟩
  refine ⟨constant, persists, fun finished commit => ?_, fun finished s t => wordReadout_failure persists s t⟩
  exact (completionReadout_succeeded commit).2 _ persists

#print axioms ab_ne_ba
#print axioms no_symmetric_order_orients
#print axioms size_unorientable
#print axioms stuck
#print axioms commutativity_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion.Commutativity
