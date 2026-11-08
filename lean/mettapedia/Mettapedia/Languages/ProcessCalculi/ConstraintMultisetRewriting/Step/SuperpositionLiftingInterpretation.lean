import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionGround
import Mathlib.Data.Nat.Pairing

/-!
# A ground simplification ordering for any countable signature: the pairing interpretation

Given injective codes of the constants and function symbols into the natural numbers
(`SymbolCodes`), every ground term is interpreted as a natural number (`interp`): a constant `c` as
`2·code(c)`, and `f(t₁, …, tₙ)` as `2·⟨code(f), ⟨t₁, ⟨t₂, … ⟨tₙ, 0⟩⟩⟩⟩ + 1`, with Cantor's pairing
function `⟨·, ·⟩` (`Nat.pair`).

* The interpretation is **injective** (`interp_injective`), so comparing interpretations is a linear
  order on ground terms (`interpOrder`), well founded (`interpOrder_wellFounded`).
* Pairing is strictly monotone in each argument and bounds both, so the order is **compatible with
  contexts** and **contains the strict subterm relation**: a ground simplification ordering
  (`interpOrder_simplification`), a valid parameter of the ground calculus.

This ordering is neither the Knuth–Bendix nor the lexicographic path ordering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

variable {sig : LPSignature}

/-! ## Pairing tuples -/

/-- A tuple of numbers paired into one: `⟨x₀, ⟨x₁, … ⟨xₙ₋₁, 0⟩⟩⟩`. -/
def pairTuple : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, x => Nat.pair (x 0) (pairTuple n fun i => x i.succ)

theorem pairTuple_injective : ∀ (n : ℕ) {x y : Fin n → ℕ}, pairTuple n x = pairTuple n y → x = y
  | 0, x, y, _ => funext fun i => i.elim0
  | n + 1, x, y, same => by
      obtain ⟨head, tail⟩ := Nat.pair_eq_pair.mp same
      have rest := pairTuple_injective n tail
      funext i
      refine Fin.cases head (fun j => ?_) i
      exact congrFun rest j

theorem le_pairTuple : ∀ (n : ℕ) (x : Fin n → ℕ) (i : Fin n), x i ≤ pairTuple n x
  | 0, _, i => i.elim0
  | n + 1, x, i => by
      refine Fin.cases (Nat.left_le_pair _ _) (fun j => ?_) i
      exact (le_pairTuple n (fun k => x k.succ) j).trans (Nat.right_le_pair _ _)

/-- **Pairing a tuple is strictly monotone in each place.** -/
theorem pairTuple_lt : ∀ (n : ℕ) {x y : Fin n → ℕ} (i : Fin n), (∀ j, j ≠ i → x j = y j) →
    x i < y i → pairTuple n x < pairTuple n y
  | 0, _, _, i, _, _ => i.elim0
  | n + 1, x, y, i, others, lt => by
      show Nat.pair (x 0) (pairTuple n fun k => x k.succ) < Nat.pair (y 0) (pairTuple n fun k => y k.succ)
      refine Fin.cases (fun others lt => ?_) (fun j others lt => ?_) i others lt
      · have tails : (fun k : Fin n => x k.succ) = fun k => y k.succ :=
          funext fun k => others k.succ (Fin.succ_ne_zero k)
        rw [tails]
        exact Nat.pair_lt_pair_left _ lt
      · rw [others 0 (Fin.succ_ne_zero j).symm]
        exact Nat.pair_lt_pair_right _ (pairTuple_lt n j
          (fun k ne => others k.succ fun h => ne (Fin.succ_injective _ h)) lt)

/-! ## The interpretation -/

/-- **Codes of the symbols**: injective codings of the constants and the function symbols. -/
structure SymbolCodes (sig : LPSignature) where
  const : sig.constants → ℕ
  const_injective : Function.Injective const
  fn : sig.functionSymbols → ℕ
  fn_injective : Function.Injective fn

variable (κ : SymbolCodes sig)

/-- **The pairing interpretation of a ground term.** -/
def interp : GroundTerm sig → ℕ
  | .const c => 2 * κ.const c
  | .app f args => 2 * Nat.pair (κ.fn f) (pairTuple _ fun i => interp (args i)) + 1

theorem interp_injective : Function.Injective (interp κ) := by
  intro s
  induction s with
  | const c =>
      intro t same
      cases t with
      | const d =>
          have codes : κ.const c = κ.const d := by
            have h : 2 * κ.const c = 2 * κ.const d := same
            omega
          rw [κ.const_injective codes]
      | app g args =>
          have h : 2 * κ.const c = 2 * Nat.pair (κ.fn g) (pairTuple _ fun i => interp κ (args i)) + 1 := same
          omega
  | app f args ih =>
      intro t same
      cases t with
      | const d =>
          have h : 2 * Nat.pair (κ.fn f) (pairTuple _ fun i => interp κ (args i)) + 1 = 2 * κ.const d := same
          omega
      | app g args' =>
          have h : 2 * Nat.pair (κ.fn f) (pairTuple _ fun i => interp κ (args i)) + 1 =
              2 * Nat.pair (κ.fn g) (pairTuple _ fun i => interp κ (args' i)) + 1 := same
          have pairs : Nat.pair (κ.fn f) (pairTuple _ fun i => interp κ (args i)) =
              Nat.pair (κ.fn g) (pairTuple _ fun i => interp κ (args' i)) := by omega
          obtain ⟨symbols, tuples⟩ := Nat.pair_eq_pair.mp pairs
          have fg := κ.fn_injective symbols
          subst fg
          have values := pairTuple_injective _ tuples
          have args_eq : args = args' := funext fun i => ih i (congrFun values i)
          rw [args_eq]

/-- **The interpretation ordering.** -/
abbrev interpOrder : LinearOrder (GroundTerm sig) := LinearOrder.lift' (interp κ) (interp_injective κ)

theorem interpOrder_lt_iff {s t : GroundTerm sig} :
    (interpOrder κ).lt s t ↔ interp κ s < interp κ t :=
  Iff.rfl

theorem interpOrder_wellFounded : @WellFoundedLT (GroundTerm sig) (interpOrder κ).toLT :=
  ⟨InvImage.wf (interp κ) wellFounded_lt⟩

/-- **The interpretation ordering is a ground simplification ordering.** -/
theorem interpOrder_simplification : @GroundSimplification sig (interpOrder κ) := by
  let _ := interpOrder κ
  constructor
  · intro f args i a lt
    show interp κ (.app f (Function.update args i a)) < interp κ (.app f args)
    show 2 * Nat.pair (κ.fn f) (pairTuple _ fun j => interp κ (Function.update args i a j)) + 1 <
      2 * Nat.pair (κ.fn f) (pairTuple _ fun j => interp κ (args j)) + 1
    have inner := pairTuple_lt _ (x := fun j => interp κ (Function.update args i a j))
      (y := fun j => interp κ (args j)) i (fun j ne => by simp only [Function.update_of_ne ne])
      (by simp only [Function.update_self]; exact lt)
    have outer := Nat.pair_lt_pair_right (κ.fn f) inner
    omega
  · intro f args i
    show interp κ (args i) < 2 * Nat.pair (κ.fn f) (pairTuple _ fun j => interp κ (args j)) + 1
    have one := le_pairTuple _ (fun j => interp κ (args j)) i
    have two := Nat.right_le_pair (κ.fn f) (pairTuple _ fun j => interp κ (args j))
    omega

#print axioms pairTuple_injective
#print axioms le_pairTuple
#print axioms pairTuple_lt
#print axioms interp_injective
#print axioms interpOrder_wellFounded
#print axioms interpOrder_simplification

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
