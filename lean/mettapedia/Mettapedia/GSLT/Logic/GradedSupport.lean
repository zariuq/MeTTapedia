import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic

/-!
# Graded rewriting: conservativity and support adequacy

A state has a finite list of candidate firings, indexed by occurrence, each
with a target and a clause value in a semiring `V` (the resolution algebra of
graded where-clauses). The Boolean image of the clauses is the base program:
a candidate is enabled when its value is nonzero, and a state is normal when no
candidate is enabled. The budgeted graded denotation `denote β s q` is the
coefficient of `q` in `T^β |s⟩`, where `T` sums the candidates weighted by
their clause values and fixes normal forms (the fictitious jump).

* **Support adequacy** (`reachIn_of_denote_ne_zero`): in every semiring a
  nonzero coefficient needs a history of enabled steps, so the support is
  inside the base program's reachable set. Grading cannot make a program do
  something its Boolean image could not do.
* **Conservativity** (`denote_ne_zero_iff_reachIn`): when the algebra cannot
  cancel (no two nonzero values sum to zero, none multiply to zero) the
  support is exactly the reachable set. This covers the Boolean semiring with
  disjunction (`OrBool`), multiplicities in `ℕ`, and nonnegative rates.
  Restricted to normal forms, the support is exactly the normal forms
  reachable within the budget (`normal_support_iff`); a state still reducing
  when the budget runs out is also in the support (`budget_frontier`).
* **Cancellation.** Over `ℤ` and over the xor ring on `Bool` two enabled
  histories can cancel, and the support loses a reachable state: the
  interference deficit.
* **End normalisation is not the jump chain.** Normalising the rate-weighted
  denotation at the end conditions on the whole history (`10/11`); the
  embedded jump chain normalises at every step (`1/2`).
* **Jump chain and uniformised chain.** For rates with a uniformisation
  constant, the uniformised chain and the embedded jump chain have the same
  absorption equations (`harmonic_uniformised_iff`) and different one-step
  laws; the continuous-time law itself is not formalised here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GradedSupport

universe u v

variable {S : Type u} {V : Type v}

/-! ## The base program and its reachability -/

section Base

variable [Zero V] (step : S → List (S × V))

/-- No candidate is enabled. -/
def IsNormal (s : S) : Prop :=
  ∀ p ∈ step s, p.2 = 0

/-- Reachability under the Boolean image of the clauses in exactly `β`
padded steps: a normal form stays where it is (the fictitious jump). -/
inductive ReachIn : ℕ → S → S → Prop where
  | refl (s : S) : ReachIn 0 s s
  | stay {β : ℕ} {s : S} : IsNormal step s → ReachIn (β + 1) s s
  | fire {β : ℕ} {s q : S} {p : S × V} : p ∈ step s → p.2 ≠ 0 → ReachIn β p.1 q →
      ReachIn (β + 1) s q

/-- Reachability in exactly `n` enabled steps, without padding. -/
inductive Reach : ℕ → S → S → Prop where
  | refl (s : S) : Reach 0 s s
  | fire {n : ℕ} {s q : S} {p : S × V} : p ∈ step s → p.2 ≠ 0 → Reach n p.1 q →
      Reach (n + 1) s q

variable {step}

/-- Padding at normal forms: a padded history reaching a normal form is an
unpadded history of at most the same length. -/
theorem reach_of_reachIn {β : ℕ} {s q : S} (reached : ReachIn step β s q) :
    ∃ n ≤ β, Reach step n s q ∧ (n < β → IsNormal step q) := by
  induction reached with
  | refl s => exact ⟨0, le_rfl, Reach.refl s, fun impossible => absurd impossible (lt_irrefl 0)⟩
  | @stay β s normal => exact ⟨0, Nat.zero_le _, Reach.refl s, fun _ => normal⟩
  | @fire β s q p member enabled _ ih =>
      obtain ⟨n, le, path, early⟩ := ih
      exact ⟨n + 1, Nat.succ_le_succ le, Reach.fire member enabled path,
        fun lt => early (Nat.lt_of_succ_lt_succ lt)⟩

/-- A history reaching a normal form can be padded to any larger budget. -/
theorem reachIn_of_reach_normal {n β : ℕ} {s q : S} (path : Reach step n s q)
    (normal : IsNormal step q) (le : n ≤ β) : ReachIn step β s q := by
  induction path generalizing β with
  | refl s =>
      cases β with
      | zero => exact ReachIn.refl s
      | succ β => exact ReachIn.stay normal
  | @fire n s q p member enabled _ ih =>
      obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
      exact ReachIn.fire member enabled (ih normal (by omega))

/-- **The padded reachable normal forms are the normal forms reachable within
the budget.** -/
theorem reachIn_normal_iff {β : ℕ} {s q : S} :
    ReachIn step β s q ∧ IsNormal step q ↔ ∃ n ≤ β, Reach step n s q ∧ IsNormal step q := by
  constructor
  · rintro ⟨reached, normal⟩
    obtain ⟨n, le, path, _⟩ := reach_of_reachIn reached
    exact ⟨n, le, path, normal⟩
  · rintro ⟨n, le, path, normal⟩
    exact ⟨reachIn_of_reach_normal path normal le, normal⟩

end Base

/-! ## The graded denotation -/

section Denotation

variable [Semiring V] [DecidableEq V] [DecidableEq S] (step : S → List (S × V))

instance (s : S) : Decidable (IsNormal step s) :=
  inferInstanceAs (Decidable (∀ p ∈ step s, p.2 = 0))

/-- **The budgeted graded denotation**: the coefficient of `q` in `T^β |s⟩`. -/
def denote : ℕ → S → S → V
  | 0, s, q => if s = q then 1 else 0
  | β + 1, s, q =>
      if IsNormal step s then (if s = q then 1 else 0)
      else ((step s).map fun p => p.2 * denote β p.1 q).sum

theorem denote_succ_of_normal {β : ℕ} {s q : S} (normal : IsNormal step s) :
    denote step (β + 1) s q = if s = q then 1 else 0 := by
  simp [denote, normal]

theorem denote_succ_of_not_normal {β : ℕ} {s q : S} (active : ¬ IsNormal step s) :
    denote step (β + 1) s q = ((step s).map fun p => p.2 * denote step β p.1 q).sum := by
  simp [denote, active]

variable {step}

/-- A list with nonzero sum has a nonzero entry. -/
theorem exists_ne_zero_of_sum_ne_zero {l : List V} (nonzero : l.sum ≠ 0) : ∃ a ∈ l, a ≠ 0 := by
  induction l with
  | nil => exact absurd List.sum_nil nonzero
  | cons a rest ih =>
      by_cases zero : a = 0
      · rw [List.sum_cons, zero, zero_add] at nonzero
        obtain ⟨b, member, ne⟩ := ih nonzero
        exact ⟨b, List.mem_cons_of_mem a member, ne⟩
      · exact ⟨a, List.mem_cons_self, zero⟩

/-- **Support adequacy**: in every semiring, a nonzero coefficient is reached
by the base program. -/
theorem reachIn_of_denote_ne_zero {β : ℕ} {s q : S} (nonzero : denote step β s q ≠ 0) :
    ReachIn step β s q := by
  induction β generalizing s with
  | zero =>
      simp only [denote] at nonzero
      split_ifs at nonzero with equal
      · subst equal
        exact ReachIn.refl s
      · exact absurd rfl nonzero
  | succ β ih =>
      by_cases normal : IsNormal step s
      · rw [denote_succ_of_normal step normal] at nonzero
        split_ifs at nonzero with equal
        · subst equal
          exact ReachIn.stay normal
        · exact absurd rfl nonzero
      · rw [denote_succ_of_not_normal step normal] at nonzero
        obtain ⟨term, member, termNonzero⟩ := exists_ne_zero_of_sum_ne_zero nonzero
        obtain ⟨p, candidate, rfl⟩ := List.mem_map.mp member
        have enabled : p.2 ≠ 0 := fun zero => termNonzero (by rw [zero, zero_mul])
        have onward : denote step β p.1 q ≠ 0 := fun zero => termNonzero (by rw [zero, mul_zero])
        exact ReachIn.fire candidate enabled (ih onward)

/-! ## Conservativity -/

/-- A resolution algebra that cannot cancel: a sum of values is zero only when
the first is, a product only when a factor is, and `1 ≠ 0`. -/
structure NoCancellation (V : Type v) [Semiring V] : Prop where
  add_eq_zero : ∀ a b : V, a + b = 0 → a = 0
  mul_eq_zero : ∀ a b : V, a * b = 0 → a = 0 ∨ b = 0
  one_ne_zero : (1 : V) ≠ 0

omit [DecidableEq V] [DecidableEq S] in
/-- Without cancellation, a list with a nonzero entry has a nonzero sum. -/
theorem sum_ne_zero_of_mem (noCancel : NoCancellation V) {l : List V} {a : V} (member : a ∈ l)
    (nonzero : a ≠ 0) : l.sum ≠ 0 := by
  induction l with
  | nil => exact absurd member List.not_mem_nil
  | cons b rest ih =>
      intro zero
      rw [List.sum_cons] at zero
      have head : b = 0 := noCancel.add_eq_zero b rest.sum zero
      have tail : rest.sum = 0 := noCancel.add_eq_zero rest.sum b (by rw [add_comm]; exact zero)
      rcases List.mem_cons.mp member with equal | inRest
      · exact nonzero (equal ▸ head)
      · exact ih inRest tail

/-- Without cancellation every reachable state has a nonzero coefficient. -/
theorem denote_ne_zero_of_reachIn (noCancel : NoCancellation V) {β : ℕ} {s q : S}
    (reached : ReachIn step β s q) : denote step β s q ≠ 0 := by
  induction reached with
  | refl s =>
      show (if s = s then (1 : V) else 0) ≠ 0
      rw [if_pos rfl]
      exact noCancel.one_ne_zero
  | @stay β s normal =>
      rw [denote_succ_of_normal step normal, if_pos rfl]
      exact noCancel.one_ne_zero
  | @fire β s q p member enabled _ ih =>
      have active : ¬ IsNormal step s := fun normal => enabled (normal p member)
      rw [denote_succ_of_not_normal step active]
      refine sum_ne_zero_of_mem noCancel (List.mem_map.mpr ⟨p, member, rfl⟩) ?_
      intro zero
      rcases noCancel.mul_eq_zero _ _ zero with left | right
      · exact enabled left
      · exact ih right

/-- **Conservativity**: over an algebra that cannot cancel, the support of the
graded denotation is exactly the base program's reachable set. -/
theorem denote_ne_zero_iff_reachIn (noCancel : NoCancellation V) {β : ℕ} {s q : S} :
    denote step β s q ≠ 0 ↔ ReachIn step β s q :=
  ⟨reachIn_of_denote_ne_zero, denote_ne_zero_of_reachIn noCancel⟩

/-- **Conservativity on normal forms**: the normal forms in the support are
exactly the normal forms reachable within the budget. -/
theorem normal_support_iff (noCancel : NoCancellation V) {β : ℕ} {s q : S} :
    denote step β s q ≠ 0 ∧ IsNormal step q ↔ ∃ n ≤ β, Reach step n s q ∧ IsNormal step q := by
  rw [denote_ne_zero_iff_reachIn noCancel]
  exact reachIn_normal_iff

/-- The interference deficit: reachable states outside the support. -/
def Deficit (β : ℕ) (s q : S) : Prop :=
  ReachIn step β s q ∧ denote step β s q = 0

/-- Without cancellation there is no deficit. -/
theorem no_deficit (noCancel : NoCancellation V) {β : ℕ} {s q : S} :
    ¬ Deficit (step := step) β s q :=
  fun ⟨reached, zero⟩ => denote_ne_zero_of_reachIn noCancel reached zero

end Denotation

/-! ## Algebras that cannot cancel -/

/-- The Boolean semiring: disjunction and conjunction. -/
structure OrBool where
  val : Bool
  deriving DecidableEq

namespace OrBool

instance : Zero OrBool := ⟨⟨false⟩⟩

instance : One OrBool := ⟨⟨true⟩⟩

instance : Add OrBool := ⟨fun a b => ⟨a.val || b.val⟩⟩

instance : Mul OrBool := ⟨fun a b => ⟨a.val && b.val⟩⟩

theorem ext' {a b : OrBool} (same : a.val = b.val) : a = b := by
  cases a
  cases b
  cases same
  rfl

instance : CommSemiring OrBool where
  add_assoc a b c := ext' (Bool.or_assoc a.val b.val c.val)
  zero_add a := ext' (Bool.false_or a.val)
  add_zero a := ext' (Bool.or_false a.val)
  add_comm a b := ext' (Bool.or_comm a.val b.val)
  left_distrib a b c := ext' (Bool.and_or_distrib_left a.val b.val c.val)
  right_distrib a b c := ext' (Bool.and_or_distrib_right a.val b.val c.val)
  zero_mul a := ext' (Bool.false_and a.val)
  mul_zero a := ext' (Bool.and_false a.val)
  mul_assoc a b c := ext' (Bool.and_assoc a.val b.val c.val)
  one_mul a := ext' (Bool.true_and a.val)
  mul_one a := ext' (Bool.and_true a.val)
  mul_comm a b := ext' (Bool.and_comm a.val b.val)
  nsmul := nsmulRec
  npow := npowRec

theorem noCancellation : NoCancellation OrBool where
  add_eq_zero a b sum := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        have value : (a || b) = false := congrArg OrBool.val sum
        cases a
        · rfl
        · exact absurd value (by simp)
  mul_eq_zero a b product := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        have value : (a && b) = false := congrArg OrBool.val product
        cases a
        · exact Or.inl rfl
        · cases b
          · exact Or.inr rfl
          · exact absurd value (by decide)
  one_ne_zero := fun equal => Bool.noConfusion (congrArg OrBool.val equal)

end OrBool

/-- Multiplicities (the bag semantics) cannot cancel. -/
theorem nat_noCancellation : NoCancellation ℕ where
  add_eq_zero a b sum := by omega
  mul_eq_zero a b product := Nat.mul_eq_zero.mp product
  one_ne_zero := Nat.one_ne_zero

/-- Exact nonnegative rational rates have neither cancellation nor zero divisors. -/
theorem nonnegative_rat_noCancellation : NoCancellation ℚ≥0 where
  add_eq_zero _ _ sum := (add_eq_zero.mp sum).1
  mul_eq_zero _ _ product := mul_eq_zero.mp product
  one_ne_zero := one_ne_zero

theorem nonnegative_rat_add_value (left right : ℚ≥0) :
    ((left + right : ℚ≥0) : ℚ) = (left : ℚ) + (right : ℚ) := rfl

theorem nonnegative_rat_multiply_value (left right : ℚ≥0) :
    ((left * right : ℚ≥0) : ℚ) = (left : ℚ) * (right : ℚ) := rfl

/-! ## Controls -/

namespace Control

/-- Five states for the controls. -/
inductive Node where
  | source
  | left
  | right
  | sink
  | other
  deriving DecidableEq

open Node

/-- Two enabled histories from `source` to `sink`, with clause values `a`
and `b` on the second step. -/
def diamond {V : Type v} [Zero V] [One V] (a b : V) : Node → List (Node × V)
  | .source => [(.left, 1), (.right, 1)]
  | .left => [(.sink, a)]
  | .right => [(.sink, b)]
  | _ => []

theorem diamond_reach {V : Type v} [Semiring V] (a b : V) (ha : a ≠ 0) (one : (1 : V) ≠ 0) :
    ReachIn (diamond a b) 2 .source .sink :=
  ReachIn.fire (p := (.left, 1)) (by simp [diamond]) one
    (ReachIn.fire (p := (.sink, a)) (by simp [diamond]) ha
      (ReachIn.refl _))

/-- **Cancellation over the integers**: the two histories carry `1` and `-1`,
so the reachable `sink` is outside the support. -/
theorem int_deficit : Deficit (step := diamond (1 : ℤ) (-1)) 2 .source .sink := by
  refine ⟨diamond_reach 1 (-1) one_ne_zero one_ne_zero, ?_⟩
  decide

/-- **The xor ring is not the Boolean semiring**: over Mathlib's Boolean ring,
`1 + 1 = 0`, and the two enabled histories cancel. -/
theorem xor_deficit : Deficit (step := diamond (1 : Bool) 1) 2 .source .sink := by
  refine ⟨diamond_reach (1 : Bool) 1 (by decide) (by decide), ?_⟩
  decide

/-- Positive control: over the disjunctive Boolean semiring the same program
keeps `sink` in the support. -/
theorem orBool_keeps_sink :
    denote (diamond (1 : OrBool) 1) 2 .source .sink ≠ 0 :=
  denote_ne_zero_of_reachIn OrBool.noCancellation
    (diamond_reach (1 : OrBool) 1 OrBool.noCancellation.one_ne_zero
      OrBool.noCancellation.one_ne_zero)

/-- A state that keeps reducing: `other` loops. -/
def loop : Node → List (Node × ℕ)
  | .other => [(.other, 1)]
  | _ => []

/-- **The budget frontier**: a state still reducing when the budget runs out
is in the support, although it is not a normal form. -/
theorem budget_frontier (β : ℕ) :
    denote loop β .other .other ≠ 0 ∧ ¬ IsNormal loop .other := by
  refine ⟨denote_ne_zero_of_reachIn nat_noCancellation ?_, fun normal => ?_⟩
  · induction β with
    | zero => exact ReachIn.refl _
    | succ β ih => exact ReachIn.fire (p := (.other, 1)) (by simp [loop]) one_ne_zero ih
  · exact one_ne_zero (normal (.other, 1) (by simp [loop]))

/-! ### End normalisation against the jump chain -/

/-- Rates: `source → left` and `source → right` at rate `1`, then
`left → sink` at rate `10` and `right → other` at rate `1`. -/
def rates : Node → List (Node × ℚ)
  | .source => [(.left, 1), (.right, 1)]
  | .left => [(.sink, 10)]
  | .right => [(.other, 1)]
  | _ => []

/-- The embedded jump chain: rates normalised at each state. -/
def jumpChain : Node → List (Node × ℚ)
  | .source => [(.left, 1 / 2), (.right, 1 / 2)]
  | .left => [(.sink, 1)]
  | .right => [(.other, 1)]
  | _ => []

/-- **End normalisation is not the jump chain.** The rate-weighted denotation
gives `sink` and `other` the weights `10` and `1`, so normalising at the end
gives `10/11`; the jump chain reaches `sink` with probability `1/2`. -/
theorem end_normalisation_is_not_the_jump_chain :
    denote rates 2 .source .sink = 10 ∧ denote rates 2 .source .other = 1 ∧
      denote jumpChain 2 .source .sink = 1 / 2 ∧
      denote rates 2 .source .sink /
          (denote rates 2 .source .sink + denote rates 2 .source .other) ≠
        denote jumpChain 2 .source .sink := by
  have normalSink : ∀ step : Node → List (Node × ℚ), step .sink = [] → IsNormal step .sink :=
    fun step empty p member => by rw [empty] at member; exact absurd member List.not_mem_nil
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [denote, rates, jumpChain, IsNormal]
  all_goals norm_num

end Control

/-! ## The jump chain and the uniformised chain -/

section Uniformisation

/-- A function is harmonic at `x` for a step law when it is the weighted
average of its values at the successors. -/
def HarmonicAt (step : S → List (S × ℚ)) (h : S → ℚ) (x : S) : Prop :=
  h x = ((step x).map fun p => p.2 * h p.1).sum

/-- The uniformised chain of a jump chain: stay with probability `1 - λ`,
otherwise take a jump-chain step. -/
def uniformised (jump : S → List (S × ℚ)) (laziness : S → ℚ) (x : S) : List (S × ℚ) :=
  (x, 1 - laziness x) :: (jump x).map fun p => (p.1, laziness x * p.2)

/-- **Same absorption equations**: where the jump rate is positive, a function
is harmonic for the uniformised chain exactly when it is harmonic for the
jump chain. Absorption probabilities, as solutions of these equations with
boundary values at absorbing states, therefore coincide. -/
theorem harmonic_uniformised_iff (jump : S → List (S × ℚ)) (laziness : S → ℚ) (h : S → ℚ)
    {x : S} (positive : laziness x ≠ 0) :
    HarmonicAt (uniformised jump laziness) h x ↔ HarmonicAt jump h x := by
  unfold HarmonicAt uniformised
  rw [List.map_cons, List.sum_cons, List.map_map]
  have scaled :
      ((jump x).map ((fun p : S × ℚ => p.2 * h p.1) ∘ fun p => (p.1, laziness x * p.2))).sum =
      laziness x * ((jump x).map fun p => p.2 * h p.1).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    ring
  rw [scaled]
  constructor
  · intro equation
    have : laziness x * h x = laziness x * ((jump x).map fun p => p.2 * h p.1).sum := by
      linarith
    exact mul_left_cancel₀ positive this
  · intro equation
    rw [← equation]
    ring

/-- **Different one-step law**: from `source`, the jump chain moves to `left`
with probability `1/2`, the chain uniformised at rate `4` stays put with
probability `1/2` and moves to `left` with probability `1/4`. -/
theorem transient_laws_differ :
    uniformised Control.jumpChain (fun _ => 1 / 2) .source =
      [(.source, 1 / 2), (.left, 1 / 4), (.right, 1 / 4)] ∧
      Control.jumpChain .source = [(.left, 1 / 2), (.right, 1 / 2)] := by
  constructor
  · simp [uniformised, Control.jumpChain]
    norm_num
  · rfl

end Uniformisation

end Mettapedia.GSLT.GradedSupport
