import Mettapedia.Algorithms.WellFoundedServices.InertRecursor

/-!
# Measured recursion and the accessibility route

Two ways to run a recursion whose calls lower a natural-number measure.

* **Measure-based recursion** recurses on a natural-number bound for the
  measure (`recBelow`, `MeasuredLoop.runBelow`). It is structural recursion on
  `Nat`, so the kernel evaluates it.
* **The accessibility route** runs the same one-step functional through an
  arbitrary `InertRecursor` over the measure relation (`MeasuredLoop.loopAcc`).
  Only the propositional unfolding is available about it.

`InertRecursor.ofMeasure` packages measure-based recursion as an inert
recursor, so programs written through the route run. The agreement theorems
(`recursor_eq_recBelow`, `MeasuredLoop.loopAcc_eq_run`) say that every inert
recursor computes what the measure-based program computes.

A `MeasuredLoop` is a state machine whose step either stops with a result or
continues with a state of smaller measure. Its invariant rule
(`MeasuredLoop.run_induction`, and `MeasuredLoop.loopAcc_induction` proved from
the unfolding alone) is the loop rule of Hoare logic with the measure as
variant.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices

open Mettapedia.Order

universe u v w

/-! ## Recursion below a bound -/

section Measure

variable {α : Sort u} (μ : α → ℕ)

variable {C : α → Sort v}

/-- **Measure-based recursion**: structural recursion on a bound for the
measure. -/
def recBelow (F : ∀ x, (∀ y, μ y < μ x → C y) → C x) : (n : ℕ) → (a : α) → μ a < n → C a
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, h => F a fun y hy => recBelow F n y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_succ h))

/-- The bound does not matter. -/
theorem recBelow_eq (F : ∀ x, (∀ y, μ y < μ x → C y) → C x) :
    ∀ (n m : ℕ) (a : α) (hn : μ a < n) (hm : μ a < m), recBelow μ F n a hn = recBelow μ F m a hm
  | 0, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | n + 1, m + 1, a, _, _ => by
      simp only [recBelow]
      congr 1
      funext y hy
      exact recBelow_eq F n m y _ _

/-- Measure-based recursion at the least sufficient bound. -/
def recMeasure (F : ∀ x, (∀ y, μ y < μ x → C y) → C x) (a : α) : C a :=
  recBelow μ F (μ a + 1) a (Nat.lt_succ_self _)

/-- The unfolding equation of measure-based recursion. -/
theorem recMeasure_eq (F : ∀ x, (∀ y, μ y < μ x → C y) → C x) (a : α) :
    recMeasure μ F a = F a fun y _ => recMeasure μ F y :=
  congrArg (F a) (funext fun y => funext fun _ => recBelow_eq μ F _ _ y _ _)

/-- **Measure-based recursion is an inert recursor** over the measure
relation. It is computable, so programs written through the accessibility
route run with it. -/
def InertRecursor.ofMeasure : InertRecursor.{u, v} (fun y x => μ y < μ x) where
  recursor := fun F a _ => recMeasure μ F a
  unfold := fun F a _ => recMeasure_eq μ F a

/-- **Agreement**: every inert recursor over the measure relation computes
measure-based recursion. -/
theorem recursor_eq_recMeasure (I : InertRecursor.{u, v} (fun y x => μ y < μ x))
    (F : ∀ x, (∀ y, μ y < μ x → C y) → C x) (a : α) :
    I.recursor F a (accCode_measure μ a) = recMeasure μ F a :=
  I.rec_eq_of_fix F (recMeasure μ F) (recMeasure_eq μ F) _

end Measure

/-! ## Measured loops -/

/-- A state machine with a variant: every step stops with a result or
continues with a state of smaller measure. -/
structure MeasuredLoop (σ : Type u) (β : Type w) where
  measure : σ → ℕ
  step : (s : σ) → {s' : σ // measure s' < measure s} ⊕ β

namespace MeasuredLoop

variable {σ : Type u} {β : Type w} (L : MeasuredLoop σ β)

/-- One pass of the loop body; `k` is the rest of the loop. -/
def body (s : σ) (k : ∀ s', L.measure s' < L.measure s → β) : β :=
  match L.step s with
  | .inl next => k next.1 next.2
  | .inr result => result

theorem body_congr (s : σ) {k k' : ∀ s', L.measure s' < L.measure s → β}
    (h : ∀ s' hs, k s' hs = k' s' hs) : L.body s k = L.body s k' := by
  have : k = k' := funext fun s' => funext fun hs => h s' hs
  rw [this]

/-- **The measure-based loop**: recursion on a bound for the variant. -/
def runBelow : (n : ℕ) → (s : σ) → L.measure s < n → β :=
  recBelow L.measure (C := fun _ => β) L.body

/-- The measure-based loop at the least sufficient bound. -/
def run (s : σ) : β := recMeasure L.measure (C := fun _ => β) L.body s

theorem run_eq (s : σ) : L.run s = L.body s fun s' _ => L.run s' :=
  recMeasure_eq L.measure (C := fun _ => β) L.body s

theorem run_of_inr {s : σ} {b : β} (h : L.step s = .inr b) : L.run s = b := by
  rw [run_eq, body, h]

theorem run_of_inl {s s' : σ} {hs : L.measure s' < L.measure s}
    (h : L.step s = .inl ⟨s', hs⟩) : L.run s = L.run s' := by
  rw [run_eq, body, h]

/-- **The loop through the accessibility route.** -/
def loopAcc (I : InertRecursor.{u + 1, w + 1} (fun y x => L.measure y < L.measure x)) (s : σ) : β :=
  I.recursor (C := fun _ => β) L.body s (accCode_measure L.measure s)

/-- **Agreement** of the two loops, for every inert recursor. -/
theorem loopAcc_eq_run (I : InertRecursor.{u + 1, w + 1} (fun y x => L.measure y < L.measure x))
    (s : σ) : L.loopAcc I s = L.run s :=
  recursor_eq_recMeasure L.measure I L.body s

/-- **The loop rule.** An invariant kept by every continuing step and turned
into the postcondition by every stopping step gives the postcondition of the
loop's result. -/
theorem run_induction (Inv : σ → Prop) (Post : β → Prop)
    (cont : ∀ s s' hs, Inv s → L.step s = .inl ⟨s', hs⟩ → Inv s')
    (stop : ∀ s b, Inv s → L.step s = .inr b → Post b) : ∀ s, Inv s → Post (L.run s) := by
  suffices h : ∀ n s, L.measure s < n → Inv s → Post (L.run s) from
    fun s => h _ s (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro s hn hs
      rcases e : L.step s with ⟨s', h'⟩ | b
      · rw [L.run_of_inl e]
        exact ih s' (Nat.lt_of_lt_of_le h' (Nat.le_of_lt_succ hn)) (cont s s' h' hs e)
      · rw [L.run_of_inr e]
        exact stop s b hs e

/-- **The loop rule through the accessibility route**, proved from the
propositional unfolding and accessibility induction only. -/
theorem loopAcc_induction (I : InertRecursor.{u + 1, w + 1} (fun y x => L.measure y < L.measure x))
    (Inv : σ → Prop) (Post : β → Prop)
    (cont : ∀ s s' hs, Inv s → L.step s = .inl ⟨s', hs⟩ → Inv s')
    (stop : ∀ s b, Inv s → L.step s = .inr b → Post b) (s : σ) (hs : Inv s) :
    Post (L.loopAcc I s) := by
  unfold loopAcc
  generalize accCode_measure L.measure s = q
  induction acc_of_accCode q with
  | intro x _ ih =>
      rw [I.unfold]
      rcases e : L.step x with ⟨s', h'⟩ | b
      · simp only [body, e]
        exact ih s' h' (cont x s' h' hs e) (q.inv s' h')
      · simp only [body, e]
        exact stop x b hs e

end MeasuredLoop

end Mettapedia.Algorithms.WellFoundedServices
