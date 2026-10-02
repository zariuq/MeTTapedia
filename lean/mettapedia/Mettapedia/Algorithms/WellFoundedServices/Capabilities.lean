import Mettapedia.Algorithms.WellFoundedServices.DependencyExamples
import Mettapedia.Algorithms.WellFoundedServices.ConstraintPlanning
import Mettapedia.TypeTheory.Authority
import Mathlib.Data.Stream.Init

/-!
# Three capabilities: total, productive, budgeted

* **Total well-founded computation.** A measured loop or a recursion on an
  accessible point always returns a decided answer. For the finite constraint
  search the answer is a witness or a checked refutation
  (`Problem.outcome_decided`). A measure is a budget known in advance
  (`MeasuredLoop.runFor_of_measure`).
* **Productive corecursion.** A watcher folds a stream of incoming snapshots
  into a stream of answers (`watch`). Each answer is produced before the rest
  of the stream (`watch_eq`), depends only on the snapshots so far
  (`watch_causal`), and every finite prefix of answers is a finite fold over
  the input prefix (`watch_take`). The rebuild watcher (`rebuildWatch`)
  applies the total dependency services to each snapshot.
* **Budgeted, possibly divergent search.** A machine without a variant runs
  under a budget (`runFor`). Stopping is established; running out of budget is
  incomplete, with the current state as a restartable receipt (`runFor_add`),
  and is never a refutation (`runFor_ne_refuted`); a larger budget refines the
  outcome (`runFor_budgetRefines`). An unbounded search is a semi-decision
  procedure (`Search.established_iff`), and its anytime stream is productive
  and monotone (`Search.anytime_budgetRefines`).

Controls: the self-call machine is incomplete at every budget
(`selfCall_incomplete`); a search with no witness stays incomplete although its
refutation is true (`noSquareTwo_incomplete`); without the accessibility guard
the unfolding equation is inconsistent (`no_unguarded_recursor`), while the
guarded one has a model on the same relation and never applies there
(`guarded_recursor_exists`).
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices

open Mettapedia.Order Mettapedia.TypeTheory.AuthorityTheory

universe u v w x

/-! ## Budgeted runs -/

section Budgeted

variable {σ : Type u} {β : Type v} {R : Sort w}

/-- **Run a machine for at most `k` steps.** -/
def runFor (step : σ → σ ⊕ β) : ℕ → σ → Outcome β R Empty σ
  | 0, s => .incomplete s
  | k + 1, s =>
      match step s with
      | .inl s' => runFor step k s'
      | .inr b => .established b

/-- Continue an incomplete outcome from its receipt. -/
def resume (continue_ : σ → Outcome β R Empty σ) : Outcome β R Empty σ → Outcome β R Empty σ
  | .incomplete s => continue_ s
  | o => o

/-- **Receipts are restartable**: `k + m` steps are `k` steps, then `m` more
from the receipt. -/
theorem runFor_add (step : σ → σ ⊕ β) :
    ∀ (k m : ℕ) (s : σ), (runFor step (k + m) s : Outcome β R Empty σ) =
      resume (runFor step m) (runFor step k s)
  | 0, m, s => by simp [runFor, resume]
  | k + 1, m, s => by
      rw [Nat.add_right_comm]
      simp only [runFor]
      cases step s with
      | inl s' => exact runFor_add step k m s'
      | inr b => rfl

/-- **Running out of budget is never a refutation.** -/
theorem runFor_ne_refuted (step : σ → σ ⊕ β) :
    ∀ (k : ℕ) (s : σ) (r : R), (runFor step k s : Outcome β R Empty σ) ≠ .refuted r
  | 0, _, _ => by simp [runFor]
  | k + 1, s, r => by
      simp only [runFor]
      cases step s with
      | inl s' => exact runFor_ne_refuted step k s' r
      | inr b => simp

/-- **A larger budget refines the outcome.** -/
theorem runFor_budgetRefines (step : σ → σ ⊕ β) (k m : ℕ) (s : σ) :
    Outcome.BudgetRefines (runFor step k s : Outcome β R Empty σ) (runFor step (k + m) s) := by
  rw [runFor_add]
  cases h : (runFor step k s : Outcome β R Empty σ) with
  | established b => exact .established b b
  | refuted r => exact absurd h (runFor_ne_refuted step k s r)
  | outsideFragment e => exact e.elim
  | incomplete s' =>
      simp only [resume]
      cases h' : (runFor step m s' : Outcome β R Empty σ) with
      | established b => exact .incompleteEstablished s' b
      | refuted r => exact absurd h' (runFor_ne_refuted step m s' r)
      | outsideFragment e => exact e.elim
      | incomplete s'' => exact .incomplete s' s''

/-- A measured loop, forgetting the variant. -/
def MeasuredLoop.machine (L : MeasuredLoop σ β) (s : σ) : σ ⊕ β :=
  (L.step s).map Subtype.val id

/-- **A measure is a budget known in advance**: with more steps than the
measure, the budgeted run of a measured loop is its total run. -/
theorem MeasuredLoop.runFor_of_measure (L : MeasuredLoop σ β) :
    ∀ (k : ℕ) (s : σ), L.measure s < k →
      (runFor L.machine k s : Outcome β R Empty σ) = .established (L.run s)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, s, h => by
      simp only [runFor, machine]
      rcases e : L.step s with ⟨s', hs⟩ | b
      · simp only [Sum.map_inl]
        rw [L.run_of_inl e]
        exact L.runFor_of_measure k s' (Nat.lt_of_lt_of_le hs (Nat.le_of_lt_succ h))
      · simp only [Sum.map_inr, id]
        rw [L.run_of_inr e]

end Budgeted

/-! ## Unbounded search -/

/-- A search: candidates enumerated by the natural numbers and a test. -/
structure Search (α : Type u) where
  candidate : ℕ → α
  accept : α → Bool

namespace Search

variable {α : Type u} (S : Search α)

/-- A witness: an index whose candidate passes. -/
abbrev Witness : Type := {n : ℕ // S.accept (S.candidate n) = true}

/-- A refutation: no candidate passes. -/
def Refutation : Prop := ∀ n, S.accept (S.candidate n) = false

/-- Test the next candidate. -/
def step (n : ℕ) : ℕ ⊕ S.Witness :=
  if h : S.accept (S.candidate n) = true then .inr ⟨n, h⟩ else .inl (n + 1)

/-- **Budgeted search** from the first candidate. -/
def run (budget : ℕ) : Outcome S.Witness S.Refutation Empty ℕ := runFor S.step budget 0

theorem runFor_step_incomplete :
    ∀ (k n m : ℕ), (runFor S.step k n : Outcome S.Witness S.Refutation Empty ℕ) = .incomplete m →
      m = n + k ∧ ∀ i, n ≤ i → i < n + k → S.accept (S.candidate i) = false
  | 0, n, m, h => by
      simp only [runFor, Outcome.incomplete.injEq] at h
      exact ⟨h.symm, fun i h₁ h₂ => absurd h₂ (by omega)⟩
  | k + 1, n, m, h => by
      simp only [runFor, step] at h
      by_cases ha : S.accept (S.candidate n) = true
      · rw [dif_pos ha] at h; cases h
      · rw [dif_neg ha] at h
        obtain ⟨hm, hi⟩ := runFor_step_incomplete k (n + 1) m h
        refine ⟨by omega, fun i h₁ h₂ => ?_⟩
        rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
        · simpa using ha
        · exact hi i h₁ (by omega)

/-- The receipt of an incomplete search: every candidate below the budget was
tested and failed. -/
theorem run_incomplete {k m : ℕ} (h : S.run k = .incomplete m) :
    m = k ∧ ∀ i < k, S.accept (S.candidate i) = false := by
  obtain ⟨hm, hi⟩ := S.runFor_step_incomplete k 0 m h
  exact ⟨by omega, fun i hk => hi i (Nat.zero_le _) (by omega)⟩

theorem run_ne_refuted (k : ℕ) (r : S.Refutation) : S.run k ≠ .refuted r :=
  runFor_ne_refuted S.step k 0 r

theorem run_budgetRefines (k m : ℕ) : Outcome.BudgetRefines (S.run k) (S.run (k + m)) :=
  runFor_budgetRefines S.step k m 0

theorem runFor_step_of_accept :
    ∀ (k n : ℕ) (i : ℕ), n ≤ i → i < n + k → S.accept (S.candidate i) = true →
      ∃ w, (runFor S.step k n : Outcome S.Witness S.Refutation Empty ℕ) = .established w
  | 0, n, i, h₁, h₂, _ => absurd h₂ (by omega)
  | k + 1, n, i, h₁, h₂, hi => by
      simp only [runFor, step]
      by_cases ha : S.accept (S.candidate n) = true
      · rw [dif_pos ha]
        exact ⟨_, rfl⟩
      · rw [dif_neg ha]
        rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
        · exact absurd hi ha
        · exact runFor_step_of_accept k (n + 1) i h₁ (by omega) hi

/-- **Semi-decision**: some budget establishes a witness exactly when a
candidate passes. -/
theorem established_iff : (∃ k w, S.run k = .established w) ↔ ∃ n, S.accept (S.candidate n) = true := by
  constructor
  · rintro ⟨k, w, -⟩
    exact ⟨w.1, w.2⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, S.runFor_step_of_accept (n + 1) 0 n (Nat.zero_le _) (by omega) hn⟩

/-- **The anytime stream**: the outcome at every budget. -/
def anytime : Stream' (Outcome S.Witness S.Refutation Empty ℕ) := fun k => S.run k

theorem anytime_budgetRefines (k : ℕ) :
    Outcome.BudgetRefines (S.anytime.get k) (S.anytime.get (k + 1)) :=
  S.run_budgetRefines k 1

end Search

/-! ## Controls for divergence -/

/-- The self-call: each state continues with itself. -/
def selfCall {σ : Type u} {β : Type v} (s : σ) : σ ⊕ β := .inl s

/-- **The self-call never stops and never refutes.** -/
theorem selfCall_incomplete {σ : Type u} {β : Type v} {R : Sort w} :
    ∀ (k : ℕ) (s : σ), (runFor (selfCall (β := β)) k s : Outcome β R Empty σ) = .incomplete s
  | 0, _ => rfl
  | k + 1, s => selfCall_incomplete k s

/-- A search with no witness: a natural number whose square is two. -/
def noSquareTwo : Search ℕ := ⟨id, fun n => n * n == 2⟩

/-- Its refutation is true. -/
theorem noSquareTwo_refutation : noSquareTwo.Refutation := by
  intro n
  simp only [noSquareTwo, id, beq_eq_false_iff_ne]
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp at h
  · have : 2 * 2 ≤ n * n := Nat.mul_le_mul hn hn
    rw [h] at this
    exact absurd this (by decide)

/-- **Exhaustion is incomplete, never refuted**: at every budget, although the
refutation is true. -/
theorem noSquareTwo_incomplete (k : ℕ) : noSquareTwo.run k = .incomplete k := by
  cases h : noSquareTwo.run k with
  | established w => exact absurd w.2 (by rw [noSquareTwo_refutation w.1]; simp)
  | refuted r => exact absurd h (noSquareTwo.run_ne_refuted k r)
  | outsideFragment e => exact e.elim
  | incomplete m => rw [(noSquareTwo.run_incomplete h).1]

/-- A search whose first witness lies beyond small budgets: a proof-of-work
style test. -/
def puzzle : Search ℕ := ⟨id, fun n => (n * 2654435761 + 12345) % 1000 < 4⟩

example : (puzzle.run 100).publicStatus = .incomplete := by decide
example : (puzzle.run 2000).publicStatus = .established := by decide

/-- **Without the guard, the unfolding is inconsistent**: no recursor on the
self-call relation satisfies the unguarded unfolding equation. -/
theorem no_unguarded_recursor {α : Sort u} (a : α) :
    ¬ ∃ rec : ((x : α) → ((y : α) → y = x → Bool) → Bool) → α → Bool,
      ∀ F x, rec F x = F x fun y _ => rec F y := by
  rintro ⟨rec, h⟩
  have e := h (fun x k => !(k x rfl)) a
  cases hb : rec (fun x k => !(k x rfl)) a <;> simp [hb] at e

/-- **With the guard, the unfolding has a model**, and on the self-call
relation it never applies: no point is accessible. -/
theorem guarded_recursor_exists {α : Sort u} :
    Nonempty (InertRecursor.{u, 1} fun (y x : α) => y = x) ∧ ∀ a : α, ¬ AccCode (fun y x : α => y = x) a :=
  ⟨⟨InertRecursor.ofAcc _⟩, fun _ => not_accCode_of_refl rfl⟩

/-! ## Total services, as outcomes -/

namespace Problem

variable {V : Type u} {D : Type v} [DecidableEq V] (P : Problem V D) (σ : Strategy V D)

/-- The outcome of the total search: a witness or a checked refutation. It has
no incomplete case. -/
def outcome (hW : P.WellFormed) :
    Outcome {f : Assignment V D // P.Solution f} {r : Refutation V // P.check [] r = true} Empty Empty :=
  match h : P.solve σ with
  | .inl f => .established ⟨f, P.solve_inl σ hW h⟩
  | .inr r => .refuted ⟨r, (P.solve_inr σ h).1⟩

theorem outcome_decided (hW : P.WellFormed) : (P.outcome σ hW).isDecided = true := by
  unfold outcome
  split <;> rfl

end Problem

/-! ## Productive watchers -/

section Watch

variable {σ : Type u} {ι : Type v} {ο : Type w}

/-- **A watcher**: fold a stream of inputs into a stream of outputs through a
state machine with output. -/
def watch (step : σ → ι → σ × ο) (s : σ) (xs : Stream' ι) : Stream' ο :=
  Stream'.corec (fun p : σ × Stream' ι => (step p.1 p.2.head).2)
    (fun p => ((step p.1 p.2.head).1, p.2.tail)) (s, xs)

/-- The outputs for a finite list of inputs. -/
def outputs (step : σ → ι → σ × ο) : σ → List ι → List ο
  | _, [] => []
  | s, x :: xs => (step s x).2 :: outputs step (step s x).1 xs

/-- **Guardedness**: the first output is produced before the rest of the
stream. -/
theorem watch_eq (step : σ → ι → σ × ο) (s : σ) (xs : Stream' ι) :
    watch step s xs = Stream'.cons (step s xs.head).2 (watch step (step s xs.head).1 xs.tail) := by
  unfold watch
  rw [Stream'.corec_eq]

/-- **Productivity**: every finite prefix of outputs is a finite fold over the
input prefix. -/
theorem watch_take (step : σ → ι → σ × ο) :
    ∀ (n : ℕ) (s : σ) (xs : Stream' ι), (watch step s xs).take n = outputs step s (xs.take n)
  | 0, _, _ => rfl
  | n + 1, s, xs => by
      rw [Stream'.take_succ, Stream'.take_succ, watch_eq, Stream'.head_cons, Stream'.tail_cons,
        outputs, watch_take step n]

/-- **Causality**: outputs so far depend only on inputs so far. -/
theorem watch_causal (step : σ → ι → σ × ο) (s : σ) {xs ys : Stream' ι} (n : ℕ)
    (h : xs.take n = ys.take n) : (watch step s xs).take n = (watch step s ys).take n := by
  rw [watch_take, watch_take, h]

end Watch

/-! ## The rebuild watcher -/

namespace Catalogue

variable {α : Type u} [DecidableEq α]

/-- Items of the new snapshot that are new or whose dependencies changed. -/
def changedFrom (old new : Catalogue α) : List α :=
  new.items.filter fun x => decide (x ∉ old.items ∨ old.deps x ≠ new.deps x)

/-- One round of watching: remember the snapshot, and schedule the rebuild of
everything the change affects. -/
def rebuildStep (old new : Catalogue α) : Catalogue α × Schedule α :=
  (new, new.schedule (new.affected (changedFrom old new)))

/-- **The rebuild watcher** over a stream of catalogue snapshots. -/
def rebuildWatch (start : Catalogue α) (snapshots : Stream' (Catalogue α)) : Stream' (Schedule α) :=
  watch rebuildStep start snapshots

/-- The previous snapshot of round `n`. -/
def previous (start : Catalogue α) (snapshots : Stream' (Catalogue α)) : ℕ → Catalogue α
  | 0 => start
  | n + 1 => snapshots.get n

omit [DecidableEq α] in
theorem previous_tail (snapshots : Stream' (Catalogue α)) (n : ℕ) :
    previous snapshots.head snapshots.tail n = snapshots.get n := by
  cases n <;> rfl

theorem rebuildWatch_get (start : Catalogue α) (snapshots : Stream' (Catalogue α)) (n : ℕ) :
    (rebuildWatch start snapshots).get n =
      (snapshots.get n).schedule ((snapshots.get n).affected
        (changedFrom (previous start snapshots n) (snapshots.get n))) := by
  induction n generalizing start snapshots with
  | zero =>
      rw [rebuildWatch, watch_eq]
      rfl
  | succ n ih =>
      rw [rebuildWatch, watch_eq, Stream'.get_succ, Stream'.tail_cons]
      have := ih snapshots.head snapshots.tail
      rw [previous_tail] at this
      exact this

/-- **Each round's plan is correct**: it schedules exactly the items that
depend on a change of that round, or reports a blocked set among them. -/
theorem rebuildWatch_spec (start : Catalogue α) (snapshots : Stream' (Catalogue α)) (n : ℕ) :
    let new := snapshots.get n
    new.ScheduleSpec (new.affected (changedFrom (previous start snapshots n) new))
      ((rebuildWatch start snapshots).get n) := by
  intro new
  rw [rebuildWatch_get]
  exact new.schedule_spec _

end Catalogue

/-! ## A watched catalogue -/

namespace DependencyExamples

open Pkg

/-- Snapshots: the catalogue, then the cyclic variant, then the catalogue
again, forever. -/
def snapshots : Stream' (Catalogue Pkg) := fun n =>
  if n % 3 = 1 then cyclic else packages

example : (Catalogue.rebuildWatch packages snapshots).take 4 =
    [.waves [], .blocked [cli, app], .waves [[cli], [app]], .waves []] := by
  decide

end DependencyExamples

end Mettapedia.Algorithms.WellFoundedServices
