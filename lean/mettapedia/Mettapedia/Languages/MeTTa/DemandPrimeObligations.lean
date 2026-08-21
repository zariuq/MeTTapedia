import Mettapedia.Languages.MeTTa.DemandSemantics

/-!
# Prime obligation canaries on demand semantics (T1-beta-b, canary layer)

This module is a **canary layer**, not a model of the production Prime
machine.  The obligation-flavored statements here are precise shadows of the
real properties, stated as far as the small calculi can carry them; the real
properties require a heap machine with cell states, branch identities,
revisions, and quote barriers (tracked as the next layer: T1-gamma).

**Non-claims (read before citing):**

* **Fuel is maximum recursion depth, not total work.**  In `evalF`/`evalAll`
  sibling sub-demands each receive the *full remaining* budget rather than
  consuming from one shared account.  This matches depth-style recursive
  fuel; it is not an instruction or resource budget.
* **`evalAll` is bag/list-valued, not set-valued.**  Occurrence order and
  multiplicity are preserved on purpose (that is the MeTTa reading of
  superposition).
* **`collapse` is a readout discipline, not the semantics.**  It erases the
  distinction between "no answer", "stuck", and "insufficient resources" at
  its output boundary; those distinctions survive in the outcome list itself,
  and `collapseChecked` below keeps them observable at the readout.
* **No changing space, no heap, no fairness.**  Nothing here models revision
  tokens, memoization, forced-once evaluation, black-hole behavior, or
  branch-local choice.  Where an obligation needs those, the canary states
  the shadow it can state and says so in its docstring.

Obligations, named and placed:

* **revision pinning (canary)** — an observed value is pinned against any later
  budget (`fuel_done_persistent`); two budgets observing the same compute
  agree (`reevaluation_consistent`);
* **sharing consistency (canary)** — re-evaluation of one immutable cell
  yields one value (`reevaluation_consistent_shared`, over a tiny `CellStore`
  model; this is NOT a heap/forced-once theorem);
* **stream pointwise-doneness (canary)** — every cell of a static stream
  eventually yields under some budget (`PointwiseDone`); proved for a
  constructor stream at *uniform* fuel, refuted for a stream hitting `stuck`;
  NOT a fair-production statement about an operational machine;
* **quote as anti-demand** — `quote t` halts demand unconditionally; the
  contents are shielded even when they contain redexes, and quotation is
  opaque to deconstructors;
* **per-occurrence superpose/collapse** — `evalAll` distributes demand over
  superposed branches occurrence-by-occurrence; collapsing the outcome bag
  satisfies the distribution law `collapse (superpose a b) = collapse a ∔
  collapse b` (`collapse_app`, `superpose_collapse_distribution`).

Every theorem is followed by `#print axioms`; examples are kernel-checked.
Proof-technique notes from the beta-a ladder (scrutinee-substitution traps,
IH fixation under nested case-splits, single-step-then-`≤`-induction for
fuel monotonicity) are recorded in the sibling module's docstrings.
-/

namespace Mettapedia.Languages.MeTTa.DemandPrimeObligations

open Mettapedia.Languages.MeTTa.DemandSemantics

/-! ## Revision pinning and sharing consistency (re-readings of beta-a) -/

/-- **Revision pinning (obligation).**  Once a value is observed under some
budget, revisiting the same compute with any larger budget yields the same
value: observation pins revision. -/
theorem fuel_done_persistent {n : Nat} {t v : Term} (h : evalF n t = .done v)
    (m : Nat) (hnm : n ≤ m) : evalF m t = .done v :=
  evalF_mono hnm h

/-- **Revision coherence (obligation).**  Any two budgets that both report a
value for the same compute report the same value. -/
theorem reevaluation_consistent {n m : Nat} {t v w : Term}
    (hn : evalF n t = .done v) (hm : evalF m t = .done w) : v = w :=
  evalF_unique hn hm

/-- A tiny shared cell store: cells map indices to terms (which may contain
redexes).  Demanding a cell is demanding its stored term; a shared cell is
one demanded through several reads. -/
structure CellStore where
  cell : Nat → Term

/-- Demanding cell `i` of the store under budget `n`. -/
def demandCell (n : Nat) (cs : CellStore) (i : Nat) : Outcome :=
  evalF n (cs.cell i)

/-- **Sharing consistency (obligation).**  Two reads of the same shared cell,
under possibly different budgets, can only differ by how much fuel they
needed — never by what value they saw. -/
theorem reevaluation_consistent_shared {n m : Nat} {cs : CellStore} {i : Nat}
    {v w : Term} (hn : demandCell n cs i = .done v)
    (hm : demandCell m cs i = .done w) : v = w :=
  evalF_unique hn hm

/-- Example cell store: cell 0 holds the CP2 redex-under-pair term, cell 1 a
plain datum. -/
def csExample : CellStore where
  cell
    | 0 => .rcar (.pair (.add (.num 1) (.num 1)) (.num 9))
    | _ => .num 7

example : demandCell 2 csExample 0 = .outOfFuel := rfl
example : demandCell 3 csExample 0 = .done (.num 2) := rfl
example : demandCell 1 csExample 1 = .done (.num 7) := rfl

/-! ## Stream productivity -/

/-- A demand stream: one term per tick. -/
abbrev TermStream : Type := Nat → Term

/-- A stream is *pointwise-done* when every cell eventually yields a value
under some (cell-dependent) budget.  No uniform bound is required.  This is a
property of the static mathematical stream, NOT a fair-production statement
about an operational machine. -/
def PointwiseDone (s : TermStream) : Prop :=
  ∀ k, ∃ n v, evalF n (s k) = .done v

/-- **Pointwise-doneness, positive canary.**  The uniform
constructor stream is pointwise-done at *uniform* budget 1: data halts. -/
theorem pairStream_pointwiseDone :
    PointwiseDone fun k => .pair (.num k) (.num k) := fun k =>
  ⟨1, .pair (.num k) (.num k), rfl⟩

/-- A stream of bare deconstructor applications is never productive: `stuck`
is not exhaustion and no budget cures it. -/
theorem rcarNum_stuck_at_any_fuel (k : Nat) :
    ∀ n v, evalF n (.rcar (.num k)) ≠ .done v := by
  intro n
  induction n with
  | zero => intro v h; simp [evalF] at h
  | succ f _ =>
      intro v h
      cases f with
      | zero => simp [evalF] at h
      | succ f' => simp [evalF] at h

/-- **Pointwise-doneness, negative canary.**  Stuckness in a
stream is a permanent verdict, not a budget-report: the rcar-of-number
stream is not pointwise-done. -/
theorem rcarNumStream_not_pointwiseDone :
    ¬ PointwiseDone fun k => .rcar (.num k) := by
  intro h
  obtain ⟨n, v, hv⟩ := h 0
  exact rcarNum_stuck_at_any_fuel 0 n v hv

/-! ## Quotation and superposition: the extended language -/

/-- The T1 term language extended with anti-demand **quotation** (quote
shields its contents from demand) and **superposition** (a nondeterministic
branch: each side is demanded occurrence-by-occurrence). -/
inductive PTerm where
  | num : Nat → PTerm
  | pair : PTerm → PTerm → PTerm
  | quote : PTerm → PTerm
  | add : PTerm → PTerm → PTerm
  | rcar : PTerm → PTerm
  | rcdr : PTerm → PTerm
  | choice : PTerm → PTerm → PTerm
  deriving Repr, DecidableEq

/-- Outcomes of a *single* per-occurrence demand: a value, genuine
stuckness, or a budget report.  A superposed demand yields a list of these —
one per branch-occurrence. -/
inductive POutcome where
  | done : PTerm → POutcome
  | stuck : POutcome
  | outOfFuel : POutcome
  deriving Repr, DecidableEq

/-- The set-valued fuel-indexed demand evaluator.  Superposition
concatenates branch demand-sets; every other position demands its
sub-demands **per occurrence**: a collection argument yields one demand-set
per element, and position-wise combination is comprehension over outcomes.
Stuckness and exhaustion are preserved, not collapsed. -/
def evalAll : Nat → PTerm → List POutcome
  | 0, _ => [.outOfFuel]
  | _+1, .num n => [.done (.num n)]
  | _+1, .pair a b => [.done (.pair a b)]
  | _+1, .quote t => [.done (.quote t)]
  | f+1, .choice a b => evalAll f a ++ evalAll f b
  | f+1, .add a b =>
      (evalAll f a).flatMap fun
        | .done (.num x) =>
            (evalAll f b).flatMap fun
              | .done (.num y) => [.done (.num (x + y))]
              | .outOfFuel => [.outOfFuel]
              | _ => [.stuck]
        | .outOfFuel => [.outOfFuel]
        | _ => [.stuck]
  | f+1, .rcar t =>
      (evalAll f t).flatMap fun
        | .done (.pair a _) => evalAll f a
        | .outOfFuel => [.outOfFuel]
        | _ => [.stuck]
  | f+1, .rcdr t =>
      (evalAll f t).flatMap fun
        | .done (.pair _ b) => evalAll f b
        | .outOfFuel => [.outOfFuel]
        | _ => [.stuck]

/-- **Collapsing** an outcome set: keep exactly the produced values.
Budget reports and stuckness are observations, not values, and are dropped
here by definition — but they are still present in the outcome list itself;
collapse never erases evidence of them anywhere but its own result list. -/
def collapse : List POutcome → List PTerm
  | [] => []
  | (.done t) :: os => t :: collapse os
  | (POutcome.stuck) :: os => collapse os
  | POutcome.outOfFuel :: os => collapse os

/-- **Status-preserving readout.**  The checked readout produces a plain
value bag only when *every* outcome was `done`; otherwise the first
offending status (`stuck` or `outOfFuel`) is returned, so "no values",
"genuine stuckness", and "insufficient budget" stay distinguishable at the
readout boundary.  `collapse` remains the readout that discards; this one
refuses to. -/
def collapseChecked : List POutcome → Except POutcome (List PTerm)
  | [] => .ok []
  | POutcome.done t :: os =>
      match collapseChecked os with
      | .ok ts => .ok (t :: ts)
      | e => e
  | POutcome.stuck :: _ => .error POutcome.stuck
  | POutcome.outOfFuel :: _ => .error POutcome.outOfFuel

/-- Soundness of the checked readout against the plain collapse: whenever
every outcome in the bag is `done`, checked and plain readouts agree. -/
theorem collapseChecked_allDone (l : List POutcome)
    (h : ∀ o ∈ l, ∃ t, o = .done t) :
    collapseChecked l = .ok (collapse l) := by
  induction l with
  | nil => simp [collapseChecked, collapse]
  | cons o os ih =>
      obtain ⟨t, rfl⟩ := h o List.mem_cons_self
      have ih' := ih (fun x hx => h x (List.mem_cons.mpr (.inr hx)))
      simp [collapse, collapseChecked, ih']

/-- Completeness of the readout boundary: a checked success is exactly the
plain collapse's value bag. -/
theorem collapseChecked_ok_collapse (l : List POutcome) (ts : List PTerm)
    (h : collapseChecked l = .ok ts) : collapse l = ts := by
  induction l generalizing ts with
  | nil =>
      cases h
      rfl
  | cons o os ih =>
      cases o with
      | done t =>
          simp only [collapseChecked] at h
          cases hc : collapseChecked os with
          | ok ts' =>
              rw [hc] at h
              cases h
              simp [collapse, ih ts' hc]
          | error e =>
              rw [hc] at h
              cases h
      | stuck => simp [collapseChecked] at h
      | outOfFuel => simp [collapseChecked] at h

-- First-bad-status propagation, kernel-checked:
example : collapseChecked [.done (.num 1), .done (.num 3)] =
    .ok [.num 1, .num 3] := rfl
example : collapseChecked [.done (.num 1), .stuck] = .error .stuck := rfl
example : collapseChecked [.outOfFuel, .done (.num 3)] =
    .error .outOfFuel := rfl

/-! ### Quote as anti-demand -/

/-- **Quote halts demand (obligation).**  Under any nonempty budget, a
quoted term evaluates to itself; the contents are never inspected. -/
theorem quote_halts (t : PTerm) (f : Nat) :
    evalAll (f + 1) (.quote t) = [.done (.quote t)] := by
  simp [evalAll]

-- Quote shields redex-bearing, superposed, *and* stuck contents:
-- nothing under a quote is ever demanded.
example : evalAll 2 (.quote (.add (.num 1) (.num 1))) =
    [.done (.quote (.add (.num 1) (.num 1)))] := rfl

example : evalAll 1 (.quote (.choice (.rcar (.num 1)) (.num 2))) =
    [.done (.quote (.choice (.rcar (.num 1)) (.num 2)))] := rfl

-- Negative: quotation is opaque to deconstructors — a quoted pair cannot be
-- penetrated by `rcar`; the verdict is `stuck`, not a budget matter.
example : evalAll 2 (.rcar (.quote (.pair (.num 1) (.num 2)))) = [.stuck] :=
  rfl

/-! ### Superpose/collapse: per-occurrence demand -/

-- The CP2 redex under a superposed choice: each occurrence is demanded
-- separately, branch outcomes concatenated in branch order.
example :
    evalAll 3 (.rcar (.choice (.pair (.num 1) (.num 9))
                              (.pair (.num 3) (.num 4)))) =
      [.done (.num 1), .done (.num 3)] := rfl

-- Arithmetic over a superposed argument: comprehension over outcomes.
example :
    evalAll 3 (.add (.choice (.num 1) (.num 2)) (.num 5)) =
      [.done (.num 6), .done (.num 7)] := rfl

-- Branch-local statuses survive side by side: one branch out of fuel, one
-- done — the outcome list keeps both, in order.
example :
    evalAll 2 (.choice (.rcar (.pair (.num 1) (.num 2))) (.num 3)) =
      [.outOfFuel, .done (.num 3)] := rfl

/-- Collapse commutes with concatenation: collecting values over a joined
outcome set is joining the two collections. -/
theorem collapse_app (l₁ l₂ : List POutcome) :
    collapse (l₁ ++ l₂) = collapse l₁ ++ collapse l₂ := by
  induction l₁ with
  | nil => rfl
  | cons o os ih =>
      cases o with
      | done t => simp [collapse, ih]
      | stuck => simp [collapse, ih]
      | outOfFuel => simp [collapse, ih]

/-- **Superpose/collapse distribution (obligation).**  Collapsing the demand
of a superposition is the concatenation of the collapsed branches: each
superposed occurrence is demanded, and collected, individually. -/
theorem superpose_collapse_distribution (f : Nat) (a b : PTerm) :
    collapse (evalAll (f + 1) (.choice a b)) =
      collapse (evalAll f a) ++ collapse (evalAll f b) := by
  show collapse (evalAll f a ++ evalAll f b) = _
  exact collapse_app _ _

-- Worked instance: the per-occurrence rcar example collapses to the two
-- branch values in order.
example :
    collapse (evalAll 3 (.rcar (.choice (.pair (.num 1) (.num 9))
                                        (.pair (.num 3) (.num 4))))) =
      [.num 1, .num 3] := rfl

-- Collapsing the mixed-status superpose yields the done branch only; the
-- budget report was evidence, not a value.
example :
    collapse (evalAll 2 (.choice (.rcar (.pair (.num 1) (.num 2)))
                                 (.num 3))) = [.num 3] := rfl

/-! ## Axiom audits -/

#print axioms fuel_done_persistent
#print axioms reevaluation_consistent
#print axioms reevaluation_consistent_shared
#print axioms pairStream_pointwiseDone
#print axioms rcarNum_stuck_at_any_fuel
#print axioms rcarNumStream_not_pointwiseDone
#print axioms quote_halts
#print axioms collapseChecked_allDone
#print axioms collapseChecked_ok_collapse
#print axioms collapse_app
#print axioms superpose_collapse_distribution

end Mettapedia.Languages.MeTTa.DemandPrimeObligations