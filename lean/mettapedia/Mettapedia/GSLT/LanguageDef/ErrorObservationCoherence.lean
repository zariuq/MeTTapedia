import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic

/-!
# Error observation coherence: which error policies can make sense together

Outcomes of a nondeterministic evaluation form a bag of successes and
errors.  This module studies three concrete observation policies: retain
both tagged channels, project the value channel, or require an error-free
bag at a declared boundary.

These policies are motivated by angelic, demonic, and convex powerdomain
semantics, but the carrier below is only an ordered list of tagged outcomes.
No semantic preorder or Hoare/Smyth/Plotkin closure is defined here, so this
module does not identify the list model with any classical powerdomain.

This module weaves the web of what coheres:

* `hasValue_append` / `errorFree_append` — the two Boolean observations are
  `∨`/`∧` homomorphisms out of bag append.
* `successes_bind` and `valueProjection_bind_safe` — for the particular
  error-propagating bind defined below, filtering errors before one bind does
  not change the final value channel.
* `errorFree_gate_not_boundary_invariant` — an all-or-nothing error-free gate
  applied before versus after a continuation can give different results, so
  its boundary is part of the policy.
* `split_join_perm` — the two-channel split (values, errors) loses
  nothing: rejoining is a permutation of the original bag.  This is the
  algebraic license for the `observe-errors` handler: observation is
  partition, not mutation.
* `evalEager_eq_of_deadFailFree` and `eager_demand_disagree_example` — a
  dead-error-free condition is sufficient for eager and demand evaluation to
  agree, while one dead error site witnesses that they can differ.

Together, the tagged bag plus its explicit sequencing operation supports a
lossless two-channel observation, a value projection with a proved local
fusion law, and boundary-scoped error-free transactions.  The treatment of
dead error sites remains a separate semantic choice.
-/

namespace Mettapedia.GSLT.LanguageDef.ErrorObservationCoherence

variable {V E W : Type*}

/-- One branch outcome: a success value or an error datum. -/
inductive Res (V E : Type*) where
  | val (v : V)
  | err (e : E)
deriving DecidableEq

/-- A nondeterministic outcome bag. -/
abbrev Bag (V E : Type*) := List (Res V E)

/-- The success channel. -/
def successes (b : Bag V E) : List V :=
  b.filterMap fun r => match r with
    | .val v => some v
    | .err _ => none

/-- The error channel. -/
def errorsOf (b : Bag V E) : List E :=
  b.filterMap fun r => match r with
    | .val _ => none
    | .err e => some e

@[simp] theorem successes_nil : successes ([] : Bag V E) = [] := rfl

@[simp] theorem successes_cons_val (v : V) (b : Bag V E) :
    successes (.val v :: b) = v :: successes b := rfl

@[simp] theorem successes_cons_err (e : E) (b : Bag V E) :
    successes (.err e :: b) = successes b := rfl

@[simp] theorem errorsOf_nil : errorsOf ([] : Bag V E) = [] := rfl

@[simp] theorem errorsOf_cons_val (v : V) (b : Bag V E) :
    errorsOf (.val v :: b) = errorsOf b := rfl

@[simp] theorem errorsOf_cons_err (e : E) (b : Bag V E) :
    errorsOf (.err e :: b) = e :: errorsOf b := rfl

theorem successes_append (a b : Bag V E) :
    successes (a ++ b) = successes a ++ successes b := by
  induction a with
  | nil => simp
  | cons r t ih => cases r <;> simp [ih]

theorem errorsOf_append (a b : Bag V E) :
    errorsOf (a ++ b) = errorsOf a ++ errorsOf b := by
  induction a with
  | nil => simp
  | cons r t ih => cases r <;> simp [ih]

/-! ## Two Boolean observations of bag append -/

/-- At least one branch produced a value. -/
def hasValue (b : Bag V E) : Prop := successes b ≠ []

/-- No branch produced an explicit error.  This is vacuously true of an empty
bag; it does not assert that a value exists. -/
def errorFree (b : Bag V E) : Prop := errorsOf b = []

/-- `hasValue` is the `∨`-homomorphism out of bag append. -/
theorem hasValue_append (a b : Bag V E) :
    hasValue (a ++ b) ↔ hasValue a ∨ hasValue b := by
  unfold hasValue
  rw [successes_append]
  constructor
  · intro h
    by_cases ha : successes a = []
    · right
      intro hb
      exact h (by rw [ha, hb]; rfl)
    · exact Or.inl ha
  · intro h hab
    rcases List.append_eq_nil_iff.mp hab with ⟨ha, hb⟩
    rcases h with h | h
    · exact h ha
    · exact h hb

/-- `errorFree` is the `∧`-homomorphism out of bag append. -/
theorem errorFree_append (a b : Bag V E) :
    errorFree (a ++ b) ↔ errorFree a ∧ errorFree b := by
  unfold errorFree
  rw [errorsOf_append, List.append_eq_nil_iff]

/-! ## Error-strict sequencing and the angelic projection -/

/-- Error-strict sequencing: continue on values, pass errors through. -/
def bindBag (b : Bag V E) (k : V → Bag W E) : Bag W E :=
  b.flatMap fun r => match r with
    | .val v => k v
    | .err e => [.err e]

@[simp] theorem bindBag_nil (k : V → Bag W E) :
    bindBag ([] : Bag V E) k = [] := rfl

theorem bindBag_cons_val (v : V) (t : Bag V E) (k : V → Bag W E) :
    bindBag (.val v :: t) k = k v ++ bindBag t k := rfl

theorem bindBag_cons_err (e : E) (t : Bag V E) (k : V → Bag W E) :
    bindBag (.err e :: t) k = .err e :: bindBag t k := rfl

/-- Keep only the success branches (as a bag). -/
def keepVals (b : Bag V E) : Bag V E :=
  (successes b).map .val

/-- The successes of a sequenced computation come only from the successes
of its first stage. -/
theorem successes_bind (b : Bag V E) (k : V → Bag W E) :
    successes (bindBag b k) =
      (successes b).flatMap fun v => successes (k v) := by
  induction b with
  | nil => rfl
  | cons r t ih =>
    cases r with
    | val v =>
      rw [bindBag_cons_val, successes_append, successes_cons_val,
        List.flatMap_cons, ih]
    | err e =>
      rw [bindBag_cons_err, successes_cons_err, successes_cons_err, ih]

/-- For `bindBag`, projecting to values before one sequencing boundary does
not change the final value channel. -/
theorem valueProjection_bind_safe (b : Bag V E) (k : V → Bag W E) :
    successes (bindBag (keepVals b) k) = successes (bindBag b k) := by
  rw [successes_bind, successes_bind]
  congr 1
  unfold keepVals
  induction successes b with
  | nil => rfl
  | cons v t ih => simp [ih]

/-- Transactional gating: pass the bag only if it is error-free. -/
def errorFreeGate (b : Bag V E) : Bag V E :=
  if errorsOf b = [] then b else []

/-- Error-free gating is not boundary-invariant: gating before versus after a
continuation gives different results.  A clean first stage whose continuation
errors is a witness. -/
theorem errorFree_gate_not_boundary_invariant :
    ∃ (b : Bag Nat Nat) (k : Nat → Bag Nat Nat),
      bindBag (errorFreeGate b) k ≠ errorFreeGate (bindBag b k) := by
  refine ⟨[.val 1], fun _ => [.err 0], ?_⟩
  decide

/-! ## Lossless two-channel observation -/

/-- Rejoining the two channels is a permutation of the original bag: the
`observe-errors` split loses nothing and reorders only. -/
theorem split_join_perm (b : Bag V E) :
    List.Perm ((successes b).map .val ++ (errorsOf b).map .err) b := by
  induction b with
  | nil => simp
  | cons r t ih =>
    cases r with
    | val v =>
      simpa using ih.cons (Res.val v)
    | err e =>
      refine List.Perm.trans ?_ (ih.cons (Res.err e))
      simp

/-! ## Eager versus demand error strictness: the genuine fork

A minimal sequencing language isolates the one place the strictness
policies disagree: *dead* error sites — computations that are constructed
and discarded without demand. -/

/-- Expressions: a value, an error, sequencing that discards the first
result (the unused-binding shape), and sequencing that demands it. -/
inductive Exp (V E : Type*) where
  | pure (v : V)
  | fail (e : E)
  | discardThen (a b : Exp V E)
  | seqThen (a b : Exp V E)

/-- Demand-driven evaluation: a discarded computation never runs. -/
def evalDemand : Exp V E → Res V E
  | .pure v => .val v
  | .fail e => .err e
  | .discardThen _ b => evalDemand b
  | .seqThen a b =>
    match evalDemand a with
    | .err e => Res.err e
    | .val _ => evalDemand b

/-- Eager evaluation: every subcomputation runs; errors fire regardless of
demand. -/
def evalEager : Exp V E → Res V E
  | .pure v => .val v
  | .fail e => .err e
  | .discardThen a b =>
    match evalEager a with
    | .err e => Res.err e
    | .val _ => evalEager b
  | .seqThen a b =>
    match evalEager a with
    | .err e => Res.err e
    | .val _ => evalEager b

/-- A result carrying no error. -/
def Res.isErrFree : Res V E → Prop
  | .val _ => True
  | .err _ => False

/-- No error site is dead: every discarded head evaluates error-free, so
nothing an eager evaluator would report is invisible to demand.
(Demanded positions are unrestricted.) -/
def DeadFailFree : Exp V E → Prop
  | .pure _ => True
  | .fail _ => True
  | .discardThen a b =>
      (evalEager a).isErrFree ∧ DeadFailFree a ∧ DeadFailFree b
  | .seqThen a b => DeadFailFree a ∧ DeadFailFree b

/-- On dead-error-free programs the two strictness policies agree. -/
theorem evalEager_eq_of_deadFailFree :
    ∀ (x : Exp V E), DeadFailFree x → evalEager x = evalDemand x := by
  intro x
  induction x with
  | pure v => intro _; rfl
  | fail e => intro _; rfl
  | discardThen a b iha ihb =>
    intro h
    obtain ⟨hfree, _, hb⟩ := h
    show (match evalEager a with
      | .err e => Res.err e
      | .val _ => evalEager b) = evalDemand b
    cases hea : evalEager a with
    | err e =>
      rw [hea] at hfree
      cases hfree
    | val v => exact ihb hb
  | seqThen a b iha ihb =>
    intro h
    obtain ⟨ha, hb⟩ := h
    show (match evalEager a with
      | .err e => Res.err e
      | .val _ => evalEager b) =
      (match evalDemand a with
      | .err e => Res.err e
      | .val _ => evalDemand b)
    rw [iha ha]
    cases evalDemand a with
    | err e => rfl
    | val v => exact ihb hb

/-- The separating witness: one dead error site, and the policies give
different answers — eager reports the discarded error, demand completes.
This is exactly the `!(let $x (+ 1 "s") ok)` shape. -/
theorem eager_demand_disagree_example :
    evalEager (Exp.discardThen (.fail 0) (.pure 1) : Exp Nat Nat) = .err 0 ∧
    evalDemand (Exp.discardThen (.fail 0) (.pure 1) : Exp Nat Nat) = .val 1 := by
  constructor <;> rfl

/-- Positive control: with the head demanded, the policies agree even when
it errors. -/
theorem eager_demand_agree_when_demanded :
    evalEager (Exp.seqThen (.fail 0) (.pure 1) : Exp Nat Nat) =
      evalDemand (Exp.seqThen (.fail 0) (.pure 1) : Exp Nat Nat) := by
  rfl

end Mettapedia.GSLT.LanguageDef.ErrorObservationCoherence
