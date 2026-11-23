import Mathlib.Tactic

/-!
# Encoding a conversation newest first

A provider request encodes its conversation message by message. Each message
encodes to a list of wire items, or fails. The conversation encodes to the
items of every message in order, unless a message fails: then it encodes to
the first failure in message order.

The reference encoder appends each message's items to the items so far, so
every message copies everything before it. The linear encoder puts each
message's items onto a newest-first list and reverses once at the end. A
failure it meets stays, and no later message replaces it.

Invariants proved here:
* for every conversation the linear encoder answers what the reference
  encoder answers, failures included;
* the linear encoder's work is twice the number of items, while the
  reference encoder's work grows with the square of the number of messages
  when each message has one item.

The counterexample is the rule the linear encoder must not follow: keeping
the newest failure (as consing failures newest first and reading the head
would) reports the second of two failing messages, where the reference
reports the first.

This is an abstract contract, not a refinement proof of `lib/llm.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ConversationEncoding

variable {α β ε : Type}

/-- The reference step: append this message's items to the items so far. -/
def appendStep (enc : α → Except ε (List β)) : Except ε (List β) → α → Except ε (List β)
  | .error e, _ => .error e
  | .ok acc, m =>
    match enc m with
    | .error e => .error e
    | .ok items => .ok (acc ++ items)

/-- The reference encoder. -/
def reference (enc : α → Except ε (List β)) (ms : List α) : Except ε (List β) :=
  ms.foldl (appendStep enc) (.ok [])

/-- The linear step: this message's items onto the newest-first list. -/
def newestStep (enc : α → Except ε (List β)) : Except ε (List β) → α → Except ε (List β)
  | .error e, _ => .error e
  | .ok acc, m =>
    match enc m with
    | .error e => .error e
    | .ok items => .ok (items.reverse ++ acc)

/-- The linear encoder: newest first, put in order once. -/
def linear (enc : α → Except ε (List β)) (ms : List α) : Except ε (List β) :=
  (ms.foldl (newestStep enc) (.ok [])).map List.reverse

theorem append_from_failure (enc : α → Except ε (List β)) (e : ε) (ms : List α) :
    ms.foldl (appendStep enc) (.error e) = .error e := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simpa [List.foldl, appendStep] using ih

theorem newest_from_failure (enc : α → Except ε (List β)) (e : ε) (ms : List α) :
    ms.foldl (newestStep enc) (.error e) = .error e := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simpa [List.foldl, newestStep] using ih

theorem linear_from (enc : α → Except ε (List β)) (ms : List α) (acc : List β) :
    (ms.foldl (newestStep enc) (.ok acc)).map List.reverse =
      ms.foldl (appendStep enc) (.ok acc.reverse) := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.foldl, newestStep, appendStep]
    cases h : enc m with
    | error e => simp [newest_from_failure, append_from_failure, Except.map]
    | ok items => simpa [List.reverse_append] using ih (items.reverse ++ acc)

/-- The linear encoder answers what the reference answers, for every
conversation: the same items in the same order, or the same first failure. -/
theorem linear_eq_reference (enc : α → Except ε (List β)) (ms : List α) :
    linear enc ms = reference enc ms := by
  simpa [linear, reference] using linear_from enc ms []

/-- The work of the reference: appending copies the items so far. `sizes`
are the messages' item counts and `before` the items already encoded. -/
def referenceWork : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: rest, before => before + referenceWork rest (before + s)

/-- The work of the linear encoder: each item is moved onto the newest-first
list once, and once more by the final reversal. -/
def newestWork : List ℕ → ℕ
  | [] => 0
  | s :: rest => s + newestWork rest

def linearWork (sizes : List ℕ) : ℕ := newestWork sizes + sizes.sum

theorem newestWork_eq_sum (sizes : List ℕ) : newestWork sizes = sizes.sum := by
  induction sizes with
  | nil => rfl
  | cons s rest ih => simp [newestWork, ih]

theorem linearWork_eq (sizes : List ℕ) : linearWork sizes = 2 * sizes.sum := by
  simp [linearWork, newestWork_eq_sum, two_mul]

/-- With one item per message the reference copies `n (n - 1) / 2` items in
all: `2 W + n = n²` for `n` messages starting from nothing. -/
theorem referenceWork_one_each (n before : ℕ) :
    2 * referenceWork (List.replicate n 1) before + n = 2 * n * before + n * n := by
  induction n generalizing before with
  | zero => simp [referenceWork]
  | succ n ih =>
    have := ih (before + 1)
    simp only [List.replicate_succ, referenceWork]
    nlinarith [this]

theorem linearWork_one_each (n : ℕ) : linearWork (List.replicate n 1) = 2 * n := by
  simp [linearWork_eq]

/-! ## Counterexample: keeping the newest failure -/

/-- A newest-first step that lets a later failure replace an earlier one. -/
def newestFailureStep (enc : α → Except ε (List β)) : Except ε (List β) → α → Except ε (List β)
  | acc, m =>
    match enc m, acc with
    | .error e, _ => .error e
    | .ok _, .error e => .error e
    | .ok items, .ok acc => .ok (items.reverse ++ acc)

def newestFailure (enc : α → Except ε (List β)) (ms : List α) : Except ε (List β) :=
  (ms.foldl (newestFailureStep enc) (.ok [])).map List.reverse

/-- Two failing messages: the first fails with `0`, the second with `1`. -/
def twoFailures : ℕ → Except ℕ (List ℕ)
  | m => .error m

theorem newest_failure_reports_the_second :
    newestFailure twoFailures [0, 1] = .error 1 ∧ reference twoFailures [0, 1] = .error 0 := by
  constructor <;> rfl

theorem newest_failure_differs :
    newestFailure twoFailures [0, 1] ≠ reference twoFailures [0, 1] := by
  rw [newest_failure_reports_the_second.1, newest_failure_reports_the_second.2]
  decide

end Mettapedia.Protocols.Agents.ConversationEncoding
