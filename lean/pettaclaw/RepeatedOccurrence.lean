/-!
# RepeatedOccurrence — one repeat check gives the staged answer

A publication stages its edit list change by change. Each staged change names
an occurrence key, and a key may be edited once: the second edit of a key is
refused as a repeated occurrence. Checking each key against every earlier one
costs `n²/2` comparisons for `n` changes, which bounds how large a single
publication can grow under a fixed evaluation budget.

`once` stages without that per-change test. It collects the keys and asks one
question, "do the keys collected so far repeat?", at each place where staging
stops: at the end, before a change whose edit fails, and at a change whose
count or index operations fail (counting that change's own key, which the
per-change test checks before them). The runtime answers the question with a
hash set in linear time.

* `once_eq_each`: from keys without repeats, `once` returns exactly what the
  per-change staging `each` returns: the same refusal, the same error, or
  the same prepared count and keys.
* `once_repeated`: once the collected keys repeat, `once` refuses as
  repeated, whatever follows. This is the invariant that lets the check wait.

The model keeps what decides the answer: each change's edit outcome, its key,
its count delta and its index outcome. The operations and created references
are accumulated alongside the keys in the same order in both stagings.
-/

namespace RepeatedOccurrence

variable {K E : Type} [DecidableEq K]

/-- A change as staging sees it: its edit failed, or it names a key, moves the
count by a delta, and its index operations succeed (`none`) or fail. -/
inductive Change (K E : Type)
  | failed (error : E)
  | edit (key : K) (delta : Int) (index : Option E)

inductive Result (K E : Type)
  | repeated
  | negativeCount
  | error (error : E)
  | prepared (count : Int) (keys : List K)
  deriving DecidableEq

/-- Whether a list holds some key twice. -/
def repeats : List K → Bool
  | [] => false
  | k :: ks => ks.contains k || repeats ks

/-- Staging with the per-change test, as the edit list was staged before. -/
def each : List K → Int → List (Change K E) → Result K E
  | seen, count, [] => .prepared count seen
  | _, _, .failed e :: _ => .error e
  | seen, count, .edit k d index :: rest =>
      if seen.contains k then .repeated
      else if count + d < 0 then .negativeCount
      else match index with
        | some e => .error e
        | none => each (k :: seen) (count + d) rest

/-- The refusal staging stops with, unless the keys repeat. -/
def stop (keys : List K) (answer : Result K E) : Result K E :=
  if repeats keys then .repeated else answer

/-- Staging that asks about repeats only where it stops. -/
def once : List K → Int → List (Change K E) → Result K E
  | seen, count, [] => stop seen (.prepared count seen)
  | seen, _, .failed e :: _ => stop seen (.error e)
  | seen, count, .edit k d index :: rest =>
      if count + d < 0 then stop (k :: seen) .negativeCount
      else match index with
        | some e => stop (k :: seen) (.error e)
        | none => once (k :: seen) (count + d) rest

theorem repeats_cons (k : K) (ks : List K) :
    repeats (k :: ks) = (ks.contains k || repeats ks) := rfl

/-- Repeated keys stay repeated as staging adds keys, so `once` refuses. -/
theorem once_repeated (rest : List (Change K E)) :
    ∀ (seen : List K) (count : Int), repeats seen = true →
      once seen count rest = .repeated := by
  induction rest with
  | nil => intro seen count h; simp [once, stop, h]
  | cons change rest ih =>
    intro seen count h
    have grown : ∀ k, repeats (k :: seen) = true := fun k => by simp [repeats_cons, h]
    cases change with
    | failed e => simp [once, stop, h]
    | edit k d index =>
      simp only [once]
      split
      · simp [stop, grown k]
      · cases index with
        | some e => simp [stop, grown k]
        | none => exact ih (k :: seen) (count + d) (grown k)

/-- From keys without repeats, checking once gives what checking each change
gives. -/
theorem once_eq_each (changes : List (Change K E)) :
    ∀ (seen : List K) (count : Int), repeats seen = false →
      once seen count changes = each seen count changes := by
  induction changes with
  | nil => intro seen count h; simp [once, each, stop, h]
  | cons change rest ih =>
    intro seen count h
    cases change with
    | failed e => simp [once, each, stop, h]
    | edit k d index =>
      by_cases member : seen.contains k = true
      · -- The per-change test refuses here; the collected keys now repeat.
        have grown : repeats (k :: seen) = true := by rw [repeats_cons, member]; rfl
        simp only [each, member, if_true, once]
        split
        · simp [stop, grown]
        · cases index with
          | some e => simp [stop, grown]
          | none => exact once_repeated rest (k :: seen) (count + d) grown
      · have fresh : repeats (k :: seen) = false := by
          simp only [repeats_cons, h, Bool.or_false]; simpa using member
        have absent : seen.contains k = false := by simpa using member
        simp only [each, absent, once]
        split
        · simp [stop, fresh]
        · cases index with
          | some e => simp [stop, fresh]
          | none => exact ih (k :: seen) (count + d) fresh

/-- Both stagings start from no keys. -/
theorem staging_agrees (count : Int) (changes : List (Change K E)) :
    once [] count changes = each [] count changes :=
  once_eq_each changes [] count rfl

/-- A repeat followed by a failing edit: the per-change staging refuses at the
repeat, so the check before the failing edit must count the earlier keys. -/
example : once (E := Nat) [] 0 [.edit 1 1 none, .edit 1 1 none, .failed 7] = .repeated := by decide

/-- A repeat whose own count would go negative is still refused as a repeat,
because the per-change test comes before the count. -/
example : each (E := Nat) [] 0 [.edit 1 1 none, .edit 1 (-5) none] = .repeated := by decide

end RepeatedOccurrence

#print axioms RepeatedOccurrence.once_eq_each
#print axioms RepeatedOccurrence.staging_agrees
