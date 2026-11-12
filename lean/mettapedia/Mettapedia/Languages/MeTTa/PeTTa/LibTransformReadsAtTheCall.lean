import Mettapedia.Languages.MeTTa.PeTTa.LibTransform

/-!
# A read as one firing at the call answers the same under every consumer

PeTTa's `match` answers from the store as it is when the match is called: the code that
consumes its answers may remove a row not answered yet, or add one, and the answers stay.
The library's model keeps what a consumer does in view: a `Trace` resumes from the store the
consumer leaves. This module states the difference between the two ways of writing a read
with `transform`.

* `Trace.under`: the answers of a trace when the consumer changes the store after each
  answer. `Trace.drain` is the case of a consumer that changes nothing (`under_id`).
* `transform_all_read`: `(transform S (all (read p)) T)` is, as a trace, the instances of
  the matches of `p` in the store at the call, given one after another without touching
  the store.
* `all_read_under_any_consumer`: so its answers are those instances whatever the consumer
  does to the store between them.
* `Controls.branch_per_match_misses_a_removed_row`: with one branch for each match (the
  kernel read `p`), a consumer that removes the second row after the first answer gets one
  answer; `Controls.all_read_answers_a_removed_row`: the read at the call gets both.
* `Controls.conjunction_in_one_state`, `Controls.conjunction_part_by_part`: over `(left a)`,
  `(left b)`, `(right a)` with a consumer that adds `(right b)` after each answer, the joint
  read in one state answers `a`, and the two reads in turn, the second when the first's
  answer is reached, answer `a` and `b`, as PeTTa's `match` on the conjunction does.

Not here: the same for takes (a take is validated at its firing by definition), and the
library's text (this is about the model).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open LibTransform

/-! ## Traces under a consumer that writes -/

section Traces

variable {S α : Type}

/-- Running a trace and then stopping is the trace. -/
theorem append_done (t : Trace S α) : t.append Trace.done = t := by
  induction t with
  | done s => rfl
  | answer a s r ih =>
      simp only [Trace.append]
      congr 1
      funext s'
      exact ih s'

/-- Every answer and the final store, for a consumer that changes the store after each
answer: the search resumes from the store the consumer leaves. -/
def under (consume : α → S → S) : Trace S α → List α × S
  | .done s => ([], s)
  | .answer a s r =>
      (a :: ((under consume (r (consume a s)))).1, (under consume (r (consume a s))).2)

/-- A consumer that leaves the store as it is sees what `drain` gives. -/
theorem under_id (t : Trace S α) : under (fun _ s => s) t = t.drain := by
  induction t with
  | done s => rfl
  | answer a s r ih => simp only [under, Trace.drain, ih]

/-- Values given one after another without touching the store are all answered, whatever
the consumer does. -/
theorem under_superpose (consume : α → S → S) :
    ∀ (xs : List α) (s : S), (under consume (Search.superpose xs s)).1 = xs
  | [], _ => rfl
  | x :: xs, s => by
      simp only [Search.superpose, under, under_superpose consume xs]

end Traces

/-! ## The read at the call -/

/-- `(all (read p))`: one firing that reads every match of `p`. -/
def allRead (p : Atom) : Sources where
  kernel := []
  every := some [.pat .read p]

theorem walk_read (s : Store) (firing : Bool) (σ : Subst) (p : Atom) :
    walk s firing σ [.pat .read p] = (matchesIn s σ p).map fun r => (r.1, [(.read, r.2)]) := by
  simp [walk, List.map_eq_flatMap]

/-- The firing of `(all (read p))` leaves the store and gives one instance set for each
match, in match order. -/
theorem fire_all_read (s : Store) (p : Atom) (emit : Subst → Answers) :
    fire s [] (allRead p) emit = some (s, (matchesIn s [] p).flatMap fun r => emit r.1) := by
  have cands : candidates s [] (allRead p) = [⟨[], walk s true [] [.pat .read p]⟩] := rfl
  have reads : ∀ e ∈ Candidate.footprint ⟨[], walk s true [] [.pat .read p]⟩, e.1 = .read := by
    intro e member
    simp only [Candidate.footprint, List.nil_append, List.mem_flatMap] at member
    obtain ⟨w, inWalk, inRow⟩ := member
    exact walk_reads_entries (ps := [p]) inWalk e inRow
  rw [fire_of_first cands (valid_of_reads reads s), commit_of_reads reads]
  simp [Candidate.instances, walk_read, List.flatMap_map]

/-- **A read written as one firing at the call is, as a trace, the instances of the
matches in the store at the call, given one after another without touching the store.** -/
theorem transform_all_read (s : Store) (p template : Atom) :
    transform (allRead p) template s =
      Search.superpose ((matchesIn s [] p).flatMap fun r => instances template r.1) s := by
  have props : proposals s (allRead p) = [[]] := rfl
  simp only [transform, transformWith, props, Search.bind, Search.superpose, Trace.bind,
    firing, fire_all_read, toCaller]
  exact (append_done _).trans (append_done _)

/-- **Its answers are the same under every consumer**: the instances of the matches in the
store at the call, whatever is written to the store between them. -/
theorem all_read_under_any_consumer (consume : Atom → Store → Store) (s : Store)
    (p template : Atom) :
    (under consume (transform (allRead p) template s)).1 =
      (matchesIn s [] p).flatMap fun r => instances template r.1 := by
  rw [transform_all_read, under_superpose]

namespace Controls

/-- The rows `(n one)` and `(n two)`. -/
def one : Atom := .expression [.symbol "n", .symbol "one"]
def two : Atom := .expression [.symbol "n", .symbol "two"]

/-- The pattern `(n $x)`. -/
def anyN : Atom := .expression [.symbol "n", .var "x"]

/-- After each answer the consumer removes `(n two)`. -/
def dropTwo : Atom → Store → Store := fun _ s => s.filter fun row => decide (row ≠ two)

/-- Negative: with one branch for each match, the branch of the second row finds it gone. -/
theorem branch_per_match_misses_a_removed_row :
    (under dropTwo (transform (readSources [anyN] none) (.var "x") [one, two])).1 =
      [.symbol "one"] := by
  decide

/-- Positive: the read at the call answers both rows. -/
theorem all_read_answers_a_removed_row :
    (under dropTwo (transform (allRead anyN) (.var "x") [one, two])).1 =
      [.symbol "one", .symbol "two"] := by
  decide

/-- The rows `(left a)`, `(left b)`, `(right a)`. -/
def sides : Store :=
  [.expression [.symbol "left", .symbol "a"], .expression [.symbol "left", .symbol "b"],
    .expression [.symbol "right", .symbol "a"]]

/-- After each answer the consumer adds `(right b)`. -/
def addRightB : Atom → Store → Store :=
  fun _ s => s ++ [.expression [.symbol "right", .symbol "b"]]

/-- The joint read of `(left $x)` and `(right $x)` in one state answers `a` only. -/
theorem conjunction_in_one_state :
    (under addRightB
      (transform { kernel := [], every := some [.pat .read (.expression [.symbol "left", .var "x"]),
          .pat .read (.expression [.symbol "right", .var "x"])] } (.var "x") sides)).1 =
      [.symbol "a"] := by
  decide

/-- The two reads in turn, the second when the first's answer is reached, answer `a` and
`b`: the consumer of `a` added the row that gives `b`. -/
theorem conjunction_part_by_part :
    (under addRightB
      (((transform (allRead (.expression [.symbol "left", .var "x"])) (.var "x")).bind fun value =>
          transform (allRead (.expression [.symbol "right", value])) value) sides)).1 =
      [.symbol "a", .symbol "b"] := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
