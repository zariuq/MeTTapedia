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
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom matchAtom)
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

theorem under_append (consume : α → S → S) (trace : Trace S α) (next : Search S α) :
    under consume (trace.append next) =
      ((under consume trace).1 ++ (under consume (next (under consume trace).2)).1,
        (under consume (next (under consume trace).2)).2) := by
  induction trace with
  | done store => rfl
  | answer value store rest ih =>
    simp only [Trace.append, under, ih, List.cons_append]

theorem under_superpose_world (consume : α → S → S) (values : List α) (store : S) :
    (under consume (Search.superpose values store)).2 =
      values.foldl (fun world value => consume value world) store := by
  induction values generalizing store with
  | nil => rfl
  | cons value values ih => exact ih (consume value store)

private theorem superpose_append (first later : List α) (store : S) :
    Search.superpose (first ++ later) store =
      (Search.superpose first store).append (Search.superpose later) := by
  induction first generalizing store with
  | nil => rfl
  | cons head rest ih =>
    exact congrArg (Trace.answer head store) (funext ih)

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
theorem fire_all_read {A : Type} (s : Store) (p : Atom) (emit : Subst → List A) :
    fire s [] (allRead p) emit = some (s, (matchesIn s [] p).flatMap fun r => emit r.1) := by
  have kernel : (([], []) : Subst × Footprint) ∈ walk [] false [] ([].map (.pat .read)) := by simp [walk]
  have fired := fire_retained_reads_check (s := s) (ps := []) (ext := some [p]) (emit := emit)
    (by simp) kernel
  simpa [allRead, readSources, matchConj, List.flatMap_assoc] using fired

theorem fireFirst_all_read {A : Type} (s : Store) (p : Atom) (emit : Subst → List A) :
    fireFirst s (allRead p) emit = some (s, (matchesIn s [] p).flatMap fun row => emit row.1) := by
  change List.findSome? (fun guide => fire s guide (allRead p) emit) [[]] = _
  simp only [List.findSome?_cons, fire_all_read]

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

/-! ## Captured guide reuse with caller writes -/

private theorem under_guides (consume : Atom → Store → Store) {entry : Store}
    (ground : ∀ value ∈ entry, isGroundAtom value = true)
    (patterns : List Atom) (emit : Subst → Answers) (rows : List (Subst × Footprint))
    (proposed : ∀ row ∈ rows, row ∈ walk entry false [] (patterns.map (.pat .read)))
    (preserves : rows.Pairwise (fun current later =>
      ∀ value ∈ emit current.1, ∀ item ∈ later.2, ∀ world : Store,
        item.2 ∈ world → item.2 ∈ consume value world))
    (current : Store) (live : ∀ row ∈ rows, ∀ item ∈ row.2, item.2 ∈ current) :
    under consume
      ((Search.superpose (rows.map Prod.snd)).bind
        (fun guide => (firing (readSources patterns none) emit guide).bind toCaller) current) =
      under consume (Search.superpose (rows.flatMap (emit ∘ Prod.fst)) current) := by
  induction rows generalizing current with
  | nil => rfl
  | cons row later ih =>
    have kept := (List.pairwise_cons.mp preserves)
    have fired : fire current row.2 (readSources patterns none) emit = some (current, emit row.1) := by
      simpa [matchConj] using fire_retained_reads ground (ext := none) (emit := emit)
        (proposed row List.mem_cons_self) (live row List.mem_cons_self)
    have branch :
        (firing (readSources patterns none) emit row.2).bind toCaller current =
          Search.superpose (emit row.1) current := by
      simp only [Search.bind, firing, fired, Trace.bind, toCaller]
      exact append_done _
    have stay (target : Subst × Footprint) (member : target ∈ later) (item : Mode × Atom)
        (selected : item ∈ target.2) :
        item.2 ∈ (under consume (Search.superpose (emit row.1) current)).2 := by
      rw [under_superpose_world]
      have remains (answers : List Atom) (included : ∀ out ∈ answers, out ∈ emit row.1)
          (world : Store) (present : item.2 ∈ world) :
          item.2 ∈ answers.foldl (fun world value => consume value world) world := by
        induction answers generalizing world with
        | nil => exact present
        | cons head tail next =>
          exact next (fun out found => included out (List.mem_cons_of_mem _ found)) _
            (kept.1 target member head (included head List.mem_cons_self) item selected world present)
      exact remains _ (fun _ found => found) current (live target (List.mem_cons_of_mem _ member) item selected)
    have suffix := ih (fun row found => proposed row (List.mem_cons_of_mem _ found)) kept.2 _ stay
    simp only [List.map_cons, Search.bind, Search.superpose, Trace.bind, List.flatMap_cons, Function.comp_apply]
    change under consume
      (((firing (readSources patterns none) emit row.2).bind toCaller current).append
        ((Search.superpose (later.map Prod.snd)).bind
          (fun guide => (firing (readSources patterns none) emit guide).bind toCaller))) = _
    rw [branch, superpose_append, under_append, under_append, suffix]

/-- The actual per-guide traversal agrees with captured delivery under
caller writes that preserve the payloads of guides still due. Earlier
choices may be removed; new matching rows are not added to the queue.
The observation here is the ordered answer list and reached store. -/
theorem guided_reads_under_preserving_consumer (consume : Atom → Store → Store) (entry : Store)
    (ground : ∀ value ∈ entry, isGroundAtom value = true)
    (patterns : List Atom) (template : Atom)
    (preserves : (walk entry false [] (patterns.map (.pat .read))).Pairwise (fun current later =>
      ∀ value ∈ instances template current.1, ∀ item ∈ later.2, ∀ world : Store,
        item.2 ∈ world → item.2 ∈ consume value world)) :
    under consume (transform (readSources patterns none) template entry) =
      under consume (Search.superpose ((matchConj entry [] patterns).flatMap (instances template)) entry) := by
  rw [transform, transformWith]
  simp only [proposals, readSources]
  have captured := under_guides consume ground patterns (instances template)
    (walk entry false [] (patterns.map (.pat .read))) (fun _ member => member) preserves entry
    (fun _ member => (walk_sound member).2)
  rw [← walk_reads_fst entry false patterns [], List.flatMap_map]
  exact captured

namespace Controls

/-- The rows `(n one)` and `(n two)`. -/
def one : Atom := .expression [.symbol "n", .symbol "one"]
def two : Atom := .expression [.symbol "n", .symbol "two"]

/-- The pattern `(n $x)`. -/
def anyN : Atom := .expression [.symbol "n", .var "x"]

private theorem grounded_rows : ∀ value ∈ [one, two], isGroundAtom value = true := by
  intro value found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with rfl | rfl <;> decide

private def dropDelivered (value : Atom) (store : Store) : Store :=
  store.filter fun row => row != .expression [.symbol "n", value]

/-- Real writes are allowed by the preserving-consumer law. In this
example each answer removes its own row and leaves every later guide live. -/
theorem guided_read_survives_removing_each_delivered_row :
    under dropDelivered (transform (readSources [anyN] none) (.var "x") [one, two]) =
      ([.symbol "one", .symbol "two"], []) := by
  have preserves : (walk [one, two] false [] ([anyN].map (.pat .read))).Pairwise (fun current later =>
      ∀ value ∈ instances (.var "x") current.1, ∀ item ∈ later.2, ∀ world : Store,
        item.2 ∈ world → item.2 ∈ dropDelivered value world) := by
    let a : Subst × Footprint := ([("x", .symbol "one")], [(.read, one)])
    let b : Subst × Footprint := ([("x", .symbol "two")], [(.read, two)])
    have rows : walk [one, two] false [] ([anyN].map (.pat .read)) = [a, b] := by decide +kernel
    rw [rows]
    refine .cons ?_ (.cons (by simp) .nil)
    intro next found word delivered item selected world live
    obtain rfl := List.mem_singleton.mp found
    have values : instances (.var "x") a.1 = [.symbol "one"] := by decide +kernel
    rw [values] at delivered
    simp only [b, List.mem_singleton] at selected delivered
    subst word
    subst item
    simpa [dropDelivered, one, two] using live
  rw [guided_reads_under_preserving_consumer dropDelivered [one, two] grounded_rows
    [anyN] (.var "x") preserves]
  decide +kernel

/-- A plain read in the first-commit policy returns one kernel answer.
An all-read segment at the call returns both; neither commits a take. -/
theorem one_kernel_is_not_all_read :
    fireFirst [one, two] (readSources [anyN] none) (instances (.var "x")) =
      some ([one, two], [.symbol "one"]) ∧
    fireFirst [one, two] (allRead anyN) (instances (.var "x")) =
      some ([one, two], [.symbol "one", .symbol "two"]) := by
  constructor
  · rw [fireFirst_reads _ grounded_rows]
    decide +kernel
  · rw [fireFirst_all_read]
    decide +kernel

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
