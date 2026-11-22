import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Validations

/-!
# The policies at an observation, at the grain of kinds: one table of instances

An observation says two things: which answers it returns, and what it publishes.
`Policy.returningAll` and `Policy.returningFirst` put the selection of an
observation form, every answer or the first one, on the publication of any
policy.  Four publications are compared: none (`Policy.publishNone`), the chosen
proposal (`Policy.publishChosen`), a wave validated on its writes
(`Policy.publishWaveOnWrites`), a wave validated on its reads as well
(`Policy.publishWave`).

Five programs are run, each a directive that is observed and then a directive
that reads the whole space.  A space is read by kinds; a read of the whole
pattern is a complete read of both kinds (`Probes.bagOfMatches`), and one answer
of a match is a positive read of one kind (`seeKind`).

| Program | observation | none | the chosen | wave on writes | wave on reads | committed mode |
|---|---|---|---|---|---|---|
| `Probes.addThenReadAll`: each sibling adds an atom and reads the pattern | all | `(1,0) (0,1)`; then `(0,0)` | `(1,0) (0,1)`; then `(1,0)` | `(1,0) (0,1)`; then `(1,1)` | `(1,0) (0,1)`, conflict; then `(0,0)` | `(1,0) (1,1)`; then `(1,1)` |
| `Probes.addThenAnswer`: each sibling adds an atom and answers with it | first | `a`; then `(0,0)` | `a`; then `(1,0)` | `a`; then `(1,1)` | `a`; then `(1,1)` | `a b`; then `(1,1)` |
| `Probes.seeThenTake`: each sibling sees the one token and takes it | all | both; then `(1,0)` | both; then `(0,0)` | both, conflict; then `(1,0)` | both, conflict; then `(1,0)` | the first; then `(0,0)` |
| `Probes.addThenFail`: one sibling adds and fails, the other adds and answers | all | `b`; then `(0,0)` | `b`; then `(0,1)` | `b`; then `(0,1)` | `b`; then `(0,1)` | `b`; then `(1,1)` |
| `Probes.addOnly`: each sibling adds an atom | all | two; then `(0,0)` | two; then `(1,0)` | two; then `(1,1)` | two; then `(1,1)` | two; then `(1,1)` |

One theorem for each row: `Probes.addThenReadAll_table`, `Probes.addThenAnswer_table`,
`Probes.seeThenTake_table`, `Probes.addThenFail_table`, `Probes.addOnly_table`.
On these five programs installation on writes does what replay on writes does
(`Probes.installation_agrees`).  A fifth publication, a wave validated on its
claims, is run on the same programs in `PatternFootprints.Claims`
(`ClaimControls.programs_on_claims`).

A match itself, observed.  The first answer of a match is one positive read: its
outcome is an outcome from every larger state (`Region.matchKinds_first_stillHas`).
All the answers of a match are a complete read: an addition of a kind of the
pattern adds an answer (`Region.matchKinds_answers_grow`).  Both on one instance:
`Probes.match_observed`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

section Selection

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **Return every answer**, and publish as the policy does. -/
def Policy.returningAll (policy : Policy Location Value Answer) : Policy Location Value Answer where
  returned outcomes := outcomes.map Prod.fst
  change := policy.change

/-- **Return the first answer only**, and publish as the policy does. -/
def Policy.returningFirst (policy : Policy Location Value Answer) :
    Policy Location Value Answer where
  returned outcomes := (outcomes.head?.map Prod.fst).toList
  change := policy.change

/-- Selection does not touch publication. -/
theorem Policy.returning_change (policy : Policy Location Value Answer) :
    policy.returningAll.change = policy.change ∧ policy.returningFirst.change = policy.change :=
  ⟨rfl, rfl⟩

end Selection

/-! ## A match, observed -/

/-- A filter that accepts more, and one element that the other refuses, keeps
strictly more. -/
theorem length_filter_lt_of_accepts_more {α : Type u} {accepts more : α → Bool} (list : List α)
    (weaker : ∀ element ∈ list, accepts element = true → more element = true) {witness : α}
    (member : witness ∈ list) (gained : more witness = true) (refused : accepts witness = false) :
    (list.filter accepts).length < (list.filter more).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  induction list with
  | nil => cases member
  | cons head rest ih =>
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp member with rfl | later
      · have restLe : rest.countP accepts ≤ rest.countP more :=
          List.countP_mono_left fun element inside holds =>
            weaker element (List.mem_cons_of_mem _ inside) holds
        rw [refused, gained]
        simp only [Bool.false_eq_true, if_false, if_true]
        omega
      · have restLt := ih (fun element inside holds =>
          weaker element (List.mem_cons_of_mem head inside) holds) later
        by_cases headAccepted : accepts head = true
        · rw [headAccepted, weaker head List.mem_cons_self headAccepted]
          omega
        · have headRefused : accepts head = false := Bool.not_eq_true _ |>.mp headAccepted
          rw [headRefused]
          simp only [Bool.false_eq_true, if_false]
          split <;> omega

section MatchObserved

variable [DecidableEq Location]

/-- **The first answer of a match is one positive read.**  The outcome that an
observation of the first answer returns is an outcome of the match from every
larger state.  It need not be the first one there. -/
theorem Region.matchKinds_first_stillHas (candidates : List (Location × Answer))
    (state added : Location → ℕ) {chosen : Answer × Proposal Location ℕ Answer}
    (first : ((Region.matchKinds candidates).branchLocal state).head? = some chosen) :
    (Region.matchKinds candidates).StillHas (state + added) chosen :=
  ((Region.matchKinds_monotone candidates).positive.branchLocal_sublist state added).subset
    (List.mem_of_mem_head? (Option.mem_def.mpr first))

/-- **All the answers of a match are a complete read.**  The addition of a
candidate kind that was absent adds an answer: what an observation of every
answer returned is no longer what the match returns. -/
theorem Region.matchKinds_answers_grow (candidates : List (Location × Answer))
    (state : Location → ℕ) {kind : Location} {answer : Answer}
    (candidate : (kind, answer) ∈ candidates) (absent : state kind = 0) :
    (((Region.matchKinds candidates).branchLocal state).map Prod.fst).length <
      (((Region.matchKinds candidates).branchLocal (state + Pi.single kind 1)).map
        Prod.fst).length := by
  rw [Region.matchKinds_answers, Region.matchKinds_answers, List.length_map, List.length_map]
  refine length_filter_lt_of_accepts_more candidates (fun element _ present => ?_) candidate ?_ ?_
  · have positive : 0 < state element.1 := of_decide_eq_true present
    exact decide_eq_true (Nat.lt_of_lt_of_le positive (Nat.le_add_right _ _))
  · refine decide_eq_true ?_
    show 0 < state kind + (Pi.single kind 1 : Location → ℕ) kind
    rw [Pi.single_eq_same]
    omega
  · exact decide_eq_false (by rw [absent]; exact Nat.lt_irrefl 0)

end MatchObserved

namespace Probes

open AddOnly (Kind noKinds)

/-- The answers of the programs. -/
inductive Reply where
  /-- An atom, as an answer. -/
  | atom (kind : Kind)
  /-- The whole bag of matches of the pattern: how often each kind. -/
  | bag (a b : ℕ)
  /-- A receipt: which sibling got the token. -/
  | got (first : Bool)
  /-- Nothing to say. -/
  | done
  deriving DecidableEq

/-- **The whole bag of answers of a match of the pattern**: a complete read of
both kinds. -/
def bagOfMatches : Readout Kind ℕ Reply :=
  ⟨{.a, .b}, fun state => .bag (state .a) (state .b),
    fun agrees => by rw [agrees Kind.a (by decide), agrees Kind.b (by decide)]⟩

/-- The directive that reads the whole space. -/
def readSpace : Region Kind ℕ Reply :=
  .answer bagOfMatches

/-- One token. -/
def oneToken : Kind → ℕ := Pi.single Kind.a 1

/-- **Positive, selection**: with the policy that publishes nothing, returning
every answer is that policy; with the policy of the chosen one, returning the
first answer is that policy. -/
theorem returning_same :
    (Policy.publishNone : Policy Kind ℕ Reply).returningAll = Policy.publishNone ∧
      (Policy.publishChosen : Policy Kind ℕ Reply).returningFirst = Policy.publishChosen :=
  ⟨rfl, rfl⟩

/-- **Negative, selection**: returning every answer with the publication of the
chosen one is not the policy of the chosen one: of two outcomes it returns two
answers. -/
theorem returningAll_publishChosen_ne :
    (Policy.publishChosen : Policy Kind ℕ Reply).returningAll.returned
        [(.done, ⟨[], Readout.const .done⟩), (.done, ⟨[], Readout.const .done⟩)] ≠
      (Policy.publishChosen : Policy Kind ℕ Reply).returned
        [(.done, ⟨[], Readout.const .done⟩), (.done, ⟨[], Readout.const .done⟩)] := by
  decide

/-- **Negative, selection**: returning the first answer with the publication of
nothing is not the policy that publishes nothing: of two outcomes it returns one
answer. -/
theorem returningFirst_publishNone_ne :
    (Policy.publishNone : Policy Kind ℕ Reply).returningFirst.returned
        [(.done, ⟨[], Readout.const .done⟩), (.done, ⟨[], Readout.const .done⟩)] ≠
      (Policy.publishNone : Policy Kind ℕ Reply).returned
        [(.done, ⟨[], Readout.const .done⟩), (.done, ⟨[], Readout.const .done⟩)] := by
  decide

/-- A match of the pattern over the two kinds, each answering with its kind. -/
def matchBoth : Region Kind ℕ Reply :=
  Region.matchKinds [(.a, .atom .a), (.b, .atom .b)]

/-- **A match observed for its first answer, and for all its answers.**  From the
state with a `b`, both observations return `b`.  After an `a` is added, the
observation of all answers returns two: the list that was returned is no longer
the list (`Region.matchKinds_answers_grow`).  The observation of the first answer
returns `a`: which answer is the first depends on the order of evaluation; the
outcome that was returned is still an outcome (`Region.matchKinds_first_stillHas`). -/
theorem match_observed :
    (matchBoth.observe Policy.publishNone.returningFirst (Pi.single Kind.b 1)).1 = [.atom .b] ∧
      (matchBoth.observe Policy.publishNone (Pi.single Kind.b 1)).1 = [.atom .b] ∧
      (matchBoth.observe Policy.publishNone.returningFirst
        (Pi.single Kind.b 1 + Pi.single Kind.a 1)).1 = [.atom .a] ∧
      (matchBoth.observe Policy.publishNone (Pi.single Kind.b 1 + Pi.single Kind.a 1)).1 =
        [.atom .a, .atom .b] := by
  decide

/-! ### Each sibling adds an atom and reads the pattern -/

/-- A sibling: add an atom, then answer with the whole bag of matches. -/
def addThenReadAllSibling (kind : Kind) : Region Kind ℕ Reply :=
  .step (addKind kind) (.answer bagOfMatches)

/-- The two siblings. -/
def addThenReadAll : Region Kind ℕ Reply :=
  Region.alternatives [addThenReadAllSibling .a, addThenReadAllSibling .b]

/-- **Each sibling adds an atom and reads the pattern.**  Every publication
returns the two answers that the siblings read from their own views.  Nothing
published: the space stays empty.  The chosen: one atom.  A wave on writes: both
atoms, with answers that no serial run gives.  A wave on reads: a conflict, and
the space stays empty. -/
theorem addThenReadAll_table :
    (runDirectives Policy.publishNone [addThenReadAll, readSpace] noKinds).1 =
        [([.bag 1 0, .bag 0 1], false), ([.bag 0 0], false)] ∧
      (runDirectives Policy.publishChosen.returningAll [addThenReadAll, readSpace] noKinds).1 =
        [([.bag 1 0, .bag 0 1], false), ([.bag 1 0], false)] ∧
      (runDirectives Policy.publishWaveOnWrites [addThenReadAll, readSpace] noKinds).1 =
        [([.bag 1 0, .bag 0 1], false), ([.bag 1 1], false)] ∧
      (runDirectives Policy.publishWave [addThenReadAll, readSpace] noKinds).1 =
        [([.bag 1 0, .bag 0 1], true), ([.bag 0 0], false)] := by
  decide

/-- The committed mode: the second sibling reads the atom of the first. -/
theorem addThenReadAll_committed :
    (addThenReadAll.committed noKinds).1 = [.bag 1 0, .bag 1 1] ∧
      (readSpace.committed (addThenReadAll.committed noKinds).2).1 = [.bag 1 1] := by
  decide

/-! ### Each sibling adds an atom and answers with it; the first answer is returned -/

/-- A sibling: add an atom and answer with it. -/
def addThenAnswerSibling (kind : Kind) : Region Kind ℕ Reply :=
  .step (addKind kind) (.answer (Readout.const (.atom kind)))

/-- The two siblings. -/
def addThenAnswer : Region Kind ℕ Reply :=
  Region.alternatives [addThenAnswerSibling .a, addThenAnswerSibling .b]

/-- **Each sibling adds an atom and answers with it; the observation returns the
first answer.**  Nothing published: the space stays empty.  The chosen: its atom
only.  A wave, on writes or on reads: both atoms, also the one of the sibling
whose answer was not returned. -/
theorem addThenAnswer_table :
    (runDirectives Policy.publishNone.returningFirst [addThenAnswer, readSpace] noKinds).1 =
        [([.atom .a], false), ([.bag 0 0], false)] ∧
      (runDirectives Policy.publishChosen [addThenAnswer, readSpace] noKinds).1 =
        [([.atom .a], false), ([.bag 1 0], false)] ∧
      (runDirectives Policy.publishWaveOnWrites.returningFirst [addThenAnswer, readSpace]
        noKinds).1 = [([.atom .a], false), ([.bag 1 1], false)] ∧
      (runDirectives Policy.publishWave.returningFirst [addThenAnswer, readSpace] noKinds).1 =
        [([.atom .a], false), ([.bag 1 1], false)] := by
  decide

/-- The committed mode: both atoms. -/
theorem addThenAnswer_committed :
    (addThenAnswer.committed noKinds).1 = [.atom .a, .atom .b] ∧
      (readSpace.committed (addThenAnswer.committed noKinds).2).1 = [.bag 1 1] := by
  decide

/-! ### Each sibling sees the one token and takes it -/

/-- A sibling: see the token, take it, answer with a receipt. -/
def seeThenTakeSibling (first : Bool) : Region Kind ℕ Reply :=
  .step (seeKind .a) (.step (removeKind .a) (.answer (Readout.const (.got first))))

/-- The two siblings. -/
def seeThenTake : Region Kind ℕ Reply :=
  Region.alternatives [seeThenTakeSibling true, seeThenTakeSibling false]

/-- **Each sibling sees the one token and takes it.**  Both answer from the
snapshot under every publication.  Nothing published: the token stays.  The
chosen: the token is gone once, and two receipts were returned.  A wave, on
writes or on reads: a conflict, and the token stays. -/
theorem seeThenTake_table :
    (runDirectives Policy.publishNone [seeThenTake, readSpace] oneToken).1 =
        [([.got true, .got false], false), ([.bag 1 0], false)] ∧
      (runDirectives Policy.publishChosen.returningAll [seeThenTake, readSpace] oneToken).1 =
        [([.got true, .got false], false), ([.bag 0 0], false)] ∧
      (runDirectives Policy.publishWaveOnWrites [seeThenTake, readSpace] oneToken).1 =
        [([.got true, .got false], true), ([.bag 1 0], false)] ∧
      (runDirectives Policy.publishWave [seeThenTake, readSpace] oneToken).1 =
        [([.got true, .got false], true), ([.bag 1 0], false)] := by
  decide

/-- The committed mode: the first sibling in the order of evaluation gets it. -/
theorem seeThenTake_committed :
    (seeThenTake.committed oneToken).1 = [.got true] ∧
      (readSpace.committed (seeThenTake.committed oneToken).2).1 = [.bag 0 0] := by
  decide

/-! ### One sibling adds and fails, the other adds and answers -/

/-- Add an atom, then fail. -/
def addThenFailFailing : Region Kind ℕ Reply :=
  .step (addKind .a) .fail

/-- Add an atom and answer with it. -/
def addThenFailAnswering : Region Kind ℕ Reply :=
  .step (addKind .b) (.answer (Readout.const (.atom .b)))

/-- The two siblings. -/
def addThenFail : Region Kind ℕ Reply :=
  Region.alternatives [addThenFailFailing, addThenFailAnswering]

/-- **One sibling adds and fails, the other adds and answers.**  The sibling that
failed proposes nothing.  Nothing published: the space stays empty.  Every other
publication: the atom of the sibling that answered, and no other. -/
theorem addThenFail_table :
    (runDirectives Policy.publishNone [addThenFail, readSpace] noKinds).1 =
        [([.atom .b], false), ([.bag 0 0], false)] ∧
      (runDirectives Policy.publishChosen.returningAll [addThenFail, readSpace] noKinds).1 =
        [([.atom .b], false), ([.bag 0 1], false)] ∧
      (runDirectives Policy.publishWaveOnWrites [addThenFail, readSpace] noKinds).1 =
        [([.atom .b], false), ([.bag 0 1], false)] ∧
      (runDirectives Policy.publishWave [addThenFail, readSpace] noKinds).1 =
        [([.atom .b], false), ([.bag 0 1], false)] := by
  decide

/-- The committed mode: the atom of the sibling that failed stays. -/
theorem addThenFail_committed :
    (addThenFail.committed noKinds).1 = [.atom .b] ∧
      (readSpace.committed (addThenFail.committed noKinds).2).1 = [.bag 1 1] := by
  decide

/-! ### Each sibling adds an atom -/

/-- A sibling: add an atom. -/
def addOnlySibling (kind : Kind) : Region Kind ℕ Reply :=
  .step (addKind kind) (.answer (Readout.const .done))

/-- The two siblings. -/
def addOnly : Region Kind ℕ Reply :=
  Region.alternatives [addOnlySibling .a, addOnlySibling .b]

/-- **Each sibling adds an atom.**  Nothing published: the space stays empty.  The
chosen: one atom.  A wave, on writes or on reads: both atoms; at the grain of
kinds the two additions write two locations and read nothing. -/
theorem addOnly_table :
    (runDirectives Policy.publishNone [addOnly, readSpace] noKinds).1 =
        [([.done, .done], false), ([.bag 0 0], false)] ∧
      (runDirectives Policy.publishChosen.returningAll [addOnly, readSpace] noKinds).1 =
        [([.done, .done], false), ([.bag 1 0], false)] ∧
      (runDirectives Policy.publishWaveOnWrites [addOnly, readSpace] noKinds).1 =
        [([.done, .done], false), ([.bag 1 1], false)] ∧
      (runDirectives Policy.publishWave [addOnly, readSpace] noKinds).1 =
        [([.done, .done], false), ([.bag 1 1], false)] := by
  decide

/-- The committed mode: both atoms. -/
theorem addOnly_committed :
    (addOnly.committed noKinds).1 = [.done, .done] ∧
      (readSpace.committed (addOnly.committed noKinds).2).1 = [.bag 1 1] := by
  decide

/-- **On these five programs installation on writes does what replay on writes
does.** -/
theorem installation_agrees :
    (runDirectives Policy.installWaveOnWrites [addThenReadAll, readSpace] noKinds).1 =
        (runDirectives Policy.publishWaveOnWrites [addThenReadAll, readSpace] noKinds).1 ∧
      (runDirectives Policy.installWaveOnWrites.returningFirst [addThenAnswer, readSpace]
        noKinds).1 =
        (runDirectives Policy.publishWaveOnWrites.returningFirst [addThenAnswer, readSpace]
          noKinds).1 ∧
      (runDirectives Policy.installWaveOnWrites [seeThenTake, readSpace] oneToken).1 =
        (runDirectives Policy.publishWaveOnWrites [seeThenTake, readSpace] oneToken).1 ∧
      (runDirectives Policy.installWaveOnWrites [addThenFail, readSpace] noKinds).1 =
        (runDirectives Policy.publishWaveOnWrites [addThenFail, readSpace] noKinds).1 ∧
      (runDirectives Policy.installWaveOnWrites [addOnly, readSpace] noKinds).1 =
        (runDirectives Policy.publishWaveOnWrites [addOnly, readSpace] noKinds).1 := by
  decide

/-- **Which of the five are monotone regions.**  The siblings that add and answer
with a constant are; the siblings that read the pattern, and those that take the
token, are not. -/
theorem monotone_programs :
    addThenAnswer.Monotone ∧ addThenFail.Monotone ∧ addOnly.Monotone ∧
      ¬ addThenReadAll.Monotone ∧ ¬ seeThenTake.Monotone := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Region.monotone_alternatives_iff.mpr fun sibling member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact .step (addKind_monotone _) (.answer rfl)
      · rw [List.mem_singleton.mp later]
        exact .step (addKind_monotone _) (.answer rfl)
  · exact Region.monotone_alternatives_iff.mpr fun sibling member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact .step (addKind_monotone _) .fail
      · rw [List.mem_singleton.mp later]
        exact .step (addKind_monotone _) (.answer rfl)
  · exact Region.monotone_alternatives_iff.mpr fun sibling member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact .step (addKind_monotone _) (.answer rfl)
      · rw [List.mem_singleton.mp later]
        exact .step (addKind_monotone _) (.answer rfl)
  · intro monotone
    have first := Region.monotone_alternatives_iff.mp monotone (addThenReadAllSibling .a)
      List.mem_cons_self
    cases first with
    | step _ restMonotone =>
        cases restMonotone with
        | answer constant => exact absurd constant (by decide)
  · intro monotone
    have first := Region.monotone_alternatives_iff.mp monotone (seeThenTakeSibling true)
      List.mem_cons_self
    cases first with
    | step _ restMonotone =>
        cases restMonotone with
        | step stepMonotone _ => exact removeKind_not_monotone Kind.a stepMonotone

end Probes

#print axioms Policy.returning_change
#print axioms length_filter_lt_of_accepts_more
#print axioms Region.matchKinds_first_stillHas
#print axioms Region.matchKinds_answers_grow
#print axioms Probes.match_observed
#print axioms Probes.returning_same
#print axioms Probes.returningAll_publishChosen_ne
#print axioms Probes.returningFirst_publishNone_ne
#print axioms Probes.addThenReadAll_table
#print axioms Probes.addThenReadAll_committed
#print axioms Probes.addThenAnswer_table
#print axioms Probes.addThenAnswer_committed
#print axioms Probes.seeThenTake_table
#print axioms Probes.seeThenTake_committed
#print axioms Probes.addThenFail_table
#print axioms Probes.addThenFail_committed
#print axioms Probes.addOnly_table
#print axioms Probes.addOnly_committed
#print axioms Probes.installation_agrees
#print axioms Probes.monotone_programs

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
