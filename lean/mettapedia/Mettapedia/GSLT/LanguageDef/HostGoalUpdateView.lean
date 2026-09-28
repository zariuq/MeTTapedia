import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters
import Mettapedia.GSLT.LanguageDef.MatchStepControls

/-!
# Mutation between a host goal's answers

**The setting.**  A host goal is entered in a space and delivers its answers one pull at a time.
Between its pulls other code runs, the continuation of each answer, and it may write to the space:
add an atom, or remove one.  `underWrites H react w entry` is the host goal `H` entered in the space
`entry`, with that code as a writer: after the entry and after every pull, from its own state, the
space as it stands and what the pull gave (an answer, or none), it makes its writes and moves to its
next state.  Every pull of `H` reads the space as the writes so far have left it.  The writer is
arbitrary, so it stands for any continuation and any interleaving of writes with the pulls.

**A space with its history** (`Space`).  A space keeps the revision it has reached and the log of
its writes, each with the revision it made.  `Space.view s r` is the space as of revision `r`, the
atoms added and not removed by then, in the order added; `Space.contents` is the space now.  A write
makes a new revision, so it leaves the space as of every revision already reached as it was
(`Space.view_write`, `Space.view_writes`).

**The logical update view** (`underWrites_streams`).  When a host's pull at any space its entry
space has been written over into corresponds to its pull at the entry space (`PullMatch`, under a
relation of its states), the host goal delivers under every writer what it delivers with the space
held at its entry state: the same answers within every number of pulls (`delivered`), the same
`once`, and the same collection, published within the same pulls.  Three matches meet the
condition, the three ways a match takes its snapshot when it is entered:
* `revisionMatch` pins the entry revision, and at every pull reads the space as it stands, as of
  that revision (`revisionMatch_reads`, from `Space.view_writes`);
* `rowsMatch` copies the candidates when it is entered and reads its copy;
* `answersMatch` unifies every candidate when it is entered and delivers the answers it kept.

Under every writer each publishes the answers of the entry state's atoms, in order, within one pull
per atom and one more, and its `once` is the first of them (`revisionMatch_update_view`,
`rowsMatch_update_view`, `answersMatch_update_view`).  With the space held at its entry state, the
pinned revision and the copied rows deliver the same answers pull for pull
(`rowsMatch_eq_revisionMatch`).  The stream laws are general: hosts whose pulls correspond have the
same `delivered`, `once` and `collect` (`delivered_eq_of_match`, `once_eq_of_match`,
`collect_eq_of_match`), and a published collection's first answer is `once`'s (`once_of_collect`).

**Controls** (over the match step's substitution store, checked by `decide`).  `threeWrites_views`:
after adding `1` and `2` and removing the `1`, the space holds `2`, and as of revision `2` it held
`1` and `2`.  For the goal `(p $x)`, against `liveMatch`, which reads the live space at each pull:
* `added_between_pulls`: over `(p a)`, a writer adds `(p b)` after the first answer; the live
  reader delivers `a` and then `b`, each snapshot match `a` alone;
* `removed_between_pulls`: over `(p a) (p b)`, a writer removes `(p b)` after the first answer; the
  live reader publishes `a` alone and loses `b`, each snapshot match publishes both;
* `removed_before_first`: over `(p a)`, a writer removes `(p a)` between the entry and the first
  pull; the live reader's `once` finds no answer, each snapshot match's is `a`;
* `liveMatch_not_update_view`: the live reader's collection under writes is not its collection with
  the space held at the entry state.

In the first two the live reader's `once` agrees with the snapshots': it is decided at the first
answer, before the continuation of any answer runs.  Only a write between the entry and the first
pull separates it, and in a depth-first machine nothing runs there.

**The C.**  The tier's match copies, when it runs, the rows its space's index offers for the
pattern that may unify with it: `rowsMatch`, over the index's candidates.  The enclosing machine's
match, where host goals run, takes one of three snapshots when it is entered: references to the
occurrences it will try (`rowsMatch`); a pinned read of the space with an occurrence ceiling, under
which later appends are invisible and a removal leaves the pinned rows readable (`revisionMatch`);
or the bindings of its matches, computed when it is entered (`answersMatch`).

**Not covered.**  The C's pinned read is invalidated by a rewrite of the space other than an append
or a removal, which the enclosing machine reports as its own outcome; the model's history only
grows, so it has no such case.  A removal names one occurrence by the revision that added it; a
removal by value must choose an occurrence, which is left to the writer.  The writer is
deterministic and every pull reads one space: concurrent writers are not modelled.  The index's
candidates and the may-unify filter change how many pulls a match takes, a candidate that does not
unify being a suspension here, not its answers; that is not stated.  The statements are per host
goal: the machine with host goals has no space, so a run of the machine over a shared space is not
stated.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals.UpdateView

open Mettapedia.GSLT.LanguageDef.HostCalls (Host Pull collect)

/-! ## A space with its history -/

/-- A write to a space: add an atom, or remove the atom that the revision `added` added. -/
inductive Write (Atom : Type) where
  | add (atom : Atom)
  | remove (added : ℕ)

/-- A space with its history: the revision it has reached, and every write it has taken, each
with the revision the write made. -/
structure Space (Atom : Type) where
  revision : ℕ
  log : List (ℕ × Write Atom)

section Space

variable {Atom : Type}

/-- The empty space, at revision `0`. -/
def Space.empty : Space Atom := ⟨0, []⟩

/-- Take one write, making the next revision. -/
def Space.write (s : Space Atom) (w : Write Atom) : Space Atom :=
  ⟨s.revision + 1, s.log ++ [(s.revision + 1, w)]⟩

/-- Take writes in order. -/
def Space.writes (s : Space Atom) (ws : List (Write Atom)) : Space Atom :=
  ws.foldl Space.write s

/-- The atoms a history holds, each with the revision that added it, in the order added. -/
def replay : List (ℕ × Atom) → List (ℕ × Write Atom) → List (ℕ × Atom)
  | held, [] => held
  | held, (revision, .add atom) :: rest => replay (held ++ [(revision, atom)]) rest
  | held, (_, .remove added) :: rest => replay (held.filter fun entry => entry.1 != added) rest

/-- The space as of revision `r`: the atoms added and not removed by then, in the order added. -/
def Space.view (s : Space Atom) (r : ℕ) : List Atom :=
  (replay [] (s.log.filter fun entry => decide (entry.1 ≤ r))).map Prod.snd

/-- The space now. -/
def Space.contents (s : Space Atom) : List Atom := s.view s.revision

theorem Space.writes_append (s : Space Atom) (ws ws' : List (Write Atom)) :
    (s.writes ws).writes ws' = s.writes (ws ++ ws') := by
  simp [Space.writes, List.foldl_append]

/-- **A write does not change the past.**  It makes a new revision, so the space as of any
revision already reached stays as it was. -/
theorem Space.view_write (s : Space Atom) (w : Write Atom) {r : ℕ} (reached : r ≤ s.revision) :
    (s.write w).view r = s.view r := by
  have later : ¬ s.revision + 1 ≤ r := by omega
  simp [Space.view, Space.write, List.filter_append, later]

/-- Writes do not change the space as of a revision already reached. -/
theorem Space.view_writes (s : Space Atom) (ws : List (Write Atom)) {r : ℕ}
    (reached : r ≤ s.revision) : (s.writes ws).view r = s.view r := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [Space.writes, List.foldl_cons] at ih ⊢
    rw [ih (s.write w) (by simp only [Space.write]; omega), s.view_write w reached]

end Space

/-! ## Host goals under writes -/

/-- A host whose `start` reads the space the goal is entered in, and whose `pull` may read the
space as it stands when the pull is made. -/
structure SpaceHost (Atom Goal HState Answer : Type) where
  start : Space Atom → Goal → HState
  pull : Space Atom → HState → Pull HState Answer

section Hosts

variable {Atom Goal HState Answer : Type}

/-- **A host goal while the code between its pulls writes.**  The goal is entered in the space
`entry`, which the host reads to start.  The code that runs after the entry and after every pull,
before the next pull (the continuation of an answer, or anything else), is a writer: from its state
`W`, the space as it stands and what the pull gave (an answer, or none; none after the entry), it
makes its writes and moves to its next state.  Every pull of `H` reads the space as the writes so
far have left it. -/
def underWrites (H : SpaceHost Atom Goal HState Answer) {W : Type}
    (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W)
    (entry : Space Atom) : Host Goal (Space Atom × W × HState) Answer where
  start goal := (entry.writes (react w entry none).2, (react w entry none).1, H.start entry goal)
  pull state :=
    match H.pull state.1 state.2.2 with
    | .done => .done
    | .yield a h =>
      .yield a (state.1.writes (react state.2.1 state.1 (some a)).2,
        (react state.2.1 state.1 (some a)).1, h)
    | .suspend h =>
      .suspend (state.1.writes (react state.2.1 state.1 none).2,
        (react state.2.1 state.1 none).1, h)

/-- A pull with its states relabelled. -/
def relabel {S T : Type} (f : S → T) : Pull S Answer → Pull T Answer
  | .done => .done
  | .yield a h => .yield a (f h)
  | .suspend h => .suspend (f h)

/-- Pulls that correspond: both done, the same answer with related states, or both suspended with
related states. -/
inductive PullMatch {S₁ S₂ : Type} (R : S₁ → S₂ → Prop) : Pull S₁ Answer → Pull S₂ Answer → Prop
  | done : PullMatch R .done .done
  | yield {a : Answer} {h₁ : S₁} {h₂ : S₂} : R h₁ h₂ → PullMatch R (.yield a h₁) (.yield a h₂)
  | suspend {h₁ : S₁} {h₂ : S₂} : R h₁ h₂ → PullMatch R (.suspend h₁) (.suspend h₂)

theorem PullMatch.refl {S : Type} : ∀ p : Pull S Answer, PullMatch (· = ·) p p
  | .done => .done
  | .yield _ _ => .yield rfl
  | .suspend _ => .suspend rfl

theorem PullMatch.map {S₁ S₂ T₁ T₂ : Type} {R : S₁ → S₂ → Prop} {R' : T₁ → T₂ → Prop}
    {f : S₁ → T₁} {g : S₂ → T₂} (preserves : ∀ x y, R x y → R' (f x) (g y)) :
    ∀ {p : Pull S₁ Answer} {q : Pull S₂ Answer}, PullMatch R p q →
      PullMatch R' (relabel f p) (relabel g q)
  | _, _, .done => .done
  | _, _, .yield related => .yield (preserves _ _ related)
  | _, _, .suspend related => .suspend (preserves _ _ related)

theorem PullMatch.of_relabel {S T : Type} {R : T → S → Prop} {f : S → T} (image : ∀ x, R (f x) x) :
    ∀ p : Pull S Answer, PullMatch R (relabel f p) p
  | .done => .done
  | .yield _ h => .yield (image h)
  | .suspend h => .suspend (image h)

section Streams

variable {S₁ S₂ : Type} {pull₁ : S₁ → Pull S₁ Answer} {pull₂ : S₂ → Pull S₂ Answer}
  {R : S₁ → S₂ → Prop}

/-- Hosts whose pulls correspond deliver the same answers within every number of pulls. -/
theorem delivered_eq_of_match (step : ∀ h₁ h₂, R h₁ h₂ → PullMatch R (pull₁ h₁) (pull₂ h₂)) :
    ∀ (n : ℕ) {h₁ : S₁} {h₂ : S₂}, R h₁ h₂ → delivered pull₁ n h₁ = delivered pull₂ n h₂
  | 0, _, _, _ => rfl
  | n + 1, h₁, h₂, related => by
    have matched := step h₁ h₂ related
    simp only [delivered]
    generalize pull₁ h₁ = p₁ at matched ⊢
    generalize pull₂ h₂ = p₂ at matched ⊢
    cases matched with
    | done => rfl
    | yield next => simp only [delivered_eq_of_match step n next]
    | suspend next => exact delivered_eq_of_match step n next

/-- Their `once`s agree. -/
theorem once_eq_of_match (step : ∀ h₁ h₂, R h₁ h₂ → PullMatch R (pull₁ h₁) (pull₂ h₂)) :
    ∀ (n : ℕ) {h₁ : S₁} {h₂ : S₂}, R h₁ h₂ → once pull₁ n h₁ = once pull₂ n h₂
  | 0, _, _, _ => rfl
  | n + 1, h₁, h₂, related => by
    have matched := step h₁ h₂ related
    simp only [once]
    generalize pull₁ h₁ = p₁ at matched ⊢
    generalize pull₂ h₂ = p₂ at matched ⊢
    cases matched with
    | done => rfl
    | yield next => rfl
    | suspend next => exact once_eq_of_match step n next

/-- Their collections agree: they are published within the same pulls, with the same answers. -/
theorem collect_eq_of_match (step : ∀ h₁ h₂, R h₁ h₂ → PullMatch R (pull₁ h₁) (pull₂ h₂)) :
    ∀ (n : ℕ) {h₁ : S₁} {h₂ : S₂}, R h₁ h₂ → collect pull₁ n h₁ = collect pull₂ n h₂
  | 0, _, _, _ => rfl
  | n + 1, h₁, h₂, related => by
    have matched := step h₁ h₂ related
    simp only [collect]
    generalize pull₁ h₁ = p₁ at matched ⊢
    generalize pull₂ h₂ = p₂ at matched ⊢
    cases matched with
    | done => rfl
    | yield next => simp only [collect_eq_of_match step n next]
    | suspend next => exact collect_eq_of_match step n next

end Streams

/-- A published collection's first answer is `once`'s. -/
theorem once_of_collect {S : Type} {pull : S → Pull S Answer} :
    ∀ {n : ℕ} {h : S} {as : List Answer}, collect pull n h = some as → once pull n h = some as.head?
  | 0, _, _, published => by simp [collect] at published
  | n + 1, h, as, published => by
    cases pulled : pull h with
    | done =>
      simp only [collect, pulled, Option.some.injEq] at published
      subst published
      simp [once, pulled]
    | yield a h' =>
      simp only [collect, pulled, Option.map_eq_some_iff] at published
      obtain ⟨rest, -, rfl⟩ := published
      simp [once, pulled]
    | suspend h' =>
      simp only [collect, pulled] at published
      simp only [once, pulled]
      exact once_of_collect published

/-- The states of the host goal under writes that correspond to states of the host with the space
held at its entry state: the space is the entry space written over, and the host's own states are
related by `R`. -/
def Written (entry : Space Atom) {W : Type} (R : HState → HState → Prop)
    (state : Space Atom × W × HState) (h : HState) : Prop :=
  (∃ ws, state.1 = entry.writes ws) ∧ R state.2.2 h

/-- **Pulls that read the entry state.**  If the host's pull at any space the entry space has been
written over into corresponds to its pull at the entry space, then under any writer the host goal's
pulls correspond to its pulls with the space held at the entry state. -/
theorem underWrites_matches (H : SpaceHost Atom Goal HState Answer) (entry : Space Atom)
    {W : Type} (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W)
    (R : HState → HState → Prop)
    (reads : ∀ ws h h', R h h' → PullMatch R (H.pull (entry.writes ws) h) (H.pull entry h')) :
    ∀ state h, Written entry R state h →
      PullMatch (Written entry R) ((underWrites H react w entry).pull state) (H.pull entry h) := by
  rintro ⟨space, v, h⟩ h' ⟨⟨ws, written⟩, related⟩
  dsimp only at written related
  subst written
  have matched := reads ws h h' related
  simp only [underWrites]
  generalize H.pull (entry.writes ws) h = p₁ at matched ⊢
  generalize H.pull entry h' = p₂ at matched ⊢
  cases matched with
  | done => exact .done
  | yield next => exact .yield ⟨⟨_, Space.writes_append entry ws _⟩, next⟩
  | suspend next => exact .suspend ⟨⟨_, Space.writes_append entry ws _⟩, next⟩

/-- **The logical update view.**  For such a host, under any writer, the host goal delivers the
answers it delivers with the space held at its entry state: the same answers within every number
of pulls, the same `once`, and the same collection. -/
theorem underWrites_streams (H : SpaceHost Atom Goal HState Answer) (entry : Space Atom)
    {W : Type} (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W)
    (R : HState → HState → Prop)
    (reads : ∀ ws h h', R h h' → PullMatch R (H.pull (entry.writes ws) h) (H.pull entry h'))
    (goal : Goal) (starts : R (H.start entry goal) (H.start entry goal)) (n : ℕ) :
    delivered (underWrites H react w entry).pull n ((underWrites H react w entry).start goal) =
        delivered (H.pull entry) n (H.start entry goal) ∧
      once (underWrites H react w entry).pull n ((underWrites H react w entry).start goal) =
        once (H.pull entry) n (H.start entry goal) ∧
      collect (underWrites H react w entry).pull n ((underWrites H react w entry).start goal) =
        collect (H.pull entry) n (H.start entry goal) := by
  have step := underWrites_matches H entry react w R reads
  have start : Written entry R ((underWrites H react w entry).start goal) (H.start entry goal) :=
    ⟨⟨(react w entry none).2, rfl⟩, starts⟩
  exact ⟨delivered_eq_of_match step n start, once_eq_of_match step n start,
    collect_eq_of_match step n start⟩

/-! ## Matches -/

section Matches

variable (answer : Goal → Atom → Option Answer)

/-- The pull of a match at position `i` of its candidates: exhausted, the answer of a candidate
that unifies, or a candidate that does not. -/
def nextCandidate (goal : Goal) (candidates : List Atom) (i : ℕ) : Pull ℕ Answer :=
  match candidates[i]? with
  | none => .done
  | some atom =>
    match answer goal atom with
    | some a => .yield a (i + 1)
    | none => .suspend (i + 1)

/-- A scan publishes the answers of the candidates it has not passed, one pull per candidate and
one more. -/
theorem collect_scan (goal : Goal) (xs : List Atom) :
    ∀ (ys : List Atom) (m i : ℕ), xs.drop i = ys → ys.length ≤ m →
      collect (nextCandidate answer goal xs) (m + 1) i = some (ys.filterMap (answer goal))
  | [], m, i, dropped, _ => by
    have past : xs[i]? = none := List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp dropped)
    simp [collect, nextCandidate, past]
  | y :: ys, m, i, dropped, fits => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at fits; omega⟩
    have found : xs[i]? = some y := by
      have first := congrArg (·[0]?) dropped
      simpa [List.getElem?_drop] using first
    have rest : xs.drop (i + 1) = ys := by
      have tail := congrArg (List.drop 1) dropped
      simpa [List.drop_drop, Nat.add_comm] using tail
    have later := collect_scan goal xs ys m (i + 1) rest (by simp at fits; omega)
    rw [collect]
    cases unifies : answer goal y with
    | none =>
      simp only [nextCandidate, found, unifies, List.filterMap_cons_none unifies]
      exact later
    | some a =>
      simp only [nextCandidate, found, unifies, List.filterMap_cons_some unifies]
      rw [later]
      rfl

/-- **The match with a pinned revision.**  It enters the goal at the space's revision and, at every
pull, reads the space's history as of that revision: its snapshot is the revision, and it reads the
space as it stands, not a copy. -/
def revisionMatch : SpaceHost Atom Goal (Goal × ℕ × ℕ) Answer where
  start space goal := (goal, space.revision, 0)
  pull space state :=
    relabel (fun i => (state.1, state.2.1, i))
      (nextCandidate answer state.1 (space.view state.2.1) state.2.2)

/-- **The match with copied rows.**  It copies the candidates when the goal is entered and reads
only its copy. -/
def rowsMatch : SpaceHost Atom Goal (Goal × List Atom × ℕ) Answer where
  start space goal := (goal, space.contents, 0)
  pull _ state :=
    relabel (fun i => (state.1, state.2.1, i)) (nextCandidate answer state.1 state.2.1 state.2.2)

/-- **The match with answers computed at entry.**  It unifies every candidate when the goal is
entered, keeps the answers, and delivers the next at each pull. -/
def answersMatch : SpaceHost Atom Goal (List Answer) Answer where
  start space goal := space.contents.filterMap (answer goal)
  pull _ answers :=
    match answers with
    | [] => .done
    | a :: rest => .yield a rest

/-- **A match that reads the live space**, as it stands at each pull. -/
def liveMatch : SpaceHost Atom Goal (Goal × ℕ) Answer where
  start _ goal := (goal, 0)
  pull space state := relabel (fun i => (state.1, i)) (nextCandidate answer state.1 space.contents state.2)

/-- The pinned revision reads, at any space the entry space has been written over into, what it
reads at the entry space. -/
theorem revisionMatch_reads (entry : Space Atom) (ws : List (Write Atom)) (h h' : Goal × ℕ × ℕ)
    (related : h = h' ∧ h.2.1 ≤ entry.revision) :
    PullMatch (fun h h' : Goal × ℕ × ℕ => h = h' ∧ h.2.1 ≤ entry.revision)
      ((revisionMatch answer).pull (entry.writes ws) h) ((revisionMatch answer).pull entry h') := by
  obtain ⟨rfl, reached⟩ := related
  obtain ⟨goal, r, i⟩ := h
  simp only [revisionMatch]
  rw [entry.view_writes ws reached]
  exact PullMatch.map (fun x y same => ⟨by rw [same], reached⟩) (PullMatch.refl _)

/-- **The logical update view of the pinned revision.**  Under any writer, it delivers what it
delivers with the space held at the entry state: the same answers within every number of pulls,
the same `once`, the same collection. -/
theorem revisionMatch_streams (entry : Space Atom) {W : Type}
    (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W) (goal : Goal)
    (n : ℕ) :
    delivered (underWrites (revisionMatch answer) react w entry).pull n
        ((underWrites (revisionMatch answer) react w entry).start goal) =
        delivered ((revisionMatch answer).pull entry) n ((revisionMatch answer).start entry goal) ∧
      once (underWrites (revisionMatch answer) react w entry).pull n
          ((underWrites (revisionMatch answer) react w entry).start goal) =
        once ((revisionMatch answer).pull entry) n ((revisionMatch answer).start entry goal) ∧
      collect (underWrites (revisionMatch answer) react w entry).pull n
          ((underWrites (revisionMatch answer) react w entry).start goal) =
        collect ((revisionMatch answer).pull entry) n ((revisionMatch answer).start entry goal) :=
  underWrites_streams (revisionMatch answer) entry react w
    (fun h h' => h = h' ∧ h.2.1 ≤ entry.revision) (revisionMatch_reads answer entry) goal
    ⟨rfl, Nat.le_refl _⟩ n

/-- The copied rows read the same at any space. -/
theorem rowsMatch_streams (entry : Space Atom) {W : Type}
    (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W) (goal : Goal)
    (n : ℕ) :
    delivered (underWrites (rowsMatch answer) react w entry).pull n
        ((underWrites (rowsMatch answer) react w entry).start goal) =
        delivered ((rowsMatch answer).pull entry) n ((rowsMatch answer).start entry goal) ∧
      once (underWrites (rowsMatch answer) react w entry).pull n
          ((underWrites (rowsMatch answer) react w entry).start goal) =
        once ((rowsMatch answer).pull entry) n ((rowsMatch answer).start entry goal) ∧
      collect (underWrites (rowsMatch answer) react w entry).pull n
          ((underWrites (rowsMatch answer) react w entry).start goal) =
        collect ((rowsMatch answer).pull entry) n ((rowsMatch answer).start entry goal) :=
  underWrites_streams (rowsMatch answer) entry react w (· = ·)
    (fun _ h _ same => by subst same; exact PullMatch.refl _) goal rfl n

/-- The answers computed at entry are delivered the same at any space. -/
theorem answersMatch_streams (entry : Space Atom) {W : Type}
    (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W) (goal : Goal)
    (n : ℕ) :
    delivered (underWrites (answersMatch answer) react w entry).pull n
        ((underWrites (answersMatch answer) react w entry).start goal) =
        delivered ((answersMatch answer).pull entry) n ((answersMatch answer).start entry goal) ∧
      once (underWrites (answersMatch answer) react w entry).pull n
          ((underWrites (answersMatch answer) react w entry).start goal) =
        once ((answersMatch answer).pull entry) n ((answersMatch answer).start entry goal) ∧
      collect (underWrites (answersMatch answer) react w entry).pull n
          ((underWrites (answersMatch answer) react w entry).start goal) =
        collect ((answersMatch answer).pull entry) n ((answersMatch answer).start entry goal) :=
  underWrites_streams (answersMatch answer) entry react w (· = ·)
    (fun _ h _ same => by subst same; exact PullMatch.refl _) goal rfl n

/-- With the space held at its entry state, the pinned revision publishes the answers of the
entry state's atoms, in order, within one pull per atom and one more. -/
theorem revisionMatch_collect_entry (entry : Space Atom) (goal : Goal) :
    collect ((revisionMatch answer).pull entry) (entry.contents.length + 1)
        ((revisionMatch answer).start entry goal) =
      some (entry.contents.filterMap (answer goal)) := by
  have same : collect ((revisionMatch answer).pull entry) (entry.contents.length + 1)
        ((revisionMatch answer).start entry goal) =
      collect (nextCandidate answer goal entry.contents) (entry.contents.length + 1) 0 :=
    collect_eq_of_match (R := fun h i => h = (goal, entry.revision, i))
      (fun h i related => by
        subst related
        exact PullMatch.of_relabel (R := fun h i => h = (goal, entry.revision, i))
          (f := fun j => (goal, entry.revision, j)) (fun _ => rfl) _) _ rfl
  rw [same]
  exact collect_scan answer goal entry.contents entry.contents _ 0 rfl (Nat.le_refl _)

/-- So do the copied rows. -/
theorem rowsMatch_collect_entry (entry : Space Atom) (goal : Goal) :
    collect ((rowsMatch answer).pull entry) (entry.contents.length + 1)
        ((rowsMatch answer).start entry goal) =
      some (entry.contents.filterMap (answer goal)) := by
  have same : collect ((rowsMatch answer).pull entry) (entry.contents.length + 1)
        ((rowsMatch answer).start entry goal) =
      collect (nextCandidate answer goal entry.contents) (entry.contents.length + 1) 0 :=
    collect_eq_of_match (R := fun h i => h = (goal, entry.contents, i))
      (fun h i related => by
        subst related
        exact PullMatch.of_relabel (R := fun h i => h = (goal, entry.contents, i))
          (f := fun j => (goal, entry.contents, j)) (fun _ => rfl) _) _ rfl
  rw [same]
  exact collect_scan answer goal entry.contents entry.contents _ 0 rfl (Nat.le_refl _)

/-- A list of kept answers is published within one pull per answer and one more. -/
theorem answersMatch_collect_list (entry : Space Atom) :
    ∀ (as : List Answer) (m : ℕ), as.length ≤ m →
      collect ((answersMatch answer).pull entry) (m + 1) as = some as
  | [], _, _ => rfl
  | a :: as, m, fits => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at fits; omega⟩
    have later := answersMatch_collect_list entry as m (by simp at fits; omega)
    rw [collect]
    show (collect ((answersMatch answer).pull entry) (m + 1) as).map (a :: ·) = some (a :: as)
    rw [later]
    rfl

/-- And so do the answers computed at entry. -/
theorem answersMatch_collect_entry (entry : Space Atom) (goal : Goal) :
    collect ((answersMatch answer).pull entry) (entry.contents.length + 1)
        ((answersMatch answer).start entry goal) =
      some (entry.contents.filterMap (answer goal)) :=
  answersMatch_collect_list answer entry _ _ (List.length_filterMap_le _ _)

/-- **The answers are the entry state's.**  Under any writer, the pinned revision publishes the
answers of the entry state's atoms, in order, within one pull per atom and one more, and its
`once` is the first of them. -/
theorem revisionMatch_update_view (entry : Space Atom) {W : Type}
    (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W) (goal : Goal) :
    collect (underWrites (revisionMatch answer) react w entry).pull (entry.contents.length + 1)
        ((underWrites (revisionMatch answer) react w entry).start goal) =
        some (entry.contents.filterMap (answer goal)) ∧
      once (underWrites (revisionMatch answer) react w entry).pull (entry.contents.length + 1)
          ((underWrites (revisionMatch answer) react w entry).start goal) =
        some (entry.contents.filterMap (answer goal)).head? := by
  have collected := (revisionMatch_streams answer entry react w goal _).2.2.trans
    (revisionMatch_collect_entry answer entry goal)
  exact ⟨collected, once_of_collect collected⟩

/-- So for the copied rows. -/
theorem rowsMatch_update_view (entry : Space Atom) {W : Type}
    (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W) (goal : Goal) :
    collect (underWrites (rowsMatch answer) react w entry).pull (entry.contents.length + 1)
        ((underWrites (rowsMatch answer) react w entry).start goal) =
        some (entry.contents.filterMap (answer goal)) ∧
      once (underWrites (rowsMatch answer) react w entry).pull (entry.contents.length + 1)
          ((underWrites (rowsMatch answer) react w entry).start goal) =
        some (entry.contents.filterMap (answer goal)).head? := by
  have collected := (rowsMatch_streams answer entry react w goal _).2.2.trans
    (rowsMatch_collect_entry answer entry goal)
  exact ⟨collected, once_of_collect collected⟩

/-- And for the answers computed at entry. -/
theorem answersMatch_update_view (entry : Space Atom) {W : Type}
    (react : W → Space Atom → Option Answer → W × List (Write Atom)) (w : W) (goal : Goal) :
    collect (underWrites (answersMatch answer) react w entry).pull (entry.contents.length + 1)
        ((underWrites (answersMatch answer) react w entry).start goal) =
        some (entry.contents.filterMap (answer goal)) ∧
      once (underWrites (answersMatch answer) react w entry).pull (entry.contents.length + 1)
          ((underWrites (answersMatch answer) react w entry).start goal) =
        some (entry.contents.filterMap (answer goal)).head? := by
  have collected := (answersMatch_streams answer entry react w goal _).2.2.trans
    (answersMatch_collect_entry answer entry goal)
  exact ⟨collected, once_of_collect collected⟩

/-- With the space held at its entry state, the pinned revision and the copied rows deliver the
same answers, pull for pull. -/
theorem rowsMatch_eq_revisionMatch (entry : Space Atom) (goal : Goal) (n : ℕ) :
    delivered ((rowsMatch answer).pull entry) n ((rowsMatch answer).start entry goal) =
      delivered ((revisionMatch answer).pull entry) n ((revisionMatch answer).start entry goal) := by
  refine delivered_eq_of_match (R := fun (h₁ : Goal × List Atom × ℕ) (h₂ : Goal × ℕ × ℕ) =>
    h₁.1 = h₂.1 ∧ h₁.2.1 = entry.contents ∧ h₂.2.1 = entry.revision ∧ h₁.2.2 = h₂.2.2)
    ?_ n ⟨rfl, rfl, rfl, rfl⟩
  rintro ⟨goal₁, rows, i⟩ ⟨goal₂, r, j⟩ ⟨same, copied, pinned, index⟩
  dsimp only at same copied pinned index
  subst same copied pinned index
  exact PullMatch.map (fun x y same => ⟨rfl, rfl, rfl, same⟩) (PullMatch.refl _)

end Matches

end Hosts

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.LP (Term Subst)
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies (StoreAlgebra)
open Mettapedia.GSLT.LanguageDef.MatchSteps (candidate)
open Mettapedia.GSLT.LanguageDef.MatchSteps.Controls (msig L store noPrim noTest sym app Shape shape)
open Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls
  (substitutionStoreByFuel substitutionStoreByFuel_eq)

/-! ### The space -/

/-- Three writes over natural-number atoms: add `1`, add `2`, remove the `1`. -/
def threeWrites : Space ℕ := Space.empty.writes [.add 1, .add 2, .remove 1]

/-- **The space keeps its past.**  After the removal the space holds `2` alone, while as of
revision `2` it held `1` and `2`, as of revision `1` only `1`, and at first nothing. -/
theorem threeWrites_views :
    threeWrites.contents = [2] ∧ threeWrites.view 2 = [1, 2] ∧ threeWrites.view 1 = [1] ∧
      threeWrites.view 0 = [] := by
  decide

/-! ### Matches over the substitution store -/

/-- A stored atom of the match step's controls. -/
abbrev Fact := MatchSteps.Atom L

/-- `(p a)`. -/
def pa : Fact := ⟨0, app .p (sym "a")⟩

/-- `(p b)`. -/
def pb : Fact := ⟨0, app .p (sym "b")⟩

/-- A goal: a pattern and the store it is matched in. -/
abbrev MGoal := Term msig × (Subst msig × ℕ)

/-- The answer of a candidate: the store after the pattern meets a fresh copy of the atom. -/
def meet (S : StoreAlgebra (Term msig) (Subst msig × ℕ) Empty) (goal : MGoal) (atom : Fact) :
    Option (Subst msig × ℕ) :=
  candidate S atom goal.1 goal.2

/-- The goal `(p $x)`, in the empty store with the fresh supply at `10`. -/
def px : MGoal := (app .p (.var 0), MatchSteps.Controls.start)

/-- What an answer binds `$x` to. -/
def readX (σ : Subst msig × ℕ) : Shape := shape (σ.1.applyTerm (.var 0))

/-- The writer that makes the writes `first` after the first pull and none otherwise; its state
counts its turns, the entry's being the `0`-th. -/
def afterFirst (first : List (Write Fact)) :
    ℕ → Space Fact → Option (Subst msig × ℕ) → ℕ × List (Write Fact)
  | 1, _, _ => (2, first)
  | k, _, _ => (k + 1, [])

/-- The writer that makes the writes `ws` after the entry, before the first pull, and none
after. -/
def atEntry (ws : List (Write Fact)) :
    ℕ → Space Fact → Option (Subst msig × ℕ) → ℕ × List (Write Fact)
  | 0, _, _ => (1, ws)
  | k, _, _ => (k + 1, [])

/-- The space `(p a)`. -/
def onlyA : Space Fact := Space.empty.writes [.add pa]

/-- The space `(p a) (p b)`: `(p b)` is added by revision `2`. -/
def bothAB : Space Fact := Space.empty.writes [.add pa, .add pb]

/-- **An atom added between pulls.**  Over `(p a)`, the goal `(p $x)` with a writer that adds
`(p b)` after the first answer: the live reader delivers `a` and then `b`; the pinned revision,
the copied rows and the answers computed at entry deliver `a` alone, the entry state's answer.
The live reader's `once` is still `a`: it is decided at the first answer, before any write. -/
theorem added_between_pulls :
    (delivered (underWrites (liveMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).pull 3
        ((underWrites (liveMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).start px)).map
        readX = [.const "a", .const "b"] ∧
      (delivered (underWrites (revisionMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).pull 3
        ((underWrites (revisionMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).start px)).map
        readX = [.const "a"] ∧
      (delivered (underWrites (rowsMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).pull 3
        ((underWrites (rowsMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).start px)).map
        readX = [.const "a"] ∧
      (delivered (underWrites (answersMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).pull 3
        ((underWrites (answersMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).start px)).map
        readX = [.const "a"] ∧
      (once (underWrites (liveMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).pull 3
        ((underWrites (liveMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).start px)).map
        (Option.map readX) = some (some (.const "a")) := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- **An atom removed between pulls.**  Over `(p a) (p b)`, the goal `(p $x)` with a writer that
removes `(p b)` after the first answer: the live reader is exhausted after `a` and loses `b`; the
pinned revision, the copied rows and the answers computed at entry publish `a` and `b`. -/
theorem removed_between_pulls :
    (collect (underWrites (liveMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).pull 3
        ((underWrites (liveMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).start px)).map
        (List.map readX) = some [.const "a"] ∧
      (collect (underWrites (revisionMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).pull 3
        ((underWrites (revisionMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).start
          px)).map (List.map readX) = some [.const "a", .const "b"] ∧
      (collect (underWrites (rowsMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).pull 3
        ((underWrites (rowsMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).start px)).map
        (List.map readX) = some [.const "a", .const "b"] ∧
      (collect (underWrites (answersMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).pull 3
        ((underWrites (answersMatch (meet store)) (afterFirst [.remove 2]) 0 bothAB).start
          px)).map (List.map readX) = some [.const "a", .const "b"] := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- **`once` under a write before the first pull.**  Over `(p a)`, a writer that removes `(p a)`
after the entry and before the first pull: the live reader's `once` finds no answer, and the three
snapshot matches' `once` is `a`, the entry state's.  Nothing runs there in a depth-first machine,
where the entry's host node is pulled at once; an interleaving scheduler may run other work
there. -/
theorem removed_before_first :
    (once (underWrites (liveMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).pull 2
        ((underWrites (liveMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).start px)).map
        (Option.map readX) = some none ∧
      (once (underWrites (revisionMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).pull 2
        ((underWrites (revisionMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).start px)).map
        (Option.map readX) = some (some (.const "a")) ∧
      (once (underWrites (rowsMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).pull 2
        ((underWrites (rowsMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).start px)).map
        (Option.map readX) = some (some (.const "a")) ∧
      (once (underWrites (answersMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).pull 2
        ((underWrites (answersMatch (meet store)) (atEntry [.remove 1]) 0 onlyA).start px)).map
        (Option.map readX) = some (some (.const "a")) := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- **The live reader has no logical update view.**  Under the writer that adds `(p b)` after the
first answer, its collection is not its collection with the space held at the entry state. -/
theorem liveMatch_not_update_view :
    collect (underWrites (liveMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).pull 3
        ((underWrites (liveMatch (meet store)) (afterFirst [.add pb]) 0 onlyA).start px) ≠
      collect ((liveMatch (meet store)).pull onlyA) 3 ((liveMatch (meet store)).start onlyA px) := by
  intro same
  have read := congrArg (Option.map (List.map readX)) same
  revert read
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.HostGoals.UpdateView
