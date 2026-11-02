import Mettapedia.Machines.NestedQuerySchedule

/-!
# Nested queries whose bodies write: when the snapshot answers

`NestedQuerySchedule` runs a nested query two ways.  The source schedule reads
a level when its branch is reached, after the bodies of the branches before it
have written; the fused schedule joins every level against the store the query
began with and then runs the bodies in the join's order.  The two are equal
when no body writes.  Here they are equal under a weaker condition, and the
changes of the fused bodies may then be made in another order.

* **Only what is read again matters.**  The first level is read once, before
  any body runs.  The schedules are equal, store and answers and their order
  included, whenever some invariant holds of the initial store, survives
  every body of the join, and makes every later read of the snapshot run read
  as it did on the initial store (`source_eq_fused`).  The later reads are the
  levels after the first, each under a prefix the snapshot join reaches
  (`innerReads`).  No body is ever restricted by what the first level reads.
* **Nesting is conjunction.**  A query whose body is another nested query is
  one nested query over the levels of both, with live reads
  (`source_append`).
* **Primitive changes.**  A body adds a row (one more copy, `Effect.add`),
  inserts it (present once, `Effect.insert`), or removes every row that a
  pattern deletes (`Effect.remove`).  The schedules are equal when no later
  read event accepts an added row and none accepts a row of the initial store
  that a removal deletes (`source_eq_fused_of_keepsReads`).  These conditions
  name finitely many rows and read events, so they are decided after the
  snapshot join, before any change is made.
* **Any order of the changes.**  Read as bags, the changes act on bags
  (`Effect.coe_apply`).  Additions commute with additions, insertions with
  insertions, removals with removals, and an addition or insertion with a
  removal that does not delete its row (`Effect.act_comm`).  When every two
  changes of a run commute, every permutation of them leaves the same bag
  (`Effect.foldl_apply_perm`).
* **The native run.**  Join against the snapshot, check both conditions, and
  make the changes in another order, all removals first: the answers and the
  final bag are the source schedule's (`native_eq_source`, `nativeRun_sound`).
  A run whose check fails has changed nothing, so answering by the source
  schedule instead is the source schedule (`withFallback_eq`).
* **Negated reads.**  A body that acts only when no row passes a test, read
  live, is the body whose test is read on the snapshot, when no change touches
  a row the test reads under any joined choice (`source_unless_eq_fused`,
  `native_eq_source_unless`): stratification, decided on the actual reads.
* **Branching on a negated read.**  A body choosing between two branches, each
  with its own changes and answers, by whether a row passes a test, is the body
  whose branch is decided on the snapshot, when no change of either branch
  touches a row the test or a later level reads (`source_cond_eq_fused`,
  `native_eq_source_cond`); a test reading what its own branch writes is decided
  otherwise live (`cond_reads_target_differs`).

Controls: a body that writes a relation a later level reads answers
differently for two orders of the same stored rows, so no snapshot answers as
it does, and the check rejects it (`Controls.live_answers_depend_on_order`,
`Controls.fused_differs`, `Controls.check_rejects`); a body may write what the
first level reads (`Controls.first_level_written`); a body writing the
relation it reads, at a level that later reads never ask for, passes the check
(`Controls.levels_pass`); the step schedule answers the same over both orders
of the rows (`Controls.fused_order_free`); a body adding the row its negated
test reads answers differently live and on the snapshot, and the check
rejects it (`Controls.negated_read_live`, `Controls.negated_check_rejects`);
a removal that meets no later pattern still deletes an open row a later
pattern reads, and the check rejects it (`Controls.open_row_removal`,
`Controls.open_row_check_rejects`); an addition and a removal of the same row
do not commute (`Controls.add_remove_not_comm`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NestedQueryEffects

open NestedQuerySchedule

universe u v w
variable {Row : Type u} {Answer : Type v}

/-! ## Sequencing -/

theorem sequence_append {Item : Type w} (branch : Item → List Row → List Row × List Answer) :
    ∀ (first second : List Item) (acc : List Row × List Answer),
      NestedQuerySchedule.sequence branch (first ++ second) acc =
        NestedQuerySchedule.sequence branch second (NestedQuerySchedule.sequence branch first acc)
  | [], _, _ => rfl
  | item :: first, second, acc => by
      simp only [List.cons_append, NestedQuerySchedule.sequence]
      exact sequence_append branch first second _

/-- A run's answers are appended to those given before it. -/
theorem sequence_answers {Item : Type w} (branch : Item → List Row → List Row × List Answer) :
    ∀ (items : List Item) (store : List Row) (answers : List Answer),
      NestedQuerySchedule.sequence branch items (store, answers) =
        ((NestedQuerySchedule.sequence branch items (store, [])).1,
          answers ++ (NestedQuerySchedule.sequence branch items (store, [])).2)
  | [], store, answers => by simp [NestedQuerySchedule.sequence]
  | item :: items, store, answers => by
      simp only [NestedQuerySchedule.sequence, List.nil_append]
      rw [sequence_answers branch items _ (answers ++ _),
        sequence_answers branch items _ (branch item store).2]
      simp [List.append_assoc]

/-- A property of the store that every branch keeps holds after the run. -/
theorem sequence_preserves {Item : Type w} (branch : Item → List Row → List Row × List Answer)
    (P : List Row → Prop) :
    ∀ (items : List Item),
      (∀ item ∈ items, ∀ store, P store → P (branch item store).1) →
      ∀ (acc : List Row × List Answer), P acc.1 →
        P (NestedQuerySchedule.sequence branch items acc).1
  | [], _, _, h => h
  | item :: items, keeps, acc, h => by
      simp only [NestedQuerySchedule.sequence]
      exact sequence_preserves branch P items
        (fun i hi => keeps i (List.mem_cons_of_mem _ hi)) _
        (keeps item List.mem_cons_self acc.1 h)

/-! ## Read events -/

/-- The reads a snapshot run makes below `chosen`: each level, with the prefix
it is read under. -/
def readsBelow (store : List Row) : List (Level Row) → List Row → List (Level Row × List Row)
  | [], _ => []
  | level :: rest, chosen =>
      (level, chosen) :: (store.filter (level chosen)).flatMap
        fun row => readsBelow store rest (chosen ++ [row])

/-- The reads of a snapshot run after its first level: every read a body can
run before. -/
def innerReads (store : List Row) (first : Level Row) (rest : List (Level Row)) :
    List (Level Row × List Row) :=
  (store.filter (first [])).flatMap fun row => readsBelow store rest [row]

/-- A store answers the given reads as `initial` does. -/
def ReadsAs (initial store : List Row) (reads : List (Level Row × List Row)) : Prop :=
  ∀ event ∈ reads, store.filter (event.1 event.2) = initial.filter (event.1 event.2)

/-- A read event below `chosen` reads one of the levels. -/
theorem readsBelow_level_mem (store : List Row) :
    ∀ (levels : List (Level Row)) (chosen : List Row) (e : Level Row × List Row),
      e ∈ readsBelow store levels chosen → e.1 ∈ levels
  | [], _, _, he => by simp [readsBelow] at he
  | level :: rest, chosen, e, he => by
      simp only [readsBelow, List.mem_cons, List.mem_flatMap] at he
      rcases he with rfl | ⟨row, _, he⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (readsBelow_level_mem store rest _ e he)

/-- **A later read reads a level after the first.** -/
theorem innerReads_level_mem {store : List Row} {first : Level Row} {rest : List (Level Row)}
    {e : Level Row × List Row} (he : e ∈ innerReads store first rest) : e.1 ∈ rest := by
  obtain ⟨row, _, he⟩ := List.mem_flatMap.mp he
  exact readsBelow_level_mem store rest [row] e he

theorem readsBelow_sub {store : List Row} {level : Level Row} {rest : List (Level Row)}
    {chosen : List Row} {row : Row} (hrow : row ∈ store.filter (level chosen)) :
    ∀ e ∈ readsBelow store rest (chosen ++ [row]),
      e ∈ readsBelow store (level :: rest) chosen :=
  fun _ he => List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨row, hrow, he⟩)

theorem join_sub {store : List Row} {level : Level Row} {rest : List (Level Row)}
    {chosen : List Row} {row : Row} (hrow : row ∈ store.filter (level chosen)) :
    ∀ c ∈ join store rest (chosen ++ [row]), c ∈ join store (level :: rest) chosen :=
  fun _ hc => by
    simp only [join, joinWith, id] at hc ⊢
    exact List.mem_flatMap.mpr ⟨row, hrow, hc⟩

section Fusion

variable (body : Body Row Answer) (initial : List Row) (Inv : List Row → Prop)
  (choices : List (List Row))

/-- The rows of one read, each followed by its branch, run as the
concatenation of the branches' joined choices. -/
theorem sequence_rows (preserve : ∀ c ∈ choices, ∀ s, Inv s → Inv (body c s).1)
    (rest : List (Level Row)) (chosen : List Row) :
    ∀ (rows : List Row),
      (∀ row ∈ rows, ∀ s, Inv s →
        source id body rest (chosen ++ [row]) s =
          NestedQuerySchedule.sequence body (join initial rest (chosen ++ [row])) (s, [])) →
      (∀ row ∈ rows, ∀ c ∈ join initial rest (chosen ++ [row]), c ∈ choices) →
      ∀ (s : List Row) (acc : List Answer), Inv s →
        NestedQuerySchedule.sequence
            (fun row store => source id body rest (chosen ++ [row]) store) rows (s, acc) =
          NestedQuerySchedule.sequence body
            (rows.flatMap fun row => join initial rest (chosen ++ [row])) (s, acc)
  | [], _, _, s, acc, _ => by simp [NestedQuerySchedule.sequence]
  | row :: rows, below, inChoices, s, acc, hs => by
      simp only [NestedQuerySchedule.sequence, List.flatMap_cons]
      rw [below row List.mem_cons_self s hs, sequence_append,
        sequence_answers body (join initial rest (chosen ++ [row])) s acc]
      apply sequence_rows preserve rest chosen rows
        (fun r hr => below r (List.mem_cons_of_mem _ hr))
        (fun r hr => inChoices r (List.mem_cons_of_mem _ hr))
      exact sequence_preserves body Inv _
        (fun c hc => preserve c (inChoices row List.mem_cons_self c hc)) (s, []) hs

/-- Below reads that agree with the snapshot, the source schedule runs the
snapshot join's choices in order. -/
theorem source_eq_sequence_join (events : List (Level Row × List Row))
    (reads : ∀ s, Inv s → ReadsAs initial s events)
    (preserve : ∀ c ∈ choices, ∀ s, Inv s → Inv (body c s).1) :
    ∀ (levels : List (Level Row)) (chosen : List Row),
      (∀ e ∈ readsBelow initial levels chosen, e ∈ events) →
      (∀ c ∈ join initial levels chosen, c ∈ choices) →
      ∀ s, Inv s → source id body levels chosen s =
        NestedQuerySchedule.sequence body (join initial levels chosen) (s, [])
  | [], chosen, _, _, s, _ => by simp [source, join, joinWith, NestedQuerySchedule.sequence]
  | level :: rest, chosen, inEvents, inChoices, s, hs => by
      have first : s.filter (level chosen) = initial.filter (level chosen) :=
        reads s hs (level, chosen) (inEvents _ List.mem_cons_self)
      simp only [source, id, first]
      have joined : join initial (level :: rest) chosen =
          (initial.filter (level chosen)).flatMap fun row => join initial rest (chosen ++ [row]) :=
        rfl
      rw [joined]
      exact sequence_rows body initial Inv choices preserve rest chosen _
        (fun row hrow s' hs' => source_eq_sequence_join events reads preserve rest
          (chosen ++ [row]) (fun e he => inEvents e (readsBelow_sub hrow e he))
          (fun c hc => inChoices c (join_sub hrow c hc)) s' hs')
        (fun row hrow c hc => inChoices c (join_sub hrow c hc)) s [] hs

/-- **Only what is read again matters.**  If some invariant holds of the
initial store, survives every body of the snapshot join, and makes every read
after the first level read as on the initial store, the source schedule is
the fused one: the same final store, and the same answers in the same order. -/
theorem source_eq_fused (first : Level Row) (rest : List (Level Row)) (start : Inv initial)
    (reads : ∀ s, Inv s → ReadsAs initial s (innerReads initial first rest))
    (preserve : ∀ c ∈ join initial (first :: rest) [], ∀ s, Inv s → Inv (body c s).1) :
    source id body (first :: rest) [] initial = fused body (first :: rest) initial := by
  simp only [source, fused, id, List.nil_append]
  have joined : join initial (first :: rest) [] =
      (initial.filter (first [])).flatMap fun row => join initial rest ([] ++ [row]) := rfl
  rw [joined]
  simp only [List.nil_append]
  have rows := sequence_rows body initial Inv (join initial (first :: rest) []) preserve rest []
    (initial.filter (first []))
    (fun row hrow s hs => by
      simpa using source_eq_sequence_join body initial Inv (join initial (first :: rest) [])
        (innerReads initial first rest) reads preserve rest [row]
        (fun e he => List.mem_flatMap.mpr ⟨row, hrow, he⟩)
        (fun c hc => join_sub (chosen := []) hrow c (by simpa using hc)) s hs)
    (fun row hrow c hc => join_sub (chosen := []) hrow c (by simpa using hc))
    initial [] start
  simpa using rows

/-- The case of bodies that leave the store alone (`fusion_admitted`) is the
invariant "the store is the initial one". -/
theorem source_eq_fused_of_preserving (first : Level Row) (rest : List (Level Row))
    (keeps : body.Preserves) :
    source id body (first :: rest) [] initial = fused body (first :: rest) initial :=
  source_eq_fused body initial (· = initial) first rest rfl
    (fun s hs => by subst hs; exact fun _ _ => rfl)
    (fun c _ s hs => by rw [keeps c s]; exact hs)

end Fusion

/-- **Nesting is conjunction**: a nested query whose body is a nested query is
one nested query over the levels of both, read live. -/
theorem source_append (order : List Row → List Row) (body : Body Row Answer) :
    ∀ (pre post : List (Level Row)) (chosen store : List Row),
      source order body (pre ++ post) chosen store =
        source order (fun chosen' store' => source order body post chosen' store') pre chosen store
  | [], _, _, _ => rfl
  | level :: rest, post, chosen, store => by
      simp only [List.cons_append, source]
      congr 1
      funext row store'
      exact source_append order body rest post (chosen ++ [row]) store'

/-! ## Primitive changes -/

/-- A primitive change a body makes to the store. -/
inductive Effect (Row : Type u) where
  /-- One more copy of a row: an addition to a bag. -/
  | add (row : Row)
  /-- A row present once: an addition to a set. -/
  | insert (row : Row)
  /-- Every row the pattern deletes goes. -/
  | remove (pattern : Row)

namespace Effect

/-- Whether the change is a removal. -/
def isRemove : Effect Row → Bool
  | .remove _ => true
  | _ => false

variable [DecidableEq Row] (deletes : Row → Row → Bool)

/-- The change made to a stored list of rows. -/
def apply : Effect Row → List Row → List Row
  | .add row, store => store ++ [row]
  | .insert row, store => if row ∈ store then store else store ++ [row]
  | .remove pattern, store => store.filter fun u => !deletes pattern u

/-- The change made to the bag of rows. -/
def act : Effect Row → Multiset Row → Multiset Row
  | .add row, m => row ::ₘ m
  | .insert row, m => m.ndinsert row
  | .remove pattern, m => m.filter fun u => deletes pattern u = false

omit [DecidableEq Row] in
theorem coe_append_singleton (store : List Row) (row : Row) :
    ((store ++ [row] : List Row) : Multiset Row) = row ::ₘ (store : Multiset Row) := by
  rw [Multiset.cons_coe]
  exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton row store)

/-- **Read as bags, the changes act on bags.** -/
theorem coe_apply (e : Effect Row) (store : List Row) :
    ((e.apply deletes store : List Row) : Multiset Row) = e.act deletes (store : Multiset Row) := by
  cases e with
  | add row => exact coe_append_singleton store row
  | insert row =>
      by_cases h : row ∈ store
      · simp only [apply, act, h, if_true]
        exact (Multiset.ndinsert_of_mem (Multiset.mem_coe.mpr h)).symm
      · simp only [apply, act, h, if_false]
        rw [coe_append_singleton, Multiset.ndinsert_of_notMem (by simpa using h)]
  | remove pattern =>
      simp only [apply, act, Multiset.filter_coe]
      congr 1
      apply List.filter_congr
      intro u _
      cases deletes pattern u <;> rfl

/-- When two changes commute. -/
def Commute : Effect Row → Effect Row → Prop
  | .add r, .insert r' => r ≠ r'
  | .insert r, .add r' => r ≠ r'
  | .add r, .remove p => deletes p r = false
  | .remove p, .add r => deletes p r = false
  | .insert r, .remove p => deletes p r = false
  | .remove p, .insert r => deletes p r = false
  | _, _ => True

instance (e e' : Effect Row) : Decidable (Commute deletes e e') := by
  cases e <;> cases e' <;> (simp only [Commute]; infer_instance)

theorem cons_ndinsert {r r' : Row} (h : r ≠ r') (m : Multiset Row) :
    r ::ₘ m.ndinsert r' = (r ::ₘ m).ndinsert r' := by
  by_cases hm : r' ∈ m
  · rw [Multiset.ndinsert_of_mem hm, Multiset.ndinsert_of_mem (Multiset.mem_cons_of_mem hm)]
  · rw [Multiset.ndinsert_of_notMem hm, Multiset.ndinsert_of_notMem, Multiset.cons_swap]
    rw [Multiset.mem_cons]
    rintro (e | e)
    · exact h e.symm
    · exact hm e

theorem ndinsert_comm (r r' : Row) (m : Multiset Row) :
    (m.ndinsert r').ndinsert r = (m.ndinsert r).ndinsert r' := by
  by_cases same : r = r'
  · rw [same]
  have notIn : ∀ {a b : Row}, a ≠ b → a ∉ m → a ∉ b ::ₘ m := fun ne nm h =>
    (Multiset.mem_cons.mp h).elim ne nm
  by_cases hr : r ∈ m <;> by_cases hr' : r' ∈ m
  · simp only [Multiset.ndinsert_of_mem hr, Multiset.ndinsert_of_mem hr']
  · rw [Multiset.ndinsert_of_notMem hr', Multiset.ndinsert_of_mem hr,
      Multiset.ndinsert_of_mem (Multiset.mem_cons_of_mem hr : r ∈ r' ::ₘ m),
      Multiset.ndinsert_of_notMem hr']
  · rw [Multiset.ndinsert_of_mem hr', Multiset.ndinsert_of_notMem hr,
      Multiset.ndinsert_of_mem (Multiset.mem_cons_of_mem hr' : r' ∈ r ::ₘ m)]
  · rw [Multiset.ndinsert_of_notMem hr', Multiset.ndinsert_of_notMem hr,
      Multiset.ndinsert_of_notMem (notIn same hr),
      Multiset.ndinsert_of_notMem (notIn (Ne.symm same) hr'), Multiset.cons_swap]

theorem ndinsert_filter {q : Row → Prop} [DecidablePred q] {r : Row} (hr : q r)
    (m : Multiset Row) : (m.filter q).ndinsert r = (m.ndinsert r).filter q := by
  by_cases hm : r ∈ m
  · rw [Multiset.ndinsert_of_mem hm,
      Multiset.ndinsert_of_mem (Multiset.mem_filter.mpr ⟨hm, hr⟩)]
  · rw [Multiset.ndinsert_of_notMem hm, Multiset.filter_cons_of_pos _ hr,
      Multiset.ndinsert_of_notMem]
    exact fun h => hm (Multiset.mem_filter.mp h).1

omit [DecidableEq Row] in
theorem filter_comm (q q' : Row → Prop) [DecidablePred q] [DecidablePred q'] (m : Multiset Row) :
    (m.filter q').filter q = (m.filter q).filter q' := by
  rw [Multiset.filter_filter, Multiset.filter_filter]
  exact Multiset.filter_congr fun _ _ => and_comm

/-- **Commuting changes commute on bags.** -/
theorem act_comm {e e' : Effect Row} (h : Commute deletes e e') (m : Multiset Row) :
    e.act deletes (e'.act deletes m) = e'.act deletes (e.act deletes m) := by
  cases e with
  | add r =>
      cases e' with
      | add r' => exact Multiset.cons_swap r r' m
      | insert r' => exact cons_ndinsert h m
      | remove p =>
          exact (Multiset.filter_cons_of_pos (p := fun u => deletes p u = false) m h).symm
  | insert r =>
      cases e' with
      | add r' => exact (cons_ndinsert (Ne.symm h) m).symm
      | insert r' => exact ndinsert_comm r r' m
      | remove p => exact ndinsert_filter (q := fun u => deletes p u = false) h m
  | remove p =>
      cases e' with
      | add r => exact Multiset.filter_cons_of_pos (p := fun u => deletes p u = false) m h
      | insert r => exact (ndinsert_filter (q := fun u => deletes p u = false) h m).symm
      | remove p' => exact filter_comm _ _ m

theorem coe_foldl_apply (effects : List (Effect Row)) (store : List Row) :
    ((effects.foldl (fun s e => e.apply deletes s) store : List Row) : Multiset Row) =
      effects.foldl (fun m e => e.act deletes m) (store : Multiset Row) := by
  induction effects generalizing store with
  | nil => rfl
  | cons e effects ih =>
      simp only [List.foldl_cons]
      rw [ih, coe_apply]

/-- **Any order of commuting changes leaves the same bag.** -/
theorem foldl_apply_perm {effects effects' : List (Effect Row)} (perm : effects.Perm effects')
    (commute : ∀ e ∈ effects, ∀ e' ∈ effects, Commute deletes e e') (store : List Row) :
    ((effects.foldl (fun s e => e.apply deletes s) store : List Row) : Multiset Row) =
      ((effects'.foldl (fun s e => e.apply deletes s) store : List Row) : Multiset Row) := by
  rw [coe_foldl_apply, coe_foldl_apply]
  exact perm.foldl_eq' (fun e he e' he' m => act_comm deletes (commute e' he' e he) m) _

end Effect

/-! ## Bodies that make primitive changes -/

section Changes

variable [DecidableEq Row] (deletes : Row → Row → Bool)

/-- A body making a choice's changes in order and answering what the choice
answers, whatever the store. -/
def effectBody (effects : List Row → List (Effect Row)) (answers : List Row → List Answer) :
    Body Row Answer :=
  fun chosen store => ((effects chosen).foldl (fun s e => e.apply deletes s) store, answers chosen)

theorem sequence_effectBody (effects : List Row → List (Effect Row))
    (answers : List Row → List Answer) :
    ∀ (choices : List (List Row)) (store : List Row) (acc : List Answer),
      NestedQuerySchedule.sequence (effectBody deletes effects answers) choices (store, acc) =
        ((choices.flatMap effects).foldl (fun s e => e.apply deletes s) store,
          acc ++ choices.flatMap answers)
  | [], store, acc => by simp [NestedQuerySchedule.sequence]
  | c :: choices, store, acc => by
      simp only [NestedQuerySchedule.sequence, effectBody]
      rw [sequence_effectBody effects answers choices]
      simp [List.flatMap_cons, List.foldl_append, List.append_assoc]

/-- No read event accepts the row. -/
def Unread (events : List (Level Row × List Row)) (row : Row) : Prop :=
  ∀ event ∈ events, event.1 event.2 row = false

instance (events : List (Level Row × List Row)) (row : Row) : Decidable (Unread events row) := by
  unfold Unread
  infer_instance

/-- A change that keeps every read event's answer: an added or inserted row
that no event accepts, or a removal that deletes no initial row an event
accepts. -/
def KeepsReads (initial : List Row) (events : List (Level Row × List Row)) :
    Effect Row → Prop
  | .add row => Unread events row
  | .insert row => Unread events row
  | .remove pattern => ∀ u ∈ initial, deletes pattern u = true → Unread events u

instance (initial : List Row) (events : List (Level Row × List Row)) (e : Effect Row) :
    Decidable (KeepsReads deletes initial events e) := by
  cases e <;> (simp only [KeepsReads]; infer_instance)

/-- What a run keeps: the events read as on the initial store, and every row
is an initial row or one no event accepts. -/
def Keeps (initial : List Row) (events : List (Level Row × List Row)) (store : List Row) :
    Prop :=
  ReadsAs initial store events ∧ ∀ u ∈ store, u ∈ initial ∨ Unread events u

omit [DecidableEq Row] in
theorem keeps_append {initial store : List Row} {events : List (Level Row × List Row)}
    {row : Row} (unread : Unread events row) (k : Keeps initial events store) :
    Keeps initial events (store ++ [row]) := by
  refine ⟨fun event he => ?_, fun u hu => ?_⟩
  · rw [List.filter_append, k.1 event he, List.filter_singleton, unread event he]
    simp
  · rcases List.mem_append.mp hu with hu | hu
    · exact k.2 u hu
    · rw [List.mem_singleton] at hu
      exact Or.inr (hu ▸ unread)

theorem keeps_apply {initial : List Row} {events : List (Level Row × List Row)}
    {e : Effect Row} (h : KeepsReads deletes initial events e) {store : List Row}
    (k : Keeps initial events store) : Keeps initial events (e.apply deletes store) := by
  cases e with
  | add row => exact keeps_append h k
  | insert row =>
      by_cases hm : row ∈ store
      · simpa [Effect.apply, hm] using k
      · simpa [Effect.apply, hm] using keeps_append h k
  | remove pattern =>
      refine ⟨fun event he => ?_, fun u hu => k.2 u (List.mem_filter.mp hu).1⟩
      simp only [Effect.apply, List.filter_filter]
      rw [← k.1 event he]
      apply List.filter_congr
      intro u hu
      cases accepted : event.1 event.2 u
      · simp
      · have notUnread : ¬ Unread events u := fun unread => by
          rw [unread event he] at accepted
          cases accepted
        rcases k.2 u hu with initialRow | unread
        · cases deleted : deletes pattern u
          · simp
          · exact absurd (h u initialRow deleted) notUnread
        · exact absurd unread notUnread

theorem keeps_foldl {initial : List Row} {events : List (Level Row × List Row)} :
    ∀ (effects : List (Effect Row)), (∀ e ∈ effects, KeepsReads deletes initial events e) →
      ∀ store, Keeps initial events store →
        Keeps initial events (effects.foldl (fun s e => e.apply deletes s) store)
  | [], _, _, k => k
  | e :: effects, h, store, k => by
      simp only [List.foldl_cons]
      exact keeps_foldl effects (fun e' he' => h e' (List.mem_cons_of_mem _ he')) _
        (keeps_apply deletes (h e List.mem_cons_self) k)

variable (effects : List Row → List (Effect Row)) (answers : List Row → List Answer)
  (first : Level Row) (rest : List (Level Row)) (initial : List Row)

/-- **Changes that keep every later read keep the schedules equal.** -/
theorem source_eq_fused_of_keepsReads
    (keep : ∀ c ∈ join initial (first :: rest) [], ∀ e ∈ effects c,
      KeepsReads deletes initial (innerReads initial first rest) e) :
    source id (effectBody deletes effects answers) (first :: rest) [] initial =
      fused (effectBody deletes effects answers) (first :: rest) initial :=
  source_eq_fused (effectBody deletes effects answers) initial
    (Keeps initial (innerReads initial first rest)) first rest
    ⟨fun _ _ => rfl, fun _ hu => Or.inl hu⟩ (fun _ k => k.1)
    (fun c hc s k => keeps_foldl deletes (effects c) (keep c hc) s k)

/-- The changes of the snapshot join, in the join's order. -/
def changes : List (Effect Row) :=
  (join initial (first :: rest) []).flatMap effects

/-- What the native run checks after its join and before any change: every
change keeps the later reads, and every two changes commute. -/
def Admissible : Prop :=
  (∀ c ∈ join initial (first :: rest) [], ∀ e ∈ effects c,
      KeepsReads deletes initial (innerReads initial first rest) e) ∧
    ∀ e ∈ changes effects first rest initial, ∀ e' ∈ changes effects first rest initial,
      Effect.Commute deletes e e'

instance : Decidable (Admissible deletes effects first rest initial) := by
  unfold Admissible
  infer_instance

/-- **The native run answers as the source schedule.**  Given the check, any
order of the changes (`native`) leaves the source schedule's final bag, and
any order of the joined choices (`enumeration`) gives its answers as a bag. -/
theorem native_eq_source (admissible : Admissible deletes effects first rest initial)
    (native : List (Effect Row)) (perm : native.Perm (changes effects first rest initial))
    (enumeration : List (List Row))
    (permChoices : enumeration.Perm (join initial (first :: rest) [])) :
    ((native.foldl (fun s e => e.apply deletes s) initial : List Row) : Multiset Row) =
        ((source id (effectBody deletes effects answers) (first :: rest) [] initial).1 :
          Multiset Row) ∧
      (enumeration.flatMap answers).Perm
        (source id (effectBody deletes effects answers) (first :: rest) [] initial).2 := by
  rw [source_eq_fused_of_keepsReads deletes effects answers first rest initial admissible.1,
    fused, sequence_effectBody]
  refine ⟨Effect.foldl_apply_perm deletes perm
    (fun e he e' he' => admissible.2 e (perm.mem_iff.mp he) e' (perm.mem_iff.mp he')) initial, ?_⟩
  simpa using permChoices.flatMap_right answers

/-- The native run: join against the snapshot, decline unless the check
passes, otherwise make every removal first, then every other change, and
answer the joined choices' answers. -/
def nativeRun : Option (List Row × List Answer) :=
  if Admissible deletes effects first rest initial then
    some (((changes effects first rest initial).filter Effect.isRemove ++
        (changes effects first rest initial).filter (fun e => !e.isRemove)).foldl
          (fun s e => e.apply deletes s) initial,
      (join initial (first :: rest) []).flatMap answers)
  else none

/-- **A native run that answers, answers as the source schedule.** -/
theorem nativeRun_sound {store : List Row} {answered : List Answer}
    (h : nativeRun deletes effects answers first rest initial = some (store, answered)) :
    (store : Multiset Row) =
        ((source id (effectBody deletes effects answers) (first :: rest) [] initial).1 :
          Multiset Row) ∧
      answered = (source id (effectBody deletes effects answers) (first :: rest) [] initial).2 := by
  unfold nativeRun at h
  split at h
  · rename_i admissible
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have both := native_eq_source deletes effects answers first rest initial admissible
      ((changes effects first rest initial).filter Effect.isRemove ++
        (changes effects first rest initial).filter (fun e => !e.isRemove))
      (List.filter_append_perm Effect.isRemove (changes effects first rest initial))
      (join initial (first :: rest) []) (List.Perm.refl _)
    refine ⟨both.1, ?_⟩
    rw [source_eq_fused_of_keepsReads deletes effects answers first rest initial admissible.1,
      fused, sequence_effectBody]
    simp
  · cases h

theorem nativeRun_eq_none_iff :
    nativeRun deletes effects answers first rest initial = none ↔
      ¬ Admissible deletes effects first rest initial := by
  unfold nativeRun
  split <;> simp_all

/-- **Declining before any change is safe**: answering by the native run when
it answers and by the source schedule otherwise is the source schedule, up to
the order of the final bag. -/
theorem withFallback_eq :
    let outcome := (nativeRun deletes effects answers first rest initial).getD
      (source id (effectBody deletes effects answers) (first :: rest) [] initial)
    (outcome.1 : Multiset Row) =
        ((source id (effectBody deletes effects answers) (first :: rest) [] initial).1 :
          Multiset Row) ∧
      outcome.2 =
        (source id (effectBody deletes effects answers) (first :: rest) [] initial).2 := by
  intro outcome
  cases h : nativeRun deletes effects answers first rest initial with
  | none => simp [outcome, h]
  | some result =>
      obtain ⟨store, answered⟩ := result
      simpa [outcome, h] using nativeRun_sound deletes effects answers first rest initial h

end Changes

/-! ## Negated reads -/

/-- Two runs whose branches agree wherever an invariant holds, and whose first
branch keeps it, are one run. -/
theorem sequence_congr_inv {Item : Type w}
    (branch branch' : Item → List Row → List Row × List Answer)
    (P : List Row → Prop) :
    ∀ (items : List Item), (∀ item ∈ items, ∀ s, P s → branch item s = branch' item s) →
      (∀ item ∈ items, ∀ s, P s → P (branch item s).1) →
      ∀ (acc : List Row × List Answer), P acc.1 →
        NestedQuerySchedule.sequence branch items acc =
          NestedQuerySchedule.sequence branch' items acc
  | [], _, _, _, _ => rfl
  | item :: items, same, keeps, acc, h => by
      simp only [NestedQuerySchedule.sequence]
      rw [← same item List.mem_cons_self acc.1 h]
      exact sequence_congr_inv branch branch' P items
        (fun i hi => same i (List.mem_cons_of_mem _ hi))
        (fun i hi => keeps i (List.mem_cons_of_mem _ hi)) _
        (keeps item List.mem_cons_self acc.1 h)

section Negation

variable [DecidableEq Row] (deletes : Row → Row → Bool)

/-- A body that answers and makes its changes only when no row of the store it
runs on passes `test` under the choice: a negated match, read live. -/
def unlessBody (test : Level Row) (effects : List Row → List (Effect Row))
    (answers : List Row → List Answer) : Body Row Answer :=
  fun chosen store =>
    if (store.filter (test chosen)).isEmpty then
      ((effects chosen).foldl (fun s e => e.apply deletes s) store, answers chosen)
    else (store, [])

/-- The changes of a choice whose negated test passes on the initial store. -/
def snapshotEffects (initial : List Row) (test : Level Row)
    (effects : List Row → List (Effect Row)) : List Row → List (Effect Row) :=
  fun chosen => if (initial.filter (test chosen)).isEmpty then effects chosen else []

/-- The answers of a choice whose negated test passes on the initial store. -/
def snapshotAnswers (initial : List Row) (test : Level Row) (answers : List Row → List Answer) :
    List Row → List Answer :=
  fun chosen => if (initial.filter (test chosen)).isEmpty then answers chosen else []

theorem unlessBody_eq_snapshot {initial store : List Row} {events : List (Level Row × List Row)}
    (k : Keeps initial events store) {test : Level Row} {chosen : List Row}
    (h : (test, chosen) ∈ events) (effects : List Row → List (Effect Row))
    (answers : List Row → List Answer) :
    unlessBody deletes test effects answers chosen store =
      effectBody deletes (snapshotEffects initial test effects)
        (snapshotAnswers initial test answers) chosen store := by
  have same : store.filter (test chosen) = initial.filter (test chosen) := k.1 (test, chosen) h
  simp only [unlessBody, effectBody, snapshotEffects, snapshotAnswers, same]
  split <;> simp

variable (test : Level Row) (effects : List Row → List (Effect Row))
  (answers : List Row → List Answer) (first : Level Row) (rest : List (Level Row))
  (initial : List Row)

/-- The reads a run with a negated test makes after its first level: the later
levels, and the test under every joined choice. -/
def guardedReads : List (Level Row × List Row) :=
  innerReads initial first rest ++ (join initial (first :: rest) []).map fun c => (test, c)

/-- **A negated read may be read on the snapshot** when no change touches what
it, or any later level, reads. -/
theorem source_unless_eq_fused
    (keep : ∀ c ∈ join initial (first :: rest) [], ∀ e ∈ effects c,
      KeepsReads deletes initial (guardedReads test first rest initial) e) :
    source id (unlessBody deletes test effects answers) (first :: rest) [] initial =
      fused (effectBody deletes (snapshotEffects initial test effects)
        (snapshotAnswers initial test answers)) (first :: rest) initial := by
  have start : Keeps initial (guardedReads test first rest initial) initial :=
    ⟨fun _ _ => rfl, fun _ hu => Or.inl hu⟩
  have preserve : ∀ c ∈ join initial (first :: rest) [], ∀ s,
      Keeps initial (guardedReads test first rest initial) s →
        Keeps initial (guardedReads test first rest initial)
          (unlessBody deletes test effects answers c s).1 := by
    intro c hc s k
    simp only [unlessBody]
    split
    · exact keeps_foldl deletes (effects c) (keep c hc) s k
    · exact k
  rw [source_eq_fused (unlessBody deletes test effects answers) initial
    (Keeps initial (guardedReads test first rest initial)) first rest start
    (fun s k e he => k.1 e (List.mem_append_left _ he)) preserve]
  unfold fused
  exact sequence_congr_inv _ _ (Keeps initial (guardedReads test first rest initial)) _
    (fun c hc s k => unlessBody_eq_snapshot deletes k
      (List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)) effects answers)
    preserve (initial, []) start

/-- **The native run with a negated test**: the snapshot's verdicts, then the
changes in any order, answer what the live run answers. -/
theorem native_eq_source_unless
    (keep : ∀ c ∈ join initial (first :: rest) [], ∀ e ∈ effects c,
      KeepsReads deletes initial (guardedReads test first rest initial) e)
    (commute : ∀ e ∈ changes (snapshotEffects initial test effects) first rest initial,
      ∀ e' ∈ changes (snapshotEffects initial test effects) first rest initial,
        Effect.Commute deletes e e')
    (native : List (Effect Row))
    (perm : native.Perm (changes (snapshotEffects initial test effects) first rest initial)) :
    ((native.foldl (fun s e => e.apply deletes s) initial : List Row) : Multiset Row) =
        ((source id (unlessBody deletes test effects answers) (first :: rest) [] initial).1 :
          Multiset Row) ∧
      (source id (unlessBody deletes test effects answers) (first :: rest) [] initial).2 =
        (join initial (first :: rest) []).flatMap (snapshotAnswers initial test answers) := by
  rw [source_unless_eq_fused deletes test effects answers first rest initial keep, fused,
    sequence_effectBody]
  exact ⟨Effect.foldl_apply_perm deletes perm
    (fun e he e' he' => commute e (perm.mem_iff.mp he) e' (perm.mem_iff.mp he')) initial,
    by simp⟩

end Negation

section Branching

variable [DecidableEq Row] (deletes : Row → Row → Bool)

/-- A body that branches on a negated test read live: when no row of the store
passes `test` under the choice it makes the `then` changes and answers,
otherwise the `else` ones, as `(if (== (collapse (match S P T)) ()) A B)` does. -/
def condBody (test : Level Row) (thenEffects elseEffects : List Row → List (Effect Row))
    (thenAnswers elseAnswers : List Row → List Answer) : Body Row Answer :=
  fun chosen store =>
    if (store.filter (test chosen)).isEmpty then
      ((thenEffects chosen).foldl (fun s e => e.apply deletes s) store, thenAnswers chosen)
    else
      ((elseEffects chosen).foldl (fun s e => e.apply deletes s) store, elseAnswers chosen)

/-- The changes of a choice, its branch decided on the initial store. -/
def condSnapshotEffects (initial : List Row) (test : Level Row)
    (thenEffects elseEffects : List Row → List (Effect Row)) : List Row → List (Effect Row) :=
  fun chosen =>
    if (initial.filter (test chosen)).isEmpty then thenEffects chosen else elseEffects chosen

/-- The answers of a choice, its branch decided on the initial store. -/
def condSnapshotAnswers (initial : List Row) (test : Level Row)
    (thenAnswers elseAnswers : List Row → List Answer) : List Row → List Answer :=
  fun chosen =>
    if (initial.filter (test chosen)).isEmpty then thenAnswers chosen else elseAnswers chosen

theorem condBody_eq_snapshot {initial store : List Row} {events : List (Level Row × List Row)}
    (k : Keeps initial events store) {test : Level Row} {chosen : List Row}
    (h : (test, chosen) ∈ events) (thenEffects elseEffects : List Row → List (Effect Row))
    (thenAnswers elseAnswers : List Row → List Answer) :
    condBody deletes test thenEffects elseEffects thenAnswers elseAnswers chosen store =
      effectBody deletes (condSnapshotEffects initial test thenEffects elseEffects)
        (condSnapshotAnswers initial test thenAnswers elseAnswers) chosen store := by
  have same : store.filter (test chosen) = initial.filter (test chosen) := k.1 (test, chosen) h
  simp only [condBody, effectBody, condSnapshotEffects, condSnapshotAnswers, same]
  split <;> simp

variable (test : Level Row) (thenEffects elseEffects : List Row → List (Effect Row))
  (thenAnswers elseAnswers : List Row → List Answer) (first : Level Row)
  (rest : List (Level Row)) (initial : List Row)

/-- **A branch on a negated read may be decided on the snapshot** when no change
of either branch touches what the test, or any later level, reads. -/
theorem source_cond_eq_fused
    (keep : ∀ c ∈ join initial (first :: rest) [], ∀ e ∈ thenEffects c ++ elseEffects c,
      KeepsReads deletes initial (guardedReads test first rest initial) e) :
    source id (condBody deletes test thenEffects elseEffects thenAnswers elseAnswers)
        (first :: rest) [] initial =
      fused (effectBody deletes (condSnapshotEffects initial test thenEffects elseEffects)
        (condSnapshotAnswers initial test thenAnswers elseAnswers)) (first :: rest) initial := by
  have start : Keeps initial (guardedReads test first rest initial) initial :=
    ⟨fun _ _ => rfl, fun _ hu => Or.inl hu⟩
  have preserve : ∀ c ∈ join initial (first :: rest) [], ∀ s,
      Keeps initial (guardedReads test first rest initial) s →
        Keeps initial (guardedReads test first rest initial)
          (condBody deletes test thenEffects elseEffects thenAnswers elseAnswers c s).1 := by
    intro c hc s k
    simp only [condBody]
    split
    · exact keeps_foldl deletes (thenEffects c)
        (fun e he => keep c hc e (List.mem_append_left _ he)) s k
    · exact keeps_foldl deletes (elseEffects c)
        (fun e he => keep c hc e (List.mem_append_right _ he)) s k
  rw [source_eq_fused (condBody deletes test thenEffects elseEffects thenAnswers elseAnswers)
    initial (Keeps initial (guardedReads test first rest initial)) first rest start
    (fun s k e he => k.1 e (List.mem_append_left _ he)) preserve]
  unfold fused
  exact sequence_congr_inv _ _ (Keeps initial (guardedReads test first rest initial)) _
    (fun c hc s k => condBody_eq_snapshot deletes k
      (List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
      thenEffects elseEffects thenAnswers elseAnswers)
    preserve (initial, []) start

/-- **The native run with a branch on a negated test**: the snapshot decides each
choice's branch, then the changes of the chosen branches, in any order, answer
what the live run answers. -/
theorem native_eq_source_cond
    (keep : ∀ c ∈ join initial (first :: rest) [], ∀ e ∈ thenEffects c ++ elseEffects c,
      KeepsReads deletes initial (guardedReads test first rest initial) e)
    (commute : ∀ e ∈ changes (condSnapshotEffects initial test thenEffects elseEffects)
        first rest initial,
      ∀ e' ∈ changes (condSnapshotEffects initial test thenEffects elseEffects)
        first rest initial, Effect.Commute deletes e e')
    (native : List (Effect Row))
    (perm : native.Perm
      (changes (condSnapshotEffects initial test thenEffects elseEffects) first rest initial)) :
    ((native.foldl (fun s e => e.apply deletes s) initial : List Row) : Multiset Row) =
        ((source id (condBody deletes test thenEffects elseEffects thenAnswers elseAnswers)
          (first :: rest) [] initial).1 : Multiset Row) ∧
      (source id (condBody deletes test thenEffects elseEffects thenAnswers elseAnswers)
          (first :: rest) [] initial).2 =
        (join initial (first :: rest) []).flatMap
          (condSnapshotAnswers initial test thenAnswers elseAnswers) := by
  rw [source_cond_eq_fused deletes test thenEffects elseEffects thenAnswers elseAnswers first
    rest initial keep, fused, sequence_effectBody]
  exact ⟨Effect.foldl_apply_perm deletes perm
    (fun e he e' he' => commute e (perm.mem_iff.mp he) e' (perm.mem_iff.mp he')) initial,
    by simp⟩

end Branching

/-! ## Controls -/

namespace Controls

/-- Rows `(relation, first, second)`: relation `0` is `p x`, relation `1` is
`q x y`. -/
abbrev R := ℕ × ℕ × ℕ

/-- `(match S (p $x) (match S (q $x $y) (add-atom S (q 2 $y))))`. -/
def levelsPQ : List (Level R) :=
  [fun _ row => row.1 == 0,
   fun chosen row => row.1 == 1 && chosen.head?.map (fun r => r.2.1) == some row.2.1]

def addsQ2 (chosen : List R) : List (Effect R) :=
  match chosen with
  | [_, (_, _, y)] => [.add (1, 2, y)]
  | _ => []

def answersOne (_ : List R) : List Unit := [()]

/-- Exact removal. -/
def exact (pattern row : R) : Bool := pattern == row

def bodyPQ : Body R Unit := effectBody exact addsQ2 answersOne

/-- `(p 1) (p 2) (q 1 7)` and the same rows with `(p 2)` first. -/
def storeA : List R := [(0, 1, 0), (0, 2, 0), (1, 1, 7)]
def storeB : List R := [(0, 2, 0), (0, 1, 0), (1, 1, 7)]

/-- **The source schedule's answers depend on the order of the rows**: two
answers over one order, one over the other. -/
theorem live_answers_depend_on_order :
    (source id bodyPQ levelsPQ [] storeA).2.length = 2 ∧
      (source id bodyPQ levelsPQ [] storeB).2.length = 1 := by
  decide

/-- The snapshot answers once over either order: no fused run answers as the
source schedule over both. -/
theorem fused_differs :
    (fused bodyPQ levelsPQ storeA).2.length = 1 ∧
      (fused bodyPQ levelsPQ storeA).2.length ≠
        (source id bodyPQ levelsPQ [] storeA).2.length := by
  decide

/-- The check rejects the query: the added `(q 2 7)` is read under the prefix
`(p 2)`. -/
theorem check_rejects : ¬ Admissible exact addsQ2 (levelsPQ.head!) levelsPQ.tail storeA := by
  decide

/-- `(match S (q $y) (add-atom S (q (s $y))))`: one level, which writes what
it reads. -/
def levelQ : List (Level R) := [fun _ row => row.1 == 1]

def addsSucc (chosen : List R) : List (Effect R) :=
  match chosen with
  | [(_, x, y)] => [.add (1, x + 1, y)]
  | _ => []

/-- **A body may write what the first level reads**: the first level is read
once, before any body, so the schedules agree. -/
theorem first_level_written (store : List R) :
    source id (effectBody exact addsSucc answersOne) levelQ [] store =
      fused (effectBody exact addsSucc answersOne) levelQ store :=
  source_eq_fused_of_keepsReads exact addsSucc answersOne _ [] store
    (fun _ _ _ _ => by
      rename_i e he
      cases e <;> simp [KeepsReads, Unread, innerReads, readsBelow])

/-- `(match S (lvl 2 $w) (match S (val 2 $w $v) (add-atom S (val 3 $w $v))))`:
relation `0` is `lvl k w`, relation `1` is `val k w` with the level `k` in the
first column.  The body writes the relation the second level reads, at a level
that level never asks for. -/
def levelsVal : List (Level (ℕ × ℕ × ℕ)) :=
  [fun _ row => row.1 == 0 && row.2.1 == 2,
   fun chosen row => row.1 == 1 && row.2.1 == 2 &&
     chosen.head?.map (fun r => r.2.2) == some row.2.2]

def addsVal3 (chosen : List R) : List (Effect R) :=
  match chosen with
  | [_, (_, _, w)] => [.add (1, 3, w)]
  | _ => []

def storeVal : List R := [(0, 2, 5), (0, 2, 6), (1, 2, 5), (1, 2, 6), (1, 3, 9)]

/-- **A level loop passes the check**: what it writes, no later read accepts. -/
theorem levels_pass :
    Admissible exact addsVal3 (levelsVal.head!) levelsVal.tail storeVal := by
  decide

theorem levels_agree :
    source id (effectBody exact addsVal3 answersOne) levelsVal [] storeVal =
      fused (effectBody exact addsVal3 answersOne) levelsVal storeVal :=
  source_eq_fused_of_keepsReads exact addsVal3 answersOne _ _ storeVal levels_pass.1

/-- **The step schedule does not depend on the order of the rows**: the
snapshot, then the changes, answers once over both orders and leaves the same
bag. -/
theorem fused_order_free :
    (fused bodyPQ levelsPQ storeA).2.length = (fused bodyPQ levelsPQ storeB).2.length ∧
      ((fused bodyPQ levelsPQ storeA).1 : Multiset R) =
        ((fused bodyPQ levelsPQ storeB).1 : Multiset R) := by
  decide

/-- `(match S (p $x) (unless (q 2) (add-atom S (q 2))))`: the body writes the
row its negated test reads. -/
def levelsP : List (Level R) := [fun _ row => row.1 == 0]
def testQ2 : Level R := fun _ row => row.1 == 1 && row.2.1 == 2
def addsQ2Always (_ : List R) : List (Effect R) := [.add (1, 2, 0)]
def storeP : List R := [(0, 1, 0), (0, 2, 0)]

/-- **A change to what a negated test reads changes the answers**: read live,
the second choice sees the first one's row; read on the snapshot, it does
not. -/
theorem negated_read_live :
    (source id (unlessBody exact testQ2 addsQ2Always answersOne) levelsP [] storeP).2.length = 1 ∧
      (fused (effectBody exact (snapshotEffects storeP testQ2 addsQ2Always)
        (snapshotAnswers storeP testQ2 answersOne)) levelsP storeP).2.length = 2 := by
  decide

/-- The check rejects it: the added row is read by the negated test. -/
theorem negated_check_rejects :
    ¬ ∀ c ∈ join storeP levelsP [], ∀ e ∈ addsQ2Always c,
      KeepsReads exact storeP (guardedReads testQ2 (levelsP.head!) levelsP.tail storeP) e := by
  decide

/-- Rows `(relation, value)`, value 0 standing for a row holding a variable.
A removal deletes the rows of its relation whose value is its own or open, as
a unifying removal does. -/
def unifyingLike (pattern row : ℕ × ℕ) : Bool :=
  pattern.1 == row.1 && (row.2 == 0 || row.2 == pattern.2)

/-- `(match S (p $x) (match S (q 5) (remove-atom S (q 7))))` over `(p 1)`,
`(p 2)` and the open row `(q $z)`. -/
def levelsOpen : List (Level (ℕ × ℕ)) :=
  [fun _ row => row.1 == 0, fun _ row => row.1 == 1 && (row.2 == 0 || row.2 == 5)]

def removesQ7 (_ : List (ℕ × ℕ)) : List (Effect (ℕ × ℕ)) := [.remove (1, 7)]

def answerOnce (_ : List (ℕ × ℕ)) : List Unit := [()]

def storeOpen : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 0)]

/-- **A removal that meets no later pattern can still delete a row a later
pattern reads**: `(q 7)` and `(q 5)` do not meet, but both meet the open row,
so live the second solution finds nothing, and on the snapshot it does. -/
theorem open_row_removal :
    (source id (effectBody unifyingLike removesQ7 answerOnce) levelsOpen [] storeOpen).2.length =
        1 ∧
      (fused (effectBody unifyingLike removesQ7 answerOnce) levelsOpen storeOpen).2.length = 2 := by
  decide

/-- The check rejects it: the open row is deleted, and a later read accepts it. -/
theorem open_row_check_rejects :
    ¬ Admissible unifyingLike removesQ7 (levelsOpen.head!) levelsOpen.tail storeOpen := by
  decide

/-- `(match S (p $x) (if (== (collapse (match S (q $x) t)) ()) (add-atom S (q $x)) done))`
over `(p 1 0)` and `(p 1 1)`: the test reads the space its `then` branch writes. -/
def levelsPOnce : List (Level R) := [fun _ row => row.1 == 0]

def testQOfP : Level R :=
  fun chosen row => row.1 == 1 && chosen.head?.map (fun r => r.2.1) == some row.2.1

def addsQOfP (chosen : List R) : List (Effect R) :=
  match chosen with
  | [(_, x, _)] => [.add (1, x, 0)]
  | _ => []

def noChanges (_ : List R) : List (Effect R) := []

def answersThen (_ : List R) : List Bool := [true]

def answersElse (_ : List R) : List Bool := [false]

def storeTwice : List R := [(0, 1, 0), (0, 1, 1)]

/-- **A test that reads what its own branch writes is decided otherwise live**:
the first solution adds `(q 1)`, so the second takes `else`; decided on the
snapshot, both take `then`. -/
theorem cond_reads_target_differs :
    (source id (condBody exact testQOfP addsQOfP noChanges answersThen answersElse)
        levelsPOnce [] storeTwice).2 = [true, false] ∧
      (fused (effectBody exact (condSnapshotEffects storeTwice testQOfP addsQOfP noChanges)
        (condSnapshotAnswers storeTwice testQOfP answersThen answersElse))
        levelsPOnce storeTwice).2 = [true, true] := by
  decide

/-- **An addition and a removal of one row do not commute.** -/
theorem add_remove_not_comm :
    (Effect.add (0, 0, 0) : Effect R).act exact ((Effect.remove (0, 0, 0)).act exact 0) ≠
      (Effect.remove (0, 0, 0) : Effect R).act exact ((Effect.add (0, 0, 0)).act exact 0) := by
  decide

end Controls

end Mettapedia.Machines.NestedQueryEffects
