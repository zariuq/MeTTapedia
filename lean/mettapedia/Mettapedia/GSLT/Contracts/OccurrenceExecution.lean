import Mettapedia.GSLT.Contracts.OccurrenceObservers
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Occurrence observations of executions

A completed observation is an observation of a path, not merely its final
term. In particular, silent steps affect fuel, and a stopped or faulted
path does not report absence. The path on the realizing side is read at
every step, using a relation on terms rather than a relation on executions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.OccurrenceExecution

open IndexedOperational (ExecutionPath)
open OccurrenceObservers (Demand Result Trace observe)

def nodes {sys : GSLT} {start finish : sys.Term} :
    ExecutionPath sys start finish → List sys.Term
  | .refl s => [s]
  | .cons (source := s) _ rest => s :: nodes rest

theorem nodes_chain {sys : GSLT} {start finish : sys.Term} (path : ExecutionPath sys start finish) :
    ∃ tail, nodes path = start :: tail ∧ (start :: tail).IsChain sys.Step ∧
      (start :: tail).getLast? = some finish := by
  induction path with
  | refl s => exact ⟨[], rfl, .singleton _, rfl⟩
  | @cons before next final first rest ih =>
    obtain ⟨tail, representation, contiguous, last⟩ := ih
    exact ⟨next :: tail, congrArg (before :: ·) representation, contiguous.cons_cons first.down, last⟩

theorem path_of_chain {sys : GSLT} {start : sys.Term} {tail : List sys.Term}
    (chain : (start :: tail).IsChain sys.Step) :
    ∃ finish, ∃ path : ExecutionPath sys start finish, nodes path = start :: tail := by
  induction tail generalizing start with
  | nil => exact ⟨start, .refl start, rfl⟩
  | cons next tail ih =>
    obtain ⟨first, rest⟩ := List.isChain_cons_cons.mp chain
    obtain ⟨finish, path, equals⟩ := ih rest
    exact ⟨finish, .cons ⟨first⟩ path, congrArg (start :: ·) equals⟩

private def nextBatches {View : Type*} {Answer : Type}
    (emit : View → View → List Answer) (previous : View) : List View → Trace Answer
  | [] => []
  | next :: rest => emit previous next :: nextBatches emit next rest

def batches {View : Type*} {Answer : Type}
    (emit : View → View → List Answer) : List View → Trace Answer
  | [] => []
  | initial :: rest => nextBatches emit initial rest

theorem exact_ticks {sys : GSLT} {View : Type*} {Answer : Type} (view : sys.Term → View)
    (emit : View → View → List Answer) {start finish : sys.Term}
    (run : ExecutionPath sys start finish) :
    (batches emit ((nodes run).map view)).length = run.length := by
  induction run with
  | refl => rfl
  | @cons before next finish first rest ih =>
    obtain ⟨_, split, _, _⟩ := nodes_chain rest
    change (batches emit ((before :: nodes rest).map view)).length = rest.length + 1
    rw [split] at ih ⊢
    simp only [List.map_cons, batches, nextBatches, List.length_cons] at ih ⊢
    exact congrArg (· + 1) ih

/-- Some evaluators publish one final batch, rather than streaming answers
before they settle. The transition into the terminal term owns that batch. -/
def settlingBatch {Answer : Type} (before after : Option (List Answer)) : List Answer :=
  if before.isNone then after.getD [] else []

theorem flattened_settling_batch {sys : GSLT} {Answer : Type}
    (view : sys.Term → Option (List Answer))
    (opens : ∀ {a b}, sys.Step a b → view a = none)
    {start finish : sys.Term} (run : ExecutionPath sys start finish)
    (pending : view start = none) {answers : List Answer} (finished : view finish = some answers) :
    (batches settlingBatch ((nodes run).map view)).flatten = answers := by
  induction run with
  | refl => rw [pending] at finished; cases finished
  | @cons before next finish step rest ih =>
    cases rest with
    | refl => simp [nodes, batches, nextBatches, settlingBatch, pending, finished]
    | cons second remaining =>
      have stillPending := opens second.down
      simpa only [nodes, List.map_cons, batches, nextBatches, List.flatten_cons,
        settlingBatch, pending, stillPending, Option.isNone_none, if_true, Option.getD_none,
        List.nil_append] using ih stillPending finished

structure MatchingSteps {source target : GSLT} (shows : source.Term → target.Term → Prop) :
    Prop where
  realize : ∀ {s s' t}, shows s t → source.Step s s' →
    ∃ t', target.Step t t' ∧ shows s' t'
  reflect : ∀ {s t t'}, shows s t → target.Step t t' →
    ∃ s', source.Step s s' ∧ shows s' t'

theorem realize_nodes {source target : GSLT} {shows : source.Term → target.Term → Prop}
    (law : MatchingSteps shows) {start finish : source.Term} {physical : target.Term}
    (initial : shows start physical) (run : ExecutionPath source start finish) :
    ∃ final, ∃ realized : ExecutionPath target physical final,
      shows finish final ∧ List.Forall₂ shows (nodes run) (nodes realized) := by
  induction run generalizing physical with
  | refl _ => exact ⟨physical, .refl physical, initial, .cons initial .nil⟩
  | cons step rest ih =>
    obtain ⟨next, first, now⟩ := law.realize initial step.down
    obtain ⟨final, tail, last, states⟩ := ih now
    exact ⟨final, .cons ⟨first⟩ tail, last, .cons initial states⟩

theorem reflect_nodes {source target : GSLT} {shows : source.Term → target.Term → Prop}
    (law : MatchingSteps shows) {start : source.Term} {physical final : target.Term}
    (initial : shows start physical) (run : ExecutionPath target physical final) :
    ∃ finish, ∃ reflected : ExecutionPath source start finish,
      shows finish final ∧ List.Forall₂ shows (nodes reflected) (nodes run) := by
  induction run generalizing start with
  | refl _ => exact ⟨start, .refl start, initial, .cons initial .nil⟩
  | cons step rest ih =>
    obtain ⟨next, first, now⟩ := law.reflect initial step.down
    obtain ⟨finish, tail, last, states⟩ := ih now
    exact ⟨finish, .cons ⟨first⟩ tail, last, .cons initial states⟩

def completed {sys : GSLT} {View : Type*} {Answer : Type}
    (view : sys.Term → View) (done : View → Prop) (emit : View → View → List Answer)
    (start : sys.Term) (trace : Trace Answer) : Prop :=
  ∃ finish, ∃ run : ExecutionPath sys start finish,
    done (view finish) ∧ batches emit ((nodes run).map view) = trace

theorem completed_iff_chain {sys : GSLT} {View : Type*} {Answer : Type}
    (view : sys.Term → View) (done : View → Prop) (emit : View → View → List Answer)
    (start : sys.Term) (trace : Trace Answer) :
    completed (sys := sys) view done emit start trace ↔
      ∃ tail finish, (start :: tail).IsChain sys.Step ∧
        (start :: tail).getLast? = some finish ∧ done (view finish) ∧
        batches emit ((start :: tail).map view) = trace := by
  constructor
  · rintro ⟨finish, path, ended, calculated⟩
    obtain ⟨tail, represented, edges, last⟩ := nodes_chain path
    exact ⟨tail, finish, edges, last, ended, by simpa only [represented] using calculated⟩
  · rintro ⟨tail, finish, edges, last, ended, calculated⟩
    obtain ⟨reached, path, represented⟩ := path_of_chain (sys := sys) edges
    obtain ⟨sameTail, repr', _, last'⟩ := nodes_chain path
    have same : sameTail = tail := (List.cons.inj (repr'.symm.trans represented)).2
    rw [same, last] at last'
    have found := Option.some.inj last'
    subst reached
    exact ⟨finish, path, ended, by simpa only [represented] using calculated⟩

/-- The realizing side reads its own terms along an actual execution. -/
def readCompleted {sys : GSLT} {View : Type*} {Answer : Type}
    (read : sys.Term → View → Prop) (done : View → Prop) (emit : View → View → List Answer)
    (start : sys.Term) (trace : Trace Answer) : Prop :=
  ∃ finish, ∃ run : ExecutionPath sys start finish, ∃ views,
    List.Forall₂ read (nodes run) views ∧
    (∃ finalView, read finish finalView ∧ done finalView) ∧ batches emit views = trace

def ofTerm {S T View : Type*} (shows : S → T → Prop) (view : S → View)
    (physical : T) (reading : View) : Prop :=
  ∃ semantic, shows semantic physical ∧ view semantic = reading

theorem ofTerm_functional {S T View : Type*} {shows : S → T → Prop} {view : S → View}
    (unique : ∀ {a b t}, shows a t → shows b t → view a = view b) :
    ∀ {t x y}, ofTerm shows view t x → ofTerm shows view t y → x = y := by
  rintro t x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  exact unique ha hb

private theorem readList {S T View : Type*} {shows : S → T → Prop} {view : S → View}
    {read : T → View → Prop} (reads : ∀ {s t}, shows s t → read t (view s))
    {ss : List S} {ts : List T} (states : List.Forall₂ shows ss ts) :
    List.Forall₂ read ts (ss.map view) := by
  induction states with
  | nil => exact .nil
  | cons a _ ih => exact .cons (reads a) ih

private theorem uniqueList {T View : Type*} {read : T → View → Prop}
    (unique : ∀ {t x y}, read t x → read t y → x = y) {ts : List T} {xs ys : List View}
    (first : List.Forall₂ read ts xs) (second : List.Forall₂ read ts ys) :
    xs = ys := by
  induction first generalizing ys with
  | nil => cases second; rfl
  | cons h _ ih =>
    cases second with
    | cons h' rest => exact congrArg₂ List.cons (unique h h') (ih rest)

theorem completed_iff {source target : GSLT} {shows : source.Term → target.Term → Prop}
    {View : Type*} {Answer : Type} (view : source.Term → View) (read : target.Term → View → Prop)
    (law : MatchingSteps shows) (reads : ∀ {s t}, shows s t → read t (view s))
    (unique : ∀ {t x y}, read t x → read t y → x = y)
    {start : source.Term} {physical : target.Term} (initial : shows start physical)
    (done : View → Prop) (emit : View → View → List Answer) (trace : Trace Answer) :
    completed view done emit start trace ↔ readCompleted read done emit physical trace := by
  constructor
  · rintro ⟨finish, run, done', traceEq⟩
    obtain ⟨final, realized, last, states⟩ := realize_nodes law initial run
    exact ⟨final, realized, _, readList (view := view) (read := read) reads states,
      ⟨view finish, reads last, done'⟩, traceEq⟩
  · rintro ⟨final, run, views, readings, ⟨finalView, lastRead, done'⟩, traceEq⟩
    obtain ⟨finish, reflected, last, states⟩ := reflect_nodes law initial run
    have finalEq := unique (reads last) lastRead
    have viewsEq := uniqueList (read := read) unique (readList (view := view) (read := read) reads states) readings
    exact ⟨finish, reflected, by simpa only [finalEq] using done', by simpa only [viewsEq] using traceEq⟩

def reports {Answer : Type} (traces : Trace Answer → Prop)
    (demand : Demand) (answer : Result Answer demand) : Prop :=
  ∃ trace, traces trace ∧ observe demand trace = answer

theorem reports_congr {Answer : Type} {first second : Trace Answer → Prop}
    (traces : ∀ trace, first trace ↔ second trace) (demand : Demand) (answer : Result Answer demand) :
    reports first demand answer ↔ reports second demand answer := by
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, (traces t).mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, (traces t).mpr ht, rfl⟩

theorem reports_shown_iff {source target : GSLT} {shows : source.Term → target.Term → Prop}
    {View : Type*} {Answer : Type} (view : source.Term → View)
    (law : MatchingSteps shows)
    (determined : ∀ {a b t}, shows a t → shows b t → view a = view b)
    {start : source.Term} {physical : target.Term} (initial : shows start physical)
    (done : View → Prop) (emit : View → View → List Answer)
    (demand : Demand) (answer : Result Answer demand) :
    reports (completed (sys := source) view done emit start) demand answer ↔
      reports (readCompleted (sys := target) (ofTerm shows view) done emit physical) demand answer := by
  apply reports_congr
  exact completed_iff view (ofTerm shows view) law (fun h => ⟨_, h, rfl⟩)
    (ofTerm_functional (shows := shows) (view := view) determined) initial done emit

/-- The timed observer sees the trace itself, including silent ticks. -/
theorem all_reports_iff {Answer : Type} (first second : Trace Answer → Prop) :
    (∀ demand answer, reports first demand answer ↔ reports second demand answer) ↔
    (∀ trace, first trace ↔ second trace) := by
  constructor
  · intro h trace
    have reportTimed (traces : Trace Answer → Prop) :
        reports traces .timed trace ↔ traces trace := by
      constructor
      · rintro ⟨t, ht, eq⟩
        change t = trace at eq
        exact eq ▸ ht
      · intro ht; exact ⟨trace, ht, rfl⟩
    exact (reportTimed first).symm.trans ((h .timed trace).trans (reportTimed second))
  · exact fun h demand answer => reports_congr h demand answer

theorem stuck_is_not_completed {sys : GSLT} {View : Type*} {Answer : Type}
    (view : sys.Term → View) (done : View → Prop) (emit : View → View → List Answer)
    {start : sys.Term} (stuck : ∀ next, ¬sys.Step start next) (unfinished : ¬done (view start))
    (trace : Trace Answer) : ¬completed view done emit start trace := by
  rintro ⟨finish, run, finished, _⟩
  cases run with
  | refl => exact unfinished finished
  | cons first _ => exact stuck _ first.down

end Mettapedia.GSLT.Contracts.OccurrenceExecution
