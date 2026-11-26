import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionSemantics

/-!
# The cost of reading a mutable constructor on resumption

The PeTTa term `(S (pick))` wraps each answer of an already entered generator.
In the absence of an equation, `(S x)` is data. A consumer may install or
remove the single equation `(= (S $x) (T $x))` before requesting another
answer. The expression, payload and selected alternatives can all stay the same.

The direct SWI clause shape `p(['S',X], Y, ['S',D]) :- p(X,Y,D).`
unifies the output tag before the recursive call. The rigid-head theorem
isolates precisely this commitment when a consumer can change the meaning of
`S` across that call's answers.

The cost model gives a deterministic reader arbitrary private state and
adaptive reads of the current Boolean interface. It counts only these reads.
Published edits can also update private state. The pull-only theorem applies
when such updates do not reach the suspended reader. It charges one read per
independently editable resumption, even on a run with no edits. The matching
implementations exhibit the effect of a writer notification and of several
constructor layers sharing a stable interval.

The units are interface observations at exposed answers. Translating them into
SWI instructions, live frames or elapsed time requires a concrete lowering
and a corresponding cost model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionLowerBound

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search Trace)
open Mettapedia.Machines.ReadOnlyQuery (Program run)
open PeTTaWorldSemantics (Expr Model eval evalArgs invokeAtEntry)
open PeTTaWorldSemantics.Search (pure)

inductive Head where
  | pick
  | s

/-- The only equation of `S`, when installed, returns `(T x)` as data. -/
def wrap (installed : Bool) (x : Atom) : Atom :=
  .expression [.symbol (if installed then "T" else "S"), x]

theorem flip_changes_answer (installed : Bool) (x : Atom) :
    wrap (!installed) x ≠ wrap installed x := by
  cases installed <;> simp [wrap]

/-- `pick` exposes a prescribed list of alternatives in order, including
duplicates. Both heads evaluate their arguments. -/
def model (alternatives : List Atom) : Model Bool Head Atom Bool Head where
  update installed _ := installed
  editValue _ := .symbol "true"
  argumentModes _ _ := []
  holdArgument _ := .expression []
  data head args := .expression (.symbol (match head with | .s => "S" | .pick => "pick") :: args)
  candidates world
    | .pick => [.pick]
    | .s => if world then [.s] else []
  runCandidate
    | .pick, _ => Search.superpose alternatives
    | .s, args => pure (.expression (.symbol "T" :: args))

def source : Expr Head Atom Bool := .apply .s (.cons (.apply .pick .nil) .nil)

private theorem pick_eq (xs : List Atom) :
    eval (model xs) (.apply .pick .nil) = Search.superpose xs := by
  change (pure ([] : List Atom)).bind (invokeAtEntry (model xs) .pick) = _
  rw [PeTTaWorldSemantics.Search.pure_bind]
  funext world
  exact PeTTaWorldSemantics.Trace.append_done (Search.superpose xs world)

private theorem invoke_s (xs : List Atom) (x : Atom) :
    invokeAtEntry (model xs) .s [x] = fun world => pure (wrap world x) world := by
  funext world
  cases world <;> rfl

private theorem wrap_expr (xs : List Atom) (arg : Expr Head Atom Bool) :
    eval (model xs) (.apply .s (.cons arg .nil)) =
      (eval (model xs) arg).bind fun x world => pure (wrap world x) world := by
  change (((eval (model xs) arg).bind fun x =>
    (pure ([] : List Atom)).bind fun tail => pure (x :: tail)).bind
      (invokeAtEntry (model xs) .s)) = _
  simp only [PeTTaWorldSemantics.Search.pure_bind, PeTTaWorldSemantics.Search.bind_assoc, invoke_s]

/-- The remaining values are fixed while each application of `S` takes the
world passed by the consumer at that particular resumption. -/
def pending : List Atom → Search Bool Atom
  | [], world => .done world
  | x :: xs, world => .answer (wrap world x) world (pending xs)

theorem source_trace (xs : List Atom) : eval (model xs) source = pending xs := by
  rw [source, wrap_expr, pick_eq]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    funext world
    change Trace.answer (wrap world x) world
        ((Search.superpose xs).bind fun value w => pure (wrap w value) w) =
      Trace.answer (wrap world x) world (pending xs)
    rw [ih]

private def residual : Trace Bool Atom → Search Bool Atom
  | .done _ => Trace.done
  | .answer _ _ next => next

private def observe : List Bool → Search Bool Atom → List Atom
  | [], _ => []
  | world :: worlds, next =>
    match next world with
    | .done _ => []
    | .answer value _ later => value :: observe worlds later

/-- Demand a first result in the given initial world. Then, for each world
supplied by the consumer, demand one answer of the actual residual. -/
def liveAnswers (x : Atom) (initial : Bool) (worlds : List Bool) : List Atom :=
  let xs := x :: List.replicate worlds.length x
  observe worlds (residual (eval (model xs) source initial))

theorem liveAnswers_eq (x : Atom) (initial : Bool) (worlds : List Bool) :
    liveAnswers x initial worlds = worlds.map (fun world => wrap world x) := by
  simp only [liveAnswers, source_trace, pending, residual]
  induction worlds with
  | nil => rfl
  | cons world worlds ih =>
    simp only [List.length_cons, List.replicate_succ, observe, pending, List.map_cons, ih]

/-- Pre-unifying the result with the rigid list head `S` loses the installed
answer, even if the compiler leaves the entire list tail free. -/
theorem rigid_head_fails_after_install (x : Atom) (tail : List Atom) :
    liveAnswers x false [true] ≠ [.expression (.symbol "S" :: tail)] := by
  simp [liveAnswers_eq, wrap]

/-- For this discriminating instance the previously recorded negative
callability decision gives the right answer exactly while `S` stays data. -/
theorem retaining_data_agrees_iff (x : Atom) (current : Bool) :
    (PeTTaResumptionSemantics.evalAt .editsOnly .resume (fun world (_ : Unit) => world)
      false (.read () .pure) (fun callable =>
        if callable then invokeAtEntry (model []) .s [x] else pure (wrap false x)) current).drain.1 =
      liveAnswers x false [current] ↔ current = false := by
  cases current <;> simp [PeTTaResumptionSemantics.evalAt, run,
    PeTTaWorldSemantics.Search.pure, liveAnswers_eq, wrap]

/-! ## Private state, writes and pull queries

One interval admits either no write or a single publication before the next
answer. This restricted family already allows either interface at every
handoff. A machine may be specialized to the exact number of remaining
answers and may keep the whole prior history in its private state.
-/

/-- `publish` is the writer's opportunity to change what the reader knows.
`resume` may query the current interface. The payload and next private state
are determined by the state and the observed replies. -/
structure Machine (State : Type) where
  publish : Bool → State → State
  resume : State → Program Unit Bool (Atom × State)

variable {State : Type}

def worldsAt : Bool → List (Option Bool) → List Bool
  | _, [] => []
  | old, edit :: rest =>
    let now := edit.getD old
    now :: worldsAt now rest

theorem every_world_schedule_is_realizable (old : Bool) (worlds : List Bool) :
    worldsAt old (worlds.map some) = worlds := by
  induction worlds generalizing old with
  | nil => rfl
  | cons world worlds ih => simp [worldsAt, ih]

/-- Deliver a write, if present, then run the reader and record its queries. -/
def step (m : Machine State) (state : State) (old : Bool) (edit : Option Bool) :=
  let state' := match edit with | none => state | some new => m.publish new state
  run (fun _ : Unit => edit.getD old) (m.resume state')

/-- Answers and number of actual reads. A retained value, an ordinary
instruction and an indirect call do not have assigned cycle costs here. -/
def serve (m : Machine State) : State → Bool → List (Option Bool) → List Atom × Nat
  | _, _, [] => ([], 0)
  | state, old, edit :: rest =>
    let here := step m state old edit
    let later := serve m here.answer.2 (edit.getD old) rest
    (here.answer.1 :: later.1, here.reads.length + later.2)

def CorrectFor (m : Machine State) (x : Atom) (state : State) (old : Bool) (count : Nat) : Prop :=
  ∀ edits : List (Option Bool), edits.length = count →
    (serve m state old edits).1 = liveAnswers x old (worldsAt old edits)

private theorem correct_step {m : Machine State} {x : Atom} {s : State} {old : Bool} {n : Nat}
    (correct : CorrectFor m x s old (n + 1)) (edit : Option Bool) :
    (step m s old edit).answer.1 = wrap (edit.getD old) x ∧
      CorrectFor m x (step m s old edit).answer.2 (edit.getD old) n := by
  have atCons (rest : List (Option Bool)) (size : rest.length = n) :
      (step m s old edit).answer.1 = wrap (edit.getD old) x ∧
        (serve m (step m s old edit).answer.2 (edit.getD old) rest).1 =
          (worldsAt (edit.getD old) rest).map (fun world => wrap world x) := by
    have answers := correct (edit :: rest) (by simp [size])
    rw [liveAnswers_eq] at answers
    exact List.cons.inj answers
  refine ⟨(atCons (List.replicate n none) (by simp)).1, ?_⟩
  intro rest size
  rw [liveAnswers_eq]
  exact (atCons rest size).2

/-- To distinguish an installation/removal from no write, either the writer
delivers different private state, or the reader performs a fresh observation
in both executions. -/
theorem notification_or_read {m : Machine State} {x : Atom} {s : State} {old : Bool} {n : Nat}
    (correct : CorrectFor m x s old (n + 1)) :
    m.publish (!old) s ≠ s ∨
      (0 < (step m s old none).reads.length ∧
       0 < (step m s old (some (!old))).reads.length) := by
  by_cases same : m.publish (!old) s = s
  · right
    have quiet := (correct_step correct none).1
    have edited := (correct_step correct (some (!old))).1
    cases q : m.resume s with
    | pure result =>
      simp only [step, same, q, run, Option.getD_none, Option.getD_some] at quiet edited
      exact (flip_changes_answer old x (edited.symm.trans quiet)).elim
    | read key next => simp [step, same, q, run]
  · exact Or.inl same

private theorem step_without_notification (m : Machine State) (s : State)
    (old : Bool) (edit : Option Bool) (silent : ∀ b state, m.publish b state = state) :
    step m s old edit = run (fun _ => edit.getD old) (m.resume s) := by
  cases edit <;> simp [step, silent]

/-- On every history of `n` independently editable resumptions, any exact
pull-only machine pays at least `n` Boolean interface reads. The quiet
history is included. This counts exposed resumptions, not recursion depth. -/
theorem pull_read_lower_bound (m : Machine State) (x : Atom)
    (silent : ∀ b state, m.publish b state = state)
    (s : State) (old : Bool) (edits : List (Option Bool))
    (correct : CorrectFor m x s old edits.length) :
    edits.length ≤ (serve m s old edits).2 := by
  induction edits generalizing old s with
  | nil => simp [serve]
  | cons edit rest ih =>
    obtain ⟨positive, _⟩ := (notification_or_read correct).resolve_left (not_not_intro (silent _ _))
    have here : 0 < (step m s old edit).reads.length := by
      rw [step_without_notification _ _ _ _ silent] at positive ⊢
      cases q : m.resume s with
      | pure _ => simp [q, run] at positive
      | read _ _ => simp [run]
    have later := ih (step m s old edit).answer.2 (edit.getD old) (correct_step correct edit).2
    change rest.length + 1 ≤ (step m s old edit).reads.length +
      (serve m (step m s old edit).answer.2 (edit.getD old) rest).2
    omega

theorem quiet_run_still_polls (m : Machine State) (x : Atom) (s : State) (old : Bool) (n : Nat)
    (silent : ∀ b state, m.publish b state = state) (correct : CorrectFor m x s old n) :
    n ≤ (serve m s old (List.replicate n none)).2 := by
  simpa using pull_read_lower_bound m x silent s old (List.replicate n none) (by simpa using correct)

def polling (x : Atom) : Machine Unit where
  publish _ s := s
  resume _ := .read () fun b => .pure (wrap b x, ())

theorem polling_attains_bound (x : Atom) (old : Bool) (edits : List (Option Bool)) :
    serve (polling x) () old edits = (liveAnswers x old (worldsAt old edits), edits.length) := by
  rw [liveAnswers_eq]
  induction edits generalizing old with
  | nil => rfl
  | cons edit rest ih =>
    have here : step (polling x) () old edit =
        ⟨(wrap (edit.getD old) x, ()), [((), edit.getD old)]⟩ := by cases edit <;> rfl
    simp [serve, here, worldsAt, ih, Nat.add_comm]

/-- Publication replaces the pending target. The receiver then calls it
with the payload. Dispatch, publication, and synchronization have their own
implementation costs. -/
def relinked (x : Atom) : Machine (Atom → Atom) where
  publish b _ := wrap b
  resume target := .pure (target x, target)

theorem relinking_has_zero_pull_reads (x : Atom) (old : Bool) (edits : List (Option Bool)) :
    serve (relinked x) (wrap old) old edits = (liveAnswers x old (worldsAt old edits), 0) := by
  rw [liveAnswers_eq]
  induction edits generalizing old with
  | nil => rfl
  | cons edit rest ih =>
    have here : step (relinked x) (wrap old) old edit =
        ⟨(wrap (edit.getD old) x, wrap (edit.getD old)), []⟩ := by cases edit <;> rfl
    simp [serve, here, worldsAt, ih]

/-! ## Constructor depth inside a stable interval -/

def nested : Nat → Expr Head Atom Bool → Expr Head Atom Bool
  | 0, arg => arg
  | n + 1, arg => .apply .s (.cons (nested n arg) .nil)

/-- Ordinary accumulator for repeated applications of one pure constructor. -/
def build (constructor : Atom → Atom) : Nat → Atom → Atom
  | 0, acc => acc
  | n + 1, acc => build constructor n (constructor acc)

private theorem build_commutes (f : Atom → Atom) (n : Nat) (x : Atom) :
    build f n (f x) = f (build f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- The argument can edit and yield repeatedly. The pure homogeneous layers
around each answer run in that answer's world. -/
theorem nested_one_interval_per_answer (xs : List Atom) (n : Nat) (arg : Expr Head Atom Bool) :
    eval (model xs) (nested n arg) =
      (eval (model xs) arg).bind fun x w => pure (build (wrap w) n x) w := by
  induction n with
  | zero => exact (PeTTaWorldSemantics.Search.bind_pure _).symm
  | succ n ih =>
    rw [nested, wrap_expr, ih, PeTTaWorldSemantics.Search.bind_assoc]
    apply congrArg ((eval (model xs) arg).bind)
    funext x w
    change (pure (wrap w (build (wrap w) n x)) w).append Trace.done =
      pure (build (wrap w) n (wrap w x)) w
    rw [build_commutes]
    rfl

/-- One read per produced answer suffices at every positive depth, even
when the consumer can install or remove `S` between successive answers. -/
theorem one_read_per_answer_at_any_depth (xs : List Atom) (n : Nat) (arg : Expr Head Atom Bool) :
    let q (x : Atom) : Program Unit Bool Atom := .read () fun b => .pure (build (wrap b) (n + 1) x)
    (∀ (w : Bool) x, (run (fun _ => w) (q x)).reads.length = 1) ∧
      eval (model xs) (nested (n + 1) arg) =
        (eval (model xs) arg).bind fun x w => pure (run (fun _ => w) (q x)).answer w :=
  ⟨fun _ _ => rfl, nested_one_interval_per_answer xs (n + 1) arg⟩

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionLowerBound
