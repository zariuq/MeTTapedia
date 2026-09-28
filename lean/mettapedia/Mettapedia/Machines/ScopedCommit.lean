import Mathlib.Data.List.Basic

/-!
# Delimited commitment in finite equation search

This executable core separates branch-local bindings from a world which is
threaded through backtracking. A scope saves its failure continuation. A commit
discards the alternatives accumulated since that delimiter, preserving both
the current world and the successful branch's remaining computation. Choices
created later remain available until another commit removes them.

The evaluator uses a chosen depth-first traversal of finite alternatives. This
is an operational policy, not an assertion that equation meaning has a first
answer. Primitive computations are total functions in this finite model;
divergence, concurrent cancellation and native memory ownership are separate
obligations. A `choose` operation snapshots its finite alternatives when run.

`scope_locality` derives an exact law for the retained outside continuation,
including its effects. The token controls distinguish actual cancellation from
merely requiring a one-shot token at selected program points. No token scheme
or public MeTTa syntax is identified with delimited commitment by definition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedCommit

universe u v r t

/-- A finite search plan. `scope body next` delimits commitments in `body`;
on a success, `next` resumes in the caller's scope. -/
inductive Body (Local : Type u) (World : Type v) where
  | done
  | fail
  | choice (left right : Body Local World)
  | choose (alternatives : Local → World → List Local) (next : Body Local World)
  | effect (action : Local → World → Local × World) (next : Body Local World)
  | branch (test : Local → World → Bool) (yes no : Body Local World)
  | commit (next : Body Local World)
  | scope (body next : Body Local World)

abbrev Failure (World : Type v) (Result : Type r) := World → Result

abbrev Success (Local : Type u) (World : Type v) (Result : Type r) :=
  Local → Failure World Result → World → Result

variable {Local : Type u} {World : Type v} {Result : Type r} {Target : Type t}

/-- `failure` is the currently pending search; `saved` is the failure
continuation captured by the nearest scope. A failure continuation receives
the current world, so abandoning an alternative does not undo its effects. -/
def eval : Body Local World → Local → Success Local World Result →
    Failure World Result → Failure World Result → World → Result
  | .done, s, success, failure, _, world => success s failure world
  | .fail, _, _, failure, _, world => failure world
  | .choice left right, s, success, failure, saved, world =>
      eval left s success (fun w => eval right s success failure saved w) saved world
  | .choose alternatives next, s, success, failure, saved, world =>
      ((alternatives s world).foldr
        (fun t rest => fun w => eval next t success rest saved w) failure) world
  | .effect action next, s, success, failure, saved, world =>
      let result := action s world
      eval next result.1 success failure saved result.2
  | .branch test yes no, s, success, failure, saved, world =>
      if test s world then eval yes s success failure saved world
      else eval no s success failure saved world
  | .commit next, s, success, _, saved, world =>
      eval next s success saved saved world
  | .scope body next, s, success, failure, saved, world =>
      eval body s
        (fun t alternatives w => eval next t success alternatives saved w)
        failure failure world

/-- Sequencing preserves existing inner delimiters. In particular it appends
to a scope's caller continuation, not to the body inside that scope. -/
def andThen : Body Local World → Body Local World → Body Local World
  | .done, next => next
  | .fail, _ => .fail
  | .choice left right, next => .choice (andThen left next) (andThen right next)
  | .choose alternatives body, next => .choose alternatives (andThen body next)
  | .effect action body, next => .effect action (andThen body next)
  | .branch test yes no, next => .branch test (andThen yes next) (andThen no next)
  | .commit body, next => .commit (andThen body next)
  | .scope body continuation, next => .scope body (andThen continuation next)

/-- A first-answer delimiter for this finite operational policy. The encoding
does not assert equality with every equational theory of scoped effects. -/
def once (body : Body Local World) : Body Local World :=
  .scope (andThen body (.commit .done)) .done

/-- Structural result transport. Only the local success algebra is assumed to
commute with the transport; the whole-program property follows by induction. -/
theorem eval_natural (transform : Result → Target) (body : Body Local World)
    (s : Local) (success : Success Local World Result)
    (success' : Success Local World Target)
    (failure saved : Failure World Result) (world : World)
    (compatible : ∀ s failure world,
      success' s (fun w => transform (failure w)) world =
        transform (success s failure world)) :
    eval body s success' (fun w => transform (failure w))
      (fun w => transform (saved w)) world =
      transform (eval body s success failure saved world) := by
  induction body generalizing s success success' failure saved world with
  | done => exact compatible s failure world
  | fail => rfl
  | choice left right ihLeft ihRight =>
      simp only [eval]
      rw [show (fun w =>
        eval right s success' (fun w => transform (failure w))
          (fun w => transform (saved w)) w) =
          (fun w => transform (eval right s success failure saved w)) by
        funext w
        exact ihRight s success success' failure saved w compatible]
      exact ihLeft _ _ _ _ _ _ compatible
  | choose alternatives next ih =>
      simp only [eval]
      have folded : ∀ values : List Local,
          values.foldr (fun t rest => fun w =>
            eval next t success' rest (fun w => transform (saved w)) w)
            (fun w => transform (failure w)) =
          (fun w => transform ((values.foldr
            (fun t rest => fun w => eval next t success rest saved w) failure) w)) := by
        intro values
        induction values with
        | nil => rfl
        | cons value values ihValues =>
            simp only [List.foldr_cons, ihValues]
            funext w
            exact ih _ _ _ _ _ _ compatible
      rw [folded]
  | effect action next ih => exact ih _ _ _ _ _ _ compatible
  | branch test yes no ihYes ihNo =>
      simp only [eval]
      cases test s world
      · exact ihNo _ _ _ _ _ _ compatible
      · exact ihYes _ _ _ _ _ _ compatible
  | commit next ih => exact ih _ _ _ _ _ _ compatible
  | scope body next ihBody ihNext =>
      simp only [eval]
      apply ihBody
      intro t alternatives w
      exact ihNext t success success' alternatives saved w compatible

/-- The structural sequencing construction agrees with success-continuation
composition, retaining the caller's delimiter when a nested scope returns. -/
theorem eval_andThen (body next : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (andThen body next) s success failure saved world =
      eval body s (fun t alternatives w => eval next t success alternatives saved w)
        failure saved world := by
  induction body generalizing s success failure saved world with
  | done => rfl
  | fail => rfl
  | choice left right ihLeft ihRight => simp only [andThen, eval, ihLeft, ihRight]
  | choose alternatives body ih =>
      simp only [andThen, eval, ih]
  | effect action body ih => exact ih _ _ _ _ _
  | branch test yes no ihYes ihNo => simp only [andThen, eval, ihYes, ihNo]
  | commit body ih =>
      -- The commit updates the delimiter to the same saved continuation, so
      -- the appended computation still sees the original enclosing scope.
      exact ih _ _ _ _ _
  | scope body continuation ihBody ihContinuation =>
      simp only [andThen, eval]
      congr 1
      funext t alternatives w
      exact ihContinuation _ _ _ _ _

/-- The first success discards its own residual operand search and receives
only the outside failure continuation. This is a local operational equation. -/
theorem eval_once (body : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (once body) s success failure saved world =
      eval body s (fun value _ w => success value failure w) failure failure world := by
  change eval (andThen body (.commit .done)) s success failure failure world = _
  rw [eval_andThen]
  rfl

abbrev Observation (Local : Type u) (World : Type v) := List Local × World

def collect : Success Local World (Observation Local World) :=
  fun value failure world =>
    let rest := failure world
    (value :: rest.1, rest.2)

def finish : Failure World (Observation Local World) := fun world => ([], world)

/-- All answers under this finite traversal policy, plus the final world. -/
def run (body : Body Local World) (s : Local) (world : World) :
    Observation Local World :=
  eval body s collect finish finish world

/-- Execute the remaining outer search in the world left by the inner search.
The retained local binding of that outside search is supplied by its closure. -/
def appendObservation (earlier : Observation Local World)
    (later : Failure World (Observation Local World)) : Observation Local World :=
  let rest := later earlier.2
  (earlier.1 ++ rest.1, rest.2)

/-- A delimited finite search invokes its outside search exactly once on the
world it leaves. Answer multiplicity and outside effects remain observable. -/
theorem eval_with_suffix (body : Body Local World) (s : Local)
    (outside : Failure World (Observation Local World)) (world : World) :
    eval body s collect outside outside world =
      appendObservation (run body s world) outside := by
  have natural := eval_natural (fun result => appendObservation result outside)
    body s collect collect finish finish world (by
      intro t failure w
      simp [collect, appendObservation])
  simpa [run, finish, appendObservation] using natural

/-- A nested delimiter cannot discard its caller's alternative. Even if the
inner search commits, the outside program runs after it in the resulting world. -/
theorem scope_locality (body outside : Body Local World) (s : Local) (world : World) :
    run (.choice (.scope body .done) outside) s world =
      appendObservation (run body s world) (fun w => run outside s w) := by
  exact eval_with_suffix body s (fun w => run outside s w) world

/-- Cutting twice with no intervening choice is idempotent in every context. -/
theorem adjacent_commits (body : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (.commit (.commit body)) s success failure saved world =
      eval (.commit body) s success failure saved world := rfl

/-- A commit discards alternatives already pending; a choice in its retained
continuation is installed afterwards and remains available. -/
theorem commit_then_choice (left right : Body Local World) (s : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (.commit (.choice left right)) s success failure saved world =
      eval left s success (fun w => eval right s success saved saved w) saved world := rfl

/-- The first selected local binding commits the choices preceding the point.
This equation describes the chosen traversal, not an order-independent observer. -/
theorem choose_then_commit (alternatives : Local → World → List Local)
    (body : Body Local World) (s : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (.choose alternatives (.commit body)) s success failure saved world =
      match alternatives s world with
      | [] => failure world
      | first :: _ => eval body first success saved saved world := by
  simp only [eval]
  cases alternatives s world <;> rfl

/-- Effects performed before commitment are kept, rather than restored from a
scope checkpoint. -/
theorem effect_before_commit (action : Local → World → Local × World)
    (body : Body Local World) (s : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (.effect action (.commit body)) s success failure saved world =
      eval body (action s world).1 success saved saved (action s world).2 := rfl

namespace Controls

abbrev TestBody := Body Nat (Nat × Bool)

def answer (value : Nat) : TestBody := .effect (fun _ w => (value, w)) .done

def touch (next : TestBody) : TestBody :=
  .effect (fun s w => (s, (w.1 + 1, w.2))) next

/-- A real consumable token in the world. This operation does not cancel any
other search task merely because the token becomes unavailable. -/
def takeToken (next : TestBody) : TestBody :=
  .branch (fun _ w => w.2)
    (.effect (fun s w => (s, (w.1, false))) next) .fail

/-- A winner's subsequent acquire is treated as a no-op. This candidate keeps
the winner alive, but cannot implement a later cut of new alternatives. -/
def reacquireWinner (next : TestBody) : TestBody :=
  .effect (fun s w => (s, (w.1, false))) next

theorem cut_cancels_uncommitted_sibling :
    run (.choice (.commit (answer 1)) (answer 2)) 0 (0, true) = ([1], (0, true)) := by
  decide

theorem token_leaves_uncommitted_sibling :
    run (.choice (takeToken (answer 1)) (answer 2)) 0 (0, true) =
      ([1, 2], (0, false)) := by
  decide

theorem winner_continuation_keeps_choices :
    run (.choice (.commit (.choice (answer 1) (answer 2))) (answer 3))
      0 (0, true) = ([1, 2], (0, true)) := by
  decide

theorem requiring_token_again_loses_winner :
    run (takeToken (.choice (takeToken (answer 1)) (takeToken (answer 2))))
      0 (0, true) = ([], (0, false)) := by
  decide

theorem repeated_commit_keeps_execution :
    run (.commit (.commit (answer 1))) 0 (0, true) = ([1], (0, true)) ∧
      run (takeToken (takeToken (answer 1))) 0 (0, true) = ([], (0, false)) := by
  decide

/-- Idempotence of adjacent cuts does not make a later cut a permanent no-op. -/
theorem second_commit_prunes_new_choices :
    run (.commit (.choice (.commit (answer 1)) (answer 2)))
      0 (0, true) = ([1], (0, true)) ∧
    run (takeToken (.choice (reacquireWinner (answer 1)) (answer 2)))
      0 (0, true) = ([1, 2], (0, false)) := by
  decide

theorem inner_scope_preserves_outer_choice :
    run (.choice (.scope (.commit (answer 1)) .done) (answer 2))
      0 (0, true) = ([1, 2], (0, true)) := by
  decide

theorem nested_scopes_preserve_both_callers :
    run (.choice
      (.scope (.choice (.scope (.commit (answer 1)) .done) (answer 2)) .done)
      (answer 3)) 0 (0, true) = ([1, 2, 3], (0, true)) := by
  decide

/-- Correct lexical sequencing leaves a continuation cut in the caller scope. -/
theorem sequencing_does_not_capture_continuation :
    run (.choice (andThen (.scope (answer 1) .done) (.commit .done)) (answer 2))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choice (.scope (andThen (answer 1) (.commit .done)) .done) (answer 2))
      0 (0, true) = ([1, 2], (0, true)) := by
  decide

/-- Gate every answer with a token and the answer list happens to agree here;
the losing alternative's preceding effect still occurs. A cut cancels it. -/
theorem token_gating_does_not_cancel_effects :
    run (.choice (.commit (answer 1)) (touch (.commit (answer 2))))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choice (takeToken (answer 1)) (touch (takeToken (answer 2))))
      0 (0, true) = ([1], (1, false)) := by
  decide

theorem performed_effect_is_not_rolled_back :
    run (.choice (touch .fail) (.commit (answer 1)))
      0 (0, true) = ([1], (1, true)) := by
  decide

theorem traversal_changes_committed_answer :
    run (.choose (fun _ _ => [1, 2]) (.commit .done))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choose (fun _ _ => [2, 1]) (.commit .done))
      0 (0, true) = ([2], (0, true)) := by
  decide

/-- The losing operand is never run; merely taking the head after collecting
would instead retain its effect. -/
theorem once_stops_before_losing_effect :
    run (once (.choice (answer 1) (touch (answer 2))))
      0 (0, true) = ([1], (0, true)) ∧
    run (.choice (answer 1) (touch (answer 2)))
      0 (0, true) = ([1, 2], (1, true)) := by
  decide

end Controls

end Mettapedia.Machines.ScopedCommit
