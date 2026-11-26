import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability

/-!
# World-threaded PeTTa evaluation

This file gives the control-flow foundation behind P-DEF-4. Sequenced
fragments, `let` bodies, branches and function bodies all use the same
state-threaded search. The program world is outside nondeterminism, so effects
survive backtracking. An application first reads its argument modes, then
evaluates or holds its arguments in order, and finally fixes its equation candidates. Thus
an argument's effects cannot retroactively change whether that argument was
held, while those effects are visible to candidate selection.

## The rules

`⟦e⟧` is a `Search World Value`: each answer carries the world at that
moment, and resuming the search takes the world as the answer's consumer
left it.

```text
⟦v⟧                     = return v          -- values, quotes, bound variables: never re-read
⟦(let p e₁ e₂)⟧         = ⟦e₁⟧ >>= λv. unify p v; ⟦e₂⟧   -- the world flows from e₁ into e₂
⟦f₁ f₂ … fₙ⟧ (in sequence) = ⟦f₁⟧ >> ⟦f₂⟧ >> … >> ⟦fₙ⟧  -- grouping within one search
⟦(superpose (e₁ … eₙ))⟧ = ⟦e₁⟧ ++ … ++ ⟦eₙ⟧  -- each branch starts in the world
                                             -- the previous branch's consumer left
⟦(collapse e)⟧          = all answers of ⟦e⟧, in the current world
⟦(= l r)⟧, add-atom, remove-atom, import!  : the only operations that change the world
⟦(f e₁ … eₙ)⟧           = read f's declarations (they say which arguments to evaluate);
                          evaluate the arguments in order;
                          read f's equations now and fix them for this call;
                          none → the data (f v₁ … vₙ);
                          otherwise each candidate in order, in the current world
```

`eval` below gives the value, quote, `let`, sequencing, choice, edit and
application rows (`evalArgs` and `invokeAtEntry` for the last). `evalForms`
gives the sequence row. Top-level requests can be collected separately.
`collapse` drains a search (`Trace.drain`). The world-changing operations in
this fragment are `edit`s.

These rules read the program live everywhere. A live compiler stages this
evaluator: a captured stretch may run while its recorded reads remain valid;
otherwise the entire stretch is translated again in the world in which it is
reached. Values are opaque and are never retranslated.

`PeTTaStagedSemantics` models SWI-PeTTa's staging. A query is translated
when it is reached. A function enters its installed compiled clauses.
The model's fresh entry describes such a clause when its translation reads
still agree with the current program. A run-time `eval` explicitly
translates its source at that occurrence.

This is deliberately an abstract control theorem. Pattern matching, recursive
equation bodies, exceptions, and concrete atoms are supplied by `Model` (or by
the candidate runner) rather than reimplemented here. Consequently this file
does not by itself certify SWI-PeTTa's translator: that still requires a
simulation showing that its generated Prolog goals implement these boundaries
without losing relational demand or exception propagation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaWorldSemantics

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search Trace)
open Mettapedia.Machines.CallabilityTranslation

namespace Trace

variable {World A B C : Type}

theorem append_assoc (trace : Trace World A)
    (first second : World → Trace World A) :
    (trace.append first).append second =
      trace.append (fun world => (first world).append second) := by
  induction trace with
  | done world => rfl
  | answer value world resume ih =>
      simp only [Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.append]
      congr
      funext next
      exact ih next

theorem append_bind (trace : Trace World A) (later : World → Trace World A)
    (next : A → World → Trace World B) :
    (trace.append later).bind next =
      (trace.bind next).append (fun world => (later world).bind next) := by
  induction trace with
  | done world => rfl
  | answer value world resume ih =>
      simp only [Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.append,
        Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.bind]
      rw [append_assoc]
      congr
      funext nextWorld
      exact ih nextWorld

theorem append_done (trace : Trace World A) :
    trace.append (fun world => .done world) = trace := by
  induction trace with
  | done world => rfl
  | answer value world resume ih =>
      simp only [Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.append]
      congr
      funext nextWorld
      exact ih nextWorld

theorem bind_pure (trace : Trace World A) :
    trace.bind (fun value world => .answer value world .done) = trace := by
  induction trace with
  | done world => rfl
  | answer value world resume ih =>
      simp only [Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.bind,
        Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.append]
      congr
      funext nextWorld
      exact ih nextWorld

theorem bind_assoc (trace : Trace World A)
    (first : A → World → Trace World B)
    (second : B → World → Trace World C) :
    (trace.bind first).bind second =
      trace.bind (fun value world => (first value world).bind second) := by
  induction trace with
  | done world => rfl
  | answer value world resume ih =>
      simp only [Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.bind]
      rw [append_bind]
      congr
      funext nextWorld
      exact ih nextWorld

end Trace

namespace Search

variable {World A B C : Type}

def pure (value : A) : Search World A :=
  fun world => .answer value world .done

def modify (update : World → World) : Search World Unit :=
  fun world => .answer () (update world) .done

def append (first second : Search World A) : Search World A :=
  fun world => (first world).append second

@[simp] theorem pure_bind (value : A) (next : A → Search World B) :
    (pure value).bind next = next value := by
  funext world
  simp only [Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Search.bind, pure,
    Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.bind]
  exact Trace.append_done (next value world)

@[simp] theorem bind_pure (search : Search World A) :
    search.bind pure = search := by
  funext world
  exact Trace.bind_pure (search world)

theorem bind_assoc (search : Search World A)
    (first : A → Search World B) (second : B → Search World C) :
    (search.bind first).bind second =
      search.bind (fun value => (first value).bind second) := by
  funext world
  exact Trace.bind_assoc (search world) first second

end Search

/-! ## Exact decision certificates for compiled stretches

Callability is only one compiler observation. A concrete PeTTa compiler also
observes arities, argument modes, intrinsic ownership, and (on typed lines)
type-directed dispatch facts. The generic certificate below validates the
complete observed value at every key. A revision counter may skip validation
when unchanged, but cannot replace this certificate after the counter moves.
-/

namespace DecisionStaging

open Mettapedia.Machines.ReadOnlyQuery

variable {Key Observation Plan World A B : Type}

structure Capture (Key Observation Plan : Type) where
  program : Program Key Observation Plan
  plan : Plan
  reads : Reads Key Observation

def capture (store : Key → Observation)
    (program : Program Key Observation Plan) : Capture Key Observation Plan :=
  let result := run store program
  ⟨program, result.answer, result.reads⟩

def refresh [DecidableEq Observation] (store : Key → Observation)
    (saved : Capture Key Observation Plan) : Plan :=
  if checkReads store saved.reads then saved.plan
  else (run store saved.program).answer

theorem refresh_capture [DecidableEq Observation]
    (first second : Key → Observation)
    (program : Program Key Observation Plan) :
    refresh second (capture first program) = (run second program).answer := by
  by_cases valid : checkReads second (run first program).reads = true
  · simp only [refresh, capture, valid, ↓reduceIte]
    exact (validated_answer first second program valid).symm
  · simp [refresh, capture, valid]

def enterLive (store : World → Key → Observation)
    (program : Program Key Observation Plan)
    (execute : Plan → Search World A) : Search World A :=
  fun world => execute (run (store world) program).answer world

def enterRevalidated [DecidableEq Observation]
    (store : World → Key → Observation)
    (saved : Capture Key Observation Plan)
    (execute : Plan → Search World A) : Search World A :=
  fun world => execute (refresh (store world) saved) world

theorem enterRevalidated_eq_live [DecidableEq Observation]
    (store : World → Key → Observation)
    (translatedIn : World) (program : Program Key Observation Plan)
    (execute : Plan → Search World A) :
    enterRevalidated store (capture (store translatedIn) program) execute =
      enterLive store program execute := by
  funext world
  simp only [enterRevalidated, enterLive]
  rw [refresh_capture]

/-- Each answer from a preceding computation reaches the compiled stretch in
the world that answer produced. Revalidating every exact compiler observation
is extensionally equal to running a fresh translation query there. -/
theorem bind_revalidated_eq_live [DecidableEq Observation]
    (prior : Search World A) (store : World → Key → Observation)
    (translatedIn : A → World)
    (program : A → Program Key Observation Plan)
    (execute : A → Plan → Search World B) :
    prior.bind (fun answer => enterRevalidated store
          (capture (store (translatedIn answer)) (program answer)) (execute answer)) =
      prior.bind (fun answer => enterLive store (program answer) (execute answer)) := by
  apply congrArg (Search.bind prior)
  funext answer
  exact enterRevalidated_eq_live store (translatedIn answer) (program answer) (execute answer)

end DecisionStaging

mutual
  inductive Expr (Name Value Edit : Type) where
    | value (value : Value)
    | quote (value : Value)
    | edit (edit : Edit)
    | letE (bound : Expr Name Value Edit)
        (body : Value → Expr Name Value Edit)
    | seq (first second : Expr Name Value Edit)
    | choice (first second : Expr Name Value Edit)
    | apply (head : Name) (arguments : Exprs Name Value Edit)

  inductive Exprs (Name Value Edit : Type) where
    | nil
    | cons (first : Expr Name Value Edit) (rest : Exprs Name Value Edit)
end

inductive ArgumentMode where
  | evaluate
  | hold
  deriving DecidableEq, Repr

structure Model (World Name Value Edit Candidate : Type) where
  update : Edit → World → World
  editValue : Edit → Value
  argumentModes : World → Name → List ArgumentMode
  holdArgument : Expr Name Value Edit → Value
  data : Name → List Value → Value
  candidates : World → Name → List Candidate
  runCandidate : Candidate → List Value → Search World Value

variable {World Name Value Edit Candidate : Type}

/-- Candidate selection is performed once, in the world where the application
is entered. Candidate bodies may change the world, but resumption retains the
selected tail. -/
def invokeAtEntry (model : Model World Name Value Edit Candidate)
    (head : Name) (arguments : List Value) : Search World Value :=
  fun world =>
    match model.candidates world head with
    | [] => Search.pure (model.data head arguments) world
    | candidates =>
        ((Search.superpose candidates).bind
          (fun candidate => model.runCandidate candidate arguments)) world

theorem invokeAtEntry_selected (model : Model World Name Value Edit Candidate)
    (head : Name) (arguments : List Value) {world : World}
    {first : Candidate} {rest : List Candidate}
    (selected : model.candidates world head = first :: rest) :
    invokeAtEntry model head arguments world =
      (model.runCandidate first arguments world).append fun nextWorld =>
        ((Search.superpose rest).bind
          (fun candidate => model.runCandidate candidate arguments)) nextWorld := by
  simp only [invokeAtEntry, selected,
    Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Search.bind,
    Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Search.superpose,
    Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.bind]

mutual
  def eval (model : Model World Name Value Edit Candidate) :
      Expr Name Value Edit → Search World Value
    | .value value => Search.pure value
    | .quote value => Search.pure value
    | .edit edit =>
        fun world => .answer (model.editValue edit) (model.update edit world) .done
    | .letE bound body =>
        (eval model bound).bind fun value => eval model (body value)
    | .seq first second =>
        (eval model first).bind fun _ => eval model second
    | .choice first second =>
        Search.append (eval model first) (eval model second)
    | .apply head arguments =>
        fun world =>
          let modes := model.argumentModes world head
          ((evalArgs model modes arguments).bind fun values =>
            invokeAtEntry model head values) world

  def evalArgs (model : Model World Name Value Edit Candidate) :
      List ArgumentMode → Exprs Name Value Edit → Search World (List Value)
    | _, .nil => Search.pure []
    | .hold :: modes, .cons first rest =>
        (evalArgs model modes rest).bind fun values =>
          Search.pure (model.holdArgument first :: values)
    | .evaluate :: modes, .cons first rest =>
        (eval model first).bind fun value =>
          (evalArgs model modes rest).bind fun values =>
            Search.pure (value :: values)
    | [], .cons first rest =>
        (eval model first).bind fun value =>
          (evalArgs model [] rest).bind fun values =>
            Search.pure (value :: values)
end

/-- A nonempty sequence of fragments inside one search uses the same bind
as `seq`. The last fragment supplies its result. -/
def evalForms (model : Model World Name Value Edit Candidate) :
    Expr Name Value Edit → List (Expr Name Value Edit) → Search World Value
  | first, [] => eval model first
  | first, next :: rest =>
      (eval model first).bind fun _ => evalForms model next rest

@[simp] theorem eval_value (model : Model World Name Value Edit Candidate)
    (value : Value) :
    eval model (.value value) = Search.pure value := rfl

@[simp] theorem eval_quote (model : Model World Name Value Edit Candidate)
    (value : Value) :
    eval model (.quote value) = Search.pure value := rfl

@[simp] theorem eval_let_value (model : Model World Name Value Edit Candidate)
    (value : Value) (body : Value → Expr Name Value Edit) :
    eval model (.letE (.value value) body) = eval model (body value) := by
  simp [eval]

/-- A zero-argument wrapper is semantically inert. This is the abstract
lambda-wrapping half of the inlining law. -/
theorem inert_wrapper (model : Model World Name Unit Edit Candidate)
    (body : Expr Name Unit Edit) :
    eval model (.letE (.value ()) fun _ => body) = eval model body := by
  simp

theorem line_break_invariance (model : Model World Name Value Edit Candidate)
    (first second : Expr Name Value Edit) :
    evalForms model first [second] = eval model (.seq first second) := rfl

theorem evalForms_append (model : Model World Name Value Edit Candidate)
    (first : Expr Name Value Edit) (middle : List (Expr Name Value Edit))
    (next : Expr Name Value Edit) (rest : List (Expr Name Value Edit)) :
    evalForms model first (middle ++ next :: rest) =
      (evalForms model first middle).bind fun _ => evalForms model next rest := by
  induction middle generalizing first with
  | nil => rfl
  | cons second middle ih =>
      simp only [List.cons_append, evalForms]
      rw [ih, Search.bind_assoc]

theorem sequence_associative (model : Model World Name Value Edit Candidate)
    (first second third : Expr Name Value Edit) :
    eval model (.seq (.seq first second) third) =
      eval model (.seq first (.seq second third)) := by
  simp only [eval]
  rw [Search.bind_assoc]

/-- Revalidating a compiled stretch at the bind boundary gives exactly the
fresh plan in the world delivered by the preceding computation. -/
theorem compiled_stretch_after_prefix
    {A B : Type}
    (prior : Search World A)
    (available : World → Name → Bool)
    (translatedIn : A → World)
    (source : A → Source Name Value)
    (execute : A → Plan Name Value → Search World B) :
    prior.bind (fun answer =>
        Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability.enterRevalidated
          available (capture (available (translatedIn answer)) (source answer))
          (execute answer)) =
      prior.bind (fun answer =>
        Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability.enterLive
          available (source answer) (execute answer)) :=
  Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability.bind_revalidated_eq_live
    prior available translatedIn source execute

/-- The normal compiled stretch is the fast path when all decisions it read
still hold. -/
theorem compiled_stretch_fast_path
    {A : Type}
    (available : World → Name → Bool) (saved : Capture Name Value)
    (execute : Plan Name Value → Search World A) (world : World)
    (valid : Mettapedia.Machines.ReadOnlyQuery.checkReads
      (available world) saved.reads = true) :
    Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability.enterRevalidated
        available saved execute world =
      execute saved.plan world := by
  simp [Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability.enterRevalidated,
    refresh, valid]

/-- If one recorded decision changed, the slow path is exactly a fresh
translation of the whole reached stretch. -/
theorem compiled_stretch_slow_path
    {A : Type}
    (available : World → Name → Bool) (saved : Capture Name Value)
    (execute : Plan Name Value → Search World A) (world : World)
    (invalid : Mettapedia.Machines.ReadOnlyQuery.checkReads
      (available world) saved.reads = false) :
    Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability.enterRevalidated
        available saved execute world =
      execute (compile (available world) saved.source) world := by
  simp [Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability.enterRevalidated,
    refresh, invalid]

namespace Controls

inductive Change where
  | install
  deriving DecidableEq, Repr

def model : Model Bool Nat Nat Change Nat where
  update
    | .install, _ => true
  editValue _ := 0
  argumentModes _ _ := []
  holdArgument _ := 0
  data head _ := head
  candidates world head := if world && head = 7 then [11, 12] else []
  runCandidate candidate _ := Search.pure candidate

def installThenCall : Expr Nat Nat Change :=
  .seq (.edit .install) (.apply 7 .nil)

def carryThenInstall : Expr Nat Nat Change :=
  .letE (.value 7) fun carried =>
    .seq (.edit .install) (.value carried)

def choiceSharesWorld : Expr Nat Nat Change :=
  .choice installThenCall (.apply 7 .nil)

def argumentEditThenCandidates : Expr Nat Nat Change :=
  .apply 7 (.cons (.edit .install) .nil)

def heldModel : Model Bool Nat Nat Change Nat where
  update
    | .install, _ => true
  editValue _ := 0
  argumentModes world head :=
    if !world && head = 8 then [.hold] else [.evaluate]
  holdArgument _ := 41
  data _ arguments := arguments.headD 0
  candidates _ _ := []
  runCandidate candidate _ := Search.pure candidate

def heldModeIsReadBeforeArgument : Expr Nat Nat Change :=
  .apply 8 (.cons (.edit .install) .nil)

theorem edit_flows_to_next_application :
    (eval model installThenCall false).drain.1 = [11, 12] := by
  decide +kernel

theorem carried_value_is_not_retranslated :
    (eval model carryThenInstall false).drain.1 = [7] := by
  decide +kernel

/-- Candidate selection happens after evaluated arguments, so their effects
are visible to the equation lookup that this call fixes. -/
theorem candidate_selection_follows_argument_evaluation :
    (eval model argumentEditThenCandidates false).drain.1 = [11, 12] := by
  decide +kernel

theorem line_break_control :
    (evalForms model (.edit .install) [.apply 7 .nil] false).drain.1 =
      (eval model installThenCall false).drain.1 := by
  rfl

theorem alternatives_share_the_world_left_to_right :
    (eval model choiceSharesWorld false).drain.1 = [11, 12, 11, 12] := by
  decide +kernel

/-- The declaration-like mode read at application entry says to hold the
argument. The edit inside that argument therefore does not run and cannot
retroactively change the mode. -/
theorem argument_mode_precedes_argument_evaluation :
    (eval heldModel heldModeIsReadBeforeArgument false).drain = ([41], false) := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaWorldSemantics
