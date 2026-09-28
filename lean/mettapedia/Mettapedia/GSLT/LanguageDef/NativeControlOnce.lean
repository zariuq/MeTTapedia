import Mettapedia.GSLT.LanguageDef.HostGoalScopes
import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters

/-!
# Local commitment across native and host control

A `once` delimiter owns all alternatives created while evaluating its operand,
including residual host nodes.  Its successful return carries the witness's
context into a commit instruction.  The commit drops exactly that segment and
continues above the unchanged outer frontier.

The first section uses `withHostCut` directly: one host pull, one return through
the delimiter frame, and one cut implement this protocol.  In particular,
cutting only a host's private state or only native choices is insufficient.

The reusable adapter below places a local delimiter around a `CProgram` frontier.
Its values, contexts, calls and base frames are arbitrary; higher-order closures
can therefore be values without changing the control law.  These are operational
model theorems, not a verification of the C representation or resource release.

The source operand includes all constraints already installed by its language's
evaluation rules.  These laws neither postpone those constraints nor authorize
moving additional constraints across the delimiter.  In particular, PeTTa's
outer `let` can constrain the operand before `once` starts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlOnce

open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.LanguageDef.HostGoals
open Mettapedia.GSLT.LanguageDef.HostGoals.Scopes
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats repeats_add)

variable {C K Call F A HState : Type}

/-- A successful host answer returns through the local delimiter, then removes
both its residual host node and all native alternatives inside that delimiter.
The witness context comes from the answer's return, not the entry context. -/
theorem host_yield_resume_cut
    (P : CProgram C K Call F A) (isHost : Call → Bool)
    (H : Host (C × Call) HState (C × A))
    (entry : C) {h h' : HState} {answer : C × A} (frame : F)
    (outer : List (F × Option Nat))
    (inside below : List (CTask C (Node K HState A) F))
    (scope : Option Nat) (emitted : List (C × A)) {next : K}
    (pulled : H.pull h = .yield answer h')
    (committing : P.inspect (P.resume answer.1 frame answer.2).2 = .cut next) :
    repeats (cstep (withHostCut P isHost H)) 3
      ⟨⟨entry, .host h, (frame, some below.length) :: outer, scope⟩ ::
        (inside ++ below), emitted⟩ =
      ⟨⟨(P.resume answer.1 frame answer.2).1, .run next, outer,
          some below.length⟩ :: below, emitted⟩ := by
  rw [show 3 = 1 + 2 from rfl, repeats_add]
  simp only [repeats, cstep_host_yield P isHost H entry _ scope _ emitted pulled]
  simp only [cstep, cexpand, withHostCut, liftInstr, List.append_nil]
  rw [committing]
  simp only [List.append_nil]
  rw [show
    keepBelow (some below.length)
      (⟨entry, .host h', (frame, some below.length) :: outer,
          some (inside ++ below).length⟩ :: (inside ++ below)) = below from
    keepBelow_append (_ :: inside) below]

/-- Once the witness has returned to the delimiter, commitment needs no host
pull.  Any host implementation gives the same two administrative steps. -/
theorem commit_suffix_host_independent
    (P : CProgram C K Call F A) (isHost : Call → Bool)
    (H : Host (C × Call) HState (C × A))
    (answer : C × A) (frame : F) (outer : List (F × Option Nat))
    (inside below : List (CTask C (Node K HState A) F))
    (scope : Option Nat) (emitted : List (C × A)) {next : K}
    (committing : P.inspect (P.resume answer.1 frame answer.2).2 = .cut next) :
    repeats (cstep (withHostCut P isHost H)) 2
      ⟨⟨answer.1, .answer answer.2, (frame, some below.length) :: outer, scope⟩ ::
        (inside ++ below), emitted⟩ =
      ⟨⟨(P.resume answer.1 frame answer.2).1, .run next, outer,
          some below.length⟩ :: below, emitted⟩ := by
  simp only [repeats, cstep, cexpand, withHostCut, liftInstr, List.append_nil]
  rw [committing]
  simp only [List.append_nil, keepBelow_append]

/-- The adapter separates ordinary base frames from the delimiter return. -/
inductive Frame (F : Type) where
  | base (frame : F)
  | first
  deriving DecidableEq

/-- A commit instruction runs before the witness is returned to the caller. -/
inductive Control (K A : Type) where
  | run (control : K)
  | commit (value : A)
  | answer (value : A)
  deriving DecidableEq

/-- Base instructions preserve their calls and scopes in the adapter. -/
def liftInstruction : CInstruction Call F A K → CInstruction Call (Frame F) A (Control K A)
  | .ret a => .ret a
  | .fail => .fail
  | .call c f => .call c (.base f)
  | .tail c => .tail c
  | .enter c f => .enter c (.base f)
  | .cut k => .cut (.run k)

/-- A local `once` needs just a return frame and a cut continuation. -/
def program (P : CProgram C K Call F A) :
    CProgram C (Control K A) Call (Frame F) A where
  inspect
    | .run k => liftInstruction (P.inspect k)
    | .commit a => .cut (.answer a)
    | .answer a => .ret a
  branches c call := (P.branches c call).map fun next => (next.1, .run next.2)
  resume c frame a := match frame with
    | .base f => ((P.resume c f a).1, .run (P.resume c f a).2)
    | .first => (c, .commit a)

/-- The delimiter shifts every base scope above its outside frontier.  A cut
at the operand's own level reaches the local delimiter, not the caller's. -/
def scopeAt (base : Nat) : Option Nat → Option Nat :=
  shiftScope base (some base)

def liftTask (base : Nat) (outer : List (Frame F × Option Nat)) (t : CTask C K F) :
    CTask C (Control K A) (Frame F) :=
  ⟨t.context, .run t.control,
    t.returns.map (fun f => (.base f.1, scopeAt base f.2)) ++
      ((.first, some base) :: outer), scopeAt base t.scope⟩

def initial (tasks : List (CTask C K F))
    (below : List (CTask C (Control K A) (Frame F)))
    (outer : List (Frame F × Option Nat)) (emitted : List (C × A)) :
    CState C (Control K A) (Frame F) A :=
  ⟨tasks.map (liftTask below.length outer) ++ below, emitted⟩

/-- Administrative commitment preserves the witness context and outer
continuation, and it drops every remaining alternative in one step. -/
theorem commit_step (P : CProgram C K Call F A) (answer : C × A)
    (inside below : List (CTask C (Control K A) (Frame F)))
    (outer : List (Frame F × Option Nat)) (emitted : List (C × A)) :
    cstep (program P)
      ⟨⟨answer.1, .commit answer.2, outer, some below.length⟩ ::
        (inside ++ below), emitted⟩ =
      ⟨⟨answer.1, .answer answer.2, outer, some below.length⟩ :: below, emitted⟩ := by
  simp [cstep, cexpand, program, keepBelow_append]

/-- Shifting a cut scope preserves exactly the local suffix while protecting
the outside frontier. -/
theorem keepBelow_scopeAt (scope : Option Nat) (xs : List (CTask C K F))
    (below : List (CTask C (Control K A) (Frame F)))
    (outer : List (Frame F × Option Nat)) :
    keepBelow (scopeAt below.length scope) (xs.map (liftTask below.length outer) ++ below) =
      (keepBelow scope xs).map (liftTask below.length outer) ++ below := by
  cases scope with
  | none => simp [scopeAt, shiftScope, keepBelow]
  | some n =>
      simp only [scopeAt, shiftScope, keepBelow, List.length_append, List.length_map]
      rw [show xs.length + below.length - (n + below.length) = xs.length - n by omega]
      rw [List.drop_append_of_le_length (by simp), List.map_drop]

/-- Each operand step executes once under the delimiter.  A successful return
is intercepted as a commit node; quiet steps keep the source frontier mapped
above the unchanged caller frontier. -/
theorem expand_liftTask (P : CProgram C K Call F A) (t : CTask C K F)
    (rest : List (CTask C K F))
    (below : List (CTask C (Control K A) (Frame F)))
    (outer : List (Frame F × Option Nat)) :
    cexpand (program P) (liftTask below.length outer t)
      (rest.map (liftTask below.length outer) ++ below) =
    match (cexpand P t rest).2 with
    | [] => ((cexpand P t rest).1.map (liftTask below.length outer) ++ below, [])
    | answer :: _ =>
      (⟨answer.1, .commit answer.2, outer, some below.length⟩ ::
        (rest.map (liftTask below.length outer) ++ below), []) := by
  cases inspect : P.inspect t.control with
  | ret value =>
      cases frames : t.returns with
      | nil => simp [cexpand, program, liftTask, liftInstruction, inspect, frames]
      | cons frame frames =>
          rcases frame with ⟨frame, scope⟩
          simp [cexpand, program, liftTask, liftInstruction, *]
  | fail => simp [cexpand, program, liftTask, liftInstruction, inspect]
  | call callee frame =>
      simp [cexpand, program, liftTask, liftInstruction, inspect, List.map_map,
        Function.comp_def, scopeAt, shiftScope]
  | tail callee =>
      simp [cexpand, program, liftTask, liftInstruction, inspect, List.map_map,
        Function.comp_def, scopeAt, shiftScope]
  | enter callee frame =>
      simp [cexpand, program, liftTask, liftInstruction, inspect, List.map_map,
        Function.comp_def]
  | cut next =>
      have keep := keepBelow_scopeAt t.scope rest below outer
      simp only [cexpand, program, liftTask, inspect, liftInstruction, List.map_cons]
      rw [keep]
      rfl

/-- The target state reached when the first-answer observer is decided.  No
answer leaves the delimiter until its operand has either failed or committed. -/
def decided (first : Option (C × A))
    (below : List (CTask C (Control K A) (Frame F)))
    (outer : List (Frame F × Option Nat)) (emitted : List (C × A)) :
    CState C (Control K A) (Frame F) A :=
  ⟨match first with
    | none => below
    | some answer => ⟨answer.1, .answer answer.2, outer, some below.length⟩ :: below,
    emitted⟩

/-- Bounded refinement to the existing first-answer observer.  Each source
suspension costs one target step; a successful return adds one local cut.  The
operand may contain cuts: its own-level cuts are confined to this delimiter. -/
theorem once_refines (P : CProgram C K Call F A)
    (below : List (CTask C (Control K A) (Frame F)))
    (outer : List (Frame F × Option Nat)) (emitted : List (C × A)) :
    ∀ (n : Nat) (tasks : List (CTask C K F)) (first : Option (C × A)),
      once (cpull P) n tasks = some first →
      ∃ steps ≤ n + 1, repeats (cstep (program P)) steps (initial tasks below outer emitted) =
        decided first below outer emitted
  | 0, _, _, observed => by simp [once] at observed
  | n + 1, [], first, observed => by
      simp only [once, cpull, Option.some.injEq] at observed
      subst first
      exact ⟨0, by omega, rfl⟩
  | n + 1, t :: rest, first, observed => by
      have mapped := expand_liftTask P t rest below outer
      rcases cexpand_delivers P t rest with quiet | ⟨answer, yields⟩
      · have observed' : once (cpull P) n (cexpand P t rest).1 = some first := by
          simpa [once, cpull, quiet] using observed
        obtain ⟨steps, bound, done⟩ := once_refines P below outer emitted n
          (cexpand P t rest).1 first observed'
        refine ⟨steps + 1, by omega, ?_⟩
        change repeats (cstep (program P)) steps
          (cstep (program P) (initial (t :: rest) below outer emitted)) = _
        rw [show cstep (program P) (initial (t :: rest) below outer emitted) =
            initial (cexpand P t rest).1 below outer emitted by
          simp only [initial, List.map_cons, List.cons_append, cstep_cons, mapped, quiet,
            List.append_nil]]
        exact done
      · have first_eq : first = some answer := by simpa [once, cpull, yields] using observed.symm
        subst first
        refine ⟨2, by omega, ?_⟩
        change cstep (program P) (cstep (program P)
          (initial (t :: rest) below outer emitted)) = _
        rw [show cstep (program P) (initial (t :: rest) below outer emitted) =
            ⟨⟨answer.1, .commit answer.2, outer, some below.length⟩ ::
              (rest.map (liftTask below.length outer) ++ below), emitted⟩ by
          simp only [initial, List.map_cons, List.cons_append, cstep_cons, mapped, yields,
            List.append_nil]]
        exact commit_step P answer _ below outer emitted

/-- After a local commit, dropping the wrapper's answer node does not permit
backtracking into the operand: only the preserved outside frontier remains. -/
theorem committed_return (P : CProgram C K Call F A) (answer : C × A)
    (below : List (CTask C (Control K A) (Frame F))) (emitted : List (C × A)) :
    cstep (program P) (decided (some answer) below [] emitted) =
      ⟨below, emitted ++ [answer]⟩ := by
  simp [decided, cstep, cexpand, program]

/-- A decided source observer gives a complete local run containing zero or one
answer occurrence, with the witness context intact. -/
theorem once_complete (P : CProgram C K Call F A) (n : Nat)
    (tasks : List (CTask C K F)) (first : Option (C × A))
    (observed : once (cpull P) n tasks = some first) :
    ∃ steps ≤ n + 2,
      repeats (cstep (program P)) steps (initial tasks [] [] []) =
        ⟨[], first.toList⟩ := by
  obtain ⟨steps, bound, done⟩ := once_refines P [] [] [] n tasks first observed
  cases first with
  | none => exact ⟨steps, by omega, done⟩
  | some answer =>
      refine ⟨steps + 1, by omega, ?_⟩
      rw [repeats_add, done]
      exact committed_return P answer [] []

private theorem repeats_nil (P : CProgram C K Call F A) (n : Nat) (emitted : List (C × A)) :
    repeats (cstep P) n ⟨[], emitted⟩ = ⟨[], emitted⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [repeats, cstep_nil] using ih

/-- No extra terminating behavior: a complete run of the local adapter reflects
to a decided source `once`, with precisely its zero or one answer occurrence.
Together with `once_complete`, this is finite two-sided adequacy. -/
theorem once_reflects (P : CProgram C K Call F A) :
    ∀ (n : Nat) (tasks : List (CTask C K F)),
      (repeats (cstep (program P)) n (initial tasks [] [] [])).frontier = [] →
      ∃ m first, once (cpull P) m tasks = some first ∧
        (repeats (cstep (program P)) n (initial tasks [] [] [])).emitted = first.toList
  | n, [], _ => ⟨1, none, rfl, by simp [initial, repeats_nil]⟩
  | 0, _ :: _, complete => by simp [repeats, initial] at complete
  | n + 1, t :: rest, complete => by
      have mapped := expand_liftTask P t rest [] []
      simp only [List.length_nil, List.append_nil] at mapped
      rcases cexpand_delivers P t rest with quiet | ⟨answer, yields⟩
      · have firstStep : cstep (program P) (initial (t :: rest) [] [] []) =
            initial (cexpand P t rest).1 [] [] [] := by
          simp only [initial, List.map_cons, cstep_cons, List.length_nil, List.append_nil]
          rw [mapped, quiet]
          rfl
        have complete' : (repeats (cstep (program P)) n
            (initial (cexpand P t rest).1 [] [] [])).frontier = [] := by
          simpa only [repeats, firstStep] using complete
        obtain ⟨m, first, observed, values⟩ := once_reflects P n (cexpand P t rest).1 complete'
        refine ⟨m + 1, first, ?_, ?_⟩
        · simpa [once, cpull, quiet] using observed
        · simpa only [repeats, firstStep] using values
      · have firstStep : cstep (program P) (initial (t :: rest) [] [] []) =
            ⟨⟨answer.1, .commit answer.2, [], some 0⟩ ::
              rest.map (liftTask 0 []), []⟩ := by
          simp only [initial, List.map_cons, cstep_cons, List.length_nil, List.append_nil]
          rw [mapped, yields]
          rfl
        have commitStep : cstep (program P)
            ⟨⟨answer.1, .commit answer.2, [], some 0⟩ ::
              rest.map (liftTask 0 []), []⟩ =
            decided (some answer) [] [] [] := by
          simpa [decided] using commit_step P answer (rest.map (liftTask 0 [])) [] [] []
        cases n with
        | zero => simp only [repeats, firstStep] at complete; cases complete
        | succ n =>
            cases n with
            | zero => simp only [repeats, firstStep, commitStep, decided] at complete; cases complete
            | succ n =>
                refine ⟨1, some answer, ?_, ?_⟩
                · simp [once, cpull, yields]
                · simp only [repeats, firstStep, commitStep, committed_return, List.nil_append]
                  rw [repeats_nil]
                  rfl

/-- Nested delimiters preserve the enclosing delimiter's alternatives as part
of their outside frontier. -/
theorem nested_commit_keeps_enclosing (P : CProgram C K Call F A) (answer : C × A)
    (inner enclosing outside : List (CTask C (Control K A) (Frame F)))
    (outer : List (Frame F × Option Nat)) (emitted : List (C × A)) :
    cstep (program P)
      ⟨⟨answer.1, .commit answer.2, outer, some (enclosing ++ outside).length⟩ ::
        (inner ++ enclosing ++ outside), emitted⟩ =
      ⟨⟨answer.1, .answer answer.2, outer, some (enclosing ++ outside).length⟩ ::
        (enclosing ++ outside), emitted⟩ := by
  simpa [List.append_assoc] using commit_step P answer inner (enclosing ++ outside) outer emitted

namespace Controls

inductive Code where
  | give (value : Nat)
  | commit (value : Nat)
  | fail
  deriving DecidableEq

/-- Context is a visible logical binding in these controls. -/
def base : CProgram Nat Code Unit Unit Nat where
  inspect
    | .give n => .ret n
    | .commit n => .cut (.give n)
    | .fail => .fail
  branches context _ := [(context + 7, .give 0), (context + 8, .give 1)]
  resume context _ answer := (context, .commit answer)

/-- Infinitely many possible host answers make a retained residual observable. -/
def host : Host (Nat × Unit) Nat (Nat × Nat) where
  start _ := 0
  pull n := .yield (n + 7, n) (n + 1)

def machine := withHostCut base (fun _ => true) host

def external : CTask Nat (Node Code Nat Nat) Unit := ⟨100, .run (.give 99), [], none⟩
def alternative : CTask Nat (Node Code Nat Nat) Unit := ⟨8, .run (.give 9), [], some 1⟩
def residual : CTask Nat (Node Code Nat Nat) Unit :=
  ⟨0, .host 1, [((), some 1)], some 1⟩

/-- The host's first binding escapes, both kinds of pending choice disappear,
and an alternative outside the delimiter still runs. -/
theorem cuts_across_host_and_tier :
    repeats (cstep machine) 5
      ⟨[⟨0, .host 0, [((), some 1)], none⟩, alternative, external], []⟩ =
      ⟨[], [(7, 0), (100, 99)]⟩ := by rfl

/-- Removing the host residual alone leaves the native alternative observable. -/
theorem host_only_cut_is_wrong :
    (repeats (cstep machine) 3
      ⟨[⟨7, .run (.give 0), [], some 1⟩, alternative, external], []⟩).emitted =
      [(7, 0), (8, 9), (100, 99)] := by decide

/-- Removing native alternatives alone permits another pull and another
witness.  Commitment must remove the residual host node too. -/
theorem tier_only_cut_is_wrong :
    (repeats (cstep machine) 6
      ⟨[⟨7, .run (.give 0), [], some 1⟩, residual, external], []⟩).emitted =
      [(7, 0), (8, 1), (100, 99)] := by decide

/-- Using the enclosing query's scope for the delimiter wrongly removes the
external alternative; a local `once` requires a local scope. -/
theorem enclosing_scope_is_wrong :
    (repeats (cstep machine) 5
      ⟨[⟨0, .host 0, [((), none)], none⟩, alternative, external], []⟩).emitted =
      [(7, 0)] := by decide

def source : List (CTask Nat Code Unit) :=
  [⟨7, .give 0, [], none⟩, ⟨8, .give 1, [], none⟩]

def callerAlternative : CTask Nat (Control Code Nat) (Frame Unit) :=
  ⟨100, .run (.give 99), [], none⟩

/-- Full adapter execution returns one witness then resumes outside search. -/
theorem adapter_preserves_binding_and_outside :
    repeats (cstep (program base)) 4 (initial source [callerAlternative] [] []) =
      ⟨[], [(7, 0), (100, 99)]⟩ := by rfl

/-- A failing operand produces no artificial value and resumes outside search. -/
theorem empty_operand :
    repeats (cstep (program base)) 2
      (initial [⟨7, .fail, [], none⟩] [callerAlternative] [] []) =
      ⟨[], [(100, 99)]⟩ := by rfl

/-- An own-level cut inside the operand is confined to the local delimiter. -/
theorem operand_cut_is_local :
    repeats (cstep (program base)) 5
      (initial [⟨7, .commit 0, [], none⟩, ⟨8, .give 1, [], none⟩]
        [callerAlternative] [] []) =
      ⟨[], [(7, 0), (100, 99)]⟩ := by rfl

def listPull : List Nat → Pull (List Nat) Nat
  | [] => .done
  | x :: xs => .yield x xs

/-- Moving a filter across an already specified delimiter can change the first
witness.  This does not require late destination matching: constraints already
inside the source operand must remain there. -/
theorem output_first_filter_changes_once :
    once listPull 1 [0, 1] = some (some 0) ∧
    once listPull 1 ([0, 1].filter (fun x => x == 1)) = some (some 1) ∧
    (some 0 : Option Nat).filter (fun x => x == 1) = none := by decide

/-- An initially constrained operand succeeds with `2`; imposing that same
constraint after an unconstrained first-answer selection fails.  The source
language decides which program is meant, and refinement must preserve it. -/
theorem initially_constrained_operand_succeeds :
    once listPull 1 ([1, 2].filter (fun x => x == 2)) = some (some 2) ∧
    (once listPull 1 [1, 2]).map (fun first => first.filter (fun x => x == 2)) =
      some none := by decide

/-- The answer carrier can contain higher-order values without a new control
mechanism.  The general refinement theorem applies to this program as well. -/
def higherOrder : CProgram Unit (Nat → Nat) Unit Unit (Nat → Nat) where
  inspect f := .ret f
  branches _ _ := [((), fun x => x + 10), ((), fun x => x + 20)]
  resume _ _ f := ((), f)

theorem higher_order_witness :
    ((repeats (cstep (program higherOrder)) 3
      (initial [⟨(), fun x => x + 10, [], none⟩, ⟨(), fun x => x + 20, [], none⟩]
        [] [] [])).emitted.map (fun answer => answer.2 3)) = [13] := by rfl

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlOnce
