import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaWorldSemantics
import Mettapedia.Languages.MeTTa.PeTTa.LibTransformRunner

/-!
# Translation decisions on resumption

Both policies use the same ordered, world-threaded `Search`. In particular,
both keep the selected candidates of an entered call. The distinction is the
time at which pending executable code reads its **translation interface**.

* Live evaluation reads the interface in the world where the code runs.
* Edits-only evaluation reads it there on entry and after an edit boundary.
  At a choice-only resumption it uses the prepared decisions. Execution still
  runs in the current world, so a retained direct call can see newly installed
  equations for its predicate.

This is a model of the policies, with edges given by the lowering. In the SWI
experiment an edit boundary is inferred from a possible edit, so it can also
be crossed on redo or when no edit actually happened. Applying the results
to that implementation requires a correspondence between its lowering and
these abstract edges.

The transform example uses the authored `transformWith` and its actual
search residual. It retains the pending proposals while routing each firing
from the reached store. Selection, routing, and prior values have distinct
lifetimes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionSemantics

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search Trace)
open Mettapedia.Machines.ReadOnlyQuery (Program run Agrees)
open PeTTaWorldSemantics

inductive Policy where
  | live
  | editsOnly

inductive Boundary where
  | entry
  | afterEdit
  | resume

variable {World Key Fact Plan A : Type}

/-- Use the chosen translation view, then run the plan in the actual world. -/
def evalAt (policy : Policy) (boundary : Boundary) (observe : World → Key → Fact)
    (preparedIn : World) (prepare : Program Key Fact Plan)
    (execute : Plan → Search World A) : Search World A :=
  match policy, boundary with
  | .editsOnly, .resume => execute (run (observe preparedIn) prepare).answer
  | _, _ => DecisionStaging.enterLive observe prepare execute

@[simp] theorem evalAt_live (boundary : Boundary) (observe : World → Key → Fact)
    (preparedIn : World) (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    evalAt .live boundary observe preparedIn prepare execute =
      DecisionStaging.enterLive observe prepare execute := by
  cases boundary <;> rfl

@[simp] theorem evalAt_entry (policy : Policy) (observe : World → Key → Fact)
    (preparedIn : World) (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    evalAt policy .entry observe preparedIn prepare execute =
      DecisionStaging.enterLive observe prepare execute := by
  cases policy <;> rfl

@[simp] theorem evalAt_afterEdit (policy : Policy) (observe : World → Key → Fact)
    (preparedIn : World) (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    evalAt policy .afterEdit observe preparedIn prepare execute =
      DecisionStaging.enterLive observe prepare execute := by
  cases policy <;> rfl

/-- Full liveness can use a saved translation and refresh it only when a
read fails validation. Equality covers the first result and all resumptions
of the returned search. -/
theorem checked_resume_eq_live [DecidableEq Fact] (observe : World → Key → Fact)
    (preparedIn : World) (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    DecisionStaging.enterRevalidated observe
        (DecisionStaging.capture (observe preparedIn) prepare) execute =
      evalAt .live .resume observe preparedIn prepare execute :=
  DecisionStaging.enterRevalidated_eq_live observe preparedIn prepare execute

/-- A difference between policies requires a changed observation on the
prepared read path. Other facts and the current equation rows may differ. -/
theorem resume_eq_live_of_agrees (observe : World → Key → Fact) {preparedIn current : World}
    (prepare : Program Key Fact Plan) (execute : Plan → Search World A)
    (agrees : Agrees (observe current) (run (observe preparedIn) prepare).reads) :
    evalAt .editsOnly .resume observe preparedIn prepare execute current =
      evalAt .live .resume observe preparedIn prepare execute current := by
  change execute (run (observe preparedIn) prepare).answer current =
    execute (run (observe current) prepare).answer current
  rw [Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees _ _ _ agrees]

/-- The interval may include writes by the consumer of a suspended answer.
Its bound is expressed on observations, so it can include arities,
declarations, or dispatch rules in addition to whether a name is callable. -/
def ChangesWithin (observe : World → Key → Fact) (writes : Key → Prop)
    (before after : World) : Prop :=
  ∀ key, ¬ writes key → observe after key = observe before key

theorem ChangesWithin.trans {observe : World → Key → Fact} {left right : Key → Prop}
    {before middle after : World} (first : ChangesWithin observe left before middle)
    (second : ChangesWithin observe right middle after) :
    ChangesWithin observe (fun key => left key ∨ right key) before after := by
  intro key outside
  exact (second key (fun present => outside (.inr present))).trans
    (first key (fun present => outside (.inl present)))

/-- If every possible intervening write misses a continuation's read
certificate, full liveness permits ordinary compiled execution at this
edge, with no runtime check. Negative reads are among the dependencies. -/
theorem resume_eq_unchecked_of_disjoint (observe : World → Key → Fact)
    {preparedIn current : World} {writes : Key → Prop}
    (prepare : Program Key Fact Plan) (execute : Plan → Search World A)
    (within : ChangesWithin observe writes preparedIn current)
    (disjoint : ∀ read ∈ (run (observe preparedIn) prepare).reads, ¬ writes read.1) :
    evalAt .live .resume observe preparedIn prepare execute current =
      execute (run (observe preparedIn) prepare).answer current := by
  symm
  apply resume_eq_live_of_agrees observe prepare execute
  intro read listed
  exact (within read.1 (disjoint read listed)).trans
    (Mettapedia.Machines.ReadOnlyQuery.run_agrees _ _ read listed)

/-- A fresh continuation has no dependency on a previous preparation world.
This applies equally after a bind, in a later alternative, and inside a
fresh wrapper. The edits-only counterexample below distinguishes the last
two positions. -/
theorem live_resume_eq_fresh_entry (policy : Policy) (observe : World → Key → Fact)
    (preparedIn other : World) (prepare : Program Key Fact Plan)
    (execute : Plan → Search World A) :
    evalAt .live .resume observe preparedIn prepare execute =
      evalAt policy .entry observe other prepare execute := by
  simp

/-- The modes belong to the already entered application. An edit by one
argument is visible to the remaining source evaluations and later equation
lookup. The remaining arguments keep the modes picked at entry. -/
theorem argument_edit_keeps_entry_modes {Name Value Edit Candidate : Type}
    (model : Model World Name Value Edit Candidate) (world : World)
    (head : Name) (edit : Edit) (rest : Exprs Name Value Edit)
    (modes : List ArgumentMode)
    (atEntry : model.argumentModes world head = .evaluate :: modes) :
    eval model (.apply head (.cons (.edit edit) rest)) world =
      ((evalArgs model modes rest).bind fun values =>
        invokeAtEntry model head (model.editValue edit :: values)) (model.update edit world) := by
  simp only [eval, atEntry, evalArgs,
    Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Search.bind,
    Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.bind, Trace.append_done]
  rw [Trace.bind_assoc]
  simp only [Search.pure, Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Trace.bind,
    Trace.append_done]

namespace Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa (Answers)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Store Sources transformWith)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open PeTTaWorldSemantics (Expr Model eval invokeAtEntry)
open PeTTaWorldSemantics.Search (pure append)

private def helper : Atom := .expression [.symbol "helper"]
private def value : Atom := .grounded (.int 42)
private def truth : Atom := .symbol "true"

private def equation (name : String) (body : Atom) : Atom :=
  .expression [.symbol "=", .expression [.symbol name], body]

private def installed : Atom := equation "helper" value

/-- A nullary fragment suffices to distinguish the read times. A stored row
identifies a candidate. Its body here is an opaque value. -/
private def equations (world : Store) (head : String) : List Atom :=
  world.filterMap fun row => match row with
  | .expression [.symbol "=", .expression [.symbol name], body] =>
      if name = head then some body else none
  | _ => none

private def nullaryModel : Model Store String Atom Atom Atom where
  update row world := world ++ [row]
  editValue _ := truth
  argumentModes _ _ := []
  holdArgument _ := .symbol "held"
  data head args := .expression (.symbol head :: args)
  candidates := equations
  runCandidate candidate _ := pure candidate

private def install : Search Store Atom := eval nullaryModel (.edit installed)

private def observe (world : Store) (head : String) : Bool := !(equations world head).isEmpty

private def named (policy : Policy) (boundary : Boundary) (preparedIn : Store)
    (head : String) : Search Store Atom :=
  evalAt policy boundary observe preparedIn (.read head .pure) fun callable =>
    if callable then invokeAtEntry nullaryModel head [] else pure (nullaryModel.data head [])

/-- The live version of the experiment agrees with the independent source
evaluator on every nullary call in this fragment. -/
theorem live_named_eq_source (boundary : Boundary) (preparedIn : Store) (head : String) :
    named .live boundary preparedIn head = eval nullaryModel (.apply head .nil) := by
  funext world
  rw [named, evalAt_live]
  simp only [DecisionStaging.enterLive, run, observe, eval,
    PeTTaWorldSemantics.evalArgs, PeTTaWorldSemantics.Search.pure_bind]
  by_cases empty : equations world head = []
  · simp [empty, invokeAtEntry, nullaryModel]
  · simp [empty]

theorem forward_edit :
    ((install.bind fun _ => named .editsOnly .afterEdit [] "helper") []).drain.1 = [value] ∧
    ((install.bind fun _ => named .live .afterEdit [] "helper") []).drain.1 = [value] := by
  decide +kernel

theorem later_alternative :
    (append install (named .editsOnly .resume [] "helper") []).drain.1 = [truth, helper] ∧
    (append install (named .live .resume [] "helper") []).drain.1 = [truth, value] := by
  decide +kernel

/-- Replacing the later expression by a fresh invocation of a wrapper around
it changes the edits-only result. The wrapper has no effects of its own. -/
theorem fresh_wrapper_changes_editsOnly :
    (append install (named .editsOnly .entry [] "helper") []).drain.1 = [truth, value] ∧
    (append install (named .editsOnly .resume [] "helper") []).drain.1 ≠
      (append install (named .editsOnly .entry [] "helper") []).drain.1 := by
  decide +kernel

theorem existing_call_reads_new_equations :
    let before := [equation "helper" (.symbol "old")]
    (append install (named .editsOnly .resume before "helper") before).drain.1 =
        [truth, .symbol "old", value] ∧
    (append install (named .live .resume before "helper") before).drain.1 =
        [truth, .symbol "old", value] := by
  decide +kernel

private def colorRules : Store :=
  [equation "color" (.symbol "red"), equation "color" (.symbol "blue")]

private def color (policy : Policy) : Search Store Atom :=
  (PeTTaLiveCallability.candidatesAtEntry fun world => equations world "color").bind
    fun body =>
      if body = .symbol "blue" then named policy .resume colorRules "helper" else pure body

private def consumeColor (answer : Atom) : Search Store Atom := fun world =>
  if answer = .symbol "red" then
    pure answer (world ++ [installed, equation "color" (.symbol "green")])
  else pure answer world

/-- A consumer changes the interface of the next body without reopening the
entered call's clause selection. Neither run can see the newly added `green`
candidate in that call. -/
theorem entered_call_retains_candidates_and_resumes_body :
    ((color .editsOnly).bind consumeColor colorRules).drain.1 = [.symbol "red", helper] ∧
    ((color .live).bind consumeColor colorRules).drain.1 = [.symbol "red", value] ∧
    equations (colorRules ++ [installed, equation "color" (.symbol "green")]) "color" =
      [.symbol "red", .symbol "blue", .symbol "green"] := by
  decide +kernel

private def installButFail : Search Store Atom :=
  install.bind fun _ => Trace.done

theorem answerless_edit_reaches_next_alternative :
    (append installButFail (named .editsOnly .resume [] "helper") []).drain =
        ([helper], [installed]) ∧
    (append installButFail (named .live .resume [] "helper") []).drain =
        ([value], [installed]) := by
  decide +kernel

/-- Independent requests exhaust each search, and bind runs its suffix per
answer. Regrouping a sequence and collecting separate requests are distinct
operations. -/
theorem collecting_requests_and_binding_differ :
    (named .live .entry [] "helper" (installButFail []).drain.2).drain = ([value], [installed]) ∧
    ((installButFail.bind fun _ => named .live .afterEdit [] "helper") []).drain =
      ([], [installed]) := by
  decide +kernel

private def one : Atom := .grounded (.int 1)
private def two : Atom := .grounded (.int 2)
private def three : Atom := .grounded (.int 3)
private def addition : Atom := .expression [.symbol "+", one, two]

/-- The Boolean models whether the declaration holding argument two has
been installed. The only held expression used by the control is `(+ 1 2)`. -/
private def modeModel : Model Bool String Atom Unit String where
  update _ _ := true
  editValue _ := truth
  argumentModes world head :=
    if world && head == "two-arg" then [.evaluate, .hold] else [.evaluate, .evaluate]
  holdArgument _ := addition
  data head args := .expression (.symbol head :: args)
  candidates _ head := [head]
  runCandidate head args :=
    if head = "+" then pure three else pure (.expression (.symbol "held" :: args))

private def twoArg (first : Expr String Atom Unit) : Expr String Atom Unit :=
  let plus : Expr String Atom Unit := .apply "+" (.cons (.value one) (.cons (.value two) .nil))
  .apply "two-arg" (.cons first (.cons plus .nil))

/-- A new declaration can change the next invocation without changing the
current invocation's argument modes. -/
theorem argument_declaration_affects_the_next_invocation :
    (eval modeModel (twoArg (.edit ())) false).drain =
      ([.expression [.symbol "held", truth, three]], true) ∧
    (eval modeModel (twoArg (.value truth)) true).drain =
      ([.expression [.symbol "held", truth, addition]], true) := by
  decide +kernel

/-! ### Transform demand and an intervening installation -/

private def start : Store := [.symbol "red", .symbol "blue"]

private def transformSources : Sources := ⟨[.pat .take (.var "x")], [], none⟩

private def emit : Subst → Answers :=
  Mettapedia.Languages.MeTTa.PeTTa.LibTransform.instances (.var "x")

private def route (policy : Policy) (packet : Answers) : Search Store Atom :=
  if packet = [.symbol "red"] then pure (.symbol "red") else named policy .resume start "helper"

private def afterConsumer (store : Store) : Store := store ++ [installed, .symbol "green"]

/-- Observe the first answer, let its consumer install data and an equation,
then observe the actual continuation. -/
private def consumeFirst : Trace Store Atom → Option (Atom × Store × (List Atom × Store))
  | .done _ => none
  | .answer first here resume => some (first, here, (resume (afterConsumer here)).drain)

private def transformRun (policy : Policy) : Search Store Atom :=
  transformWith (route policy) transformSources emit

theorem transform_first_answer_preserves_pending_work (policy : Policy) :
    (Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Search.once (transformRun policy) start).drain =
      ([.symbol "red"], [.symbol "blue"]) := by
  cases policy <;> decide +kernel

/-- First-answer demand consumes only the first take. The caller can add an
equation and a new row before resuming. The residual retains the old proposal
for blue and leaves the new green row untouched. Only the live route reads
the newly callable `helper`. -/
theorem transform_resume_respects_demand_and_current_interface :
    consumeFirst (transformRun .live start) =
      some (.symbol "red", [.symbol "blue"], ([value], [installed, .symbol "green"])) ∧
    consumeFirst (transformRun .editsOnly start) =
      some (.symbol "red", [.symbol "blue"], ([helper], [installed, .symbol "green"])) := by
  decide +kernel

/-- The library's prepared runner exposes the same residual after a first
answer, including its response to the consumer's writes. -/
theorem prepared_transform_resumes_the_same_search (policy : Policy) :
    let guides := Mettapedia.Languages.MeTTa.PeTTa.LibTransform.proposals start transformSources
    consumeFirst (Mettapedia.Languages.MeTTa.PeTTa.LibTransform.resumeGuides
        (route policy) transformSources emit guides start) =
      consumeFirst (transformRun policy start) :=
  congrArg consumeFirst
    (Mettapedia.Languages.MeTTa.PeTTa.LibTransform.resumeGuides_eq_transformWith
      (route policy) transformSources emit start)

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionSemantics
