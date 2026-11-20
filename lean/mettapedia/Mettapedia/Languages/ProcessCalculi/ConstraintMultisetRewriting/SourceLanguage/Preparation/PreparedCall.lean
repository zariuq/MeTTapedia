import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Services
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Cost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation
import Mettapedia.GSLT.Dynamics.CacheCoherence

/-!
# Prepare a uniquely selected equation

A compile-time head test may exclude clauses whose head cannot unify
with the call. It counts occurrences, including repeated equal
equations. The admitted template stores the selected equation. Its
entry performs the same fresh opening as the source call.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedCall

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit FunctionVariables

abbrev Head := String ⊕ Int ⊕ Nat ⊕ Nat
abbrev Clause (D : Discipline MSig [] ()) := Equation mkeys [] () D.Ty

variable {D : Discipline MSig [] ()}

def candidate (head : Head) (equation : Clause D) : Bool :=
  match headCode equation.lhs with
  | none => true
  | some given => decide (given = head)

def candidates (program : Program mkeys [] () D.Ty) (head : Head) : List (Clause D) :=
  program.equations.filter (candidate head)

structure Plan (program : Program mkeys [] () D.Ty) (head : Head) where
  selected : Clause D
  only : candidates program head = [selected]

/-- The filter preserves occurrences and counts duplicates separately.
Only the selected equation is retained as execution data. -/
def compile (program : Program mkeys [] () D.Ty) (head : Head) : Option (Plan program head) :=
  match found : candidates program head with
  | [selected] => some ⟨selected, found⟩
  | _ => none

theorem Plan.selection {program : Program mkeys [] () D.Ty} {head : Head} (plan : Plan program head) :
    ∃ before after, program.equations = before ++ plan.selected :: after ∧
      ∀ other ∈ before ++ after, candidate head other = false := by
  cases findFirst (candidate head) program.equations with
  | absent missing =>
    have empty := List.filter_eq_nil_iff.mpr fun equation member =>
      Bool.eq_false_iff.mp (missing equation member)
    have only := plan.only
    unfold candidates at only
    rw [empty] at only
    cases only
  | found before chosen after split accepted =>
    have only := plan.only
    rw [candidates, split, List.filter_append, List.filter_cons_of_pos accepted] at only
    have count := congrArg List.length only
    simp only [List.length_append, List.length_cons, List.length_nil] at count
    have fore : (before.filter (candidate head)).length = 0 := by omega
    have aft : (after.filter (candidate head)).length = 0 := by omega
    have same : chosen = plan.selected := by
      simpa [List.length_eq_zero_iff.mp fore, List.length_eq_zero_iff.mp aft] using only
    refine ⟨before, after, by rw [← same]; exact split, ?_⟩
    intro other member
    rcases List.mem_append.mp member with earlier | later
    · exact Bool.eq_false_iff.mpr (List.filter_eq_nil_iff.mp (List.length_eq_zero_iff.mp fore) other earlier)
    · exact Bool.eq_false_iff.mpr (List.filter_eq_nil_iff.mp (List.length_eq_zero_iff.mp aft) other later)

/-- Retaining the ordered head observation retains the actual compiled
equation, even across changes to excluded equations. -/
def Plan.rebind {program current : Program mkeys [] () D.Ty} {head : Head} (plan : Plan program head)
    (reading : candidates current head = candidates program head) : Plan current head :=
  ⟨plan.selected, reading.trans plan.only⟩

open Mettapedia.GSLT.Dynamics.CacheCoherence (Notifies execute)

def Plan.afterPublications {Edit : Type} {program : Program mkeys [] () D.Ty} {head : Head}
    (plan : Plan program head) (publish : Program mkeys [] () D.Ty → Edit → Program mkeys [] () D.Ty)
    (valid : Program mkeys [] () D.Ty → Prop) (stamp : Program mkeys [] () D.Ty → Head → Nat)
    (notifies : Notifies publish valid stamp candidates) (started : valid program)
    (edits : List Edit) (accepted : stamp (execute publish program edits) head = stamp program head) :
    Plan (execute publish program edits) head :=
  plan.rebind (notifies.observe_execute_of_counter_eq started edits head accepted)

theorem excluded_is_dead {knowledge : List (Constraint mkeys [] ())} {equation : Clause D}
    {call : MData} {head : Head} (position : Nat)
    (identified : headCode call = some head) (excluded : candidate head equation = false) :
    ¬ Solvable (knowledge ++ [(instantiate (copyAt mkeys position) equation.lhs, call)]) := by
  cases code : headCode equation.lhs with
  | none => simp [candidate, code] at excluded
  | some key =>
    have differs : key ≠ head := by simpa [candidate, code] using excluded
    exact dead_of_heads (headCode_instantiate (copyAt mkeys position) _ code) identified differs

def enter {program : Program mkeys [] () D.Ty} {head : Head} (plan : Plan program head)
    (world : World mkeys [] ()) (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () D.Ty)) (cells : List (MData × Comp mkeys [] () D.Ty)) :
    Branch mkeys [] () D.Ty :=
  callBranch D world.scope knowledge call frames cells plan.selected

theorem enter_refines {program : Program mkeys [] () D.Ty} {head : Head}
    (plan : Plan program head) {supply : Nat → MClosed}
    {start : Config mkeys [] () D.Ty} {world : World mkeys [] ()}
    {knowledge : List (Constraint mkeys [] ())} {call : MData}
    {frames : List (Frame mkeys [] () D.Ty)} {cells : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D program supply start world ⟨knowledge, .eval (.apply call), frames, cells⟩)
    (identified : headCode call = some head) :
    Along D program supply start world.fresh (enter plan world knowledge call frames cells) := by
  obtain ⟨before, after, split, excludes⟩ := plan.selection
  exact along.call before plan.selected after split
    (fun other member => excluded_is_dead world.scope identified (excludes other member))

inductive Decline where
  | head | unrepresentable | capacity | unsolved
  deriving DecidableEq

/-- Entry checks the shape and resource requirements before publishing
the fresh binding. Refusals expose only a reason, so the caller still
has the exact source application for ordinary evaluation. -/
def activate {program : Program mkeys [] () D.Ty} {head : Head} (plan : Plan program head)
    (solver : Solver mkeys [] ()) (world : World mkeys [] ())
    (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () D.Ty)) (cells : List (MData × Comp mkeys [] () D.Ty))
    (representable fits : Branch mkeys [] () D.Ty → Bool) :
    Except Decline (Branch mkeys [] () D.Ty) :=
  if headCode call = some head then
    let next := enter plan world knowledge call frames cells
    if !representable next then .error .unrepresentable
    else if !fits next then .error .capacity
    else if solver.satisfiable next.store then .ok next else .error .unsolved
  else .error .head

theorem activate_conditions {program : Program mkeys [] () D.Ty} {head : Head}
    (plan : Plan program head) (solver : Solver mkeys [] ()) (world : World mkeys [] ())
    (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () D.Ty)) (cells : List (MData × Comp mkeys [] () D.Ty))
    (representable fits : Branch mkeys [] () D.Ty → Bool) {next : Branch mkeys [] () D.Ty}
    (accepted : activate plan solver world knowledge call frames cells representable fits = .ok next) :
    next = enter plan world knowledge call frames cells ∧ headCode call = some head ∧ Solvable next.store := by
  unfold activate at accepted
  split at accepted
  · rename_i identified
    dsimp only at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · split at accepted
        · rename_i solved
          cases accepted
          exact ⟨rfl, identified, (solver.satisfiable_iff _).mp solved⟩
        · cases accepted
  · cases accepted

theorem activate_sound {program : Program mkeys [] () D.Ty} {head : Head}
    (plan : Plan program head) (solver : Solver mkeys [] ()) {supply : Nat → MClosed}
    {start : Config mkeys [] () D.Ty} {world : World mkeys [] ()}
    {knowledge : List (Constraint mkeys [] ())} {call : MData}
    {frames : List (Frame mkeys [] () D.Ty)} {cells : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D program supply start world ⟨knowledge, .eval (.apply call), frames, cells⟩)
    (representable fits : Branch mkeys [] () D.Ty → Bool) {next : Branch mkeys [] () D.Ty}
    (computed : activate plan solver world knowledge call frames cells representable fits = .ok next) :
    Along D program supply start world.fresh next ∧ Solvable next.store := by
  obtain ⟨rfl, identified, live⟩ :=
    activate_conditions plan solver world knowledge call frames cells representable fits computed
  exact ⟨enter_refines plan along identified, live⟩

/-- The selected alternative can be resumed by the full evaluator.
The source run reinstates the earlier dead alternatives as a frame.
Their presence leaves the observations and quiescence of the reached
configuration unchanged. -/
theorem handback_refines {program : Program mkeys [] () D.Ty} {supply : Nat → MClosed}
    {start finish : Config mkeys [] () D.Ty} {world : World mkeys [] ()}
    {selected : Branch mkeys [] () D.Ty} {strategy : Strategy mkeys [] () D.Ty}
    {work : List (Charge MData)}
    (along : Along D program supply start world selected) (live : Solvable selected.store)
    (resumed : ChargedRun D program supply strategy ⟨world, {selected}⟩ work finish) :
    ∃ whole, Runs D program supply start whole ∧
      Observation.observe (D := D) whole = Observation.observe (D := D) finish ∧
      (Config.Quiescent (D := D) program supply finish → Config.Quiescent (D := D) program supply whole) := by
  obtain ⟨dead, noMoves, earlier⟩ := along
  refine ⟨⟨finish.world, finish.branches + dead⟩, ?_,
    Observation.observe_add_dead (D := D) finish dead noMoves, ?_⟩
  · have continuing := Runs.frame resumed.source dead
    rw [Multiset.singleton_add] at continuing
    exact (earlier live).trans continuing
  · intro done branch appears liveBranch next replies moved
    rcases Multiset.mem_add.mp appears with old | discarded
    · exact done branch old liveBranch next replies moved
    · exact noMoves branch discarded liveBranch

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedCall
