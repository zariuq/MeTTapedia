import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.HostedAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedExample

/-!
# Hosted world histories with fresh aliases and competing origins

The controls use the existing hosted examples. Two calls using the same
equation occurrence may end at different physical rows while keeping one
answer. Calls using distinct equal equations retain distinct rigid origins.
Independent returns give a real source square with one final answer bag and
different ordered prefix observations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.HostedAnswers.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting Hosting.Alternatives
open RuleSyntax RuleSyntax.Worlds RuleSyntax.RuleOccurrences RuleSyntax.StepWeb
open Hosting.Alternatives.Controls (N D supply one dupP q3 dupP_plain emptyP emptyP_plain)
open Counted.Example (callRet q3_unopened)
open Classical

private theorem world_injective : Function.Injective (world (D := D) N dupP) := by
  intro first second same
  have systems := congrArg Bag.worlds same
  have sameSystem := Multiset.singleton_inj.mp systems
  exact congrArg RuleSyntax.Equivalence.System.state sameSystem

/-- Actual fresh-occurrence variants produce different worlds and one
answer, while both retain the same rigid origin word and two-firing length. -/
theorem fresh_alias_world_histories :
    ∃ first second : HostState MSig, first ≠ second ∧
      ∃ left : Run (D := D) N dupP q3 2, ∃ right : Run (D := D) N dupP q3 2,
        left.val.last = Counted.heldState N dupP first ∧
        right.val.last = Counted.heldState N dupP second ∧
        Counted.originsOf N left.val = callRet 0 ∧ Counted.originsOf N right.val = callRet 0 ∧
        world (D := D) N dupP (projected (D := D) (P := dupP) N q3 left).val.last ≠ world (D := D) N dupP (projected (D := D) (P := dupP) N q3 right).val.last ∧
        stateAnswer N (projected (D := D) (P := dupP) N q3 left).val.last 4 = stateAnswer N (projected (D := D) (P := dupP) N q3 right).val.last 6 ∧
        (history (D := D) (P := dupP) N q3 left).length = 2 ∧ (history (D := D) (P := dupP) N q3 right).length = 2 := by
  obtain ⟨first,second,different,leftHeld,rightHeld,_,_⟩ := Counted.Example.fresh_variant_histories
  have leftNamed := (Counted.heldFrom_map_iff N (D := D) (P := dupP) q3 dupP_plain trivial q3_unopened
    (ν := [.eqn 0,.ret])).mp leftHeld
  have rightNamed := (Counted.heldFrom_map_iff N (D := D) (P := dupP) q3 dupP_plain trivial q3_unopened
    (ν := [.eqn 0,.ret])).mp rightHeld
  obtain ⟨left,leftOrigins,leftLast,leftEndpoint,leftLength⟩ := named_history_world (D := D) (P := dupP) N q3 leftNamed
  obtain ⟨right,rightOrigins,rightLast,rightEndpoint,rightLength⟩ := named_history_world (D := D) (P := dupP) N q3 rightNamed
  refine ⟨first,second,different,left,right,leftLast,rightLast,leftOrigins,rightOrigins,?_,?_,leftLength,rightLength⟩
  · rw [leftEndpoint,rightEndpoint]
    exact fun same => different (world_injective same)
  · rw [projected_last (D := D) (P := dupP) N q3 left leftLast,projected_last (D := D) (P := dupP) N q3 right rightLast]
    exact (fresh_alias_readout (D := D) (P := dupP) N q3 dupP_plain trivial q3_unopened leftHeld rightHeld).1

/-- Equal schemas and equal answers do not identify equation occurrences.
Both rigid choices have actual terminal world histories. -/
theorem duplicate_equation_world_histories :
    ∃ left : Run (D := D) N dupP q3 2, ∃ right : Run (D := D) N dupP q3 2,
      Counted.originsOf N left.val = callRet 0 ∧ Counted.originsOf N right.val = callRet 1 ∧
        Counted.originsOf N left.val ≠ Counted.originsOf N right.val ∧
        ∃ (first second : HostState MSig) (firstIndex secondIndex : Nat),
          left.val.last = Counted.heldState N dupP first ∧ right.val.last = Counted.heldState N dupP second ∧
            world (D := D) N dupP (projected (D := D) (P := dupP) N q3 left).val.last = world (D := D) N dupP first ∧
            world (D := D) N dupP (projected (D := D) (P := dupP) N q3 right).val.last = world (D := D) N dupP second ∧
            stateAnswer N first firstIndex = stateAnswer N second secondIndex ∧
            (∀ next, ¬ RuleSyntax.Worlds.Fires
              (events (Interface.Frames.contextual MSig) ℕ (RuleSyntax.Contextual.declarations MSig))
                (world (D := D) N dupP first) next) ∧
            (∀ next, ¬ RuleSyntax.Worlds.Fires
              (events (Interface.Frames.contextual MSig) ℕ (RuleSyntax.Contextual.declarations MSig))
                (world (D := D) N dupP second) next) := by
  obtain ⟨_,originsApart,_,answerEqual,leftComplete,rightComplete⟩ := Counted.Example.rigid_origins_apart
  obtain ⟨left,leftOrigins,first,firstIndex,leftLast,_,leftNamed,leftEndpoint,leftTerminal⟩ :=
    complete_word_world (D := D) (P := dupP) N q3 dupP_plain trivial q3_unopened (word := [.eqn 0,.ret]) leftComplete
  obtain ⟨right,rightOrigins,second,secondIndex,rightLast,_,rightNamed,rightEndpoint,rightTerminal⟩ :=
    complete_word_world (D := D) (P := dupP) N q3 dupP_plain trivial q3_unopened (word := [.eqn 1,.ret]) rightComplete
  refine ⟨left,right,leftOrigins,rightOrigins,?_,first,second,firstIndex,secondIndex,
    leftLast,rightLast,leftEndpoint,rightEndpoint,?_,leftTerminal,rightTerminal⟩
  · rw [leftOrigins,rightOrigins]
    exact originsApart
  · exact (named_endpoint_answer (D := D) (P := dupP) N q3 leftNamed).symm.trans
      (answerEqual.trans (named_endpoint_answer (D := D) (P := dupP) N q3 rightNamed))

private theorem choice_unopened :
    ∀ term ∈ Counted.Example.qc.data, ∀ name ∈ support term, name.scopes = [] := by
  intro term member name inside
  simp only [Counted.Example.qc,Comp.data,List.mem_append,List.mem_singleton] at member
  rcases member with rfl | rfl
  · simp [one,sym,support,supportArgs] at inside
  · simp [Counted.Example.two,sym,support,supportArgs] at inside

/-- Two actual schedules of independent returns close a source square.
Their completed bag has actual world witnesses; their ordered observations
of intermediate prefixes remain different. -/
theorem independent_returns_world_bag_ordered_history :
    ∃ first left right final : Config mkeys [] () MTy,
      Runs D emptyP supply (Config.initial (fun _ => 0) Counted.Example.qc) first ∧
        SourceLanguage.Step D emptyP supply first left ∧ SourceLanguage.Step D emptyP supply left final ∧
        SourceLanguage.Step D emptyP supply first right ∧ SourceLanguage.Step D emptyP supply right final ∧
        final.Quiescent (D := D) emptyP supply ∧
        final.answers (D := D) = {{csym "one"}, {csym "two"}} ∧
        [first.answers (D := D),left.answers (D := D),final.answers (D := D)] ≠
          [first.answers (D := D),right.answers (D := D),final.answers (D := D)] ∧
        ∃ M : Multiset (List RuleName),
          (∀ word, M.count word = if Counted.CompleteHeldRun N emptyP Counted.Example.qc
            (word.map (Counted.origin N)) then 1 else 0) ∧
          final.answers (D := D) =
            (M.filter fun word => Counted.FinishedHeldClass N emptyP Counted.Example.qc
              (word.map (Counted.origin N))).map (classAnswer (D := D) N emptyP Counted.Example.qc) ∧
          (∀ word ∈ M, ∃ run : Run (D := D) N emptyP Counted.Example.qc word.length,
            Counted.originsOf N run.val = word.map (Counted.origin N) ∧
              (history (D := D) (P := emptyP) N Counted.Example.qc run).length = word.length ∧
              ∃ (state : HostState MSig) (index : Nat),
                run.val.last = Counted.heldState N emptyP state ∧
                world (D := D) N emptyP (projected (D := D) (P := emptyP) N Counted.Example.qc run).val.last =
                  world (D := D) N emptyP state ∧
                classAnswer (D := D) N emptyP Counted.Example.qc word = stateAnswer N state index) := by
  obtain ⟨first,left,right,final,initialRun,leftStep,leftFinish,rightStep,rightFinish,quiet,answers,_,_,ordered⟩ :=
    Counted.Example.ordered_observer_does_not_descend
  have leftRun := (initialRun.tail leftStep).tail leftFinish
  have rightRun := (initialRun.tail rightStep).tail rightFinish
  obtain ⟨M,counts,worlds,observed,_⟩ := complete_world_bag_determined (D := D) (P := emptyP) N
    (fun _ => 0) Counted.Example.qc emptyP_plain (by constructor <;> trivial) choice_unopened leftRun quiet rightRun quiet
  refine ⟨first,left,right,final,initialRun,leftStep,leftFinish,rightStep,rightFinish,quiet,answers,ordered,M,counts,observed,?_⟩
  intro word member
  obtain ⟨run,origins,state,index,last,_,named,endpoint,_⟩ := worlds word member
  exact ⟨run,origins,history_length (D := D) (P := emptyP) N Counted.Example.qc run,
    state,index,last,endpoint,named_endpoint_answer (D := D) (P := emptyP) N Counted.Example.qc named⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.HostedAnswers.Controls
