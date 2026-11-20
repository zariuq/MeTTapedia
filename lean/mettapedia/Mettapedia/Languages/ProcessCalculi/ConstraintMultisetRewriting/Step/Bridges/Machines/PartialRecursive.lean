import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.MacroCost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive

/-!
# The nineteen-rule compiler: actual runs, budgets and divergence

The compiler is the existing finite positive program. Its local forward
and backward firing theorems discharge the premises of `NativeBudget` on
every state that reads as the current configuration's row. No new source
semantics, rule table or admission oracle is introduced.

The resulting theorems quantify over actual `Interface.Step.Run` objects,
retain their literal endpoints and event counts, and provide exact bounded
answers and resumption. Partial-recursive evaluation and native halting
agree for every code and input, while undefined evaluation corresponds to
an actual infinite admitted event stream.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive

open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open FragmentsOfTheStep.TransitionMaps
open LogicOverTheStep.StepSpan (Succ)
open RuleSyntax.Presentation.Schematic (SState schematicStep)
open RuleSyntax.Machines (ReadsBag rowState_reads)
open RuleSyntax.Machines.PartialRecursive
  (Point program firing_of_reduction reduction_of_firing HaltedWith)

abbrev native := (schematicStep Nat program).toStep

def point : FrameState → Point
  | .inl (code, continuation, input) => .normal code (contOf continuation) input
  | .inr (.inl (continuation, input)) => .config (.ret (contOf continuation) input)
  | .inr (.inr output) => .config (.halt output)

theorem point_pattern (state : FrameState) : (point state).pattern = encFrameState state := by
  rcases state with _ | _ | _ <;> rfl

theorem pattern_injective : Function.Injective Point.pattern := by
  intro left right same
  cases left with
  | normal code continuation input =>
      cases right with
      | normal code' continuation' input' =>
          simp only [Point.pattern, normalTerm, Pattern.apply.injEq, List.cons.injEq,
            and_true, true_and] at same
          rw [encCode_injective same.1, encCont_injective same.2.1, encNats_injective same.2.2]
      | config cfg => exact False.elim (normalTerm_ne_encCfg _ _ _ _ same)
  | config cfg =>
      cases right with
      | normal code continuation input => exact False.elim (normalTerm_ne_encCfg _ _ _ _ same.symm)
      | config cfg' => exact congrArg Point.config (encCfg_injective same)

def Represents (frame : FrameState) (state : SState Nat) : Prop :=
  ReadsBag state {(point frame).row}

/-- The one-step licence is proved from the actual compiler's admitted
firings in both directions, at arbitrary represented intermediate states. -/
theorem comparison : IsBisimulation Authored.frames.Step (Succ native) Represents := by
  constructor
  · rintro frame state after atFrame ⟨notHalted, rfl⟩
    have sourceStep : Reduces (point frame).pattern (point (frameStep frame)).pattern := by
      rw [point_pattern, point_pattern]
      exact (reduces_frameState_iff frame _).mpr ⟨notHalted, rfl⟩
    obtain ⟨firing, admitted, afterPoint, same, atAfter⟩ := firing_of_reduction atFrame sourceStep
    have pointEq : afterPoint = point (frameStep frame) := pattern_injective same.symm
    subst pointEq
    exact ⟨_, ⟨firing, admitted, rfl⟩, atAfter⟩
  · rintro frame state after atFrame ⟨firing, admitted, rfl⟩
    obtain ⟨afterPoint, _, reduced, atAfter⟩ := reduction_of_firing atFrame firing admitted
    rw [point_pattern] at reduced
    obtain ⟨notHalted, same⟩ := (reduces_frameState_iff frame afterPoint.pattern).mp reduced
    have pointEq : afterPoint = point (frameStep frame) :=
      pattern_injective (same.trans (point_pattern _).symm)
    subst pointEq
    exact ⟨frameStep frame, ⟨notHalted, rfl⟩, atAfter⟩

/-- This representation is the relation of the existing composed arrows,
with their intermediate pattern and row bag made explicit. -/
theorem composed_related_iff (frame : FrameState) (state : SState Nat) :
    (Authored.correspondence.comp RuleSyntax.Machines.PartialRecursive.composite).related frame state ↔
      Represents frame state := by
  change (∃ term, encFrameState frame = term ∧
    ∃ bag, (∃ p : Point, term = p.pattern ∧ bag = {p.row}) ∧ ReadsBag state bag) ↔ _
  constructor
  · rintro ⟨_, rfl, _, ⟨p, same, rfl⟩, reads⟩
    have pointEq : point frame = p := pattern_injective ((point_pattern frame).trans same)
    rw [← pointEq] at reads
    exact reads
  · intro reads
    exact ⟨_, rfl, _, ⟨point frame, (point_pattern frame).symm, rfl⟩, reads⟩

theorem observation {frame : FrameState} {state : SState Nat} (atFrame : Represents frame state)
    (output : List Nat) : HaltedWith output state ↔ SourceBudget.observe frame = .answer output := by
  have observes := RuleSyntax.Machines.PartialRecursive.observes output
    ⟨{(point frame).row}, ⟨point frame, rfl, rfl⟩, atFrame⟩
  rw [point_pattern] at observes
  exact observes.symm.trans (Authored.answer_iff frame output)

abbrev start := RuleSyntax.Machines.PartialRecursive.start

theorem initial (code : Code) (input : List Nat) :
    Represents (SourceBudget.start code input) (start code input) := rowState_reads _

theorem run_endpoint {frame : FrameState} {state : SState Nat} (atFrame : Represents frame state)
    (run : native.Run state) : Represents (frameStep^[run.word.length] frame) run.last :=
  NativeBudget.run_endpoint native comparison atFrame run

theorem bounded_answer_iff (budget : Nat) (code : Code) (input output : List Nat) :
    (∃ run : native.Run (start code input), run.word.length ≤ budget ∧ HaltedWith output run.last) ↔
      SourceBudget.run budget (SourceBudget.start code input) = .answer output :=
  NativeBudget.bounded_answer_iff native comparison HaltedWith observation budget (initial code input) output

theorem answer_iff (code : Code) (input output : List Nat) :
    (∃ run : native.Run (start code input), HaltedWith output run.last) ↔ output ∈ code.eval input :=
  NativeBudget.eventual_answer_iff native comparison HaltedWith observation code input output (initial code input)

theorem resume_iff (code : Code) (input : List Nat) (earlier : native.Run (start code input))
    (later : Nat) (output : List Nat) :
    (∃ run : native.Run earlier.last, run.word.length ≤ later ∧ HaltedWith output run.last) ↔
      SourceBudget.run (earlier.word.length + later) (SourceBudget.start code input) = .answer output :=
  NativeBudget.resume_answer_iff native comparison HaltedWith observation (initial code input) earlier later output

theorem normalizing_iff (code : Code) (input : List Nat) :
    Acc (fun after before => Succ native before after) (start code input) ↔ (code.eval input).Dom :=
  NativeBudget.normalizing_iff_defined native comparison code input (initial code input)

theorem divergence_iff_events (code : Code) (input : List Nat) :
    code.eval input = Part.none ↔
      ∃ states : Nat → SState Nat, states 0 = start code input ∧
        Nonempty ((n : Nat) → native.toEffectCore.Event native.eventAdmission (states n) (states (n + 1))) :=
  NativeBudget.divergence_iff_events native comparison code input (initial code input)

/-- The same fixed finite program computes every partial-recursive
function, now stated with actual admitted firing runs. -/
theorem computes_partrec {arity : Nat} {f : List.Vector Nat arity →. Nat} (computable : Nat.Partrec' f) :
    ∃ code : Code, ∀ (input : List.Vector Nat arity) (output : Nat),
      (∃ run : native.Run (start code input.val), HaltedWith [output] run.last) ↔ output ∈ f input := by
  obtain ⟨code, allInputs⟩ := RuleSyntax.Machines.PartialRecursive.computes_partrec computable
  refine ⟨code, fun input output => ?_⟩
  exact (answer_iff code input.val [output]).trans
    ((RuleSyntax.Machines.PartialRecursive.halts_iff code input.val [output]).symm.trans (allInputs input output))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.comparison
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.bounded_answer_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.answer_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.computes_partrec
