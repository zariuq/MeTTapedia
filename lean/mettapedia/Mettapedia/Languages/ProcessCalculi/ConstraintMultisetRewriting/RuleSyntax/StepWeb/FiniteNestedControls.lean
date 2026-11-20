import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteNested
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteBridge

/-!
# The finite program along runs with nested binding: an example and a control

The step is the one-match step of the three-rule `program` at the one frame of structural substitution
on patterns, with the five choices stated in `FiniteComm`: a bag store, one match, guards asked after the
firing's own tells (the rules have none), a fixed set of rules beside the store, one store of knowledge.

## An example with nested binding

`for((0) <- @0)0 | for(y <- @0)for(z <- y)z | for((0) <- @((0)))0`. The receiver's continuation is an
input on the name it receives. The process is nested (`nested_example`) and not hosted
(`nested_not_hosted`), so `FiniteHosting` does not apply to it. The source takes two COMMs: the first gives
the receiver `(0)` and leaves `for(z <- @((0)))z` beside the third part (`first_step`); the second joins
these two and leaves `@((0))` (`second_step`). Both are steps of the tree's corrected semantics modulo the
bag laws (`nested_corrected`). By the fifth clause of `manuscript_calculus_nested`, the step runs both,
from the initial state, through two communications (`nested_run`); `runs_complete_nested` matches the
two-step source run as a whole (`nested_run_matched`).

## Control: the variable convention across parts

`for((0) <- @0)0 | for(y <- @0)y | for(y <- @((0)))y`: the manuscript's example beside a third part that
binds the receiver's name `y` again. Each part is nested; the process is not, since two parts' inputs bind
`y` (`shared_parts`). The source's COMM of the sender and the receiver leaves the third part as it is
(`shared_step`). At the initial state no housekeeping firing is admitted (`shared_no_housekeeping`), and
after every communication there every solution of the knowledge gives `y` the value `(0)`
(`shared_comm_pins`). By `pinned_represents_nothing`, no run of housekeeping firings and one communication
from the initial state reaches a state that represents the source's reduct (`shared_binder_unmatched`): the
fifth clause fails there. With the third part's bound name renamed to `w`, the process is nested and the
same COMM is matched (`renamed_matched`).

## Control: binary parallel composition

The manuscript's example and `0` written as one ternary parallel bag is one part, and that part is no
input: the bag presentation takes no step from it, and at its initial state the step has no transition,
while the tree's corrected semantics modulo the bag laws flattens the bag and takes the manuscript's COMM
(`ternary_unhosted`).

## Soundness along every run, at the manuscript's example

From `for((0) <- @0)0 | for(y <- @0)y` the source reaches only the example and the parts of its reduct
`@((0))`, whichever input is taken first and whichever ground principal unifier is used
(`example_reachable`); both bags are ground-unifiable (`example_grounded`), so the hypothesis of
`runs_sound_nested` holds there. Hence every run of the step from the example's initial state ends at a
state that represents the example's parts or the parts of its reduct (`example_runs_sound`).

## What is not shown

A control for the convention within a part (`FramesApart`); it is used where a nested parallel
composition is split (`Nested.parts_of_par`), so that the two halves bind no common variable. Renaming a
process into the convention is not shown.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram.NestedControls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot demoChan)
open MeTTaOperationsComm (psubst pvars patternAction PSubst GroundPrincipal firstOrder psubst_of_pvars_nil
  psubst_pFor applyDot_eq)
open MeTTaCalculus.Corrected (Apart BagCommStep conventional BagEq bagEq_iff components)
open Comm (Tm X E)
open Comm.Controls (zeroTerm y z w sender receiver source unifier reduct unifier_groundPrincipal)
open FiniteProgram.Controls (unifier_values example_apart value_mem parts_source parts_reduct
  example_groundUnifiable)
open LogicOverTheStep.StepSpan (Succ)

/-! ## A variable against a term without variables -/

theorem lookup_single (v : String) (g : Pattern) : Bindings.lookup [(v, g)] v = some g := by
  simp [Bindings.lookup]

/-- **A variable and a term without variables**: binding the variable to the term is a ground principal
unifier. -/
theorem var_groundPrincipal (v : String) {g : Pattern} (ground : pvars g = []) :
    GroundPrincipal (.fvar v) g [(v, g)] := by
  have vars : pvars (.fvar v) ++ pvars g = [v] := by simp [ground, pvars]
  refine ⟨fun e member => ?_, fun x member => ?_, ?_, fun σ equation x member value found => ?_⟩
  · rw [vars, List.mem_singleton.mp member]
    exact List.mem_singleton_self v
  · rw [vars, List.mem_singleton] at member
    subst member
    exact ⟨g, lookup_single _ g, ground⟩
  · show (Bindings.lookup [(v, g)] v).getD (.fvar v) = _
    rw [lookup_single, Option.getD_some, psubst_of_pvars_nil _ g ground]
  · rw [vars, List.mem_singleton] at member
    subst member
    rw [lookup_single, Option.some.injEq] at found
    subst found
    exact equation.trans (psubst_of_pvars_nil σ _ ground)

/-- Binding a variable to a first-order term has first-order values. -/
theorem single_values (v : String) {g : Pattern} (fo : firstOrder g = true) :
    ∀ x value, Bindings.lookup [(v, g)] x = some value → firstOrder value = true := by
  intro x value found
  obtain ⟨k, member⟩ := value_mem found
  rw [List.mem_singleton, Prod.mk.injEq] at member
  rw [member.2]
  exact fo

/-! ## An example with nested binding -/

/-- `for(z <- y)z`: an input on the name `y`. -/
def innerInput : Pattern := pFor z y z

/-- `for(y <- @0)for(z <- y)z`: a receiver whose continuation is an input on the name it receives. -/
def nestedReceiver : Pattern := pFor y demoChan innerInput

/-- `for((0) <- @((0)))0`. -/
def relay : Pattern := pFor zeroTerm (nQuote zeroTerm) pZero

/-- `for((0) <- @0)0 | (for(y <- @0)for(z <- y)z | for((0) <- @((0)))0)`. -/
def nestedSource : Pattern := par sender (par nestedReceiver relay)

/-- `for(z <- @((0)))z`: the receiver's continuation after it receives `(0)`. -/
def middleInput : Pattern := pFor z (nQuote zeroTerm) z

/-- `for(z <- @((0)))z | for((0) <- @((0)))0`. -/
def middle : Pattern := par middleInput relay

theorem parts_nestedSource : parts nestedSource = [sender, nestedReceiver, relay] := by decide +kernel

theorem parts_middle : parts middle = [middleInput, relay] := by decide +kernel

theorem sender_nested : Nested sender :=
  ⟨by decide +kernel, scoped_of_ground sender [] (by decide +kernel), by decide +kernel⟩

theorem relay_nested : Nested relay :=
  ⟨by decide +kernel, scoped_of_ground relay [] (by decide +kernel), by decide +kernel⟩

theorem nestedReceiver_nested : Nested nestedReceiver :=
  ⟨by decide +kernel, (scoped_pFor [] y demoChan innerInput).mpr ⟨by decide +kernel, by decide +kernel,
    scoped_of_ground demoChan [] (by decide +kernel), (scoped_pFor (pvars y ++ []) z y z).mpr
      ⟨by decide +kernel, by decide +kernel, show "y" ∈ pvars y ++ [] by decide +kernel,
        show "z" ∈ pvars z ++ (pvars y ++ []) by decide +kernel⟩⟩, by decide +kernel⟩

/-- **The example is a nested process.** -/
theorem nested_example : NestedProcess nestedSource := by
  refine ⟨fun c member => ?_, ?_⟩
  · rw [parts_nestedSource] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact sender_nested
    · exact nestedReceiver_nested
    · exact relay_nested
  · rw [parts_nestedSource]
    decide +kernel

/-- **The example is not a hosted process**: the receiver's continuation binds `z`, which its own pattern
does not have. -/
theorem nested_not_hosted : ¬ HostedProcess nestedSource := by
  intro hostedP
  obtain ⟨-, plain | ⟨t, x, A, same, -, own, -⟩⟩ :=
    hostedP.hosted nestedReceiver (by rw [parts_nestedSource]; simp)
  · exact absurd plain (by decide +kernel)
  · obtain ⟨rfl, -, rfl⟩ := pFor_inj (show pFor y demoChan innerInput = pFor t x A from same)
    exact absurd (own "z" (by decide +kernel)) (by decide +kernel)

theorem first_apart : Apart zeroTerm pZero y innerInput :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem second_apart : Apart z z zeroTerm pZero :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The first COMM**: the sender gives the receiver `(0)`, which leaves `for(z <- @((0)))z` beside the
third part. -/
theorem first_step : BagComm (parts nestedSource : Multiset Pattern) (parts middle : Multiset Pattern) := by
  have step := BagComm.comm zeroTerm y demoChan pZero innerInput unifier ({relay} : Multiset Pattern)
    unifier_groundPrincipal first_apart unifier_values
  have source' : (parts nestedSource : Multiset Pattern) =
      pFor zeroTerm demoChan pZero ::ₘ pFor y demoChan innerInput ::ₘ {relay} := by
    rw [parts_nestedSource]
    rfl
  have target : (parts (applyDot unifier pZero) : Multiset Pattern) +
      (parts (applyDot unifier innerInput) : Multiset Pattern) + {relay} =
        (parts middle : Multiset Pattern) := by
    rw [show applyDot unifier pZero = pZero by decide +kernel,
      show applyDot unifier innerInput = middleInput by decide +kernel, parts_pZero,
      show parts middleInput = [middleInput] by decide +kernel, parts_middle]
    rfl
  rw [source', ← target]
  exact step

/-- **The second COMM**: `for(z <- @((0)))z` and the third part leave `@((0))`. -/
theorem second_step : BagComm (parts middle : Multiset Pattern) {nQuote zeroTerm} := by
  have step := BagComm.comm z zeroTerm (nQuote zeroTerm) z pZero [("z", zeroTerm)] 0
    (var_groundPrincipal "z" (by decide +kernel)) second_apart (single_values "z" (by decide +kernel))
  have source' : (parts middle : Multiset Pattern) =
      pFor z (nQuote zeroTerm) z ::ₘ pFor zeroTerm (nQuote zeroTerm) pZero ::ₘ 0 := by
    rw [parts_middle]
    rfl
  have target : (parts (applyDot [("z", zeroTerm)] z) : Multiset Pattern) +
      (parts (applyDot [("z", zeroTerm)] pZero) : Multiset Pattern) + 0 = {nQuote zeroTerm} := by
    rw [show applyDot [("z", zeroTerm)] z = nQuote zeroTerm by decide +kernel,
      show applyDot [("z", zeroTerm)] pZero = pZero by decide +kernel, parts_pZero,
      show parts (nQuote zeroTerm) = [nQuote zeroTerm] by decide +kernel]
    rfl
  rw [source', ← target]
  exact step

/-- **Both COMMs of the example are steps of the tree's corrected semantics modulo the bag laws.** -/
theorem nested_corrected :
    (∃ P' : Pattern, BagCommStep conventional nestedSource P' ∧
      (parts P' : Multiset Pattern) = (parts middle : Multiset Pattern)) ∧
    ∃ P' : Pattern, BagCommStep conventional middle P' ∧ (parts P' : Multiset Pattern) = {nQuote zeroTerm} :=
  ⟨bagComm_bagCommStep (by decide +kernel) first_step, bagComm_bagCommStep (by decide +kernel) second_step⟩

/-- **The example runs through the correspondence**: from the initial state, housekeeping firings and one
communication reach a state that represents the parts of `for(z <- @((0)))z | for((0) <- @((0)))0`; from
there, housekeeping firings and one communication reach a state that represents `@((0))`. -/
theorem nested_run : ∃ s₁ s₂ s₃ s₄ : State Tm ℕ,
    Relation.ReflTransGen Administers (initial (parts nestedSource)) s₁ ∧ Communicates s₁ s₂ ∧
      RepresentsNested s₂ (parts middle : Multiset Pattern) ∧
      Relation.ReflTransGen Administers s₂ s₃ ∧ Communicates s₃ s₄ ∧
      RepresentsNested s₄ {nQuote zeroTerm} := by
  obtain ⟨s₁, s₂, run₁, fires₁, comp₂, nestedBy₂⟩ :=
    communication_complete_nested (initial_nested nestedSource nested_example) first_step
  obtain ⟨s₃, s₄, run₂, fires₂, represented₄⟩ := communication_complete_nested nestedBy₂ second_step
  exact ⟨s₁, s₂, s₃, s₄, run₁, fires₁, ⟨comp₂, nestedBy₂⟩, run₂, fires₂, represented₄⟩

/-- **The example's source run, matched as a whole** (`runs_complete_nested`): a run of the step from the
initial state reaches a state that represents `@((0))`. -/
theorem nested_run_matched : ∃ s', Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep)
    (initial (parts nestedSource)) s' ∧ RepresentsNested s' {nQuote zeroTerm} :=
  runs_complete_nested ⟨_, initial_nested nestedSource nested_example⟩
    ((Relation.ReflTransGen.single first_step).tail second_step)

/-! ## Control: the variable convention across parts -/

/-- `for(y <- @((0)))y`: an input that binds the receiver's name `y` again. -/
def echo : Pattern := pFor y (nQuote zeroTerm) y

/-- The manuscript's example beside it: `for((0) <- @0)0 | for(y <- @0)y | for(y <- @((0)))y`. -/
def sharedSource : Pattern := par source echo

/-- The source's reduct: the manuscript's reduct beside the untouched third part. -/
def sharedReduct : Pattern := par reduct echo

theorem parts_sharedSource : parts sharedSource = [sender, receiver, echo] := by decide +kernel

theorem parts_sharedReduct : parts sharedReduct = [nQuote zeroTerm, echo] := by decide +kernel

theorem receiver_nested : Nested receiver :=
  ⟨by decide +kernel, (scoped_pFor [] y demoChan y).mpr ⟨by decide +kernel, by decide +kernel,
    scoped_of_ground demoChan [] (by decide +kernel), show "y" ∈ pvars y ++ [] by decide +kernel⟩,
    by decide +kernel⟩

theorem echo_nested : Nested echo :=
  ⟨by decide +kernel, (scoped_pFor [] y (nQuote zeroTerm) y).mpr ⟨by decide +kernel, by decide +kernel,
    scoped_of_ground (nQuote zeroTerm) [] (by decide +kernel), show "y" ∈ pvars y ++ [] by decide +kernel⟩,
    by decide +kernel⟩

/-- **Each part is nested; the process is not**: the receiver and the third part both bind `y`. -/
theorem shared_parts : (∀ c ∈ parts sharedSource, Nested c) ∧ ¬ NestedProcess sharedSource := by
  refine ⟨fun c member => ?_, fun nestedP => ?_⟩
  · rw [parts_sharedSource] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact sender_nested
    · exact receiver_nested
    · exact echo_nested
  · have disjoint := nestedP.disjoint
    rw [parts_sharedSource] at disjoint
    exact absurd disjoint (by decide +kernel)

/-- **The manuscript's COMM beside a third part**: the sender and the receiver are replaced by `@((0))`, and
the third part stays. -/
theorem beside_step {e : Pattern} (single : parts e = [e]) :
    BagComm (parts (par source e) : Multiset Pattern) (parts (par reduct e) : Multiset Pattern) := by
  have step := BagComm.comm zeroTerm y demoChan pZero y unifier ({e} : Multiset Pattern)
    unifier_groundPrincipal example_apart unifier_values
  have source' : (parts (par source e) : Multiset Pattern) =
      pFor zeroTerm demoChan pZero ::ₘ pFor y demoChan y ::ₘ {e} := by
    rw [parts_par, parts_source, single]
    rfl
  have target : (parts (applyDot unifier pZero) : Multiset Pattern) +
      (parts (applyDot unifier y) : Multiset Pattern) + {e} = (parts (par reduct e) : Multiset Pattern) := by
    rw [show applyDot unifier pZero = pZero by decide +kernel,
      show applyDot unifier y = nQuote zeroTerm by decide +kernel, parts_pZero,
      show parts (nQuote zeroTerm) = [nQuote zeroTerm] by decide +kernel, parts_par, parts_reduct, single]
    rfl
  rw [source', ← target]
  exact step

/-- **The source's COMM leaves the third part as it is.** -/
theorem shared_step :
    BagComm (parts sharedSource : Multiset Pattern) (parts sharedReduct : Multiset Pattern) :=
  beside_step (e := echo) (by decide +kernel)

/-- The pattern of each represented row of the initial state. -/
def sharedPattern (o : ℕ) : Pattern := if o = 0 then zeroTerm else y

/-- The channel of each represented row of the initial state. -/
def sharedChannel (o : ℕ) : Pattern := if o = 2 then nQuote zeroTerm else demoChan

/-- The continuation of each represented row of the initial state. -/
def sharedBody (o : ℕ) : Pattern := if o = 0 then pZero else nQuote y

theorem shared_label {o : ℕ} (small : o < 3) :
    (initial (parts sharedSource)).label o = pFor (sharedPattern o) (sharedChannel o) (sharedBody o) := by
  interval_cases o <;> decide +kernel

theorem shared_present {o : ℕ} (present : o ∈ (initial (parts sharedSource)).present) : o < 3 := by
  have inRange : o ∈ Finset.range (parts sharedSource).length := present
  rw [parts_sharedSource] at inRange
  simpa using inRange

/-- **At the initial state no housekeeping firing is admitted**: every row is an input. -/
theorem shared_no_housekeeping (s' : State Tm ℕ) : ¬ Administers (initial (parts sharedSource)) s' := by
  rintro ⟨f, kind, admitted, -⟩
  rcases kind with isHeat | isClear
  · obtain ⟨o, m₁, m₂, same, -, present, -, -⟩ := heat_normal f isHeat admitted
    rw [same] at admitted
    obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
    have solvedInfo : patternAction.Models σ₀
        ((heatAt f.opening o m₁ m₂).information X (initial (parts sharedSource))) := solved₀
    rw [heatAt_info] at solvedInfo
    have take : psubst σ₀ (psubst f.opening (par leftPart rightPart)) =
        psubst σ₀ ((initial (parts sharedSource)).label o) :=
      solvedInfo (psubst f.opening (par leftPart rightPart), (initial (parts sharedSource)).label o)
        (by simp)
    rw [shared_label (shared_present present)] at take
    simp only [MeTTaOperationsComm.psubst_par, psubst_pFor] at take
    exact not_par_pFor _ _ _ ⟨_, _, take.symm⟩
  · obtain ⟨o, same, present⟩ := clear_normal f isClear admitted
    rw [same] at admitted
    obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
    have solvedInfo : patternAction.Models σ₀
        ((clearAt f.opening o).information X (initial (parts sharedSource))) := solved₀
    rw [clearAt_info] at solvedInfo
    have take : psubst σ₀ (psubst f.opening pZero) = psubst σ₀ ((initial (parts sharedSource)).label o) :=
      solvedInfo (psubst f.opening pZero, (initial (parts sharedSource)).label o) (by simp)
    rw [shared_label (shared_present present)] at take
    simp only [MeTTaOperationsComm.psubst_pZero, psubst_pFor] at take
    exact pFor_ne_pZero _ _ _ take.symm

/-- **After every communication at the initial state, every solution of the knowledge gives `y` the value
`(0)`.** The only two rows on one channel hold the sender and the receiver. -/
theorem shared_comm_pins {s' : State Tm ℕ} (fires : Communicates (initial (parts sharedSource)) s') :
    ∀ σ : PSubst, patternAction.Models σ s'.knowledge → (σ "y").getD (.fvar "y") = zeroTerm := by
  intro σ solved
  obtain ⟨f, isComm, admitted, rfl⟩ := fires
  obtain ⟨o₁, o₂, m₁, m₂, same, distinct, madeDistinct, present₁, present₂, -, -⟩ :=
    comm_normal f isComm admitted
  rw [same] at solved
  have small₁ := shared_present present₁
  have small₂ := shared_present present₂
  obtain ⟨-, unify, channels, -, -⟩ := comm_reads_inputs (initial (parts sharedSource)).label
    (sharedPattern o₁) (sharedPattern o₂) (sharedChannel o₁) (sharedChannel o₂) (sharedBody o₁)
    (sharedBody o₂) ⟨(initial (parts sharedSource)).knowledge, (initial (parts sharedSource)).present⟩
    o₁ o₂ m₁ m₂ (fun τ _ => by rw [shared_label small₁]) (fun τ _ => by rw [shared_label small₂])
    madeDistinct f.opening solved
  have groundChannel : ∀ o, psubst σ (sharedChannel o) = sharedChannel o := fun o =>
    psubst_of_pvars_nil σ _ (by unfold sharedChannel; split_ifs <;> decide +kernel)
  rw [groundChannel, groundChannel] at channels
  have groundZero : psubst σ zeroTerm = zeroTerm := psubst_of_pvars_nil σ zeroTerm (by decide +kernel)
  interval_cases o₁ <;> interval_cases o₂
  all_goals first
    | exact absurd rfl distinct
    | exact absurd channels (by decide +kernel)
    | exact unify.symm.trans groundZero
    | exact unify.trans groundZero

/-- **Control: the variable convention across parts.** Each part of `for((0) <- @0)0 | for(y <- @0)y |
for(y <- @((0)))y` is nested, but the process is not, since two parts bind `y`. The source's COMM of the
first two parts leaves the third as it is, and no run of housekeeping firings and one communication from
the initial state reaches a state that represents the source's reduct: the fifth clause of
`manuscript_calculus_nested` fails here. -/
theorem shared_binder_unmatched :
    (∀ c ∈ parts sharedSource, Nested c) ∧ ¬ NestedProcess sharedSource ∧
      BagComm (parts sharedSource : Multiset Pattern) (parts sharedReduct : Multiset Pattern) ∧
      ¬ ∃ s₁ s₂ : State Tm ℕ, Relation.ReflTransGen Administers (initial (parts sharedSource)) s₁ ∧
        Communicates s₁ s₂ ∧ RepresentsNested s₂ (parts sharedReduct : Multiset Pattern) := by
  refine ⟨shared_parts.1, shared_parts.2, shared_step, ?_⟩
  rintro ⟨s₁, s₂, run, fires, represented⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨c, first, -⟩
  · exact pinned_represents_nothing (shared_comm_pins fires) (c := echo)
      (by rw [parts_sharedReduct]; simp) (by decide +kernel) represented
  · exact shared_no_housekeeping c first

/-- `for(w <- @((0)))w`: the third part with its bound name renamed. -/
def renamedEcho : Pattern := pFor w (nQuote zeroTerm) w

theorem renamedEcho_nested : Nested renamedEcho :=
  ⟨by decide +kernel, (scoped_pFor [] w (nQuote zeroTerm) w).mpr ⟨by decide +kernel, by decide +kernel,
    scoped_of_ground (nQuote zeroTerm) [] (by decide +kernel), show "w" ∈ pvars w ++ [] by decide +kernel⟩,
    by decide +kernel⟩

/-- **With the third part's bound name renamed, the process is nested and the same COMM is matched**:
housekeeping firings and one communication from the initial state reach a state that represents the
source's reduct. -/
theorem renamed_matched : NestedProcess (par source renamedEcho) ∧
    ∃ s₁ s₂ : State Tm ℕ, Relation.ReflTransGen Administers (initial (parts (par source renamedEcho))) s₁ ∧
      Communicates s₁ s₂ ∧ RepresentsNested s₂ (parts (par reduct renamedEcho) : Multiset Pattern) := by
  have partsSame : parts (par source renamedEcho) = [sender, receiver, renamedEcho] := by decide +kernel
  have nestedP : NestedProcess (par source renamedEcho) := by
    refine ⟨fun c member => ?_, ?_⟩
    · rw [partsSame] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact sender_nested
      · exact receiver_nested
      · exact renamedEcho_nested
    · rw [partsSame]
      decide +kernel
  exact ⟨nestedP, communication_complete_nested (initial_nested _ nestedP)
    (beside_step (e := renamedEcho) (by decide +kernel))⟩

/-! ## Control: binary parallel composition -/

/-- The manuscript's example and `0` as one ternary parallel bag. -/
def ternary : Pattern := MeTTaCalculus.pPar [sender, receiver, pZero]

/-- **Control: binary parallel composition.** The ternary bag is one part, and that part is no input: the
bag presentation takes no step from it, and at its initial state the step has no transition. The tree's
corrected semantics modulo the bag laws flattens the bag and takes the manuscript's COMM. -/
theorem ternary_unhosted :
    parts ternary = [ternary] ∧ (∀ M, ¬ BagComm (parts ternary : Multiset Pattern) M) ∧
      (∀ s', ¬ Succ (RuleSyntax.step X ℕ E program).toStep (initial (parts ternary)) s') ∧
      ∃ P', BagCommStep conventional ternary P' := by
  have single : parts ternary = [ternary] := by decide +kernel
  have closed : Scoped [] ternary := by
    show ScopedList [] [sender, receiver, pZero]
    rw [scopedList_iff]
    intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact sender_nested.2.1
    · exact receiver_nested.2.1
    · exact scoped_of_ground pZero [] (by decide +kernel)
  have label : (initial (parts ternary)).label 0 = predot ternary := by decide +kernel
  have onlyZero : ∀ o ∈ (initial (parts ternary)).present, o = 0 := by
    intro o member
    have inRange : o ∈ Finset.range (parts ternary).length := member
    rw [single] at inRange
    simpa using inRange
  refine ⟨single, fun M step => ?_, fun s' fires => ?_, ?_⟩
  · generalize start : (parts ternary : Multiset Pattern) = N at step
    obtain ⟨t, u, x, A, B, bs, rest, -, -, -⟩ := step
    rw [single] at start
    have counted := congrArg Multiset.card start
    rw [Multiset.coe_card, List.length_singleton, Multiset.card_cons, Multiset.card_cons] at counted
    omega
  · rcases (succ_iff _ _).mp fires with ⟨f, isComm, admitted, -⟩ | ⟨f, kind, admitted, -⟩
    · obtain ⟨o₁, o₂, -, -, -, distinct, -, present₁, present₂, -, -⟩ := comm_normal f isComm admitted
      exact distinct ((onlyZero o₁ present₁).trans (onlyZero o₂ present₂).symm)
    · rcases kind with isHeat | isClear
      · obtain ⟨o, m₁, m₂, same, -, present, -, -⟩ := heat_normal f isHeat admitted
        rw [same] at admitted
        obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
        have solvedInfo : patternAction.Models σ₀
            ((heatAt f.opening o m₁ m₂).information X (initial (parts ternary))) := solved₀
        rw [heatAt_info] at solvedInfo
        have take : psubst σ₀ (psubst f.opening (par leftPart rightPart)) =
            psubst σ₀ ((initial (parts ternary)).label o) :=
          solvedInfo (psubst f.opening (par leftPart rightPart), (initial (parts ternary)).label o) (by simp)
        rw [onlyZero o present, label] at take
        simp only [MeTTaOperationsComm.psubst_par] at take
        obtain ⟨a, b, isPar⟩ := closed_par_of_instance closed take.symm
        simp [ternary, par, MeTTaCalculus.pPar] at isPar
      · obtain ⟨o, same, present⟩ := clear_normal f isClear admitted
        rw [same] at admitted
        obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
        have solvedInfo : patternAction.Models σ₀
            ((clearAt f.opening o).information X (initial (parts ternary))) := solved₀
        rw [clearAt_info] at solvedInfo
        have take : psubst σ₀ (psubst f.opening pZero) = psubst σ₀ ((initial (parts ternary)).label o) :=
          solvedInfo (psubst f.opening pZero, (initial (parts ternary)).label o) (by simp)
        rw [onlyZero o present, label] at take
        simp only [MeTTaOperationsComm.psubst_pZero] at take
        exact absurd (closed_zero_of_instance closed take.symm) (by decide +kernel)
  · have similar : BagEq ternary (par sender receiver) := by
      rw [bagEq_iff]
      apply List.Perm.map
      exact List.Perm.of_eq (by decide +kernel)
    exact ⟨_, .congruence similar (.comm zeroTerm y demoChan pZero y unifier
      (Comm.principal_of_groundPrincipal unifier_groundPrincipal) example_apart) (BagEq.refl _)⟩

/-! ## Soundness along every run, at the manuscript's example -/

/-- The manuscript's example is a nested process, since it is hosted. -/
theorem example_nested : NestedProcess source :=
  nestedProcess_of_hosted FiniteProgram.Controls.example_hostedProcess

/-- A ground principal unifier of the example's two patterns binds `y` to `(0)`. -/
theorem lookup_y {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs)
    (mem : "y" ∈ pvars t ++ pvars u) (unifies : psubst unifier.lookup t = psubst unifier.lookup u) :
    Bindings.lookup bs "y" = some zeroTerm := by
  obtain ⟨v, found, -⟩ := gp.covers "y" mem
  rw [found, ← gp.principal unifier.lookup unifies "y" mem v found]
  decide +kernel

theorem dot_pZero (bs : Bindings) : applyDot bs pZero = pZero :=
  (applyDot_eq bs pZero (by decide +kernel)).trans (MeTTaOperationsComm.psubst_pZero _)

theorem dot_y {bs : Bindings} (lookY : Bindings.lookup bs "y" = some zeroTerm) :
    applyDot bs y = nQuote zeroTerm := by
  rw [applyDot_eq bs y (by decide +kernel)]
  show (Option.map nQuote (Bindings.lookup bs "y")).getD (.fvar "y") = _
  simp [lookY]

/-- **Every source step from the manuscript's example reaches the parts of its reduct**, whichever input
is taken first and whichever ground principal unifier is used. -/
theorem example_step_target {M : Multiset Pattern} (step : BagComm (parts source : Multiset Pattern) M) :
    M = parts reduct := by
  generalize start : (parts source : Multiset Pattern) = N at step
  obtain ⟨t, u, x, A, B, bs, rest, gp, -, -⟩ := step
  rw [parts_source] at start
  have inFirst : pFor t x A ∈ (↑[sender, receiver] : Multiset Pattern) := by
    rw [start]
    exact Multiset.mem_cons_self _ _
  have erased : (↑[sender, receiver] : Multiset Pattern).erase (pFor t x A) = pFor u x B ::ₘ rest := by
    rw [start, Multiset.erase_cons_head]
  have senderNe : sender ≠ receiver := by decide +kernel
  have quoteParts : parts (nQuote zeroTerm) = [nQuote zeroTerm] := by decide +kernel
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at inFirst
  rcases inFirst with isSender | isReceiver
  · rw [isSender, Multiset.coe_erase, List.erase_cons_head, Multiset.coe_singleton,
      Multiset.singleton_eq_cons_iff] at erased
    obtain ⟨second, rfl⟩ := erased
    obtain ⟨rfl, rfl, rfl⟩ := pFor_inj (show pFor t x A = pFor zeroTerm demoChan pZero from isSender)
    obtain ⟨rfl, -, rfl⟩ := pFor_inj (show pFor y demoChan y = pFor u demoChan B from second)
    rw [dot_pZero, dot_y (lookup_y gp (by decide +kernel) (by decide +kernel)), parts_pZero, quoteParts,
      parts_reduct]
    rfl
  · rw [isReceiver, Multiset.coe_erase, List.erase_cons_tail (by simpa using senderNe), List.erase_cons_head,
      Multiset.coe_singleton, Multiset.singleton_eq_cons_iff] at erased
    obtain ⟨second, rfl⟩ := erased
    obtain ⟨rfl, rfl, rfl⟩ := pFor_inj (show pFor t x A = pFor y demoChan y from isReceiver)
    obtain ⟨rfl, -, rfl⟩ := pFor_inj (show pFor zeroTerm demoChan pZero = pFor u demoChan B from second)
    rw [dot_y (lookup_y gp (by decide +kernel) (by decide +kernel)), dot_pZero, parts_pZero, quoteParts,
      parts_reduct]
    rfl

/-- The parts of the manuscript's reduct hold no input: the source takes no step from them. -/
theorem reduct_final {M : Multiset Pattern} : ¬ BagComm (parts reduct : Multiset Pattern) M := by
  intro step
  generalize start : (parts reduct : Multiset Pattern) = N at step
  obtain ⟨t, u, x, A, B, bs, rest, -, -, -⟩ := step
  have member : pFor t x A ∈ (parts reduct : Multiset Pattern) := by
    rw [start]
    exact Multiset.mem_cons_self _ _
  rw [parts_reduct] at member
  simp [pFor, nQuote] at member

/-- **From the manuscript's example the source reaches only the example and the parts of its reduct.** -/
theorem example_reachable {M : Multiset Pattern}
    (run : Relation.ReflTransGen BagComm (parts source : Multiset Pattern) M) :
    M = parts source ∨ M = parts reduct := by
  induction run with
  | refl => exact .inl rfl
  | tail _ step earlier =>
      rcases earlier with rfl | rfl
      · exact .inr (example_step_target step)
      · exact absurd step reduct_final

/-- **The example meets the hypothesis of soundness along runs**: every bag the source reaches from it is
ground-unifiable. -/
theorem example_grounded :
    ∀ M, Relation.ReflTransGen BagComm (parts source : Multiset Pattern) M → GroundUnifiable M := by
  intro M run
  rcases example_reachable run with rfl | rfl
  · exact example_groundUnifiable
  · intro t x A u B member
    rw [parts_reduct] at member
    simp [pFor, nQuote] at member

/-- **Every run of the step from the manuscript's example is a run of the source**: it ends at a state that
represents the example's parts or the parts of its reduct. -/
theorem example_runs_sound {s' : State Tm ℕ}
    (run : Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep) (initial (parts source)) s') :
    RepresentsNested s' (parts source) ∨ RepresentsNested s' (parts reduct) := by
  obtain ⟨M, sourceRun, represented⟩ :=
    runs_sound_nested ⟨_, initial_nested source example_nested⟩ example_grounded run
  rcases example_reachable sourceRun with rfl | rfl
  · exact .inl represented
  · exact .inr represented

#print axioms var_groundPrincipal
#print axioms single_values
#print axioms nested_example
#print axioms nested_not_hosted
#print axioms first_step
#print axioms second_step
#print axioms nested_corrected
#print axioms nested_run
#print axioms nested_run_matched
#print axioms shared_parts
#print axioms beside_step
#print axioms shared_step
#print axioms shared_label
#print axioms shared_no_housekeeping
#print axioms shared_comm_pins
#print axioms shared_binder_unmatched
#print axioms renamed_matched
#print axioms ternary_unhosted
#print axioms example_nested
#print axioms example_step_target
#print axioms example_reachable
#print axioms example_grounded
#print axioms example_runs_sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram.NestedControls
