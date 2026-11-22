import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Strict
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Congruence

/-!
# The control for the restricted composition: knowledge without a solution switches everything off

`stepParallel ω` lets every pair of systems compose, and the tensor carries both knowledges.
Admission asks the whole information, the knowledge included, to be solvable
(`RuleSyntax.Firing.Admits`), and the may-barb asks for a model of the knowledge
(`RuleSyntax.Equivalence.not_mayBarb_of_unsolvable`). So a neighbour with no rule and no row, whose
knowledge has no solution, switches every system off.

* `junk`: no row, knowledge `0 = @0!(0)`; it has no solution (`junk_unsolvable`) and represents no
  process (`junk_not_represented`). A system whose knowledge has no solution never succeeds
  (`system_inert`).
* `junk_switches`: with every pair composable, the step is switchable with the four-rule program on
  both sides: the system with the one row `ω!(0)` succeeds, and beside the system of the four-rule
  program with the junk state it never does. No rule of that program has a check, a collect pattern or
  a tell (`program_positive`).
* `image_switched_off`: the translation of `@0!(0)` succeeds, and beside the junk system it never
  does.
* `fourRuleParallel ω`: the states of the four-rule program alone, composed by the tensor with every
  pair composable, success the output barb on `ω`, equality as the static equivalence. The reflective
  calculus embeds into it uniformly (`encodeUniform`), and it does not embed back
  (`strict_separation_fourRule`): with every pair composable, the same criterion separates the
  reflective calculus from the states of its own four-rule program.
* With composition restricted to solvable joint knowledge (`stepParallelSolvable`), the junk pair is
  not composable (`junk_pair_not_composable`), while the absence pair is (`solvable_switchable`).
* Weak barbed bisimilarity with a state that represents nothing: `junk` and the empty state are
  bisimilar (neither moves nor shows a barb), and beside `ω!(0)` they are not (`junk_not_congruence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus UniformTranslation isEmpty_uniformTranslation)
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding GroundSolves read outputT zeroT
  knowledge groundFrame)

/-! ## A state whose knowledge has no solution -/

/-- **The junk state**: no row; the knowledge equates `0` with `@0!(0)`. -/
def junk : ByInstantiation.State :=
  ⟨groundFrame, [(ByInstantiation.obs zeroT, ByInstantiation.obs ByInstantiation.outputZero)], ∅,
    fun _ => ByInstantiation.obs zeroT⟩

/-- `0` and `@0!(0)` are not similar. -/
theorem zero_not_similar_output : ¬ Similar (zeroT : G [] .pr) ByInstantiation.outputZero := by
  intro similar
  obtain ⟨c', p', shape, _, _⟩ := ByInstantiation.similar_output_inv
    (c := ByInstantiation.nameZero) (p := zeroT) (ByInstantiation.similar_symm similar)
  have reads := congrArg read shape
  rw [ByInstantiation.read_zero, ByInstantiation.read_output] at reads
  simp at reads

/-- **The junk state's knowledge has no solution.** -/
theorem junk_unsolvable : ¬ knowledge.Solvable junk.knowledge := by
  intro solvable
  obtain ⟨g, solves⟩ := (ByInstantiation.solvable_iff (F := groundFrame)
    [(ByInstantiation.obs zeroT, ByInstantiation.obs ByInstantiation.outputZero)]).mp solvable
  have similar := solves _ (List.mem_singleton_self _)
  change ObsSimilar (instantiateObservation g (ByInstantiation.obs (zeroT : G [] .pr)))
    (instantiateObservation g (ByInstantiation.obs ByInstantiation.outputZero)) at similar
  rw [ByInstantiation.instantiateObservation_ground, ByInstantiation.instantiateObservation_ground]
    at similar
  exact zero_not_similar_output (ByInstantiation.obsSimilar_closed.mp similar)

/-- The junk state represents no process. -/
theorem junk_not_represented (P : RhoProcess) : ¬ ByInstantiation.Represents junk P := by
  rintro ⟨value, represented⟩
  exact junk_unsolvable ((ByInstantiation.solvable_iff _).mpr represented.solvable)

/-- Beside the junk state, the knowledge has no solution. -/
theorem tensor_junk_unsolvable (s : ByInstantiation.State) :
    ¬ knowledge.Solvable (tensor s junk).knowledge := fun solvable =>
  junk_unsolvable ((tensor_solvable_iff s junk).mp solvable).2

/-- Junk on the left of a tensor: still no solution. -/
theorem junk_tensor_unsolvable (s : ByInstantiation.State) :
    ¬ knowledge.Solvable (tensor junk s).knowledge := fun solvable =>
  junk_unsolvable ((tensor_solvable_iff junk s).mp solvable).1

/-! ## Unsolvable knowledge is inert -/

/-- **No firing of any program is admitted at a state whose knowledge has no solution.** -/
theorem not_admitted {P : RuleSyntax.Program (RuleSyntax.Contextual.Terms sig)}
    {s : ByInstantiation.State} (unsolvable : ¬ knowledge.Solvable s.knowledge)
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations sig) P s.frame) :
    ¬ f.Admits knowledge s := by
  rintro ⟨_, _, ⟨b, σ, solved⟩, _⟩
  exact unsolvable ⟨b, _, RuleSyntax.Firing.knowledge_solved f solved⟩

/-- **A system whose knowledge has no solution never succeeds.** -/
theorem system_inert (ω : G [] .nm) {S : System}
    (unsolvable : ¬ knowledge.Solvable S.state.knowledge) : ¬ (stepParallel ω).Succeeds S := by
  rintro ⟨T, run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨T₁, ⟨_, f, admitted, _⟩, _⟩
  · exact RuleSyntax.Equivalence.not_mayBarb_of_unsolvable (X := knowledge) unsolvable shows
  · exact not_admitted unsolvable f admitted

/-- **A state of the four-rule program whose knowledge has no solution never succeeds.** -/
theorem state_inert (ω : G [] .nm) {s : ByInstantiation.State}
    (unsolvable : ¬ knowledge.Solvable s.knowledge) : ¬ ∃ t, Runs s t ∧ OutBarb ω t := by
  rintro ⟨t, run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨t₁, ⟨f, admitted, _⟩, _⟩
  · exact RuleSyntax.Equivalence.not_mayBarb_of_unsolvable (X := knowledge) unsolvable shows
  · exact not_admitted unsolvable f admitted

/-! ## The four-rule program is positive -/

/-- **No rule of the four-rule program has a check, a collect pattern or a tell.** -/
theorem program_positive :
    ∀ r ∈ ByInstantiation.program, r.body.checks = [] ∧ r.collect = [] ∧ r.body.tell = [] := by
  intro r member
  rcases ByInstantiation.mem_program.mp member with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl⟩

/-! ## The switch, with the four-rule program on both sides -/

/-- `ω!(0)` is closed when `ω` is. -/
theorem output_closed {ω : G [] .nm} (closed : Closed ω) : Closed (outputT ω zeroT) := by
  change binderSafeAt "NQuote" 0 (read (outputT ω zeroT)) = true
  rw [ByInstantiation.read_output, ByInstantiation.read_zero]
  have unfolded : binderSafeAt "NQuote" 0 (read ω) = true := closed
  simp [binderSafeAt, binderSafeListAt, unfolded]

/-- The state with the one row `ω!(0)` shows the output barb on `ω`. -/
theorem single_output_barb {ω : G [] .nm} (closed : Closed ω) :
    OutBarb ω (single (outputT ω zeroT)) :=
  (outBarb_iff (ByInstantiation.initial_represents
      (ByInstantiation.rowProcess _ (output_closed closed)) rfl) ω).mpr
    ⟨0, Finset.mem_singleton_self 0, ω, zeroT, rfl, ByInstantiation.similar_refl ω⟩

/-- The system of the four-rule program with the one row `ω!(0)`. -/
def outputSystem (ω : G [] .nm) : System := ⟨ByInstantiation.program, single (outputT ω zeroT)⟩

/-- The system of the four-rule program with the junk state. -/
def junkSystem : System := ⟨ByInstantiation.program, junk⟩

/-- **With every pair composable, the step is switchable without any absence**: the system of the
four-rule program with the row `ω!(0)` succeeds, and beside the system of the same program with the
junk state it never does. -/
theorem junk_switches {ω : G [] .nm} (closed : Closed ω) : (stepParallel ω).Switchable :=
  ⟨outputSystem ω, junkSystem, trivial, ⟨outputSystem ω, .refl, single_output_barb closed⟩,
    system_inert ω (tensor_junk_unsolvable (single (outputT ω zeroT)))⟩

/-- **The image of the reflective calculus is switched off by junk**: `rhoIntoStep` of `@0!(0)`
succeeds on `@0`, and beside the junk system it never does. -/
theorem image_switched_off :
    (stepParallel ByInstantiation.nameZero).Succeeds ((rhoIntoStep (ω := ByInstantiation.nameZero)
        (by decide)).map outputNil) ∧
      ¬ (stepParallel ByInstantiation.nameZero).Succeeds
        ((stepParallel ByInstantiation.nameZero).par
          ((rhoIntoStep (ω := ByInstantiation.nameZero) (by decide)).map outputNil) junkSystem) :=
  ⟨(rhoIntoStep (ω := ByInstantiation.nameZero) (by decide)).preserves outputNil succeeds_output,
    system_inert _ (tensor_junk_unsolvable (encode outputNil))⟩

/-! ## The states of the four-rule program, as a calculus with a parallel composition -/

/-- **The four-rule program's states**, composed by the tensor with every pair composable; success
the output barb on `ω`; equality as the static equivalence. -/
def fourRuleParallel (ω : G [] .nm) : ParallelCalculus where
  Term := ByInstantiation.State
  step := Moves
  par := tensor
  composable _ _ := True
  success := OutBarb ω
  same := Eq

/-- **The reflective calculus embeds uniformly into the states of its own four-rule program.** -/
def encodeUniform {ω : G [] .nm} (closed : Closed ω) :
    UniformTranslation (rhoParallel ω) (fourRuleParallel ω) where
  map := encode
  homomorphic P Q _ := encode_par P Q
  preserves P succeeds := (encode_successSensitive closed P).mp succeeds
  reflects P succeeds := (encode_successSensitive closed P).mpr succeeds

/-- **With every pair composable, the states of the four-rule program are switchable**, by junk. -/
theorem fourRule_switchable {ω : G [] .nm} (closed : Closed ω) : (fourRuleParallel ω).Switchable :=
  ⟨single (outputT ω zeroT), junk, trivial, ⟨_, .refl, single_output_barb closed⟩,
    state_inert ω (tensor_junk_unsolvable (single (outputT ω zeroT)))⟩

/-- **The same strict separation, between the reflective calculus and the states of its own
four-rule program**, with every pair composable: the criterion then measures the failure state of
unsolvable knowledge. -/
theorem strict_separation_fourRule {ω : G [] .nm} (closed : Closed ω) :
    Nonempty (UniformTranslation (rhoParallel ω) (fourRuleParallel ω)) ∧
      IsEmpty (UniformTranslation (fourRuleParallel ω) (rhoParallel ω)) :=
  ⟨⟨encodeUniform closed⟩,
    isEmpty_uniformTranslation (fourRule_switchable closed) (rhoParallel_persistent ω)⟩

/-- **With every pair composable, the negative half holds for every persistent target.** -/
theorem step_not_into_any_persistent (ω : G [] .nm) (M : ParallelCalculus) (persistent : M.Persistent) :
    IsEmpty (UniformTranslation (stepParallel ω) M) :=
  isEmpty_uniformTranslation (stepParallel_switchable ω) persistent

/-! ## What the restriction excludes -/

/-- **The junk pair is not composable when composition asks for solvable joint knowledge.** -/
theorem junk_pair_not_composable (ω : G [] .nm) :
    ¬ (stepParallelSolvable ω).composable (outputSystem ω) junkSystem :=
  tensor_junk_unsolvable _

/-! ## Weak barbed bisimilarity and the tensor, with a state that represents nothing -/

/-- **The junk state and the empty state are weakly barbed bisimilar**: neither moves nor shows a
barb. -/
theorem junk_bisimilar_empty : WeaklyBarbedBisimilar junk emptyState := by
  refine ⟨fun s t => (s = junk ∧ t = emptyState) ∨ (s = emptyState ∧ t = junk), ⟨?_, ?_, ?_⟩,
    .inl ⟨rfl, rfl⟩⟩
  · rintro s t (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .inr ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · rintro s t s' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) move
    · obtain ⟨f, admitted, _⟩ := move
      exact (not_admitted junk_unsolvable f admitted).elim
    · exact (empty_stuck _ move).elim
  · rintro s t c _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) barb
    · exact (RuleSyntax.Equivalence.not_mayBarb_of_unsolvable (X := knowledge) junk_unsolvable
        barb).elim
    · obtain ⟨o, present, _⟩ := barb
      exact absurd present (Finset.notMem_empty o)

/-- The empty state beside `ω!(0)` shows the barb on `ω`. -/
theorem empty_output_barb {ω : G [] .nm} (closed : Closed ω) :
    OutBarb ω (tensor emptyState (single (outputT ω zeroT))) := by
  have represented := tensor_represents (empty_represents (P := nil) primes_zero)
    (ByInstantiation.initial_represents (ByInstantiation.rowProcess _ (output_closed closed)) rfl)
    (R := ByInstantiation.rowProcess _ (output_closed closed))
    (by rw [nil_bag, zero_add])
  refine (outBarb_iff represented ω).mpr ⟨1, mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩),
    ω, zeroT, ?_, ByInstantiation.similar_refl ω⟩
  exact tensorValue_odd (fun _ => zeroT) (fun _ => outputT ω zeroT) 0

/-- **With a state that represents nothing, weak barbed bisimilarity is not a congruence for the
tensor**: the junk state and the empty state are bisimilar, and beside `ω!(0)` they are not. -/
theorem junk_not_congruence {ω : G [] .nm} (closed : Closed ω) :
    WeaklyBarbedBisimilar junk emptyState ∧
      ¬ WeaklyBarbedBisimilar (tensor junk (single (outputT ω zeroT)))
        (tensor emptyState (single (outputT ω zeroT))) := by
  refine ⟨junk_bisimilar_empty, ?_⟩
  rintro ⟨R, bisimulation, related⟩
  obtain ⟨t', run, shows⟩ := bisimulation.barbs ω closed (bisimulation.symm related)
    (empty_output_barb closed)
  exact state_inert ω (junk_tensor_unsolvable _) ⟨t', run, shows⟩

#print axioms zero_not_similar_output
#print axioms junk_unsolvable
#print axioms junk_not_represented
#print axioms tensor_junk_unsolvable
#print axioms junk_tensor_unsolvable
#print axioms not_admitted
#print axioms system_inert
#print axioms state_inert
#print axioms program_positive
#print axioms single_output_barb
#print axioms junk_switches
#print axioms image_switched_off
#print axioms encodeUniform
#print axioms fourRule_switchable
#print axioms strict_separation_fourRule
#print axioms step_not_into_any_persistent
#print axioms junk_pair_not_composable
#print axioms junk_bisimilar_empty
#print axioms empty_output_barb
#print axioms junk_not_congruence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
