import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Strict
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Compositionality

/-!
# The calculus of the separation: systems, where composition brings rules

The richer criteria (`rho_into_step`) are stated for the states of the four-rule program
(`stepCalculus ω`), with weak barbed bisimilarity as the equivalence. The separation is stated for
systems (`stepParallelSolvable ω`), whose composition is the union of the programs with the tensor of
the states and whose equivalence is equality. This module puts the translation of the separation,
`P ↦ ⟨program, encode P⟩` (`image`), in the calculus of systems.

## The richer criteria there

* With equality, the equivalence of the separation, operational correspondence fails
  (`oc_fails_up_to_equality`): `@0(y).0 | @0!(0)` reduces to `0`, and no run of the step from the
  image of the first reaches the image of the second, because every firing of the four-rule program
  leaves knowledge behind (`moves_knowledge_ne_nil`) and the image of `0` has none.
* With "same program and weakly barbed bisimilar states" (`SystemBisimilar`), operational
  correspondence and divergence reflection hold (`image_operationalCorrespondence`,
  `image_divergenceReflecting`): they transfer from the states.

## Composition brings rules: the image of `0` is not a unit

In the reflective calculus `P | 0 ≡ P`. Here a component brings its rules to the rows of the other:
a system with no rule has no reduction, whatever its rows (`ruleless_stuck`); the system with no rule
and the rows of `@0(y).0 | @0!(0)` is composable with the image of `0` (the four-rule program, no
row), and beside it reduces (`image_nil_not_unit`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (sig G Closed read zeroT knowledge)

/-! ## The calculus of systems -/

/-- **Systems as a calculus**, with a chosen equivalence. -/
def systemsCalculus (ω : G [] .nm) (equiv : System → System → Prop) : Calculus :=
  ⟨System, SystemReduces, fun S => OutBarb ω S.state, equiv⟩

/-- The translation of the separation, `P ↦ ⟨program, encode P⟩`. -/
def image (P : RhoProcess) : System := ⟨ByInstantiation.program, encode P⟩

/-- Same program, weakly barbed bisimilar states. -/
def SystemBisimilar (S T : System) : Prop :=
  S.program = T.program ∧ WeaklyBarbedBisimilar S.state T.state

/-! ## The richer criteria transfer with the lifted equivalence -/

/-- **Operational correspondence of `image`, up to `SystemBisimilar`.** -/
theorem image_operationalCorrespondence (ω : G [] .nm) :
    OperationalCorrespondence (L := rhoCalculus ω) (M := systemsCalculus ω SystemBisimilar) image where
  complete P P' run := by
    obtain ⟨T, runs, bisimilar⟩ := (encode_operationalCorrespondence ω).complete P P' run
    exact ⟨⟨ByInstantiation.program, T⟩, systemRuns_of_runs runs, rfl, bisimilar⟩
  sound P T run := by
    obtain ⟨same, runs⟩ := systemRuns_program run
    obtain ⟨P', reaches, T', runs', bisimilar⟩ := (encode_operationalCorrespondence ω).sound P _ runs
    refine ⟨P', reaches, ⟨ByInstantiation.program, T'⟩, ?_, rfl, bisimilar⟩
    obtain ⟨program, state⟩ := T
    change program = ByInstantiation.program at same
    subst same
    exact systemRuns_of_runs runs'

/-- **Divergence reflection of `image`.** -/
theorem image_divergenceReflecting (ω : G [] .nm) :
    DivergenceReflecting (L := rhoCalculus ω) (M := systemsCalculus ω SystemBisimilar) image := by
  intro P diverges
  obtain ⟨f, start, steps⟩ :
      ∃ f : ℕ → System, f 0 = image P ∧ ∀ n, SystemReduces (f n) (f (n + 1)) := diverges
  have programs : ∀ n, (f n).program = ByInstantiation.program := by
    intro n
    induction n with
    | zero => rw [start]; rfl
    | succ n ih => exact (steps n).1.trans ih
  refine divergence_reflected (encode_represents P) ⟨fun n => (f n).state, ?_, ?_⟩
  · show (f 0).state = encode P
    rw [start]
    rfl
  intro n
  obtain ⟨_, moved⟩ := steps n
  rw [programs n] at moved
  exact moved

/-! ## With equality, operational correspondence fails -/

/-- **Every firing of the four-rule program leaves knowledge behind.** -/
theorem moves_knowledge_ne_nil {s s' : ByInstantiation.State} (move : Moves s s') :
    s'.knowledge ≠ [] := by
  obtain ⟨f, admitted, rfl⟩ := move
  obtain ⟨⟨_, _, _, takeLength, _⟩, _⟩ := admitted
  have takes : f.rule.body.take ≠ [] := by
    rcases ByInstantiation.mem_program.mp f.member with h | h | h | h <;> rw [h] <;> simp
  have taken : f.selection.taken ≠ [] := by
    intro empty
    rw [empty] at takeLength
    exact takes (List.eq_nil_of_length_eq_zero takeLength)
  change RuleSyntax.Firing.information knowledge s f ≠ []
  unfold RuleSyntax.Firing.information RuleSyntax.Firing.matching RuleSyntax.Firing.opened
  intro empty
  simp only [List.append_eq_nil_iff, List.zipWith_eq_nil_iff, RuleInstance.map,
    List.map_eq_nil_iff] at empty
  rcases empty.1.1.2 with none | none
  · exact takes none
  · exact taken none

/-- **`@0(y).0 | @0!(0)` reduces to `0`**, modulo the equations. -/
theorem receiver_sender_to_nil : rhoLanguageDefGSLT.Step (par receiver sender) nil := by
  refine (CanonicalReaction.publicStep_iff _ _).mpr ⟨Source.afterwards, CanonicalBag.empty, ?_, ?_⟩
  · apply Subtype.ext
    rw [fromProcess_par, fromProcess_primes, fromProcess_primes, CanonicalBag.append_inventory]
    change primes Source.receiver + primes CanonicalReactionControls.payload = _
    rw [primes_of_isPrime Source.receiver_prime, primes_of_isPrime Source.payload_prime]
    rfl
  · apply Subtype.ext
    rw [nil_bag, CanonicalBag.append_inventory]
    change 0 = (fromProcess Source.afterwards.result).1 + 0
    rw [add_zero, fromProcess_primes]
    change 0 = primes (semanticCommSubst CanonicalReactionControls.zero CanonicalReactionControls.zero)
    rw [show semanticCommSubst CanonicalReactionControls.zero CanonicalReactionControls.zero =
      .apply "PZero" [] by decide]
    exact primes_zero.symm

theorem encode_nil_knowledge : (encode nil).knowledge = [] := by
  rw [encode_nil]
  rfl

theorem encode_nil_present : (encode nil).present = ∅ := by
  rw [encode_nil]
  rfl

/-- A represented state of a process with a nonempty bag has a row. -/
theorem present_nonempty {s : ByInstantiation.State} {P : RhoProcess}
    (represented : ByInstantiation.Represents s P) (nonzero : (fromProcess P).1 ≠ 0) :
    s.present ≠ ∅ := by
  obtain ⟨value, represented⟩ := represented
  intro empty
  apply nonzero
  rw [← represented.inventory_eq]
  unfold ByInstantiation.inventoryOf
  rw [empty, Finset.sum_empty]

/-- **With equality as the equivalence of systems, operational correspondence fails.** -/
theorem oc_fails_up_to_equality (ω : G [] .nm) :
    ¬ OperationalCorrespondence (L := rhoCalculus ω) (M := systemsCalculus ω Eq) image := by
  intro correspondence
  obtain ⟨T, run, same⟩ := correspondence.complete _ _ (.single receiver_sender_to_nil)
  change T = image nil at same
  subst same
  obtain ⟨_, runs⟩ := systemRuns_program run
  rcases Relation.ReflTransGen.cases_tail runs with equal | ⟨u, _, move⟩
  · have nonempty := present_nonempty (encode_represents (par receiver sender)) (by
      rw [fromProcess_par, fromProcess_primes, fromProcess_primes]
      change primes Source.receiver + primes CanonicalReactionControls.payload ≠ 0
      rw [primes_of_isPrime Source.receiver_prime]
      simp)
    apply nonempty
    rw [← equal]
    exact encode_nil_present
  · exact moves_knowledge_ne_nil move encode_nil_knowledge

/-! ## Composition brings rules -/

/-- The rows of `@0(y).0 | @0!(0)`. -/
abbrev receiverSenderRows : ByInstantiation.State := encode (par receiver sender)

/-- A represented state has solvable knowledge. -/
theorem represented_solvable {s : ByInstantiation.State} {P : RhoProcess}
    (represented : ByInstantiation.Represents s P) : knowledge.Solvable s.knowledge := by
  obtain ⟨value, represented⟩ := represented
  exact (ByInstantiation.solvable_iff _).mpr represented.solvable

/-- **A system with no rule has no reduction.** -/
theorem ruleless_stuck (s : ByInstantiation.State) (T : System) : ¬ SystemReduces ⟨∅, s⟩ T := by
  rintro ⟨_, f, _, _⟩
  exact Set.notMem_empty _ f.member

/-- `@0(y).0 | @0!(0)` communicates. -/
theorem receiver_sender_communicates : ∃ P', rhoLanguageDefGSLT.Step (par receiver sender) P' :=
  ⟨nil, receiver_sender_to_nil⟩

/-- A state that represents a process with a reduction has a move. -/
theorem moves_of_step {s : ByInstantiation.State} {P P' : RhoProcess}
    (represented : ByInstantiation.Represents s P) (step : rhoLanguageDefGSLT.Step P P') :
    ∃ t, Moves s t := by
  obtain ⟨s₁, s₂, admin, comm, _⟩ :=
    ByInstantiation.reflective_calculus_by_instantiation.2.2.2.2.1 represented step
  rcases Relation.ReflTransGen.cases_head admin with rfl | ⟨t, first, _⟩
  · exact ⟨s₂, communicates_moves comm⟩
  · exact ⟨t, administers_moves first⟩

/-- The composite of a rule-less system with the image of `0` is the four-rule program on the
tensor. -/
theorem composite_ruleless_eq (ω : G [] .nm) (s : ByInstantiation.State) :
    (stepParallelSolvable ω).par ⟨∅, s⟩ ⟨ByInstantiation.program, encode nil⟩ =
      ⟨ByInstantiation.program, tensor s (encode nil)⟩ := by
  show (⟨∅ ∪ ByInstantiation.program, tensor s (encode nil)⟩ : System) = _
  rw [Set.empty_union]

/-- **The image of `0` is not a unit of the composition**: the rule-less system holding the rows of
`@0(y).0 | @0!(0)` has no reduction; it is composable with the image of `0`, and beside it it has
one. -/
theorem image_nil_not_unit (ω : G [] .nm) :
    (∀ T, ¬ SystemReduces ⟨∅, receiverSenderRows⟩ T) ∧
      (stepParallelSolvable ω).composable ⟨∅, receiverSenderRows⟩ ⟨ByInstantiation.program, encode nil⟩ ∧
      ∃ T, SystemReduces
        ((stepParallelSolvable ω).par ⟨∅, receiverSenderRows⟩ ⟨ByInstantiation.program, encode nil⟩) T := by
  refine ⟨ruleless_stuck receiverSenderRows, (tensor_solvable_iff _ _).mpr
    ⟨represented_solvable (encode_represents _), represented_solvable (encode_represents _)⟩, ?_⟩
  rw [composite_ruleless_eq]
  obtain ⟨P', step⟩ := receiver_sender_communicates
  have represented : ByInstantiation.Represents (tensor receiverSenderRows (encode nil))
      (par (par receiver sender) nil) := by
    obtain ⟨left, onLeft⟩ := encode_represents (par receiver sender)
    obtain ⟨right, onRight⟩ := encode_represents nil
    exact ⟨_, tensor_represents onLeft onRight (fromProcess_par _ _)⟩
  obtain ⟨t, move⟩ := moves_of_step represented (rho_closedBeside _ _ nil step)
  exact ⟨⟨ByInstantiation.program, t⟩, rfl, move⟩

#print axioms image_operationalCorrespondence
#print axioms image_divergenceReflecting
#print axioms moves_knowledge_ne_nil
#print axioms receiver_sender_to_nil
#print axioms encode_nil_knowledge
#print axioms present_nonempty
#print axioms oc_fails_up_to_equality
#print axioms represented_solvable
#print axioms ruleless_stuck
#print axioms moves_of_step
#print axioms composite_ruleless_eq
#print axioms image_nil_not_unit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
