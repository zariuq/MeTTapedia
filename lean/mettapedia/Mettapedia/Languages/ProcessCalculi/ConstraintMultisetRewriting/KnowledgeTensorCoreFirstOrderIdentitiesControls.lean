import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrderLent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreTraceControls

/-!
# Controls for the reading on occurrence identities

* **A predicate query that saw identities is inside the reading on identities.** The firing
  `sees` asks a predicate query that saw exactly occurrence `1`. Every occurrence has the same
  label. Where occurrence `1` is present its one-firing run is a graded proof
  (`a_query_that_saw_an_identity_is_a_zoned_proof`); where occurrence `2` is present instead it
  has none (`no_zoned_proof_at_another_identity`). On labels the two states are the same.
* **Counting.** The run that counts and then adds and removes an occurrence is a graded proof on
  identities (`a_counting_run_is_a_zoned_proof_on_identities`).
* **A word that does not run has no proof.** The word `turn`, `move`, whose uses run on labels,
  has no graded proof on identities that admits the empty extra context and ends in consistent
  knowledge (`no_zoned_proof_for_the_transposed_word`).
* **Consistent final knowledge is needed.** A use that tells `1 = 2` is a graded proof on
  identities whose final knowledge is inconsistent, and it has no native run
  (`an_inconsistent_tell_is_a_zoned_proof_on_identities`).
* **The context of a placement is a lent zone.** The run that reads, placed beside the
  occurrence `9`, is a graded proof with that occurrence lent
  (`reads_beside_nine_is_a_lent_proof`); the firing that checks the absence of `9` has no graded
  proof with it lent (`absence_has_no_proof_with_nine_lent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory
open AnnotatedRuns (Firing firstOrder)
open PredicateQueryAdmission (Query)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder (knowledge)
open KnowledgeTensorFirstOrderControls (plain sawOne)

/-! ## A predicate query that saw identities -/

/-- Asks a predicate query that saw exactly occurrence `1`; takes, reads and makes nothing. -/
def sees : Firing Nat Unit Nat := ⟨⟨[], [], [], [], []⟩, [Query.fixed sawOne], ⟨[], [], []⟩⟩

/-- Occurrence `1` is present. -/
def holdsOne : Configuration Nat Nat := ⟨[], {1}⟩

/-- Occurrence `2` is present instead; it has the same label. -/
def holdsTwo : Configuration Nat Nat := ⟨[], {2}⟩

theorem sees_admitted : sees.Valid plain (fun _ : Nat => 0) holdsOne := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, by decide,
    ⟨(), fun _ member => by cases member⟩, ?_⟩, ?_⟩
  · intro check member
    cases member
  · intro query member σ _
    obtain rfl := List.mem_singleton.mp member
    exact KnowledgeTensorFirstOrderControls.a_predicate_query_observes_identities.1

theorem sees_refused : ¬ sees.Valid plain (fun _ : Nat => 0) holdsTwo := by
  intro valid
  have asked := valid.observations (Query.fixed sawOne) (List.mem_singleton.mpr rfl) ()
    (fun _ member => by cases member)
  exact KnowledgeTensorFirstOrderControls.a_predicate_query_observes_identities.2.1 asked

theorem a_query_that_saw_an_identity_is_a_zoned_proof :
    ∃ (along : (() : Unit) ⟶ ()) (reached : Set Unit) (left : Multiset Nat)
      (grade : Multiset Nat → Prop), grade 0 ∧
        (FirstOrder.identityZoned plain (fun _ : Nat => 0)).Proves () 0
          (knowledge plain holdsOne) holdsOne.present.val grade
          ([sees].map (Sigma.mk (β := KnowledgeTensor.Const (Firing Nat Unit Nat)) ())) () along
          reached left ∧ reached.Nonempty :=
  (FirstOrder.native_run_iff_zoned_proof_on_identities plain (fun _ : Nat => 0) holdsOne [sees]).mp
    ⟨.cons sees sees_admitted (.nil _), rfl, ⟨(), fun _ member => by cases member⟩⟩

theorem no_zoned_proof_at_another_identity :
    ¬ ∃ (along : (() : Unit) ⟶ ()) (reached : Set Unit) (left : Multiset Nat)
      (grade : Multiset Nat → Prop), grade 0 ∧
        (FirstOrder.identityZoned plain (fun _ : Nat => 0)).Proves () 0
          (knowledge plain holdsTwo) holdsTwo.present.val grade
          ([sees].map (Sigma.mk (β := KnowledgeTensor.Const (Firing Nat Unit Nat)) ())) () along
          reached left ∧ reached.Nonempty := by
  intro proof
  obtain ⟨run, word, _⟩ :=
    (FirstOrder.native_run_iff_zoned_proof_on_identities plain (fun _ : Nat => 0) holdsTwo
      [sees]).mpr proof
  have executable := executable_of_nonempty plain (fun _ : Nat => 0) run
    (by rw [word]; exact List.cons_ne_nil _ _)
  rw [word] at executable
  exact sees_refused executable.1

/-! ## Counting -/

theorem a_counting_run_is_a_zoned_proof_on_identities :
    ∃ (along : (() : Unit) ⟶ ()) (reached : Set Unit) (left : Multiset Nat)
      (grade : Multiset Nat → Prop), grade 0 ∧
        (FirstOrder.identityZoned plain five).Proves () 0 (knowledge plain joint)
          joint.present.val grade
          ([counts 1, adds, removes].map
            (Sigma.mk (β := KnowledgeTensor.Const (Firing Nat Unit Nat)) ())) () along
          reached left ∧ reached.Nonempty :=
  (FirstOrder.native_run_iff_zoned_proof_on_identities plain five joint
      [counts 1, adds, removes]).mp
    ⟨countsFirst, rfl, ⟨(), removes_problem_solved
      (adds_problem_solved (counts_problem_solved 1 joint_solved))⟩⟩

/-! ## A word that does not run -/

theorem no_zoned_proof_for_the_transposed_word :
    ¬ ∃ (along : (() : Unit) ⟶ ()) (reached : Set Unit) (left : Multiset Nat)
      (grade : Multiset Nat → Prop), grade 0 ∧
        (FirstOrder.identityZoned plain tokenLabel).Proves () 0 (knowledge plain start)
          start.present.val grade
          ([turn, move].map (Sigma.mk (β := KnowledgeTensor.Const (Firing Nat Unit Nat)) ())) ()
          along reached left ∧ reached.Nonempty := by
  intro proof
  obtain ⟨run, word, _⟩ :=
    (FirstOrder.native_run_iff_zoned_proof_on_identities plain tokenLabel start [turn, move]).mpr
      proof
  exact no_transposed_run ⟨run, word⟩

/-! ## The hypothesis on the final knowledge -/

/-- Tells `1 = 2`; takes, reads and makes nothing. -/
def contradicts : Firing Nat Unit Nat := ⟨⟨[], [], [(1, 2)], [], []⟩, [], ⟨[], [], []⟩⟩

theorem contradicts_fires :
    (FirstOrder.identityZoned plain id).FiresUnder (a := ()) 0 contradicts
      (knowledge plain holdsOne) holdsOne.present.val
      (knowledge plain holdsOne ⊓
        {σ | plain.Models σ (GuardFreeProcessOrders.added id contradicts.rule contradicts.selection)})
      holdsOne.present.val := by
  refine ⟨holdsOne.present.val, ?_, ?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_⟩, rfl, ?_⟩
  · show holdsOne.present.val = ([] : List Nat).toFinset.val + holdsOne.present.val
    simp
  · show ([] : List Nat).toFinset.val ≤ holdsOne.present.val + 0
    simp
  · show Disjoint ([] : List Nat).toFinset
      (([] : List Nat).toFinset ∪ (holdsOne.present.val + 0).toFinset)
    simp
  · intro check member
    cases member
  · intro query member
    cases member
  · show holdsOne.present.val = ([] : List Nat).toFinset.val +
      Multiset.map (fun atom : Nat => atom) holdsOne.present.val
    simp

/-- **Consistent final knowledge is needed.** A use that tells `1 = 2` is a graded proof on
identities whose grade admits the empty extra context; its final knowledge is inconsistent, and
it has no native run. -/
theorem an_inconsistent_tell_is_a_zoned_proof_on_identities :
    (∃ (along : (() : Unit) ⟶ ()) (reached : Set Unit) (left : Multiset Nat)
      (grade : Multiset Nat → Prop), grade 0 ∧
        (FirstOrder.identityZoned plain id).Proves () 0 (knowledge plain holdsOne)
          holdsOne.present.val grade
          ([contradicts].map (Sigma.mk (β := KnowledgeTensor.Const (Firing Nat Unit Nat)) ())) ()
          along reached left ∧ ¬ reached.Nonempty) ∧
      ¬ ∃ run : (firstOrder plain id).toStep.Run holdsOne, sites plain id run = [contradicts] := by
  have added : GuardFreeProcessOrders.added id contradicts.rule contradicts.selection = [(1, 2)] :=
    rfl
  constructor
  · have zoned := KnowledgeTensor.ZonedSystem.RunUnder.fire
      (sys := FirstOrder.identityZoned plain id) contradicts_fires
      (KnowledgeTensor.ZonedSystem.RunUnder.done _ _ _ _)
    obtain ⟨grade, atZero, proof⟩ := KnowledgeTensor.ZonedSystem.RunUnder.proves zoned
    refine ⟨_, _, _, grade, atZero, proof, ?_⟩
    rintro ⟨σ, member⟩
    have solved : plain.Models σ
        (GuardFreeProcessOrders.added id contradicts.rule contradicts.selection) := member.2
    rw [added] at solved
    have wrong : (1 : Nat) = 2 := solved (1, 2) (List.mem_singleton.mpr rfl)
    exact absurd wrong (by decide)
  · rintro ⟨run, word⟩
    have executable := executable_of_nonempty plain id run
      (by rw [word]; exact List.cons_ne_nil _ _)
    rw [word] at executable
    obtain ⟨σ, solved⟩ := executable.1.firing.consistent
    have shape : contradicts.selection.problem id contradicts.rule holdsOne = [(1, 2)] := rfl
    rw [shape] at solved
    have wrong : (1 : Nat) = 2 := solved (1, 2) (List.mem_singleton.mpr rfl)
    exact absurd wrong (by decide)

/-! ## The context of a placement is a lent zone -/

open KnowledgeTensorFirstOrderControls (one) in
/-- The run that reads, beside the occurrence `9`, is a graded proof with that occurrence
lent. -/
theorem reads_beside_nine_is_a_lent_proof :
    ∃ (along : (() : Unit) ⟶ ()) (reached : Set Unit) (left : Multiset Nat)
      (grade : Multiset Nat → Prop), grade 0 ∧
        (FirstOrder.identityZoned plain id).Proves () (nine.present \ one.present).val
          (knowledge plain one ⊓ knowledge plain nine) one.present.val grade
          ((sites plain id readsRun).map
            (Sigma.mk (β := KnowledgeTensor.Const (Firing Nat Unit Nat)) ())) () along
          reached left :=
  FirstOrder.checks_gives_lent_proof plain id readsRun
    ⟨⟨reads_frames_nine, (valid_tensor_iff plain id reads reads_admitted).mp
      reads_is_admitted_beside_nine⟩, trivial⟩

open KnowledgeTensorFirstOrderControls (one) in
/-- The firing that checks the absence of `9` has no graded proof with the occurrence `9` lent:
a lent identity is seen by the check. -/
theorem absence_has_no_proof_with_nine_lent :
    ¬ ∃ (along : (() : Unit) ⟶ ()) (reached : Set Unit) (left : Multiset Nat)
      (grade : Multiset Nat → Prop), grade 0 ∧
        (FirstOrder.identityZoned plain id).Proves () nine.present.val
          (knowledge plain (AnnotatedRuns.tensor one nine))
          ((AnnotatedRuns.tensor one nine).present \ nine.present).val grade
          ([unlessNineFiring].map
            (Sigma.mk (β := KnowledgeTensor.Const (Firing Nat Unit Nat)) ())) () along
          reached left ∧ reached.Nonempty := by
  intro proof
  obtain ⟨run, word, _, _⟩ :=
    (FirstOrder.lent_run_iff_zoned_proof plain id (AnnotatedRuns.tensor one nine) nine.present
      Finset.subset_union_right [unlessNineFiring]).mpr proof
  have executable := executable_of_nonempty plain id run
    (by rw [word]; exact List.cons_ne_nil _ _)
  rw [word] at executable
  exact unless_nine_refused_beside_nine executable.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
