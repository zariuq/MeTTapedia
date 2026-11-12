import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrder
import Mettapedia.Logic.LinearLogic.KnowledgeTensorInitial

/-!
# The first-order step on occurrence identities: runs are zoned proofs

The reading of the first-order step on labels needs a supply of fresh occurrences and excludes
predicate queries that saw identities. On the step itself the atoms are the occurrence
identities. Read on identities, the first-order step is a zoned system at one frame:

* knowledge is the set of solutions of the store, and telling adds the matching equations and
  the rule's tell;
* a firing takes, reads and makes the identities of its selection;
* its guard holds the shape conditions, which do not depend on the state;
* its check reads every present identity: the outputs are fresh, and every check and every
  predicate query holds at every solution of the knowledge after the tell.

## Results

* `firesUnder_of_valid`, `valid_of_firesUnder`: an admitted firing is a firing of the zoned
  transition, and conversely when the knowledge it reaches is consistent.
* `native_run_iff_zoned_proof_on_identities`: **native runs that end in consistent knowledge are
  exactly the graded proofs** whose grade admits the empty extra context and whose final
  knowledge is consistent, with the same firings in the same order. Every kind of check and
  every predicate query is included, and no supply of occurrences is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory
open AnnotatedRuns (Firing firstOrder)
open GuardFreeProcessOrders (problem_eq added)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder (knowledge)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- A set of present identities splits into the taken ones and the rest. -/
theorem val_split {present taken : Finset O} (inside : taken ⊆ present) :
    present.val = taken.val + (present \ taken).val := by
  rw [Finset.sdiff_val, add_tsub_cancel_of_le (Finset.val_le_iff.mpr inside)]

/-- The identities after a firing: the fresh outputs beside the rest. -/
theorem fire_val {present taken made : Finset O} (fresh : Disjoint made present) :
    ((present \ taken) ∪ made).val = made.val + (present \ taken).val := by
  have apart : Disjoint (present \ taken) made := (fresh.mono_right Finset.sdiff_subset).symm
  rw [← Finset.disjUnion_eq_union _ _ apart, add_comm]
  rfl

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The first-order step as declared transitions on occurrence identities.** -/
abbrev identityZoned : KnowledgeTensor.ZonedSystem Unit (KnowledgeTensor.Const (Set S))
    (KnowledgeTensor.Const O) (KnowledgeTensor.Const (Firing T S O)) where
  know := fun _ known => known
  know_id := fun _ => rfl
  know_comp := fun _ _ _ => rfl
  know_inf := fun _ _ _ => rfl
  carry := fun _ atom => atom
  carry_id := fun _ => rfl
  carry_comp := fun _ _ _ => rfl
  target := fun {a} _ => a
  extend := fun {a} _ => 𝟙 a
  take := fun f => f.selection.taken.toFinset.val
  read := fun f => f.selection.read.toFinset.val
  make := fun f => f.selection.made.toFinset.val
  tell := fun f => {σ | A.Models σ (added label f.rule f.selection)}
  guard := fun f _ => f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
    f.rule.take.length = f.selection.taken.length ∧
    f.rule.read.length = f.selection.read.length ∧ f.selection.made.map label = f.rule.produce
  guard_mono := fun _ _ _ _ holds => holds
  check := fun f known rest =>
    Disjoint f.selection.made.toFinset (f.selection.taken.toFinset ∪ rest.toFinset) ∧
      (∀ check ∈ f.rule.checks, ∀ σ ∈ known,
        check.Holds A σ label (f.selection.taken.toFinset ∪ rest.toFinset)) ∧
      ∀ query ∈ f.queries, ∀ σ ∈ known,
        (query.atSolution σ).Holds label (f.selection.taken.toFinset ∪ rest.toFinset)
  check_mono := fun _ _ _ _ refines holds =>
    ⟨holds.1, fun check member σ inside => holds.2.1 check member σ (refines inside),
      fun query member σ inside => holds.2.2 query member σ (refines inside)⟩

/-- The knowledge after a firing is the knowledge before, and what the firing tells. -/
theorem knowledge_result (C : Configuration T O) (f : Firing T S O) :
    knowledge A (f.result label C) =
      knowledge A C ⊓ {σ | A.Models σ (added label f.rule f.selection)} := by
  ext σ
  show A.Models σ (f.selection.problem label f.rule C) ↔
    A.Models σ C.equations ∧ A.Models σ (added label f.rule f.selection)
  rw [problem_eq, A.models_append]

omit [DecidableEq O] in
/-- A solution of the problem of a firing is in the knowledge after its tell. -/
theorem mem_of_models_problem (C : Configuration T O) (f : Firing T S O) (σ : S)
    (solved : A.Models σ (f.selection.problem label f.rule C)) :
    σ ∈ (knowledge A C ⊓ {σ | A.Models σ (added label f.rule f.selection)} : Set S) := by
  rw [problem_eq, A.models_append] at solved
  exact solved

omit [DecidableEq O] in
/-- A solution in the knowledge after the tell solves the problem of the firing. -/
theorem models_problem_of_mem (C : Configuration T O) (f : Firing T S O) (σ : S)
    (member : σ ∈ (knowledge A C ⊓ {σ | A.Models σ (added label f.rule f.selection)} : Set S)) :
    A.Models σ (f.selection.problem label f.rule C) := by
  rw [problem_eq, A.models_append]
  exact member

/-- The identities a check reads beside the taken ones are all the present identities. -/
theorem read_store {C : Configuration T O} {f : Firing T S O}
    (inside : f.selection.taken.toFinset ⊆ C.present) :
    f.selection.taken.toFinset ∪ ((C.present \ f.selection.taken.toFinset).val + 0).toFinset =
      C.present := by
  rw [add_zero, Finset.val_toFinset, Finset.union_sdiff_of_subset inside]

/-- **An admitted firing is a firing of the zoned transition.** -/
theorem firesUnder_of_valid {C : Configuration T O} {f : Firing T S O} (valid : f.Valid A label C) :
    (identityZoned A label).FiresUnder (a := ()) 0 f (knowledge A C) C.present.val
      (knowledge A (f.result label C)) (f.result label C).present.val := by
  have occurrences := valid.firing.occurrences
  have inside : f.selection.taken.toFinset ⊆ C.present := occurrences.taken_subset
  have store := read_store inside
  refine ⟨(C.present \ f.selection.taken.toFinset).val, val_split inside, ?_, ?_, ?_,
    knowledge_result A label C f, ?_⟩
  · show f.selection.read.toFinset.val ≤ (C.present \ f.selection.taken.toFinset).val + 0
    rw [add_zero]
    exact Finset.val_le_iff.mpr fun occurrence member =>
      Finset.mem_sdiff.mpr ⟨occurrences.kept_subset member,
        fun taken => Finset.disjoint_left.mp occurrences.apart taken member⟩
  · exact ⟨valid.firing.take_distinct, valid.firing.output_distinct, valid.firing.take_length,
      valid.firing.read_length, valid.firing.outputs⟩
  · refine ⟨?_, ?_, ?_⟩
    · show Disjoint f.selection.made.toFinset
        (f.selection.taken.toFinset ∪ ((C.present \ f.selection.taken.toFinset).val + 0).toFinset)
      rw [store]
      exact occurrences.fresh
    · intro check member σ known
      have here := valid.firing.checks check member σ (models_problem_of_mem A label C f σ known)
      show check.Holds A σ label
        (f.selection.taken.toFinset ∪ ((C.present \ f.selection.taken.toFinset).val + 0).toFinset)
      rw [store]
      exact here
    · intro query member σ known
      have here := valid.observations query member σ (models_problem_of_mem A label C f σ known)
      show (query.atSolution σ).Holds label
        (f.selection.taken.toFinset ∪ ((C.present \ f.selection.taken.toFinset).val + 0).toFinset)
      rw [store]
      exact here
  · show (f.result label C).present.val = f.selection.made.toFinset.val +
      Multiset.map (fun atom : O => atom) (C.present \ f.selection.taken.toFinset).val
    rw [Multiset.map_id']
    exact fire_val occurrences.fresh

/-- **A firing of the zoned transition that reaches consistent knowledge is an admitted
firing.** -/
theorem valid_of_firesUnder (C : Configuration T O) (f : Firing T S O) {reached : Set S}
    {left : Multiset O}
    (fires : (identityZoned A label).FiresUnder (a := ()) 0 f (knowledge A C) C.present.val
      reached left)
    (consistent : reached.Nonempty) :
    f.Valid A label C ∧ reached = knowledge A (f.result label C) ∧
      left = (f.result label C).present.val := by
  obtain ⟨frame, source, readable, shaped, checked, known, target⟩ := fires
  have sourced : C.present.val = f.selection.taken.toFinset.val + frame := source
  have inside : f.selection.taken.toFinset ⊆ C.present :=
    Finset.val_le_iff.mp (sourced ▸ Multiset.le_add_right _ _)
  have whole : frame = (C.present \ f.selection.taken.toFinset).val := by
    rw [Finset.sdiff_val, sourced, add_tsub_cancel_left]
  subst whole
  have store := read_store inside
  have reads : f.selection.read.toFinset.val ≤ (C.present \ f.selection.taken.toFinset).val + 0 :=
    readable
  rw [add_zero] at reads
  have readIn := Finset.val_le_iff.mp reads
  have shapes : f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
      f.rule.take.length = f.selection.taken.length ∧
      f.rule.read.length = f.selection.read.length ∧ f.selection.made.map label = f.rule.produce :=
    shaped
  have checks : Disjoint f.selection.made.toFinset
        (f.selection.taken.toFinset ∪ ((C.present \ f.selection.taken.toFinset).val + 0).toFinset) ∧
      (∀ check ∈ f.rule.checks,
        ∀ σ ∈ (knowledge A C ⊓ {σ | A.Models σ (added label f.rule f.selection)} : Set S),
          check.Holds A σ label (f.selection.taken.toFinset ∪
            ((C.present \ f.selection.taken.toFinset).val + 0).toFinset)) ∧
      ∀ query ∈ f.queries,
        ∀ σ ∈ (knowledge A C ⊓ {σ | A.Models σ (added label f.rule f.selection)} : Set S),
          (query.atSolution σ).Holds label (f.selection.taken.toFinset ∪
            ((C.present \ f.selection.taken.toFinset).val + 0).toFinset) := checked
  rw [store] at checks
  have reaches : reached = knowledge A (f.result label C) :=
    (show reached = knowledge A C ⊓ {σ | A.Models σ (added label f.rule f.selection)} from known).trans
      (knowledge_result A label C f).symm
  obtain ⟨witness, member⟩ := consistent
  have inResult : witness ∈ knowledge A (f.result label C) := reaches ▸ member
  have solved : A.Models witness (f.selection.problem label f.rule C) := inResult
  refine ⟨⟨⟨shapes.1, shapes.2.1, shapes.2.2.1, shapes.2.2.2.1, shapes.2.2.2.2,
    ⟨inside, fun occurrence member => (Finset.mem_sdiff.mp (readIn member)).1,
      Finset.disjoint_left.mpr fun occurrence taken read =>
        (Finset.mem_sdiff.mp (readIn read)).2 taken, checks.1, ?_⟩,
    ⟨witness, solved⟩,
    fun check member σ models => checks.2.1 check member σ (mem_of_models_problem A label C f σ models)⟩,
    fun query member σ models => checks.2.2 query member σ (mem_of_models_problem A label C f σ models)⟩,
    reaches, ?_⟩
  · intro query member
    simp [Selection.commit] at member
  · have made : left = f.selection.made.toFinset.val +
        Multiset.map (fun atom : O => atom) (C.present \ f.selection.taken.toFinset).val := target
    rw [made, Multiset.map_id']
    exact (fire_val checks.1).symm

/-- **A native run is a run of the zoned calculus on identities**, with the same firings. -/
theorem runUnder_of_native_run : ∀ {C : Configuration T O} (run : (firstOrder A label).toStep.Run C),
    ∃ along : (() : Unit) ⟶ (),
      (identityZoned A label).RunUnder () 0 (knowledge A C) C.present.val
        ((sites A label run).map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () along
        (knowledge A run.last) run.last.present.val
  | _, .nil C => ⟨𝟙 (), KnowledgeTensor.ZonedSystem.RunUnder.done _ _ _ _⟩
  | C, .cons f allowed rest => by
      obtain ⟨along, later⟩ := runUnder_of_native_run rest
      have carried : Multiset.map (fun atom : O => atom) (0 : Multiset O) = 0 := Multiset.map_zero _
      have later' : (identityZoned A label).RunUnder () (Multiset.map (fun atom : O => atom) 0)
          (knowledge A (f.result label C)) (f.result label C).present.val
          ((sites A label rest).map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) ()
          along (knowledge A rest.last) rest.last.present.val := carried.symm ▸ later
      exact ⟨_, KnowledgeTensor.ZonedSystem.RunUnder.fire (firesUnder_of_valid A label allowed) later'⟩

/-- **A run of the zoned calculus on identities that ends in consistent knowledge is a native
run**, with the same firings, ending in consistent knowledge. -/
theorem native_run_of_runUnder : ∀ (word : List (Firing T S O)) {C : Configuration T O}
    {along : (() : Unit) ⟶ ()} {reached : Set S} {left : Multiset O},
    (identityZoned A label).RunUnder () 0 (knowledge A C) C.present.val
      (word.map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () along reached left →
      reached.Nonempty →
      ∃ run : (firstOrder A label).toStep.Run C, sites A label run = word ∧
        A.Consistent run.last.equations
  | [], C, _, _, _, zoned, consistent => by
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines zoned
      obtain ⟨witness, member⟩ := consistent
      exact ⟨.nil C, rfl, ⟨witness, refined member⟩⟩
  | f :: rest, C, _, _, _, zoned, consistent => by
      obtain ⟨declaration, middle, held, onward, same, _, fires, later⟩ :=
        KnowledgeTensor.ZonedSystem.RunUnder.cons_inv zoned
      have which : f = declaration := eq_of_heq (Sigma.mk.inj same).2
      subst which
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines later
      have between : Set.Nonempty middle := consistent.mono refined
      obtain ⟨valid, reaches, holds⟩ := valid_of_firesUnder A label C f fires between
      subst reaches
      subst holds
      have carried : Multiset.map (fun atom : O => atom) (0 : Multiset O) = 0 := Multiset.map_zero _
      have later' : (identityZoned A label).RunUnder () 0 (knowledge A (f.result label C))
          (f.result label C).present.val
          (rest.map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () onward _ _ :=
        carried ▸ later
      obtain ⟨run, word, solvable⟩ := native_run_of_runUnder rest later' consistent
      exact ⟨.cons f valid run, congrArg (List.cons f) word, solvable⟩

/-- **Native runs of the first-order step are zoned proofs on occurrence identities.** A native
run with given firings that ends in consistent knowledge exists exactly when a graded proof
exists, from the knowledge and the present identities of the configuration, whose grade admits
the empty extra context and whose final knowledge is consistent. -/
theorem native_run_iff_zoned_proof_on_identities (C : Configuration T O)
    (word : List (Firing T S O)) :
    (∃ run : (firstOrder A label).toStep.Run C, sites A label run = word ∧
        A.Consistent run.last.equations) ↔
      ∃ (along : (() : Unit) ⟶ ()) (reached : Set S) (left : Multiset O)
        (grade : Multiset O → Prop), grade 0 ∧
          (identityZoned A label).Proves () 0 (knowledge A C) C.present.val grade
            (word.map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () along
            reached left ∧ reached.Nonempty := by
  constructor
  · rintro ⟨run, rfl, consistent⟩
    obtain ⟨along, zoned⟩ := runUnder_of_native_run A label run
    obtain ⟨grade, atZero, proof⟩ := KnowledgeTensor.ZonedSystem.RunUnder.proves zoned
    exact ⟨along, _, _, grade, atZero, proof, consistent⟩
  · rintro ⟨along, reached, left, grade, atZero, proof, consistent⟩
    have zoned := KnowledgeTensor.ZonedSystem.Proves.run proof 0 atZero
    rw [add_zero] at zoned
    exact native_run_of_runUnder A label word zoned consistent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder
