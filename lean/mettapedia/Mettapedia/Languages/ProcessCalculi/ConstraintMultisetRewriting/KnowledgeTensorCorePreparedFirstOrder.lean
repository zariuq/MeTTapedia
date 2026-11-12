import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCorePrepared
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreTraceControls

/-!
# The first-order step: every native run is a cut of framed prepared leaves

The proofs of the first-order effect core are paths of prepared candidates: shaped selections of
present occurrences with fresh outputs and a consistent problem. Admission, the guards and the
predicate queries, is the grade. Nothing here restricts the checks or the queries of a firing.

* `proofTransport`, `proofInterpretation`: transport and framing of the proof step. A prepared
  candidate is framed beside a context whose occurrences it does not take; the placed candidate
  must be prepared there.
* `admission_invariant`: admission is a property of similarity classes of proofs.
* `native_run_iff_permitted`: **the native runs of the first-order step are exactly the permitted
  proofs**, with the same firings at the same states. No hypothesis.
* `first_order_placed_proof_runs_iff_graded`: a proof has a placed proof that is permitted
  exactly on its grade.
* `prepares_footprint`, `event_is_framed_prepared_leaf`: **every admitted firing is a prepared
  leaf at its footprint, and the rest of the configuration is in its grade.** So every native
  run is a cut of framed prepared leaves (`every_event_is_a_framed_prepared_leaf`). This holds
  for counting checks and for predicate queries, where the leaf itself need not be admitted.

## Controls

* `a_count_is_a_prepared_leaf_at_its_footprint`: the firing `counts 2`, refused at its
  footprint, is a prepared leaf there, and the two occurrences beside it are in its grade.
* `the_empty_context_is_not_in_its_grade`: beside nothing it is not permitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open GuardFreeProcessOrders (SameUpTo problem_eq equivalent_append)
open FirstOrderNativeRuns

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- The effect core of the first-order step. -/
abbrev effect : EffectCore (Frames.ofSubstitution A) O (Configuration T O) (fun _ => Firing T S O) :=
  (firstOrder A label).toStep.effectCore

/-- The admission of the first-order step, as an admission of its effect core. -/
def admission : (effect A label).Admission := fun {C} f _ => f.Valid A label C

/-- Preparation depends only on the solutions and the present occurrences. -/
theorem prepares_congr {C D : Configuration T O} (same : SameUpTo A C D) (f : Firing T S O) :
    (effect A label).Prepares (s := C) f ↔ (effect A label).Prepares (s := D) f := by
  have problems : A.Equivalent (f.selection.problem label f.rule C)
      (f.selection.problem label f.rule D) := by
    rw [problem_eq, problem_eq]
    exact equivalent_append A same.1 _
  constructor
  · rintro ⟨shapes, enabled, solvable⟩
    have here : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) := enabled
    rw [same.2] at here
    obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
    exact ⟨shapes, here, (Frames.ofSubstitution_solvable_iff A _).mpr ⟨σ, (problems σ).mp solved⟩⟩
  · rintro ⟨shapes, enabled, solvable⟩
    have here : Enabled (fun _ : O => ()) D.present (f.selection.commit (T := Unit)) := enabled
    rw [← same.2] at here
    obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
    exact ⟨shapes, here, (Frames.ofSubstitution_solvable_iff A _).mpr ⟨σ, (problems σ).mpr solved⟩⟩

/-- **Transport of the first-order proof step**: configurations with the same solutions and
occurrences, and firings moved as themselves. -/
def proofTransport : Transport (proofStep (effect A label)) where
  Iso C D := PLift (SameUpTo A C D)
  toStateIso i :=
    ⟨Frames.Iso.refl PUnit.unit,
      Frames.Equivalent.trans (Frames.Iso.equivalent_refl _) (fun _ σ => i.down.1 σ),
      Equiv.refl O, by
        simp only [Equiv.refl_toEmbedding, Finset.map_refl]
        exact i.down.2⟩
  refl C := ⟨SameUpTo.refl A C⟩
  symm i := ⟨AnnotatedRuns.sameUpTo_symm A i.down⟩
  trans i j := ⟨SameUpTo.trans A i.down j.down⟩
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike same := congrArg _ same
  admits_alike same := same ▸ Iff.rfl
  result_alike {C} {f} _ same _ _ := by
    subst same
    exact ⟨SameUpTo.refl A _⟩
  move _ f := f
  move_alike _ _ _ same := same
  move_refl _ := rfl
  move_trans _ _ _ := rfl
  move_symm _ _ := rfl
  selection_move _ f := (Interface.renameSelection_refl f.selection).symm
  admits_move i f :=
    ⟨fun ⟨prepared, _⟩ => ⟨(prepares_congr A label i.down f).mpr prepared, trivial⟩,
      fun ⟨prepared, _⟩ => ⟨(prepares_congr A label i.down f).mp prepared, trivial⟩⟩
  result_move i f _ := ⟨f.result_congr A label i.down⟩
  residual _ _ f := f
  selection_residual _ _ _ := rfl
  move_residual _ _ _ _ := rfl

/-- **The framing of first-order proofs**: a prepared candidate beside a context it does not take
from; its placed candidate must be prepared at the tensor. No permission is asked. -/
abbrev proofInterpretation : ContextualRunInterpretation (proofTransport A label) where
  Place _ _ := PUnit.{1}
  pair := fun {left right} _ => nativePair A label left right
  candidate _ f := f
  advance _ _ _ := PUnit.unit
  domain := fun {_ right} _ f => Disjoint f.selection.taken.toFinset right.present
  check := fun {left right} _ f =>
    (effect A label).Prepares (s := AnnotatedRuns.tensor left right) f
  admission := fun _ _ _ => ⟨fun ⟨prepared, _⟩ => prepared, fun prepared => ⟨prepared, trivial⟩⟩
  resultIso := fun _ _ _ framed _ => ⟨AnnotatedRuns.tensor_result_left A label framed⟩

/-- **Admission is a property of similarity classes of proofs.** -/
theorem admission_invariant : Invariant (admission A label) (proofTransport A label) := by
  intro s t one two
  induction one generalizing t with
  | nil s =>
      cases two with
      | nil => exact fun _ => Iff.rfl
      | cons g allowed later => exact fun impossible => False.elim impossible
  | cons f allowed rest ih =>
      cases two with
      | nil => exact fun impossible => False.elim impossible
      | cons g permitted later =>
          intro related
          obtain ⟨iso, same, tail⟩ := related
          have fg : f = g := same
          subst fg
          exact and_congr (Firing.valid_congr A label iso.down) (ih later tail)

/-- **The native runs of the first-order step are exactly the permitted proofs.** -/
theorem native_run_iff_permitted :
    ∀ {s : Configuration T O} (proof : (proofStep (effect A label)).Run s),
      (∃ run : (firstOrder A label).toStep.Run s, run.word = proof.word) ↔
        Permitted (admission A label) proof
  | _, .nil s => ⟨fun _ => trivial, fun _ => ⟨.nil s, rfl⟩⟩
  | _, .cons f admitted rest => by
      have ih := native_run_iff_permitted rest
      constructor
      · rintro ⟨run, word⟩
        cases run with
        | nil => exact absurd word.symm (List.cons_ne_nil _ _)
        | cons g allowed later =>
            have parts := List.cons.inj word
            have same : g = f := eq_of_heq (Sigma.mk.inj parts.1).2
            subst same
            exact ⟨allowed, ih.mp ⟨later, parts.2⟩⟩
      · rintro ⟨permitted, later⟩
        obtain ⟨run, word⟩ := ih.mpr later
        exact ⟨.cons f permitted run, congrArg (List.cons _) word⟩

/-- **A first-order proof has a permitted placed proof exactly on its grade.** -/
theorem first_order_placed_proof_runs_iff_graded {left right : Configuration T O}
    (proof : (proofStep (effect A label)).Run left) :
    (∃ native : (proofStep (effect A label)).Run (AnnotatedRuns.tensor left right),
      Places (proofInterpretation A label) (left := left) (right := right) PUnit.unit proof native ∧
        Permitted (admission A label) native) ↔
      (proofInterpretation A label).Checks (left := left) (right := right) PUnit.unit proof ∧
        PermittedAt (admission A label) (proofInterpretation A label) (left := left)
          (right := right) PUnit.unit proof :=
  placed_proof_runs_iff_graded (admission A label) (proofInterpretation A label)
    (admission_invariant A label) (left := left) (right := right) PUnit.unit proof

/-- An admitted firing is prepared at its footprint. -/
theorem prepares_footprint {C : Configuration T O} {f : Firing T S O} (valid : f.Valid A label C) :
    (effect A label).Prepares (s := footprint C f) f := by
  have occurrences := valid.firing.occurrences
  have inside : f.selection.taken.toFinset ∪ f.selection.read.toFinset ⊆ C.present :=
    Finset.union_subset occurrences.taken_subset occurrences.kept_subset
  refine ⟨⟨valid.firing.take_distinct, valid.firing.output_distinct, valid.firing.take_length,
    valid.firing.read_length, valid.firing.outputs⟩, ?_,
    (Frames.ofSubstitution_solvable_iff A _).mpr valid.firing.consistent⟩
  refine ⟨Finset.subset_union_left, Finset.subset_union_right, occurrences.apart,
    Finset.disjoint_of_subset_right inside occurrences.fresh, ?_⟩
  intro query member
  simp [Selection.commit] at member

/-- **Every native event is a framed prepared leaf, and its admission is the grade.** An admitted
firing, with any checks and any predicate queries, is a prepared candidate at its footprint; the
rest of the configuration is in the structural grade of that leaf and in its permission. -/
theorem event_is_framed_prepared_leaf {C : Configuration T O} {f : Firing T S O}
    (valid : f.Valid A label C) :
    ∃ leaf : (proofStep (effect A label)).Admits (s := footprint C f) f,
      (proofInterpretation A label).Checks (left := footprint C f) (right := rest C f) PUnit.unit
        (.cons f leaf (.nil _)) ∧
      PermittedAt (admission A label) (proofInterpretation A label) (left := footprint C f)
        (right := rest C f) PUnit.unit (.cons f leaf (.nil _)) ∧
      Nonempty ((proofTransport A label).Iso (AnnotatedRuns.tensor (footprint C f) (rest C f)) C) := by
  have occurrences := valid.firing.occurrences
  have same : SameUpTo A (AnnotatedRuns.tensor (footprint C f) (rest C f)) C :=
    tensor_footprint_rest A occurrences.taken_subset occurrences.kept_subset
  have placed : (effect A label).Prepares (s := AnnotatedRuns.tensor (footprint C f) (rest C f)) f :=
    (prepares_congr A label same f).mpr ((firstOrder A label).toStep.prepares valid)
  have framed : Disjoint f.selection.taken.toFinset (C.present \ f.selection.taken.toFinset) :=
    Finset.disjoint_sdiff
  exact ⟨⟨prepares_footprint A label valid, trivial⟩, ⟨⟨framed, placed⟩, trivial⟩,
    ⟨⟨placed, (Firing.valid_congr A label same).mpr valid⟩, trivial⟩, ⟨⟨same⟩⟩⟩

/-- Every firing of a native run is admitted at the state it fires at. -/
theorem valid_of_mem_word : ∀ {s : Configuration T O} (run : (firstOrder A label).toStep.Run s)
    (event : (_ : Configuration T O) × Firing T S O), event ∈ run.word →
      event.2.Valid A label event.1
  | _, .nil _, _, member => (List.not_mem_nil member).elim
  | _, .cons _ allowed rest, event, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact allowed
      · exact valid_of_mem_word rest event later

/-- **Every native run is a cut of framed prepared leaves.** Each of its events is a prepared
leaf at its footprint, with the rest of the state it fires at in its grade. -/
theorem every_event_is_a_framed_prepared_leaf {s : Configuration T O}
    (run : (firstOrder A label).toStep.Run s) (event : (_ : Configuration T O) × Firing T S O)
    (member : event ∈ run.word) :
    ∃ leaf : (proofStep (effect A label)).Admits (s := footprint event.1 event.2) event.2,
      (proofInterpretation A label).Checks (left := footprint event.1 event.2)
        (right := rest event.1 event.2) PUnit.unit (.cons event.2 leaf (.nil _)) ∧
      PermittedAt (admission A label) (proofInterpretation A label)
        (left := footprint event.1 event.2) (right := rest event.1 event.2) PUnit.unit
        (.cons event.2 leaf (.nil _)) ∧
      Nonempty ((proofTransport A label).Iso
        (AnnotatedRuns.tensor (footprint event.1 event.2) (rest event.1 event.2)) event.1) :=
  event_is_framed_prepared_leaf A label (valid_of_mem_word A label run event member)

/-! ## Controls -/

open KnowledgeTensorFirstOrderControls (plain) in
/-- **A count is a prepared leaf at its footprint.** The firing `counts 2` is refused at its
footprint and is a prepared candidate there; the two occurrences beside it are in its grade. -/
theorem a_count_is_a_prepared_leaf_at_its_footprint :
    ¬ (Controls.counts 2).Valid plain Controls.five
        (footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) ∧
      ∃ leaf : (proofStep (effect plain Controls.five)).Admits
          (s := footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) (Controls.counts 2),
        (proofInterpretation plain Controls.five).Checks
          (left := footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2))
          (right := rest ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) PUnit.unit
          (.cons (Controls.counts 2) leaf (.nil _)) ∧
        PermittedAt (admission plain Controls.five) (proofInterpretation plain Controls.five)
          (left := footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2))
          (right := rest ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) PUnit.unit
          (.cons (Controls.counts 2) leaf (.nil _)) := by
  have valid : (Controls.counts 2).Valid plain Controls.five ⟨[], {0} ∪ {1}⟩ :=
    (Controls.counts_valid_iff 2 ({0} ∪ {1})).mpr (by decide)
  obtain ⟨leaf, checked, permitted, _⟩ := event_is_framed_prepared_leaf plain Controls.five valid
  exact ⟨a_count_is_no_leaf_at_its_footprint.2, leaf, checked, permitted⟩

open KnowledgeTensorFirstOrderControls (plain) in
/-- **The empty context is not in its grade.** Beside nothing the same leaf is framed, its
placed candidate is prepared, and it is not permitted. -/
theorem the_empty_context_is_not_in_its_grade
    (leaf : (proofStep (effect plain Controls.five)).Admits
      (s := footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) (Controls.counts 2)) :
    ¬ PermittedAt (admission plain Controls.five) (proofInterpretation plain Controls.five)
      (left := footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) (right := Controls.empty) PUnit.unit
      (.cons (Controls.counts 2) leaf (.nil _)) := by
  rintro ⟨⟨_, valid⟩, _⟩
  have solved : plain.Models ()
      (AnnotatedRuns.tensor (footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) Controls.empty).equations :=
    fun _ member => by cases member
  have size := Controls.card_of_counts_valid 2 solved valid
  exact absurd size (by decide)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder
