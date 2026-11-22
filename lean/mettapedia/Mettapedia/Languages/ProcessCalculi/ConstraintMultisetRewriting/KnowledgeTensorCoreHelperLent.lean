import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreHelperZoned

/-!
# The binding-aware helper step: the context of a placement is a lent zone

A helper firing takes nothing, so every set of present identities may be lent to a helper run:
the run owns the other identities, and its freshness check sees the lent ones.

* `helper_lent_run_iff_zoned_proof`: helper runs that end in consistent knowledge are exactly the
  graded proofs over the frames under any set of present identities as lent zone, from the
  remaining identities.
* `helper_checks_gives_lent_proof`: **the context of a placement is a lent zone, over the
  frames.** A local helper run whose grade admits a placement beside a context has a placed
  native run that is a graded proof at the frame of the placement: it owns the identities of its
  own state, has the other identities of the context lent, and starts from the meet of the two
  knowledges, each transported along its own frame map.
* `helper_tensor_is_zoned_proof`: **the native parallel composition of two helper runs is a
  graded proof of the tensor sequent, over the frames.**
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.HelperZoned

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory
open Helpers (State Firing helperStep extend incl)

variable {S : Signature} {O : Type} [DecidableEq O]

/-- The present occurrences after a helper firing: its occurrence beside the old ones. -/
theorem after_present {s : State S O} (f : Firing s) :
    f.after.present = insert f.made s.present := by
  show fire s.present (f.selection.commit (T := Unit)) = insert f.made s.present
  ext occurrence
  rw [mem_fire]
  simp [Firing.selection, Selection.commit, or_comm]

/-- The owned identities after a helper firing, when a set of present identities is lent. -/
theorem after_owned_val {s : State S O} (f : Firing s) (absent : f.made ∉ s.present)
    {lent : Finset O} (lentIn : lent ⊆ s.present) :
    (f.after.present \ lent).val = {f.made} + (s.present \ lent).val := by
  have unlent : f.made ∉ s.present \ lent := fun member => absent (Finset.mem_sdiff.mp member).1
  have same : f.after.present \ lent = insert f.made (s.present \ lent) := by
    rw [after_present]
    ext occurrence
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨made | present, unlentHere⟩
      · exact Or.inl made
      · exact Or.inr ⟨present, unlentHere⟩
    · rintro (made | ⟨present, unlentHere⟩)
      · refine ⟨Or.inl made, fun lentHere => absent ?_⟩
        rw [← made]
        exact lentIn lentHere
      · exact ⟨Or.inr present, unlentHere⟩
  rw [same, Finset.insert_val_of_notMem unlent, Multiset.singleton_add]

/-- **An admitted helper firing is a firing under any set of present identities as lent
zone.** -/
theorem firesUnder_lent_of_admits {s : State S O} (f : Firing s) (allowed : helperStep.Admits f)
    {lent : Finset O} (lentIn : lent ⊆ s.present) :
    (helperZoned S O).FiresUnder (a := s.frame) lent.val (ruleOf f)
      (solutions (Frames.contextual S) s.knowledge) (s.present \ lent).val
      (solutions (Frames.contextual S) f.information) (f.after.present \ lent).val := by
  have absent : f.made ∉ s.present := (Helpers.enabled_iff f).mp allowed.2.1
  refine ⟨(s.present \ lent).val, (zero_add _).symm, Multiset.zero_le _, ?_, ?_,
    solutions_information f, ?_⟩
  · intro solution member
    have solved : (Frames.contextual S).Models solution.2 f.information := by
      have inside : solution ∈ solutions (Frames.contextual S) f.information :=
        (solutions_information f).symm ▸ member
      exact inside
    exact allowed.2.2.2 solution.1 solution.2 solved
  · intro member
    have present : f.made ∈ (s.present \ lent).val + lent.val := member
    rcases Multiset.mem_add.mp present with owned | lentHere
    · exact absent (Finset.mem_sdiff.mp (Finset.mem_val.mp owned)).1
    · exact absent (lentIn (Finset.mem_val.mp lentHere))
  · have carried : Multiset.map (fun occurrence : O => occurrence) (s.present \ lent).val =
        (s.present \ lent).val := Multiset.map_id' _
    show (f.after.present \ lent).val =
      {f.made} + Multiset.map (fun occurrence : O => occurrence) (s.present \ lent).val
    rw [carried, after_owned_val f absent lentIn]

/-- **A firing under a lent zone that reaches consistent knowledge is an admitted helper
firing.** -/
theorem admits_of_firesUnder_lent (s : State S O) (rule : Rule S O s.frame) {lent : Finset O}
    (lentIn : lent ⊆ s.present) {reached : Known S (extend s.frame rule.helper)}
    {left : Multiset O}
    (fires : (helperZoned S O).FiresUnder (a := s.frame) lent.val rule
      (solutions (Frames.contextual S) s.knowledge) (s.present \ lent).val reached left)
    (consistent : reached.Nonempty) :
    helperStep.Admits (firingOf s rule) ∧
      reached = solutions (Frames.contextual S) (firingOf s rule).information ∧
      left = ((firingOf s rule).after.present \ lent).val := by
  obtain ⟨frame, source, _, asked, checked, knowledge, target⟩ := fires
  have sourced : (s.present \ lent).val = 0 + frame := source
  have whole : frame = (s.present \ lent).val := (zero_add frame).symm.trans sourced.symm
  subst whole
  have fresh : rule.made ∉ (s.present \ lent).val + lent.val := checked
  have absent : (firingOf s rule).made ∉ s.present := by
    intro present
    have here : rule.made ∈ s.present := present
    by_cases lentHere : rule.made ∈ lent
    · exact fresh (Multiset.mem_add.mpr (Or.inr (Finset.mem_val.mpr lentHere)))
    · exact fresh (Multiset.mem_add.mpr
        (Or.inl (Finset.mem_val.mpr (Finset.mem_sdiff.mpr ⟨here, lentHere⟩))))
  have known : reached = pull (Frames.contextual S) (incl s.frame rule.helper)
      (solutions (Frames.contextual S) s.knowledge) ⊓
        solutions (Frames.contextual S) [(firingOf s rule).tell] := knowledge
  have reaches : reached = solutions (Frames.contextual S) (firingOf s rule).information :=
    known.trans (solutions_information (firingOf s rule)).symm
  have guarded : ∀ solution ∈ reached,
      (Frames.contextual S).Models (Assignment.compose solution.2 (incl s.frame rule.helper))
        rule.guards := known ▸ asked
  refine ⟨⟨List.nodup_singleton _, (Helpers.enabled_iff (firingOf s rule)).mpr absent, ?_, ?_⟩,
    reaches, ?_⟩
  · exact (solvable_iff_nonempty _).mpr (reaches ▸ consistent)
  · intro later σ solved
    have member : (⟨later, σ⟩ : Frames.Solution
        (fun F G : Frames.Frame S => Assignment F.arity G.arity) (extend s.frame rule.helper)) ∈
        solutions (Frames.contextual S) (firingOf s rule).information := solved
    exact guarded ⟨later, σ⟩ (reaches ▸ member)
  · have carried : Multiset.map (fun occurrence : O => occurrence) (s.present \ lent).val =
        (s.present \ lent).val := Multiset.map_id' _
    have made : left = {rule.made} +
        Multiset.map (fun occurrence : O => occurrence) (s.present \ lent).val := target
    rw [made, carried, after_owned_val (firingOf s rule) absent lentIn]
    rfl

/-- A set of present identities stays present after a helper firing. -/
theorem lent_stays {s : State S O} (f : Firing s) {lent : Finset O} (lentIn : lent ⊆ s.present) :
    lent ⊆ f.after.present := fun occurrence member => by
  rw [after_present]
  exact Finset.mem_insert_of_mem (lentIn member)

/-- **A helper run is a run under any set of present identities as lent zone.** -/
theorem runUnder_lent_of_run : ∀ {s : State S O} (run : helperStep.Run s) (lent : Finset O),
    lent ⊆ s.present →
    (helperZoned S O).RunUnder s.frame lent.val (solutions (Frames.contextual S) s.knowledge)
      (s.present \ lent).val (usesOf run) run.last.frame (alongOf run)
      (solutions (Frames.contextual S) run.last.knowledge) (run.last.present \ lent).val
  | _, .nil s, _, _ => KnowledgeTensor.ZonedSystem.RunUnder.done _ _ _ _
  | s, .cons f allowed rest, lent, lentIn => by
      have later := runUnder_lent_of_run rest lent (lent_stays f lentIn)
      have carried : Multiset.map (fun occurrence : O => occurrence) lent.val = lent.val :=
        Multiset.map_id' _
      have later' : (helperZoned S O).RunUnder (extend s.frame f.helper)
          (Multiset.map (fun occurrence : O => occurrence) lent.val)
          (solutions (Frames.contextual S) f.information) (f.after.present \ lent).val
          (usesOf rest) rest.last.frame (alongOf rest)
          (solutions (Frames.contextual S) rest.last.knowledge) (rest.last.present \ lent).val :=
        carried.symm ▸ later
      exact KnowledgeTensor.ZonedSystem.RunUnder.fire
        (firesUnder_lent_of_admits f allowed lentIn) later'

/-- **A run under a lent zone from a helper state that ends in consistent knowledge is a helper
run.** -/
theorem run_of_runUnder_lent : ∀ (uses : List (Sigma (Rule S O))) {s : State S O}
    {lent : Finset O} {last : Frames.Frame S} {along : FrameMap S s.frame last}
    {reached : Known S last} {left : Multiset O}, lent ⊆ s.present →
    (helperZoned S O).RunUnder s.frame lent.val (solutions (Frames.contextual S) s.knowledge)
      (s.present \ lent).val uses last along reached left → reached.Nonempty →
      ∃ run : helperStep.Run s, usesOf run = uses ∧
        (Frames.contextual S).Solvable run.last.knowledge
  | [], s, _, _, _, _, _, _, zoned, consistent => by
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines zoned
      have start := knowAlong_nonempty S _ _ (consistent.mono refined)
      exact ⟨.nil s, rfl, (solvable_iff_nonempty _).mpr start⟩
  | use :: rest, s, lent, _, _, _, _, lentIn, zoned, consistent => by
      obtain ⟨declaration, middle, held, onward, rfl, rfl, fires, later⟩ :=
        KnowledgeTensor.ZonedSystem.RunUnder.cons_inv zoned
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines later
      have between : middle.Nonempty := knowAlong_nonempty S onward middle (consistent.mono refined)
      obtain ⟨allowed, reaches, holds⟩ :=
        admits_of_firesUnder_lent s declaration lentIn fires between
      subst reaches
      subst holds
      have carried : (helperZoned S O).carried
          ((helperZoned S O).extend (a := s.frame) declaration) lent.val = lent.val :=
        Multiset.map_id' _
      have later' : (helperZoned S O).RunUnder (firingOf s declaration).after.frame lent.val
          (solutions (Frames.contextual S) (firingOf s declaration).after.knowledge)
          ((firingOf s declaration).after.present \ lent).val rest _ onward _ _ := carried ▸ later
      obtain ⟨run, word, solvable⟩ :=
        run_of_runUnder_lent rest (lent_stays (firingOf s declaration) lentIn) later' consistent
      exact ⟨.cons (firingOf s declaration) allowed run, congrArg (List.cons _) word, solvable⟩

/-- **Every set of present identities may be lent to a helper run.** Helper runs with given uses
that end in consistent knowledge are exactly the graded proofs under that set as lent zone, from
the remaining identities. -/
theorem helper_lent_run_iff_zoned_proof (s : State S O) (lent : Finset O)
    (lentIn : lent ⊆ s.present) (uses : List (Sigma (Rule S O))) :
    (∃ run : helperStep.Run s, usesOf run = uses ∧
        (Frames.contextual S).Solvable run.last.knowledge) ↔
      ∃ (last : Frames.Frame S) (along : FrameMap S s.frame last)
        (reached : Known S last) (left : Multiset O) (grade : Multiset O → Prop),
        grade 0 ∧
          (helperZoned S O).Proves s.frame lent.val (solutions (Frames.contextual S) s.knowledge)
            (s.present \ lent).val grade uses last along reached left ∧ reached.Nonempty := by
  constructor
  · rintro ⟨run, rfl, solvable⟩
    obtain ⟨grade, atZero, proof⟩ :=
      KnowledgeTensor.ZonedSystem.RunUnder.proves (runUnder_lent_of_run run lent lentIn)
    exact ⟨_, _, _, _, grade, atZero, proof, (solvable_iff_nonempty _).mp solvable⟩
  · rintro ⟨last, along, reached, left, grade, atZero, proof, consistent⟩
    have zoned := KnowledgeTensor.ZonedSystem.Proves.run proof 0 atZero
    rw [add_zero] at zoned
    exact run_of_runUnder_lent uses lentIn zoned consistent

/-- **The context of a placement is a lent zone, over the frames.** A local helper run whose
grade admits a placement beside a context has a placed native run that is a graded proof at the
frame of the placement: it owns the identities of its own state, has the other identities of the
context lent, and starts from the meet of the two knowledges, each transported along its own
frame map. -/
theorem helper_checks_gives_lent_proof {left right : State S O}
    (placed : Helpers.ContextPlacement left right) (run : helperStep.Run left)
    (checked : Helpers.contextualRunInterpretation.Checks placed run) :
    ∃ native : helperStep.Run placed.state,
      Places Helpers.contextualRunInterpretation placed run native ∧
      ∃ grade : Multiset O → Prop, grade 0 ∧
        (helperZoned S O).Proves placed.frame (right.present \ left.present).val
          (pull (Frames.contextual S) placed.leftMap
              (solutions (Frames.contextual S) left.knowledge) ⊓
            pull (Frames.contextual S) placed.rightMap
              (solutions (Frames.contextual S) right.knowledge))
          left.present.val grade (usesOf native) native.last.frame (alongOf native)
          (solutions (Frames.contextual S) native.last.knowledge)
          (native.last.present \ (right.present \ left.present)).val := by
  obtain ⟨native, placedRun, _⟩ :=
    placed_run_of_checks Helpers.contextualRunInterpretation placed run checked
  have zoned := runUnder_lent_of_run (s := placed.state) native (right.present \ left.present)
    (fun occurrence member => Finset.mem_union_right _ (Finset.mem_sdiff.mp member).1)
  have owned : placed.state.present \ (right.present \ left.present) = left.present := by
    show (left.present ∪ right.present) \ (right.present \ left.present) = left.present
    ext occurrence
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨here | there, outside⟩
      · exact here
      · by_contra absent
        exact outside ⟨there, absent⟩
    · intro here
      exact ⟨Or.inl here, fun both => both.2 here⟩
  have known : solutions (Frames.contextual S) placed.state.knowledge =
      pull (Frames.contextual S) placed.leftMap (solutions (Frames.contextual S) left.knowledge) ⊓
        pull (Frames.contextual S) placed.rightMap
          (solutions (Frames.contextual S) right.knowledge) := by
    show solutions (Frames.contextual S)
      ((Frames.contextual S).applyStore placed.leftMap left.knowledge ++
        (Frames.contextual S).applyStore placed.rightMap right.knowledge) = _
    rw [solutions_append, solutions_applyStore, solutions_applyStore]
  rw [owned, known] at zoned
  obtain ⟨grade, atZero, proof⟩ := KnowledgeTensor.ZonedSystem.RunUnder.proves zoned
  exact ⟨native, placedRun, grade, atZero, proof⟩

/-- Every helper run is a graded proof over the frames whose grade admits the empty extra
context. -/
theorem helper_run_is_zoned_proof {s : State S O} (run : helperStep.Run s) :
    ∃ grade : Multiset O → Prop, grade 0 ∧
      (helperZoned S O).Proves s.frame 0 (solutions (Frames.contextual S) s.knowledge)
        s.present.val grade (usesOf run) run.last.frame (alongOf run)
        (solutions (Frames.contextual S) run.last.knowledge) run.last.present.val :=
  KnowledgeTensor.ZonedSystem.RunUnder.proves (runUnder_of_run run)

/-- The uses of a helper run are as many as its firings. -/
theorem usesOf_length : ∀ {s : State S O} (run : helperStep.Run s),
    (usesOf run).length = run.word.length
  | _, .nil _ => rfl
  | _, .cons _ _ rest => congrArg Nat.succ (usesOf_length rest)

/-- The knowledge of a placed state is the meet of the two knowledges, each transported along
its own frame map. -/
theorem placed_knowledge {left right : State S O} (placed : Helpers.ContextPlacement left right) :
    solutions (Frames.contextual S) placed.state.knowledge =
      pull (Frames.contextual S) placed.leftMap (solutions (Frames.contextual S) left.knowledge) ⊓
        pull (Frames.contextual S) placed.rightMap
          (solutions (Frames.contextual S) right.knowledge) := by
  show solutions (Frames.contextual S)
    ((Frames.contextual S).applyStore placed.leftMap left.knowledge ++
      (Frames.contextual S).applyStore placed.rightMap right.knowledge) = _
  rw [solutions_append, solutions_applyStore, solutions_applyStore]

/-- **The native tensor of two helper runs is a graded proof of the tensor sequent, over the
frames.** It starts at the frame of the placement from the meet of the two knowledges, each
transported along its own frame map, and from the identities of both states; it has as many
uses as the two runs together. -/
theorem helper_tensor_is_zoned_proof {left right : State S O}
    {placed : Helpers.ContextPlacement left right} {first : helperStep.Run left}
    {second : helperStep.Run right} (plan : Helpers.TensorPlan placed first second) :
    ∃ grade : Multiset O → Prop, grade 0 ∧
      (helperZoned S O).Proves placed.frame 0
        (pull (Frames.contextual S) placed.leftMap
            (solutions (Frames.contextual S) left.knowledge) ⊓
          pull (Frames.contextual S) placed.rightMap
            (solutions (Frames.contextual S) right.knowledge))
        (left.present ∪ right.present).val grade
        (usesOf (Helpers.TensorPlan.realize plan).execution)
        (Helpers.TensorPlan.realize plan).execution.last.frame
        (alongOf (Helpers.TensorPlan.realize plan).execution)
        (solutions (Frames.contextual S) (Helpers.TensorPlan.realize plan).execution.last.knowledge)
        (Helpers.TensorPlan.realize plan).execution.last.present.val ∧
      (usesOf (Helpers.TensorPlan.realize plan).execution).length =
        first.word.length + second.word.length := by
  obtain ⟨grade, atZero, proof⟩ :=
    helper_run_is_zoned_proof (s := placed.state) (Helpers.TensorPlan.realize plan).execution
  rw [placed_knowledge] at proof
  exact ⟨grade, atZero, proof,
    (usesOf_length _).trans (Helpers.TensorPlan.realize plan).length_preserved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.HelperZoned
