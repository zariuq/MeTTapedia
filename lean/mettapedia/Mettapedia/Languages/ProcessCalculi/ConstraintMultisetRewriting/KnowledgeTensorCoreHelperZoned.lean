import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreHelpers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreKnowledge
import Mettapedia.Logic.LinearLogic.KnowledgeTensorInitial
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The binding-aware helper step: runs are zoned proofs over the frames

The helper step lives over the declaration frames with contextual assignments. A firing makes one
occurrence and one fresh helper: it extends the frame by the helper, tells the helper's value
there, and is guarded by equations on the old names.

Read on the zones:

* the frames are the declaration frames, and a frame map is a path of contextual assignments;
* knowledge at a frame is a set of solutions, transported by inverse image;
* the atoms are the occurrence identities, carried unchanged;
* a declared transition at a frame is the data of a firing: it takes and reads nothing, makes its
  occurrence, moves along the inclusion of the old names, tells the helper's equation, is guarded
  by its equations and checks that its occurrence is not present.

## Results

* `firesUnder_of_admits`, `admits_of_firesUnder`: an admitted helper firing is a firing of the
  zoned transition, and conversely when the knowledge it reaches is consistent.
* `runUnder_of_run`, `run_of_runUnder`: the same for runs, with the same uses.
* `helper_run_iff_zoned_proof`: **runs of the helper step that end in consistent knowledge are
  exactly the graded proofs of the zoned calculus over the frames** whose grade admits the empty
  extra context and whose final knowledge is consistent, with the same uses in the same order.
* `a_leaf_refuses_its_own_occurrence`: the grade of a leaf excludes every context that holds the
  occurrence it makes; `a_leaf_admits_the_empty_context`: it admits the empty one.
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

variable (S : Signature)

/-- The declaration frames, as the objects of the quiver of contextual assignments. -/
def FrameObject := Frames.Frame S

instance frameQuiver : Quiver (FrameObject S) where
  Hom := fun F G : Frames.Frame S => Assignment F.arity G.arity

/-- A frame map: a path of contextual assignments. -/
abbrev FrameMap (F G : Frames.Frame S) := @Quiver.Path (FrameObject S) _ F G

/-- Knowledge at a frame: a set of solutions in later frames. -/
abbrev Known (F : Frames.Frame S) : Type 1 :=
  Set (Frames.Solution (fun F G : Frames.Frame S => Assignment F.arity G.arity) F)

/-- Transport of knowledge along a frame map. -/
noncomputable def knowAlong {F G : Frames.Frame S} (path : FrameMap S F G) (known : Known S F) :
    Known S G :=
  @Quiver.Path.rec (FrameObject S) _ F (fun G _ => Known S G) known
    (fun _ arrow earlier => pull (Frames.contextual S) arrow earlier) G path

theorem knowAlong_nil {F : Frames.Frame S} (known : Known S F) :
    knowAlong S (Quiver.Path.nil : FrameMap S F F) known = known :=
  rfl

theorem knowAlong_cons {F G H : Frames.Frame S} (path : FrameMap S F G)
    (arrow : Assignment G.arity H.arity) (known : Known S F) :
    knowAlong S (Quiver.Path.cons path arrow : FrameMap S F H) known =
      pull (Frames.contextual S) arrow (knowAlong S path known) :=
  rfl

theorem knowAlong_comp {F G H : Frames.Frame S} (first : FrameMap S F G)
    (second : FrameMap S G H) (known : Known S F) :
    knowAlong S (Quiver.Path.comp first second : FrameMap S F H) known =
      knowAlong S second (knowAlong S first known) := by
  induction second with
  | nil => rfl
  | cons path arrow ih =>
      rw [Quiver.Path.comp_cons, knowAlong_cons, knowAlong_cons, ih]

theorem knowAlong_inf {F G : Frames.Frame S} (path : FrameMap S F G) (one two : Known S F) :
    knowAlong S path (one ⊓ two) = knowAlong S path one ⊓ knowAlong S path two := by
  induction path with
  | nil => rfl
  | cons path arrow ih =>
      rw [knowAlong_cons, knowAlong_cons, knowAlong_cons, ih]
      rfl

theorem knowAlong_nonempty {F G : Frames.Frame S} (path : FrameMap S F G) (known : Known S F)
    (nonempty : (knowAlong S path known).Nonempty) : known.Nonempty := by
  induction path with
  | nil => exact nonempty
  | cons path arrow ih =>
      obtain ⟨solution, member⟩ := nonempty
      rw [knowAlong_cons] at member
      exact ih ⟨_, member⟩

variable (O : Type) [DecidableEq O]

/-- A declared transition at a frame: the data of a helper firing. -/
abbrev Rule (F : Frames.Frame S) : Type := Firing (S := S) (O := O) ⟨F, [], ∅⟩

variable {S O}

/-- The declared transition a firing uses. -/
def ruleOf {s : State S O} (f : Firing s) : Rule S O s.frame :=
  ⟨f.made, f.helper, f.value, f.guards⟩

/-- A declared transition, as a firing at a state of its frame. -/
def firingOf (s : State S O) (rule : Rule S O s.frame) : Firing s :=
  ⟨rule.made, rule.helper, rule.value, rule.guards⟩

variable (S O)

/-- **The helper step as declared transitions over the frames.** -/
noncomputable abbrev helperZoned :
    KnowledgeTensor.ZonedSystem (Paths (FrameObject S)) (Known S) (fun _ => O) (Rule S O) where
  know := fun path known => knowAlong S path known
  know_id := fun _ => rfl
  know_comp := fun first second known => knowAlong_comp S first second known
  know_inf := fun path one two => knowAlong_inf S path one two
  carry := fun _ occurrence => occurrence
  carry_id := fun _ => rfl
  carry_comp := fun _ _ _ => rfl
  target := fun {F} rule => extend F rule.helper
  extend := fun {F} rule => Quiver.Hom.toPath (incl F rule.helper)
  take := fun _ => 0
  read := fun _ => 0
  make := fun rule => {rule.made}
  tell := fun rule => solutions (Frames.contextual S) [rule.tell]
  guard := fun {F} rule known => ∀ solution ∈ known,
    (Frames.contextual S).Models (Assignment.compose solution.2 (incl F rule.helper)) rule.guards
  guard_mono := fun _ _ _ refines holds solution member => holds solution (refines member)
  check := fun rule _ rest => rule.made ∉ rest
  check_mono := fun _ _ _ _ _ holds => holds

variable {S O}

/-- The present occurrences after a helper firing. -/
theorem after_present_val {s : State S O} (f : Firing s) (absent : f.made ∉ s.present) :
    f.after.present.val = {f.made} + s.present.val := by
  have same : fire s.present (f.selection.commit (T := Unit)) = insert f.made s.present := by
    ext occurrence
    rw [mem_fire]
    simp [Firing.selection, Selection.commit, or_comm]
  show (fire s.present (f.selection.commit (T := Unit))).val = _
  rw [same, Finset.insert_val_of_notMem absent, Multiset.singleton_add]

omit [DecidableEq O] in
/-- The knowledge a helper firing reaches, on the zones. -/
theorem solutions_information {s : State S O} (f : Firing s) :
    solutions (Frames.contextual S) f.information =
      pull (Frames.contextual S) (incl s.frame f.helper)
        (solutions (Frames.contextual S) s.knowledge) ⊓
        solutions (Frames.contextual S) [f.tell] := by
  show solutions (Frames.contextual S)
    ((Frames.contextual S).applyStore (incl s.frame f.helper) s.knowledge ++ [f.tell]) = _
  rw [solutions_append, solutions_applyStore]

/-- **An admitted helper firing is a firing of the zoned transition.** -/
theorem firesUnder_of_admits {s : State S O} (f : Firing s) (allowed : helperStep.Admits f) :
    (helperZoned S O).FiresUnder (a := s.frame) 0 (ruleOf f)
      (solutions (Frames.contextual S) s.knowledge) s.present.val
      (solutions (Frames.contextual S) f.information) f.after.present.val := by
  have absent : f.made ∉ s.present := (Helpers.enabled_iff f).mp allowed.2.1
  refine ⟨s.present.val, (zero_add _).symm, Multiset.zero_le _, ?_, ?_,
    solutions_information f, ?_⟩
  · intro solution member
    have solved : (Frames.contextual S).Models solution.2 f.information := by
      have inside : solution ∈ solutions (Frames.contextual S) f.information :=
        (solutions_information f).symm ▸ member
      exact inside
    exact allowed.2.2.2 solution.1 solution.2 solved
  · intro member
    have present : f.made ∈ s.present.val + 0 := member
    rw [add_zero] at present
    exact absent (Finset.mem_val.mp present)
  · have carried : Multiset.map (fun occurrence : O => occurrence) s.present.val = s.present.val :=
      Multiset.map_id' _
    show f.after.present.val =
      {f.made} + Multiset.map (fun occurrence : O => occurrence) s.present.val
    rw [carried, after_present_val f absent]

/-- **A firing of the zoned transition that reaches consistent knowledge is an admitted helper
firing.** -/
theorem admits_of_firesUnder (s : State S O) (rule : Rule S O s.frame)
    {reached : Known S (extend s.frame rule.helper)} {left : Multiset O}
    (fires : (helperZoned S O).FiresUnder (a := s.frame) 0 rule
      (solutions (Frames.contextual S) s.knowledge) s.present.val reached left)
    (consistent : reached.Nonempty) :
    helperStep.Admits (firingOf s rule) ∧
      reached = solutions (Frames.contextual S) (firingOf s rule).information ∧
      left = (firingOf s rule).after.present.val := by
  obtain ⟨frame, source, _, asked, checked, knowledge, target⟩ := fires
  have sourced : s.present.val = 0 + frame := source
  have whole : frame = s.present.val := (zero_add frame).symm.trans sourced.symm
  subst whole
  have fresh : rule.made ∉ s.present.val + 0 := checked
  have absent : (firingOf s rule).made ∉ s.present := fun present =>
    fresh ((add_zero s.present.val).symm ▸ Finset.mem_val.mpr present)
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
  · have carried : Multiset.map (fun occurrence : O => occurrence) s.present.val = s.present.val :=
      Multiset.map_id' _
    have made : left = {rule.made} + Multiset.map (fun occurrence : O => occurrence) s.present.val :=
      target
    rw [made, carried, after_present_val (firingOf s rule) absent]
    rfl

/-- The uses of a helper run: its firings as declared transitions at their frames. -/
def usesOf : ∀ {s : State S O}, helperStep.Run s → List (Sigma (Rule S O))
  | _, .nil _ => []
  | s, .cons f _ rest => ⟨s.frame, ruleOf f⟩ :: usesOf rest

/-- The frame map of a helper run: the path of its inclusions. -/
def alongOf : ∀ {s : State S O} (run : helperStep.Run s), FrameMap S s.frame run.last.frame
  | _, .nil _ => Quiver.Path.nil
  | s, .cons f _ rest =>
      Quiver.Path.comp (Quiver.Hom.toPath (V := FrameObject S) (incl s.frame f.helper)) (alongOf rest)

/-- **A helper run is a run of the zoned calculus**, with the same uses, over its frame map. -/
theorem runUnder_of_run : ∀ {s : State S O} (run : helperStep.Run s),
    (helperZoned S O).RunUnder s.frame 0 (solutions (Frames.contextual S) s.knowledge)
      s.present.val (usesOf run) run.last.frame (alongOf run)
      (solutions (Frames.contextual S) run.last.knowledge) run.last.present.val
  | _, .nil s => KnowledgeTensor.ZonedSystem.RunUnder.done _ _ _ _
  | s, .cons f allowed rest => by
      have later := runUnder_of_run rest
      have carried : Multiset.map (fun occurrence : O => occurrence) (0 : Multiset O) = 0 :=
        Multiset.map_zero _
      have later' : (helperZoned S O).RunUnder (extend s.frame f.helper)
          (Multiset.map (fun occurrence : O => occurrence) (0 : Multiset O))
          (solutions (Frames.contextual S) f.information) f.after.present.val (usesOf rest)
          rest.last.frame (alongOf rest) (solutions (Frames.contextual S) rest.last.knowledge)
          rest.last.present.val := carried.symm ▸ later
      exact KnowledgeTensor.ZonedSystem.RunUnder.fire (firesUnder_of_admits f allowed) later'

/-- **A run of the zoned calculus from a helper state that ends in consistent knowledge is a
helper run**, with the same uses, ending in consistent knowledge. -/
theorem run_of_runUnder : ∀ (uses : List (Sigma (Rule S O))) {s : State S O}
    {last : Frames.Frame S} {along : FrameMap S s.frame last}
    {reached : Known S last} {left : Multiset O},
    (helperZoned S O).RunUnder s.frame 0 (solutions (Frames.contextual S) s.knowledge)
      s.present.val uses last along reached left → reached.Nonempty →
      ∃ run : helperStep.Run s, usesOf run = uses ∧
        (Frames.contextual S).Solvable run.last.knowledge
  | [], s, _, _, _, _, zoned, consistent => by
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines zoned
      have start := knowAlong_nonempty S _ _ (consistent.mono refined)
      exact ⟨.nil s, rfl, (solvable_iff_nonempty _).mpr start⟩
  | use :: rest, s, _, _, _, _, zoned, consistent => by
      obtain ⟨declaration, middle, held, onward, rfl, rfl, fires, later⟩ :=
        KnowledgeTensor.ZonedSystem.RunUnder.cons_inv zoned
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines later
      have between : middle.Nonempty := knowAlong_nonempty S onward middle (consistent.mono refined)
      obtain ⟨allowed, reaches, holds⟩ := admits_of_firesUnder s declaration fires between
      subst reaches
      subst holds
      have carried : Multiset.map (fun occurrence : O => occurrence) (0 : Multiset O) = 0 :=
        Multiset.map_zero _
      have later' : (helperZoned S O).RunUnder (firingOf s declaration).after.frame 0
          (solutions (Frames.contextual S) (firingOf s declaration).after.knowledge)
          (firingOf s declaration).after.present.val rest _ onward _ _ := carried ▸ later
      obtain ⟨run, word, solvable⟩ := run_of_runUnder rest later' consistent
      exact ⟨.cons (firingOf s declaration) allowed run, congrArg (List.cons _) word, solvable⟩

/-- **Runs of the binding-aware helper step are zoned proofs over the frames.** A helper run with
given uses that ends in consistent knowledge exists exactly when a graded proof exists, from the
reading of the state, whose grade admits the empty extra context and whose final knowledge is
consistent. -/
theorem helper_run_iff_zoned_proof (s : State S O) (uses : List (Sigma (Rule S O))) :
    (∃ run : helperStep.Run s, usesOf run = uses ∧
        (Frames.contextual S).Solvable run.last.knowledge) ↔
      ∃ (last : Frames.Frame S) (along : FrameMap S s.frame last)
        (reached : Known S last) (left : Multiset O) (grade : Multiset O → Prop),
        grade 0 ∧
          (helperZoned S O).Proves s.frame 0 (solutions (Frames.contextual S) s.knowledge)
            s.present.val grade uses last along reached left ∧ reached.Nonempty := by
  constructor
  · rintro ⟨run, rfl, solvable⟩
    obtain ⟨grade, atZero, proof⟩ :=
      KnowledgeTensor.ZonedSystem.RunUnder.proves (runUnder_of_run run)
    exact ⟨_, _, _, _, grade, atZero, proof, (solvable_iff_nonempty _).mp solvable⟩
  · rintro ⟨last, along, reached, left, grade, atZero, proof, consistent⟩
    have zoned := KnowledgeTensor.ZonedSystem.Proves.run proof 0 atZero
    rw [add_zero] at zoned
    exact run_of_runUnder uses zoned consistent

/-! ## Controls -/

omit [DecidableEq O] in
/-- The grade of a leaf excludes every extra context that holds the occurrence it makes. -/
theorem a_leaf_refuses_its_own_occurrence {F : Frames.Frame S} (rule : Rule S O F)
    (extra : Multiset O) (holds : rule.made ∈ extra) : ¬ rule.made ∉ (0 : Multiset O) + extra :=
  fun fresh => fresh (Multiset.mem_add.mpr (Or.inr holds))

omit [DecidableEq O] in
/-- The grade of a leaf admits the empty extra context. -/
theorem a_leaf_admits_the_empty_context {F : Frames.Frame S} (rule : Rule S O F) :
    rule.made ∉ (0 : Multiset O) + 0 :=
  fun member => by
    rw [add_zero] at member
    exact absurd member (Multiset.notMem_zero _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.HelperZoned
