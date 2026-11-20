import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketQueryView

/-!
# Own and pair cuts keep the full packet image and original position tags

Only the selected members contribute equations. The other members' row
closures remain in the same label map, but no model of their information is
required. A pair uses distinct original positions, including when the two
member values happen to be equal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketQueryCuts

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled)
open TaggedAssignments (Substitution)
open ContextPackets (Environment)
open NativePacketStep (Terms Ports packetAction)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

def memberProblem {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :=
  (NativePacketStep.selection members[index]).problem (NativePacketRounds.label members)
    (NativePacketStep.body members[index] (NativePacketRounds.useTag index)) (NativePacketStep.configuration s 0)

def pairProblem {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (first second : Fin members.length) :=
  AnnotatedRuns.pairCut (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
    (NativePacketStep.baseFiring members[first] (NativePacketRounds.useTag first))
    (NativePacketStep.baseFiring members[second] (NativePacketRounds.useTag second))

theorem member_models_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (substitution : Substitution S) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (memberProblem members index) ↔
      ContextualResidual.Models (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
        (FamilyInformation.memberInformation members[index]) ∧
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
        (NativePacketStep.captureRow s (NativePacketRounds.useTag index),
          ContextPackets.anchor (NativePacketStep.baseObject s 0)) := by
  constructor
  · intro model
    have pieces := model
    simp only [memberProblem,Selection.problem,SubstitutionAction.models_append] at pieces
    refine ⟨(ContextPackets.models_problem substitution _ _).mp pieces.2,?_⟩
    have read := pieces.1.2
    change (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (Selection.equations (NativePacketRounds.label members)
        (members[index].selection.read.map (NativePacketStep.readRow s (NativePacketRounds.useTag index)) ++
          [NativePacketStep.captureRow s (NativePacketRounds.useTag index)])
        (members[index].selection.read.map Sum.inl ++ [.inr ()])) at read
    unfold Selection.equations at read
    rw [List.zipWith_append (by simp)] at read
    exact ((SubstitutionAction.models_append _ _ _ _).mp read).2 _ List.mem_cons_self
  · rintro ⟨nativeModel,captured⟩
    have rowSolved (occurrence : O) (selected : occurrence ∈ members[index].selection.taken ++ members[index].selection.read) :
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
          (NativePacketStep.readRow s (NativePacketRounds.useTag index) occurrence,
            NativePacketRounds.label members (.inl occurrence)) := by
      have present : occurrence ∈ s.state.present := by
        rcases List.mem_append.mp selected with taken | read
        · exact enabled.taken_subset (List.mem_toFinset.mpr taken)
        · exact enabled.kept_subset (List.mem_toFinset.mpr read)
      rw [NativePacketRounds.label_old members occurrence present]
      exact NativePacketStep.read_row_solved s 0 (NativePacketRounds.useTag index) substitution captured occurrence
    simp only [memberProblem,Selection.problem,SubstitutionAction.models_append]
    refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
    · apply (ContextPackets.models_problem substitution (NativePacketStep.baseObject s 0) s.state.equations).mpr
      have known := ((NativeResidual.models_problemOf_iff members[index].selection members[index].rule
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2).mp nativeModel).1
      have same := (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
        (target := NativePacketStep.useObject s (NativePacketRounds.useTag index))
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution).mp captured
      have carried := NativePacketRounds.retarget_models
        (domain := (NativePacketStep.baseObject s 0).2) (congrArg Environment.target same)
        (Assignment.compose (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
          (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)) s.state.equations known
      rw [NativePacketRounds.retarget_environment same] at carried
      exact carried
    · apply (Selection.models_equations_iff _ _ _ (by simp [NativePacketStep.body,NativePacketStep.selection])).mpr
      change List.Forall₂ _
        (members[index].selection.taken.map (NativePacketStep.readRow s (NativePacketRounds.useTag index)))
        (members[index].selection.taken.map Sum.inl)
      rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
      exact fun occurrence member => rowSolved occurrence (List.mem_append_left _ member)
    · change (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        (Selection.equations (NativePacketRounds.label members)
          (members[index].selection.read.map (NativePacketStep.readRow s (NativePacketRounds.useTag index)) ++
            [NativePacketStep.captureRow s (NativePacketRounds.useTag index)])
          (members[index].selection.read.map Sum.inl ++ [.inr ()]))
      unfold Selection.equations
      rw [List.zipWith_append (by simp),SubstitutionAction.models_append]
      refine ⟨?_,?_⟩
      · apply (Selection.models_equations_iff _ _ _ (by simp)).mpr
        rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
        exact fun occurrence member => rowSolved occurrence (List.mem_append_right _ member)
      · intro equation member
        have same := List.mem_singleton.mp member
        subst equation
        exact captured
    · exact (ContextPackets.models_problem substitution _ _).mpr nativeModel

theorem pair_models_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (substitution : Substitution S) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (pairProblem members first second) ↔
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (memberProblem members first) ∧
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (memberProblem members second) := by
  simp only [pairProblem,memberProblem,AnnotatedRuns.pairCut,AnnotatedRuns.Firing.added,
    NativePacketStep.baseFiring,AnnotatedRuns.Firing.ofPlain,GuardFreeProcessOrders.problem_eq,
    SubstitutionAction.models_append]
  tauto

noncomputable def pairFit {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (_different : first ≠ second) (target : Frames.Frame S)
    (data : FamilyInformation.SolutionData s [members[first],members[second]] target) : Substitution S := by
  classical
  exact NativePacketRounds.patch s members.length ⟨(0,target),data.shared⟩ (fun index =>
    if index = first then ⟨(0,target),data.member 0⟩ else
    if index = second then ⟨(0,target),data.member 1⟩ else
      ⟨NativePacketStep.useObject s (NativePacketRounds.useTag index),generator s.infoFrame.arity⟩)

omit [DecidableEq O] in
theorem pairFit_base {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second) (target : Frames.Frame S)
    (data : FamilyInformation.SolutionData s [members[first],members[second]] target) :
    pairFit members first second different target data (NativePacketStep.baseObject s 0) = ⟨(0,target),data.shared⟩ :=
  NativePacketRounds.patch_base s _ _ _

omit [DecidableEq O] in
theorem pairFit_first {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second) (target : Frames.Frame S)
    (data : FamilyInformation.SolutionData s [members[first],members[second]] target) :
    pairFit members first second different target data (NativePacketStep.useObject s (NativePacketRounds.useTag first)) =
      ⟨(0,target),data.member 0⟩ := by
  classical
  unfold pairFit
  rw [NativePacketRounds.patch_use]
  simp only [if_true]
  rfl

omit [DecidableEq O] in
theorem pairFit_second {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second) (target : Frames.Frame S)
    (data : FamilyInformation.SolutionData s [members[first],members[second]] target) :
    pairFit members first second different target data (NativePacketStep.useObject s (NativePacketRounds.useTag second)) =
      ⟨(0,target),data.member 1⟩ := by
  classical
  unfold pairFit
  rw [NativePacketRounds.patch_use]
  simp only [if_neg different.symm,if_true]
  rfl

theorem pairFit_model {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (target : Frames.Frame S) (data : FamilyInformation.SolutionData s [members[first],members[second]] target) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models (pairFit members first second different target data)
      (pairProblem members first second) := by
  apply (pair_models_iff members first second _).mpr
  constructor
  · apply (member_models_iff members first firstEnabled _).mpr
    refine ⟨?_,?_⟩
    · rw [pairFit_first]
      exact data.models 0
    · apply (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
        (target := NativePacketStep.useObject s (NativePacketRounds.useTag first))
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) _).mpr
      rw [pairFit_base,pairFit_first]
      exact congrArg (Environment.mk (NativePacketStep.baseObject s 0).2 (0,target)) (data.agrees 0)
  · apply (member_models_iff members second secondEnabled _).mpr
    refine ⟨?_,?_⟩
    · rw [pairFit_second members first second different]
      exact data.models 1
    · apply (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
        (target := NativePacketStep.useObject s (NativePacketRounds.useTag second))
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) _).mpr
      rw [pairFit_base,pairFit_second members first second different]
      exact congrArg (Environment.mk (NativePacketStep.baseObject s 0).2 (0,target)) (data.agrees 1)

noncomputable def readPair {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (_different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (pairProblem members first second)) :
    FamilyInformation.SolutionData s [members[first],members[second]]
      (substitution (NativePacketStep.baseObject s 0)).1.2 := by
  have pair := (pair_models_iff members first second substitution).mp model
  have left := (member_models_iff members first firstEnabled substitution).mp pair.1
  have right := (member_models_iff members second secondEnabled substitution).mp pair.2
  let leftSame := (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
    (target := NativePacketStep.useObject s (NativePacketRounds.useTag first))
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution).mp left.2
  let rightSame := (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
    (target := NativePacketStep.useObject s (NativePacketRounds.useTag second))
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution).mp right.2
  refine
    { shared := (substitution (NativePacketStep.baseObject s 0)).2
      member := fun index => if index.val = 0 then
        NativePacketRounds.retarget (congrArg Environment.target leftSame)
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag first))).2
        else NativePacketRounds.retarget (congrArg Environment.target rightSame)
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag second))).2
      models := ?_
      agrees := ?_ }
  · intro index
    fin_cases index
    · dsimp only
      exact (NativePacketRounds.retarget_compose (domain := s.infoFrame)
        (inputs := (NativePacketStep.baseObject s 0).2) (congrArg Environment.target leftSame)
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag first))).2
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)).trans
          (NativePacketRounds.retarget_environment leftSame)
    · dsimp only
      exact (NativePacketRounds.retarget_compose (domain := s.infoFrame)
        (inputs := (NativePacketStep.baseObject s 0).2) (congrArg Environment.target rightSame)
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag second))).2
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)).trans
          (NativePacketRounds.retarget_environment rightSame)
  · intro index
    fin_cases index
    · dsimp only
      exact NativePacketRounds.retarget_models (domain := s.infoFrame) (congrArg Environment.target leftSame)
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag first))).2 _ left.1
    · dsimp only
      exact NativePacketRounds.retarget_models (domain := s.infoFrame) (congrArg Environment.target rightSame)
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag second))).2 _ right.1

private theorem package_retarget {domain : Frames.Frame S} {first second : TaggedAssignments.Object S}
    (same : first = second) (candidate : Assignment domain.arity first.2.arity) :
    (⟨first,candidate⟩ : (target : TaggedAssignments.Object S) × Assignment domain.arity target.2.arity) =
      ⟨second,NativePacketRounds.retarget same candidate⟩ := by
  cases same
  rfl

theorem readPair_first_use {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (pairProblem members first second)) :
    substitution (NativePacketStep.useObject s (NativePacketRounds.useTag first)) =
      ⟨(substitution (NativePacketStep.baseObject s 0)).1,
        (readPair members first second different firstEnabled secondEnabled substitution model).member 0⟩ := by
  have captured := ((member_models_iff members first firstEnabled substitution).mp
    ((pair_models_iff members first second substitution).mp model).1).2
  exact package_retarget (domain := s.infoFrame)
    (ContextPackets.capture_targets (source := NativePacketStep.baseObject s 0)
      (target := NativePacketStep.useObject s (NativePacketRounds.useTag first))
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution captured)
    (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag first))).2

theorem readPair_second_use {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (pairProblem members first second)) :
    substitution (NativePacketStep.useObject s (NativePacketRounds.useTag second)) =
      ⟨(substitution (NativePacketStep.baseObject s 0)).1,
        (readPair members first second different firstEnabled secondEnabled substitution model).member 1⟩ := by
  have captured := ((member_models_iff members second secondEnabled substitution).mp
    ((pair_models_iff members first second substitution).mp model).2).2
  exact package_retarget (domain := s.infoFrame)
    (ContextPackets.capture_targets (source := NativePacketStep.baseObject s 0)
      (target := NativePacketStep.useObject s (NativePacketRounds.useTag second))
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution captured)
    (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag second))).2

theorem pair_region {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (pairProblem members first second)) (pattern : Term (signature S s.infoFrame.arity) Γ sort) :
    MeTTaCalculus.OccurrenceCommits.regionOf (NativePacketRounds.label members) (NativePacketStep.present s)
        (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern substitution) =
      (ContextualConditionalGuards.region s.locals
        ((readPair members first second different firstEnabled secondEnabled substitution model).member 0)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present pattern).image Sum.inl := by
  have captured := ((member_models_iff members first firstEnabled substitution).mp
    ((pair_models_iff members first second substitution).mp model).1).2
  have actual := NativePacketQueryView.source_region s 0 (NativePacketRounds.useTag first) pattern substitution
    (NativePacketRounds.label members) (NativePacketRounds.label_old members) rfl captured
  rw [readPair_first_use members first second different firstEnabled secondEnabled substitution model] at actual
  exact actual

theorem pairFit_region {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (target : Frames.Frame S) (data : FamilyInformation.SolutionData s [members[first],members[second]] target)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) :
    MeTTaCalculus.OccurrenceCommits.regionOf (NativePacketRounds.label members) (NativePacketStep.present s)
        (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern
          (pairFit members first second different target data)) =
      (ContextualConditionalGuards.region s.locals (data.member 0)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present pattern).image Sum.inl := by
  have model := pairFit_model members first second different firstEnabled secondEnabled target data
  have captured := ((member_models_iff members first firstEnabled _).mp
    ((pair_models_iff members first second _).mp model).1).2
  have actual := NativePacketQueryView.source_region s 0 (NativePacketRounds.useTag first) pattern _
    (NativePacketRounds.label members) (NativePacketRounds.label_old members) rfl captured
  rw [pairFit_first members first second different target data] at actual
  exact actual

theorem pair_count_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (number : Nat) :
    (NativePacketQueryView.countQuery (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern number).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (pairProblem members first second)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      ∀ (target : Frames.Frame S) (data : FamilyInformation.SolutionData s [members[first],members[second]] target),
        (ContextualConditionalGuards.region s.locals (data.member 0)
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern).card = number := by
  constructor
  · intro asked target data
    have actual := asked _ (pairFit_model members first second different firstEnabled secondEnabled target data)
    change (MeTTaCalculus.OccurrenceCommits.regionOf _ _
      (NativePacketQueryView.region _ _ _)).card = number at actual
    rw [pairFit_region members first second different firstEnabled secondEnabled target data pattern,
      Finset.card_image_of_injective _ Sum.inl_injective] at actual
    exact actual
  · intro asked substitution model
    have actual := asked _ (readPair members first second different firstEnabled secondEnabled substitution model)
    change (MeTTaCalculus.OccurrenceCommits.regionOf _ _
      (NativePacketQueryView.region _ _ _)).card = number
    rw [pair_region members first second different firstEnabled secondEnabled substitution model pattern,
      Finset.card_image_of_injective _ Sum.inl_injective]
    exact actual

theorem pair_exact_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (seen : Finset O) :
    (NativePacketQueryView.exactQuery (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern
      (seen.image Sum.inl)).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (pairProblem members first second)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      ∀ (target : Frames.Frame S) (data : FamilyInformation.SolutionData s [members[first],members[second]] target),
        ContextualConditionalGuards.region s.locals (data.member 0)
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern = seen := by
  constructor
  · intro asked target data
    have actual := asked _ (pairFit_model members first second different firstEnabled secondEnabled target data)
    change MeTTaCalculus.OccurrenceCommits.regionOf _ _ (NativePacketQueryView.region _ _ _) = seen.image Sum.inl at actual
    rw [pairFit_region members first second different firstEnabled secondEnabled target data pattern,
      Finset.image_inj Sum.inl_injective] at actual
    exact actual
  · intro asked substitution model
    have actual := asked _ (readPair members first second different firstEnabled secondEnabled substitution model)
    change MeTTaCalculus.OccurrenceCommits.regionOf _ _ (NativePacketQueryView.region _ _ _) = seen.image Sum.inl
    rw [pair_region members first second different firstEnabled secondEnabled substitution model pattern,
      Finset.image_inj Sum.inl_injective]
    exact actual

theorem pair_old_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (pairProblem members first second)) (pattern : Term (signature S s.infoFrame.arity) Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern substitution
        (NativePacketStep.oldRow s 0 occurrence) ↔
      ContextualConditionalRows.Matches s.locals s.infoFrame.arity
        ((readPair members first second different firstEnabled secondEnabled substitution model).member 0)
        (instantiate ((readPair members first second different firstEnabled secondEnabled substitution model).member 0) pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence) := by
  have captured := ((member_models_iff members first firstEnabled substitution).mp
    ((pair_models_iff members first second substitution).mp model).1).2
  have actual := NativePacketQueryView.rowMatches_old_iff s 0 (NativePacketRounds.useTag first)
    pattern substitution captured occurrence
  rw [readPair_first_use members first second different firstEnabled secondEnabled substitution model] at actual
  exact actual

theorem pair_output_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (pairProblem members first second)) (pattern : Term (signature S s.infoFrame.arity) Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern substitution
        (NativePacketStep.outputRow members[second] (NativePacketRounds.useTag second) occurrence) ↔
      instantiate ((readPair members first second different firstEnabled secondEnabled substitution model).member 0) pattern =
        instantiate ((readPair members first second different firstEnabled secondEnabled substitution model).member 1)
          (members[second].outputs occurrence) :=
  NativePacketQueryView.rowMatches_output_iff members[second] _ pattern (NativePacketRounds.useTag second) substitution
    (substitution (NativePacketStep.baseObject s 0)).1 _ _
    (readPair_first_use members first second different firstEnabled secondEnabled substitution model)
    (readPair_second_use members first second different firstEnabled secondEnabled substitution model) occurrence

omit [DecidableEq O] in
theorem pairFit_old_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second) (target : Frames.Frame S)
    (data : FamilyInformation.SolutionData s [members[first],members[second]] target)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern
        (pairFit members first second different target data) (NativePacketStep.oldRow s 0 occurrence) ↔
      ContextualConditionalRows.Matches s.locals s.infoFrame.arity (data.member 0) (instantiate (data.member 0) pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence) := by
  have captured : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves
      (pairFit members first second different target data)
      (NativePacketStep.captureRow s (NativePacketRounds.useTag first),ContextPackets.anchor (NativePacketStep.baseObject s 0)) := by
    apply (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
      (target := NativePacketStep.useObject s (NativePacketRounds.useTag first))
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) _).mpr
    rw [pairFit_base,pairFit_first]
    exact congrArg (Environment.mk (NativePacketStep.baseObject s 0).2 (0,target)) (data.agrees 0)
  have actual := NativePacketQueryView.rowMatches_old_iff s 0 (NativePacketRounds.useTag first) pattern
    (pairFit members first second different target data) captured occurrence
  rw [pairFit_first] at actual
  exact actual

omit [DecidableEq O] in
theorem pairFit_output_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second) (target : Frames.Frame S)
    (data : FamilyInformation.SolutionData s [members[first],members[second]] target)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern
        (pairFit members first second different target data)
        (NativePacketStep.outputRow members[second] (NativePacketRounds.useTag second) occurrence) ↔
      instantiate (data.member 0) pattern = instantiate (data.member 1) (members[second].outputs occurrence) :=
  NativePacketQueryView.rowMatches_output_iff members[second] _ pattern (NativePacketRounds.useTag second)
    (pairFit members first second different target data) (0,target) _ _
    (pairFit_first members first second different target data) (pairFit_second members first second different target data) occurrence

theorem pair_count_ignoresWrites_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (unique : ∀ occurrence ∈ members[second].selection.made, ∀ other : Fin members.length,
      occurrence ∈ members[other].selection.made → other = second)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (number : Nat) :
    (NativePacketQueryView.countQuery (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern number).IgnoresWrites
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (pairProblem members first second)
        (NativePacketRounds.label members) (NativePacketStep.selection members[second]) ↔
      ∀ (target : Frames.Frame S) (data : FamilyInformation.SolutionData s [members[first],members[second]] target),
        (∀ occurrence ∈ members[second].selection.taken,
          ¬ ContextualConditionalRows.Matches s.locals s.infoFrame.arity (data.member 0)
            (instantiate (data.member 0) pattern)
            (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence)) ∧
        (∀ occurrence ∈ members[second].selection.made,
          instantiate (data.member 0) pattern ≠ instantiate (data.member 1) (members[second].outputs occurrence)) := by
  constructor
  · intro ignored target data
    have model := pairFit_model members first second different firstEnabled secondEnabled target data
    refine ⟨?_,?_⟩
    · intro occurrence taken matched
      have written : Sum.inl occurrence ∈ (NativePacketStep.selection members[second]).taken ++
          (NativePacketStep.selection members[second]).made :=
        List.mem_append_left _ (List.mem_map_of_mem taken)
      have outside := (NativePacketQueryView.region_false_iff _ _ _ _).mp (ignored _ model _ written)
      apply outside
      rw [NativePacketRounds.label_old members occurrence (secondEnabled.taken_subset (List.mem_toFinset.mpr taken))]
      exact (pairFit_old_iff members first second different target data pattern occurrence).mpr matched
    · intro occurrence made same
      have written : Sum.inl occurrence ∈ (NativePacketStep.selection members[second]).taken ++
          (NativePacketStep.selection members[second]).made :=
        List.mem_append_right _ (List.mem_map_of_mem made)
      have outside := (NativePacketQueryView.region_false_iff _ _ _ _).mp (ignored _ model _ written)
      apply outside
      rw [NativePacketQueryView.made_label members second secondEnabled occurrence made (unique occurrence made)]
      exact (pairFit_output_iff members first second different target data pattern occurrence).mpr same
  · intro ignored substitution model port written
    have mapped : port ∈ (members[second].selection.taken ++ members[second].selection.made).map Sum.inl := by
      simpa only [NativePacketStep.selection,List.map_append] using written
    obtain ⟨occurrence,member,rfl⟩ := List.mem_map.mp mapped
    change NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern substitution
      (NativePacketRounds.label members (.inl occurrence)) = false
    apply (NativePacketQueryView.region_false_iff _ _ _ _).mpr
    intro matched
    have native := ignored _ (readPair members first second different firstEnabled secondEnabled substitution model)
    rcases List.mem_append.mp member with taken | made
    · rw [NativePacketRounds.label_old members occurrence (secondEnabled.taken_subset (List.mem_toFinset.mpr taken))] at matched
      exact native.1 occurrence taken
        ((pair_old_iff members first second different firstEnabled secondEnabled substitution model pattern occurrence).mp matched)
    · rw [NativePacketQueryView.made_label members second secondEnabled occurrence made (unique occurrence made)] at matched
      exact native.2 occurrence made
        ((pair_output_iff members first second different firstEnabled secondEnabled substitution model pattern occurrence).mp matched)

theorem member_fit_model {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (target : Frames.Frame S) (candidate : Assignment s.infoFrame.arity target.arity)
    (solved : ContextualResidual.Models candidate (FamilyInformation.memberInformation members[index])) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models
      (NativePacketStep.fit s 0 (NativePacketRounds.useTag index) target candidate) (memberProblem members index) := by
  apply (member_models_iff members index enabled _).mpr
  constructor
  · rw [NativePacketStep.fit_use]
    exact solved
  · exact NativePacketStep.fit_capture s (by simp [NativePacketRounds.useTag]) target candidate

theorem member_entails_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (observation : (target : Frames.Frame S) → Assignment s.infoFrame.arity target.arity → Prop) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails (memberProblem members index)
        (fun substitution => observation
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).1.2
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2) ↔
      (Frames.contextual S).Entails (FamilyInformation.memberInformation members[index]) observation := by
  constructor
  · intro asked target candidate solved
    have actual := asked _ (member_fit_model members index enabled target candidate solved)
    dsimp only at actual
    rw [NativePacketStep.fit_use s 0 (NativePacketRounds.useTag index) target candidate] at actual
    exact actual
  · intro asked substitution model
    exact asked _ _ ((member_models_iff members index enabled substitution).mp model).1

theorem member_region {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (memberProblem members index))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) :
    MeTTaCalculus.OccurrenceCommits.regionOf (NativePacketRounds.label members) (NativePacketStep.present s)
        (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern substitution) =
      (ContextualConditionalGuards.region s.locals
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present pattern).image Sum.inl :=
  NativePacketQueryView.source_region s 0 (NativePacketRounds.useTag index) pattern substitution
    (NativePacketRounds.label members) (NativePacketRounds.label_old members) rfl
    ((member_models_iff members index enabled substitution).mp model).2

theorem member_count_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (number : Nat) :
    (NativePacketQueryView.countQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern number).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberProblem members index)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      (Frames.contextual S).Entails (FamilyInformation.memberInformation members[index])
        (fun _ candidate => (ContextualConditionalGuards.region s.locals candidate
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern).card = number) := by
  have point (substitution : Substitution S)
      (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (memberProblem members index)) :
      (NativePacketQueryView.countQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern number).Holds
          substitution (NativePacketRounds.label members) (NativePacketStep.present s) ↔
        (ContextualConditionalGuards.region s.locals
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern).card = number := by
    change (MeTTaCalculus.OccurrenceCommits.regionOf _ _ (NativePacketQueryView.region _ _ _)).card = number ↔ _
    rw [member_region members index enabled substitution model pattern,
      Finset.card_image_of_injective _ Sum.inl_injective]
  have bridge := member_entails_iff members index enabled
    (fun _ candidate => (ContextualConditionalGuards.region s.locals candidate
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern).card = number)
  constructor
  · intro asked
    exact bridge.mp (fun substitution model => (point substitution model).mp (asked substitution model))
  · intro asked substitution model
    exact (point substitution model).mpr (bridge.mpr asked substitution model)

theorem member_exact_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (seen : Finset O) :
    (NativePacketQueryView.exactQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern
      (seen.image Sum.inl)).Ask (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberProblem members index)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      (Frames.contextual S).Entails (FamilyInformation.memberInformation members[index])
        (fun _ candidate => ContextualConditionalGuards.region s.locals candidate
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern = seen) := by
  have point (substitution : Substitution S)
      (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (memberProblem members index)) :
      ((NativePacketQueryView.exactQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern
        (seen.image Sum.inl)).atSolution substitution).Holds (NativePacketRounds.label members) (NativePacketStep.present s) ↔
        ContextualConditionalGuards.region s.locals
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern = seen := by
    change MeTTaCalculus.OccurrenceCommits.regionOf _ _ (NativePacketQueryView.region _ _ _) = seen.image Sum.inl ↔ _
    rw [member_region members index enabled substitution model pattern,Finset.image_inj Sum.inl_injective]
  have bridge := member_entails_iff members index enabled
    (fun _ candidate => ContextualConditionalGuards.region s.locals candidate
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern = seen)
  constructor
  · intro asked
    exact bridge.mp (fun substitution model => (point substitution model).mp (asked substitution model))
  · intro asked substitution model
    exact (point substitution model).mpr (bridge.mpr asked substitution model)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketQueryCuts
