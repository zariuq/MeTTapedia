import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundEveryOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeRoundExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeConcurrent

/-!
# A finite native family with one symbolic state and fixed program

Every present physical row retains its original schema closure. Absent made
identities receive the producing member's actual output closure. The finite
program contains every member's packet clause, with a distinct use tag for
each position, including equal member values at different positions.

The first comparison is the unguarded live-output facet. Nonempty families
keep the different empty-family conventions out of the round equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketRounds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled Independent)
open TaggedAssignments (Object Substitution)
open ContextPackets (Value Environment)
open NativePacketStep (Terms Ports packetAction)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

def useTag {count : Nat} (index : Fin count) : Nat := index.val + 1

def owner {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (occurrence : O) :
    Option (Fin members.length) :=
  (List.finRange members.length).find? fun index => decide (occurrence ∈ members[index].selection.made)

def label {s : NativeState S O Γ sort} (members : List (LiveFiring s)) : Ports O → Terms S O Γ sort
  | .inl occurrence =>
      if occurrence ∈ s.state.present then NativePacketStep.oldRow s 0 occurrence else
        match owner members occurrence with
        | none => NativePacketStep.oldRow s 0 occurrence
        | some index => NativePacketStep.outputRow members[index] (useTag index) occurrence
  | .inr () => ContextPackets.anchor (NativePacketStep.baseObject s 0)

def source {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :=
  RuleSyntax.OneFrame.embed (label members) (NativePacketStep.configuration s 0)

def program {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    RuleSyntax.Program (RuleSyntax.OneFrame.Terms (Terms S O Γ sort)) :=
  {rule | ∃ index : Fin members.length, rule = NativePacketStep.rule members[index] (useTag index)}

def member {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    RuleSyntax.JointFirings.OneMember (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (Ports O)
      (program members) where
  rule := NativePacketStep.rule members[index] (useTag index)
  member := ⟨index,rfl⟩
  opening := TaggedAssignments.identity S
  selection := NativePacketStep.selection members[index]
  seen := []

def memberList {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :=
  (List.finRange members.length).map (member members)

noncomputable def image {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :=
  RuleSyntax.StepWeb.Rounds.image (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)

theorem label_old {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (occurrence : O)
    (present : occurrence ∈ s.state.present) :
    label members (.inl occurrence) = NativePacketStep.oldRow s 0 occurrence := by simp [label,present]

theorem source_congruent {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit))) :
    RuleSyntax.Scope.Congruent (NativePacketStep.source members[index] 0 (useTag index)) (source members) := by
  refine ⟨fun _ => Iff.rfl,rfl,?_⟩
  intro port present
  cases port with
  | inl occurrence =>
      have old := (NativePacketStep.mem_present_inl s occurrence).mp present
      have unmade : occurrence ∉ members[index].selection.made := fun made =>
        Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr made) old
      change NativePacketStep.label members[index] 0 (useTag index) (.inl occurrence) = label members (.inl occurrence)
      rw [label_old members occurrence old]
      exact if_neg unmade
  | inr token => cases token; rfl

omit [DecidableEq O] in
theorem member_opened {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (member members index).firing.opened (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) =
      NativePacketStep.body members[index] (useTag index) :=
  NativePacketStep.opened_eq members[index] (useTag index)

omit [DecidableEq O] in
theorem member_image {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    RuleSyntax.StepWeb.Rounds.baseFiring (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (member members index) =
      NativePacketStep.baseFiring members[index] (useTag index) :=
  NativePacketStep.image_eq members[index] (useTag index)

section Admission

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem member_admission_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (shapes : native.Shapes members[index].toNative)
    (noChecks : members[index].rule.checks = []) (noQueries : members[index].patterns = []) :
    (member members index).firing.Admits (RuleSyntax.OneFrame.frames
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members) ↔
      members[index].toNative.Realized := by
  have different : (0 : Nat) ≠ useTag index := by simp [useTag]
  constructor
  · intro accepted
    have enabled := (NativePacketStep.selection_enabled members[index]).mp accepted.2.1
    have comparison := RuleSyntax.Scope.admits_iff_of_congruent (A := packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (source_congruent members index enabled) (member members index).firing
    have original := comparison.mpr accepted
    exact (NativePacketStep.unguarded_admission_iff members[index] different shapes noChecks noQueries).mp original
  · intro realized
    have enabled := ((native_admits_iff members[index].toNative).mp realized).2.1
    have original := (NativePacketStep.unguarded_admission_iff members[index] different shapes noChecks noQueries).mpr realized
    exact RuleSyntax.Scope.admits_of_congruent (A := packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (f := (member members index).firing) (source_congruent members index enabled) original

end Admission

omit [DecidableEq O] in
theorem mem_image {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    NativePacketStep.baseFiring members[index] (useTag index) ∈ image members := by
  have inside : member members index ∈ memberList members := List.mem_map.mpr ⟨index,by simp,rfl⟩
  have mapped := List.mem_map_of_mem (f := RuleSyntax.StepWeb.Rounds.baseFiring
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) inside
  rwa [member_image] at mapped

noncomputable def jointProblem {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :=
  AnnotatedRuns.jointProblem (label members) (NativePacketStep.configuration s 0) (image members)

theorem joint_models_member {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (jointProblem members)) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      ((NativePacketStep.selection members[index]).problem (label members)
        (NativePacketStep.body members[index] (useTag index)) (NativePacketStep.configuration s 0)) := by
  have pieces := (SubstitutionAction.models_append _ _ _ _).mp model
  rw [GuardFreeProcessOrders.problem_eq,SubstitutionAction.models_append]
  refine ⟨pieces.1,?_⟩
  intro equation inside
  exact pieces.2 equation (List.mem_flatMap.mpr
    ⟨NativePacketStep.baseFiring members[index] (useTag index),mem_image members index,inside⟩)

theorem member_models_native {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      ((NativePacketStep.selection members[index]).problem (label members)
        (NativePacketStep.body members[index] (useTag index)) (NativePacketStep.configuration s 0))) :
    ContextualResidual.Models (substitution (NativePacketStep.useObject s (useTag index))).2
      (FamilyInformation.memberInformation members[index]) := by
  apply (ContextPackets.models_problem _ _ _).mp
  intro equation inside
  exact model equation (List.mem_append_right _ inside)

theorem member_models_capture {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      ((NativePacketStep.selection members[index]).problem (label members)
        (NativePacketStep.body members[index] (useTag index)) (NativePacketStep.configuration s 0))) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
      (NativePacketStep.captureRow s (useTag index),ContextPackets.anchor (NativePacketStep.baseObject s 0)) := by
  have actual : (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))).Models (b := PUnit.unit) substitution
      ((member members index).firing.information
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members)) := by
    have information := RuleSyntax.OneFrame.information_eq (NativePacketStep.configuration s 0)
      (member members index).firing (label := label members)
    apply (congrArg (fun equations => (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))).Models (b := PUnit.unit) substitution equations)
      information).mpr
    have opened := member_opened members index
    exact (congrArg (fun ruleBody => (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      ((NativePacketStep.selection members[index]).problem (label members) ruleBody (NativePacketStep.configuration s 0)))
      opened).mpr model
  have paired : (NativePacketStep.captureRow s (useTag index),Sum.inr ()) ∈
      ((member members index).firing.opened
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))).read.zip
          (member members index).selection.read := by
    rw [member_opened]
    change _ ∈ (members[index].selection.read.map (NativePacketStep.readRow s (useTag index)) ++
      [NativePacketStep.captureRow s (useTag index)]).zip (members[index].selection.read.map Sum.inl ++ [.inr ()])
    rw [List.zip_append (by simp)]
    exact List.mem_append_right _ List.mem_cons_self
  have solved := RuleSyntax.Firing.read_solved (X := RuleSyntax.OneFrame.frames
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (s := source members)
      (member members index).firing actual paired
  have rowEqual : (member members index).firing.row (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members) = label members :=
    RuleSyntax.OneFrame.row_eq (NativePacketStep.configuration s 0) (member members index).firing (label := label members)
  rw [rowEqual] at solved
  exact solved

def retarget {domain : Frames.Frame S} {first second : Object S} (same : first = second)
    (candidate : Assignment domain.arity first.2.arity) : Assignment domain.arity second.2.arity := same ▸ candidate

theorem retarget_models {domain : Frames.Frame S} {first second : Object S} (same : first = second)
    (candidate : Assignment domain.arity first.2.arity) (equations : ContextualResidual.Problem domain.arity)
    (model : ContextualResidual.Models candidate equations) :
    ContextualResidual.Models (retarget same candidate) equations := by cases same; exact model

theorem retarget_compose {domain inputs : Frames.Frame S} {first second : Object S} (same : first = second)
    (candidate : Assignment domain.arity first.2.arity) (input : Assignment inputs.arity domain.arity) :
    Assignment.compose (retarget same candidate) input = retarget same (Assignment.compose candidate input) := by
  cases same
  rfl

theorem retarget_environment {domain : Frames.Frame S} {first second : Object S}
    {left : Assignment domain.arity first.2.arity} {right : Assignment domain.arity second.2.arity}
    (equal : Environment.mk domain first left = Environment.mk domain second right) :
    retarget (congrArg Environment.target equal) left = right := by
  have targets : first = second := congrArg Environment.target equal
  subst second
  exact eq_of_heq (Environment.assignment_heq S equal)

noncomputable def readData {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution (jointProblem members)) :
    FamilyInformation.SolutionData s members (substitution (NativePacketStep.baseObject s 0)).1.2 where
  shared := (substitution (NativePacketStep.baseObject s 0)).2
  member index := retarget
    (ContextPackets.capture_targets (source := NativePacketStep.baseObject s 0)
      (target := NativePacketStep.useObject s (useTag index))
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution
      (member_models_capture members index substitution (joint_models_member members index substitution model)))
    (substitution (NativePacketStep.useObject s (useTag index))).2
  models index := retarget_models _ _ _
    (member_models_native members index substitution (joint_models_member members index substitution model))
  agrees index := by
    have equal := (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
      (target := NativePacketStep.useObject s (useTag index))
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution).mp
      (member_models_capture members index substitution (joint_models_member members index substitution model))
    exact (retarget_compose (domain := s.infoFrame) (inputs := (NativePacketStep.baseObject s 0).2)
      (congrArg Environment.target equal) (substitution (NativePacketStep.useObject s (useTag index))).2
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)).trans (retarget_environment equal)

noncomputable def patch (s : NativeState S O Γ sort) (count : Nat)
    (base : (target : Object S) × Assignment s.state.declarations target.2.arity)
    (uses : Fin count → (target : Object S) × Assignment s.infoFrame.arity target.2.arity) : Substitution S := by
  classical
  intro point
  by_cases old : point = NativePacketStep.baseObject s 0
  · subst point
    exact base
  · by_cases used : ∃ index : Fin count, point = NativePacketStep.useObject s (useTag index)
    · exact (Classical.choose_spec used).symm ▸ uses (Classical.choose used)
    · exact TaggedAssignments.identity S point

omit [DecidableEq O] in
theorem patch_base (s : NativeState S O Γ sort) (count : Nat)
    (base : (target : Object S) × Assignment s.state.declarations target.2.arity)
    (uses : Fin count → (target : Object S) × Assignment s.infoFrame.arity target.2.arity) :
    patch s count base uses (NativePacketStep.baseObject s 0) = base := by
  classical
  simp [patch]
  rfl

omit [DecidableEq O] in
private theorem transport_use {s : NativeState S O Γ sort} {first second : Nat}
    (equal : NativePacketStep.useObject s first = NativePacketStep.useObject s second)
    (value : (target : Object S) × Assignment s.infoFrame.arity target.2.arity) :
    Eq.ndrec (motive := fun point : Object S => (target : Object S) × Assignment point.2.arity target.2.arity)
      value equal = value := by
  have tags : first = second := congrArg Prod.fst equal
  subst second
  rfl

omit [DecidableEq O] in
theorem patch_use (s : NativeState S O Γ sort) (count : Nat)
    (base : (target : Object S) × Assignment s.state.declarations target.2.arity)
    (uses : Fin count → (target : Object S) × Assignment s.infoFrame.arity target.2.arity) (index : Fin count) :
    patch s count base uses (NativePacketStep.useObject s (useTag index)) = uses index := by
  classical
  have notOld : NativePacketStep.useObject s (useTag index) ≠ NativePacketStep.baseObject s 0 := by
    intro equal
    have tags := congrArg Prod.fst equal
    change index.val + 1 = 0 at tags
    omega
  have used : ∃ other : Fin count,
      NativePacketStep.useObject s (useTag index) = NativePacketStep.useObject s (useTag other) := ⟨index,rfl⟩
  simp only [patch,dif_neg notOld,dif_pos used]
  have chosen : Classical.choose used = index := by
    apply Fin.ext
    have tags := congrArg Prod.fst (Classical.choose_spec used)
    change index.val + 1 = (Classical.choose used).val + 1 at tags
    omega
  exact (transport_use (s := s) (Classical.choose_spec used).symm (uses (Classical.choose used))).trans
    (congrArg uses chosen)

noncomputable def fitData {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) : Substitution S :=
  patch s members.length ⟨(0,target),data.shared⟩ (fun index => ⟨(0,target),data.member index⟩)

omit [DecidableEq O] in
theorem fitData_base {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) :
    fitData data (NativePacketStep.baseObject s 0) = ⟨(0,target),data.shared⟩ := patch_base s _ _ _

omit [DecidableEq O] in
theorem fitData_use {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) (index : Fin members.length) :
    fitData data (NativePacketStep.useObject s (useTag index)) = ⟨(0,target),data.member index⟩ := patch_use s _ _ _ index

omit [DecidableEq O] in
theorem data_models_knowledge {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) (nonempty : members ≠ []) :
    ContextualResidual.Models data.shared s.state.equations := by
  have positive : 0 < members.length := List.length_pos_iff.mpr nonempty
  let index : Fin members.length := ⟨0,positive⟩
  have known := ((NativeResidual.models_problemOf_iff members[index].selection members[index].rule
    (data.member index)).mp (data.models index)).1
  rw [data.agrees index] at known
  exact known

omit [DecidableEq O] in
theorem fitData_capture {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) (index : Fin members.length) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves (fitData data)
      (NativePacketStep.captureRow s (useTag index),ContextPackets.anchor (NativePacketStep.baseObject s 0)) := by
  apply (ContextPackets.capture_solution (source := NativePacketStep.baseObject s 0)
    (target := NativePacketStep.useObject s (useTag index))
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) _).mpr
  rw [fitData_base,fitData_use]
  exact congrArg (Environment.mk (NativePacketStep.baseObject s 0).2 (0,target)) (data.agrees index)

theorem fitData_member {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) (nonempty : members ≠ []) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit))) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models (fitData data)
      ((NativePacketStep.selection members[index]).problem (label members)
        (NativePacketStep.body members[index] (useTag index)) (NativePacketStep.configuration s 0)) := by
  have rowSolved : ∀ occurrence ∈ members[index].selection.taken ++ members[index].selection.read,
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves (fitData data)
        (NativePacketStep.readRow s (useTag index) occurrence,label members (.inl occurrence)) := by
    intro occurrence present
    have old : occurrence ∈ s.state.present := by
      rcases List.mem_append.mp present with taken | read
      · exact enabled.taken_subset (List.mem_toFinset.mpr taken)
      · exact enabled.kept_subset (List.mem_toFinset.mpr read)
    rw [label_old members occurrence old]
    exact NativePacketStep.read_row_solved s 0 (useTag index) (fitData data) (fitData_capture data index) occurrence
  simp only [Selection.problem,SubstitutionAction.models_append]
  refine ⟨⟨⟨?known,?taken⟩,?read⟩,?told⟩
  case known =>
    apply (ContextPackets.models_problem _ _ _).mpr
    rw [fitData_base]
    exact data_models_knowledge data nonempty
  case taken =>
    apply (Selection.models_equations_iff _ _ _ (by simp [NativePacketStep.body,NativePacketStep.selection])).mpr
    change List.Forall₂ _ (members[index].selection.taken.map (NativePacketStep.readRow s (useTag index)))
      (members[index].selection.taken.map Sum.inl)
    rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    exact fun occurrence present => rowSolved occurrence (List.mem_append_left _ present)
  case read =>
    apply (Selection.models_equations_iff _ _ _ (by simp [NativePacketStep.body,NativePacketStep.selection])).mpr
    change List.Forall₂ _ (members[index].selection.read.map (NativePacketStep.readRow s (useTag index)) ++
      [NativePacketStep.captureRow s (useTag index)]) (members[index].selection.read.map Sum.inl ++ [.inr ()])
    have matched : List.Forall₂
        (fun pattern port => (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).E
          (ContextPackets.apply S (fitData data) pattern) (ContextPackets.apply S (fitData data) (label members port)))
        (members[index].selection.read.map (NativePacketStep.readRow s (useTag index)))
        (members[index].selection.read.map Sum.inl) := by
      rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
      exact fun occurrence present => rowSolved occurrence (List.mem_append_right _ present)
    have extend : ∀ {left : List (Terms S O Γ sort)} {right : List (Ports O)},
        List.Forall₂ (fun pattern port => (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).E
          (ContextPackets.apply S (fitData data) pattern) (ContextPackets.apply S (fitData data) (label members port))) left right →
        List.Forall₂ (fun pattern port => (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).E
          (ContextPackets.apply S (fitData data) pattern) (ContextPackets.apply S (fitData data) (label members port)))
          (left ++ [NativePacketStep.captureRow s (useTag index)]) (right ++ [.inr ()]) := by
      intro left right fits
      induction fits with
      | nil => exact .cons (fitData_capture data index) .nil
      | cons one rest ih => exact .cons one ih
    exact extend matched
  case told =>
    apply (ContextPackets.models_problem _ _ _).mpr
    rw [fitData_use]
    exact data.models index

omit [DecidableEq O] in
theorem image_as_indices {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    image members = (List.finRange members.length).map
      (fun index => NativePacketStep.baseFiring members[index] (useTag index)) := by
  change ((List.finRange members.length).map (member members)).map _ = _
  rw [List.map_map]
  exact List.map_congr_left fun index _ => member_image members index

theorem fitData_joint {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) (nonempty : members ≠ [])
    (enabled : ∀ index : Fin members.length,
      Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit))) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models (fitData data) (jointProblem members) := by
  apply (SubstitutionAction.models_append _ _ _ _).mpr
  refine ⟨?_,?_⟩
  · apply (ContextPackets.models_problem _ _ _).mpr
    rw [fitData_base]
    exact data_models_knowledge data nonempty
  · intro equation inside
    obtain ⟨event,inImage,member⟩ := List.mem_flatMap.mp inside
    rw [image_as_indices] at inImage
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inImage
    have whole := fitData_member data nonempty index (enabled index)
    rw [GuardFreeProcessOrders.problem_eq,SubstitutionAction.models_append] at whole
    exact whole.2 equation member

theorem consistent_iff_jointly {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (enabled : ∀ index : Fin members.length,
      Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit))) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Consistent (jointProblem members) ↔
      NativeIterated.Jointly s members := by
  constructor
  · rintro ⟨substitution,model⟩
    let data := readData members substitution model
    exact (FamilyInformation.jointly_iff_solvable s members).mpr
      ⟨_,FamilyInformation.assemble data,FamilyInformation.assemble_models data⟩
  · intro jointly
    obtain ⟨target,candidate,model⟩ := (FamilyInformation.jointly_iff_solvable s members).mp jointly
    let data := FamilyInformation.extract candidate model
    exact ⟨fitData data,fitData_joint data nonempty enabled⟩

theorem owner_some {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (occurrence : O)
    (index : Fin members.length) (found : owner members occurrence = some index) :
    occurrence ∈ members[index].selection.made :=
  of_decide_eq_true (List.find?_some (p := fun position : Fin members.length =>
    decide (occurrence ∈ members[position].selection.made)) found)

theorem owner_unique {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (occurrence : O)
    (index : Fin members.length) (inside : occurrence ∈ members[index].selection.made)
    (unique : ∀ other : Fin members.length, occurrence ∈ members[other].selection.made → other = index) :
    owner members occurrence = some index := by
  cases found : owner members occurrence with
  | none =>
      have none := (List.find?_eq_none.mp found) index (by simp)
      exact False.elim (none (by simpa using inside))
  | some other => exact congrArg some (unique other (owner_some members occurrence other found))

def ResourcesApart {s : NativeState S O Γ sort} (first second : LiveFiring s) : Prop :=
  Disjoint first.selection.taken.toFinset second.selection.taken.toFinset ∧
    Disjoint first.selection.made.toFinset second.selection.made.toFinset ∧
      Disjoint first.selection.taken.toFinset second.selection.read.toFinset ∧
        Disjoint second.selection.taken.toFinset first.selection.read.toFinset

theorem physical_independent_iff {s : NativeState S O Γ sort} (first second : LiveFiring s)
    (rows : Ports O → Terms S O Γ sort) :
    Independent rows ((NativePacketStep.selection first).commit (T := Terms S O Γ sort))
      ((NativePacketStep.selection second).commit (T := Terms S O Γ sort)) ↔ ResourcesApart first second := by
  have disjoint (left right : List O) :
      Disjoint (left.map (Sum.inl : O → Ports O)).toFinset (right.map Sum.inl).toFinset ↔
        Disjoint left.toFinset right.toFinset := by
    have imageEq (values : List O) : (values.map (Sum.inl : O → Ports O)).toFinset = values.toFinset.image Sum.inl := by
      ext port
      simp
    rw [imageEq,imageEq]
    exact Finset.disjoint_image Sum.inl_injective
  simp only [Independent,MeTTaCalculus.OccurrenceCommits.Clash,MeTTaCalculus.OccurrenceCommits.Spoils,
    MeTTaCalculus.OccurrenceCommits.WritesInto,NativePacketStep.selection,Selection.commit,List.not_mem_nil,false_and,
    exists_false,or_false,not_or,not_not,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
    Finset.disjoint_union_right,Finset.disjoint_insert_right]
  simp only [disjoint,List.mem_toFinset,List.mem_map,Sum.inl_ne_inr]
  simp [ResourcesApart,and_assoc]

theorem compatible_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) :
    AnnotatedRuns.Compatible (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members)
      (NativePacketStep.configuration s 0) (NativePacketStep.baseFiring members[first] (useTag first))
      (NativePacketStep.baseFiring members[second] (useTag second)) ↔ ResourcesApart members[first] members[second] := by
  simp only [AnnotatedRuns.Compatible,NativePacketStep.baseFiring,AnnotatedRuns.Firing.ofPlain,
    NativePacketStep.body]
  simp only [List.not_mem_nil,false_implies,implies_true,and_true]
  exact physical_independent_iff members[first] members[second] (label members)

section Native

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem resources_of_clears {s : NativeState S O Γ sort} {first second : LiveFiring s}
    (clear : NativeIterated.Clears first second) : ResourcesApart first second :=
  ⟨clear.1.takes,clear.1.ports,clear.2.keeps,clear.1.keeps⟩

theorem clears_at {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (clear : NativeIterated.FamilyClear s members) (first second : Fin members.length) (different : first ≠ second) :
    NativeIterated.Clears members[first] members[second] := by
  rcases lt_or_gt_of_ne different with before | after
  · exact (List.pairwise_iff_getElem.mp clear.pairwise) first.val second.val first.isLt second.isLt before
  · exact NativeIterated.Clears.symm
      ((List.pairwise_iff_getElem.mp clear.pairwise) second.val first.val second.isLt first.isLt after)

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem clear_of_resources {s : NativeState S O Γ sort} (first second : LiveFiring s)
    (takes : Disjoint first.selection.taken.toFinset second.selection.taken.toFinset)
    (ports : Disjoint first.selection.made.toFinset second.selection.made.toFinset)
    (keeps : Disjoint second.selection.taken.toFinset first.selection.read.toFinset)
    (joint : ∃ target : Frames.Frame S, Nonempty (NativeResidual.Joint s first.toNative.information second.toNative.information target))
    (noChecks : first.rule.checks = []) (noQueries : first.patterns = []) :
    Clear first second.selection second.rule second.outputs := by
  have checks : first.toNative.prepared.rule.checks = [] := by
    change first.rule.checks.map _ = []
    rw [noChecks]
    rfl
  refine ⟨takes,ports,keeps,joint,?_,?_⟩
  · intro _ _ _ _
    refine ⟨?_,?_⟩
    · intro _ inside
      rw [checks] at inside
      cases inside
    · intro _ inside
      rw [noQueries] at inside
      cases inside
  · intro _ _ _ _
    refine ⟨?_,?_⟩
    · intro _ inside
      rw [checks] at inside
      cases inside
    · intro _ inside
      rw [noQueries] at inside
      cases inside

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem clears_of_resources {s : NativeState S O Γ sort} (first second : LiveFiring s)
    (apart : ResourcesApart first second)
    (joint : ∃ target : Frames.Frame S, Nonempty (NativeResidual.Joint s first.toNative.information second.toNative.information target))
    (noChecksFirst : first.rule.checks = []) (noQueriesFirst : first.patterns = [])
    (noChecksSecond : second.rule.checks = []) (noQueriesSecond : second.patterns = []) :
    NativeIterated.Clears first second := by
  refine ⟨clear_of_resources first second apart.1 apart.2.1 apart.2.2.2 joint noChecksFirst noQueriesFirst,?_⟩
  obtain ⟨target,⟨joint⟩⟩ := joint
  exact clear_of_resources second first apart.1.symm apart.2.1.symm apart.2.2.1
    ⟨target,⟨joint.swap⟩⟩ noChecksSecond noQueriesSecond

theorem owner_of_clear {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (clear : NativeIterated.FamilyClear s members) (index : Fin members.length)
    (occurrence : O) (inside : occurrence ∈ members[index].selection.made) : owner members occurrence = some index := by
  apply owner_unique members occurrence index inside
  intro other otherMade
  by_contra different
  exact Finset.disjoint_left.mp (clears_at clear other index different).1.ports
    (List.mem_toFinset.mpr otherMade) (List.mem_toFinset.mpr inside)

theorem keeps_of_clear {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (clear : NativeIterated.FamilyClear s members) (index : Fin members.length) :
    RuleSyntax.StepWeb.Rounds.KeepsLabels (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (label members) (member members index) := by
  rw [RuleSyntax.StepWeb.Rounds.KeepsLabels,member_opened]
  change (members[index].selection.made.map Sum.inl).map (label members) =
    members[index].selection.made.map (NativePacketStep.outputRow members[index] (useTag index))
  rw [List.map_map]
  apply List.map_congr_left
  intro occurrence inside
  have enabled := ((native_admits_iff members[index].toNative).mp
    (clear.admitted members[index] (List.getElem_mem ..))).2.1
  have notOld : occurrence ∉ s.state.present := fun old =>
    Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr inside) old
  simp only [Function.comp_apply,label,if_neg notOld,owner_of_clear clear index occurrence inside]

theorem valid_of_clear {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (clear : NativeIterated.FamilyClear s members) (index : Fin members.length)
    (noChecks : members[index].rule.checks = []) (noQueries : members[index].patterns = []) :
    (NativePacketStep.baseFiring members[index] (useTag index)).Valid
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members) (NativePacketStep.configuration s 0) := by
  have realized := clear.admitted members[index] (List.getElem_mem ..)
  have shapes := ((native_admits_iff members[index].toNative).mp realized).1
  have actual := (member_admission_iff members index shapes noChecks noQueries).mpr realized
  have mapped := (RuleSyntax.OneFrame.admits_toFirstOrder_iff (NativePacketStep.configuration s 0)
    (member members index).firing (label := label members)).mp ⟨actual,keeps_of_clear clear index⟩
  exact (congrArg (fun event => event.Valid (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
    (label members) (NativePacketStep.configuration s 0)) (member_image members index)).mp mapped.1

theorem realized_of_valid {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (shapes : native.Shapes members[index].toNative)
    (noChecks : members[index].rule.checks = []) (noQueries : members[index].patterns = [])
    (valid : (NativePacketStep.baseFiring members[index] (useTag index)).Valid
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members) (NativePacketStep.configuration s 0)) :
    members[index].toNative.Realized := by
  have packetEnabled : Enabled (fun _ : Ports O => ()) (NativePacketStep.present s)
      ((NativePacketStep.selection members[index]).commit (T := Unit)) :=
    ⟨valid.1.occurrences.taken_subset,valid.1.occurrences.kept_subset,valid.1.occurrences.apart,valid.1.occurrences.fresh,
      fun _ inside => by simp [Selection.commit] at inside⟩
  have enabled := (NativePacketStep.selection_enabled members[index]).mp packetEnabled
  have originalFresh := NativePacketStep.fresh members[index] (base := 0) (use := useTag index) (by simp [useTag]) enabled
  have actualFresh := (RuleSyntax.Scope.fresh_congruent (A := packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
    (source_congruent members index enabled) (member members index).firing).mp originalFresh
  have mappedValid := (congrArg (fun event => event.Valid (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
    (label members) (NativePacketStep.configuration s 0)) (member_image members index)).mpr valid
  have actual := (RuleSyntax.OneFrame.admits_toFirstOrder_iff (NativePacketStep.configuration s 0)
    (member members index).firing (label := label members)).mpr ⟨mappedValid,actualFresh,rfl⟩
  exact (member_admission_iff members index shapes noChecks noQueries).mp actual.1

theorem round_of_clear {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (nonempty : members ≠ []) (clear : NativeIterated.FamilyClear s members)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = []) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members)
      (NativePacketStep.configuration s 0) (image members) := by
  refine ⟨?_,?_,?_⟩
  · intro event inside
    rw [image_as_indices] at inside
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    exact valid_of_clear clear index (noChecks index) (noQueries index)
  · apply (consistent_iff_jointly members nonempty ?_).mpr clear.jointly
    intro index
    exact ((native_admits_iff members[index].toNative).mp (clear.admitted _ (List.getElem_mem ..))).2.1
  · rw [image_as_indices,List.pairwise_map]
    apply (List.pairwise_lt_finRange members.length).imp
    intro first second before
    apply (compatible_iff members first second).mpr
    exact resources_of_clears ((List.pairwise_iff_getElem.mp clear.pairwise)
      first.val second.val first.isLt second.isLt before)

theorem clear_of_round {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = [])
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members)
      (NativePacketStep.configuration s 0) (image members)) : NativeIterated.FamilyClear s members := by
  have realized : ∀ index : Fin members.length, members[index].toNative.Realized := fun index =>
    realized_of_valid members index (shapes index) (noChecks index) (noQueries index)
      (round.valid _ (mem_image members index))
  have enabled : ∀ index : Fin members.length,
      Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)) :=
    fun index => ((native_admits_iff members[index].toNative).mp (realized index)).2.1
  have jointly := (consistent_iff_jointly members nonempty enabled).mp round.joint
  have pairs : (List.finRange members.length).Pairwise
      (fun first second => ResourcesApart members[first] members[second]) := by
    have compatible := round.compatible
    rw [image_as_indices,List.pairwise_map] at compatible
    exact compatible.imp fun compatible => (compatible_iff members _ _).mp compatible
  refine ⟨?_,?_,jointly⟩
  · intro firing present
    obtain ⟨index,bound,equal⟩ := List.getElem_of_mem present
    have accepted := realized ⟨index,bound⟩
    change members[index].toNative.Realized at accepted
    rw [equal] at accepted
    exact accepted
  · apply List.pairwise_iff_getElem.mpr
    intro first second firstBound secondBound before
    have apart := (List.pairwise_iff_getElem.mp pairs) first second (by simpa) (by simpa) before
    have actualApart : ResourcesApart members[first] members[second] := by simpa using apart
    exact clears_of_resources members[first] members[second] actualApart
      (jointly.joint (List.getElem_mem ..) (List.getElem_mem ..))
      (noChecks ⟨first,firstBound⟩) (noQueries ⟨first,firstBound⟩)
      (noChecks ⟨second,secondBound⟩) (noQueries ⟨second,secondBound⟩)

theorem round_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = []) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members)
        (NativePacketStep.configuration s 0) (image members) ↔ NativeIterated.FamilyClear s members :=
  ⟨clear_of_round members nonempty shapes noChecks noQueries,
    fun clear => round_of_clear nonempty clear noChecks noQueries⟩

theorem round_iff_concurrent {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = []) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members)
        (NativePacketStep.configuration s 0) (image members) ↔
      ∃ last, NativeConcurrent.Concurrent s (members : Multiset (LiveFiring s)) last := by
  rw [round_iff members nonempty shapes noChecks noQueries]
  constructor
  · exact NativeConcurrent.concurrent_of_clear
  · rintro ⟨_,order,same,clear,_⟩
    exact clear.perm (Multiset.coe_eq_coe.mp same).symm

theorem native_every_order {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = [])
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members)
      (NativePacketStep.configuration s 0) (image members))
    {order : List (LiveFiring s)} (permutes : order.Perm members) :
    ∃ last, ∃ witness : NativeRoundExecution.Witness s order last,
      witness.toRun.last = last ∧ witness.toRun.word.length = members.length ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) :=
  NativeRoundExecution.every_order_run_of_family
    (clear_of_round members nonempty shapes noChecks noQueries round) permutes

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketRounds
