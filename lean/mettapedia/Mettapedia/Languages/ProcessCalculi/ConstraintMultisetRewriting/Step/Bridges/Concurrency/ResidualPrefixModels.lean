import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.InformationNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketRounds

/-!
# Given symbolic models through actual finite native prefixes

The execution witness is the existing native witness. Remaining firings are
carried by its actual residualAfter operation. Physical separation is the
existing NativeIterated.Unmade condition; initial occurrence enabling earns
it for an actual round. An arbitrary witness does not imply that condition
for an arbitrary remaining family.

Targets grow by faithful declaration extensions. The empty-prefix boundary
retains an explicit model of the initial knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualPrefixModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled)
open NativeResidual NativeIterated
open NativeRoundExecution (Witness)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

noncomputable def residuals : {state last : NativeState S O Γ sort} → {front : List (LiveFiring state)} →
    Witness state front last → List (LiveFiring state) → List (LiveFiring last)
  | _,_,_,.nil _,remaining => remaining
  | _,_,_,.cons _ _ accepted tail,remaining => residuals tail (remaining.map (residualAfter accepted))

noncomputable def changes : {state last : NativeState S O Γ sort} → {front : List (LiveFiring state)} →
    Witness state front last → Assignment state.state.declarations last.state.declarations
  | state,_,_,.nil _ => generator state.state.declarations
  | _,_,_,.cons _ _ accepted tail => Assignment.compose (changes tail) (change (LiveFiring.execution accepted))

noncomputable def carried : {state last : NativeState S O Γ sort} → {front : List (LiveFiring state)} →
    Witness state front last → Assignment
      (ContextualActivatedStep.target state.locals state.state.declarations)
      (ContextualActivatedStep.target last.locals last.state.declarations)
  | state,_,_,.nil _ => generator (ContextualActivatedStep.target state.locals state.state.declarations)
  | _,_,_,.cons _ _ accepted tail => Assignment.compose (carried tail) (carry (LiveFiring.execution accepted))

theorem residuals_length {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) (remaining : List (LiveFiring initial)) :
    (residuals witness remaining).length = remaining.length := by
  induction witness with
  | nil => rfl
  | cons _ _ _ tail ih => exact (ih _).trans (List.length_map ..)

def remainingPick {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) (remaining : List (LiveFiring initial))
    (index : Fin (residuals witness remaining).length) : Fin (front ++ remaining).length :=
  ⟨front.length + index.val,by
    rw [List.length_append]
    exact Nat.add_lt_add_left ((residuals_length witness remaining) ▸ index.isLt) front.length⟩

theorem step_change {state : NativeState S O Γ sort} (firing : LiveFiring state) (accepted : firing.toNative.Realized) :
    native.toStep.along firing.toNative accepted = change (LiveFiring.execution accepted) := rfl

def lastTransport {initial first last : NativeState S O Γ sort} (same : first = last)
    (assignment : Assignment initial.state.declarations first.state.declarations) :
    Assignment initial.state.declarations last.state.declarations := same ▸ assignment

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem lastTransport_compose {initial middle first last : NativeState S O Γ sort} (same : first = last)
    (assignment : Assignment middle.state.declarations first.state.declarations)
    (input : Assignment initial.state.declarations middle.state.declarations) :
    lastTransport same (Assignment.compose assignment input) = Assignment.compose (lastTransport same assignment) input := by
  cases same
  rfl

theorem changes_actual {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) :
    changes witness = lastTransport witness.toRun_last witness.toRun.toLast := by
  induction witness with
  | nil => rfl
  | @cons initial first rest accepted last tail ih =>
      change Assignment.compose (changes tail) (change (LiveFiring.execution accepted)) =
        lastTransport tail.toRun_last (Assignment.compose tail.toRun.toLast (change (LiveFiring.execution accepted)))
      exact (congrArg (fun assignment => Assignment.compose assignment (change (LiveFiring.execution accepted))) ih).trans
        (lastTransport_compose tail.toRun_last tail.toRun.toLast (change (LiveFiring.execution accepted))).symm

theorem residuals_output {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) (remaining : List (LiveFiring initial))
    (index : Fin (residuals witness remaining).length) (occurrence : O) :
    (residuals witness remaining)[index].outputs occurrence =
      instantiate (carried witness) (remaining[(⟨index.val,by simpa only [residuals_length] using index.isLt⟩ :
        Fin remaining.length)].outputs occurrence) := by
  induction witness with
  | nil => exact (instantiate_identity _).symm
  | @cons initial first rest accepted last tail ih =>
      have next := ih (remaining.map (residualAfter accepted)) index
      have bound : index.val < (remaining.map (residualAfter accepted)).length := by
        have original := index.isLt
        change index.val < (residuals tail (remaining.map (residualAfter accepted))).length at original
        simpa only [residuals_length] using original
      change (residuals tail (remaining.map (residualAfter accepted)))[index].outputs occurrence =
        instantiate (carried tail)
          (((remaining.map (residualAfter accepted))[index.val]'bound).outputs occurrence) at next
      rw [List.getElem_map] at next
      exact next.trans (instantiate_comp (carry (LiveFiring.execution accepted)) (carried tail) _)

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem unmade_of_enabled {state : NativeState S O Γ sort} (firings : List (LiveFiring state))
    (enabled : ∀ firing ∈ firings, Enabled (fun _ : O => ()) state.state.present (firing.selection.commit (T := Unit))) :
    Unmade firings := by
  intro reader inReader writer inWriter occurrence selected made
  have old : occurrence ∈ state.state.present := by
    rcases List.mem_append.mp selected with taken | read
    · exact (enabled reader inReader).taken_subset (List.mem_toFinset.mpr taken)
    · exact (enabled reader inReader).kept_subset (List.mem_toFinset.mpr read)
  exact Finset.disjoint_left.mp (enabled writer inWriter).fresh (List.mem_toFinset.mpr made) old

theorem unmade_of_clear {state : NativeState S O Γ sort} {firings : List (LiveFiring state)}
    (clear : FamilyClear state firings) : Unmade firings :=
  unmade_of_enabled firings fun firing inside => ((native_admits_iff firing.toNative).mp (clear.admitted firing inside)).2.1

variable {state : NativeState S O Γ sort}
  (execution : ContextualConditionalExecution.Firing state.locals state.state)

theorem publishedModel_right {target : Frames.Frame S}
    (right : Assignment (ContextualActivatedStep.target state.locals state.state.declarations) target.arity) :
    Assignment.compose (ResidualModels.publishedModel execution right)
        (ContextualComputedFreshFrame.includeSource execution.update) =
      Assignment.compose (ResidualModels.inclusion execution target) right := by
  funext name
  exact (congrArg (instantiate (ResidualModels.publishedModel execution right)) (includeSource_apply execution name)).trans
    (instantiate_generator (ResidualModels.publishedModel execution right) (.inl name))

theorem publishedModel_known {target : Frames.Frame S}
    (right : Assignment (ContextualActivatedStep.target state.locals state.state.declarations) target.arity)
    (model : ContextualResidual.Models right (problemOf state execution.selection execution.rule)) :
    ContextualResidual.Models (ResidualModels.publishedModel execution right) execution.target.equations := by
  apply (ContextualResidual.models_mapProblem _ _ _).mpr
  rw [publishedModel_right]
  exact ContextualResidual.models_compose model (ResidualModels.inclusion execution target)

theorem publishedModel_captures {target : Frames.Frame S}
    (right : Assignment (ContextualActivatedStep.target state.locals state.state.declarations) target.arity) :
    Assignment.compose (ResidualModels.publishedModel execution right) (change execution) =
      Assignment.compose (ResidualModels.inclusion execution target)
        (Assignment.compose right (ContextualSelectionViews.capturedTarget state.locals state.state.declarations)) := by
  change Assignment.compose (ResidualModels.publishedModel execution right)
    (Assignment.compose (ContextualComputedFreshFrame.includeSource execution.update)
      (ContextualSelectionViews.capturedTarget state.locals state.state.declarations)) = _
  rw [Assignment.compose_associative,publishedModel_right,← Assignment.compose_associative]

structure Lifted (initial last : NativeState S O Γ sort) (remaining : List (LiveFiring last))
    (target : Frames.Frame S) (shared : Assignment initial.state.declarations target.arity)
    (transport : Assignment initial.state.declarations last.state.declarations)
    (sourceMembers : Fin remaining.length → Assignment
      (ContextualActivatedStep.target initial.locals initial.state.declarations) target.arity)
    (informationTransport : Assignment (ContextualActivatedStep.target initial.locals initial.state.declarations)
      (ContextualActivatedStep.target last.locals last.state.declarations)) where
  extension : ContextualGuardMatching.Extension target.arity
  data : FamilyInformation.SolutionData last remaining ⟨extension.Names,extension.declarations⟩
  known : ContextualResidual.Models data.shared last.state.equations
  captures : Assignment.compose data.shared transport = Assignment.compose extension.assignment shared
  members : ∀ index, Assignment.compose (data.member index) informationTransport =
    Assignment.compose extension.assignment (sourceMembers index)

def castData {initial : NativeState S O Γ sort} {first second : List (LiveFiring initial)} {target : Frames.Frame S}
    (same : first = second) (data : FamilyInformation.SolutionData initial first target) :
    FamilyInformation.SolutionData initial second target := same ▸ data

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem castData_shared {initial : NativeState S O Γ sort} {first second : List (LiveFiring initial)} {target : Frames.Frame S}
    (same : first = second) (data : FamilyInformation.SolutionData initial first target) :
    (castData same data).shared = data.shared := by cases same; rfl

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem castData_member {initial : NativeState S O Γ sort} {first second : List (LiveFiring initial)} {target : Frames.Frame S}
    (same : first = second) (data : FamilyInformation.SolutionData initial first target) (index : Fin second.length) :
    (castData same data).member index = data.member ⟨index.val,by simpa only [same] using index.isLt⟩ := by
  cases same
  rfl

def tailData {initial : NativeState S O Γ sort} {first : LiveFiring initial} {rest : List (LiveFiring initial)}
    {target : Frames.Frame S} (data : FamilyInformation.SolutionData initial (first :: rest) target) :
    FamilyInformation.SolutionData initial rest target :=
  InformationNaturality.restrictData (members := first :: rest) (subfamily := rest)
    (fun index => index.succ) (fun _ => rfl) data

noncomputable def lift {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) {remaining : List (LiveFiring initial)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData initial (front ++ remaining) target)
    (known : ContextualResidual.Models data.shared initial.state.equations) (unmade : Unmade (front ++ remaining)) :
    Lifted initial last (residuals witness remaining) target data.shared (changes witness)
      (fun index => data.member (remainingPick witness remaining index)) (carried witness) := by
  induction witness generalizing target with
  | nil initial =>
      refine ⟨ContextualGuardMatching.Extension.identity target.arity,data,known,?_,?_⟩
      · exact (Assignment.compose_identity_right data.shared).trans (Assignment.compose_identity_left data.shared).symm
      · intro index
        have same : remainingPick (.nil initial) remaining index = index := by
          apply Fin.ext
          change 0 + index.val = index.val
          omega
        change Assignment.compose (data.member index) (generator _) =
          Assignment.compose (ContextualGuardMatching.Extension.identity target.arity).assignment
            (data.member (remainingPick (.nil initial) remaining index))
        rw [same]
        exact (Assignment.compose_identity_right (data.member index)).trans
          (Assignment.compose_identity_left (data.member index)).symm
  | @cons initial first rest accepted last tail ih =>
      let currentExecution := LiveFiring.execution accepted
      let head : Fin ((first :: rest) ++ remaining).length := ⟨0,by simp⟩
      let right := data.member head
      let oldRemaining : FamilyInformation.SolutionData initial (rest ++ remaining) target := tailData data
      have rightModel : ContextualResidual.Models right
          (problemOf initial currentExecution.selection currentExecution.rule) := by
        rw [problemOf_execution accepted]
        exact data.models head
      have rightAgrees : Assignment.compose right
          (ContextualSelectionViews.capturedTarget initial.locals initial.state.declarations) = oldRemaining.shared :=
        data.agrees head
      have untouched : ∀ firing ∈ rest ++ remaining, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
          occurrence ∉ currentExecution.selection.made := by
        intro firing inside occurrence selected
        rw [(LiveFiring.execution_data accepted).2.1]
        exact unmade firing (List.mem_cons_of_mem first inside) first List.mem_cons_self occurrence selected
      let post := ResidualModels.residualData currentExecution oldRemaining right rightModel rightAgrees untouched
      have mapped : (rest ++ remaining).map (fun firing : LiveFiring initial => firing.residualAt currentExecution) =
          rest.map (residualAfter accepted) ++ remaining.map (residualAfter accepted) := List.map_append ..
      let reordered := castData mapped post
      have sameShared : reordered.shared = ResidualModels.publishedModel currentExecution right := castData_shared mapped post
      have postKnown : ContextualResidual.Models reordered.shared (native.result first.toNative accepted).state.equations :=
        (congrArg (fun assignment => ContextualResidual.Models assignment
          (native.result first.toNative accepted).state.equations) sameShared).mpr
          (publishedModel_known currentExecution right rightModel)
      have nextUnmade : Unmade (rest.map (residualAfter accepted) ++ remaining.map (residualAfter accepted)) := by
        exact (congrArg (fun firings : List (LiveFiring (native.result first.toNative accepted)) => Unmade firings) mapped).mp
          (Unmade.residual accepted unmade)
      let later := ih reordered postKnown nextUnmade
      have postCaptures : Assignment.compose reordered.shared (change currentExecution) =
          Assignment.compose (ResidualModels.inclusion currentExecution target) data.shared := by
        calc
          _ = Assignment.compose (ResidualModels.publishedModel currentExecution right) (change currentExecution) :=
            congrArg (fun assignment => Assignment.compose assignment (change currentExecution)) sameShared
          _ = Assignment.compose (ResidualModels.inclusion currentExecution target)
              (Assignment.compose right (ContextualSelectionViews.capturedTarget initial.locals initial.state.declarations)) :=
            publishedModel_captures currentExecution right
          _ = Assignment.compose (ResidualModels.inclusion currentExecution target) data.shared :=
            congrArg (Assignment.compose (ResidualModels.inclusion currentExecution target)) (data.agrees head)
      have captureLaw : Assignment.compose later.data.shared (Assignment.compose (changes tail) (change currentExecution)) =
        Assignment.compose ((ResidualModels.extension currentExecution target).trans later.extension).assignment data.shared
          := by
        have final : Assignment.compose (Assignment.compose later.extension.assignment (ResidualModels.inclusion currentExecution target))
            data.shared = Assignment.compose ((ResidualModels.extension currentExecution target).trans later.extension).assignment data.shared :=
          congrArg (fun assignment : Assignment target.arity later.extension.declarations => Assignment.compose assignment data.shared)
            (ContextualGuardMatching.Extension.trans_assignment (ResidualModels.extension currentExecution target) later.extension).symm
        refine Eq.trans ?_ final
        calc
          _ = Assignment.compose (Assignment.compose later.data.shared (changes tail)) (change currentExecution) :=
            Assignment.compose_associative _ _ _
          _ = Assignment.compose (Assignment.compose later.extension.assignment reordered.shared) (change currentExecution) :=
            congrArg (fun assignment => Assignment.compose assignment (change currentExecution)) later.captures
          _ = Assignment.compose later.extension.assignment (Assignment.compose reordered.shared (change currentExecution)) :=
            (Assignment.compose_associative _ _ _).symm
          _ = Assignment.compose later.extension.assignment
              (Assignment.compose (ResidualModels.inclusion currentExecution target) data.shared) :=
            congrArg (Assignment.compose later.extension.assignment) postCaptures
          _ = Assignment.compose (Assignment.compose later.extension.assignment (ResidualModels.inclusion currentExecution target)) data.shared :=
            Assignment.compose_associative _ _ _
      refine ⟨(ResidualModels.extension currentExecution target).trans later.extension,later.data,later.known,captureLaw,?_⟩
      intro index
      let nextIndex := remainingPick tail (remaining.map (residualAfter accepted)) index
      let oldIndex : Fin (rest ++ remaining).length := ⟨nextIndex.val,by
        have bound := nextIndex.isLt
        simpa only [List.length_append,List.length_map] using bound⟩
      have originalIndex : oldIndex.succ = remainingPick (.cons first rest accepted tail) remaining index := by
        apply Fin.ext
        change (rest.map (residualAfter accepted)).length + index.val + 1 = (first :: rest).length + index.val
        simp only [List.length_map,List.length_cons]
        omega
      have memberSame := castData_member mapped post nextIndex
      have currentLaw : Assignment.compose (reordered.member nextIndex) (carry currentExecution) =
          Assignment.compose (ResidualModels.inclusion currentExecution target) (oldRemaining.member oldIndex) :=
        (congrArg (fun assignment => Assignment.compose assignment (carry currentExecution)) memberSame).trans
          (ResidualModels.amalgam_left currentExecution
            (ResidualModels.familyJoint currentExecution oldRemaining right rightModel rightAgrees oldIndex))
      have sourceSame : oldRemaining.member oldIndex =
          data.member (remainingPick (.cons first rest accepted tail) remaining index) := congrArg data.member originalIndex
      have currentOriginal : Assignment.compose (reordered.member nextIndex) (carry currentExecution) =
          Assignment.compose (ResidualModels.inclusion currentExecution target)
            (data.member (remainingPick (.cons first rest accepted tail) remaining index)) :=
        currentLaw.trans (congrArg (Assignment.compose (ResidualModels.inclusion currentExecution target)) sourceSame)
      have final : Assignment.compose (Assignment.compose later.extension.assignment (ResidualModels.inclusion currentExecution target))
          (data.member (remainingPick (.cons first rest accepted tail) remaining index)) =
          Assignment.compose ((ResidualModels.extension currentExecution target).trans later.extension).assignment
            (data.member (remainingPick (.cons first rest accepted tail) remaining index)) :=
        congrArg (fun assignment : Assignment target.arity later.extension.declarations =>
          Assignment.compose assignment (data.member (remainingPick (.cons first rest accepted tail) remaining index)))
          (ContextualGuardMatching.Extension.trans_assignment (ResidualModels.extension currentExecution target) later.extension).symm
      refine Eq.trans ?_ final
      change Assignment.compose (later.data.member index) (Assignment.compose (carried tail) (carry currentExecution)) = _
      calc
        _ = Assignment.compose (Assignment.compose (later.data.member index) (carried tail)) (carry currentExecution) :=
          Assignment.compose_associative _ _ _
        _ = Assignment.compose (Assignment.compose later.extension.assignment (reordered.member nextIndex)) (carry currentExecution) :=
          congrArg (fun assignment => Assignment.compose assignment (carry currentExecution)) (later.members index)
        _ = Assignment.compose later.extension.assignment (Assignment.compose (reordered.member nextIndex) (carry currentExecution)) :=
          (Assignment.compose_associative _ _ _).symm
        _ = Assignment.compose later.extension.assignment
            (Assignment.compose (ResidualModels.inclusion currentExecution target)
              (data.member (remainingPick (.cons first rest accepted tail) remaining index))) :=
          congrArg (Assignment.compose later.extension.assignment) currentOriginal
        _ = Assignment.compose (Assignment.compose later.extension.assignment (ResidualModels.inclusion currentExecution target))
            (data.member (remainingPick (.cons first rest accepted tail) remaining index)) :=
          Assignment.compose_associative _ _ _

noncomputable def lift_of_clear {initial last : NativeState S O Γ sort} {front remaining : List (LiveFiring initial)}
    (witness : Witness initial front last) {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData initial (front ++ remaining) target)
    (nonempty : front ++ remaining ≠ []) (clear : FamilyClear initial (front ++ remaining)) :
    Lifted initial last (residuals witness remaining) target data.shared (changes witness)
      (fun index => data.member (remainingPick witness remaining index)) (carried witness) :=
  lift witness data (NativePacketRounds.data_models_knowledge data nonempty) (unmade_of_clear clear)

theorem lift_actual_captures {initial last : NativeState S O Γ sort} {front remaining : List (LiveFiring initial)}
    (witness : Witness initial front last) {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData initial (front ++ remaining) target)
    (known : ContextualResidual.Models data.shared initial.state.equations) (unmade : Unmade (front ++ remaining)) :
    Assignment.compose (lift witness data known unmade).data.shared
        (lastTransport witness.toRun_last witness.toRun.toLast) =
      Assignment.compose (lift witness data known unmade).extension.assignment data.shared :=
  (congrArg (Assignment.compose (lift witness data known unmade).data.shared) (changes_actual witness)).symm.trans
    (lift witness data known unmade).captures

theorem lift_output_reading {initial last : NativeState S O Γ sort} {front remaining : List (LiveFiring initial)}
    (witness : Witness initial front last) {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData initial (front ++ remaining) target)
    (known : ContextualResidual.Models data.shared initial.state.equations) (unmade : Unmade (front ++ remaining))
    (index : Fin (residuals witness remaining).length) (occurrence : O) :
    instantiate ((lift witness data known unmade).data.member index) ((residuals witness remaining)[index].outputs occurrence) =
      instantiate (lift witness data known unmade).extension.assignment
        (instantiate (data.member (remainingPick witness remaining index))
          (remaining[(⟨index.val,by simpa only [residuals_length] using index.isLt⟩ : Fin remaining.length)].outputs occurrence)) := by
  let output := remaining[(⟨index.val,by simpa only [residuals_length] using index.isLt⟩ : Fin remaining.length)].outputs occurrence
  exact (congrArg (instantiate ((lift witness data known unmade).data.member index)) (residuals_output witness remaining index occurrence)).trans
    ((instantiate_comp (carried witness) ((lift witness data known unmade).data.member index) output).trans
      ((congrArg (fun assignment => instantiate assignment output) ((lift witness data known unmade).members index)).trans
        (Assignment.instantiate_compose (lift witness data known unmade).extension.assignment
          (data.member (remainingPick witness remaining index)) output)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualPrefixModels
