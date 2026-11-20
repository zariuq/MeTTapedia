import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualPrefixModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativeClosedReadings

/-!
# Recovering given original models from actual native results

A model of a returned state restricts to the pinned execution's information. Models of remaining
residuals restrict through the actual carrying. The returned shared model must model the returned
knowledge even when there are no remaining members; an empty solution family alone says nothing
about that knowledge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketResultModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeIterated
open FamilyInformation (SolutionData memberInformation)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

section Step

variable {initial : NativeState S O Γ sort} {first : LiveFiring initial}
  (accepted : first.toNative.Realized) (remaining : List (LiveFiring initial))
  {target : Frames.Frame S}

def residualIndex (index : Fin remaining.length) : Fin (remaining.map (residualAfter accepted)).length :=
  ⟨index.val, by simpa only [List.length_map] using index.isLt⟩

noncomputable def headAssignment
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target) : Assignment initial.infoFrame.arity target.arity :=
  Assignment.compose post.shared
    (ContextualComputedFreshFrame.includeSource (LiveFiring.execution accepted).update)

theorem headAssignment_models
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target)
    (known : ContextualResidual.Models post.shared (native.result first.toNative accepted).state.equations) :
    ContextualResidual.Models (headAssignment accepted remaining post) (memberInformation first) := by
  have actual : ContextualResidual.Models post.shared
      (ContextualResidual.mapProblem
        (ContextualComputedFreshFrame.includeSource (LiveFiring.execution accepted).update)
        (problemOf initial (LiveFiring.execution accepted).selection (LiveFiring.execution accepted).rule)) := known
  have restricted := (ContextualResidual.models_mapProblem _ _ _).mp actual
  rw [problemOf_execution accepted] at restricted
  exact restricted

noncomputable def remainingJoint
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target)
    (unmade : ∀ firing ∈ remaining, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ first.selection.made) (index : Fin remaining.length) :
    Joint initial (memberInformation remaining[index])
      (problemOf initial (LiveFiring.execution accepted).selection (LiveFiring.execution accepted).rule) target := by
  have untouched : ∀ occurrence ∈ remaining[index].selection.taken ++ remaining[index].selection.read,
      occurrence ∉ (LiveFiring.execution accepted).selection.made := by
    rw [(LiveFiring.execution_data accepted).2.1]
    exact unmade remaining[index] (List.getElem_mem ..)
  have model := post.models (residualIndex accepted remaining index)
  change ContextualResidual.Models (post.member (residualIndex accepted remaining index))
    ((remaining.map (residualAfter accepted))[(residualIndex accepted remaining index).val]).toNative.information at model
  rw [List.getElem_map] at model
  exact Joint.ofResidual (LiveFiring.execution accepted) remaining[index] untouched
    (post.member (residualIndex accepted remaining index)) model

theorem remainingJoint_right
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target)
    (unmade : ∀ firing ∈ remaining, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ first.selection.made) (index : Fin remaining.length) :
    (remainingJoint accepted remaining post unmade index).right = headAssignment accepted remaining post := by
  change Assignment.compose
      (Assignment.compose (post.member (residualIndex accepted remaining index))
        (laterCaptured (LiveFiring.execution accepted)))
      (ContextualComputedFreshFrame.includeSource (LiveFiring.execution accepted).update) = _
  have agrees := post.agrees (residualIndex accepted remaining index)
  exact congrArg
    (fun assignment => Assignment.compose assignment
      (ContextualComputedFreshFrame.includeSource (LiveFiring.execution accepted).update)) agrees

noncomputable def stepData
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target)
    (known : ContextualResidual.Models post.shared (native.result first.toNative accepted).state.equations)
    (unmade : ∀ firing ∈ remaining, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ first.selection.made) : SolutionData initial (first :: remaining) target where
  shared := Assignment.compose (headAssignment accepted remaining post)
    (ContextualSelectionViews.capturedTarget initial.locals initial.state.declarations)
  member := Fin.cases (headAssignment accepted remaining post)
    (fun index => (remainingJoint accepted remaining post unmade index).left)
  agrees index := by
    refine Fin.cases rfl (fun position => ?_) index
    exact (remainingJoint accepted remaining post unmade position).agree.trans
      (congrArg
        (fun assignment => Assignment.compose assignment
          (ContextualSelectionViews.capturedTarget initial.locals initial.state.declarations))
        (remainingJoint_right accepted remaining post unmade position))
  models index := by
    refine Fin.cases (headAssignment_models accepted remaining post known)
      (fun position => ?_) index
    exact (remainingJoint accepted remaining post unmade position).left_models

theorem stepData_known
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target)
    (known : ContextualResidual.Models post.shared (native.result first.toNative accepted).state.equations)
    (unmade : ∀ firing ∈ remaining, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ first.selection.made) :
    ContextualResidual.Models (stepData accepted remaining post known unmade).shared initial.state.equations :=
  ((models_problemOf_iff first.selection first.rule (headAssignment accepted remaining post)).mp
    (headAssignment_models accepted remaining post known)).1

theorem stepData_captures
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target)
    (known : ContextualResidual.Models post.shared (native.result first.toNative accepted).state.equations)
    (unmade : ∀ firing ∈ remaining, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ first.selection.made) :
    (stepData accepted remaining post known unmade).shared =
      Assignment.compose post.shared (change (LiveFiring.execution accepted)) :=
  (Assignment.compose_associative _ _ _).symm

theorem stepData_remaining
    (post : SolutionData (native.result first.toNative accepted)
      (remaining.map (residualAfter accepted)) target)
    (known : ContextualResidual.Models post.shared (native.result first.toNative accepted).state.equations)
    (unmade : ∀ firing ∈ remaining, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ first.selection.made) (index : Fin remaining.length) :
    (stepData accepted remaining post known unmade).member index.succ =
      Assignment.compose (post.member (residualIndex accepted remaining index))
        (carry (LiveFiring.execution accepted)) := rfl

end Step

open NativeRoundExecution (Witness)
open ResidualPrefixModels (residuals residuals_length changes carried remainingPick castData castData_shared castData_member)

structure Recovered {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) (remaining : List (LiveFiring initial))
    {target : Frames.Frame S} (post : SolutionData last (residuals witness remaining) target) where
  data : SolutionData initial (front ++ remaining) target
  known : ContextualResidual.Models data.shared initial.state.equations
  captures : data.shared = Assignment.compose post.shared (changes witness)
  members : ∀ index, data.member (remainingPick witness remaining index) =
    Assignment.compose (post.member index) (carried witness)

/-- Restrict a supplied returned model through every actual pinned execution. No target is chosen
or collapsed, and the explicit returned-knowledge model covers the empty-remaining boundary. -/
noncomputable def recover {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) {remaining : List (LiveFiring initial)} {target : Frames.Frame S}
    (post : SolutionData last (residuals witness remaining) target)
    (known : ContextualResidual.Models post.shared last.state.equations)
    (unmade : Unmade (front ++ remaining)) : Recovered witness remaining post := by
  induction witness generalizing target with
  | nil initial =>
      refine ⟨post, known, ?_, ?_⟩
      · exact (Assignment.compose_identity_right post.shared).symm
      · intro index
        have same : remainingPick (.nil initial) remaining index = index := by
          apply Fin.ext
          change 0 + index.val = index.val
          omega
        rw [same]
        exact (Assignment.compose_identity_right (post.member index)).symm
  | @cons initial first rest accepted last tail ih =>
      have mapped : (rest ++ remaining).map (residualAfter accepted) =
          rest.map (residualAfter accepted) ++ remaining.map (residualAfter accepted) := List.map_append ..
      have nextUnmade : Unmade (rest.map (residualAfter accepted) ++ remaining.map (residualAfter accepted)) :=
        (congrArg (fun firings : List (LiveFiring (native.result first.toNative accepted)) => Unmade firings)
          mapped).mp (Unmade.residual accepted unmade)
      let before := ih (remaining := remaining.map (residualAfter accepted)) post known nextUnmade
      let nextData := castData mapped.symm before.data
      have sameShared : nextData.shared = before.data.shared := castData_shared mapped.symm before.data
      have nextKnown : ContextualResidual.Models nextData.shared
          (native.result first.toNative accepted).state.equations :=
        (congrArg (fun assignment => ContextualResidual.Models assignment
          (native.result first.toNative accepted).state.equations) sameShared).mpr before.known
      have untouched : ∀ firing ∈ rest ++ remaining,
          ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read, occurrence ∉ first.selection.made := by
        intro firing inside occurrence selected
        exact unmade firing (List.mem_cons_of_mem first inside) first List.mem_cons_self occurrence selected
      let result := stepData accepted (rest ++ remaining) nextData nextKnown untouched
      refine ⟨result, stepData_known accepted (rest ++ remaining) nextData nextKnown untouched, ?_, ?_⟩
      · calc
          result.shared = Assignment.compose nextData.shared (change (LiveFiring.execution accepted)) :=
            stepData_captures accepted (rest ++ remaining) nextData nextKnown untouched
          _ = Assignment.compose before.data.shared (change (LiveFiring.execution accepted)) :=
            congrArg (fun assignment => Assignment.compose assignment (change (LiveFiring.execution accepted))) sameShared
          _ = Assignment.compose (Assignment.compose post.shared (changes tail))
              (change (LiveFiring.execution accepted)) :=
            congrArg (fun assignment => Assignment.compose assignment (change (LiveFiring.execution accepted))) before.captures
          _ = Assignment.compose post.shared (changes (.cons first rest accepted tail)) :=
            (Assignment.compose_associative _ _ _).symm
      · intro index
        let nextIndex := remainingPick tail (remaining.map (residualAfter accepted)) index
        let oldIndex : Fin (rest ++ remaining).length := ⟨nextIndex.val, by
          have bound := nextIndex.isLt
          simpa only [List.length_append, List.length_map] using bound⟩
        let mappedIndex := residualIndex accepted (rest ++ remaining) oldIndex
        have originalIndex : oldIndex.succ = remainingPick (.cons first rest accepted tail) remaining index := by
          apply Fin.ext
          change (rest.map (residualAfter accepted)).length + index.val + 1 = (first :: rest).length + index.val
          simp only [List.length_map, List.length_cons]
          omega
        have memberImported : nextData.member mappedIndex = before.data.member nextIndex :=
          (castData_member mapped.symm before.data mappedIndex).trans
            (congrArg before.data.member (Fin.ext rfl))
        calc
          result.member (remainingPick (.cons first rest accepted tail) remaining index) =
              result.member oldIndex.succ := congrArg result.member originalIndex.symm
          _ = Assignment.compose (nextData.member mappedIndex) (carry (LiveFiring.execution accepted)) :=
            stepData_remaining accepted (rest ++ remaining) nextData nextKnown untouched oldIndex
          _ = Assignment.compose (before.data.member nextIndex) (carry (LiveFiring.execution accepted)) :=
            congrArg (fun assignment => Assignment.compose assignment (carry (LiveFiring.execution accepted))) memberImported
          _ = Assignment.compose (Assignment.compose (post.member index) (carried tail))
              (carry (LiveFiring.execution accepted)) :=
            congrArg (fun assignment => Assignment.compose assignment (carry (LiveFiring.execution accepted)))
              (before.members index)
          _ = Assignment.compose (post.member index) (carried (.cons first rest accepted tail)) :=
            (Assignment.compose_associative _ _ _).symm

def emptyData (last : NativeState S O Γ sort) (target : Frames.Frame S)
    (candidate : Assignment last.state.declarations target.arity) : SolutionData last [] target where
  shared := candidate
  member index := index.elim0
  agrees index := index.elim0
  models index := index.elim0

theorem residuals_nil {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) : residuals witness [] = [] :=
  List.length_eq_zero_iff.mp (residuals_length witness [])

noncomputable def finalPost {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) {target : Frames.Frame S}
    (candidate : Assignment last.state.declarations target.arity) : SolutionData last (residuals witness []) target :=
  castData (residuals_nil witness).symm (emptyData last target candidate)

theorem finalPost_shared {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) {target : Frames.Frame S}
    (candidate : Assignment last.state.declarations target.arity) : (finalPost witness candidate).shared = candidate :=
  castData_shared (residuals_nil witness).symm (emptyData last target candidate)

noncomputable def recoverFinal {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) {target : Frames.Frame S}
    (candidate : Assignment last.state.declarations target.arity)
    (known : ContextualResidual.Models candidate last.state.equations) (unmade : Unmade front) :
    Recovered witness [] (finalPost witness candidate) := by
  exact recover witness (finalPost witness candidate)
    ((congrArg (fun assignment => ContextualResidual.Models assignment last.state.equations)
      (finalPost_shared witness candidate)).mpr known)
    (by simpa only [List.append_nil] using unmade)

/-! ## Actual conditional row readings through publication -/

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem matches_post {Local Shared Before After : Type}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {before : Before → MetaArity S} {after : After → MetaArity S}
    (post : Assignment before after) (candidate : Assignment captures before)
    (pattern : Term (signature S before) Γ sort)
    (row : ContextualConditionalRows.Row locals captures Γ sort)
    (matched : ContextualConditionalRows.Matches locals captures candidate pattern row) :
    ContextualConditionalRows.Matches locals captures (Assignment.compose post candidate)
      (instantiate post pattern) row := by
  obtain ⟨witness, images, conditions, same⟩ := matched
  let fresh := ContextualGuardMatching.Extension.withLocals witness.complementDeclarations after
  let lifted := witness.liftModel post
  let nextImages := Assignment.compose lifted images
  have square : ContextualGuardMatching.instanceAssignment locals nextImages fresh.assignment
        (Assignment.compose post candidate) =
      Assignment.compose lifted (ContextualGuardMatching.instanceAssignment locals images witness.assignment candidate) := by
    funext name
    cases name with
    | inl name => rfl
    | inr name =>
        change instantiate fresh.assignment (instantiate post (candidate name)) =
          instantiate lifted (instantiate witness.assignment (candidate name))
        rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
        exact congrArg (fun assignment => instantiate assignment (candidate name))
          (witness.liftModel_square post).symm
  refine ⟨fresh, nextImages, ?_, ?_⟩
  · rw [square]
    exact ContextualResidual.models_compose conditions lifted
  · calc
      instantiate (ContextualGuardMatching.instanceAssignment locals nextImages fresh.assignment
          (Assignment.compose post candidate))
          (ContextualStoredRows.asTemplate locals captures row.value)
          = instantiate lifted (instantiate
              (ContextualGuardMatching.instanceAssignment locals images witness.assignment candidate)
              (ContextualStoredRows.asTemplate locals captures row.value)) := by
            rw [square, Assignment.instantiate_compose]
      _ = instantiate lifted (instantiate witness.assignment pattern) :=
        congrArg (instantiate lifted) same
      _ = instantiate (Assignment.compose lifted witness.assignment) pattern :=
        (Assignment.instantiate_compose _ _ _).symm
      _ = instantiate (Assignment.compose fresh.assignment post) pattern :=
        congrArg (fun assignment => instantiate assignment pattern) (witness.liftModel_square post)
      _ = instantiate fresh.assignment (instantiate post pattern) := Assignment.instantiate_compose _ _ _

theorem state_matches_retained {initial : NativeState S O Γ sort}
    (execution : ContextualConditionalExecution.Firing initial.locals initial.state)
    {target : Frames.Frame S} (candidate : Assignment execution.target.declarations target.arity)
    {occurrence : O} (notMade : occurrence ∉ execution.selection.made)
    (pattern : Term (signature S target.arity) Γ sort) :
    ContextualConditionalRows.Matches (ContextualPublication.privateFamily initial.locals execution.update.declaration)
        execution.target.declarations candidate pattern (execution.target.rows occurrence) ↔
      ContextualConditionalRows.Matches initial.locals initial.state.declarations
        (Assignment.compose candidate (change execution)) pattern (initial.state.rows occurrence) := by
  rw [rows_of_not_made execution notMade, retained,
    ContextualConditionalPublication.extendPrivate_matches_iff,
    ContextualConditionalRows.matches_map_iff]

theorem state_matches_made {initial : NativeState S O Γ sort}
    (execution : ContextualConditionalExecution.Firing initial.locals initial.state)
    {target : Frames.Frame S} (candidate : Assignment execution.target.declarations target.arity)
    {occurrence : O} (made : occurrence ∈ execution.selection.made) (live : execution.reusable occurrence = false)
    (pattern : Term (signature S target.arity) Γ sort) :
    ContextualConditionalRows.Matches (ContextualPublication.privateFamily initial.locals execution.update.declaration)
        execution.target.declarations candidate pattern (execution.target.rows occurrence) ↔
      pattern = instantiate (Assignment.compose candidate
        (ContextualComputedFreshFrame.includeSource execution.update)) (execution.outputs occurrence) := by
  rw [execution.shared_row occurrence made live, ContextualConditionalRows.ofStored_matches_iff,
    ContextualGuardMatching.shared_matches_iff, ← Assignment.instantiate_compose]

theorem actual_matches_retained {initial : NativeState S O Γ sort} {first : LiveFiring initial}
    (accepted : first.toNative.Realized) {target : Frames.Frame S}
    (candidate : Assignment (native.result first.toNative accepted).state.declarations target.arity)
    {occurrence : O} (notMade : occurrence ∉ first.selection.made)
    (pattern : Term (signature S target.arity) Γ sort) :
    ContextualConditionalRows.Matches (native.result first.toNative accepted).locals
        (native.result first.toNative accepted).state.declarations candidate pattern
        ((native.result first.toNative accepted).state.rows occurrence) ↔
      ContextualConditionalRows.Matches initial.locals initial.state.declarations
        (Assignment.compose candidate (change (LiveFiring.execution accepted))) pattern (initial.state.rows occurrence) := by
  apply state_matches_retained (LiveFiring.execution accepted) candidate
  rwa [(LiveFiring.execution_data accepted).2.1]

theorem witness_matches_retained {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) {target : Frames.Frame S}
    (candidate : Assignment last.state.declarations target.arity) (occurrence : O)
    (notMade : ∀ firing ∈ front, occurrence ∉ firing.selection.made)
    (pattern : Term (signature S target.arity) Γ sort) :
    ContextualConditionalRows.Matches last.locals last.state.declarations candidate pattern (last.state.rows occurrence) ↔
      ContextualConditionalRows.Matches initial.locals initial.state.declarations
        (Assignment.compose candidate (changes witness)) pattern (initial.state.rows occurrence) := by
  induction witness with
  | nil =>
      rw [changes, Assignment.compose_identity_right]
  | @cons initial first rest accepted last tail ih =>
      have laterNotMade : ∀ firing ∈ rest.map (residualAfter accepted), occurrence ∉ firing.selection.made := by
        intro firing member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact notMade original (List.mem_cons_of_mem first inside)
      refine (ih candidate laterNotMade).trans ?_
      have step := actual_matches_retained accepted (Assignment.compose candidate (changes tail))
        (notMade first List.mem_cons_self) pattern
      refine step.trans (Iff.of_eq ?_)
      exact congrArg (fun assignment => ContextualConditionalRows.Matches initial.locals initial.state.declarations
        assignment pattern (initial.state.rows occurrence)) (Assignment.compose_associative _ _ _).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketResultModels
