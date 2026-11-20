import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformation

/-!
# Target instantiation of actual native family solutions

The all-target family equivalence commutes with contextual assignment
composition. Shared captures and each positional private copy are transported
through their actual terms. Model transport is forward; an instantiation need
not reflect equations or preserve inequalities. Source-state and residual transport,
admission, compatibility and round execution remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.InformationNaturality

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open FamilyInformation

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}
  {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
  {b c d : Frames.Frame S}

abbrev Solutions (s : NativeState S O Γ sort) (members : List (LiveFiring s)) (b : Frames.Frame S) :=
  {candidate : Assignment (familyFrame s members.length).arity b.arity //
    ContextualResidual.Models candidate (information s members)}

def postSolution (post : Assignment b.arity c.arity) (candidate : Solutions s members b) : Solutions s members c :=
  ⟨Assignment.compose post candidate.val, ContextualResidual.models_compose candidate.property post⟩

def postData (post : Assignment b.arity c.arity) (data : SolutionData s members b) : SolutionData s members c where
  shared := Assignment.compose post data.shared
  member index := Assignment.compose post (data.member index)
  agrees index := by
    calc
      _ = Assignment.compose post (Assignment.compose (data.member index)
          (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)) :=
        (Assignment.compose_associative _ _ _).symm
      _ = Assignment.compose post data.shared := congrArg (Assignment.compose post) (data.agrees index)
  models index := ContextualResidual.models_compose (data.models index) post

theorem sharedRestriction_post {count : Nat} (post : Assignment b.arity c.arity)
    (candidate : Assignment (familyFrame s count).arity b.arity) :
    sharedRestriction (Assignment.compose post candidate) =
      Assignment.compose post (sharedRestriction candidate) :=
  (Assignment.compose_associative (sharedInclusion s count) candidate post).symm

theorem memberRestriction_post {count : Nat} (post : Assignment b.arity c.arity)
    (candidate : Assignment (familyFrame s count).arity b.arity) (index : Fin count) :
    memberRestriction (Assignment.compose post candidate) index =
      Assignment.compose post (memberRestriction candidate index) :=
  (Assignment.compose_associative (memberInclusion s index) candidate post).symm

theorem assemble_postData (post : Assignment b.arity c.arity) (data : SolutionData s members b) :
    assemble (postData post data) = Assignment.compose post (assemble data) := by
  funext name
  cases name <;> rfl

theorem extract_post (post : Assignment b.arity c.arity)
    (candidate : Assignment (familyFrame s members.length).arity b.arity)
    (solved : ContextualResidual.Models candidate (information s members)) :
    extract (Assignment.compose post candidate) (ContextualResidual.models_compose solved post) =
      postData post (extract candidate solved) := by
  apply SolutionData.ext_data
  · exact sharedRestriction_post post candidate
  · funext index
    exact memberRestriction_post post candidate index

theorem solutionEquiv_natural (post : Assignment b.arity c.arity) (candidate : Solutions s members b) :
    solutionEquiv s members c (postSolution post candidate) =
      postData post (solutionEquiv s members b candidate) :=
  extract_post post candidate.val candidate.property

theorem postData_identity (data : SolutionData s members b) :
    postData (generator b.arity) data = data := by
  apply SolutionData.ext_data
  · exact Assignment.compose_identity_left data.shared
  · funext index
    exact Assignment.compose_identity_left (data.member index)

theorem postData_compose (first : Assignment b.arity c.arity) (second : Assignment c.arity d.arity)
    (data : SolutionData s members b) :
    postData second (postData first data) = postData (Assignment.compose second first) data := by
  apply SolutionData.ext_data
  · exact Assignment.compose_associative data.shared first second
  · funext index
    exact Assignment.compose_associative (data.member index) first second

theorem postSolution_identity (candidate : Solutions s members b) :
    postSolution (generator b.arity) candidate = candidate :=
  Subtype.ext (Assignment.compose_identity_left candidate.val)

theorem postSolution_compose (first : Assignment b.arity c.arity) (second : Assignment c.arity d.arity)
    (candidate : Solutions s members b) :
    postSolution second (postSolution first candidate) =
      postSolution (Assignment.compose second first) candidate :=
  Subtype.ext (Assignment.compose_associative candidate.val first second)

section Restriction

variable {subfamily : List (LiveFiring s)}

/-- An arbitrary coordinate reindexing. A noninjective pick is a diagonal
specialization, not a faithful subfamily cut. -/
def restrictSolution (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) (candidate : Solutions s members b) :
    Solutions s subfamily b :=
  ⟨Assignment.compose candidate.val (reindex s pick), restrict_models pick reads candidate.val candidate.property⟩

def restrictData (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) (data : SolutionData s members b) :
    SolutionData s subfamily b where
  shared := data.shared
  member index := data.member (pick index)
  agrees index := data.agrees (pick index)
  models index := by
    rw [reads index]
    exact data.models (pick index)

theorem sharedRestriction_reindex (pick : Fin subfamily.length → Fin members.length)
    (candidate : Assignment (familyFrame s members.length).arity b.arity) :
    sharedRestriction (Assignment.compose candidate (reindex s pick)) = sharedRestriction candidate := by
  change Assignment.compose (Assignment.compose candidate (reindex s pick)) (sharedInclusion s subfamily.length) = _
  rw [← Assignment.compose_associative, reindex_shared]
  rfl

theorem memberRestriction_reindex (pick : Fin subfamily.length → Fin members.length)
    (candidate : Assignment (familyFrame s members.length).arity b.arity) (index : Fin subfamily.length) :
    memberRestriction (Assignment.compose candidate (reindex s pick)) index = memberRestriction candidate (pick index) := by
  change Assignment.compose (Assignment.compose candidate (reindex s pick)) (memberInclusion s index) = _
  rw [← Assignment.compose_associative, reindex_member]
  rfl

theorem extract_restrict (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) (candidate : Solutions s members b) :
    extract (restrictSolution pick reads candidate).val (restrictSolution pick reads candidate).property =
      restrictData pick reads (extract candidate.val candidate.property) := by
  apply SolutionData.ext_data
  · exact sharedRestriction_reindex pick candidate.val
  · funext index
    exact memberRestriction_reindex pick candidate.val index

theorem solutionEquiv_restrict (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) (candidate : Solutions s members b) :
    solutionEquiv s subfamily b (restrictSolution pick reads candidate) =
      restrictData pick reads (solutionEquiv s members b candidate) := extract_restrict pick reads candidate

theorem assemble_restrictData (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) (data : SolutionData s members b) :
    assemble (restrictData pick reads data) = Assignment.compose (assemble data) (reindex s pick) := by
  funext name
  cases name with
  | inl name => exact (instantiate_generator (assemble data) (.inl (pick name.1, name.2))).symm
  | inr name => exact (instantiate_generator (assemble data) (.inr name)).symm

theorem restrictData_post (post : Assignment b.arity c.arity)
    (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) (data : SolutionData s members b) :
    restrictData pick reads (postData post data) = postData post (restrictData pick reads data) := by
  apply SolutionData.ext_data <;> rfl

theorem restrictSolution_post (post : Assignment b.arity c.arity)
    (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) (candidate : Solutions s members b) :
    restrictSolution pick reads (postSolution post candidate) =
      postSolution post (restrictSolution pick reads candidate) :=
  Subtype.ext (Assignment.compose_associative (reindex s pick) candidate.val post).symm

end Restriction

/-- A genuine cut selects distinct original positions. Equal member values
at distinct positions are permitted. No solution-extension law is assumed. -/
structure Cut (members subfamily : List (LiveFiring s)) where
  pick : Fin subfamily.length → Fin members.length
  injective : Function.Injective pick
  reads : ∀ index, subfamily[index] = members[pick index]

def ownCut (index : Fin members.length) : Cut members [members[index]] where
  pick _ := index
  injective first second _ := by
    apply Fin.ext
    have firstBound := first.isLt
    have secondBound := second.isLt
    change first.val < 1 at firstBound
    change second.val < 1 at secondBound
    omega
  reads position := by fin_cases position; rfl

def pairCut (first second : Fin members.length) (different : first ≠ second) :
    Cut members [members[first], members[second]] where
  pick index := if index.val = 0 then first else second
  injective left right same := by
    fin_cases left <;> fin_cases right
    · rfl
    · exact False.elim (different same)
    · exact False.elim (different same.symm)
    · rfl
  reads position := by fin_cases position <;> rfl

namespace Cut

variable {subfamily : List (LiveFiring s)}

def solution (cut : Cut members subfamily) (candidate : Solutions s members b) : Solutions s subfamily b :=
  restrictSolution cut.pick cut.reads candidate

def data (cut : Cut members subfamily) (candidate : SolutionData s members b) : SolutionData s subfamily b :=
  restrictData cut.pick cut.reads candidate

theorem solution_post (cut : Cut members subfamily) (post : Assignment b.arity c.arity)
    (candidate : Solutions s members b) :
    cut.solution (postSolution post candidate) = postSolution post (cut.solution candidate) :=
  restrictSolution_post post cut.pick cut.reads candidate

theorem data_post (cut : Cut members subfamily) (post : Assignment b.arity c.arity)
    (candidate : SolutionData s members b) : cut.data (postData post candidate) = postData post (cut.data candidate) :=
  restrictData_post post cut.pick cut.reads candidate

theorem solutionEquiv (cut : Cut members subfamily) (candidate : Solutions s members b) :
    FamilyInformation.solutionEquiv s subfamily b (cut.solution candidate) =
      cut.data (FamilyInformation.solutionEquiv s members b candidate) :=
  solutionEquiv_restrict cut.pick cut.reads candidate

end Cut

/-- The own/pair cut reads the actual native models and their shared
capture agreement, without passing through a first-order projection. -/
def jointAt (data : SolutionData s members b) (first second : Fin members.length) :
    NativeResidual.Joint s (memberInformation (members[first])) (memberInformation (members[second])) b where
  left := data.member first
  right := data.member second
  left_models := data.models first
  right_models := data.models second
  agree := (data.agrees first).trans (data.agrees second).symm

def postJoint {left right : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)}
    (post : Assignment b.arity c.arity) (joint : NativeResidual.Joint s left right b) :
    NativeResidual.Joint s left right c where
  left := Assignment.compose post joint.left
  right := Assignment.compose post joint.right
  left_models := ContextualResidual.models_compose joint.left_models post
  right_models := ContextualResidual.models_compose joint.right_models post
  agree := (Assignment.compose_associative _ _ _).symm.trans
    ((congrArg (Assignment.compose post) joint.agree).trans (Assignment.compose_associative _ _ _))

theorem jointAt_postData (post : Assignment b.arity c.arity) (data : SolutionData s members b)
    (first second : Fin members.length) :
    jointAt (postData post data) first second = postJoint post (jointAt data first second) := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.InformationNaturality
