import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIteratedJoint

/-!
# One symbolic information frame for a finite native family

Captured state names occur once. Each member receives its own copy of the
native activation locals, including the locals used by schema activation and
latent row obligations. The common problem is the actual native information
of every member, mapped through these inclusions.

The comparison concerns solutions at every target frame. It neither chooses
a ground reading nor adds an admission or execution conclusion to its data.
Residual cuts and published-result transport are separate from the initial
family and its subfamilies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.FamilyInformation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

def memberInformation {s : NativeState S O Γ sort} (member : LiveFiring s) :=
  NativeResidual.problemOf s member.selection member.rule

def familyFrame (s : NativeState S O Γ sort) (count : Nat) : Frames.Frame S :=
  ⟨(Fin count × ScopedVar s.Local) ⊕ s.state.Names,
    Sum.elim (fun name => s.locals name.2.name) s.state.declarations⟩

def sharedInclusion (s : NativeState S O Γ sort) (count : Nat) :
    Assignment s.state.declarations (familyFrame s count).arity :=
  fun name => generator (familyFrame s count).arity (.inr name)

def memberInclusion (s : NativeState S O Γ sort) {count : Nat} (index : Fin count) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations) (familyFrame s count).arity
  | .inl name => generator (familyFrame s count).arity (.inl (index,name))
  | .inr name => generator (familyFrame s count).arity (.inr name)

def sharedRestriction {s : NativeState S O Γ sort} {count : Nat} {b : Frames.Frame S}
    (candidate : Assignment (familyFrame s count).arity b.arity) : Assignment s.state.declarations b.arity :=
  Assignment.compose candidate (sharedInclusion s count)

def memberRestriction {s : NativeState S O Γ sort} {count : Nat} {b : Frames.Frame S}
    (candidate : Assignment (familyFrame s count).arity b.arity) (index : Fin count) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity :=
  Assignment.compose candidate (memberInclusion s index)

theorem restrictions_agree {s : NativeState S O Γ sort} {count : Nat} {b : Frames.Frame S}
    (candidate : Assignment (familyFrame s count).arity b.arity) (index : Fin count) :
    Assignment.compose (memberRestriction candidate index)
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = sharedRestriction candidate := by
  funext name
  exact instantiate_generator (memberRestriction candidate index) (.inr name)

def information (s : NativeState S O Γ sort) (members : List (LiveFiring s)) :
    ContextualResidual.Problem (familyFrame s members.length).arity :=
  (List.finRange members.length).flatMap fun index =>
    ContextualResidual.mapProblem (memberInclusion s index) (memberInformation (members[index]))

theorem models_information {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    {b : Frames.Frame S} (candidate : Assignment (familyFrame s members.length).arity b.arity) :
    ContextualResidual.Models candidate (information s members) ↔
      ∀ index : Fin members.length,
        ContextualResidual.Models (memberRestriction candidate index) (memberInformation (members[index])) := by
  constructor
  · intro solved index
    apply (ContextualResidual.models_mapProblem (memberInclusion s index) candidate _).mp
    intro equation present
    exact solved equation (List.mem_flatMap.mpr ⟨index,by simp,present⟩)
  · intro each equation present
    obtain ⟨index,_,inside⟩ := List.mem_flatMap.mp present
    exact (ContextualResidual.models_mapProblem (memberInclusion s index) candidate _).mpr (each index) equation inside

structure SolutionData (s : NativeState S O Γ sort) (members : List (LiveFiring s)) (b : Frames.Frame S) where
  shared : Assignment s.state.declarations b.arity
  member : (index : Fin members.length) →
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity
  agrees : ∀ index, Assignment.compose (member index)
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = shared
  models : ∀ index, ContextualResidual.Models (member index) (memberInformation (members[index]))

theorem SolutionData.ext_data {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    {b : Frames.Frame S} {first second : SolutionData s members b}
    (shared : first.shared = second.shared) (member : first.member = second.member) : first = second := by
  cases first
  cases second
  cases shared
  cases member
  rfl

def assemble {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {b : Frames.Frame S}
    (data : SolutionData s members b) : Assignment (familyFrame s members.length).arity b.arity
  | .inl (index,name) => data.member index (.inl name)
  | .inr name => data.shared name

theorem assemble_shared {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {b : Frames.Frame S}
    (data : SolutionData s members b) : sharedRestriction (assemble data) = data.shared := by
  funext name
  exact instantiate_generator (assemble data) (.inr name)

theorem assemble_member {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {b : Frames.Frame S}
    (data : SolutionData s members b) (index : Fin members.length) :
    memberRestriction (assemble data) index = data.member index := by
  funext name
  cases name with
  | inl name => exact instantiate_generator (assemble data) (.inl (index,name))
  | inr name =>
      have agrees := congrFun (data.agrees index) name
      change instantiate (data.member index)
        (generator (ContextualActivatedStep.target s.locals s.state.declarations) (.inr name)) = data.shared name at agrees
      rw [instantiate_generator] at agrees
      exact (instantiate_generator (assemble data) (.inr name)).trans agrees.symm

theorem assemble_models {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {b : Frames.Frame S}
    (data : SolutionData s members b) : ContextualResidual.Models (assemble data) (information s members) := by
  apply (models_information (assemble data)).mpr
  intro index
  rw [assemble_member]
  exact data.models index

def extract {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {b : Frames.Frame S}
    (candidate : Assignment (familyFrame s members.length).arity b.arity)
    (solved : ContextualResidual.Models candidate (information s members)) : SolutionData s members b where
  shared := sharedRestriction candidate
  member := memberRestriction candidate
  agrees := restrictions_agree candidate
  models := (models_information candidate).mp solved

theorem assemble_extract {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {b : Frames.Frame S}
    (candidate : Assignment (familyFrame s members.length).arity b.arity)
    (solved : ContextualResidual.Models candidate (information s members)) :
    assemble (extract candidate solved) = candidate := by
  funext name
  cases name with
  | inl name => exact instantiate_generator candidate (.inl name)
  | inr name => exact instantiate_generator candidate (.inr name)

def solutionEquiv (s : NativeState S O Γ sort) (members : List (LiveFiring s)) (b : Frames.Frame S) :
    {candidate : Assignment (familyFrame s members.length).arity b.arity //
      ContextualResidual.Models candidate (information s members)} ≃ SolutionData s members b where
  toFun candidate := extract candidate.val candidate.property
  invFun data := ⟨assemble data,assemble_models data⟩
  left_inv candidate := Subtype.ext (assemble_extract candidate.val candidate.property)
  right_inv data := SolutionData.ext_data (assemble_shared data) (funext (assemble_member data))

section Native

theorem memberInformation_eq_native {s : NativeState S O Γ sort} (member : LiveFiring s) :
    memberInformation member = member.toNative.information := rfl

theorem jointly_iff_solvable (s : NativeState S O Γ sort) (members : List (LiveFiring s)) :
    NativeIterated.Jointly s members ↔
      (Frames.contextual S).Solvable (a := familyFrame s members.length) (information s members) := by
  constructor
  · rintro ⟨b,shared,each⟩
    have indexed : ∀ index : Fin members.length,
        ∃ candidate : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity,
          ContextualResidual.Models candidate (members[index]).toNative.information ∧
          Assignment.compose candidate (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = shared :=
      fun index => each (members[index]) (List.getElem_mem ..)
    choose member models agrees using indexed
    let data : SolutionData s members b := ⟨shared,member,agrees,models⟩
    exact ⟨b,assemble data,assemble_models data⟩
  · rintro ⟨b,candidate,solved⟩
    let data := extract candidate solved
    refine ⟨b,data.shared,fun firing present => ?_⟩
    obtain ⟨index,inside,equal⟩ := List.getElem_of_mem present
    have model := data.models ⟨index,inside⟩
    change ContextualResidual.Models (data.member ⟨index,inside⟩) (memberInformation (members[index])) at model
    rw [equal] at model
    exact ⟨data.member ⟨index,inside⟩,model,data.agrees ⟨index,inside⟩⟩

end Native

def reindex (s : NativeState S O Γ sort) {count other : Nat} (pick : Fin other → Fin count) :
    Assignment (familyFrame s other).arity (familyFrame s count).arity
  | .inl (index,name) => generator (familyFrame s count).arity (.inl (pick index,name))
  | .inr name => generator (familyFrame s count).arity (.inr name)

theorem reindex_member (s : NativeState S O Γ sort) {count other : Nat}
    (pick : Fin other → Fin count) (index : Fin other) :
    Assignment.compose (reindex s pick) (memberInclusion s index) = memberInclusion s (pick index) := by
  funext name
  cases name <;> exact instantiate_generator (reindex s pick) _

theorem reindex_shared (s : NativeState S O Γ sort) {count other : Nat} (pick : Fin other → Fin count) :
    Assignment.compose (reindex s pick) (sharedInclusion s other) = sharedInclusion s count := by
  funext name
  exact instantiate_generator (reindex s pick) _

theorem restrict_models {s : NativeState S O Γ sort} {members subfamily : List (LiveFiring s)}
    (pick : Fin subfamily.length → Fin members.length)
    (reads : ∀ index, subfamily[index] = members[pick index]) {b : Frames.Frame S}
    (candidate : Assignment (familyFrame s members.length).arity b.arity)
    (solved : ContextualResidual.Models candidate (information s members)) :
    ContextualResidual.Models (Assignment.compose candidate (reindex s pick)) (information s subfamily) := by
  apply (models_information _).mpr
  intro index
  have composed : memberRestriction (Assignment.compose candidate (reindex s pick)) index =
      memberRestriction candidate (pick index) := by
    funext name
    cases name with
    | inl name => exact instantiate_generator (Assignment.compose candidate (reindex s pick)) (.inl (index,name))
    | inr name => exact instantiate_generator (Assignment.compose candidate (reindex s pick)) (.inr name)
  rw [composed,reads index]
  exact (models_information candidate).mp solved (pick index)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.FamilyInformation
