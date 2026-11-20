import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramScope
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowRuns

/-!
# The public hosted query reaches the existing native frontier

The actual source program's scope clauses and public query supply the
premises of the established whole-frontier correspondence. The observation
here is membership in its bag of reading sets; no multiplicity of native
reduction strategies is identified with that bag.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NativePublic

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration Hosting
open PublicQuery (rows keys query)

def Contains (bag : Multiset (Set MClosed)) (value : MClosed) : Prop :=
  ∃ answers ∈ bag, value ∈ answers

theorem has_answer_iff {D : Discipline MSig [] ()}
    (sourceRows : List (ProgramBinders.Equation MSig [] ()))
    (configuration : Config (BinderCore.keys sourceRows) [] () D.Ty) (value : MClosed) :
    HasAnswer (D := D) sourceRows configuration value ↔ Contains (configuration.answers (D := D)) value := by
  classical
  constructor
  · rintro ⟨branch, member, finished, read⟩
    have live : Solvable branch.store := by
      obtain ⟨term, _, X, family, assignment, solved, _⟩ := read
      exact ⟨X, family, assignment, solved⟩
    exact ⟨branch.answer (D := D), Multiset.mem_map.mpr
      ⟨branch, Multiset.mem_filter.mpr ⟨member, finished, live⟩, rfl⟩, read⟩
  · rintro ⟨answers, member, read⟩
    unfold Config.answers at member
    have found : ∃ branch : Branch (BinderCore.keys sourceRows) [] () D.Ty,
        branch ∈ configuration.branches.filter (fun branch => branch.Finished (D := D) ∧ Solvable branch.store) ∧
        branch.answer (D := D) = answers := Multiset.mem_map.mp member
    obtain ⟨branch, filtered, same⟩ := found
    obtain ⟨inside, finished, _⟩ := Multiset.mem_filter.mp filtered
    exact ⟨branch, inside, finished, same.symm ▸ read⟩

variable (helpers authored : List ProgramLayout.Rule) (D : Discipline MSig [] ())
  (N : Nodes MSig [] ()) (supply : Nat → MClosed)
  (separated : HeadSeparated (rows helpers authored) activeTag doneTag)

include separated supply

theorem public_answers_by_native (call value : MClosed)
    (initialHead : closedHead call = some activeTag ∨ closedHead call = some doneTag) :
    PublicInvariant.Reach helpers authored call (doneC value) ↔
      ∃ next, (FrontierArrow.target (D := D) N (BinderCore.program (rows helpers authored))).MultiStep
        (FrontierArrow.initialState (D := D) N (BinderCore.program (rows helpers authored))
          (query helpers authored call)) next ∧ Contains (FrontierArrow.answers N next) value := by
  constructor
  · intro reached
    obtain ⟨configuration, sourceRun, answered⟩ :=
      (PublicAnswers.public_answers_iff helpers authored D supply separated call value initialHead).mp reached
    obtain ⟨next, nativeRun, _, same⟩ := FrontierArrow.source_run (D := D) N
      (BinderCore.program (rows helpers authored)) supply (fun _ => 0) (query helpers authored call)
      (ProgramScope.equations (rows helpers authored) D)
      (PublicQuery.query_scoped helpers authored call) (PublicQuery.query_distinct helpers authored call)
      (PublicQuery.query_arrows helpers authored call) sourceRun
    exact ⟨next, nativeRun, same ▸ (has_answer_iff (rows helpers authored) configuration value).mp answered⟩
  · rintro ⟨next, nativeRun, answered⟩
    obtain ⟨configuration, sourceRun, _, same⟩ := FrontierArrow.target_run (D := D) N
      (BinderCore.program (rows helpers authored)) supply (fun _ => 0) (query helpers authored call)
      (ProgramScope.equations (rows helpers authored) D)
      (PublicQuery.query_scoped helpers authored call) (PublicQuery.query_distinct helpers authored call)
      (PublicQuery.query_arrows helpers authored call) nativeRun
    exact (PublicAnswers.public_answers_iff helpers authored D supply separated call value initialHead).mpr
      ⟨configuration, sourceRun,
        (has_answer_iff (rows helpers authored) configuration value).mpr (same.symm ▸ answered)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NativePublic

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NativePublic.public_answers_by_native
