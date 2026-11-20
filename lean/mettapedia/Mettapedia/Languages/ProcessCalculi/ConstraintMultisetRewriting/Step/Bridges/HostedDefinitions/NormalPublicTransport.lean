import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgramFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalFrameTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowRuns

/-!
# The new public query and its complete native frontier

The source program and entry here are the general-normal profile, including
its real done-payload bind. Scope and arrow licences are discharged on that
program. The existing correspondence then preserves every reached bag of
reading sets and reflects controller termination. This does not yet identify
those answers with the package's directed normal forms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalPublicTransport

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

theorem initial_step (term : Tower.Tm 0) :
    SourceLanguage.Step D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built term))
      (ContinuationLift.configuration (PublicQuery.frame RuntimeSubstitution.rules built.authored)
        (BinderCore.start built.rules (NormalProgram.code term))) := by
  have live : Solvable ([] : List (Constraint (BinderCore.keys built.rules) [] ())) :=
    ⟨Empty, ProgramBinders.ground MSig, ProgramBinders.close (fam (BinderCore.keys built.rules)),
      fun _ inside => False.elim (List.not_mem_nil inside)⟩
  have moved := Move.letStart (D := D) (P := NormalProgram.program built D) (supply := supply)
    (⟨0, 0, fun _ => 0⟩ : World (BinderCore.keys built.rules) [] ()) []
    (PublicQuery.site RuntimeSubstitution.rules built.authored)
    (PublicReadout.pattern (PublicQuery.result RuntimeSubstitution.rules built.authored))
    (.apply (Rigid.includeTerm (fam (BinderCore.keys built.rules)) (NormalProgram.code term)))
    (.ret (PublicQuery.result RuntimeSubstitution.rules built.authored)) [] []
  have one := SourceLanguage.Step.move (D := D) (P := NormalProgram.program built D)
    (supply := supply) _ _ _ 0 _ live moved
  simpa [Config.initial, NormalProgram.query, PublicQuery.query, PublicQuery.frame,
    BinderCore.start, ContinuationLift.configuration, ContinuationLift.branch,
    Compiled.rules, PublicQuery.keys, PublicQuery.rows] using one

theorem runs_inside (term : Tower.Tm 0) {after : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply
      (BinderCore.start built.rules (NormalProgram.code term)) after) :
    Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built term))
      (ContinuationLift.configuration (PublicQuery.frame RuntimeSubstitution.rules built.authored) after) := by
  apply (Relation.ReflTransGen.single (initial_step built D supply term)).trans
  apply NormalFrameTransport.runs D (NormalProgram.program built D) supply
    (NormalProgramFormation.program_arrows built D)
  · intro before member
    rw [Multiset.mem_singleton.mp member]
    exact ⟨trivial, .inl ⟨_, rfl, trivial⟩⟩
  · exact executed

variable (N : Nodes MSig [] ())

theorem prefixes_iff (term : Tower.Tm 0) (post : Multiset (Set MClosed) → Prop) :
    (∃ after, Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built term)) after ∧
      post (after.answers (D := D))) ↔
      ∃ next, (FrontierArrow.target (D := D) N (NormalProgram.program built D)).MultiStep
        (FrontierArrow.initialState (D := D) N (NormalProgram.program built D)
          (NormalProgram.query built term)) next ∧ post (FrontierArrow.answers N next) :=
  FrontierArrow.prefixes_iff (D := D) N (NormalProgram.program built D) supply (fun _ => 0)
    (NormalProgram.query built term) (NormalProgramFormation.equations_formed built D)
    (NormalProgramFormation.query_scoped built term) (NormalProgramFormation.query_distinct built term)
    (NormalProgramFormation.query_arrows built term) post

theorem normalization_iff (term : Tower.Tm 0) :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after)
      (Config.initial (fun _ => 0) (NormalProgram.query built term)) ↔
      Acc (fun next before => (FrontierArrow.target (D := D) N (NormalProgram.program built D)).Step before next)
        (FrontierArrow.initialState (D := D) N (NormalProgram.program built D)
          (NormalProgram.query built term)) := by
  have initial := FrontierArrow.initial_related (D := D) N (NormalProgram.program built D) supply
    (fun _ => 0) (NormalProgram.query built term) (NormalProgramFormation.query_arrows built term)
    (query_unopened (NormalProgramFormation.query_scoped built term)
      (NormalProgramFormation.query_distinct built term) (NormalProgramFormation.query_arrows built term))
  exact FrontierArrow.normalization_iff (D := D) N (NormalProgram.program built D) supply (fun _ => 0)
    (NormalProgram.query built term) (NormalProgramFormation.equations_formed built D)
    (NormalProgramFormation.query_scoped built term) (NormalProgramFormation.query_distinct built term)
    (NormalProgramFormation.query_arrows built term) initial

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalPublicTransport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalPublicTransport.runs_inside
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalPublicTransport.prefixes_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalPublicTransport.normalization_iff
