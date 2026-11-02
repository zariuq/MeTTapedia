import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformation

/-!
# Joint common-frame information and prefix-local guards

The conjunction of the transported incoming equations and all catalogue
prefix problems has exactly the final endpoint's models, in every later
declaration family. Enumerating catalogue entries differently preserves that
joint information. Guard acceptance nevertheless uses each entry's original
problem and world, not this final conjunction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion

variable {S : Signature} {Local O V Future : Type} {locals : Local → MetaArity S}
  {declarations : V → MetaArity S} {future : Future → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

def jointProblem (incoming : EquationStore (Term (signature S declarations) Γ sort))
    (catalogue : List (Event locals (O := O) declarations Γ sort)) :
    EquationStore (Term (signature S declarations) Γ sort) := incoming ++ catalogue.flatMap Event.problem

theorem models_joint_iff (incoming : EquationStore (Term (signature S declarations) Γ sort))
    (catalogue : List (Event locals (O := O) declarations Γ sort))
    (candidate : Assignment declarations future) :
    ContextualFrameUnifier.Models candidate (jointProblem incoming catalogue) ↔
      ContextualFrameUnifier.Models candidate incoming ∧
        ∀ event ∈ catalogue, ContextualFrameUnifier.Models candidate event.problem := by
  rw [jointProblem, ContextualFrameUnifier.models_append]
  apply and_congr_right
  intro _incoming
  constructor
  · intro all event present equation member
    exact all equation (List.mem_flatMap.mpr ⟨event, present, member⟩)
  · intro all equation member
    obtain ⟨event, present, member⟩ := List.mem_flatMap.mp member
    exact all event present equation member

theorem joint_problem_perm (incoming : EquationStore (Term (signature S declarations) Γ sort))
    {catalogue reordered : List (Event locals (O := O) declarations Γ sort)}
    (perm : catalogue.Perm reordered) :
    ContextualInformation.Equivalent (jointProblem incoming catalogue) (jointProblem incoming reordered) := by
  constructor <;> intro Later later candidate models
  · obtain ⟨initial, all⟩ := (models_joint_iff incoming catalogue candidate).mp models
    exact (models_joint_iff incoming reordered candidate).mpr
      ⟨initial, fun event member => all event (perm.symm.subset member)⟩
  · obtain ⟨initial, all⟩ := (models_joint_iff incoming reordered candidate).mp models
    exact (models_joint_iff incoming catalogue candidate).mpr
      ⟨initial, fun event member => all event (perm.subset member)⟩

variable [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem final_model_satisfies_each_prefix {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target)
    (candidate : Assignment target.declarations future)
    (models : ContextualFrameUnifier.Models candidate target.inventory.configuration.equations) :
    ∀ event ∈ events certificate, ContextualFrameUnifier.Models candidate event.problem := by
  induction certificate with
  | nil => intro event member; cases member
  | snoc past next earlier =>
      intro event member
      rcases List.mem_append.mp member with old | last
      · obtain ⟨original, present, rfl⟩ := List.mem_map.mp old
        apply (ContextualFrameUnifier.models_mapProblem
          (ContextualProcessTransport.captureExtension next).assignment candidate original.problem).mpr
        exact earlier (Assignment.compose candidate (ContextualProcessTransport.captureExtension next).assignment)
          (ContextualProcessTransport.prepared_models_refine next candidate models) original present
      · obtain rfl := List.mem_singleton.mp last
        exact models

def incomingProblem {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    EquationStore (Term (signature S target.declarations) Γ sort) :=
  ContextualFrameUnifier.mapProblem (ContextualProcessTransport.assignment certificate)
    source.inventory.configuration.equations

theorem joint_models_iff_final {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) (candidate : Assignment target.declarations future) :
    ContextualFrameUnifier.Models candidate (jointProblem (incomingProblem certificate) (events certificate)) ↔
      ContextualFrameUnifier.Models candidate target.inventory.configuration.equations := by
  constructor
  · intro joint
    obtain ⟨incoming, prefixes⟩ := (models_joint_iff _ _ candidate).mp joint
    cases certificate with
    | nil =>
        have original := (ContextualFrameUnifier.models_mapProblem _ candidate _).mp incoming
        change ContextualFrameUnifier.Models (Assignment.compose candidate (generator source.declarations)) _ at original
        rw [Assignment.compose_identity_right] at original
        exact original
    | snoc past next =>
        exact prefixes (preparedEvent next) (List.mem_append_right _ (List.mem_singleton_self _))
  · intro final
    apply (models_joint_iff _ _ candidate).mpr
    exact ⟨(ContextualFrameUnifier.models_mapProblem _ candidate _).mpr
      (ContextualProcessTransport.assignment_models_refine certificate candidate final),
      final_model_satisfies_each_prefix certificate candidate final⟩

theorem joint_information_equivalent {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    ContextualInformation.Equivalent (jointProblem (incomingProblem certificate) (events certificate))
      target.inventory.configuration.equations := by
  constructor <;> intro Later later candidate model
  · exact (joint_models_iff_final certificate candidate).mp model
  · exact (joint_models_iff_final certificate candidate).mpr model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
