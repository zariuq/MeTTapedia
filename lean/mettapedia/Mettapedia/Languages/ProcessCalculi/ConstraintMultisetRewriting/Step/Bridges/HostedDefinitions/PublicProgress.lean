import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ConfigProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.FramedProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NativePublic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.MachineProgress

/-!
# Administrative termination through the actual public query

Ground equation execution terminates beneath the real public bind. The
existing whole-frontier correspondence then transports this result to the
native controller. The rule-dependency licence is explicit and separate from
closed-machine termination; it must be checked on a concrete program.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality
open SourceLanguage SourceLanguage.Elaboration Hosting
open PublicQuery (rows keys query)

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable (helpers authored : List ProgramLayout.Rule) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

theorem source_normalizes (grounded : ∀ rule ∈ rows helpers authored, GroundRead.Grounding rule)
    (call : MClosed)
    (normalizing : Acc (fun after before => ProgramBinders.Rewrites (rows helpers authored).get before after) call) :
    Acc (fun after before => SourceLanguage.Step D (BinderCore.program (rows helpers authored)) supply before after)
      (Config.initial (fun _ => 0) (query helpers authored call)) := by
  apply ConfigProgress.ready_normalizes (rows helpers authored) D supply
  intro branch member _
  rw [Multiset.mem_singleton.mp member]
  refine Acc.intro _ ?_
  rintro child ⟨_, world, nextWorld, children, moved, member, _⟩
  cases moved with
  | letStart =>
      rw [Multiset.mem_singleton.mp member]
      apply FramedProgress.call_normalizes (rows helpers authored) D supply grounded call normalizing
      constructor
      · exact ⟨Empty, ProgramBinders.ground MSig,
          ProgramBinders.close (fam (keys helpers authored)),
          fun _ absent => False.elim (List.not_mem_nil absent)⟩
      · intro X target assignment _
        exact Rigid.instantiate_include assignment call

include supply

theorem native_normalizes (N : Nodes MSig [] ())
    (grounded : ∀ rule ∈ rows helpers authored, GroundRead.Grounding rule) (call : MClosed)
    (normalizing : Acc (fun after before => ProgramBinders.Rewrites (rows helpers authored).get before after) call) :
    Acc (fun after before => (FrontierArrow.target (D := D) N (BinderCore.program (rows helpers authored))).Step before after)
      (FrontierArrow.initialState (D := D) N (BinderCore.program (rows helpers authored))
        (query helpers authored call)) := by
  have sourceAcc := source_normalizes helpers authored D supply grounded call normalizing
  have initial := FrontierArrow.initial_related (D := D) N (BinderCore.program (rows helpers authored))
    supply (fun _ => 0) (query helpers authored call) (PublicQuery.query_arrows helpers authored call)
    (query_unopened (PublicQuery.query_scoped helpers authored call) (PublicQuery.query_distinct helpers authored call)
      (PublicQuery.query_arrows helpers authored call))
  exact (FrontierArrow.normalization_iff (D := D) N (BinderCore.program (rows helpers authored)) supply
    (fun _ => 0) (query helpers authored call) (ProgramScope.equations (rows helpers authored) D)
    (PublicQuery.query_scoped helpers authored call) (PublicQuery.query_distinct helpers authored call)
    (PublicQuery.query_arrows helpers authored call) initial).mp sourceAcc

theorem compiled_native_normalizes {dev : NativeTypesOnTheStep.Computing.Definitions.Development}
    (built : Compiled dev) (N : Nodes MSig [] ())
    (grounded : ∀ rule ∈ built.rules, GroundRead.Grounding rule) (term : Tower.Tm 0)
    (normalizing : Acc (fun after before => StrongNormalization.Reduces
      (NativeTypesOnTheStep.Computing.Definitions.devPackage dev built.nativeRows) before after) term) :
    Acc (fun after before => (FrontierArrow.target (D := D) N (BinderCore.program built.rules)).Step before after)
      (FrontierArrow.initialState (D := D) N (BinderCore.program built.rules)
        (query RuntimeSubstitution.rules built.authored (queryCode term))) :=
  native_normalizes RuntimeSubstitution.rules built.authored D supply N grounded (queryCode term)
    (MachineProgress.evaluate_normalizes built term normalizing)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicProgress.compiled_native_normalizes
