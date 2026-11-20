import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalGroundingCompiled

/-!
# Directed normalization survives the complete compiled execution chain

The program's dependency licence is proved by the actual compiler. Native
directed accessibility therefore reaches the real source query and the
whole-frontier controller without an additional grounding assumption. This
does not derive accessibility from answer existence or extend the value
profile's endpoint to arbitrary normal forms.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CompiledProgress

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev)
  (D : Discipline MSig [] ()) (supply : Nat → MClosed)

theorem source_normalizes (term : Tower.Tm 0)
    (normalizing : Acc (fun after before => StrongNormalization.Reduces
      (Definitions.devPackage dev built.nativeRows) before after) term) :
    Acc (fun after before => SourceLanguage.Step D (BinderCore.program built.rules) supply before after)
      (Config.initial (fun _ => 0)
        (PublicQuery.query RuntimeSubstitution.rules built.authored (queryCode term))) :=
  PublicProgress.source_normalizes RuntimeSubstitution.rules built.authored D supply
    (NormalGroundingCompiled.grounded built) (queryCode term)
    (MachineProgress.evaluate_normalizes built term normalizing)

include supply

theorem native_normalizes (N : Hosting.Nodes MSig [] ()) (term : Tower.Tm 0)
    (normalizing : Acc (fun after before => StrongNormalization.Reduces
      (Definitions.devPackage dev built.nativeRows) before after) term) :
    Acc (fun after before => (FrontierArrow.target (D := D) N (BinderCore.program built.rules)).Step before after)
      (FrontierArrow.initialState (D := D) N (BinderCore.program built.rules)
        (PublicQuery.query RuntimeSubstitution.rules built.authored (queryCode term))) :=
  PublicProgress.compiled_native_normalizes D supply built N (NormalGroundingCompiled.grounded built) term normalizing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CompiledProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CompiledProgress.native_normalizes
