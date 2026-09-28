import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorCompatibility
import Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonProofService

/-!
# Megalodon guest admission over native dependent wire data

The guest's checker is executed through a native data service. These lemmas
preserve data typing and service execution; they do not identify Mathdata
proofs with Prime's dependent proof terms or select a set-theoretic foundation.
-/

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Machines.BranchLocalNeed

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonRelatorIntegration

open Presentation NativeWireRelatorCompatibility
open NeedReference Presentation.PolarizedNeed Presentation.PolarizedNeedMachine

variable {n : Nat}

theorem nativeProof_operation_formed :
    ScopedComputation.OperationFormation rules MegalodonProofService.signature () :=
  operation_formation MegalodonProofService.operation_formed

theorem nativeProof_primitive_sound
    (environment : Mettapedia.Languages.Megalodon.MathdataKernel.Environment)
    (current : MegalodonProofWire.Scope)
    (expected : MegalodonProofWire.Request) (context : Tower.Ctx n) :
    PrimitiveSoundness rules MegalodonProofService.signature context
      (MegalodonProofService.primitive environment current expected) := by
  intro operation argument value _ _ produced
  cases operation
  simp only [MegalodonProofService.primitive, Produced.value.injEq] at produced
  cases produced
  exact encode_typed context _

theorem nativeProof_source_typed {v k : Nat} {Effect : Type} (context : Tower.Ctx n)
    (values : Fin v → VTy Tower.Head n) (needs : Fin k → CTy Tower.Head n)
    (input : NativeWireData.Wire) :
    ComputationTyping rules MegalodonProofService.signature context values needs
      (MegalodonProofService.source (Effect := Effect) input)
      (.returns (.native NativeWireData.dataType)) := by
  have formed : ComputationFormation rules context (.returns (.native NativeWireData.dataType)) :=
    .returns (.native ⟨.sort Tower.zero, .sort _, dataType_formed context⟩)
  exact .letNeed formed formed
    (.call nativeProof_operation_formed (encode_typed context input)) (.forceNeed 0)

end Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonRelatorIntegration
