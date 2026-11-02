import Mettapedia.Languages.VibeITP.CheckingMachine
import Mettapedia.Languages.VibeITP.CheckingMachineV2
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategory

/-!
# Hosted VibeITP judgments as actual persistent inference executions

The independent static and simultaneous-substitution source calculi connect
through their existing proof-category correspondences to the actual selected
client/server execution model. This composes existing correspondences; it does
not introduce another transition system or select a common foundational theory.

Hosting, source axioms and definitions remain explicit. Realization is a
mathematical existence result, not executable extraction. The proof observation
forgets physical traffic and cost. JIT observations, native C refinement and
arbitrary linear-resource profiles are outside these two static interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.CheckingInteraction

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Presentation Spec

private def emptyContext (definition : ValidatedCalculusLanguageDef) :
    PersistentInference.PersistentContext definition :=
  ⟨[],by intro pattern member; cases member⟩

private abbrev ClosedExecution (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :=
  PersistentInference.Execution (definition := definition)
    (emptyContext definition).state (emptyContext definition).board [goal]

private theorem arrow_iff_execution (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Nonempty ((⟨[]⟩ : CertificateGSLT.ClassifyingContext definition) ⟶ ⟨[goal]⟩) ↔
      Nonempty (ClosedExecution definition goal) := by
  constructor
  · rintro ⟨arrow⟩
    have proofs : CertificateGSLT.OpenDerivationList definition (emptyContext definition).board.judgments [goal] := by
      rw [PersistentInference.PersistentContext.board_judgments]
      exact arrow
    exact ⟨PersistentInference.compile (emptyContext definition).consistent proofs⟩
  · rintro ⟨execution⟩
    have proofs := execution.observe
    rw [PersistentInference.PersistentContext.board_judgments] at proofs
    exact ⟨proofs⟩

abbrev StaticExecution (theory : Theory) (allocated : Nat) (statement : Term) :=
  ClosedExecution (kernelValidated theory allocated) (jThm (encTerm theory.sig statement))

abbrev SimultaneousExecution (theory : Theory) (allocated : Nat) (statement : Term) :=
  ClosedExecution (SimultaneousPresentation.validatedV2 theory allocated) (jThm (encTerm theory.sig statement))

theorem static_derives_iff_execution {theory : Theory} {allocated : Nat}
    (hosted : Hosted theory allocated) (statement : Term) :
    Derives theory statement ↔ Nonempty (StaticExecution theory allocated statement) :=
  (CheckingMachine.kernel_derives_iff_classifyingArrow hosted statement).trans (arrow_iff_execution _ _)

theorem simultaneous_derives_iff_execution {theory : Theory} {allocated : Nat}
    (hosted : Hosted theory allocated) (statement : Term) :
    DerivesV2 theory statement ↔ Nonempty (SimultaneousExecution theory allocated statement) :=
  (CheckingMachineV2.derives_iff_classifyingArrow hosted statement).trans (arrow_iff_execution _ _)

#print axioms static_derives_iff_execution
#print axioms simultaneous_derives_iff_execution
end Mettapedia.Languages.VibeITP.CheckingInteraction
