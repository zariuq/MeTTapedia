import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputationFunction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedNaturalAdequacy

/-! # Finite execution and admission controls -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedComputationFunction
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
open ScopedNeedComputation (Code NeedFormation weakenNeedTypes)
open ScopedComputation (OperationSignature)
open ScopedNeedMachine
open NeedReference
variable {Head Operation Effect : Type} {n m k l : Nat}
variable {R : Rules Head} {signature : OperationSignature Head Operation}
  {Γ : Ctx Head n} {Δ : Ctx Head m} {needTypes : Fin k → Tm Head n}
  {function : Function Head Operation Effect n k}

namespace Examples

abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev context := ScopedComputation.NativeExamples.context
abbrev older := ScopedComputation.NativeExamples.older
abbrev newer := ScopedComputation.NativeExamples.newer
abbrev operationSignature := ScopedNeedComputation.Examples.operationSignature

def identityResult : Tower.Tm 3 := .id ground (.var 0) (.var 0)

/-- The selected argument is captured in a suspended reflexivity computation.
Its effect occurs at first force; two uses share that native evidence. -/
def identityFunction : Function Tower.Head Empty Nat 2 0 where
  domain := ground
  result := identityResult
  body := .letNeed (.emit 7 (.returnValue (.refl (.var 0))))
    (.sequence (.force 0) (.force 0))

theorem identityFunction_qualified :
    Qualified Tower.rules operationSignature context Fin.elim0 identityFunction := by
  have formed : FormationSensitive.Typing Tower.rules (.snoc context ground)
      identityResult (sortTm Tower.zero) :=
    .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)
  refine ⟨ScopedComputation.NativeExamples.context_formed, (fun index => Fin.elim0 index),
    ⟨.sort Tower.zero, .sort Tower.zero, .headType .legacyGround⟩,
    ⟨.sort Tower.zero, .sort Tower.zero, formed⟩, ?_⟩
  refine .letNeed formed (.sort Tower.zero) formed (.sort Tower.zero)
    (.emit (.returnValue (.reflIntro (.var 0)))) ?_
  exact .sequence formed (.sort Tower.zero) formed (.sort Tower.zero) (.force 0) (.force 0)

theorem selected_argument_types_differ :
    inst0 older identityFunction.result ≠ inst0 newer identityFunction.result := by decide

theorem newer_application_qualified :
    ScopedNeedComputation.Judgment Tower.rules operationSignature context Fin.elim0
      (identityFunction.apply newer) (.id ground newer newer) :=
  identityFunction_qualified.apply_judgment (.var 0)

theorem wrong_selected_evidence_not_admitted :
    ¬ FormationSensitive.Typing Tower.rules context (.refl older)
      (inst0 newer identityFunction.result) :=
  ScopedComputation.NativeExamples.wrong_selected_index_not_admitted

def primitive (operation : Empty) (_ : Tower.Tm 2) : Produced (Tower.Tm 2) Empty Empty :=
  nomatch operation

def initial (argument : Tower.Tm 2) : NeedMachine Tower.Head Empty Nat Empty Empty 2 where
  world :=
    { lineage := 0, path := [], heap := .empty, receipts := .empty,
      nextCell := 0, nextEvaluator := 0 }
  control := .run (.evaluate (identityFunction.open ids Fin.elim0 argument) .done) []

def observe (machine : NeedMachine Tower.Head Empty Nat Empty Empty 2) :
    Option (Outcome Tower.Head Empty Empty 2) × List Nat :=
  (haltedOutcome machine, machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect event => some event
    | _ => none)

theorem actual_opened_closure_shares :
    (runFrontier (spec primitive) 64 [initial newer]).map observe =
      [(some (.value (.refl newer)), [7])] := rfl

theorem actual_opened_closure_keeps_argument :
    (runFrontier (spec primitive) 64 [initial older]).map observe =
      [(some (.value (.refl older)), [7])] := rfl

theorem opened_closure_result_admitted {argument value : Tower.Tm 2}
    (argumentTyped : FormationSensitive.Typing Tower.rules context argument ground)
    {fuel : Nat} (returned : Produced.value value ∈ answers (spec primitive) fuel (initial argument)) :
    FormationSensitive.Judgment Tower.rules context value (inst0 argument identityFunction.result) := by
  obtain ⟨final, ⟨evaluation⟩⟩ := ScopedNeedNaturalSemantics.answers_have_natural_derivations returned
  have sound : PrimitiveSoundness Tower.rules operationSignature context primitive := by
    intro operation
    exact Empty.elim operation
  have admitted := identityFunction_qualified.evaluation_value_judgment
    identityEnvironment (fun index => Fin.elim0 index)
    (by simpa only [identityFunction, subst_ids] using argumentTyped)
    ScopedComputation.NativeExamples.context_formed sound HeapTyping.empty evaluation
  simpa only [Function.substitute, liftSub_ids, subst_ids] using admitted

/-- Substitution passes under an internal native sequence binder without
capturing the argument in that newer slot. -/
def captureFunction : Function Nat Unit Unit 1 1 :=
  ⟨.head 0, .head 0, ScopedNeedComputation.Examples.nativeBody⟩

theorem argument_not_captured :
    captureFunction.apply (.var 0) ≠
      (.letNeed (.call () (.var 0))
        (.sequence (.force 0) (.returnValue (.pair (.var 0) (.var 0)))) :
          Code Nat Unit Unit 1 1) :=
  ScopedNeedComputation.Examples.native_opening_rejects_capture

end Examples

#print axioms Examples.identityFunction_qualified

#print axioms Examples.selected_argument_types_differ

#print axioms Examples.newer_application_qualified

#print axioms Examples.wrong_selected_evidence_not_admitted

#print axioms Examples.actual_opened_closure_shares

#print axioms Examples.actual_opened_closure_keeps_argument

#print axioms Examples.opened_closure_result_admitted

#print axioms Examples.argument_not_captured

end ScopedNeedComputationFunction
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
