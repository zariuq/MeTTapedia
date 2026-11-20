import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory

/-!
# Actual reclaim, structural debit and reissue executions

The finite controller is present in the initial process. Each reclaim
activates its remaining controller and the supplied stack cell. A second
COMM consumes the cell, records its complete head and publishes its tail.
Occurrence executions retain every intermediate configuration and firing.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Canonical CanonicalTyping CanonicalBag CanonicalReaction
open LanguageDefGSLT LanguageDefRewriteSystem DerivedContextualStep
open ResourcePredation ResourceClaimHistory

universe u
variable {Head : Type u}

private theorem step_congr {source source' target target' : RhoProcess}
    (before : rhoProcessEquations.r source' source)
    (actual : rhoLanguageDefGSLT.Step source target)
    (after : rhoProcessEquations.r target target') :
    rhoLanguageDefGSLT.Step source' target' := by
  obtain ⟨redex, contractum, first, firing, last⟩ := actual
  exact ⟨redex, contractum, before.trans first, firing, last.trans after⟩

private theorem parallel_perm (first second : List RhoProcess) (perm : List.Perm first second) :
    rhoProcessEquations.r (parallel first) (parallel second) :=
  (rhoProcessEquations_iff_structuralCongruence _ _).mpr
    (.par_perm _ _ (perm.map Subtype.val))

private theorem parallel_flatten (inner rest : List RhoProcess) :
    rhoProcessEquations.r (parallel (parallel inner :: rest)) (parallel (inner ++ rest)) :=
  (rhoProcessEquations_iff_structuralCongruence _ _).mpr (by
    simpa [parallel, ofList] using hashBagSpliceHead
      (inner.map Subtype.val) (rest.map Subtype.val))

/-- The actual authored COMM rule, with an independently supplied result
whose substitution equation is proved by the protocol's syntax lemmas. -/
private theorem actual_comm (receiver resource result : RhoProcess)
    (channel body contents : Pattern) (rest : List RhoProcess)
    (receiverShape : receiver.1 = input channel body)
    (resourceShape : resource.1 = output channel contents)
    (resultShape : result.1 = semanticCommSubst body contents) :
    rhoLanguageDefGSLT.Step (parallel (receiver :: resource :: rest)) (parallel (result :: rest)) := by
  have receiverTyped := ((rhoClosedTermWellSorted_process_iff _).mp receiver.2).1
  rw [receiverShape] at receiverTyped
  have bodyTyped := (rho_input_wellSorted_inv receiverTyped).2.2
  have resourceTyped := ((rhoClosedTermWellSorted_process_iff _).mp resource.2).1
  rw [resourceShape] at resourceTyped
  have contentsTyped := (rho_output_wellSorted_inv resourceTyped).2
  have firing : RhoStep (parallel (receiver :: resource :: rest)).1
      (.collection .hashBag
        (semanticCommSubst
          (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body)
          contents :: rest.map Subtype.val) none) := by
    simpa [parallel, ofList, receiverShape, resourceShape, input, output] using
      RhoStep.comm_resolved channel body contents (rest.map Subtype.val) bodyTyped contentsTyped
  refine ⟨parallel (receiver :: resource :: rest),
    (parallel (receiver :: resource :: rest)).stepTarget firing, rfl, firing, ?_⟩
  apply (rhoProcessEquations_iff_structuralCongruence _ _).mpr
  change StructuralCongruence
    (.collection .hashBag
      (semanticCommSubst
        (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body)
        contents :: rest.map Subtype.val) none)
    (.collection .hashBag (result.1 :: rest.map Subtype.val) none)
  rw [resultShape]
  exact collectionCongruence_of_forall₂ .hashBag none
    (.cons (SubstitutionCanonicalCommutation.semanticCommSubst_resolveQuotes_structuralCongruence
        bodyTyped (PureBoundary.rhoProcWellSorted_hashSetFree contentsTyped))
      (List.forall₂_same.mpr fun _ _ => .refl _))

def payloadProcess (encoding : Encoding Head) (stack : Stack Head) : RhoProcess :=
  closedProcess (payload encoding stack) (payload_typed _ _ _) (payload_safe _ _ _)

def triggerProcess : RhoProcess :=
  closedProcess trigger (.output (pop_typed _) .unit)
    (by simp [trigger, output, binderSafeAt, binderSafeListAt, zero, (names_safe 0).2.1])

def claimantProcess : RhoProcess :=
  closedProcess claimant
    (.input (acquisition_typed _) (.output (metabolic_typed _) (.drop (.bvar rfl))))
    (by simp [claimant, input, output, binderSafeAt, binderSafeListAt,
      metabolic, acquisition, spent, pop, zero])

def offeredProcess (encoding : Encoding Head) (stack : Stack Head) : RhoProcess :=
  closedProcess (offer encoding stack) (.output (acquisition_typed _) (payload_typed _ _ _))
    (by simp [offer, output, binderSafeAt, binderSafeListAt, payload_safe, (names_safe 0).2.2.2])

theorem reclaim_step (encoding : Encoding Head) (stack : Stack Head) (count : Nat) (record : List Head) :
    rhoLanguageDefGSLT.Step (live encoding stack (count + 1) record)
      (reclaimed encoding stack count record) := by
  let result := parallel [payloadProcess encoding stack, triggerProcess, ownerProcess count]
  have actual := actual_comm (ownerProcess (count + 1)) (messageProcess encoding stack)
    result metabolic (.collection .hashBag [.apply "PDrop" [.bvar 0], trigger, owner count] none)
    (payload encoding stack) (record.map (burnedProcess encoding)) rfl rfl (by
      exact (reclaim_substitution encoding stack count).symm)
  apply step_congr ?_ actual ?_
  · exact parallel_perm _ _ (List.Perm.swap _ _ _)
  · exact parallel_flatten _ _

theorem pop_step (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) :
    rhoLanguageDefGSLT.Step (reclaimed encoding (.cell head tail) count record)
      (live encoding tail count (head :: record)) := by
  let result := parallel [messageProcess encoding tail, burnedProcess encoding head]
  have actual := actual_comm (payloadProcess encoding (.cell head tail)) triggerProcess result pop
    (.collection .hashBag [message encoding tail, burned encoding head] none) zero
    (ownerProcess count :: record.map (burnedProcess encoding)) rfl rfl
      (pop_substitution encoding head tail).symm
  apply step_congr rfl actual
  exact (parallel_flatten _ _).trans
    (parallel_perm _ _ (by
      exact ((List.Perm.swap (burnedProcess encoding head) (ownerProcess count)
        (record.map (burnedProcess encoding))).symm).cons (messageProcess encoding tail)))

theorem acquisition_step (encoding : Encoding Head) (stack : Stack Head)
    (count : Nat) (record : List Head) :
    rhoLanguageDefGSLT.Step (acquisitionSource encoding stack count record)
      (live encoding stack count record) :=
  actual_comm claimantProcess (offeredProcess encoding stack) (messageProcess encoding stack)
    acquisition (output metabolic (.apply "PDrop" [.bvar 0])) (payload encoding stack)
    (ownerProcess count :: record.map (burnedProcess encoding)) rfl rfl
    (acquisition_substitution encoding stack).symm

/-- A supplied occurrence inventory executes the independently proved
public step. Its selected occurrences and resulting configuration are retained. -/
structure SelectedStep (source : Configuration) (target : RhoProcess) where
  firing : ResourcePredation.Firing source
  targetInventory : inventory firing.target = fromProcess target

private def selectedStep {expected target : RhoProcess} (source : Configuration)
    (sourceInventory : inventory source = fromProcess expected)
    (actual : rhoLanguageDefGSLT.Step expected target) : SelectedStep source target := by
  have sourceStep : rhoLanguageDefGSLT.Step (readout source) target := by
    apply (publicStep_iff _ _).mpr
    rw [readout, fromProcess_toProcess, sourceInventory]
    exact (publicStep_iff _ _).mp actual
  let witnesses := publicStep_lifts sourceStep
  exact ⟨Classical.choose witnesses, Classical.choose_spec witnesses⟩

structure Cycle (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) (source : Configuration) where
  reclaim : ResourcePredation.Firing source
  intermediate : inventory reclaim.target = fromProcess (reclaimed encoding (.cell head tail) count record)
  pop : ResourcePredation.Firing reclaim.target
  remaining : inventory pop.target = fromProcess (live encoding tail count (head :: record))

def cycle (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding (.cell head tail) (count + 1) record)) :
    Cycle encoding head tail count record source := by
  let first := selectedStep source sourceInventory (reclaim_step encoding (.cell head tail) count record)
  let second := selectedStep first.firing.target first.targetInventory (pop_step encoding head tail count record)
  exact ⟨first.firing, first.targetInventory, second.firing, second.targetInventory⟩

namespace Cycle

variable {encoding : Encoding Head} {head : Head} {tail : Stack Head}
variable {count : Nat} {record : List Head} {source : Configuration}

def execution (receipt : Cycle encoding head tail count record source) :
    Execution source receipt.pop.target :=
  .next receipt.reclaim (.next receipt.pop (.done _))

theorem execution_length (receipt : Cycle encoding head tail count record source) :
    receipt.execution.length = 2 := rfl

theorem actual_public_path (receipt : Cycle encoding head tail count record source) :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) (readout receipt.pop.target) :=
  receipt.execution.public_history

theorem positive_burn (receipt : Cycle encoding head tail count record source) :
    (Stack.cell head tail).size = tail.size + 1 ∧ 0 < receipt.execution.length :=
  ⟨rfl, by rw [execution_length]; decide⟩

theorem exact_tail_readout (receipt : Cycle encoding head tail count record source) :
    inventory receipt.pop.target = fromProcess (live encoding tail count (head :: record)) ∧
      PayloadReadout (payload encoding tail) (tail.heads.map encoding.code) :=
  ⟨receipt.remaining, payload_readout encoding tail⟩

end Cycle

structure Batch (encoding : Encoding Head) (consumed suffix : Stack Head)
    (record : List Head) (source : Configuration) where
  target : Configuration
  execution : Execution source target
  length : execution.length = 2 * consumed.size
  remaining : inventory target = fromProcess (live encoding suffix 0 (consumed.heads.reverse ++ record))

def batch (encoding : Encoding Head) (consumed suffix : Stack Head) (record : List Head)
    (source : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding (consumed.append suffix) consumed.size record)) :
    Batch encoding consumed suffix record source := by
  induction consumed generalizing source record with
  | empty => exact ⟨source, .done source, rfl, sourceInventory⟩
  | cell head rest ih =>
      let first := cycle encoding head (rest.append suffix) rest.size record source sourceInventory
      let later := ih (head :: record) first.pop.target first.remaining
      refine ⟨later.target, first.execution.append later.execution, ?_, ?_⟩
      · rw [Execution.append_length, first.execution_length, later.length]
        simp only [Stack.size]
        omega
      · simpa [Stack.heads, List.reverse_cons, List.append_assoc] using later.remaining

theorem batch_ledger (consumed suffix : Stack Head) :
    (consumed.append suffix).size = suffix.size + consumed.size := by
  rw [Stack.append_size, Nat.add_comm]

structure Acquisition (encoding : Encoding Head) (stack : Stack Head)
    (count : Nat) (record : List Head) (source : Configuration) where
  claim : ResourcePredation.Firing source
  transferred : inventory claim.target = fromProcess (live encoding stack count record)

def acquire (encoding : Encoding Head) (stack : Stack Head) (count : Nat) (record : List Head)
    (source : Configuration)
    (sourceInventory : inventory source = fromProcess (acquisitionSource encoding stack count record)) :
    Acquisition encoding stack count record source := by
  let selected := selectedStep source sourceInventory (acquisition_step encoding stack count record)
  exact ⟨selected.firing, selected.targetInventory⟩

namespace Acquisition

variable {encoding : Encoding Head} {stack : Stack Head} {count : Nat} {record : List Head} {source : Configuration}

def execution (receipt : Acquisition encoding stack count record source) : Execution source receipt.claim.target :=
  .next receipt.claim (.done _)

theorem execution_length (receipt : Acquisition encoding stack count record source) : receipt.execution.length = 1 := rfl

theorem full_stack_readout (receipt : Acquisition encoding stack count record source) :
    inventory receipt.claim.target = fromProcess (live encoding stack count record) ∧
      PayloadReadout (payload encoding stack) (stack.heads.map encoding.code) :=
  ⟨receipt.transferred, payload_readout encoding stack⟩

end Acquisition

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
