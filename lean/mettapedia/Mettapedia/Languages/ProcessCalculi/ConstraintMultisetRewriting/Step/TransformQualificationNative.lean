import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance

/-!
# Joined qualification: compiled clauses are admitted exactly as native firings of the step

A compiled clause (`ContextualNativeBodies.Body`) carries the original-cut guard and absence results of
the native lane. Its admission is already characterized by one constructed native firing with
predicate queries (`ContextualNativeBodies.Body.Producer.source_iff_native_body_admission`). This
module states that firing as a firing of the candidate step's native instance `Interface.native`,
with no publication recipes:

* `bindingState`: the native state at which the clause's binding firing is read;
* `nativeFiring`: the producer's rule, the clause's binding selection, the producer's outputs,
  flags and queries (resource queries and every original-cut guard query), and the budget;
* `admitted_iff_native`: the clause is admitted exactly when that firing is admitted by
  `Interface.native`.

So the absence, count and original-cut verdicts of the compiled clauses are verdicts of the native
instance's `Holds` at the binding state. Result-level agreement depends on each clause kind's
publication contract and is not claimed here.

* `guarded_valid_iff_native`: a contextual guarded firing at an execution endpoint
  (`ContextualGuardedStep.Valid`) is admitted exactly when its query-free native firing is admitted
  by `Interface.native`, at every budget. This places the admission of the contextual λ, pair,
  causal and schematic-storage executions in the native instance; their results are not compared
  with the native published state here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification.Native

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualNativeBodies

variable {S : Signature} {O First Last : Type} [DecidableEq O] [DecidableEq First]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

/-- The native state at which a compiled clause's binding firing is read. -/
noncomputable def bindingState (clause : Body S O Γ sort before after) (occupied : Finset Nat) :
    Interface.NativeState S (Option (OccurrenceAllocationRenaming.Name O)) Γ sort :=
  ⟨_, inferInstance, clause.guardNativeBank, clause.nativeBindingState occupied⟩

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- The producer's binding firing as data of a native firing, without recipes. -/
noncomputable def nativeFiring {clause : Body S O Γ sort before after} (producer : clause.Producer)
    (occupied : Finset Nat) (fuel : Nat) : Interface.NativeFiring (bindingState clause occupied) :=
  ⟨producer.rule, clause.bindingSelection, producer.outputs occupied, producer.reusable,
    producer.queries occupied, fuel, fun _ => none, fun _ _ => rfl⟩

/-- **A compiled clause is admitted exactly when its native firing is admitted by the step.** -/
theorem admitted_iff_native {clause : Body S O Γ sort before after} (producer : clause.Producer)
    (occupied : Finset Nat) (fuel : Nat) :
    clause.Admitted ↔
      (Interface.native (S := S) (O := Option (OccurrenceAllocationRenaming.Name O)) (Γ := Γ)
        (sort := sort)).Admits (nativeFiring producer occupied fuel) :=
  Body.Producer.source_iff_native_body_admission producer occupied fuel

#print axioms admitted_iff_native

/-! ## Contextual guarded firings are native firings without queries

The contextual guarded step (`ContextualGuardedStep.Valid` at an execution endpoint) carries the
contextual λ, pair, causal and schematic-storage executions. Its admission is the conditional
execution's admission (`ContextualConditionalExecution.admitted_ofEndpoint_iff`), and every admitted
operation has a solver return at every budget (`ContextualConditionalExecution.realize_at_fuel`). -/

section Guarded

variable {Local O' : Type} [DecidableEq Local] [DecidableEq O'] (locals : Local → MetaArity S)

/-- The native state of an execution endpoint. -/
def endpointState (point : ContextualExecution.Endpoint locals O' Γ sort) :
    Interface.NativeState S O' Γ sort :=
  ⟨Local, inferInstance, locals, ContextualConditionalExecution.ofEndpoint locals point⟩

/-- A query-free native firing with the given data, without recipes. -/
def plainFiring (point : ContextualExecution.Endpoint locals O' Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals point.declarations)) Γ sort))
    (selection : Selection O')
    (outputs : O' → Term (signature S (ContextualActivatedStep.target locals point.declarations)) Γ sort)
    (reusable : O' → Bool) (fuel : Nat) : Interface.NativeFiring (endpointState locals point) :=
  ⟨rule, selection, outputs, reusable, [], fuel, fun _ => none, fun _ _ => rfl⟩

/-- **A contextual guarded firing is admitted exactly when its query-free native firing is admitted
by the step**, at every budget and with any reuse flags. -/
theorem guarded_valid_iff_native (point : ContextualExecution.Endpoint locals O' Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals point.declarations)) Γ sort))
    (selection : Selection O')
    (outputs : O' → Term (signature S (ContextualActivatedStep.target locals point.declarations)) Γ sort)
    (reusable : O' → Bool) (fuel : Nat) :
    ContextualGuardedStep.Valid locals point.declarations point.occupied selection rule
        point.inventory.rows point.inventory.configuration outputs ↔
      (Interface.native (S := S) (O := O') (Γ := Γ) (sort := sort)).Admits
        (plainFiring locals point rule selection outputs reusable fuel) := by
  rw [← ContextualConditionalExecution.admitted_ofEndpoint_iff locals point rule selection outputs]
  constructor
  · intro admitted
    obtain ⟨firing, hrule, hselection, houtputs, hreusable, hfuel⟩ :=
      ContextualConditionalExecution.realize_at_fuel locals (ContextualConditionalExecution.ofEndpoint locals point)
        rule selection outputs reusable admitted fuel
    exact ⟨⟨firing, [], fun _ member => by cases member⟩, hrule, hselection, houtputs, hreusable, hfuel, rfl⟩
  · rintro ⟨observed, hrule, hselection, houtputs, -, -, -⟩
    have admitted := observed.firing.admitted
    rw [hrule, hselection, houtputs] at admitted
    exact admitted

#print axioms guarded_valid_iff_native

end Guarded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification.Native
