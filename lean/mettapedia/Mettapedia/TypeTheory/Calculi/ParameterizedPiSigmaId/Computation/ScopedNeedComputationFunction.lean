import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputationTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalAdequacy

/-!
# Native-domain scoped computation functions

A function contains a raw native domain, a native result family and an actual
scoped computation body with one additional native variable. Application uses
the existing capture-avoiding code substitution; effects and need references
remain source syntax. Qualification is independent of execution and includes
formation of the domain, result family, native context and available need types.

Captured application uses the existing machine value-body opening. Materializing
its native environment agrees with substituting and then applying the source
function. Qualified natural evaluations of this actual closure yield admitted
native results through existing whole-machine preservation. Heap qualification
and primitive soundness remain explicit independent premises.

This is a native-domain function-body interface, not a new evaluator or a full
first-class CBPV value/computation grammar. It supplies neither termination nor
an equality of worlds for different representations of captured heap origins.
-/

open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedComputationFunction

open ScopedNeedComputation (Code NeedFormation weakenNeedTypes)
open ScopedComputation (OperationSignature)
open ScopedNeedMachine
open NeedReference

variable {Head Operation Effect : Type} {n m k l : Nat}

/-- The binder belongs to raw computation syntax, not to a host function. -/
structure Function (Head Operation Effect : Type) (n k : Nat) where
  domain : Tm Head n
  result : Tm Head (n + 1)
  body : Code Head Operation Effect (n + 1) k

def Function.apply (function : Function Head Operation Effect n k) (argument : Tm Head n) :
    Code Head Operation Effect n k :=
  Code.instantiate argument function.body

def Function.substitute (σ : Sub Head n m) (function : Function Head Operation Effect n k) :
    Function Head Operation Effect m k :=
  ⟨subst σ function.domain, subst (liftSub σ) function.result,
    function.body.substitute (liftSub σ)⟩

def Function.renameHandles (ρ : Fin k → Fin l) (function : Function Head Operation Effect n k) :
    Function Head Operation Effect n l :=
  ⟨function.domain, function.result, function.body.renameHandles ρ⟩

theorem Function.substitute_apply (σ : Sub Head n m)
    (function : Function Head Operation Effect n k) (argument : Tm Head n) :
    (function.apply argument).substitute σ = (function.substitute σ).apply (subst σ argument) :=
  Code.substitute_instantiate σ argument function.body

theorem Function.renameHandles_apply (ρ : Fin k → Fin l)
    (function : Function Head Operation Effect n k) (argument : Tm Head n) :
    (function.apply argument).renameHandles ρ = (function.renameHandles ρ).apply argument :=
  Code.renameHandles_instantiate ρ argument function.body

theorem Function.substitute_result (σ : Sub Head n m)
    (function : Function Head Operation Effect n k) (argument : Tm Head n) :
    subst σ (inst0 argument function.result) =
      inst0 (subst σ argument) (function.substitute σ).result :=
  subst_inst0 σ argument function.result

/-- Formation is retained separately from the raw source object. -/
structure Qualified (R : Rules Head) (signature : OperationSignature Head Operation)
    (Γ : Ctx Head n) (needTypes : Fin k → Tm Head n)
    (function : Function Head Operation Effect n k) : Prop where
  context : FormationSensitive.ContextFormation R Γ
  needs : NeedFormation R Γ needTypes
  domain : ∃ u, R.isUniverse u ∧ FormationSensitive.Typing R Γ function.domain (.head u)
  result : ∃ u, R.isUniverse u ∧
    FormationSensitive.Typing R (.snoc Γ function.domain) function.result (.head u)
  body : ScopedNeedComputation.Typing R signature (.snoc Γ function.domain)
    (weakenNeedTypes needTypes) function.body function.result

variable {R : Rules Head} {signature : OperationSignature Head Operation}
  {Γ : Ctx Head n} {Δ : Ctx Head m} {needTypes : Fin k → Tm Head n}
  {function : Function Head Operation Effect n k}

theorem identityEnvironment : FormationSensitive.CtxMor R Γ Γ ids := by
  intro index
  simpa only [ids, subst_ids] using (FormationSensitive.Typing.var (R := R) (Γ := Γ) index)

private theorem argumentEnvironment {argument A : Tm Head n}
    (admitted : FormationSensitive.Typing R Γ argument A) :
    FormationSensitive.CtxMor R (.snoc Γ A) Γ (subst0 argument) := by
  have source : FormationSensitive.Typing R Γ argument (subst ids A) := by
    simpa only [subst_ids] using admitted
  exact ScopedComputation.extendEnvironment identityEnvironment source

/-- Application opens the selected native fibre while removing only its
native binder. Existing handle coordinates retain their original result types. -/
theorem Qualified.apply_judgment (qualified : Qualified R signature Γ needTypes function)
    {argument : Tm Head n} (admitted : FormationSensitive.Typing R Γ argument function.domain) :
    ScopedNeedComputation.Judgment R signature Γ needTypes (function.apply argument)
      (inst0 argument function.result) := by
  refine ⟨qualified.context, qualified.needs, ?_⟩
  have body := qualified.body.substitute (argumentEnvironment admitted)
  have sameTypes : (fun index => subst (subst0 argument) (weakenNeedTypes needTypes index)) =
      needTypes := by
    funext index
    exact inst0_rename_wk argument (needTypes index)
  rw [sameTypes] at body
  exact body

theorem Qualified.applied_result_formed (qualified : Qualified R signature Γ needTypes function)
    {argument : Tm Head n} (admitted : FormationSensitive.Typing R Γ argument function.domain) :
    ∃ u, R.isUniverse u ∧ FormationSensitive.Judgment R Γ
      (inst0 argument function.result) (.head u) := by
  obtain ⟨u, universeWitness, formation⟩ := qualified.result
  exact ⟨u, universeWitness, qualified.context, formation.substitute (argumentEnvironment admitted)⟩

theorem Qualified.substitute (qualified : Qualified R signature Γ needTypes function)
    {σ : Sub Head n m} (target : FormationSensitive.ContextFormation R Δ)
    (environment : FormationSensitive.CtxMor R Γ Δ σ) :
    Qualified R signature Δ (fun index => subst σ (needTypes index)) (function.substitute σ) := by
  refine ⟨target, qualified.needs.substitute environment, ?_, ?_, ?_⟩
  · obtain ⟨u, universeWitness, formation⟩ := qualified.domain
    exact ⟨u, universeWitness, formation.substitute environment⟩
  · obtain ⟨u, universeWitness, formation⟩ := qualified.result
    exact ⟨u, universeWitness, formation.substitute (environment.lift _)⟩
  · simpa only [Function.substitute, ScopedNeedComputation.substitute_weakenNeedTypes] using
      qualified.body.substitute (environment.lift _)

theorem Qualified.renameHandles (qualified : Qualified R signature Γ needTypes function)
    {targetTypes : Fin l → Tm Head n} {ρ : Fin k → Fin l}
    (target : NeedFormation R Γ targetTypes)
    (compatible : ∀ index, targetTypes (ρ index) = needTypes index) :
    Qualified R signature Γ targetTypes (function.renameHandles ρ) := by
  refine ⟨qualified.context, target, qualified.domain, qualified.result, ?_⟩
  exact qualified.body.renameHandles (fun index => congrArg (rename wk) (compatible index))

/-- Captured application uses the actual runtime native-value opening. -/
def Function.open (function : Function Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId) (argument : Tm Head m) :
    Closure Head Operation Effect m :=
  (⟨n, k, function.body, values, needs⟩ : ValueBody Head Operation Effect m).open argument

/-- Runtime capture and source substitution have the same materialized code.
This does not equate their intensional heap-origin representations. -/
theorem Function.open_materializes (function : Function Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId) (argument : Tm Head m) :
    let opened := function.open values needs argument
    opened.code.substitute opened.values = (function.substitute values).apply argument :=
  Code.substitute_consSub argument values function.body

theorem Qualified.open_typing (qualified : Qualified R signature Γ needTypes function)
    {values : Sub Head n m} {needs : Fin k → CellId} {types : CellTypes Head m}
    (environment : FormationSensitive.CtxMor R Γ Δ values)
    (references : ∀ index, types (needs index) = some (subst values (needTypes index)))
    {argument : Tm Head m}
    (admitted : FormationSensitive.Typing R Δ argument (subst values function.domain)) :
    ClosureTyping R signature Δ types (function.open values needs argument)
      (inst0 argument (function.substitute values).result) :=
  value_body_open qualified.body environment references admitted

/-- A successful native value from an independently defined natural evaluation
of the actual captured closure receives its argument-indexed native judgment. -/
theorem Qualified.evaluation_value_judgment
    (qualified : Qualified R signature Γ needTypes function)
    {StableFault NativeFault : Type}
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {values : Sub Head n m} {needs : Fin k → CellId} {types : CellTypes Head m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {argument value : Tm Head m}
    (environment : FormationSensitive.CtxMor R Γ Δ values)
    (references : ∀ index, types (needs index) = some (subst values (needTypes index)))
    (admitted : FormationSensitive.Typing R Δ argument (subst values function.domain))
    (target : FormationSensitive.ContextFormation R Δ)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (heap : HeapTyping R signature Δ types world.heap)
    (evaluation : ScopedNeedNaturalSemantics.Eval primitive
      (function.open values needs argument) world (.value value) final) :
    FormationSensitive.Judgment R Δ value
      (inst0 argument (function.substitute values).result) := by
  have result := evaluation.result_typing sound
    (qualified.open_typing environment references admitted) heap
  cases result with
  | value typed => exact ⟨target, typed⟩


#print axioms Function.substitute_apply
#print axioms Function.renameHandles_apply
#print axioms Function.substitute_result
#print axioms Qualified.apply_judgment
#print axioms Qualified.applied_result_formed
#print axioms Qualified.substitute
#print axioms Qualified.renameHandles
#print axioms Function.open_materializes
#print axioms Qualified.open_typing
#print axioms Qualified.evaluation_value_judgment

end ScopedNeedComputationFunction
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
