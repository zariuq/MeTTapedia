import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayApplicationComparison
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceFunctionRelations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayTypingCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation

/-!
# A closed higher-order comparison with unequal intermediate values

The program `(λf. λz. f z) (λx. x)` has two accepted replay trees at
`U₀ → U₁`. The internal identity is checked at `U₀ → U₀` in one tree and
`U₁ → U₁` in the other. Those identity values are different sets, even in
the valid empty context. The returned functions nevertheless agree.

The comparison uses the actual assembly compatibility laws with the
relation of pointwise agreement on `U₀`; it does not assume equality of
intermediate values checked at different types. This is a positive control,
not unrestricted certificate coherence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayFunctionComparisonControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta
  TraceFunctionRelated traceFunctionRelated_graph_iff)

universe u

private abbrev u0 : Tower.Head := .sort Tower.zero
private abbrev u1 : Tower.Head := .sort (.succ Tower.zero)
private abbrev u2 : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev f0Level : Tower.Head := .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev f1Level : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev outLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero)))
private abbrev f0 {n : Nat} : Tower.Tm n := .pi (.head u0) (.head u0)
private abbrev f1 {n : Nat} : Tower.Tm n := .pi (.head u1) (.head u1)
private abbrev output {n : Nat} : Tower.Tm n := .pi (.head u0) (.head u1)
private abbrev f0Formation {n : Nat} : Code Tower.Head NoConversion n :=
  .piForm u1 u1 .headType .headType
private abbrev f1Formation {n : Nat} : Code Tower.Head NoConversion n :=
  .piForm u2 u2 .headType .headType
private abbrev outFormation {n : Nat} : Code Tower.Head NoConversion n :=
  .piForm u1 u2 .headType .headType
private abbrev lowerLevel : Tower.Head := .sort (.max
  (.max (.succ Tower.zero) (.succ Tower.zero))
  (.max (.succ Tower.zero) (.succ (.succ Tower.zero))))
private abbrev upperLevel : Tower.Head := .sort (.max
  (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
  (.max (.succ Tower.zero) (.succ (.succ Tower.zero))))

def subject : Tower.Tm 0 :=
  .app (.lam (.lam (.app (.var 1) (.var 0)))) (.lam (.var 0))

def lowerIdentity : Code Tower.Head NoConversion 0 := .lamIntro f0Level f0Formation .var
def upperIdentity : Code Tower.Head NoConversion 0 := .lamIntro f1Level f1Formation .var

private abbrev bodySubject : Tower.Tm 1 := .lam (.app (.var 1) (.var 0))
private abbrev lowerBody : Code Tower.Head NoConversion 1 :=
  .lamIntro outLevel outFormation (.cumul u0 (.appElim (.head u0) (.head u0) .var .var))
private abbrev upperBody : Code Tower.Head NoConversion 1 :=
  .lamIntro outLevel outFormation (.appElim (.head u1) (.head u1) .var (.cumul u0 .var))

def lowerCode : Code Tower.Head NoConversion 0 :=
  .appElim f0 output
    (.lamIntro lowerLevel (.piForm f0Level outLevel f0Formation outFormation)
      lowerBody) lowerIdentity

def upperCode : Code Tower.Head NoConversion 0 :=
  .appElim f1 output
    (.lamIntro upperLevel (.piForm f1Level outLevel f1Formation outFormation)
      upperBody) upperIdentity

theorem checked :
    check Tower.rules noConversionCheck .nil subject output lowerCode = true ∧
    check Tower.rules noConversionCheck .nil subject output upperCode = true := by
  decide

theorem identities_checked :
    check Tower.rules noConversionCheck .nil (.lam (.var 0)) f0 lowerIdentity = true ∧
    check Tower.rules noConversionCheck .nil (.lam (.var 0)) f1 upperIdentity = true := by
  decide

theorem context_checked :
    checkContext Tower.rules noConversionCheck (Ctx.nil : Tower.Ctx 0) .nil = true := rfl

theorem context_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (ContextCode.nil : ContextCode Tower.Head NoConversion 0) .nil = some (fun _ => True) := rfl

theorem codes_differ : lowerCode ≠ upperCode := by
  intro equal
  cases equal

theorem lower_identity_at_upper_type_rejected :
    check Tower.rules noConversionCheck .nil (.lam (.var 0)) f1 lowerIdentity = false := by
  decide

noncomputable def identity (h : CofinalInaccessibles.{u}) (level : Nat) : ZFSet.{u} :=
  traceLam (graph (universeSet h ∅ level) id)

noncomputable def programMeaning (h : CofinalInaccessibles.{u}) (level : Nat) : Meaning.{u} 0 :=
  .plain (fun _ => traceApp
    (traceLam (graph (tracePiSet (universeSet h ∅ level) (fun _ => universeSet h ∅ level))
      (fun f => traceLam (graph (universeSet h ∅ 0) (fun z => traceApp f z)))))
    (identity h level))

theorem lower_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerCode subject output = some (programMeaning h 0) := rfl

theorem upper_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperCode subject output = some (programMeaning h 1) := rfl

theorem identities_assemble (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerIdentity (.lam (.var 0)) f0 = some (.plain (fun _ => identity h 0)) ∧
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperIdentity (.lam (.var 0)) f1 = some (.plain (fun _ => identity h 1)) := ⟨rfl, rfl⟩

private theorem application_outside {A x : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    (outside : x ∉ A) : traceApp (traceLam (graph A f)) x = ∅ := by
  apply ZFSet.ext
  intro z
  rw [ZFSetTraceProducts.mem_traceApp, ZFSetTraceProducts.pair_mem_traceLam]
  constructor
  · rintro ⟨value, member, _⟩
    exact (outside (ZFSetDependentProducts.pair_mem_graph.mp member).1).elim
  · exact fun impossible => (ZFSet.notMem_empty z impossible).elim

theorem internal_identities_differ (h : CofinalInaccessibles.{u}) : identity h 0 ≠ identity h 1 := by
  intro equal
  have observed := congrArg (fun f => traceApp f (universeSet h ∅ 0)) equal
  have lower : traceApp (identity h 0) (universeSet h ∅ 0) = ∅ :=
    application_outside (universeSet_no_self_membership h ∅ 0)
  have upper : traceApp (identity h 1) (universeSet h ∅ 0) = universeSet h ∅ 0 :=
    traceApp_graph_beta _ (universeSet_mem_next h ∅ 0)
  rw [lower, upper] at observed
  have member := seed_mem_zero h (∅ : ZFSet.{u})
  rw [← observed] at member
  exact ZFSet.notMem_empty _ member

private theorem graph_congr {A : ZFSet.{u}} {f g : ZFSet.{u} → ZFSet.{u}}
    (agree : ∀ x ∈ A, f x = g x) : graph A f = graph A g := by
  apply ZFSet.ext
  intro z
  simp only [ZFSetDependentProducts.mem_graph]
  constructor
  · rintro ⟨x, hx, equal⟩
    exact ⟨x, hx, by rw [← agree x hx]; exact equal⟩
  · rintro ⟨x, hx, equal⟩
    exact ⟨x, hx, by rw [agree x hx]; exact equal⟩

theorem program_returns_identity (h : CofinalInaccessibles.{u}) (level : Nat)
    (includes : universeSet h ∅ 0 ⊆ universeSet h ∅ level)
    (env : ZFSetTypeExpressionInterpretation.Environment.{u} 0) :
    (programMeaning h level).value env = identity h 0 := by
  have member : identity h level ∈
      tracePiSet (universeSet h ∅ level) (fun _ => universeSet h ∅ level) := by
    exact ZFSetTraceProducts.mem_tracePiSet.mpr
      ⟨graph _ id, ZFSetDependentProducts.graph_mem_piSet (fun _ hx => hx), rfl⟩
  change traceApp _ (identity h level) = identity h 0
  rw [traceApp_graph_beta _ member]
  apply congrArg traceLam
  apply graph_congr
  intro z hz
  exact traceApp_graph_beta _ (includes hz)

theorem returned_values_agree (h : CofinalInaccessibles.{u})
    (env : ZFSetTypeExpressionInterpretation.Environment.{u} 0) :
    (programMeaning h 0).value env = (programMeaning h 1).value env := by
  rw [program_returns_identity h 0 (fun _ hx => hx) env,
    program_returns_identity h 1 (universeSet_subset_next h ∅ 0) env]

/-- The input relation compares the common observable domain, not the
whole function sets. Its two arguments can therefore be unequal. -/
def AgreeOnLower (h : CofinalInaccessibles.{u}) (left right : ZFSet.{u}) : Prop :=
  ∀ z ∈ universeSet h ∅ 0, traceApp left z = traceApp right z

/-- The older lower-universe observation is precisely the domain-indexed
function relation specialized to equal inputs and outputs. -/
theorem agreeOnLower_iff_traceFunctionRelated (h : CofinalInaccessibles.{u})
    (left right : ZFSet.{u}) :
    AgreeOnLower h left right ↔
      TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
        left right := by
  constructor
  · intro related x insideLeft y _ same
    subst y
    exact related x insideLeft
  · intro related x inside
    exact related x inside x (universeSet_subset_next h ∅ 0 inside) rfl

theorem identities_related_on_retained_domains (h : CofinalInaccessibles.{u}) :
    TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
      (identity h 0) (identity h 1) := by
  change TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
    (traceLam (graph (universeSet h ∅ 0) id))
    (traceLam (graph (universeSet h ∅ 1) id))
  apply (traceFunctionRelated_graph_iff _ _ Eq Eq id id).mpr
  intro x _ y _ same
  exact same

theorem identities_related (h : CofinalInaccessibles.{u}) :
    AgreeOnLower h (identity h 0) (identity h 1) :=
  (agreeOnLower_iff_traceFunctionRelated h _ _).mpr
    (identities_related_on_retained_domains h)

private noncomputable def bodyMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => traceLam (graph (universeSet h ∅ 0) (fun z => traceApp (env 0) z)))

private noncomputable def outMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ 0) (fun _ => universeSet h ∅ 1),
    some (fun _ => universeSet h ∅ 0)⟩

private noncomputable def innerMeaning : Meaning.{u} 2 :=
  .plain (fun env => traceApp (env 1) (env 0))

theorem bodies_related (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (leftEnv rightEnv : ZFSetTypeExpressionInterpretation.Environment.{u} 1)
    (related : TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1)
      Eq Eq (leftEnv 0) (rightEnv 0)) :
    (bodyMeaning h).value leftEnv = (bodyMeaning h).value rightEnv := by
  apply lambda_values_eq (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    outLevel outLevel (.head u0) (.head u0) (.head u1) (.head u1)
    (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0)) outFormation outFormation
    (.cumul u0 (.appElim (.head u0) (.head u0) .var .var))
    (.appElim (.head u1) (.head u1) .var (.cumul u0 .var))
    (outMeaning h) (outMeaning h) (bodyMeaning h) (bodyMeaning h)
    innerMeaning innerMeaning (fun _ => universeSet h ∅ 0) (fun _ => universeSet h ∅ 0)
    rfl rfl rfl rfl rfl rfl rfl rfl leftEnv rightEnv rfl
  exact (agreeOnLower_iff_traceFunctionRelated h _ _).mpr related

private noncomputable def functionSpace (h : CofinalInaccessibles.{u}) (level : Nat) : ZFSet.{u} :=
  tracePiSet (universeSet h ∅ level) (fun _ => universeSet h ∅ level)

private noncomputable def outerMeaning (h : CofinalInaccessibles.{u}) (level : Nat) : Meaning.{u} 0 :=
  ⟨fun _ => tracePiSet (functionSpace h level)
      (fun _ => tracePiSet (universeSet h ∅ 0) (fun _ => universeSet h ∅ 1)),
    some (fun _ => functionSpace h level)⟩

theorem identities_in_domains (h : CofinalInaccessibles.{u}) (level : Nat) :
    identity h level ∈ functionSpace h level :=
  ZFSetTraceProducts.mem_tracePiSet.mpr
    ⟨graph _ id, ZFSetDependentProducts.graph_mem_piSet (fun _ hx => hx), rfl⟩

/-- The generic two-certificate beta comparison applies with unequal input
values and their actual, different retained domains. -/
theorem returned_values_agree_by_comparison (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u})
    (env : ZFSetTypeExpressionInterpretation.Environment.{u} 0) :
    (programMeaning h 0).value env = (programMeaning h 1).value env := by
  apply application_lambda_related (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    lowerLevel upperLevel f0 f1 output output bodySubject bodySubject
    (.lam (.var 0)) (.lam (.var 0))
    (.piForm f0Level outLevel f0Formation outFormation)
    (.piForm f1Level outLevel f1Formation outFormation) lowerIdentity upperIdentity
    lowerBody upperBody (outerMeaning h 0) (outerMeaning h 1)
    (.plain (fun _ => identity h 0)) (.plain (fun _ => identity h 1))
    (programMeaning h 0) (programMeaning h 1) (bodyMeaning h) (bodyMeaning h)
    (fun _ => functionSpace h 0) (fun _ => functionSpace h 1)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl env env
    (TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq) Eq
    (identities_in_domains h 0) (identities_in_domains h 1)
    (identities_related_on_retained_domains h)
  intro x _ y _ related
  exact bodies_related h constants _ _ related

/-- This endpoint compares the values recovered from the two exact assembly
receipts, not merely separately named set expressions. -/
theorem assembled_program_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (left right : Meaning.{u} 0)
    (atLeft : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerCode subject output = some left)
    (atRight : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperCode subject output = some right) : left.value = right.value := by
  rw [lower_assembles] at atLeft
  rw [upper_assembles] at atRight
  cases Option.some.inj atLeft
  cases Option.some.inj atRight
  funext env
  exact returned_values_agree_by_comparison h constants env

theorem assembled_identity_values_differ (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (left right : Meaning.{u} 0)
    (atLeft : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerIdentity (.lam (.var 0)) f0 = some left)
    (atRight : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperIdentity (.lam (.var 0)) f1 = some right)
    (env : ZFSetTypeExpressionInterpretation.Environment.{u} 0) :
    left.value env ≠ right.value env := by
  rw [(identities_assemble h constants).1] at atLeft
  rw [(identities_assemble h constants).2] at atRight
  cases Option.some.inj atLeft
  cases Option.some.inj atRight
  exact internal_identities_differ h

/-! The returned functions can be used in an identity-indexed pair. Its
formation uses both independently accepted program certificates, so semantic
membership requires their actual agreement at the shared output carrier. -/

private abbrev witnessLevel : Tower.Head := .sort (.max
  (.max (.succ Tower.zero) (.succ (.succ Tower.zero)))
  (.max (.succ Tower.zero) (.succ (.succ Tower.zero))))

def equalityWitnessCode : Code Tower.Head NoConversion 0 :=
  CoherenceWitness.code outLevel witnessLevel output outFormation lowerCode upperCode

def equalityWitnessFormation : Code Tower.Head NoConversion 0 :=
  CoherenceWitness.formation outLevel outFormation lowerCode upperCode

theorem equality_witness_checked :
    checkJudgment Tower.rules noConversionCheck .nil
      (CoherenceWitness.term subject) (CoherenceWitness.type output subject)
      .nil equalityWitnessCode = true := by
  decide

private noncomputable def outputMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 0 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ 0) (fun _ => universeSet h ∅ 1),
    some (fun _ => universeSet h ∅ 0)⟩

theorem returned_value_typed (h : CofinalInaccessibles.{u})
    (env : ZFSetTypeExpressionInterpretation.Environment.{u} 0) :
    (programMeaning h 0).value env ∈ (outputMeaning h).value env := by
  rw [program_returns_identity h 0 (fun _ hx => hx) env]
  exact ZFSetTraceProducts.mem_tracePiSet.mpr
    ⟨graph _ id, ZFSetDependentProducts.graph_mem_piSet
      (fun _ hx => universeSet_subset_next h ∅ 0 hx), rfl⟩

/-- This is semantic typing of the actual identity-indexed result, not only
agreement of its two function components considered in isolation. -/
theorem equality_witness_assembles_and_inhabits (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ witness formed,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        equalityWitnessCode (CoherenceWitness.term subject)
        (CoherenceWitness.type output subject) = some witness ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        equalityWitnessFormation (CoherenceWitness.type output subject)
        (.head witnessLevel) = some formed ∧
      ∀ env, witness.value env ∈ formed.value env := by
  refine ⟨CoherenceWitness.termMeaning (programMeaning h 0),
    CoherenceWitness.typeMeaning (outputMeaning h) (programMeaning h 0) (programMeaning h 1),
    CoherenceWitness.term_assembles _ constants outLevel witnessLevel output subject
      outFormation lowerCode upperCode _ (lower_assembles h constants),
    CoherenceWitness.formation_assembles _ constants outLevel output subject
      outFormation lowerCode upperCode _ _ _ rfl
      (lower_assembles h constants) (upper_assembles h constants) witnessLevel, ?_⟩
  intro env
  exact (CoherenceWitness.membership_iff _ _ _ env).mpr
    ⟨returned_value_typed h env, returned_values_agree_by_comparison h constants env⟩

#print axioms checked
#print axioms identities_checked
#print axioms internal_identities_differ
#print axioms returned_values_agree
#print axioms bodies_related
#print axioms returned_values_agree_by_comparison
#print axioms lower_identity_at_upper_type_rejected
#print axioms assembled_program_values_agree
#print axioms assembled_identity_values_differ
#print axioms equality_witness_checked
#print axioms equality_witness_assembles_and_inhabits

/-! ## The common-domain relation does not preserve arbitrary identity fibres

Both upper functions agree with the lower identity on `U₀`, but they differ
at `U₀ ∈ U₁`. Consequently the relation cannot reflect equality between
arbitrary related functions. This refutes an unrestricted relational-context
premise for identity formation, not coherence of accepted same-erasure
certificates. The perturbed upper function is a semantic control; no source
definition of it is assumed.
-/

noncomputable def changedIdentity (h : CofinalInaccessibles.{u}) : ZFSet.{u} := by
  classical
  exact traceLam (graph (universeSet h ∅ 1)
    (fun z => if z = universeSet h ∅ 0 then ∅ else z))

theorem changed_identity_typed (h : CofinalInaccessibles.{u}) :
    changedIdentity h ∈ tracePiSet (universeSet h ∅ 1) (fun _ => universeSet h ∅ 1) := by
  classical
  apply ZFSetTraceProducts.mem_tracePiSet.mpr
  refine ⟨graph _ _, ZFSetDependentProducts.graph_mem_piSet ?_, rfl⟩
  intro z hz
  split
  · exact universeSet_subset_next h ∅ 0 (seed_mem_zero h ∅)
  · exact hz

theorem changed_identity_agrees_below (h : CofinalInaccessibles.{u})
    (z : ZFSet.{u}) (hz : z ∈ universeSet h ∅ 0) :
    traceApp (identity h 0) z = traceApp (changedIdentity h) z := by
  classical
  have unequal : z ≠ universeSet h ∅ 0 := by
    intro equal
    subst z
    exact universeSet_no_self_membership h ∅ 0 hz
  rw [show traceApp (identity h 0) z = z from traceApp_graph_beta _ hz]
  change z = traceApp (traceLam (graph _ _)) z
  rw [traceApp_graph_beta _ (universeSet_subset_next h ∅ 0 hz), if_neg unequal]

theorem upper_identities_differ (h : CofinalInaccessibles.{u}) :
    identity h 1 ≠ changedIdentity h := by
  classical
  intro equal
  have observed := congrArg (fun f => traceApp f (universeSet h ∅ 0)) equal
  have left : traceApp (identity h 1) (universeSet h ∅ 0) = universeSet h ∅ 0 :=
    traceApp_graph_beta _ (universeSet_mem_next h ∅ 0)
  have right : traceApp (changedIdentity h) (universeSet h ∅ 0) = ∅ := by
    change traceApp (traceLam (graph _ _)) _ = _
    rw [traceApp_graph_beta _ (universeSet_mem_next h ∅ 0), if_pos rfl]
  rw [left, right] at observed
  have member := seed_mem_zero h (∅ : ZFSet.{u})
  rw [observed] at member
  exact ZFSet.notMem_empty _ member

theorem domain_agreement_does_not_reflect_identity (h : CofinalInaccessibles.{u}) :
    AgreeOnLower h (identity h 0) (identity h 1) ∧
    AgreeOnLower h (identity h 0) (changedIdentity h) ∧
    ¬ (identity h 0 = identity h 0 ↔ identity h 1 = changedIdentity h) := by
  refine ⟨identities_related h, changed_identity_agrees_below h, ?_⟩
  intro reflects
  exact upper_identities_differ h (reflects.mp rfl)

theorem identity_truth_codes_differ (h : CofinalInaccessibles.{u}) :
    ZFSetTraceProofDecoding.truthCode.{u} (identity h 0 = identity h 0) ≠
      ZFSetTraceProofDecoding.truthCode.{u} (identity h 1 = changedIdentity h) := by
  intro equal
  have member : (∅ : ZFSet.{u}) ∈
      ZFSetTraceProofDecoding.truthCode (identity h 0 = identity h 0) :=
    (ZFSetTraceProofDecoding.mem_truthCode _ _).mpr ⟨rfl, rfl⟩
  rw [equal] at member
  exact upper_identities_differ h ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp member).2

/-- The two Id endpoints must use the carrier actually present in its raw
syntax. Merely having two typed identities at different Pi domains does not
permit mixing their certificates inside one Id formation. -/
theorem mixed_identity_formation_rejected :
    check Tower.rules noConversionCheck .nil
      (.id f0 (.lam (.var 0)) (.lam (.var 0))) (.head f0Level)
      (.idForm f0Level f0Formation lowerIdentity upperIdentity) = false := by
  decide

#print axioms changed_identity_typed
#print axioms agreeOnLower_iff_traceFunctionRelated
#print axioms identities_related_on_retained_domains
#print axioms domain_agreement_does_not_reflect_identity
#print axioms identity_truth_codes_differ
#print axioms mixed_identity_formation_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayFunctionComparisonControls
