import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayBetaReductionControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContextComparison

/-!
# Identity fibres with independently checked endpoint certificates

The same raw identity proposition about an applied pair-producing function
is assembled using lower/lower or upper/lower endpoint certificates. Their
internal lambda domains differ. The interpreted source context admits the
arguments in both domains; outside that context the two identity fibres can
differ. The latter is a boundary control, not a failure on valid inputs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayIdentityComparisonControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetReplayApplicationComparisonControls

universe u

private abbrev pairLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev raisedLevel : Tower.Head :=
  .sort (.succ (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def identity : Tower.Tm 1 := .id pairType term term
def lowerIdentityCode : Replay 1 := .idForm pairLevel pairFormation lowerCode lowerCode
def mixedIdentityCode : Replay 1 := .idForm pairLevel pairFormation upperCode lowerCode
def raisedIdentityCode : Replay 1 := .cumul pairLevel mixedIdentityCode
def proofCode : Replay 1 := .reflIntro pairType lowerCode

theorem lower_identity_checked : check Tower.rules noConversionCheck context identity
    (.head pairLevel) lowerIdentityCode = true := by decide

theorem mixed_identity_checked : check Tower.rules noConversionCheck context identity
    (.head pairLevel) mixedIdentityCode = true := by decide

theorem raised_identity_checked : check Tower.rules noConversionCheck context identity
    (.head raisedLevel) raisedIdentityCode = true := by decide

theorem reflexivity_checked : check Tower.rules noConversionCheck context (.refl term)
    identity proofCode = true := by decide

/-- Identity formation checks its carrier and each endpoint, rather than
accepting an arbitrary truth-code construction as typing evidence. -/
theorem wrong_carrier_rejected : check Tower.rules noConversionCheck context
    (.id (.head (.sort Tower.zero)) term term) (.head pairLevel) mixedIdentityCode = false := by
  decide

theorem forged_endpoint_rejected : check Tower.rules noConversionCheck context identity
    (.head pairLevel) (.idForm pairLevel pairFormation .var lowerCode) = false := by decide

noncomputable def lowerIdentityMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => truthCode ((meaning h 0).value env = (meaning h 0).value env))

noncomputable def mixedIdentityMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => truthCode ((meaning h 1).value env = (meaning h 0).value env))

noncomputable def proofMeaning : Meaning.{u} 1 := .plain (fun _ => ∅)

theorem lower_identity_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants lowerIdentityCode
      identity (.head pairLevel) = some (lowerIdentityMeaning h) := rfl

theorem mixed_identity_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants mixedIdentityCode
      identity (.head pairLevel) = some (mixedIdentityMeaning h) := rfl

theorem raised_identity_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants raisedIdentityCode
      identity (.head raisedLevel) = some (mixedIdentityMeaning h) := rfl

theorem reflexivity_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCode
      (.refl term) identity = some proofMeaning := rfl

/-- Actual generation of the wrapped identity exposes the upper/lower
endpoint certificates; checked root-beta comparison aligns their values with
the lower/lower identity. The admission premises come from the context. -/
theorem assembled_identity_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (first second : Meaning.{u} 1)
    (atFirst : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerIdentityCode identity (.head pairLevel) = some first)
    (atSecond : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      raisedIdentityCode identity (.head raisedLevel) = some second)
    (env : Environment.{u} 1) (admitted : valid h env) : first.value env = second.value env := by
  obtain ⟨lowerAdmitted, upperAdmitted⟩ :=
    ZFSetReplayBetaReductionControls.PairProgram.pair_domains_admitted h constants env admitted
  exact identity_rootBeta_endpoints_coherent (interpretHead h ∅ (twoCode h).1 (fun _ => 0))
    constants Tower.rules lowerIdentityCode raisedIdentityCode body body (.var 0) (.var 0)
    pairLevel pairLevel pairFormation lowerCode lowerCode pairFormation upperCode lowerCode
    .hole (.cumul pairLevel .hole) first second reductCode reductCode
    lower_identity_checked raised_identity_checked rfl rfl atFirst atSecond
    reduct_checked reduct_checked reduct_qualified reduct_qualified env
    lowerAdmitted upperAdmitted lowerAdmitted lowerAdmitted

theorem identity_fibres_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 1) (admitted : valid h env) :
    (lowerIdentityMeaning h).value env = (mixedIdentityMeaning h).value env :=
  assembled_identity_values_agree h constants (lowerIdentityMeaning h) (mixedIdentityMeaning h)
    (lower_identity_assembles h constants) (raised_identity_assembles h constants) env admitted

/-- The checked reflexivity program remains a semantic inhabitant when its
consumer independently forms the identity with mixed endpoint certificates
and a cumulative wrapper. -/
theorem reflexivity_member_independent_formation (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (proof formed : Meaning.{u} 1)
    (atProof : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      proofCode (.refl term) identity = some proof)
    (atFormation : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      raisedIdentityCode identity (.head raisedLevel) = some formed)
    (env : Environment.{u} 1) (admitted : valid h env) : proof.value env ∈ formed.value env := by
  rw [reflexivity_assembles h constants] at atProof
  cases Option.some.inj atProof
  rw [← assembled_identity_values_agree h constants (lowerIdentityMeaning h) formed
    (lower_identity_assembles h constants) atFormation env admitted]
  exact (mem_truthCode _ _).mpr ⟨rfl, rfl⟩

theorem nonempty_input_reflexivity_member (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    proofMeaning.value (fun _ => (twoCode h).1) ∈
      (mixedIdentityMeaning h).value (fun _ => (twoCode h).1) :=
  reflexivity_member_independent_formation h constants proofMeaning (mixedIdentityMeaning h)
    (reflexivity_assembles h constants) (raised_identity_assembles h constants)
    _ (nonempty_input_valid h)

def extendedContext : Tower.Ctx 2 := .snoc context identity
def lowerExtendedCode : ContextCode Tower.Head NoConversion 2 :=
  .snoc contextCode pairLevel lowerIdentityCode
def mixedExtendedCode : ContextCode Tower.Head NoConversion 2 :=
  .snoc contextCode raisedLevel raisedIdentityCode

theorem extensions_checked :
    checkContext Tower.rules noConversionCheck extendedContext lowerExtendedCode = true ∧
      checkContext Tower.rules noConversionCheck extendedContext mixedExtendedCode = true := by decide

noncomputable def lowerExtendedValid (h : CofinalInaccessibles.{u}) : Environment.{u} 2 → Prop :=
  fun env => valid h (env ∘ wk) ∧ env 0 ∈ (lowerIdentityMeaning h).value (env ∘ wk)

noncomputable def mixedExtendedValid (h : CofinalInaccessibles.{u}) : Environment.{u} 2 → Prop :=
  fun env => valid h (env ∘ wk) ∧ env 0 ∈ (mixedIdentityMeaning h).value (env ∘ wk)

theorem lower_extension_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerExtendedCode extendedContext = some (lowerExtendedValid h) := rfl

theorem mixed_extension_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      mixedExtendedCode extendedContext = some (mixedExtendedValid h) := rfl

/-- Full comprehension predicates agree because only valid prefix
environments contribute, despite the identity fibres' raw-environment
counterexample below. Both predicates come from actual context assembly. -/
theorem context_extensions_equal (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) : lowerExtendedValid h = mixedExtendedValid h :=
  assembleContext_extension_eq (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    context identity contextCode contextCode pairLevel raisedLevel lowerIdentityCode raisedIdentityCode
    (valid h) (valid h) (lowerIdentityMeaning h) (mixedIdentityMeaning h)
    (lowerExtendedValid h) (mixedExtendedValid h)
    (context_assembles h constants) (context_assembles h constants)
    (lower_identity_assembles h constants) (raised_identity_assembles h constants)
    (lower_extension_assembles h constants) (mixed_extension_assembles h constants)
    (fun _ => Iff.rfl) (identity_fibres_agree h constants)

theorem nonempty_extended_environment (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    lowerExtendedValid h (Fin.cases ∅ (fun _ => (twoCode h).1)) ∧
      mixedExtendedValid h (Fin.cases ∅ (fun _ => (twoCode h).1)) := by
  have lower : lowerExtendedValid h (Fin.cases ∅ (fun _ => (twoCode h).1)) :=
    ⟨nonempty_input_valid h, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩
  exact ⟨lower, context_extensions_equal h constants ▸ lower⟩

/-- On the excluded input `X = U₀`, the lower endpoint produces the empty
set while the upper endpoint produces a pair. Hence the mixed identity fibre
is empty although the lower/lower fibre still contains reflexivity. -/
theorem invalid_environment_identity_boundary (h : CofinalInaccessibles.{u}) :
    ¬ valid h (fun _ => universeSet h ∅ 0) ∧
      (∅ : ZFSet.{u}) ∈ (lowerIdentityMeaning h).value (fun _ => universeSet h ∅ 0) ∧
      (mixedIdentityMeaning h).value (fun _ => universeSet h ∅ 0) = ∅ := by
  refine ⟨(invalid_input_values h).1, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩, ?_⟩
  apply ZFSet.ext
  intro x
  change x ∈ truthCode ((meaning h 1).value (fun _ => universeSet h ∅ 0) =
    (meaning h 0).value (fun _ => universeSet h ∅ 0)) ↔ x ∈ (∅ : ZFSet.{u})
  rw [mem_truthCode]
  constructor
  · intro member
    exact ((invalid_input_distinguishes h) member.2.symm).elim
  · intro impossible
    exact (ZFSet.notMem_empty _ impossible).elim

theorem invalid_prefix_rejected_by_both_extensions (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ¬ lowerExtendedValid h (Fin.cases ∅ (fun _ => universeSet h ∅ 0)) ∧
      ¬ mixedExtendedValid h (Fin.cases ∅ (fun _ => universeSet h ∅ 0)) := by
  have lower : ¬ lowerExtendedValid h (Fin.cases ∅ (fun _ => universeSet h ∅ 0)) :=
    fun admitted => (invalid_input_values h).1 admitted.1
  exact ⟨lower, fun admitted => lower ((context_extensions_equal h constants).symm ▸ admitted)⟩

/-- These checked beta-dependent extensions lie outside the generic
neutral-formation fragment; their comparison above genuinely needs the
context-relative endpoint computation theorem. -/
theorem beta_identity_outside_neutral_fragment :
    lowerExtendedCode.neutralFormations extendedContext = false ∧
      mixedExtendedCode.neutralFormations extendedContext = false := ⟨rfl, rfl⟩

namespace NeutralTelescope

open ZFSetReplayInterpretationControls

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)

/-- The same dependent telescope `x : Ground, p : Id Ground x x`, with
independently raised formation evidence at both declarations. -/
def raisedContextCode : ContextCode Tower.Head NoConversion 2 :=
  .snoc (.snoc .nil one (.cumul zero .headType)) one
    (.cumul zero (.idForm zero .headType .var .var))

theorem both_contexts_checked :
    checkContext Tower.rules noConversionCheck identityContext identityContextCode = true ∧
      checkContext Tower.rules noConversionCheck identityContext raisedContextCode = true := by decide

theorem both_contexts_qualified :
    identityContextCode.neutralFormations identityContext = true ∧
      raisedContextCode.neutralFormations identityContext = true := ⟨rfl, rfl⟩

/-- Generic neutral-telescope coherence compares independently supplied
assembly receipts, including the different cumulative formation choices. -/
theorem assembled_environments_equal (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (first second : Environment.{u} 2 → Prop)
    (atFirst : assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      identityContextCode identityContext = some first)
    (atSecond : assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      raisedContextCode identityContext = some second) : first = second :=
  assembleContext_neutralFormations_coherent (interpretHead h ∅ (twoCode h).1 (fun _ => 0))
    constants Tower.rules identityContextCode both_contexts_checked.1 both_contexts_qualified.1
    atFirst both_contexts_checked.2 atSecond

end NeutralTelescope

#print axioms lower_identity_checked
#print axioms mixed_identity_checked
#print axioms raised_identity_checked
#print axioms reflexivity_checked
#print axioms wrong_carrier_rejected
#print axioms forged_endpoint_rejected
#print axioms invalid_environment_identity_boundary
#print axioms assembled_identity_values_agree
#print axioms reflexivity_member_independent_formation
#print axioms nonempty_input_reflexivity_member
#print axioms context_extensions_equal
#print axioms nonempty_extended_environment
#print axioms invalid_prefix_rejected_by_both_extensions
#print axioms beta_identity_outside_neutral_fragment
#print axioms NeutralTelescope.assembled_environments_equal

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayIdentityComparisonControls
