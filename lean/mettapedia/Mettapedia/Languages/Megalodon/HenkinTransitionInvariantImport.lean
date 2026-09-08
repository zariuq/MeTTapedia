import Mettapedia.Languages.Megalodon.HenkinTransitionInvariantProof
import Mettapedia.Languages.Megalodon.HenkinProofSoundness
import Mettapedia.Logic.HOL.TypeSubstitutionSemantics

/-!
# Native proof acceptance used by the call-guard operational model

The source model is the existing full-domain type reduct of the call-guard
model. Its three primitive symbols are interpreted by the existing operational
symbols, without redefining their meanings. Type substitution carries the
actual native statement back to the call-guard formula, and model satisfaction
transports along that map. Soundness of the supported native proof constructors
turns actual checker acceptance into model validity, which is then applied to
finite compiler runs. The existing intrinsic preservation derivation is not
used by this route.

The checked source is the Lean Mathdata kernel. Parsing, foreign execution,
and an implementation-refinement theorem for another checker remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTransitionInvariantImport

open MathdataKernel
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.TransitionInvariant
open HenkinTermInterpretation
open HenkinTransitionInvariantProof
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

abbrev NativeConstant := Constant environment

/-- The native state sort is interpreted by the existing compiler-state sort. -/
def typeProjection (_ : Base) : Ty Unit := MainlineCallGuardHOLInvariant.stateType

/-- The finite native signature is interpreted by the already specified
operational symbols. Lookup evidence determines each symbol's complete type. -/
def constantProjection {type : Ty Base} (constant : NativeConstant type) :
    MainlineCallGuardHOLInvariant.Constant (Ty.substitute typeProjection type) := by
  cases constant with
  | named name declaration lookup typed =>
      simp [environment, Environment.lookupTerm?, lookupTermList?] at lookup
  | primitive index lookup =>
      cases index with
      | zero =>
          have equal : type = (.base (.inr 0) ⇒ .base (.inr 0) ⇒ .prop) :=
            reifyType_injective (Option.some.inj lookup).symm
          subst type
          exact .step
      | succ index =>
          cases index with
          | zero =>
              have equal : type = (.base (.inr 0) ⇒ .base (.inr 0) ⇒ .prop) :=
                reifyType_injective (Option.some.inj lookup).symm
              subst type
              exact .sameResult
          | succ index =>
              cases index with
              | zero =>
                  have equal : type = (.base (.inr 0) ⇒ .prop) :=
                    reifyType_injective (Option.some.inj lookup).symm
                  subst type
                  exact .property
              | succ index => simp [environment] at lookup

/-- Reuse of the existing type-derived model construction; no source validity
is inferred from proof acceptance in defining this model. -/
def model (property : CompileLanguageControl → Prop) :
    HenkinModel.{0, 0, 0} Base NativeConstant :=
  HenkinModel.standardTypeReduct typeProjection constantProjection
    (MainlineCallGuardHOLInvariant.model property)

def emptyValuation (property : CompileLanguageControl → Prop) :
    (model property).Valuation [] := fun index => nomatch index

def interpretedHypotheses : List (ClosedFormula NativeConstant) :=
  MainlineCallGuardHOLInvariant.assumptions.map interpretFormula

def interpretedConclusion : ClosedFormula NativeConstant :=
  interpretFormula MainlineCallGuardHOLInvariant.conclusion

/-- The source and target formulas retain exactly the same three symbols
and binder positions under the two existing type-substitution maps. -/
theorem hypotheses_roundTrip :
    interpretedHypotheses.map (mapTypes typeProjection constantProjection) =
      MainlineCallGuardHOLInvariant.assumptions := rfl

theorem conclusion_roundTrip :
    mapTypes typeProjection constantProjection interpretedConclusion =
      MainlineCallGuardHOLInvariant.conclusion := rfl

theorem models_correspond (property : CompileLanguageControl → Prop)
    (formula : ClosedFormula NativeConstant) :
    (model property).models formula ↔
      (MainlineCallGuardHOLInvariant.model property).models
        (mapTypes typeProjection constantProjection formula) :=
  HenkinModel.models_mapTypes typeProjection constantProjection
    (MainlineCallGuardHOLInvariant.model property)
    (HenkinModel.fullDomains_standard _ _) formula

private theorem models_iff_denote_closed {B : Type} {C : Ty B → Type}
    (M : HenkinModel.{0, 0, 0} B C) (formula : ClosedFormula C)
    (valuation : M.Valuation []) :
    M.models formula ↔ (M.denote formula valuation).down :=
  Iff.of_eq (congrArg ULift.down (M.denote_closed_valuation_eq formula _ valuation))

/-- Model hypotheses are discharged from compiler denotation preservation,
not from an intrinsic derivation or the native proof being accepted. -/
theorem resultPredicate_satisfies_hypotheses (observe : CompilationResult → Prop) :
    Soundness.SatisfiesHyps (model (fun state => observe state.denote))
      (emptyValuation _) interpretedHypotheses := by
  intro formula member
  have targetMember : mapTypes typeProjection constantProjection formula ∈
      MainlineCallGuardHOLInvariant.assumptions := by
    rw [← hypotheses_roundTrip]
    exact List.mem_map.mpr ⟨formula, member, rfl⟩
  apply (models_iff_denote_closed _ formula (emptyValuation _)).mp
  apply (models_correspond (fun state => observe state.denote) formula).mpr
  apply (models_iff_denote_closed _ _
    (MainlineCallGuardHOLInvariant.emptyValuation _)).mpr
  exact MainlineCallGuardHOLInvariant.resultPredicate_satisfies_assumptions observe _ targetMember

/-- There are no named definitions in the native primitive signature. -/
def checkedDefinitions : CheckedPlainDefinitions environment where
  body := by
    intro name declaration body lookup defined eligible
    simp [environment, Environment.lookupTerm?, lookupTermList?] at lookup

theorem definitionEquations (property : CompileLanguageControl → Prop) :
    DefinitionEquations checkedDefinitions (model property) where
  equation := by
    intro type name declaration lookup typed body defined
    simp [environment, Environment.lookupTerm?, lookupTermList?] at lookup

theorem hypotheses_erased :
    interpretedHypotheses.map erase = nativeAssumptions.map some :=
  statement_correspondence.1

theorem conclusion_erased : erase interpretedConclusion = some nativeConclusion :=
  statement_correspondence.2

private theorem plainEnvironment : PlainEnvironment environment 0 where
  named := by
    intro name declaration lookup
    simp [environment, Environment.lookupTerm?, lookupTermList?] at lookup
  primitive := by
    intro index type lookup
    have member := List.mem_of_getElem? lookup
    simp only [environment, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide

/-- The actual proof object lies in the recursively supported fragment. Its
embedded terms use the checked native signature, not semantic assumptions. -/
theorem proof_fragment : NativeProof.Fragment environment 0 nativeProof := by
  unfold nativeProof
  repeat' first
    | apply NativeProof.Fragment.termLam
    | apply NativeProof.Fragment.proofLam
    | apply NativeProof.Fragment.proofApp
    | apply NativeProof.Fragment.termApp
    | exact NativeProof.Fragment.hyp _
    | exact plainEnvironment.plainLookups (by rfl)
    | rfl

/-- The native signature contains no named propositions to assume. -/
theorem knownValidity (property : CompileLanguageControl → Prop) :
    NativeProof.KnownValidity (model property) := by
  intro name raw lookup
  simp [environment, Environment.lookupKnown?, lookupKnownList?] at lookup

theorem emptyValuation_admissible (property : CompileLanguageControl → Prop) :
    (model property).ValuationAdmissible (emptyValuation property) := by
  intro type index
  nomatch index

/-- The accepted native proof establishes the operationally interpreted
preservation sentence. This applies native proof soundness, not the separately
constructed intrinsic derivation of the same formula. -/
theorem native_checked_preservation (observe : CompilationResult → Prop) :
    (MainlineCallGuardHOLInvariant.model (fun state => observe state.denote)).models
      MainlineCallGuardHOLInvariant.conclusion := by
  have sourceValid : (model (fun state => observe state.denote)).models interpretedConclusion := by
    apply (models_iff_denote_closed _ interpretedConclusion (emptyValuation _)).mpr
    exact NativeProof.checkProof_sound checkedDefinitions _ (definitionEquations _)
      (knownValidity _) proof_fragment hypotheses_erased interpretedConclusion conclusion_erased
      native_proof_accepted (emptyValuation _) (emptyValuation_admissible _)
      (resultPredicate_satisfies_hypotheses observe)
  have valid := (models_correspond (fun state => observe state.denote) interpretedConclusion).mp
    sourceValid
  simpa only [conclusion_roundTrip] using valid

/-- One actual compiler transition preserves a result predicate using the
validity obtained from the source proof checker. -/
theorem native_step_preserves_result (observe : CompilationResult → Prop)
    {source target : CompileLanguageControl}
    (transition : compileLanguageGSLT.Step source target)
    (holds : observe source.denote) : observe target.denote := by
  have valid := (models_iff_denote_closed _ _
    (MainlineCallGuardHOLInvariant.emptyValuation _)).mp (native_checked_preservation observe)
  have preserved := (denote_preservationFormula
    (MainlineCallGuardHOLInvariant.model (fun state => observe state.denote))
    (MainlineCallGuardHOLInvariant.emptyValuation _)
    (.const .step) (.const .property)).mp valid
  exact preserved (ULift.up source) trivial (ULift.up target) trivial transition holds

/-- The native-proof route transports the property along every finite run,
without asserting termination of arbitrary computations. -/
theorem native_run_preserves_result (observe : CompilationResult → Prop)
    {source target : CompileLanguageControl}
    (run : compileLanguageGSLT.MultiStep source target)
    (holds : observe source.denote) : observe target.denote := by
  have finite := MainlineCallGuardHOLInvariant.multiStep_finite run
  clear run
  induction finite with
  | refl => exact holds
  | tail run transition ih => exact native_step_preserves_result observe transition ih

/-- A compiled result reached by the real call-guard machine equals the
reference compilation, through acceptance of the native proof object. -/
theorem native_halts_with_specification
    (owned : MainlineCallGuardProjection.OwnedSnapshot) (head : String) (arity : Nat)
    {result : CompilationResult}
    (run : compileLanguageGSLT.MultiStep (compileLanguageStart owned head arity)
      (.halted result)) : result = compileGuards owned head arity :=
  native_run_preserves_result (fun actual => actual = compileGuards owned head arity)
    run (compileLanguageStart_denote_exact owned head arity)

/-- Keeping source acceptance while changing the model does not make the
operational conclusion true. The source model's failed premise remains visible. -/
theorem altered_model_refutes_conclusion :
    ¬ (model MainlineCallGuardHOLInvariant.runningPredicate).models interpretedConclusion := by
  intro valid
  have targetValid := (models_correspond _ interpretedConclusion).mp valid
  rw [conclusion_roundTrip] at targetValid
  exact MainlineCallGuardHOLInvariant.altered_interpretation_not_valid targetValid

/-- Native soundness locates the failed interface of the altered model: the
actual source proof is accepted, but its interpreted assumptions cannot hold. -/
theorem altered_model_refutes_hypotheses :
    ¬ Soundness.SatisfiesHyps (model MainlineCallGuardHOLInvariant.runningPredicate)
      (emptyValuation _) interpretedHypotheses := by
  intro satisfied
  apply altered_model_refutes_conclusion
  apply (models_iff_denote_closed _ interpretedConclusion (emptyValuation _)).mpr
  exact NativeProof.checkProof_sound checkedDefinitions _ (definitionEquations _)
    (knownValidity _) proof_fragment hypotheses_erased interpretedConclusion conclusion_erased
    native_proof_accepted (emptyValuation _) (emptyValuation_admissible _) satisfied

#print axioms hypotheses_roundTrip
#print axioms models_correspond
#print axioms resultPredicate_satisfies_hypotheses
#print axioms definitionEquations
#print axioms proof_fragment
#print axioms native_checked_preservation
#print axioms native_run_preserves_result
#print axioms native_halts_with_specification
#print axioms altered_model_refutes_conclusion
#print axioms altered_model_refutes_hypotheses

end Mettapedia.Languages.Megalodon.HenkinTransitionInvariantImport
