import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HigherOrderSearchedProof
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofConsumption
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofConsumptionSubstitution

/-!
# Actual searched evidence producing another native proof

The searched higher-order theorem supplies the premise of a retained proof
consumer. Its compiled program calls a supplied continuation with that exact
searched inhabitant. The continuation is itself compiled from retained HOL
syntax. Application is typed and denotes the new conclusion in the same
dependent-family model; two directed beta steps return a new proof closure.

The connecting conclusion is different from the search query. The provider
is not replaced or searched again. The source trees, their compiled terms,
and their typed application are all retained. This is a proof-transforming
native loop, not a verification of the C chainer or unrestricted reflection.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HigherOrderProofFeedback

open Mettapedia.Logic HOL Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open FormationSensitiveHOLGenericProofInstances.CallGuard

private abbrev signature := FormationSensitiveHOLInvariant.signature
private abbrev operations := Operations.logicalOnly signature proofName proofName_fresh

def conclusion : ClosedFormula Constant := .imp HigherOrderSearchedProof.query HigherOrderSearchedProof.query

def consumerFormula : ClosedFormula Constant :=
  .imp (.imp HigherOrderSearchedProof.query conclusion) conclusion

def consumer : ProofSyntax Constant [HigherOrderSearchedProof.query] consumerFormula :=
  HOLNativeProofConsumption.continuation HigherOrderSearchedProof.query conclusion

def program : Tower.Tm 0 :=
  .lam (.app (.var 0) (rename wk HigherOrderSearchedProof.native))

private theorem providerCompiled :
    compile signature proofName operations HigherOrderSearchedProof.found.proof
      Fin.elim0 Fin.elim0 = some HigherOrderSearchedProof.native := by
  simpa only [HigherOrderSearchedProof.compilation, ProofSearch.HOLAdapter.compileOutcome?,
    BoundedHOLProofPlanning.outcome, HigherOrderSearchedProof.tree_emitted] using
    HigherOrderSearchedProof.native_emitted

theorem consumer_compiles : compile signature proofName operations consumer Fin.elim0
    (fun _ => HigherOrderSearchedProof.native) = some program := by
  obtain ⟨code, represented, _typed⟩ := HigherOrderSearchedProof.native_typed
  have representedMajor : represent signature (.imp HigherOrderSearchedProof.query conclusion) =
      some (FormationSensitiveHOLGenericProofFamily.rawImp signature code
        (FormationSensitiveHOLGenericProofFamily.rawImp signature code code)) := by
    simp only [conclusion, FormationSensitiveHOLGenericProofFamily.represent_imp,
      represented]
    rfl
  change (represent signature (.imp HigherOrderSearchedProof.query conclusion)).bind
    (fun _ => some program) = some program
  rw [representedMajor]
  rfl

theorem driver_emits_program : HOLNativeProofConsumption.compile? signature proofName operations
    HigherOrderSearchedProof.found.proof consumer Fin.elim0 Fin.elim0 = some program := by
  simp only [HOLNativeProofConsumption.compile?, providerCompiled]
  exact consumer_compiles

/-- The retained searched provider and compiled consumer can be moved into
any native context by the same substitution; compilation keeps their exact
returned program, including the proof captured by its continuation. -/
theorem driver_substitute {m : Nat} (sigma : Sub Tower.Head 0 m) :
    HOLNativeProofConsumption.compile? signature proofName operations
        HigherOrderSearchedProof.found.proof consumer
        (fun index => subst sigma (Fin.elim0 index))
        (fun index => subst sigma (Fin.elim0 index)) =
      some (subst sigma program) := by
  rw [HOLNativeProofConsumption.compile_substitute signature proofName operations
    RawOperations.logicalOnly_natural HigherOrderSearchedProof.found.proof consumer
    (n := 0) Fin.elim0 Fin.elim0 sigma, driver_emits_program]
  rfl

/-- This source extensional proof is valid, but this operation algebra omits it. -/
def unsupportedProvider : ProofSyntax Constant []
    (.eq (.lam (.app (HOL.weaken (.lam (.var .vz) : Term Constant [] (stateType ⇒ stateType)))
      (.var .vz))) (.lam (.var .vz))) :=
  .eta (.lam (.var .vz))

theorem unsupported_provider_stops : HOLNativeProofConsumption.compile? signature proofName operations
    unsupportedProvider (HOLNativeProofConsumption.continuation _ conclusion)
    (n := 0) Fin.elim0 Fin.elim0 = none := by
  apply HOLNativeProofConsumption.unsupported_provider
  rfl

private theorem objectsTyped : GenericTyping.Objects signature (gamma := []) .nil Fin.elim0 := by
  intro index
  nomatch index

private theorem hypothesesTyped : GenericTyping.Hypotheses signature operations
    (gamma := []) (delta := []) .nil Fin.elim0 Fin.elim0 := by
  intro index
  nomatch index

private theorem consumeTyped {formula : ClosedFormula Constant}
    (source : ProofSyntax Constant [HigherOrderSearchedProof.query] formula)
    {returned : Tower.Tm 0}
    (compiled : compile signature proofName operations source Fin.elim0
      (fun _ => HigherOrderSearchedProof.native) = some returned) :
    ∃ code, represent signature formula = some code ∧
      FormationSensitive.Typing operations.target .nil returned
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  obtain ⟨code, represented, typed⟩ :=
    HOLNativeProofConsumption.typed signature proofName operations (gamma := [])
      HigherOrderSearchedProof.found.proof source objectsTyped hypothesesTyped
      providerCompiled compiled
  refine ⟨code, represented, ?_⟩
  change FormationSensitive.Typing operations.target .nil returned
    (FormationSensitiveHOLGenericProofFamily.proof proofName
      (Presentation.subst (Fin.elim0 : Sub Tower.Head 0 0) (code : Tower.Tm 0))) at typed
  rw [TelescopeAbstraction.subst_empty, TelescopeAbstraction.liftClosed_zero] at typed
  exact typed

theorem program_typed :
    ∃ code, represent signature consumerFormula = some code ∧
      FormationSensitive.Typing operations.target .nil program
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) :=
  consumeTyped consumer consumer_compiles

theorem program_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property) program consumerFormula := by
  apply HOLNativeProofConsumption.denotes signature proofName operations
    (CallGuardSemantics.semantics property) HigherOrderSearchedProof.found.proof consumer
    providerCompiled consumer_compiles (CallGuardSemantics.emptyState property)
  intro index
  nomatch index

/-- A retained continuation turns the supplied proof into an implication proof. -/
def continuation : ProofSyntax Constant [] (.imp HigherOrderSearchedProof.query conclusion) :=
  .impI (.impI (.hyp 1))

def nativeContinuation : Tower.Tm 0 := .lam (.lam (.var 1))

theorem continuation_compiles : compile signature proofName operations continuation
    Fin.elim0 Fin.elim0 = some nativeContinuation := by
  obtain ⟨_code, represented, _typed⟩ := HigherOrderSearchedProof.native_typed
  change (represent signature HigherOrderSearchedProof.query).bind
    (fun _ => (represent signature HigherOrderSearchedProof.query).bind
      (fun _ => some nativeContinuation)) = some nativeContinuation
  rw [represented]
  rfl

theorem continuation_typed :
    ∃ code, represent signature (.imp HigherOrderSearchedProof.query conclusion) = some code ∧
      FormationSensitive.Typing operations.target .nil nativeContinuation
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) :=
  GenericTyping.compile_closed signature proofName operations continuation continuation_compiles

theorem continuation_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property) nativeContinuation
      (.imp HigherOrderSearchedProof.query conclusion) := by
  apply GenericSemantics.compile_denotes signature proofName operations
    (CallGuardSemantics.semantics property) continuation continuation_compiles
    (CallGuardSemantics.emptyState property)
  intro index
  nomatch index

def application : ProofSyntax Constant
    [consumerFormula, .imp HigherOrderSearchedProof.query conclusion] conclusion :=
  .impE (.hyp 0) (.hyp 1)

def supplied : Fin 2 → Tower.Tm 0 := Fin.cases program (fun _ => nativeContinuation)

theorem application_compiles : compile signature proofName operations application
    Fin.elim0 supplied = some (.app program nativeContinuation) := rfl

theorem application_typed :
    ∃ code, represent signature conclusion = some code ∧
      FormationSensitive.Typing operations.target .nil (.app program nativeContinuation)
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  have actualHypotheses : GenericTyping.Hypotheses signature operations .nil Fin.elim0
      (delta := [consumerFormula, .imp HigherOrderSearchedProof.query conclusion]) supplied := by
    intro index
    refine Fin.cases ?_ (fun remaining => ?_) index
    · change ∃ code, represent signature consumerFormula = some code ∧
        FormationSensitive.Typing operations.target .nil program
          (FormationSensitiveHOLGenericProofFamily.proof proofName (Presentation.subst Fin.elim0 code))
      simpa only [TelescopeAbstraction.subst_empty,
        TelescopeAbstraction.liftClosed_zero] using program_typed
    · have zero : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      change ∃ code, represent signature (.imp HigherOrderSearchedProof.query conclusion) = some code ∧
        FormationSensitive.Typing operations.target .nil nativeContinuation
          (FormationSensitiveHOLGenericProofFamily.proof proofName (Presentation.subst Fin.elim0 code))
      simpa only [TelescopeAbstraction.subst_empty,
        TelescopeAbstraction.liftClosed_zero] using continuation_typed
  simpa only [TelescopeAbstraction.subst_empty, TelescopeAbstraction.liftClosed_zero] using
    GenericTyping.compile_typed signature proofName operations application
      objectsTyped actualHypotheses application_compiles

theorem application_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property)
      (.app program nativeContinuation) conclusion := by
  apply GenericSemantics.compile_denotes signature proofName operations
    (CallGuardSemantics.semantics property) application application_compiles
    (CallGuardSemantics.emptyState property)
  intro index
  refine Fin.cases ?_ (fun remaining => ?_) index
  · exact program_denotes property
  · have zero : remaining = 0 := Fin.eq_zero remaining
    subst remaining
    exact continuation_denotes property

/-- Execution calls the continuation, rather than simply returning its input. -/
theorem calls_continuation : TelescopeAbstraction.BetaSteps (.app program nativeContinuation)
    (.app nativeContinuation HigherOrderSearchedProof.native) := by
  apply Relation.ReflTransGen.single
  have step := StepCore.betaPi (root := (RootComputation.empty : RootComputation Tower.Head))
      (headEq := fun _ _ => False)
      (.app (.var 0) (rename wk HigherOrderSearchedProof.native)) nativeContinuation
  change StepCore RootComputation.empty (fun _ _ => False)
    (.app program nativeContinuation)
    (.app nativeContinuation (inst0 nativeContinuation (rename wk HigherOrderSearchedProof.native))) at step
  rw [inst0_rename_wk] at step
  exact step

theorem returns_new_proof : TelescopeAbstraction.BetaSteps (.app program nativeContinuation)
    (.lam (rename wk HigherOrderSearchedProof.native)) := by
  apply calls_continuation.trans
  apply Relation.ReflTransGen.single
  exact (StepCore.betaPi (root := (RootComputation.empty : RootComputation Tower.Head))
      (headEq := fun _ _ => False) (.lam (.var 1)) HigherOrderSearchedProof.native)

/-- The returned closure keeps the actual supplied proof under its new binder. -/
def returnedProof : ProofSyntax Constant [HigherOrderSearchedProof.query] conclusion :=
  .impI (.hyp 1)

theorem returned_compiles : compile signature proofName operations returnedProof
    Fin.elim0 (fun _ => HigherOrderSearchedProof.native) =
      some (.lam (rename wk HigherOrderSearchedProof.native)) := by
  obtain ⟨_code, represented, _typed⟩ := HigherOrderSearchedProof.native_typed
  change (represent signature HigherOrderSearchedProof.query).bind
    (fun _ => some (.lam (rename wk HigherOrderSearchedProof.native) : Tower.Tm 0)) =
      some (.lam (rename wk HigherOrderSearchedProof.native))
  rw [represented]
  rfl

theorem returned_typed :
    ∃ code, represent signature conclusion = some code ∧
      FormationSensitive.Typing operations.target .nil
        (.lam (rename wk HigherOrderSearchedProof.native))
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) :=
  consumeTyped returnedProof returned_compiles

theorem returned_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property)
      (.lam (rename wk HigherOrderSearchedProof.native)) conclusion := by
  apply HOLNativeProofConsumption.denotes signature proofName operations
    (CallGuardSemantics.semantics property) HigherOrderSearchedProof.found.proof returnedProof
    providerCompiled returned_compiles (CallGuardSemantics.emptyState property)
  intro index
  nomatch index

theorem changed_conclusion : conclusion ≠ HigherOrderSearchedProof.query := by
  intro equal
  cases equal

#print axioms consumer_compiles
#print axioms driver_emits_program
#print axioms driver_substitute
#print axioms unsupported_provider_stops
#print axioms program_typed
#print axioms program_denotes
#print axioms application_typed
#print axioms application_denotes
#print axioms returns_new_proof
#print axioms returned_typed
#print axioms returned_denotes
#print axioms changed_conclusion

end HigherOrderProofFeedback
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
