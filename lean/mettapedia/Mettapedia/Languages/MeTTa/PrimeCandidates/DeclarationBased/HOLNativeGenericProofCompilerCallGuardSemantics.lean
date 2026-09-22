import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeGenericProofCompilerCallGuard
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLHenkinFamilySemantics

/-!
# Call-guard semantics of the generic native HOL proof compiler

The retained call-guard preservation proof is the second semantic instance of
the signature-generic compiler.  Its source constants are interpreted in the
actual standard model of the compiler micro-machine, while native variables,
abstraction and application are interpreted in the generic dependent-family
model.

The two source assumptions remain explicit proof variables.  For the result
observation they have an independently constructed semantic environment; for
the altered control-state observation no such environment exists.  Thus the
compiler theorem neither invents the assumptions nor validates a false
interpretation vacuously as a closed theorem.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
namespace CallGuardSemantics

open Presentation Mettapedia.Logic
open FormationSensitiveHOLInterface
open HenkinFamilySemantics
open FormationSensitiveHOLGenericProofInstances.CallGuard
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open HOL.TransitionInvariant

abbrev CallGuardModel (property : CompileLanguageControl → Prop) :=
  model property

/-- The call-guard standard model supplies the full-domain premise required
only by universal proof introduction. -/
theorem callGuardModel_fullDomains
    (property : CompileLanguageControl → Prop) :
    (CallGuardModel property).FullDomains :=
  HOL.HenkinModel.fullDomains_standard Carrier
    (constantDenotation property)

/-- The empty mixed state for a closed source object context. -/
def emptyState (property : CompileLanguageControl → Prop) :
    State FormationSensitiveHOLInvariant.signature (CallGuardModel property)
      (gamma := []) (n := 0) Fin.elim0 where
  context := SemanticContext.nil
  valuation := fun _ => emptyValuation property
  objectsDenote := by
    intro type index
    nomatch index

def refinementAssumption : HOL.ClosedFormula Constant :=
  refinementFormula (.const .step) (.const .sameResult)

def preservationAssumption : HOL.ClosedFormula Constant :=
  preservationFormula (.const .sameResult) (.const .property)

/-- The mixed telescope in which the retained proof is open over precisely its
two declared assumptions. -/
def assumptionObjects : Sub Tower.Head 0 2 :=
  fun index => Presentation.rename wk
    (Presentation.rename wk (Fin.elim0 index))

def assumptionState (property : CompileLanguageControl → Prop) :
    State FormationSensitiveHOLInvariant.signature (CallGuardModel property)
      (gamma := []) assumptionObjects :=
  proofExtension
    (proofExtension (emptyState property) refinementAssumption)
    preservationAssumption

abbrev semantics (property : CompileLanguageControl → Prop) :=
  logicalOnlyAlgebra FormationSensitiveHOLInvariant.signature proofName
    proofName_fresh (CallGuardModel property) (callGuardModel_fullDomains property)

/-- The two actual native variables denote the two actual source assumptions
in source-list order. -/
theorem hypotheses_denote (property : CompileLanguageControl → Prop) :
    GenericSemantics.Hypotheses (semantics property)
      (assumptionState property) CallGuard.hypotheses := by
  intro index
  fin_cases index
  · exact Proves.weakenProof
      (proofExtension (emptyState property) refinementAssumption)
      (Proves.variable (emptyState property) refinementAssumption)
  · exact Proves.variable
      (proofExtension (emptyState property) refinementAssumption)
      preservationAssumption

/-- Every successful result of compiling the retained CallGuard proof denotes
its exact source conclusion in the actual compiler-state model. -/
theorem preservation_denotes (property : CompileLanguageControl → Prop)
    {native : Tower.Tm 2}
    (success : compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh) preservationSyntax
      assumptionObjects CallGuard.hypotheses = some native) :
    Proves (assumptionState property) native conclusion := by
  exact GenericSemantics.compile_denotes
    FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
      proofName_fresh)
    (semantics property) preservationSyntax success
    (assumptionState property) (hypotheses_denote property)

/-- The compiler really emits a native term, and that same term denotes the
retained CallGuard conclusion. -/
theorem preservation_compiles_and_denotes
    (property : CompileLanguageControl → Prop) :
    ∃ native,
      compile FormationSensitiveHOLInvariant.signature proofName
        (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
          proofName_fresh) preservationSyntax
        assumptionObjects CallGuard.hypotheses = some native ∧
      Proves (assumptionState property) native conclusion := by
  refine ⟨_, rfl, ?_⟩
  exact preservation_denotes property rfl

/-- Independent truth of the two source assumptions constructs a genuine
environment of their native proof-variable telescope. -/
def assumptionEnvironment (observe : CompilationResult → Prop) :
    (assumptionState (fun state => observe state.denote)).context.Environment := by
  have satisfied := resultPredicate_satisfies_assumptions observe
  have refinementTrue :
      ((CallGuardModel (fun state => observe state.denote)).denote
        refinementAssumption (emptyValuation _)).down :=
    satisfied refinementAssumption (by simp [assumptions, refinementAssumption])
  have preservationTrue :
      ((CallGuardModel (fun state => observe state.denote)).denote
        preservationAssumption (emptyValuation _)).down :=
    satisfied preservationAssumption (by simp [assumptions, preservationAssumption])
  exact ⟨⟨PUnit.unit, ULift.up ⟨refinementTrue⟩⟩,
    ULift.up ⟨preservationTrue⟩⟩

/-- Evaluating the exact compiled proof section at the independently supplied
assumption environment yields the closed semantic conclusion. -/
theorem compiled_conclusion_true (observe : CompilationResult → Prop)
    {native : Tower.Tm 2}
    (success : compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh) preservationSyntax
      assumptionObjects CallGuard.hypotheses = some native) :
    ((CallGuardModel (fun state => observe state.denote)).denote conclusion
      (emptyValuation _)).down := by
  obtain ⟨value, _nativeMeaning⟩ :=
    preservation_denotes (fun state => observe state.denote) success
  have closed := (value (assumptionEnvironment observe)).down.down
  exact closed

/-- One actual compiler step preserves the selected result observation by
consuming the semantic conclusion delivered by the compiled native proof. -/
theorem step_preserved_by_compiled_proof (observe : CompilationResult → Prop)
    {native : Tower.Tm 2}
    (success : compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh) preservationSyntax
      assumptionObjects CallGuard.hypotheses = some native)
    {source target : CompileLanguageControl}
    (transition : compileLanguageGSLT.Step source target)
    (holds : observe source.denote) : observe target.denote := by
  have conclusionTrue := compiled_conclusion_true observe success
  have preserves :=
    (HOL.TransitionInvariant.denote_preservationFormula
      (CallGuardModel (fun state => observe state.denote)) (emptyValuation _)
      (.const Constant.step) (.const Constant.property)).mp conclusionTrue
  exact preserves (ULift.up source) trivial (ULift.up target) trivial
    transition holds

/-- The compiled proof, rather than a separate source-proof invocation,
transports the observation along every finite GSLT run. -/
theorem run_preserved_by_compiled_proof (observe : CompilationResult → Prop)
    {native : Tower.Tm 2}
    (success : compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh) preservationSyntax
      assumptionObjects CallGuard.hypotheses = some native) :
    ∀ {source target : CompileLanguageControl},
      compileLanguageGSLT.MultiStep source target →
      observe source.denote → observe target.denote
  | _, _, .refl _, holds => holds
  | _, _, .step transition rest, holds =>
      run_preserved_by_compiled_proof observe success rest
        (step_preserved_by_compiled_proof observe success transition holds)

/-- Concrete end-to-end control: a halting micro-machine run has the reference
compiler result, with preservation obtained from the actual compiled proof. -/
theorem halts_with_specification_from_compiled_proof
    (owned : OwnedSnapshot) (head : String) (arity : Nat)
    {native : Tower.Tm 2}
    (success : compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName
        proofName_fresh) preservationSyntax
      assumptionObjects CallGuard.hypotheses = some native)
    {result : CompilationResult}
    (run : compileLanguageGSLT.MultiStep (compileLanguageStart owned head arity)
      (.halted result)) :
    result = compileGuards owned head arity := by
  exact run_preserved_by_compiled_proof
    (fun actual => actual = compileGuards owned head arity) success run
    (compileLanguageStart_denote_exact owned head arity)

/-- Conversely, an environment of the two-variable proof telescope entails
the source assumptions.  This exposes the exact non-vacuity boundary. -/
theorem environment_satisfies_assumptions
    (property : CompileLanguageControl → Prop)
    (environment : (assumptionState property).context.Environment) :
    HOL.Soundness.SatisfiesHyps (CallGuardModel property)
      (emptyValuation _) assumptions := by
  intro formula member
  rcases List.mem_cons.mp member with equal | member
  · subst formula
    exact environment.1.2.down.down
  · rcases List.mem_cons.mp member with equal | impossible
    · subst formula
      exact environment.2.down.down
    · nomatch impossible

/-- The altered control-state interpretation has no semantic environment for
the assumptions.  The same open proof syntax therefore cannot be promoted to
a closed valid theorem in that model. -/
theorem altered_assumption_context_empty :
    ¬ Nonempty (assumptionState runningPredicate).context.Environment := by
  rintro ⟨environment⟩
  exact altered_interpretation_not_satisfying
    (environment_satisfies_assumptions runningPredicate environment)

/-! ## Audit -/

#print axioms callGuardModel_fullDomains
#print axioms hypotheses_denote
#print axioms preservation_denotes
#print axioms preservation_compiles_and_denotes
#print axioms assumptionEnvironment
#print axioms compiled_conclusion_true
#print axioms run_preserved_by_compiled_proof
#print axioms halts_with_specification_from_compiled_proof
#print axioms altered_assumption_context_empty

end CallGuardSemantics
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
