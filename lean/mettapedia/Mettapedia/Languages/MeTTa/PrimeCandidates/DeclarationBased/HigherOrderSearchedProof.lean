import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.BoundedHOLProofPlanning
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeGenericProofCompilerCallGuardSemantics
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.Telescopes

/-!
# A searched higher-order theorem, compiled and interpreted natively

The query quantifies a predicate, a function, and a value. Search specializes
a universal hypothesis and applies it to an actual proof of the premise.
Neither the proof tree nor the conclusion is supplied as an assumption.

The existing logical signature and its full-domain semantic instance are
used as hosts. The theorem mentions none of the call-guard constants or its
operational invariant. The exact searched tree supplies both native typing
and denotation. A smaller depth or an empty instantiation inventory fails
without refuting this same theorem.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HigherOrderSearchedProof

open Mettapedia.Logic HOL HOL.BoundedLogicalSearch
open Presentation FormationSensitiveHOLInterface HOLNativeGenericProofCompiler
open ProofSearch
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open FormationSensitiveHOLGenericProofInstances.CallGuard

private instance (type : Ty Unit) : DecidableEq (Constant type) := fun first second => by
  cases first <;> cases second
  all_goals first | exact .isTrue rfl | exact .isFalse (by intro same; cases same)

/-- forall P f x, (forall z, P z -> P (f z)) -> P x -> P (f x). -/
def query : ClosedFormula Constant :=
  .all (σ := stateType ⇒ .prop)
    (.all (σ := stateType ⇒ stateType)
      (.all (σ := stateType)
        (.imp
          (.all (σ := stateType)
            (.imp (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))
              (.app (.var (.vs (.vs (.vs .vz))))
                (.app (.var (.vs (.vs .vz))) (.var .vz)))))
          (.imp (.app (.var (.vs (.vs .vz))) (.var .vz))
            (.app (.var (.vs (.vs .vz))) (.app (.var (.vs .vz)) (.var .vz)))))))

def goal : HOLAdapter.Goal Unit Constant := ⟨[], [], query⟩

def searched : Result goal.hypotheses goal.conclusion :=
  search contextCandidates 8 goal.hypotheses goal.conclusion

/-- Try scoped endofunction applications before the context variables. -/
def applicationFirstCandidates : Candidates Constant := fun context type =>
  (contextCandidates context (type ⇒ type)).flatMap (fun function =>
    (contextCandidates context type).map (fun argument => Term.app function argument)) ++
      contextCandidates context type

def detoured : Result goal.hypotheses goal.conclusion :=
  search applicationFirstCandidates 8 goal.hypotheses goal.conclusion

set_option maxRecDepth 10000 in
theorem search_succeeds : searched.answer.isSome = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem detoured_search_succeeds : detoured.answer.isSome = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem detoured_search_costs_more : searched.events.length < detoured.events.length := by
  decide +kernel

/-- The actual tree is obtained from the executable result, not choice. -/
def found : Found goal.hypotheses goal.conclusion := searched.answer.get search_succeeds

theorem tree_emitted : searched.answer = some found := (Option.some_get search_succeeds).symm

def compilation : Option (Tower.Tm 0) :=
  HOLAdapter.compileOutcome? FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    (BoundedHOLProofPlanning.outcome searched) Fin.elim0 Fin.elim0

def detouredCompilation : Option (Tower.Tm 0) :=
  HOLAdapter.compileOutcome? FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    (BoundedHOLProofPlanning.outcome detoured) Fin.elim0 Fin.elim0

set_option maxRecDepth 10000 in
theorem compilation_succeeds : compilation.isSome = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem detoured_compilation_succeeds : detouredCompilation.isSome = true := by decide +kernel

def native : Tower.Tm 0 := compilation.get compilation_succeeds

theorem native_emitted : compilation = some native := (Option.some_get compilation_succeeds).symm

/-- The searched theorem is a native inhabitant of its represented family. -/
theorem native_typed :
    ∃ code, represent FormationSensitiveHOLInvariant.signature query = some code ∧
      Presentation.FormationSensitive.Typing
        FormationSensitiveHOLGenericProofInstances.CallGuard.rules .nil native
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  have objectTyped : GenericTyping.Objects FormationSensitiveHOLInvariant.signature
      (gamma := []) .nil Fin.elim0 := by intro index; nomatch index
  have hypothesisTyped : GenericTyping.Hypotheses FormationSensitiveHOLInvariant.signature
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      (gamma := []) (delta := []) .nil Fin.elim0 Fin.elim0 := by intro index; nomatch index
  simpa only [goal, TelescopeAbstraction.subst_empty,
    TelescopeAbstraction.liftClosed_zero, Operations.logicalOnly,
    FormationSensitiveHOLGenericProofInstances.CallGuard.rules] using BoundedHOLProofPlanning.compiled_typed
    FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    contextCandidates 8 goal objectTyped hypothesisTyped native_emitted

/-- The same compiled term denotes the query in the actual dependent-family model. -/
theorem native_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property) native query := by
  apply BoundedHOLProofPlanning.compiled_denotes FormationSensitiveHOLInvariant.signature
    proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    (CallGuardSemantics.semantics property) contextCandidates 8 goal native_emitted
    (CallGuardSemantics.emptyState property)
  intro index
  nomatch index

/-- A proof consumer composes with the actual searched tree. -/
def relayProof : ProofSyntax Constant [] query := .impE (.impI (.hyp 0)) found.proof

def relayed : Tower.Tm 0 := .app (.lam (.var 0)) native

set_option maxRecDepth 10000 in
/-- The single compiler produces the application, not a replacement proof. -/
theorem relay_compiles :
    compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      relayProof Fin.elim0 Fin.elim0 = some relayed := by
  obtain ⟨code, represented, _typed⟩ := native_typed
  have actual : compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      found.proof Fin.elim0 Fin.elim0 = some native := by
    simpa only [compilation, HOLAdapter.compileOutcome?,
      BoundedHOLProofPlanning.outcome, tree_emitted] using native_emitted
  have consumer : compile FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      (.impI (.hyp 0) : ProofSyntax Constant [] (.imp query query))
      (n := 0) Fin.elim0 Fin.elim0 = some (.lam (.var 0)) := by
    change (represent FormationSensitiveHOLInvariant.signature query).bind
      (fun _ => some (.lam (.var 0) : Tower.Tm 0)) = some (.lam (.var 0) : Tower.Tm 0)
    rw [represented]
    rfl
  change (compile FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    (.impI (.hyp 0) : ProofSyntax Constant [] (.imp query query)) Fin.elim0 Fin.elim0).bind
      (fun function => (compile FormationSensitiveHOLInvariant.signature proofName
        (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
        found.proof Fin.elim0 Fin.elim0).bind (fun argument => some (.app function argument))) =
          some relayed
  rw [consumer, actual]
  rfl

theorem relay_typed :
    ∃ code, represent FormationSensitiveHOLInvariant.signature query = some code ∧
      Presentation.FormationSensitive.Typing
        FormationSensitiveHOLGenericProofInstances.CallGuard.rules .nil relayed
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  simpa only [Operations.logicalOnly,
    FormationSensitiveHOLGenericProofInstances.CallGuard.rules] using
    GenericTyping.compile_closed FormationSensitiveHOLInvariant.signature proofName
      (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
      relayProof relay_compiles

theorem relay_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property) relayed query := by
  apply GenericSemantics.compile_denotes FormationSensitiveHOLInvariant.signature proofName
    (Operations.logicalOnly FormationSensitiveHOLInvariant.signature proofName proofName_fresh)
    (CallGuardSemantics.semantics property) relayProof relay_compiles
    (CallGuardSemantics.emptyState property)
  intro index
  nomatch index

/-- Execution returns the exact searched inhabitant, without head equality. -/
theorem relay_returns : TelescopeAbstraction.BetaSteps relayed native := by
  apply Relation.ReflTransGen.single
  simpa only [relayed, inst0, Presentation.subst, subst0, Fin.cases_zero] using
    (StepCore.betaPi (root := (RootComputation.empty : RootComputation Tower.Head))
      (headEq := fun _ _ => False) (.var 0) native)

set_option maxRecDepth 10000 in
theorem insufficient_depth_not_refutation :
    (search contextCandidates 5 goal.hypotheses goal.conclusion).answer = none := by decide +kernel

set_option maxRecDepth 10000 in
theorem missing_instantiations_not_refutation :
    (search (fun _ _ => []) 8 goal.hypotheses goal.conclusion).answer = none := by decide +kernel

/-- Every attempted event belongs to the plan's actual search execution. -/
theorem event_cost :
    (BoundedHOLProofPlanning.cost contextCandidates 8 goal (fun _ => (1 : Nat))).total
      (BoundedHOLProofPlanning.run contextCandidates 8 goal).trace =
        searched.events.length := by
  rw [BoundedHOLProofPlanning.run_cost]
  exact searched.unit_cost

#print axioms search_succeeds
#print axioms detoured_search_succeeds
#print axioms detoured_search_costs_more
#print axioms compilation_succeeds
#print axioms detoured_compilation_succeeds
#print axioms native_typed
#print axioms native_denotes
#print axioms relay_compiles
#print axioms relay_typed
#print axioms relay_denotes
#print axioms relay_returns
#print axioms insufficient_depth_not_refutation
#print axioms missing_instantiations_not_refutation
#print axioms event_cost

end HigherOrderSearchedProof
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
