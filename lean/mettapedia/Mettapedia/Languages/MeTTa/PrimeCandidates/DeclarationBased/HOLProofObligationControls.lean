import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLProofObligations
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeGenericProofCompilerCallGuardSemantics
import Mettapedia.Logic.HOL.BoundedLogicalSearch
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.BoundedHOLProofPlanning

/-!
# Actual scoped proof-reconstruction controls

An authored refinement introduces a predicate, a value, and two equal proof
hypotheses. Its remaining premise is solved by the actual bounded search.
Reconstruction compiles that exact answer. An alternative supplied assumption
occurrence yields a different retained tree and native projection. Missing
premises cannot compile. A separate constant-free signature exhibits a true
goal with a backward route requiring a countermodel-refuted premise.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLProofObligationControls

open Mettapedia.Logic HOL
open ProofSearch ProofObligations
open Presentation FormationSensitiveHOLInterface HOLNativeGenericProofCompiler
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open FormationSensitiveHOLGenericProofInstances.CallGuard

private instance (type : Ty Unit) : DecidableEq (Constant type) := fun first second => by
  cases first <;> cases second
  all_goals first | exact .isTrue rfl | exact .isFalse (by intro same; cases same)

private abbrev signature := FormationSensitiveHOLInvariant.signature
private abbrev operations := Operations.logicalOnly signature proofName proofName_fresh
private abbrev predicateType : Ty Unit := stateType ⇒ .prop
private abbrev context : Ctx Unit := [stateType, predicateType]

def atom : Formula Constant context := .app (.var (.vs .vz)) (.var .vz)

def valueBody : Formula Constant context := .imp atom (.imp atom atom)

def predicateBody : Formula Constant [predicateType] := .all valueBody

def query : ClosedFormula Constant := .all predicateBody

def goal : HOLAdapter.Goal Unit Constant := ⟨[], [], query⟩

def leaf : HOLAdapter.Goal Unit Constant := ⟨context, [atom, atom], atom⟩

def route : Refinement HOLAdapter.Solution goal :=
  (((ProofObligations.HOL.allI (hypotheses := []) predicateBody).comp
      (fun _ => ProofObligations.HOL.allI (hypotheses := []) valueBody)).comp
      (fun _ => ProofObligations.HOL.impI (hypotheses := []) atom (.imp atom atom))).comp
      (fun _ => ProofObligations.HOL.impI (hypotheses := [atom]) atom atom)

def searched : HOL.BoundedLogicalSearch.Result leaf.hypotheses leaf.conclusion :=
  HOL.BoundedLogicalSearch.search HOL.BoundedLogicalSearch.contextCandidates 1
    leaf.hypotheses leaf.conclusion

theorem searched_succeeds : searched.answer.isSome = true := by decide +kernel

def found := searched.answer.get searched_succeeds

def olderProof : ProofSyntax Constant [atom, atom] atom := .hyp (Δ := [atom, atom]) 1

theorem searched_uses_newer : found.proof.rootObservation = ⟨.hyp, some 0⟩ := by
  decide +kernel

def candidate : ∀ index, Option (HOLAdapter.Solution (route.query index)) :=
  fun _ => some found.proof

def older : ∀ index, Option (HOLAdapter.Solution (route.query index)) :=
  fun _ => some olderProof

def rebuilt : HOLAdapter.Solution goal := .allI (.allI (.impI (.impI found.proof)))

def rebuiltOlder : HOLAdapter.Solution goal := .allI (.allI (.impI (.impI olderProof)))

theorem reconstructs_actual_search : route.tryRebuild candidate = some rebuilt := by
  apply (Refinement.tryRebuild_eq_some_iff _ _ _).2
  exact ⟨fun _ => found.proof, fun _ => rfl, rfl⟩

theorem reconstructs_older : route.tryRebuild older = some rebuiltOlder := by
  apply (Refinement.tryRebuild_eq_some_iff _ _ _).2
  exact ⟨fun _ => olderProof, fun _ => rfl, rfl⟩

def native : Tower.Tm 0 := .lam (.lam (.lam (.lam (.var 0))))

def nativeOlder : Tower.Tm 0 := .lam (.lam (.lam (.lam (.var 1))))

set_option maxRecDepth 10000 in
theorem actual_compiles : ProofObligations.HOL.compile? route candidate
    signature proofName operations Fin.elim0 Fin.elim0 = some native := by decide +kernel

set_option maxRecDepth 10000 in
theorem older_compiles : ProofObligations.HOL.compile? route older
    signature proofName operations Fin.elim0 Fin.elim0 = some nativeOlder := by decide +kernel

theorem compiled_occurrences_distinct : native ≠ nativeOlder := by
  intro same
  cases same

theorem retained_occurrences_distinct : rebuilt ≠ rebuiltOlder := by
  intro same
  have actual : compile signature proofName operations rebuilt Fin.elim0 Fin.elim0 =
      some native := by
    simpa only [ProofObligations.HOL.compile?, reconstructs_actual_search,
      Option.bind_some] using actual_compiles
  have alternative : compile signature proofName operations rebuiltOlder Fin.elim0 Fin.elim0 =
      some nativeOlder := by
    simpa only [ProofObligations.HOL.compile?, reconstructs_older,
      Option.bind_some] using older_compiles
  rw [same, alternative] at actual
  exact compiled_occurrences_distinct (Option.some.inj actual.symm)

private theorem objectsTyped : GenericTyping.Objects signature (gamma := []) .nil Fin.elim0 := by
  intro index; nomatch index

private theorem hypothesesTyped : GenericTyping.Hypotheses signature operations
    (gamma := []) (delta := []) .nil Fin.elim0 Fin.elim0 := by
  intro index; nomatch index

theorem native_typed :
    ∃ code, represent signature query = some code ∧
      FormationSensitive.Typing operations.target .nil native
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  simpa only [goal, TelescopeAbstraction.subst_empty,
    TelescopeAbstraction.liftClosed_zero] using
    ProofObligations.HOL.compiled_typed route candidate signature proofName operations
      objectsTyped hypothesesTyped actual_compiles

theorem native_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property) native query := by
  apply ProofObligations.HOL.compiled_denotes route candidate signature proofName operations
    (CallGuardSemantics.semantics property) actual_compiles (CallGuardSemantics.emptyState property)
  intro index; nomatch index

theorem nativeOlder_typed :
    ∃ code, represent signature query = some code ∧
      FormationSensitive.Typing operations.target .nil nativeOlder
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  simpa only [goal, TelescopeAbstraction.subst_empty,
    TelescopeAbstraction.liftClosed_zero] using
    ProofObligations.HOL.compiled_typed route older signature proofName operations
      objectsTyped hypothesesTyped older_compiles

/-- The erased compiled function executes to the selected supplied proof.
This relation has no head-equality oracle and imposes no typing on its inputs;
typed instantiation remains governed by the existing telescope-checking laws. -/
theorem returns_newer {n : Nat} (predicate value older newer : Tower.Tm n) :
    TelescopeAbstraction.BetaSteps
      (.app (.app (.app (.app (liftClosed native) predicate) value) older) newer) newer := by
  change TelescopeAbstraction.BetaSteps
    (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.var 0))))) predicate) value) older) newer) newer
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single
    (StepCore.congAppFun (StepCore.congAppFun (StepCore.congAppFun
      (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
        (.lam (.lam (.lam (.var 0)))) predicate)))))
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single
    (StepCore.congAppFun (StepCore.congAppFun
      (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
        (.lam (.lam (.var 0))) value))))
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single
    (StepCore.congAppFun
      (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
        (.lam (.var 0)) older)))
  exact Relation.ReflTransGen.single
    (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False) (.var 0) newer)

theorem returns_older {n : Nat} (predicate value older newer : Tower.Tm n) :
    TelescopeAbstraction.BetaSteps
      (.app (.app (.app (.app (liftClosed nativeOlder) predicate) value) older) newer) older := by
  change TelescopeAbstraction.BetaSteps
    (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.var 1))))) predicate) value) older) newer) older
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single
    (StepCore.congAppFun (StepCore.congAppFun (StepCore.congAppFun
      (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
        (.lam (.lam (.lam (.var 1)))) predicate)))))
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single
    (StepCore.congAppFun (StepCore.congAppFun
      (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
        (.lam (.lam (.var 1))) value))))
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single
    (StepCore.congAppFun
      (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
        (.lam (.var 1)) older)))
  apply Relation.ReflTransGen.single
  have captured : inst0 older (.lam (.var 1) : Tower.Tm (n + 1)) =
      .lam (rename wk older) := rfl
  rw [captured]
  simpa only [inst0_rename_wk] using
    (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
      (rename wk older) newer)

private abbrev leafPlans := fun index : route.Premise =>
  BoundedHOLProofPlanning.plan HOL.BoundedLogicalSearch.contextCandidates 1 (route.query index)

theorem searched_answer : searched.answer = some found := (Option.some_get searched_succeeds).symm

def premiseRuns : ∀ index, System.Run (leafPlans index) (.solved found.proof) :=
  fun _ => {
    final := .finished searched
    trace := .cons .execute (.nil _)
    observed := by
      change some (BoundedHOLProofPlanning.outcome searched) = some (.solved found.proof)
      simp only [BoundedHOLProofPlanning.outcome, searched_answer]
  }

def reconstructionReceipt : (route.reconstructionStage leafPlans).Evidence () rebuilt :=
  ⟨fun _ => found.proof, premiseRuns, ⟨rfl⟩⟩

/-- The two metrics have different meanings: actual provider events, and
the actual returned source-tree size. Neither is a C runtime measurement. -/
def receiptCost : Stage.Cost (route.reconstructionStage leafPlans) (Nat × Nat) :=
  route.reconstructionCost leafPlans
    (fun index => BoundedHOLProofPlanning.cost HOL.BoundedLogicalSearch.contextCandidates
      1 (route.query index) (fun _ => (1, 0)))
    (fun answers => (0, (route.rebuild answers).nodeCount))

theorem actual_receipt_cost : receiptCost.charge reconstructionReceipt = (2, 5) := by
  decide +kernel

theorem missing_not_compiled : ProofObligations.HOL.compile? route (fun _ => none)
    signature proofName operations (n := 0) Fin.elim0 Fin.elim0 = none := by
  apply ProofObligations.HOL.missing_not_compiled
  exact ⟨⟨⟨⟨⟨0⟩, ⟨0⟩⟩, ⟨0⟩⟩, ⟨0⟩⟩, rfl⟩

/-- Two premises are still two occurrences when their queried formula agrees. -/
def duplicateRoute : Refinement HOLAdapter.Solution
    (⟨[], [], .and (.imp (.bot : ClosedFormula Constant) .bot) (.imp .bot .bot)⟩ :
      HOLAdapter.Goal Unit Constant) :=
  ProofObligations.HOL.andI (.imp .bot .bot) (.imp .bot .bot)

def duplicateProof : ClosedFormula Constant := .imp .bot .bot

def duplicated : HOLAdapter.Solution
    (⟨[], [], .and duplicateProof duplicateProof⟩ : HOLAdapter.Goal Unit Constant) :=
  .andI (.impI (.hyp 0)) (.impI (.hyp 0))

def duplicateCandidate (missing : Bool) :
    ∀ index, Option (HOLAdapter.Solution (duplicateRoute.query index)) :=
  fun index => Fin.cases (motive := fun occurrence : Fin 2 =>
      Option (HOLAdapter.Solution (duplicateRoute.query ⟨occurrence⟩)))
    (if missing then none else some (.impI (.hyp 0) : ProofSyntax Constant [] duplicateProof))
    (fun _ => if missing then some (.impI (.hyp 0) : ProofSyntax Constant [] duplicateProof)
      else none) index.down

theorem either_premise_missing (missing : Bool) :
    duplicateRoute.tryRebuild (duplicateCandidate missing) = none := by
  cases missing <;> decide +kernel

theorem duplicate_goal_inhabited : Nonempty (HOLAdapter.Solution
    (⟨[], [], .and duplicateProof duplicateProof⟩ : HOLAdapter.Goal Unit Constant)) := ⟨duplicated⟩

namespace CountermodelRoute

open HOL.TypeSubstitutionExample

def goal : HOLAdapter.Goal Bool (NoConstants Bool) := ⟨[], [], .imp .bot .bot⟩

def proof : HOLAdapter.Solution goal := .impI (.hyp 0)

def route : Refinement HOLAdapter.Solution goal :=
  ProofObligations.HOL.impE sourceClaim goal.conclusion

/-- The actual separating model excludes the minor premise, even though
the original goal has an actual retained proof. -/
theorem route_has_no_complete_answers : ¬ Nonempty (∀ index,
    HOLAdapter.Solution (route.query index)) := by
  rintro ⟨answers⟩
  exact sourceClaim_not_provable (answers ⟨1⟩).erase

theorem goal_still_provable : Nonempty (HOLAdapter.Solution goal) := ⟨proof⟩

def alternatives : List (Refinement HOLAdapter.Solution goal) :=
  [route, Refinement.discharged proof]

def chosen : Refinement.Choice alternatives where
  occurrence := ⟨1, by decide⟩
  answers index := Fin.elim0 index.down

/-- Selecting a proved route owes no answers to the incompatible alternative. -/
theorem chooses_one_route : chosen.proof = proof := rfl

end CountermodelRoute

#print axioms reconstructs_actual_search
#print axioms native_typed
#print axioms native_denotes
#print axioms returns_newer
#print axioms returns_older
#print axioms retained_occurrences_distinct
#print axioms either_premise_missing
#print axioms actual_receipt_cost
#print axioms CountermodelRoute.route_has_no_complete_answers

end HOLProofObligationControls
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
