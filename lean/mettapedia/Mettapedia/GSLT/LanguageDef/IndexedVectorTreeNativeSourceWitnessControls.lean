import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeWitnessControls
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseGuardReadback
import Mettapedia.Logic.HOL.PredicateProductsInterpretation

/-!
# A nonempty source environment with the actual stored family

The payload and recursive carriers remain distinct. The constructor functions
are the installed programs, and the family is their actual least family.
The supplied handlers realize the particular motive `e ↦ F_C(e)`; they are
not methods synthesized for arbitrary motives. The original branch guard
retains its complete Vector and All-evidence arguments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceWitnessControls

open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedVectorTreeNativeWitnessModel
open IndexedVectorTreeNativeWitnessControls
  (family motive suppliedSolvedCase suppliedBranchCase solvedFunction branchFunction
   solvedFunctionGuard branchFunctionGuard solved_function_guard_holds branch_function_guard_holds)
namespace Readback
export IndexedVectorTreeSourceCaseGuardReadback
  (solvedCaseGuardFor branchCaseGuardFor rawSolvedCaseGuard rawBranchCaseGuard)
end Readback
namespace Install
export IndexedVectorTreeConstructorInstallation
  (rawImages solvedGuardFor branchGuardFor rawSolvedGuard rawBranchGuard rawRealizes)
end Install
namespace Source
export IndexedVectorTreeNativeSourceReading (ambient ambientContext)
end Source

noncomputable section

def answer := input.predicate originalPredicate

private def familyMotive (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop)) :
    ClosedTerm Native.Const (Native.E ⇒ Native.W ⇒ .prop) :=
  .lam (.lam (.app (weaken (weaken predicate)) (.var (.vs .vz))))

private theorem familyMotive_meaning (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop))
    (element : Space) (evidence : Space) :
    model.denote (familyMotive predicate) values element evidence = model.denote predicate values element := by
  change model.denote (weaken (weaken predicate))
    (model.extend (σ := Native.W) (model.extend (σ := Native.E) values element) evidence) element = _
  rw [Soundness.denote_weaken,Soundness.denote_weaken]

private theorem solvedCase_from_constructor
    (answer predicate : ClosedTerm Native.Const (Native.E ⇒ .prop))
    (constructor : ClosedTerm Native.Const (Native.E ⇒ Native.E))
    (handler : ClosedTerm Native.Const (Native.E ⇒ Native.W))
    (constructorPresent :
      (model.denote (.app (Install.solvedGuardFor answer predicate) constructor) values).down) :
    (model.denote (.app (Readback.solvedCaseGuardFor answer (familyMotive predicate) constructor) handler) values).down := by
  apply (PredicateProducts.pi_denote model answer _ handler values).mpr
  intro element admitted present
  have result := (PredicateProducts.pi_denote model answer (weaken predicate) constructor values).mp
    constructorPresent element admitted present
  rw [Soundness.denote_weaken] at result
  change (model.denote (weaken (familyMotive predicate)) (model.extend values element)
    (model.denote (weaken constructor) (model.extend values element) element)
    (model.denote handler values element)).down
  rw [Soundness.denote_weaken,Soundness.denote_weaken,familyMotive_meaning]
  exact result

private theorem branchCase_from_constructor
    (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop))
    (constructor : ClosedTerm Native.Const (Native.N ⇒ Native.V ⇒ Native.E))
    (handler : ClosedTerm Native.Const (Native.N ⇒ Native.V ⇒ Native.W ⇒ Native.W))
    (constructorPresent : (model.denote (.app (Install.branchGuardFor predicate) constructor) values).down) :
    (model.denote (.app (Readback.branchCaseGuardFor predicate (familyMotive predicate) constructor) handler) values).down := by
  apply (PredicateProducts.pi_denote model (PredicateProducts.full Native.N) _ handler values).mpr
  intro length admittedLength presentLength
  apply (PredicateProducts.pi_apply_denote model
    (NativeVectorAll.Reading.vectorCode Native.original Native.selection (weaken predicate) (.var .vz)) _
    (model.denote handler values length) (model.extend values length)).mpr
  intro vector admittedVector presentVector
  apply (PredicateProducts.pi_apply_denote model
    (NativeVectorAll.Reading.allCode Native.original Native.pairs Native.witness Native.selection
      (weaken (weaken predicate)) (weaken (weaken (familyMotive predicate))) (.var (.vs .vz)) (.var .vz)) _
    (model.denote handler values length vector) (model.extend (model.extend values length) vector)).mpr
  intro evidence _admittedEvidence _presentEvidence
  have atLength := (PredicateProducts.pi_denote model (PredicateProducts.full Native.N) _ constructor values).mp
    constructorPresent length admittedLength presentLength
  have result := (PredicateProducts.pi_apply_denote model
    (NativeVectorAll.Reading.vectorCode Native.original Native.selection (weaken predicate) (.var .vz))
    (weaken (weaken predicate)) (model.denote constructor values length) (model.extend values length)).mp
    atLength vector admittedVector presentVector
  rw [Soundness.denote_weaken,Soundness.denote_weaken] at result
  change (model.denote (weaken (weaken (weaken (familyMotive predicate))))
    (model.extend (model.extend (model.extend values length) vector) evidence)
    (model.denote (weaken (weaken (weaken constructor)))
      (model.extend (model.extend (model.extend values length) vector) evidence) length vector)
    (model.denote handler values length vector evidence)).down
  rw [Soundness.denote_weaken,Soundness.denote_weaken,Soundness.denote_weaken,
    Soundness.denote_weaken,Soundness.denote_weaken,Soundness.denote_weaken,familyMotive_meaning]
  exact result

#print axioms solvedCase_from_constructor
#print axioms branchCase_from_constructor

theorem motive_meaning (element : Space) (evidence : Space) :
    model.denote motive values element evidence = model.denote family values element :=
  familyMotive_meaning family element evidence

def solvedCaseGuard := Readback.solvedCaseGuardFor answer motive solvedFunction
def branchCaseGuard := Readback.branchCaseGuardFor family motive branchFunction

theorem solved_case_guard_holds :
    (model.denote (.app solvedCaseGuard suppliedSolvedCase) values).down :=
  solvedCase_from_constructor answer family solvedFunction suppliedSolvedCase solved_function_guard_holds

theorem branch_case_guard_holds :
    (model.denote (.app branchCaseGuard suppliedBranchCase) values).down :=
  branchCase_from_constructor family branchFunction suppliedBranchCase branch_function_guard_holds

def images : Subst Native.Const Source.ambient [] :=
  Install.rawImages answer family motive solvedFunction branchFunction suppliedSolvedCase suppliedBranchCase
def sourceValues : model.Valuation Source.ambient := Soundness.substVal model images values

def solvedVariable : Var Source.ambient (Native.E ⇒ Native.E) := .vs (.vs (.vs .vz))
def branchVariable : Var Source.ambient (Native.N ⇒ Native.V ⇒ Native.E) := .vs (.vs .vz)
def solvedCaseVariable : Var Source.ambient (Native.E ⇒ Native.W) := .vs .vz
def branchCaseVariable : Var Source.ambient (Native.N ⇒ Native.V ⇒ Native.W ⇒ Native.W) := .vz

def mappedGuard {type : Ty Native.Base} (index : Var Source.ambient type) : ClosedFormula Native.Const :=
  HOL.subst images (Source.ambientContext.telescope.guard index)

theorem mapped_solved_guard_holds : (model.denote (mappedGuard solvedVariable) values).down := by
  have comparison : mappedGuard solvedVariable = .app (Install.solvedGuardFor answer family) solvedFunction :=
    Install.rawSolvedGuard answer family motive solvedFunction branchFunction suppliedSolvedCase suppliedBranchCase
  exact Eq.mpr (congrArg (fun formula : ClosedFormula Native.Const => (model.denote formula values).down) comparison) solved_function_guard_holds
theorem mapped_branch_guard_holds : (model.denote (mappedGuard branchVariable) values).down := by
  have comparison : mappedGuard branchVariable = .app (Install.branchGuardFor family) branchFunction :=
    Install.rawBranchGuard answer family motive solvedFunction branchFunction suppliedSolvedCase suppliedBranchCase
  exact Eq.mpr (congrArg (fun formula : ClosedFormula Native.Const => (model.denote formula values).down) comparison) branch_function_guard_holds
theorem mapped_solved_case_guard_holds : (model.denote (mappedGuard solvedCaseVariable) values).down := by
  have comparison : mappedGuard solvedCaseVariable = .app solvedCaseGuard suppliedSolvedCase :=
    Readback.rawSolvedCaseGuard answer family motive solvedFunction branchFunction suppliedSolvedCase suppliedBranchCase
  exact Eq.mpr (congrArg (fun formula : ClosedFormula Native.Const => (model.denote formula values).down) comparison) solved_case_guard_holds
theorem mapped_branch_case_guard_holds : (model.denote (mappedGuard branchCaseVariable) values).down := by
  have comparison : mappedGuard branchCaseVariable = .app branchCaseGuard suppliedBranchCase :=
    Readback.rawBranchCaseGuard answer family motive solvedFunction branchFunction suppliedSolvedCase suppliedBranchCase
  exact Eq.mpr (congrArg (fun formula : ClosedFormula Native.Const => (model.denote formula values).down) comparison) branch_case_guard_holds

def hypotheses : List (ClosedFormula Native.Const) :=
  [mappedGuard solvedVariable,mappedGuard branchVariable,
   mappedGuard solvedCaseVariable,mappedGuard branchCaseVariable]

theorem hypotheses_realizable : Soundness.SatisfiesHyps model values hypotheses := by
  intro formula present
  simp only [hypotheses,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact mapped_solved_guard_holds
  · exact mapped_branch_guard_holds
  · exact mapped_solved_case_guard_holds
  · exact mapped_branch_case_guard_holds

def realizer : Source.ambientContext.telescope.Realizes images hypotheses :=
  Install.rawRealizes answer family motive solvedFunction branchFunction suppliedSolvedCase suppliedBranchCase
    (.hyp ⟨0,by simp [hypotheses]⟩) (.hyp ⟨1,by simp [hypotheses]⟩)
    (.hyp ⟨2,by simp [hypotheses]⟩) (.hyp ⟨3,by simp [hypotheses]⟩)

theorem original_source_environment_satisfies : Source.ambientContext.telescope.Satisfies model sourceValues :=
  PredicateContexts.Telescope.Realizes.satisfies_subst model (model.functionsRespectEqv_of_fullDomains full)
    realizer values (fun _ => trivial) hypotheses_realizable

theorem original_payload_and_recursive_types_distinct : Native.N ≠ Native.E := original_payload_type_distinct

#print axioms solved_case_guard_holds
#print axioms branch_case_guard_holds
#print axioms mapped_solved_case_guard_holds
#print axioms mapped_branch_case_guard_holds
#print axioms original_source_environment_satisfies

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceWitnessControls
