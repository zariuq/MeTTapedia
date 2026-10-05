import Mettapedia.Languages.MM0.Presentation.AdmissionData

/-!
# Authored sequential MM0 admission

All checks read the preceding theory. Only a successful authorization reaches
the storage update. The public initial entry takes commands and constructs the
empty theory itself; it does not accept a caller-supplied theorem store.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmission

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalConversion ComputationalProof ComputationalDeclaration
open ComputationalDefinitionAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name
private def both (left right : Term) : Term := c "mm0:form-and" [left, right]
private def state : Term := .list [.sym "MM0:Theory", v "sorts", v "terms", v "definitions", v "theorems"]
private def fresh (table : String) : Term := c "mm0:admission-fresh" [v table, v "index"]
private def consEntry (value table : String) : Term :=
  c "nik:list-cons" [.list [v "index", v value], v table]

def admissionEquations : Program := [
  ⟨"admission-fresh", "mm0:admission-fresh", [v "table", v "index"],
    c "mm0:admission-missing" [c "nik:nat-table-get" [v "table", v "index"]]⟩,
  ⟨"admission-missing", "mm0:admission-missing", [.sym "None"], .sym "True"⟩,
  ⟨"admission-occupied", "mm0:admission-missing", [c "Some" [v "entry"]], .sym "False"⟩,
  ⟨"admission-check-sort", "mm0:admission-check", [state, .list [.sym "MM0:AdmitSort", v "index", v "info"]], fresh "sorts"⟩,
  ⟨"admission-check-term", "mm0:admission-check", [state, .list [.sym "MM0:AdmitTerm", v "index", v "declaration"]],
    both (fresh "terms") (c "mm0:form-term" [v "sorts", v "declaration"])⟩,
  ⟨"admission-check-definition", "mm0:admission-check",
    [state, .list [.sym "MM0:AdmitDefinition", v "index", v "declaration", v "body"]],
    both (both (both (fresh "terms") (fresh "definitions"))
      (c "mm0:form-term" [v "sorts", v "declaration"]))
      (c "mm0:form-body" [v "sorts", v "terms", v "declaration", v "body"])⟩,
  ⟨"admission-check-axiom", "mm0:admission-check", [state, .list [.sym "MM0:AdmitAxiom", v "index", v "declaration"]],
    both (fresh "theorems") (c "mm0:form-theorem" [v "sorts", v "terms", v "declaration"])⟩,
  ⟨"admission-check-theorem", "mm0:admission-check",
    [state, .list [.sym "MM0:AdmitTheorem", v "index", v "declaration", v "dummies", v "proof"]],
    both (both (both (fresh "theorems") (c "mm0:form-theorem" [v "sorts", v "terms", v "declaration"]))
      (c "mm0:form-dummies" [v "sorts", v "dummies"]))
      (c "mm0:admission-proof" [v "terms", v "definitions", v "theorems", v "declaration", v "dummies", v "proof"])⟩,
  ⟨"admission-proof", "mm0:admission-proof", [v "terms", v "definitions", v "theorems",
    .list [.sym "MM0:Theorem", v "context", v "hypotheses", v "conclusion"], v "dummies", v "proof"],
    c "mm0:check-proof" [v "terms", v "definitions", v "theorems",
      c "nik:list-append" [v "context", c "mm0:dummy-context" [v "dummies"]],
      v "hypotheses", v "proof", v "conclusion"]⟩,
  ⟨"admission-step", "mm0:admission-step", [v "theory", v "admission"],
    c "mm0:admission-checked" [c "mm0:admission-check" [v "theory", v "admission"], v "theory", v "admission"]⟩,
  ⟨"admission-refuse", "mm0:admission-checked", [.sym "False", v "theory", v "admission"], .sym "None"⟩,
  ⟨"admission-accept", "mm0:admission-checked", [.sym "True", v "theory", v "admission"],
    c "mm0:admission-publish" [v "theory", v "admission"]⟩,
  ⟨"admission-publish-sort", "mm0:admission-publish", [state, .list [.sym "MM0:AdmitSort", v "index", v "info"]],
    c "Some" [.list [.sym "MM0:Theory", consEntry "info" "sorts", v "terms", v "definitions", v "theorems"]]⟩,
  ⟨"admission-publish-term", "mm0:admission-publish", [state, .list [.sym "MM0:AdmitTerm", v "index", v "declaration"]],
    c "Some" [.list [.sym "MM0:Theory", v "sorts", consEntry "declaration" "terms", v "definitions", v "theorems"]]⟩,
  ⟨"admission-publish-definition", "mm0:admission-publish",
    [state, .list [.sym "MM0:AdmitDefinition", v "index", v "declaration", v "body"]],
    c "Some" [.list [.sym "MM0:Theory", v "sorts", consEntry "declaration" "terms", consEntry "body" "definitions", v "theorems"]]⟩,
  ⟨"admission-publish-axiom", "mm0:admission-publish", [state, .list [.sym "MM0:AdmitAxiom", v "index", v "declaration"]],
    c "Some" [.list [.sym "MM0:Theory", v "sorts", v "terms", v "definitions", consEntry "declaration" "theorems"]]⟩,
  ⟨"admission-publish-theorem", "mm0:admission-publish",
    [state, .list [.sym "MM0:AdmitTheorem", v "index", v "declaration", v "dummies", v "proof"]],
    c "Some" [.list [.sym "MM0:Theory", v "sorts", v "terms", v "definitions", consEntry "declaration" "theorems"]]⟩,
  ⟨"admission-run", "mm0:admission-run", [v "theory", v "admissions"],
    c "mm0:admission-run-view" [c "nik:list-view" [v "admissions"], v "theory"]⟩,
  ⟨"admission-run-empty", "mm0:admission-run-view", [.sym "List:Nil", v "theory"], c "Some" [v "theory"]⟩,
  ⟨"admission-run-cons", "mm0:admission-run-view", [c "List:Cons" [v "admission", v "rest"], v "theory"],
    c "mm0:admission-run-next" [c "mm0:admission-step" [v "theory", v "admission"], v "rest"]⟩,
  ⟨"admission-run-stop", "mm0:admission-run-next", [.sym "None", v "rest"], .sym "None"⟩,
  ⟨"admission-run-next", "mm0:admission-run-next", [c "Some" [v "theory"], v "rest"],
    c "mm0:admission-run" [v "theory", v "rest"]⟩,
  ⟨"admission-start", "mm0:admission-start", [v "admissions"],
    c "mm0:admission-run" [.list [.sym "MM0:Theory", .list [], .list [], .list [], .list []], v "admissions"]⟩]

def admissionProgram : Program := bodyProgram ++ admissionEquations

theorem admissionEquations_disjoint :
    ∀ equation ∈ admissionEquations, equation.head ∉ bodyProgram.calledHeads := by
  simp only [bodyProgram, bodyBase, declarationProgram, proofProgram, conversionProgram, unfoldingProgram,
    ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
  decide

theorem admissionProgram_leftLinear : LeftLinear admissionProgram := by
  simp only [admissionProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨bodyProgram_leftLinear, ?_⟩
  simp [admissionEquations, c, v, state, patternVarsList, patternVars]

theorem admissionProgram_dataSeparated : DataSeparated admissionProgram dataEqualityHost where
  undefined := by
    intro head member
    have original := bodyProgram_dataSeparated.undefined head member
    simp only [admissionProgram, Program.defines, List.any_append]
    change (bodyProgram.defines head || admissionEquations.defines head) = false
    rw [original]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := bodyProgram_dataSeparated.unhandled

theorem admission_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term}
    (used : head ∈ admissionEquations.map Equation.head)
    (defined : admissionEquations.definesAt head arguments.length = true)
    (selected : admissionEquations.select head arguments = some (equation, environment))
    (body : Evaluates admissionProgram dataEqualityHost environment equation.body result) :
    Applies admissionProgram dataEqualityHost head arguments result :=
  Applies.suffix_equation admissionEquations_disjoint used defined selected body

theorem admission_apply (head : String) (used : head ∈ admissionEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply admissionProgram dataEqualityHost fuel head arguments =
      applyWith admissionEquations dataEqualityHost (eval admissionProgram dataEqualityHost fuel) head arguments :=
  apply_suffix_eq bodyProgram admissionEquations dataEqualityHost admissionEquations_disjoint head used fuel arguments

theorem body_reused (head : String) (used : head ∈ bodyProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies bodyProgram dataEqualityHost head arguments result) :
    Applies admissionProgram dataEqualityHost head arguments result :=
  (Applies.append_iff bodyProgram admissionEquations dataEqualityHost admissionEquations_disjoint
    head used arguments result).mpr computed

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
