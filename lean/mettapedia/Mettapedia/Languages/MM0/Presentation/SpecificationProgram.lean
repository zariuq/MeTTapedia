import Mettapedia.Languages.MM0.Presentation.SpecificationData

/-!
# Authored MM0 specification alignment

Only matching public declarations consume the expected specification. Local
definitions and proved theorems still pass the same admission checks. The
public verifier starts with an empty theory and accepts only after consuming
the whole specification.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSpecification

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalConversion ComputationalProof ComputationalDeclaration
open ComputationalDefinitionAdmission ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name
private def sameKey : Term := c "nik:data-eq"
  [.list [v "index", v "payload"], .list [v "actual", v "stored"]]
private def state : Term := .list [.sym "MM0:SpecificationState", v "theory", v "pending"]

def specificationEquations : Program := [
  ⟨"spec-match-sort", "mm0:spec-match",
    [.list [.sym "MM0:SpecSort", v "index", v "payload"],
      .list [.sym "MM0:AdmitSort", v "actual", v "stored"]], sameKey⟩,
  ⟨"spec-match-term", "mm0:spec-match",
    [.list [.sym "MM0:SpecTerm", v "index", v "payload"],
      .list [.sym "MM0:AdmitTerm", v "actual", v "stored"]], sameKey⟩,
  ⟨"spec-match-definition", "mm0:spec-match",
    [.list [.sym "MM0:SpecDefinition", v "index", v "payload", v "expected"],
      .list [.sym "MM0:AdmitDefinition", v "actual", v "stored", v "body"]],
    c "mm0:form-and" [sameKey, c "mm0:spec-body" [v "expected", v "body"]]⟩,
  ⟨"spec-match-axiom", "mm0:spec-match",
    [.list [.sym "MM0:SpecAxiom", v "index", v "payload"],
      .list [.sym "MM0:AdmitAxiom", v "actual", v "stored"]], sameKey⟩,
  ⟨"spec-match-theorem", "mm0:spec-match",
    [.list [.sym "MM0:SpecTheorem", v "index", v "payload"],
      .list [.sym "MM0:AdmitTheorem", v "actual", v "stored", v "dummies", v "proof"]], sameKey⟩,
  ⟨"spec-match-kind-refuse", "mm0:spec-match", [v "entry", v "admission"], .sym "False"⟩,
  ⟨"spec-body-omitted", "mm0:spec-body", [.sym "None", v "body"], .sym "True"⟩,
  ⟨"spec-body-supplied", "mm0:spec-body", [c "Some" [v "expected"], v "body"],
    c "nik:data-eq" [v "expected", v "body"]⟩,
  ⟨"spec-aux-definition", "mm0:spec-auxiliary",
    [.list [.sym "MM0:AdmitDefinition", v "index", v "payload", v "body"]], .sym "True"⟩,
  ⟨"spec-aux-theorem", "mm0:spec-auxiliary",
    [.list [.sym "MM0:AdmitTheorem", v "index", v "payload", v "dummies", v "proof"]], .sym "True"⟩,
  ⟨"spec-aux-refuse", "mm0:spec-auxiliary", [v "admission"], .sym "False"⟩,
  ⟨"spec-pending-local", "mm0:spec-pending", [.sym "True", v "pending", v "admission"],
    c "mm0:spec-guard" [c "mm0:spec-auxiliary" [v "admission"], v "pending"]⟩,
  ⟨"spec-pending-public", "mm0:spec-pending", [.sym "False", v "pending", v "admission"],
    c "mm0:spec-public" [c "nik:list-view" [v "pending"], v "admission"]⟩,
  ⟨"spec-guard-refuse", "mm0:spec-guard", [.sym "False", v "pending"], .sym "None"⟩,
  ⟨"spec-guard-accept", "mm0:spec-guard", [.sym "True", v "pending"], c "Some" [v "pending"]⟩,
  ⟨"spec-public-extra", "mm0:spec-public", [.sym "List:Nil", v "admission"], .sym "None"⟩,
  ⟨"spec-public-match", "mm0:spec-public", [c "List:Cons" [v "entry", v "pending"], v "admission"],
    c "mm0:spec-guard" [c "mm0:spec-match" [v "entry", v "admission"], v "pending"]⟩,
  ⟨"spec-step", "mm0:spec-step", [state,
      .list [.sym "MM0:ProofDeclaration", v "local", v "admission"]],
    c "mm0:spec-permitted" [c "mm0:spec-pending" [v "local", v "pending", v "admission"],
      v "theory", v "admission"]⟩,
  ⟨"spec-step-forbidden", "mm0:spec-permitted", [.sym "None", v "theory", v "admission"], .sym "None"⟩,
  ⟨"spec-step-permitted", "mm0:spec-permitted", [c "Some" [v "pending"], v "theory", v "admission"],
    c "mm0:spec-admitted" [c "mm0:admission-step" [v "theory", v "admission"], v "pending"]⟩,
  ⟨"spec-admission-refuse", "mm0:spec-admitted", [.sym "None", v "pending"], .sym "None"⟩,
  ⟨"spec-admission-accept", "mm0:spec-admitted", [c "Some" [v "theory"], v "pending"], c "Some" [state]⟩,
  ⟨"spec-run", "mm0:spec-run", [v "state", v "declarations"],
    c "mm0:spec-run-view" [c "nik:list-view" [v "declarations"], v "state"]⟩,
  ⟨"spec-run-empty", "mm0:spec-run-view", [.sym "List:Nil", v "state"], c "Some" [v "state"]⟩,
  ⟨"spec-run-cons", "mm0:spec-run-view", [c "List:Cons" [v "declaration", v "rest"], v "state"],
    c "mm0:spec-run-next" [c "mm0:spec-step" [v "state", v "declaration"], v "rest"]⟩,
  ⟨"spec-run-stop", "mm0:spec-run-next", [.sym "None", v "rest"], .sym "None"⟩,
  ⟨"spec-run-next", "mm0:spec-run-next", [c "Some" [v "state"], v "rest"],
    c "mm0:spec-run" [v "state", v "rest"]⟩,
  ⟨"spec-verify", "mm0:spec-verify", [v "specification", v "declarations"],
    c "mm0:spec-finish" [c "mm0:spec-run"
      [.list [.sym "MM0:SpecificationState",
        .list [.sym "MM0:Theory", .list [], .list [], .list [], .list []], v "specification"], v "declarations"]]⟩,
  ⟨"spec-finish-failed", "mm0:spec-finish", [.sym "None"], .sym "None"⟩,
  ⟨"spec-finish-run", "mm0:spec-finish", [c "Some" [state]],
    c "mm0:spec-finished" [c "nik:list-view" [v "pending"], v "theory"]⟩,
  ⟨"spec-finished-all", "mm0:spec-finished", [.sym "List:Nil", v "theory"], c "Some" [v "theory"]⟩,
  ⟨"spec-finished-incomplete", "mm0:spec-finished", [c "List:Cons" [v "entry", v "rest"], v "theory"], .sym "None"⟩]

def specificationProgram : Program := admissionProgram ++ specificationEquations

theorem specificationEquations_disjoint :
    ∀ equation ∈ specificationEquations, equation.head ∉ admissionProgram.calledHeads := by
  simp only [admissionProgram, bodyProgram, bodyBase, declarationProgram, proofProgram, conversionProgram,
    unfoldingProgram, ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies,
    encodeNaturals, Finset.sort_empty]
  decide

theorem specificationProgram_leftLinear : LeftLinear specificationProgram := by
  simp only [specificationProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨admissionProgram_leftLinear, ?_⟩
  simp [specificationEquations, c, v, state, patternVarsList, patternVars]

theorem specificationProgram_dataSeparated : DataSeparated specificationProgram dataEqualityHost where
  undefined := by
    intro head member
    have original := admissionProgram_dataSeparated.undefined head member
    simp only [specificationProgram, Program.defines, List.any_append]
    change (admissionProgram.defines head || specificationEquations.defines head) = false
    rw [original]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := admissionProgram_dataSeparated.unhandled

theorem specification_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term}
    (used : head ∈ specificationEquations.map Equation.head)
    (defined : specificationEquations.definesAt head arguments.length = true)
    (selected : specificationEquations.select head arguments = some (equation, environment))
    (body : Evaluates specificationProgram dataEqualityHost environment equation.body result) :
    Applies specificationProgram dataEqualityHost head arguments result :=
  Applies.suffix_equation specificationEquations_disjoint used defined selected body

theorem specification_apply (head : String) (used : head ∈ specificationEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply specificationProgram dataEqualityHost fuel head arguments =
      applyWith specificationEquations dataEqualityHost (eval specificationProgram dataEqualityHost fuel) head arguments :=
  apply_suffix_eq admissionProgram specificationEquations dataEqualityHost specificationEquations_disjoint head used fuel arguments

theorem admission_reused (head : String) (used : head ∈ admissionProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies admissionProgram dataEqualityHost head arguments result) :
    Applies specificationProgram dataEqualityHost head arguments result :=
  (Applies.append_iff admissionProgram specificationEquations dataEqualityHost specificationEquations_disjoint
    head used arguments result).mpr computed

theorem admission_suffix_reused (head : String) (used : head ∈ admissionEquations.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies admissionProgram dataEqualityHost head arguments result) :
    Applies specificationProgram dataEqualityHost head arguments result :=
  admission_reused head (by
    simp only [admissionProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr used) arguments result computed

end Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
