import Mettapedia.Languages.MM0.Presentation.DeclarationData

/-!
# Authored MM0 declaration profile checks

Sort flags constrain bound variables, term results, statements and dummies
separately. Context traversal checks each binder against the preceding scope.
These checks validate payloads; they never publish a theorem or definition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration

open Kernel ComputationalContext ComputationalProof
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def declarationEquations : Program := [
  ⟨"form-not-true", "mm0:form-not", [.sym "True"], .sym "False"⟩,
  ⟨"form-not-false", "mm0:form-not", [.sym "False"], .sym "True"⟩,
  ⟨"form-and-true", "mm0:form-and", [.sym "True", v "right"], v "right"⟩,
  ⟨"form-and-false", "mm0:form-and", [.sym "False", v "right"], .sym "False"⟩,
  ⟨"form-bound-index", "mm0:form-bound-index", [v "context", v "index"],
    c "mm0:form-bound-item" [c "mm0:data-at" [v "context", v "index"]]⟩,
  ⟨"form-bound-missing", "mm0:form-bound-item", [.sym "None"], .sym "False"⟩,
  ⟨"form-bound-present", "mm0:form-bound-item", [c "Some" [.list [.sym "MM0:Bound", v "sort"]]], .sym "True"⟩,
  ⟨"form-bound-regular", "mm0:form-bound-item", [c "Some" [.list [.sym "MM0:Regular", v "sort", v "deps"]]], .sym "False"⟩,
  ⟨"form-bound-indices", "mm0:form-bound-indices", [v "context", v "indices"],
    c "mm0:form-bound-view" [c "nik:list-view" [v "indices"], v "context"]⟩,
  ⟨"form-bound-empty", "mm0:form-bound-view", [.sym "List:Nil", v "context"], .sym "True"⟩,
  ⟨"form-bound-cons", "mm0:form-bound-view", [c "List:Cons" [v "index", v "indices"], v "context"],
    c "mm0:form-bound-next" [c "mm0:form-bound-index" [v "context", v "index"], v "context", v "indices"]⟩,
  ⟨"form-bound-stop", "mm0:form-bound-next", [.sym "False", v "context", v "indices"], .sym "False"⟩,
  ⟨"form-bound-next", "mm0:form-bound-next", [.sym "True", v "context", v "indices"],
    c "mm0:form-bound-indices" [v "context", v "indices"]⟩,
  ⟨"form-sort", "mm0:form-sort", [v "sorts", v "sort", v "use"],
    c "mm0:form-sort-info" [c "nik:nat-table-get" [v "sorts", v "sort"], v "use"]⟩,
  ⟨"form-sort-missing", "mm0:form-sort-info", [.sym "None", v "use"], .sym "False"⟩,
  ⟨"form-sort-bound", "mm0:form-sort-info",
    [c "Some" [.list [.sym "MM0:Sort", v "pure", v "strict", v "provable", v "free"]], .sym "Bound"],
    c "mm0:form-not" [v "strict"]⟩,
  ⟨"form-sort-regular", "mm0:form-sort-info",
    [c "Some" [.list [.sym "MM0:Sort", v "pure", v "strict", v "provable", v "free"]], .sym "Regular"], .sym "True"⟩,
  ⟨"form-sort-result", "mm0:form-sort-info",
    [c "Some" [.list [.sym "MM0:Sort", v "pure", v "strict", v "provable", v "free"]], .sym "Result"],
    c "mm0:form-not" [v "pure"]⟩,
  ⟨"form-sort-statement", "mm0:form-sort-info",
    [c "Some" [.list [.sym "MM0:Sort", v "pure", v "strict", v "provable", v "free"]], .sym "Statement"], v "provable"⟩,
  ⟨"form-sort-dummy", "mm0:form-sort-info",
    [c "Some" [.list [.sym "MM0:Sort", v "pure", v "strict", v "provable", v "free"]], .sym "Dummy"],
    c "mm0:form-and" [c "mm0:form-not" [v "strict"], c "mm0:form-not" [v "free"]]⟩,
  ⟨"form-binder-bound", "mm0:form-binder", [v "sorts", v "context", .list [.sym "MM0:Bound", v "sort"]],
    c "mm0:form-sort" [v "sorts", v "sort", .sym "Bound"]⟩,
  ⟨"form-binder-regular", "mm0:form-binder", [v "sorts", v "context", .list [.sym "MM0:Regular", v "sort", v "deps"]],
    c "mm0:form-binder-deps" [c "mm0:form-sort" [v "sorts", v "sort", .sym "Regular"], v "context", v "deps"]⟩,
  ⟨"form-binder-unknown", "mm0:form-binder-deps", [.sym "False", v "context", v "deps"], .sym "False"⟩,
  ⟨"form-binder-deps", "mm0:form-binder-deps", [.sym "True", v "context", v "deps"],
    c "mm0:form-bound-indices" [v "context", v "deps"]⟩,
  ⟨"form-context-from", "mm0:form-context-from", [v "sorts", v "initial", v "remaining"],
    c "mm0:form-context-view" [c "nik:list-view" [v "remaining"], v "sorts", v "initial"]⟩,
  ⟨"form-context-empty", "mm0:form-context-view", [.sym "List:Nil", v "sorts", v "initial"], .sym "True"⟩,
  ⟨"form-context-cons", "mm0:form-context-view", [c "List:Cons" [v "binder", v "remaining"], v "sorts", v "initial"],
    c "mm0:form-context-next" [c "mm0:form-binder" [v "sorts", v "initial", v "binder"],
      v "sorts", v "initial", v "binder", v "remaining"]⟩,
  ⟨"form-context-stop", "mm0:form-context-next", [.sym "False", v "sorts", v "initial", v "binder", v "remaining"], .sym "False"⟩,
  ⟨"form-context-next", "mm0:form-context-next", [.sym "True", v "sorts", v "initial", v "binder", v "remaining"],
    c "mm0:form-context-from" [v "sorts", c "nik:list-append" [v "initial", .list [v "binder"]], v "remaining"]⟩,
  ⟨"form-context", "mm0:form-context", [v "sorts", v "context"],
    c "mm0:form-context-from" [v "sorts", .list [], v "context"]⟩,
  ⟨"form-term", "mm0:form-term", [v "sorts", .list [.sym "MM0:TermDecl", v "context", v "sort", v "deps"]],
    c "mm0:form-term-context" [c "mm0:form-context" [v "sorts", v "context"], v "sorts", v "context", v "sort", v "deps"]⟩,
  ⟨"form-term-context-stop", "mm0:form-term-context", [.sym "False", v "sorts", v "context", v "sort", v "deps"], .sym "False"⟩,
  ⟨"form-term-context", "mm0:form-term-context", [.sym "True", v "sorts", v "context", v "sort", v "deps"],
    c "mm0:form-term-result" [c "mm0:form-sort" [v "sorts", v "sort", .sym "Result"], v "context", v "deps"]⟩,
  ⟨"form-term-result-stop", "mm0:form-term-result", [.sym "False", v "context", v "deps"], .sym "False"⟩,
  ⟨"form-term-result", "mm0:form-term-result", [.sym "True", v "context", v "deps"],
    c "mm0:form-bound-indices" [v "context", v "deps"]⟩,
  ⟨"form-dummies", "mm0:form-dummies", [v "sorts", v "dummies"],
    c "mm0:form-dummies-view" [c "nik:list-view" [v "dummies"], v "sorts"]⟩,
  ⟨"form-dummies-empty", "mm0:form-dummies-view", [.sym "List:Nil", v "sorts"], .sym "True"⟩,
  ⟨"form-dummies-cons", "mm0:form-dummies-view", [c "List:Cons" [v "sort", v "rest"], v "sorts"],
    c "mm0:form-dummies-next" [c "mm0:form-sort" [v "sorts", v "sort", .sym "Dummy"], v "sorts", v "rest"]⟩,
  ⟨"form-dummies-stop", "mm0:form-dummies-next", [.sym "False", v "sorts", v "rest"], .sym "False"⟩,
  ⟨"form-dummies-next", "mm0:form-dummies-next", [.sym "True", v "sorts", v "rest"], c "mm0:form-dummies" [v "sorts", v "rest"]⟩,
  ⟨"form-statement", "mm0:form-statement", [v "sorts", v "table", v "context", v "expression"],
    c "mm0:form-statement-type" [c "mm0:infer" [v "table", v "context", v "expression"], v "sorts"]⟩,
  ⟨"form-statement-untyped", "mm0:form-statement-type", [.sym "None", v "sorts"], .sym "False"⟩,
  ⟨"form-statement-typed", "mm0:form-statement-type", [c "MM0:Inferred" [v "remaining", v "sort"], v "sorts"],
    c "mm0:form-statement-saturated" [c "nik:list-view" [v "remaining"], v "sorts", v "sort"]⟩,
  ⟨"form-statement-saturated", "mm0:form-statement-saturated", [.sym "List:Nil", v "sorts", v "sort"],
    c "mm0:form-sort" [v "sorts", v "sort", .sym "Statement"]⟩,
  ⟨"form-statement-unsaturated", "mm0:form-statement-saturated", [c "List:Cons" [v "binder", v "remaining"], v "sorts", v "sort"], .sym "False"⟩,
  ⟨"form-statements", "mm0:form-statements", [v "sorts", v "table", v "context", v "expressions"],
    c "mm0:form-statements-view" [c "nik:list-view" [v "expressions"], v "sorts", v "table", v "context"]⟩,
  ⟨"form-statements-empty", "mm0:form-statements-view", [.sym "List:Nil", v "sorts", v "table", v "context"], .sym "True"⟩,
  ⟨"form-statements-cons", "mm0:form-statements-view", [c "List:Cons" [v "expression", v "rest"], v "sorts", v "table", v "context"],
    c "mm0:form-statements-next" [c "mm0:form-statement" [v "sorts", v "table", v "context", v "expression"],
      v "sorts", v "table", v "context", v "rest"]⟩,
  ⟨"form-statements-stop", "mm0:form-statements-next", [.sym "False", v "sorts", v "table", v "context", v "rest"], .sym "False"⟩,
  ⟨"form-statements-next", "mm0:form-statements-next", [.sym "True", v "sorts", v "table", v "context", v "rest"],
    c "mm0:form-statements" [v "sorts", v "table", v "context", v "rest"]⟩,
  ⟨"form-theorem", "mm0:form-theorem", [v "sorts", v "table", .list [.sym "MM0:Theorem", v "context", v "hypotheses", v "conclusion"]],
    c "mm0:form-theorem-context" [c "mm0:form-context" [v "sorts", v "context"], v "sorts", v "table", v "context", v "hypotheses", v "conclusion"]⟩,
  ⟨"form-theorem-context-stop", "mm0:form-theorem-context", [.sym "False", v "sorts", v "table", v "context", v "hypotheses", v "conclusion"], .sym "False"⟩,
  ⟨"form-theorem-context", "mm0:form-theorem-context", [.sym "True", v "sorts", v "table", v "context", v "hypotheses", v "conclusion"],
    c "mm0:form-and" [c "mm0:form-statements" [v "sorts", v "table", v "context", v "hypotheses"],
      c "mm0:form-statement" [v "sorts", v "table", v "context", v "conclusion"]]⟩]

def declarationProgram : Program := proofProgram ++ declarationEquations

set_option maxRecDepth 2048 in
theorem declarationEquations_disjoint :
    ∀ equation ∈ declarationEquations, equation.head ∉ proofProgram.calledHeads := by
  simp only [proofProgram, ComputationalConversion.conversionProgram,
    ComputationalDefinitions.unfoldingProgram, ComputationalFreshDummies.freshEquations,
    encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
  decide

theorem declarationProgram_leftLinear : LeftLinear declarationProgram := by
  simp only [declarationProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨proofProgram_leftLinear, ?_⟩
  simp [declarationEquations, c, v, patternVarsList, patternVars]

theorem declarationProgram_dataSeparated : DataSeparated declarationProgram dataEqualityHost where
  undefined := by
    intro head member
    have prior := proofProgram_dataSeparated.undefined head member
    simp only [declarationProgram, Program.defines, List.any_append]
    change (proofProgram.defines head || declarationEquations.defines head) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := proofProgram_dataSeparated.unhandled

theorem declaration_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term}
    (used : head ∈ declarationEquations.map Equation.head)
    (defined : declarationEquations.definesAt head arguments.length = true)
    (selected : declarationEquations.select head arguments = some (equation, environment))
    (body : Evaluates declarationProgram dataEqualityHost environment equation.body result) :
    Applies declarationProgram dataEqualityHost head arguments result :=
  Applies.suffix_equation declarationEquations_disjoint used defined selected body

theorem declaration_apply (head : String) (used : head ∈ declarationEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply declarationProgram dataEqualityHost fuel head arguments =
      applyWith declarationEquations dataEqualityHost (eval declarationProgram dataEqualityHost fuel) head arguments :=
  apply_suffix_eq proofProgram declarationEquations dataEqualityHost declarationEquations_disjoint head used fuel arguments

theorem proof_reused (head : String) (used : head ∈ proofProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies proofProgram dataEqualityHost head arguments result) :
    Applies declarationProgram dataEqualityHost head arguments result :=
  (Applies.append_iff proofProgram declarationEquations dataEqualityHost declarationEquations_disjoint
    head used arguments result).mpr computed

end Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration
