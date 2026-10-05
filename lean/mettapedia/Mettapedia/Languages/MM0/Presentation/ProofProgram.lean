import Mettapedia.Languages.MM0.Presentation.ProofData

/-!
# Authored MM0 supplied-proof checking

The equations perform theorem lookup, dependency-safe instantiation, exact
ordered premise checking and supplied conversion checking. Failure of one
child cannot be rescued by another proof of the same conclusion. The declared
theorem store is read but never extended during checking.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalProof

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open ComputationalDefinitions ComputationalConversion
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def proofEquations : Program := [
  ⟨"substitute-list", "mm0:subst-list", [v "sources", v "values"],
    c "mm0:subst-list-view" [c "nik:list-view" [v "sources"], v "values"]⟩,
  ⟨"substitute-list-empty", "mm0:subst-list-view", [.sym "List:Nil", v "values"],
    c "MM0:Expressions" [.list []]⟩,
  ⟨"substitute-list-cons", "mm0:subst-list-view", [c "List:Cons" [v "first", v "rest"], v "values"],
    c "mm0:subst-list-head" [c "mm0:subst" [v "first", v "values"], v "rest", v "values"]⟩,
  ⟨"substitute-list-head-none", "mm0:subst-list-head", [.sym "None", v "rest", v "values"], .sym "None"⟩,
  ⟨"substitute-list-head", "mm0:subst-list-head", [c "Some" [v "first"], v "rest", v "values"],
    c "mm0:subst-list-tail" [c "mm0:subst-list" [v "rest", v "values"], v "first"]⟩,
  ⟨"substitute-list-tail-none", "mm0:subst-list-tail", [.sym "None", v "first"], .sym "None"⟩,
  ⟨"substitute-list-tail", "mm0:subst-list-tail", [c "MM0:Expressions" [v "rest"], v "first"],
    c "MM0:Expressions" [c "nik:list-cons" [v "first", v "rest"]]⟩,
  ⟨"instantiate-theorem", "mm0:instantiate-theorem", [v "table", v "context",
    .list [.sym "MM0:Theorem", v "formal", v "hypotheses", v "conclusion"], v "arguments"],
    c "mm0:theorem-admissible" [c "mm0:check-admissible" [v "table", v "formal", v "context", v "arguments"],
      v "hypotheses", v "conclusion", v "arguments"]⟩,
  ⟨"theorem-inadmissible", "mm0:theorem-admissible", [.sym "False", v "hypotheses", v "conclusion", v "arguments"], .sym "None"⟩,
  ⟨"theorem-admissible", "mm0:theorem-admissible", [.sym "True", v "hypotheses", v "conclusion", v "arguments"],
    c "mm0:theorem-prepared" [v "hypotheses", v "conclusion", c "mm0:substitution-values" [v "arguments"]]⟩,
  ⟨"theorem-prepared", "mm0:theorem-prepared", [v "hypotheses", v "conclusion", v "values"],
    c "mm0:theorem-hypotheses" [c "mm0:subst-list" [v "hypotheses", v "values"], v "conclusion", v "values"]⟩,
  ⟨"theorem-hypotheses-none", "mm0:theorem-hypotheses", [.sym "None", v "conclusion", v "values"], .sym "None"⟩,
  ⟨"theorem-hypotheses", "mm0:theorem-hypotheses", [c "MM0:Expressions" [v "hypotheses"], v "conclusion", v "values"],
    c "mm0:theorem-conclusion" [c "mm0:subst" [v "conclusion", v "values"], v "hypotheses"]⟩,
  ⟨"theorem-conclusion-none", "mm0:theorem-conclusion", [.sym "None", v "hypotheses"], .sym "None"⟩,
  ⟨"theorem-conclusion", "mm0:theorem-conclusion", [c "Some" [v "conclusion"], v "hypotheses"],
    c "MM0:Instance" [v "hypotheses", v "conclusion"]⟩,
  ⟨"proof-hypothesis", "mm0:proof", [v "table", v "definitions", v "theorems", v "context", v "hypotheses",
    .list [.sym "MM0:Hyp", v "index"]], c "mm0:data-at" [v "hypotheses", v "index"]⟩,
  ⟨"proof-theorem", "mm0:proof", [v "table", v "definitions", v "theorems", v "context", v "hypotheses",
    .list [.sym "MM0:TheoremApp", v "index", v "arguments", v "children"]],
    c "mm0:proof-declaration" [c "nik:nat-table-get" [v "theorems", v "index"], v "table", v "definitions",
      v "theorems", v "context", v "hypotheses", v "arguments", v "children"]⟩,
  ⟨"proof-conversion", "mm0:proof", [v "table", v "definitions", v "theorems", v "context", v "hypotheses",
    .list [.sym "MM0:Conversion", v "conversion", v "child"]],
    c "mm0:proof-converted" [c "mm0:conversion" [v "table", v "definitions", v "context", v "conversion"],
      v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "child"]⟩,
  ⟨"proof-no-declaration", "mm0:proof-declaration", [.sym "None", v "table", v "definitions", v "theorems",
    v "context", v "hypotheses", v "arguments", v "children"], .sym "None"⟩,
  ⟨"proof-declaration", "mm0:proof-declaration", [c "Some" [v "declaration"], v "table", v "definitions", v "theorems",
    v "context", v "hypotheses", v "arguments", v "children"],
    c "mm0:proof-instance" [c "mm0:instantiate-theorem" [v "table", v "context", v "declaration", v "arguments"],
      v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "children"]⟩,
  ⟨"proof-no-instance", "mm0:proof-instance", [.sym "None", v "table", v "definitions", v "theorems",
    v "context", v "hypotheses", v "children"], .sym "None"⟩,
  ⟨"proof-instance", "mm0:proof-instance", [c "MM0:Instance" [v "premises", v "conclusion"], v "table", v "definitions",
    v "theorems", v "context", v "hypotheses", v "children"],
    c "mm0:proof-premises" [c "mm0:proof-children" [v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "children"],
      v "premises", v "conclusion"]⟩,
  ⟨"proof-no-premises", "mm0:proof-premises", [.sym "None", v "premises", v "conclusion"], .sym "None"⟩,
  ⟨"proof-premises", "mm0:proof-premises", [c "MM0:Expressions" [v "actual"], v "premises", v "conclusion"],
    c "mm0:proof-matched" [c "nik:data-eq" [v "actual", v "premises"], v "conclusion"]⟩,
  ⟨"proof-premises-differ", "mm0:proof-matched", [.sym "False", v "conclusion"], .sym "None"⟩,
  ⟨"proof-premises-match", "mm0:proof-matched", [.sym "True", v "conclusion"], c "Some" [v "conclusion"]⟩,
  ⟨"proof-conversion-refused", "mm0:proof-converted", [.sym "None", v "table", v "definitions", v "theorems",
    v "context", v "hypotheses", v "child"], .sym "None"⟩,
  ⟨"proof-converted", "mm0:proof-converted", [c "MM0:Converted" [v "left", v "right", v "sort"],
    v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "child"],
    c "mm0:proof-left" [c "mm0:proof" [v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "child"],
      v "left", v "right"]⟩,
  ⟨"proof-left-none", "mm0:proof-left", [.sym "None", v "left", v "right"], .sym "None"⟩,
  ⟨"proof-left", "mm0:proof-left", [c "Some" [v "conclusion"], v "left", v "right"],
    c "mm0:proof-conversion-matched" [c "nik:data-eq" [v "conclusion", v "left"], v "right"]⟩,
  ⟨"proof-conversion-differ", "mm0:proof-conversion-matched", [.sym "False", v "right"], .sym "None"⟩,
  ⟨"proof-conversion-match", "mm0:proof-conversion-matched", [.sym "True", v "right"], c "Some" [v "right"]⟩,
  ⟨"proof-children", "mm0:proof-children", [v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "children"],
    c "mm0:proof-children-view" [c "nik:list-view" [v "children"], v "table", v "definitions", v "theorems", v "context", v "hypotheses"]⟩,
  ⟨"proof-children-empty", "mm0:proof-children-view", [.sym "List:Nil", v "table", v "definitions", v "theorems", v "context", v "hypotheses"],
    c "MM0:Expressions" [.list []]⟩,
  ⟨"proof-children-cons", "mm0:proof-children-view", [c "List:Cons" [v "child", v "children"], v "table", v "definitions", v "theorems", v "context", v "hypotheses"],
    c "mm0:proof-child" [c "mm0:proof" [v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "child"],
      v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "children"]⟩,
  ⟨"proof-child-none", "mm0:proof-child", [.sym "None", v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "children"], .sym "None"⟩,
  ⟨"proof-child", "mm0:proof-child", [c "Some" [v "first"], v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "children"],
    c "mm0:proof-tail" [c "mm0:proof-children" [v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "children"], v "first"]⟩,
  ⟨"proof-tail-none", "mm0:proof-tail", [.sym "None", v "first"], .sym "None"⟩,
  ⟨"proof-tail", "mm0:proof-tail", [c "MM0:Expressions" [v "rest"], v "first"],
    c "MM0:Expressions" [c "nik:list-cons" [v "first", v "rest"]]⟩,
  ⟨"check-proof", "mm0:check-proof", [v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "proof", v "claim"],
    c "nik:data-eq" [c "mm0:proof" [v "table", v "definitions", v "theorems", v "context", v "hypotheses", v "proof"],
      c "Some" [v "claim"]]⟩]

def proofProgram : Program := conversionProgram ++ proofEquations

set_option maxRecDepth 2048 in
theorem proofEquations_disjoint :
    ∀ equation ∈ proofEquations, equation.head ∉ conversionProgram.calledHeads := by
  simp only [conversionProgram, unfoldingProgram, ComputationalFreshDummies.freshEquations,
    encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
  decide

theorem proofProgram_leftLinear : LeftLinear proofProgram := by
  simp only [proofProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨conversionProgram_leftLinear, ?_⟩
  simp [proofEquations, c, v, patternVarsList, patternVars]

theorem proofProgram_dataSeparated : DataSeparated proofProgram dataEqualityHost where
  undefined := by
    intro head member
    have prior := conversionProgram_dataSeparated.undefined head member
    simp only [proofProgram, Program.defines, List.any_append]
    change (conversionProgram.defines head || proofEquations.defines head) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := conversionProgram_dataSeparated.unhandled

theorem proof_equation {head : String} {arguments : List Term} {equation : Equation} {environment : Env} {result : Term}
    (used : head ∈ proofEquations.map Equation.head)
    (defined : proofEquations.definesAt head arguments.length = true)
    (selected : proofEquations.select head arguments = some (equation, environment))
    (body : Evaluates proofProgram dataEqualityHost environment equation.body result) :
    Applies proofProgram dataEqualityHost head arguments result :=
  Applies.suffix_equation proofEquations_disjoint used defined selected body

theorem proof_apply (head : String) (used : head ∈ proofEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply proofProgram dataEqualityHost fuel head arguments =
      applyWith proofEquations dataEqualityHost (eval proofProgram dataEqualityHost fuel) head arguments :=
  apply_suffix_eq conversionProgram proofEquations dataEqualityHost proofEquations_disjoint head used fuel arguments

theorem conversion_reused (head : String) (used : head ∈ conversionProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies conversionProgram dataEqualityHost head arguments result) :
    Applies proofProgram dataEqualityHost head arguments result :=
  (Applies.append_iff conversionProgram proofEquations dataEqualityHost proofEquations_disjoint
    head used arguments result).mpr computed

theorem instantiation_reused (head : String)
    (used : head ∈ ComputationalInstantiation.instantiationProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies ComputationalInstantiation.instantiationProgram computationalHost head arguments result) :
    Applies proofProgram dataEqualityHost head arguments result := by
  have inUnfolding : head ∈ unfoldingProgram.calledHeads := by
    simp only [unfoldingProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl used
  have inConversion : head ∈ conversionProgram.calledHeads := by
    simp only [conversionProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl inUnfolding
  exact conversion_reused head inConversion _ _
    (ComputationalConversion.unfolding_reused head inUnfolding _ _
      (ComputationalDefinitions.instantiation_reused head used _ _ computed))

end Mettapedia.Languages.MM0.Presentation.ComputationalProof
