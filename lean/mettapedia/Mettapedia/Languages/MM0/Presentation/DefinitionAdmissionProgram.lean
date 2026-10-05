import Mettapedia.Languages.MM0.Presentation.DeclarationCorrespondence
import Mettapedia.Languages.MM0.Presentation.FreeVariablesCorrespondence

/-!
# Authored MM0 definition-body admission

The program checks dummy sorts, infers the body at its declared result sort,
and computes its residual free variables. Every residual variable must occur
in the declared return dependencies. No body is published by these equations.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalConversion ComputationalProof ComputationalDeclaration
open ComputationalFreeVariables
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def bodyBase : Program := declarationProgram ++ (naturalDifferenceEquations ++ freeVariablesEquations)

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def bodyEquations : Program := [
  ⟨"dummy-context", "mm0:dummy-context", [v "sorts"], c "mm0:dummy-context-view" [c "nik:list-view" [v "sorts"]]⟩,
  ⟨"dummy-context-empty", "mm0:dummy-context-view", [.sym "List:Nil"], .list []⟩,
  ⟨"dummy-context-cons", "mm0:dummy-context-view", [c "List:Cons" [v "sort", v "rest"]],
    c "nik:list-cons" [.list [.sym "MM0:Bound", v "sort"], c "mm0:dummy-context" [v "rest"]]⟩,
  ⟨"body-free-missing", "mm0:body-free", [.sym "None", v "deps"], .sym "False"⟩,
  ⟨"body-free-present", "mm0:body-free", [c "Some" [v "free"], v "deps"],
    c "mm0:body-free-view" [c "nik:list-view" [c "nik:nat-difference" [v "free", v "deps"]]]⟩,
  ⟨"body-free-contained", "mm0:body-free-view", [.sym "List:Nil"], .sym "True"⟩,
  ⟨"body-free-escaping", "mm0:body-free-view", [c "List:Cons" [v "first", v "rest"]], .sym "False"⟩,
  ⟨"form-body", "mm0:form-body", [v "sorts", v "table",
    .list [.sym "MM0:TermDecl", v "context", v "sort", v "deps"],
    .list [.sym "MM0:Definition", v "dummies", v "expression"]],
    c "mm0:body-dummies" [c "mm0:form-dummies" [v "sorts", v "dummies"],
      v "table", v "context", v "sort", v "deps", v "dummies", v "expression"]⟩,
  ⟨"body-dummies-refuse", "mm0:body-dummies",
    [.sym "False", v "table", v "context", v "sort", v "deps", v "dummies", v "expression"], .sym "False"⟩,
  ⟨"body-dummies-allow", "mm0:body-dummies",
    [.sym "True", v "table", v "context", v "sort", v "deps", v "dummies", v "expression"],
    c "mm0:body-context" [v "table", c "nik:list-append" [v "context", c "mm0:dummy-context" [v "dummies"]],
      v "sort", v "deps", v "expression"]⟩,
  ⟨"body-context", "mm0:body-context", [v "table", v "context", v "sort", v "deps", v "expression"],
    c "mm0:body-typed" [c "nik:data-eq" [c "mm0:infer" [v "table", v "context", v "expression"],
      c "MM0:Inferred" [.list [], v "sort"]], v "table", v "context", v "deps", v "expression"]⟩,
  ⟨"body-untyped", "mm0:body-typed", [.sym "False", v "table", v "context", v "deps", v "expression"], .sym "False"⟩,
  ⟨"body-typed", "mm0:body-typed", [.sym "True", v "table", v "context", v "deps", v "expression"],
    c "mm0:body-free" [c "mm0:free-variables" [v "table", v "context", v "expression"], v "deps"]⟩]

def bodyProgram : Program := bodyBase ++ bodyEquations

theorem free_addition_disjoint :
    ∀ equation ∈ naturalDifferenceEquations ++ freeVariablesEquations,
      equation.head ∉ declarationProgram.calledHeads := by
  simp only [declarationProgram, proofProgram, conversionProgram, unfoldingProgram,
    ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
  decide

theorem bodyEquations_disjoint :
    ∀ equation ∈ bodyEquations, equation.head ∉ bodyBase.calledHeads := by
  simp only [bodyBase, declarationProgram, proofProgram, conversionProgram, unfoldingProgram,
    ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
  decide

theorem bodyProgram_leftLinear : LeftLinear bodyProgram := by
  simp only [bodyProgram, bodyBase, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨⟨declarationProgram_leftLinear, ?_, ?_⟩, ?_⟩
  · intro equation member
    exact naturalDifferenceProgram_leftLinear equation (List.mem_append_right _ member)
  · intro equation member
    exact freeVariablesProgram_leftLinear equation (List.mem_append_right _ member)
  · simp [bodyEquations, c, v, patternVarsList, patternVars]

theorem bodyProgram_dataSeparated : DataSeparated bodyProgram dataEqualityHost where
  undefined := by
    intro head member
    have original := declarationProgram_dataSeparated.undefined head member
    simp only [bodyProgram, bodyBase, Program.defines, List.any_append]
    change ((declarationProgram.defines head || (naturalDifferenceEquations.defines head ||
      freeVariablesEquations.defines head)) || bodyEquations.defines head) = false
    rw [original]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := declarationProgram_dataSeparated.unhandled

theorem body_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term}
    (used : head ∈ bodyEquations.map Equation.head)
    (defined : bodyEquations.definesAt head arguments.length = true)
    (selected : bodyEquations.select head arguments = some (equation, environment))
    (body : Evaluates bodyProgram dataEqualityHost environment equation.body result) :
    Applies bodyProgram dataEqualityHost head arguments result :=
  Applies.suffix_equation bodyEquations_disjoint used defined selected body

theorem body_apply (head : String) (used : head ∈ bodyEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply bodyProgram dataEqualityHost fuel head arguments =
      applyWith bodyEquations dataEqualityHost (eval bodyProgram dataEqualityHost fuel) head arguments :=
  apply_suffix_eq bodyBase bodyEquations dataEqualityHost bodyEquations_disjoint head used fuel arguments

theorem declaration_reused (head : String) (used : head ∈ declarationProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies declarationProgram dataEqualityHost head arguments result) :
    Applies bodyProgram dataEqualityHost head arguments result := by
  have base := (Applies.append_iff declarationProgram (naturalDifferenceEquations ++ freeVariablesEquations)
    dataEqualityHost free_addition_disjoint head used arguments result).mpr computed
  exact (Applies.append_iff bodyBase bodyEquations dataEqualityHost bodyEquations_disjoint
    head (by
      simp only [bodyBase, Program.calledHeads, List.flatMap_append, List.mem_append]
      exact Or.inl used) arguments result).mpr base

theorem free_reused (head : String) (used : head ∈ freeVariablesProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies freeVariablesProgram computationalHost head arguments result) :
    Applies bodyProgram dataEqualityHost head arguments result := by
  let inserted := ComputationalAdmissible.admissibleEquations ++
    substitutionProgram ++ ComputationalInstantiation.instantiationEquations ++
    ComputationalFreshDummies.freshEquations ++ naturalLookupProgram ++ unfoldingEquations ++
    conversionEquations ++ proofEquations ++ declarationEquations
  have hosts : computationalHost.AgreesOn dataEqualityHost freeVariablesProgram.calledHeads :=
    dataEqualityHost_computational_agrees _ (by decide) (by decide)
  have original := (Applies.host_iff freeVariablesProgram hosts head used arguments result).mp computed
  have sourceUsed : head ∈ (argumentProgram ++ (naturalDifferenceEquations ++ freeVariablesEquations)).calledHeads := by
    simpa only [freeVariablesProgram, freeVariablesBase, List.append_assoc] using used
  have run := (Applies.insert_iff argumentProgram (naturalDifferenceEquations ++ freeVariablesEquations)
    inserted dataEqualityHost (by
      simp only [inserted, ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies,
        encodeNaturals, Finset.sort_empty]
      decide) head sourceUsed arguments result).mpr (by
        simpa only [freeVariablesProgram, freeVariablesBase, List.append_assoc] using original)
  have base : Applies bodyBase dataEqualityHost head arguments result := by
    simpa only [bodyBase, declarationProgram, proofProgram, conversionProgram, unfoldingProgram,
      ComputationalInstantiation.instantiationProgram, ComputationalAdmissible.admissibleProgram,
      inserted, List.append_assoc] using run
  have included : head ∈ bodyBase.calledHeads := by
    simp only [freeVariablesProgram, freeVariablesBase, Program.calledHeads, List.flatMap_append,
      List.mem_append] at used
    simp only [bodyBase, declarationProgram, proofProgram, conversionProgram, unfoldingProgram,
      ComputationalInstantiation.instantiationProgram, ComputationalAdmissible.admissibleProgram,
      Program.calledHeads, List.flatMap_append, List.mem_append]
    rcases used with (used | used) | used
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl used))))))
    · exact Or.inr (Or.inl used)
    · exact Or.inr (Or.inr used)
  exact (Applies.append_iff bodyBase bodyEquations dataEqualityHost bodyEquations_disjoint
    head included arguments result).mpr base

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission
