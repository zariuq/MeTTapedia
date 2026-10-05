import Mettapedia.Languages.MM0.Presentation.DefinitionData
import Mettapedia.Languages.MM0.Presentation.InstantiationCorrespondence
import Mettapedia.Languages.MM0.Presentation.FreshDummiesCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramInsertion

/-!
# Authored MM0 definition unfolding

The declaration and body come from their respective stores. Argument typing
and fresh-dummy checks guard simultaneous substitution of the stored body.
The only new traversal constructs bound-variable images from natural indices.
All other computation reuses existing authored equation components.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def unfoldingEquations : Program := [
  ⟨"variable-images", "mm0:variable-images", [v "images"],
    c "mm0:variable-images-view" [c "nik:list-view" [v "images"]]⟩,
  ⟨"variable-images-empty", "mm0:variable-images-view", [.sym "List:Nil"], .list []⟩,
  ⟨"variable-images-cons", "mm0:variable-images-view", [c "List:Cons" [v "first", v "rest"]],
    c "nik:list-cons" [c "MM0:Var" [v "first"], c "mm0:variable-images" [v "rest"]]⟩,
  ⟨"unfold", "mm0:unfold", [v "table", v "definitions", v "target", v "symbol", v "arguments", v "images"],
    c "mm0:unfold-declaration" [c "mm0:declaration" [v "table", v "symbol"],
      v "table", v "definitions", v "target", v "symbol", v "arguments", v "images"]⟩,
  ⟨"unfold-no-declaration", "mm0:unfold-declaration",
    [.sym "None", v "table", v "definitions", v "target", v "symbol", v "arguments", v "images"], .sym "None"⟩,
  ⟨"unfold-declaration", "mm0:unfold-declaration",
    [c "Some" [.list [.sym "MM0:TermDecl", v "formal", v "sort", v "dependencies"]],
      v "table", v "definitions", v "target", v "symbol", v "arguments", v "images"],
    c "mm0:unfold-body" [c "nik:nat-table-get" [v "definitions", v "symbol"],
      v "table", v "target", v "formal", v "arguments", v "images"]⟩,
  ⟨"unfold-no-body", "mm0:unfold-body",
    [.sym "None", v "table", v "target", v "formal", v "arguments", v "images"], .sym "None"⟩,
  ⟨"unfold-body", "mm0:unfold-body",
    [c "Some" [.list [.sym "MM0:Definition", v "dummies", v "expression"]],
      v "table", v "target", v "formal", v "arguments", v "images"],
    c "mm0:unfold-arguments" [c "mm0:check-arguments" [v "table", v "target", v "arguments", v "formal"],
      v "target", v "arguments", v "dummies", v "images", v "expression"]⟩,
  ⟨"unfold-arguments-refuse", "mm0:unfold-arguments",
    [.sym "False", v "target", v "arguments", v "dummies", v "images", v "expression"], .sym "None"⟩,
  ⟨"unfold-arguments-admit", "mm0:unfold-arguments",
    [.sym "True", v "target", v "arguments", v "dummies", v "images", v "expression"],
    c "mm0:unfold-dummies" [c "mm0:check-dummies" [v "target", v "arguments", v "dummies", v "images"],
      v "arguments", v "images", v "expression"]⟩,
  ⟨"unfold-dummies-refuse", "mm0:unfold-dummies",
    [.sym "False", v "arguments", v "images", v "expression"], .sym "None"⟩,
  ⟨"unfold-dummies-admit", "mm0:unfold-dummies",
    [.sym "True", v "arguments", v "images", v "expression"],
    c "mm0:subst" [v "expression", c "mm0:substitution-values" [c "nik:list-append"
      [v "arguments", c "mm0:variable-images" [v "images"]]]]⟩]

def unfoldingProgram : Program := ComputationalInstantiation.instantiationProgram ++
  (ComputationalFreshDummies.freshEquations ++ (naturalLookupProgram ++ unfoldingEquations))

theorem unfoldingProgram_leftLinear : LeftLinear unfoldingProgram := by
  simp only [unfoldingProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨ComputationalInstantiation.instantiationProgram_leftLinear, ?_, naturalLookupProgram_leftLinear, ?_⟩
  · intro equation member
    exact ComputationalFreshDummies.freshProgram_leftLinear equation (List.mem_append_right _ member)
  · simp [unfoldingEquations, c, v, patternVarsList, patternVars]

theorem unfoldingProgram_dataSeparated : DataSeparated unfoldingProgram computationalHost where
  undefined := by
    intro head member
    have prior := ComputationalInstantiation.instantiationProgram_dataSeparated.undefined head member
    simp only [unfoldingProgram, Program.defines, List.any_append]
    change (ComputationalInstantiation.instantiationProgram.defines head ||
      (ComputationalFreshDummies.freshEquations.defines head ||
        (naturalLookupProgram.defines head || unfoldingEquations.defines head))) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := ComputationalInstantiation.instantiationProgram_dataSeparated.unhandled

theorem instantiation_reused (head : String)
    (called : head ∈ ComputationalInstantiation.instantiationProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (run : Applies ComputationalInstantiation.instantiationProgram computationalHost head arguments result) :
    Applies unfoldingProgram computationalHost head arguments result :=
  (Applies.append_iff ComputationalInstantiation.instantiationProgram
    (ComputationalFreshDummies.freshEquations ++ (naturalLookupProgram ++ unfoldingEquations))
    computationalHost (by decide) head called _ _).mpr run

set_option maxRecDepth 2048 in
theorem fresh_reused (head : String) (called : head ∈ ComputationalFreshDummies.freshProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (run : Applies ComputationalFreshDummies.freshProgram computationalHost head arguments result) :
    Applies unfoldingProgram computationalHost head arguments result := by
  let middle := ComputationalAdmissible.admissibleEquations ++
    (substitutionProgram ++ ComputationalInstantiation.instantiationEquations)
  have inserted := (Applies.insert_iff argumentProgram ComputationalFreshDummies.freshEquations middle
    computationalHost (by
      dsimp [middle]
      simp only [ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies,
        encodeNaturals, Finset.sort_empty]
      decide) head called _ _).mpr run
  have used : head ∈ (argumentProgram ++ middle ++ ComputationalFreshDummies.freshEquations).calledHeads := by
    simp only [ComputationalFreshDummies.freshProgram, Program.calledHeads,
      List.flatMap_append, List.mem_append] at called ⊢
    rcases called with left | right
    · exact Or.inl (Or.inl left)
    · exact Or.inr right
  have enlarged := (Applies.append_iff (argumentProgram ++ middle ++ ComputationalFreshDummies.freshEquations)
    (naturalLookupProgram ++ unfoldingEquations) computationalHost
    (by
      dsimp [middle]
      simp only [ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies,
        encodeNaturals, Finset.sort_empty]
      decide) head used _ _).mpr inserted
  simpa only [unfoldingProgram, ComputationalInstantiation.instantiationProgram,
    ComputationalAdmissible.admissibleProgram, middle, List.append_assoc] using enlarged

set_option maxRecDepth 2048 in
theorem definition_lookup_reused (definitions : DefinitionTable) (symbol : Nat) :
    Applies unfoldingProgram computationalHost "nik:nat-table-get" [encodeDefinitions definitions, natural symbol]
      (encodeBodyResult (definitionsOf definitions symbol)) := by
  have run := (Applies.frame_iff naturalLookupProgram
    (ComputationalInstantiation.instantiationProgram ++ ComputationalFreshDummies.freshEquations) unfoldingEquations
    computationalHost (by decide) (by decide) "nik:nat-table-get" (by decide) _ _).mpr
      (natural_lookup_computes encodeBody definitions symbol)
  simpa only [unfoldingProgram, List.append_assoc, encodeDefinitions, encodeBodyResult, definitionsOf] using run

theorem arguments_reused (table : SignatureTable) (target : Context) (arguments : List Preterm) (formal : Context) :
    Applies unfoldingProgram computationalHost "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions arguments, encodeContext formal]
      (boolean (Substitution.checkArguments (signatureOf table) target arguments formal)) :=
  fresh_reused "mm0:check-arguments" (by decide) _ _
    (ComputationalFreshDummies.arguments_reused _ (by decide) _ _ (arguments_computes table target arguments formal))

theorem declaration_reused (table : SignatureTable) (symbol : Nat) :
    Applies unfoldingProgram computationalHost "mm0:declaration" [encodeTable table, natural symbol]
      (encodeDeclarationResult (signatureOf table symbol)) := by
  let tail := listAppendProgram ++ ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations
  have run := (Applies.append_iff typingProgram tail computationalHost (by decide)
    "mm0:declaration" (by decide) _ _).mpr (declaration_computes table symbol)
  have inArguments : Applies argumentProgram computationalHost "mm0:declaration"
      [encodeTable table, natural symbol] (encodeDeclarationResult (signatureOf table symbol)) := by
    simpa only [argumentProgram, ComputationalDependency.dependencyProgram,
      ComputationalSupport.supportProgram, tail, List.append_assoc] using run
  exact fresh_reused "mm0:declaration" (by decide) _ _
    (ComputationalFreshDummies.arguments_reused _ (by decide) _ _ inArguments)

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions
