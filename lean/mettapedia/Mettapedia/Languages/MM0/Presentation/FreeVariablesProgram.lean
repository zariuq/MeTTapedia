import Mettapedia.Languages.MM0.Presentation.FreeVariablesData
import Mettapedia.Languages.MM0.Presentation.ArgumentCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalDifferenceProgram
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramInsertion

/-!
# Authored MM0 binder-sensitive free-variable computation

The equation program resolves typed bound images, removes each regular
argument's declared bindings, includes return dependencies and walks the full
application spine. Existing equations supply argument typing and occurrence
support. The host supplies only the existing list and natural primitives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeFreeLists (values : List (List Nat)) : Term := .list (values.map encodeNaturals)

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def freeVariablesEquations : Program := [
  ⟨"free-image", "mm0:free-image", [v "target", v "formal", v "arguments", v "position"],
    c "mm0:free-image-formal" [c "mm0:data-at" [v "formal", v "position"],
      v "target", v "arguments", v "position"]⟩,
  ⟨"free-image-no-formal", "mm0:free-image-formal", [.sym "None", v "target", v "arguments", v "position"], .sym "None"⟩,
  ⟨"free-image-bound-formal", "mm0:free-image-formal",
    [c "Some" [.list [.sym "MM0:Bound", v "sort"]], v "target", v "arguments", v "position"],
    c "mm0:free-image-argument" [c "mm0:data-at" [v "arguments", v "position"], v "target", v "sort"]⟩,
  ⟨"free-image-regular-formal", "mm0:free-image-formal",
    [c "Some" [.list [.sym "MM0:Regular", v "sort", v "dependencies"]], v "target", v "arguments", v "position"], .sym "None"⟩,
  ⟨"free-image-variable", "mm0:free-image-argument",
    [c "Some" [c "MM0:Var" [v "image"]], v "target", v "sort"],
    c "mm0:free-image-target" [c "mm0:data-at" [v "target", v "image"], v "sort", v "image"]⟩,
  ⟨"free-image-no-argument", "mm0:free-image-argument", [.sym "None", v "target", v "sort"], .sym "None"⟩,
  ⟨"free-image-term", "mm0:free-image-argument", [c "Some" [c "MM0:Term" [v "symbol"]], v "target", v "sort"], .sym "None"⟩,
  ⟨"free-image-app", "mm0:free-image-argument",
    [c "Some" [c "MM0:App" [v "function", v "argument"]], v "target", v "sort"], .sym "None"⟩,
  ⟨"free-image-bound-target", "mm0:free-image-target",
    [c "Some" [.list [.sym "MM0:Bound", v "actual"]], v "expected", v "image"],
    c "mm0:free-image-equal" [c "nik:nat-eq" [v "actual", v "expected"], v "image"]⟩,
  ⟨"free-image-regular-target", "mm0:free-image-target",
    [c "Some" [.list [.sym "MM0:Regular", v "sort", v "dependencies"]], v "expected", v "image"], .sym "None"⟩,
  ⟨"free-image-no-target", "mm0:free-image-target", [.sym "None", v "expected", v "image"], .sym "None"⟩,
  ⟨"free-image-equal", "mm0:free-image-equal", [.sym "True", v "image"], c "Some" [v "image"]⟩,
  ⟨"free-image-different", "mm0:free-image-equal", [.sym "False", v "image"], .sym "None"⟩,
  ⟨"free-images", "mm0:free-images", [v "target", v "formal", v "arguments", v "positions"],
    c "mm0:free-images-view" [c "nik:list-view" [v "positions"], v "target", v "formal", v "arguments"]⟩,
  ⟨"free-images-empty", "mm0:free-images-view", [.sym "List:Nil", v "target", v "formal", v "arguments"], c "Some" [.list []]⟩,
  ⟨"free-images-cons", "mm0:free-images-view",
    [c "List:Cons" [v "position", v "positions"], v "target", v "formal", v "arguments"],
    c "mm0:free-images-first" [c "mm0:free-image" [v "target", v "formal", v "arguments", v "position"],
      v "target", v "formal", v "arguments", v "positions"]⟩,
  ⟨"free-images-refuse", "mm0:free-images-first", [.sym "None", v "target", v "formal", v "arguments", v "positions"], .sym "None"⟩,
  ⟨"free-images-next", "mm0:free-images-first", [c "Some" [v "image"], v "target", v "formal", v "arguments", v "positions"],
    c "mm0:free-images-tail" [v "image", c "mm0:free-images" [v "target", v "formal", v "arguments", v "positions"]]⟩,
  ⟨"free-images-tail-refuse", "mm0:free-images-tail", [v "image", .sym "None"], .sym "None"⟩,
  ⟨"free-images-tail-cons", "mm0:free-images-tail", [v "image", c "Some" [v "images"]],
    c "Some" [c "nik:list-cons" [v "image", v "images"]]⟩,
  ⟨"free-contributions", "mm0:free-contributions", [v "target", v "full", v "arguments", v "formal", v "free-lists"],
    c "mm0:free-contributions-view" [c "nik:list-view" [v "formal"], c "nik:list-view" [v "free-lists"],
      v "target", v "full", v "arguments"]⟩,
  ⟨"free-contributions-empty", "mm0:free-contributions-view",
    [.sym "List:Nil", .sym "List:Nil", v "target", v "full", v "arguments"], c "Some" [.list []]⟩,
  ⟨"free-contributions-extra", "mm0:free-contributions-view",
    [.sym "List:Nil", c "List:Cons" [v "free", v "free-lists"], v "target", v "full", v "arguments"], .sym "None"⟩,
  ⟨"free-contributions-missing", "mm0:free-contributions-view",
    [c "List:Cons" [v "binder", v "formal"], .sym "List:Nil", v "target", v "full", v "arguments"], .sym "None"⟩,
  ⟨"free-contributions-bound", "mm0:free-contributions-view",
    [c "List:Cons" [.list [.sym "MM0:Bound", v "sort"], v "formal"], c "List:Cons" [v "free", v "free-lists"],
      v "target", v "full", v "arguments"],
    c "mm0:free-contributions" [v "target", v "full", v "arguments", v "formal", v "free-lists"]⟩,
  ⟨"free-contributions-regular", "mm0:free-contributions-view",
    [c "List:Cons" [.list [.sym "MM0:Regular", v "sort", v "dependencies"], v "formal"],
      c "List:Cons" [v "free", v "free-lists"], v "target", v "full", v "arguments"],
    c "mm0:free-contribution-bound" [c "mm0:free-images" [v "target", v "full", v "arguments", v "dependencies"],
      v "target", v "full", v "arguments", v "formal", v "free", v "free-lists"]⟩,
  ⟨"free-contribution-no-binding", "mm0:free-contribution-bound",
    [.sym "None", v "target", v "full", v "arguments", v "formal", v "free", v "free-lists"], .sym "None"⟩,
  ⟨"free-contribution-binding", "mm0:free-contribution-bound",
    [c "Some" [v "bound"], v "target", v "full", v "arguments", v "formal", v "free", v "free-lists"],
    c "mm0:free-contribution-tail" [c "nik:nat-difference" [v "free", v "bound"],
      c "mm0:free-contributions" [v "target", v "full", v "arguments", v "formal", v "free-lists"]]⟩,
  ⟨"free-contribution-no-tail", "mm0:free-contribution-tail", [v "free", .sym "None"], .sym "None"⟩,
  ⟨"free-contribution-tail", "mm0:free-contribution-tail", [v "free", c "Some" [v "rest"]],
    c "Some" [c "nik:list-append" [v "free", v "rest"]]⟩,
  ⟨"free-spine-variable", "mm0:free-spine", [v "table", v "context", c "MM0:Var" [v "index"], v "arguments", v "free-lists"],
    c "mm0:free-variable-spine" [c "nik:list-view" [v "arguments"], c "nik:list-view" [v "free-lists"], v "context", v "index"]⟩,
  ⟨"free-variable-saturated", "mm0:free-variable-spine", [.sym "List:Nil", .sym "List:Nil", v "context", v "index"],
    c "mm0:support" [v "context", c "MM0:Var" [v "index"]]⟩,
  ⟨"free-variable-extra-free", "mm0:free-variable-spine",
    [.sym "List:Nil", c "List:Cons" [v "free", v "rest"], v "context", v "index"], .sym "None"⟩,
  ⟨"free-variable-extra-argument", "mm0:free-variable-spine",
    [c "List:Cons" [v "argument", v "rest"], v "free-lists", v "context", v "index"], .sym "None"⟩,
  ⟨"free-spine-term", "mm0:free-spine", [v "table", v "context", c "MM0:Term" [v "symbol"], v "arguments", v "free-lists"],
    c "mm0:free-head" [c "mm0:declaration" [v "table", v "symbol"], v "table", v "context", v "arguments", v "free-lists"]⟩,
  ⟨"free-head-missing", "mm0:free-head", [.sym "None", v "table", v "context", v "arguments", v "free-lists"], .sym "None"⟩,
  ⟨"free-head-declared", "mm0:free-head",
    [c "Some" [.list [.sym "MM0:TermDecl", v "formal", v "sort", v "dependencies"]],
      v "table", v "context", v "arguments", v "free-lists"],
    c "mm0:free-typed" [c "mm0:check-arguments" [v "table", v "context", v "arguments", v "formal"],
      v "context", v "formal", v "arguments", v "free-lists", v "dependencies"]⟩,
  ⟨"free-typed-refuse", "mm0:free-typed", [.sym "False", v "context", v "formal", v "arguments", v "free-lists", v "dependencies"], .sym "None"⟩,
  ⟨"free-typed", "mm0:free-typed", [.sym "True", v "context", v "formal", v "arguments", v "free-lists", v "dependencies"],
    c "mm0:free-contributed" [c "mm0:free-contributions" [v "context", v "formal", v "arguments", v "formal", v "free-lists"],
      v "context", v "formal", v "arguments", v "dependencies"]⟩,
  ⟨"free-contributed-refuse", "mm0:free-contributed", [.sym "None", v "context", v "formal", v "arguments", v "dependencies"], .sym "None"⟩,
  ⟨"free-contributed", "mm0:free-contributed", [c "Some" [v "free"], v "context", v "formal", v "arguments", v "dependencies"],
    c "mm0:free-contribution-tail" [v "free", c "mm0:free-images" [v "context", v "formal", v "arguments", v "dependencies"]]⟩,
  ⟨"free-spine-application", "mm0:free-spine",
    [v "table", v "context", c "MM0:App" [v "function", v "argument"], v "arguments", v "free-lists"],
    c "mm0:free-argument" [c "mm0:free-spine" [v "table", v "context", v "argument", .list [], .list []],
      v "table", v "context", v "function", v "argument", v "arguments", v "free-lists"]⟩,
  ⟨"free-argument-refuse", "mm0:free-argument", [.sym "None", v "table", v "context", v "function", v "argument", v "arguments", v "free-lists"], .sym "None"⟩,
  ⟨"free-argument", "mm0:free-argument", [c "Some" [v "free"], v "table", v "context", v "function", v "argument", v "arguments", v "free-lists"],
    c "mm0:free-spine" [v "table", v "context", v "function", c "nik:list-cons" [v "argument", v "arguments"],
      c "nik:list-cons" [v "free", v "free-lists"]]⟩,
  ⟨"free-variables", "mm0:free-variables", [v "table", v "context", v "source"],
    c "mm0:free-spine" [v "table", v "context", v "source", .list [], .list []]⟩]

def freeVariablesBase : Program := argumentProgram ++ naturalDifferenceEquations
def freeVariablesProgram : Program := freeVariablesBase ++ freeVariablesEquations

theorem freeVariablesEquations_disjoint :
    ∀ equation ∈ freeVariablesEquations, equation.head ∉ freeVariablesBase.calledHeads := by decide

theorem freeVariablesProgram_leftLinear : LeftLinear freeVariablesProgram := by
  have difference : LeftLinear naturalDifferenceEquations := by
    simp [LeftLinear, naturalDifferenceEquations, patternVarsList, patternVars]
  have free : LeftLinear freeVariablesEquations := by
    simp [LeftLinear, freeVariablesEquations, c, v, patternVarsList, patternVars]
  simp only [freeVariablesProgram, freeVariablesBase, LeftLinear, List.mem_append, or_imp, forall_and]
  exact ⟨⟨argumentProgram_leftLinear, difference⟩, free⟩

theorem freeVariablesProgram_dataSeparated : DataSeparated freeVariablesProgram computationalHost where
  undefined := by
    intro head member
    have original := argumentProgram_dataSeparated.undefined head member
    simp only [freeVariablesProgram, freeVariablesBase, Program.defines, List.any_append]
    change ((argumentProgram.defines head || naturalDifferenceEquations.defines head) || freeVariablesEquations.defines head) = false
    rw [original]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := argumentProgram_dataSeparated.unhandled

theorem free_equation {head : String} {arguments : List Term} {equation : Equation} {environment : Env} {result : Term}
    (used : head ∈ freeVariablesEquations.map Equation.head)
    (defined : freeVariablesEquations.definesAt head arguments.length = true)
    (selected : freeVariablesEquations.select head arguments = some (equation, environment))
    (body : Evaluates freeVariablesProgram computationalHost environment equation.body result) :
    Applies freeVariablesProgram computationalHost head arguments result :=
  Applies.suffix_equation freeVariablesEquations_disjoint used defined selected body

theorem free_apply (head : String) (used : head ∈ freeVariablesEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply freeVariablesProgram computationalHost fuel head arguments =
      applyWith freeVariablesEquations computationalHost (eval freeVariablesProgram computationalHost fuel) head arguments :=
  apply_suffix_eq freeVariablesBase freeVariablesEquations computationalHost freeVariablesEquations_disjoint head used fuel arguments

theorem arguments_reused (head : String) (used : head ∈ argumentProgram.calledHeads)
    (arguments : List Term) (result : Term) (computed : Applies argumentProgram computationalHost head arguments result) :
    Applies freeVariablesProgram computationalHost head arguments result := by
  exact (Applies.append_iff argumentProgram (naturalDifferenceEquations ++ freeVariablesEquations)
    computationalHost (by decide) head used _ _).mpr computed

theorem typing_reused (head : String) (used : head ∈ typingProgram.calledHeads)
    (arguments : List Term) (result : Term) (computed : Applies typingProgram computationalHost head arguments result) :
    Applies freeVariablesProgram computationalHost head arguments result := by
  let tail := listAppendProgram ++ ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations
  have run := (Applies.append_iff typingProgram tail computationalHost (by decide) head used _ _).mpr computed
  apply arguments_reused head (by
    simp only [argumentProgram, ComputationalDependency.dependencyProgram, ComputationalSupport.supportProgram,
      Program.calledHeads, List.flatMap_append, List.mem_append] at used ⊢
    exact Or.inl (Or.inl (Or.inl used)))
  simpa only [argumentProgram, ComputationalDependency.dependencyProgram, ComputationalSupport.supportProgram,
    tail, List.append_assoc] using run

theorem support_reused (context : Context) (expression : Preterm) :
    Applies freeVariablesProgram computationalHost "mm0:support" [encodeContext context, encode expression]
      (ComputationalSupport.encodeResult (ComputationalSupport.indices? context expression)) := by
  apply arguments_reused "mm0:support" (by decide)
  exact (Applies.append_iff ComputationalDependency.dependencyProgram argumentEquations computationalHost
    (by decide) "mm0:support" (by decide) _ _).mpr (ComputationalDependency.support_reused context expression)

set_option maxRecDepth 2048 in
theorem difference_reused (source removed : List Nat) :
    Applies freeVariablesProgram computationalHost "nik:nat-difference" [encodeNaturals source, encodeNaturals removed]
      (encodeNaturals (subtract source removed)) := by
  have initial := (Applies.frame_iff naturalDifferenceProgram ComputationalSupport.supportProgram []
    computationalHost (by decide) (by simp) "nik:nat-difference" (by decide) _ _).mpr
      (natural_difference_computes source removed)
  have initial' : Applies ((ComputationalSupport.supportProgram ++ naturalMembershipProgram) ++ naturalDifferenceEquations)
      computationalHost "nik:nat-difference" [encodeNaturals source, encodeNaturals removed]
      (encodeNaturals (subtract source removed)) := by
    simpa only [naturalDifferenceProgram, List.append_nil, List.append_assoc, encodeNaturals, subtract] using initial
  have inserted := (Applies.insert_iff (ComputationalSupport.supportProgram ++ naturalMembershipProgram)
    naturalDifferenceEquations (ComputationalDependency.dependencyEquations ++ argumentEquations)
    computationalHost (by decide) "nik:nat-difference" (by decide) _ _).mpr initial'
  have inBase : Applies freeVariablesBase computationalHost "nik:nat-difference"
      [encodeNaturals source, encodeNaturals removed] (encodeNaturals (subtract source removed)) := by
    simpa only [freeVariablesBase, argumentProgram, ComputationalDependency.dependencyProgram, List.append_assoc] using inserted
  exact (Applies.append_iff freeVariablesBase freeVariablesEquations computationalHost
    freeVariablesEquations_disjoint "nik:nat-difference" (by decide) _ _).mpr inBase

theorem append_reused (left right : List Nat) :
    Applies freeVariablesProgram computationalHost "nik:list-append" [encodeNaturals left, encodeNaturals right]
      (encodeNaturals (left ++ right)) := by
  have enlarged := (Applies.append_iff ComputationalSupport.supportProgram
    (naturalMembershipProgram ++ ComputationalDependency.dependencyEquations ++ argumentEquations)
    computationalHost (by decide) "nik:list-append" (by decide) _ _).mpr
      (ComputationalSupport.append_reused left right)
  apply arguments_reused "nik:list-append" (by decide)
  simpa only [argumentProgram, ComputationalDependency.dependencyProgram, List.append_assoc] using enlarged

end Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables
