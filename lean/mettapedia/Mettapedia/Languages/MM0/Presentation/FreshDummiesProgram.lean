import Mettapedia.Languages.MM0.Presentation.ArgumentCorrespondence
import Mettapedia.Languages.MM0.Kernel.FreshDummies

/-!
# Authored freshness checks for MM0 definition unfolding

Freshness uses complete occurrence support, including bound occurrences.
Each accepted dummy is appended to the arguments inspected for the next one,
so later dummies must also avoid earlier images. The equations reuse argument
typing, dependency checking and list append; no guest primitive is added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def freshEquations : Program := [
  ⟨"fresh-for", "mm0:fresh-for", [v "target", v "image", v "expression"],
    c "mm0:check-pair" [v "target", natural 0, v "image", encodeBinder (.regular 0 ∅),
      natural 0, v "expression"]⟩,
  ⟨"fresh-all", "mm0:fresh-all", [v "target", v "image", v "arguments"],
    c "mm0:fresh-all-view" [c "nik:list-view" [v "arguments"], v "target", v "image"]⟩,
  ⟨"fresh-empty", "mm0:fresh-all-view", [.sym "List:Nil", v "target", v "image"], .sym "True"⟩,
  ⟨"fresh-cons", "mm0:fresh-all-view",
    [c "List:Cons" [v "expression", v "arguments"], v "target", v "image"],
    c "mm0:fresh-all-next" [c "mm0:fresh-for" [v "target", v "image", v "expression"],
      v "target", v "image", v "arguments"]⟩,
  ⟨"fresh-refuses", "mm0:fresh-all-next", [.sym "False", v "target", v "image", v "arguments"], .sym "False"⟩,
  ⟨"fresh-next", "mm0:fresh-all-next", [.sym "True", v "target", v "image", v "arguments"],
    c "mm0:fresh-all" [v "target", v "image", v "arguments"]⟩,
  ⟨"dummies", "mm0:check-dummies", [v "target", v "arguments", v "sorts", v "images"],
    c "mm0:dummies-view" [c "nik:list-view" [v "sorts"], c "nik:list-view" [v "images"],
      v "target", v "arguments"]⟩,
  ⟨"dummies-empty", "mm0:dummies-view", [.sym "List:Nil", .sym "List:Nil", v "target", v "arguments"], .sym "True"⟩,
  ⟨"dummy-missing", "mm0:dummies-view",
    [c "List:Cons" [v "sort", v "sorts"], .sym "List:Nil", v "target", v "arguments"], .sym "False"⟩,
  ⟨"dummy-extra", "mm0:dummies-view",
    [.sym "List:Nil", c "List:Cons" [v "image", v "images"], v "target", v "arguments"], .sym "False"⟩,
  ⟨"dummies-cons", "mm0:dummies-view",
    [c "List:Cons" [v "sort", v "sorts"], c "List:Cons" [v "image", v "images"], v "target", v "arguments"],
    c "mm0:dummy-sort" [c "mm0:check-binder" [.list [], v "target", c "MM0:Var" [v "image"],
      .list [.sym "MM0:Bound", v "sort"]], v "target", v "arguments", v "sorts", v "images", v "image"]⟩,
  ⟨"dummy-sort-refuses", "mm0:dummy-sort",
    [.sym "False", v "target", v "arguments", v "sorts", v "images", v "image"], .sym "False"⟩,
  ⟨"dummy-sort-admitted", "mm0:dummy-sort",
    [.sym "True", v "target", v "arguments", v "sorts", v "images", v "image"],
    c "mm0:dummy-fresh" [c "mm0:fresh-all" [v "target", v "image", v "arguments"],
      v "target", v "arguments", v "sorts", v "images", v "image"]⟩,
  ⟨"dummy-fresh-refuses", "mm0:dummy-fresh",
    [.sym "False", v "target", v "arguments", v "sorts", v "images", v "image"], .sym "False"⟩,
  ⟨"dummy-fresh-admitted", "mm0:dummy-fresh",
    [.sym "True", v "target", v "arguments", v "sorts", v "images", v "image"],
    c "mm0:check-dummies" [v "target", c "nik:list-append" [v "arguments",
      c "nik:list-cons" [c "MM0:Var" [v "image"], .list []]], v "sorts", v "images"]⟩]

def freshProgram : Program := argumentProgram ++ freshEquations

theorem freshProgram_leftLinear : LeftLinear freshProgram := by
  simp only [freshProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨argumentProgram_leftLinear, ?_⟩
  simp [freshEquations, c, v, encodeBinder, encodeDependencies, encodeNaturals,
    patternVarsList, patternVars, natural]

theorem freshProgram_dataSeparated : DataSeparated freshProgram computationalHost where
  undefined := by
    intro head member
    have prior := argumentProgram_dataSeparated.undefined head member
    simp only [freshProgram, Program.defines, List.any_append]
    change (argumentProgram.defines head || freshEquations.defines head) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := argumentProgram_dataSeparated.unhandled

theorem arguments_reused (head : String) (called : head ∈ argumentProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (run : Applies argumentProgram computationalHost head arguments result) :
    Applies freshProgram computationalHost head arguments result :=
  (Applies.append_iff argumentProgram freshEquations computationalHost
    (by decide) head called _ _).mpr run

theorem pair_reused (target : Context) (image : Nat) (expression : Preterm) :
    Applies freshProgram computationalHost "mm0:check-pair"
      [encodeContext target, natural 0, natural image, encodeBinder (.regular 0 ∅), natural 0, encode expression]
      (boolean (Preterm.checkFreshFor target image expression)) := by
  have run := (Applies.append_iff ComputationalDependency.dependencyProgram argumentEquations
    computationalHost (by decide) "mm0:check-pair" (by decide) _ _).mpr
      (ComputationalDependency.pair_computes target 0 image (.regular 0 ∅) 0 expression)
  have lifted := arguments_reused "mm0:check-pair" (by decide) _ _ run
  cases support : Preterm.support? target expression <;>
    simpa [Substitution.checkPair, Kernel.Binder.DependsOn, Preterm.checkFreshFor, support] using lifted

theorem append_reused (left right : List Term) :
    Applies freshProgram computationalHost "nik:list-append" [.list left, .list right] (.list (left ++ right)) := by
  let suffix := ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations ++ freshEquations
  have run := (Applies.frame_iff listAppendProgram typingProgram suffix computationalHost
    (by decide) (by decide) "nik:list-append" (by decide) _ _).mpr (list_append_computes left right)
  simpa only [freshProgram, argumentProgram, ComputationalDependency.dependencyProgram,
    ComputationalSupport.supportProgram, suffix, List.append_assoc] using run

end Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies
