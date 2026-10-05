import Mettapedia.Languages.MM0.Presentation.DependencyCorrespondence

/-!
# Authored MM0 argument checking

Bound arguments must be bound variables of the declared sort. Regular arguments
must be saturated expressions of the declared sort. The complete argument list
must have exactly the formal context's length. Dependency permission is checked
separately and cannot replace any of these typing obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalArguments

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeExpressions (expressions : List Preterm) : Term := .list (expressions.map encode)

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def argumentEquations : Program := [
  ⟨"check-bound", "mm0:check-binder",
    [v "table", v "target", v "expression", .list [.sym "MM0:Bound", v "sort"]],
    c "mm0:check-sort" [c "mm0:bound-sort" [v "target", v "expression"], v "sort"]⟩,
  ⟨"check-regular", "mm0:check-binder",
    [v "table", v "target", v "expression", .list [.sym "MM0:Regular", v "sort", v "dependencies"]],
    c "mm0:check-type" [c "mm0:infer" [v "table", v "target", v "expression"], v "sort"]⟩,
  ⟨"check-no-sort", "mm0:check-sort", [.sym "None", v "expected"], .sym "False"⟩,
  ⟨"check-sort", "mm0:check-sort", [c "Some" [v "actual"], v "expected"],
    c "nik:nat-eq" [v "actual", v "expected"]⟩,
  ⟨"check-no-type", "mm0:check-type", [.sym "None", v "expected"], .sym "False"⟩,
  ⟨"check-type", "mm0:check-type", [c "MM0:Inferred" [v "remaining", v "actual"], v "expected"],
    c "mm0:check-saturated" [c "nik:list-view" [v "remaining"], v "actual", v "expected"]⟩,
  ⟨"check-saturated", "mm0:check-saturated", [.sym "List:Nil", v "actual", v "expected"],
    c "nik:nat-eq" [v "actual", v "expected"]⟩,
  ⟨"check-unsaturated", "mm0:check-saturated",
    [c "List:Cons" [v "first", v "rest"], v "actual", v "expected"], .sym "False"⟩,
  ⟨"check-arguments", "mm0:check-arguments", [v "table", v "target", v "expressions", v "formal"],
    c "mm0:check-arguments-view" [c "nik:list-view" [v "expressions"], c "nik:list-view" [v "formal"],
      v "table", v "target"]⟩,
  ⟨"check-empty-arguments", "mm0:check-arguments-view",
    [.sym "List:Nil", .sym "List:Nil", v "table", v "target"], .sym "True"⟩,
  ⟨"check-missing-argument", "mm0:check-arguments-view",
    [.sym "List:Nil", c "List:Cons" [v "binder", v "formal"], v "table", v "target"], .sym "False"⟩,
  ⟨"check-extra-argument", "mm0:check-arguments-view",
    [c "List:Cons" [v "expression", v "expressions"], .sym "List:Nil", v "table", v "target"], .sym "False"⟩,
  ⟨"check-argument-cons", "mm0:check-arguments-view",
    [c "List:Cons" [v "expression", v "expressions"], c "List:Cons" [v "binder", v "formal"],
      v "table", v "target"],
    c "mm0:check-arguments-next" [c "mm0:check-binder" [v "table", v "target", v "expression", v "binder"],
      v "table", v "target", v "expressions", v "formal"]⟩,
  ⟨"check-argument-refuses", "mm0:check-arguments-next",
    [.sym "False", v "table", v "target", v "expressions", v "formal"], .sym "False"⟩,
  ⟨"check-argument-next", "mm0:check-arguments-next",
    [.sym "True", v "table", v "target", v "expressions", v "formal"],
    c "mm0:check-arguments" [v "table", v "target", v "expressions", v "formal"]⟩]

def argumentProgram : Program := ComputationalDependency.dependencyProgram ++ argumentEquations

theorem argumentProgram_leftLinear : LeftLinear argumentProgram := by
  simp only [argumentProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨ComputationalDependency.dependencyProgram_leftLinear, ?_⟩
  simp [argumentEquations, c, v, patternVarsList, patternVars]

theorem argumentProgram_dataSeparated : DataSeparated argumentProgram computationalHost where
  undefined := by
    intro head member
    have prior := ComputationalDependency.dependencyProgram_dataSeparated.undefined head member
    simp only [argumentProgram, Program.defines, List.any_append]
    change (ComputationalDependency.dependencyProgram.defines head || argumentEquations.defines head) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := ComputationalDependency.dependencyProgram_dataSeparated.unhandled

end Mettapedia.Languages.MM0.Presentation.ComputationalArguments
