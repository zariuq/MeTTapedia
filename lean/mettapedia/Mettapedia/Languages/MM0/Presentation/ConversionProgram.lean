import Mettapedia.Languages.MM0.Presentation.ConversionData
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramSuffix
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ComputationLists

/-!
# Authored MM0 conversion checking

The supplied witness selects the rule and its children. The equations compute
typing, exact middle endpoints, binder checks and definition unfolding. No
conversion search or normalization service is called. The result contains both
actual endpoints and their sort; failure of a supplied witness returns None.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalConversion

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def conversionEquations : Program := [
  ⟨"apply-args", "mm0:apply-args", [v "function", v "arguments"],
    c "mm0:apply-args-view" [v "function", c "nik:list-view" [v "arguments"]]⟩,
  ⟨"apply-args-empty", "mm0:apply-args-view", [v "function", .sym "List:Nil"], v "function"⟩,
  ⟨"apply-args-cons", "mm0:apply-args-view", [v "function", c "List:Cons" [v "argument", v "arguments"]],
    c "mm0:apply-args" [c "MM0:App" [v "function", v "argument"], v "arguments"]⟩,
  ⟨"conversion-refl", "mm0:conversion", [v "table", v "definitions", v "context", .list [.sym "MM0:ConvRefl", v "expression"]],
    c "mm0:conversion-refl-type" [c "mm0:infer" [v "table", v "context", v "expression"], v "expression"]⟩,
  ⟨"refl-no-type", "mm0:conversion-refl-type", [.sym "None", v "expression"], .sym "None"⟩,
  ⟨"refl-type", "mm0:conversion-refl-type", [c "MM0:Inferred" [v "remaining", v "sort"], v "expression"],
    c "mm0:conversion-refl-saturated" [c "nik:list-view" [v "remaining"], v "expression", v "sort"]⟩,
  ⟨"refl-saturated", "mm0:conversion-refl-saturated", [.sym "List:Nil", v "expression", v "sort"],
    c "MM0:Converted" [v "expression", v "expression", v "sort"]⟩,
  ⟨"refl-unsaturated", "mm0:conversion-refl-saturated", [c "List:Cons" [v "first", v "rest"], v "expression", v "sort"], .sym "None"⟩,
  ⟨"conversion-symm", "mm0:conversion", [v "table", v "definitions", v "context", .list [.sym "MM0:ConvSymm", v "child"]],
    c "mm0:conversion-swap" [c "mm0:conversion" [v "table", v "definitions", v "context", v "child"]]⟩,
  ⟨"swap-none", "mm0:conversion-swap", [.sym "None"], .sym "None"⟩,
  ⟨"swap-result", "mm0:conversion-swap", [c "MM0:Converted" [v "left", v "right", v "sort"]],
    c "MM0:Converted" [v "right", v "left", v "sort"]⟩,
  ⟨"conversion-trans", "mm0:conversion", [v "table", v "definitions", v "context", .list [.sym "MM0:ConvTrans", v "first", v "second"]],
    c "mm0:conversion-first" [c "mm0:conversion" [v "table", v "definitions", v "context", v "first"],
      v "table", v "definitions", v "context", v "second"]⟩,
  ⟨"trans-first-none", "mm0:conversion-first", [.sym "None", v "table", v "definitions", v "context", v "second"], .sym "None"⟩,
  ⟨"trans-first", "mm0:conversion-first", [c "MM0:Converted" [v "left", v "middle", v "sort"], v "table", v "definitions", v "context", v "second"],
    c "mm0:conversion-join" [v "left", v "middle", v "sort",
      c "mm0:conversion" [v "table", v "definitions", v "context", v "second"]]⟩,
  ⟨"trans-second-none", "mm0:conversion-join", [v "left", v "middle", v "sort", .sym "None"], .sym "None"⟩,
  ⟨"trans-second", "mm0:conversion-join", [v "left", v "middle", v "sort", c "MM0:Converted" [v "start", v "right", v "other-sort"]],
    c "mm0:conversion-joined" [c "nik:data-eq" [.list [v "middle", v "sort"], .list [v "start", v "other-sort"]],
      v "left", v "right", v "sort"]⟩,
  ⟨"trans-joined", "mm0:conversion-joined", [.sym "True", v "left", v "right", v "sort"],
    c "MM0:Converted" [v "left", v "right", v "sort"]⟩,
  ⟨"trans-mismatch", "mm0:conversion-joined", [.sym "False", v "left", v "right", v "sort"], .sym "None"⟩,
  ⟨"conversion-congruence", "mm0:conversion", [v "table", v "definitions", v "context", .list [.sym "MM0:ConvCongruence", v "symbol", v "children"]],
    c "mm0:conversion-declaration" [c "mm0:declaration" [v "table", v "symbol"],
      v "table", v "definitions", v "context", v "symbol", v "children"]⟩,
  ⟨"congruence-no-declaration", "mm0:conversion-declaration", [.sym "None", v "table", v "definitions", v "context", v "symbol", v "children"], .sym "None"⟩,
  ⟨"congruence-declaration", "mm0:conversion-declaration", [c "Some" [.list [.sym "MM0:TermDecl", v "formal", v "sort", v "dependencies"]],
    v "table", v "definitions", v "context", v "symbol", v "children"],
    c "mm0:conversion-congruent" [c "mm0:conversion-arguments" [v "table", v "definitions", v "context", v "children", v "formal"],
      v "symbol", v "sort"]⟩,
  ⟨"congruence-no-arguments", "mm0:conversion-congruent", [.sym "None", v "symbol", v "sort"], .sym "None"⟩,
  ⟨"congruence-arguments", "mm0:conversion-congruent", [c "MM0:ConvertedArgs" [v "left", v "right"], v "symbol", v "sort"],
    c "MM0:Converted" [c "mm0:apply-args" [c "MM0:Term" [v "symbol"], v "left"],
      c "mm0:apply-args" [c "MM0:Term" [v "symbol"], v "right"], v "sort"]⟩,
  ⟨"conversion-unfold", "mm0:conversion", [v "table", v "definitions", v "context",
    .list [.sym "MM0:ConvUnfold", v "symbol", v "arguments", v "images"]],
    c "mm0:conversion-unfold-declaration" [c "mm0:declaration" [v "table", v "symbol"],
      v "table", v "definitions", v "context", v "symbol", v "arguments", v "images"]⟩,
  ⟨"conversion-unfold-missing", "mm0:conversion-unfold-declaration", [.sym "None", v "table", v "definitions", v "context", v "symbol", v "arguments", v "images"], .sym "None"⟩,
  ⟨"conversion-unfold-declared", "mm0:conversion-unfold-declaration",
    [c "Some" [.list [.sym "MM0:TermDecl", v "formal", v "sort", v "dependencies"]],
      v "table", v "definitions", v "context", v "symbol", v "arguments", v "images"],
    c "mm0:conversion-unfold-result" [c "mm0:unfold" [v "table", v "definitions", v "context", v "symbol", v "arguments", v "images"],
      v "table", v "context", v "symbol", v "arguments", v "sort"]⟩,
  ⟨"conversion-unfold-none", "mm0:conversion-unfold-result", [.sym "None", v "table", v "context", v "symbol", v "arguments", v "sort"], .sym "None"⟩,
  ⟨"conversion-unfold-result", "mm0:conversion-unfold-result", [c "Some" [v "result"], v "table", v "context", v "symbol", v "arguments", v "sort"],
    c "mm0:conversion-unfold-typed" [c "nik:data-eq" [c "mm0:infer" [v "table", v "context", v "result"],
      c "MM0:Inferred" [.list [], v "sort"]], v "symbol", v "arguments", v "result", v "sort"]⟩,
  ⟨"conversion-unfold-typed", "mm0:conversion-unfold-typed", [.sym "True", v "symbol", v "arguments", v "result", v "sort"],
    c "MM0:Converted" [c "mm0:apply-args" [c "MM0:Term" [v "symbol"], v "arguments"], v "result", v "sort"]⟩,
  ⟨"conversion-unfold-ill-typed", "mm0:conversion-unfold-typed", [.sym "False", v "symbol", v "arguments", v "result", v "sort"], .sym "None"⟩,
  ⟨"conversion-arguments", "mm0:conversion-arguments", [v "table", v "definitions", v "context", v "children", v "formal"],
    c "mm0:conversion-arguments-view" [c "nik:list-view" [v "children"], c "nik:list-view" [v "formal"], v "table", v "definitions", v "context"]⟩,
  ⟨"conversion-arguments-empty", "mm0:conversion-arguments-view", [.sym "List:Nil", .sym "List:Nil", v "table", v "definitions", v "context"],
    c "MM0:ConvertedArgs" [.list [], .list []]⟩,
  ⟨"conversion-arguments-missing", "mm0:conversion-arguments-view", [.sym "List:Nil", c "List:Cons" [v "binder", v "binders"], v "table", v "definitions", v "context"], .sym "None"⟩,
  ⟨"conversion-arguments-extra", "mm0:conversion-arguments-view", [c "List:Cons" [v "child", v "children"], .sym "List:Nil", v "table", v "definitions", v "context"], .sym "None"⟩,
  ⟨"conversion-arguments-cons", "mm0:conversion-arguments-view", [c "List:Cons" [v "child", v "children"], c "List:Cons" [v "binder", v "binders"],
    v "table", v "definitions", v "context"],
    c "mm0:conversion-argument" [c "mm0:conversion" [v "table", v "definitions", v "context", v "child"],
      v "table", v "definitions", v "context", v "children", v "binder", v "binders"]⟩,
  ⟨"conversion-argument-none", "mm0:conversion-argument", [.sym "None", v "table", v "definitions", v "context", v "children", v "binder", v "binders"], .sym "None"⟩,
  ⟨"conversion-argument-result", "mm0:conversion-argument", [c "MM0:Converted" [v "left", v "right", v "sort"],
    v "table", v "definitions", v "context", v "children", v "binder", v "binders"],
    c "mm0:conversion-argument-checked" [c "nik:data-eq" [v "sort", c "mm0:conversion-binder-sort" [v "binder"]],
      c "mm0:check-binder" [v "table", v "context", v "left", v "binder"],
      c "mm0:check-binder" [v "table", v "context", v "right", v "binder"],
      v "table", v "definitions", v "context", v "children", v "binders", v "left", v "right"]⟩,
  ⟨"conversion-bound-sort", "mm0:conversion-binder-sort", [.list [.sym "MM0:Bound", v "sort"]], v "sort"⟩,
  ⟨"conversion-regular-sort", "mm0:conversion-binder-sort", [.list [.sym "MM0:Regular", v "sort", v "dependencies"]], v "sort"⟩,
  ⟨"conversion-argument-checked", "mm0:conversion-argument-checked", [.sym "True", .sym "True", .sym "True",
    v "table", v "definitions", v "context", v "children", v "binders", v "left", v "right"],
    c "mm0:conversion-argument-tail" [c "mm0:conversion-arguments" [v "table", v "definitions", v "context", v "children", v "binders"], v "left", v "right"]⟩,
  ⟨"conversion-argument-refused", "mm0:conversion-argument-checked", [v "sort-ok", v "left-ok", v "right-ok",
    v "table", v "definitions", v "context", v "children", v "binders", v "left", v "right"], .sym "None"⟩,
  ⟨"conversion-argument-tail-none", "mm0:conversion-argument-tail", [.sym "None", v "left", v "right"], .sym "None"⟩,
  ⟨"conversion-argument-tail", "mm0:conversion-argument-tail", [c "MM0:ConvertedArgs" [v "lefts", v "rights"], v "left", v "right"],
    c "MM0:ConvertedArgs" [c "nik:list-cons" [v "left", v "lefts"], c "nik:list-cons" [v "right", v "rights"]]⟩]

def conversionProgram : Program := unfoldingProgram ++ conversionEquations

theorem conversionEquations_disjoint :
    ∀ equation ∈ conversionEquations, equation.head ∉ unfoldingProgram.calledHeads := by
  simp only [unfoldingProgram, ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
  decide

theorem conversionProgram_leftLinear : LeftLinear conversionProgram := by
  simp only [conversionProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨unfoldingProgram_leftLinear, ?_⟩
  simp [conversionEquations, c, v, patternVarsList, patternVars]

theorem conversionProgram_dataSeparated : DataSeparated conversionProgram dataEqualityHost where
  undefined := by
    intro head member
    have prior := unfoldingProgram_dataSeparated.undefined head member
    simp only [conversionProgram, Program.defines, List.any_append]
    change (unfoldingProgram.defines head || conversionEquations.defines head) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := by
    intro head member arguments
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem conversion_equation {head : String} {arguments : List Term} {equation : Equation} {environment : Env} {result : Term}
    (used : head ∈ conversionEquations.map Equation.head)
    (defined : conversionEquations.definesAt head arguments.length = true)
    (selected : conversionEquations.select head arguments = some (equation, environment))
    (body : Evaluates conversionProgram dataEqualityHost environment equation.body result) :
    Applies conversionProgram dataEqualityHost head arguments result :=
  Applies.suffix_equation conversionEquations_disjoint used defined selected body

theorem conversion_apply (head : String) (used : head ∈ conversionEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply conversionProgram dataEqualityHost fuel head arguments =
      applyWith conversionEquations dataEqualityHost (eval conversionProgram dataEqualityHost fuel) head arguments :=
  apply_suffix_eq unfoldingProgram conversionEquations dataEqualityHost conversionEquations_disjoint head used fuel arguments

theorem unfolding_reused (head : String) (used : head ∈ unfoldingProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies unfoldingProgram computationalHost head arguments result) :
    Applies conversionProgram dataEqualityHost head arguments result := by
  have hosts : computationalHost.AgreesOn dataEqualityHost unfoldingProgram.calledHeads :=
    dataEqualityHost_computational_agrees _ (by
      simp only [unfoldingProgram, ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
      decide) (by
      simp only [unfoldingProgram, ComputationalFreshDummies.freshEquations, encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
      decide)
  have run := (Applies.host_iff unfoldingProgram hosts head used arguments result).mp computed
  exact (Applies.append_iff unfoldingProgram conversionEquations dataEqualityHost conversionEquations_disjoint
    head used arguments result).mpr run

theorem argument_reused (head : String) (used : head ∈ argumentProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies argumentProgram computationalHost head arguments result) :
    Applies conversionProgram dataEqualityHost head arguments result :=
  unfolding_reused head (by
    simp only [unfoldingProgram, ComputationalInstantiation.instantiationProgram,
      ComputationalAdmissible.admissibleProgram, Program.calledHeads, List.flatMap_append,
      List.mem_append] at used ⊢
    exact Or.inl (Or.inl (Or.inl used))) _ _
    (fresh_reused head (by
      simp only [ComputationalFreshDummies.freshProgram, Program.calledHeads,
        List.flatMap_append, List.mem_append]
      exact Or.inl used) _ _
      (ComputationalFreshDummies.arguments_reused head used _ _ computed))

theorem infer_reused (table : SignatureTable) (context : Context) (expression : Preterm) :
    Applies conversionProgram dataEqualityHost "mm0:infer"
      [encodeTable table, encodeContext context, encode expression]
      (encodeType (Preterm.infer (signatureOf table) context expression)) := by
  let tail := listAppendProgram ++ ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations
  have run := (Applies.append_iff typingProgram tail computationalHost (by decide)
    "mm0:infer" (by decide) _ _).mpr (infer_computes table context expression)
  apply argument_reused "mm0:infer" (by decide)
  simpa only [argumentProgram, ComputationalDependency.dependencyProgram,
    ComputationalSupport.supportProgram, tail, List.append_assoc] using run

end Mettapedia.Languages.MM0.Presentation.ComputationalConversion
