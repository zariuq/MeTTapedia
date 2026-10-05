import Mettapedia.Languages.MM0.Presentation.ArgumentCorrespondence

/-!
# Authored MM0 admissible-substitution checking

Argument typing is checked before the dependency matrix is traversed. Matrix
entries retain the formal binder, its actual replacement and its formal
position. Every bound image is checked against all entries, including entries
preceding it. The traversal uses the existing authored dependency-pair check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible

open Kernel ComputationalContext ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeEntry (entry : Substitution.Entry) : Term :=
  .expr [.sym "MM0:Entry", encodeBinder entry.1.1, encode entry.1.2, natural entry.2]

def encodeEntries (entries : List Substitution.Entry) : Term := .list (entries.map encodeEntry)

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def admissibleEquations : Program := [
  ⟨"entries", "mm0:entries", [v "formal", v "expressions", v "index"],
    c "mm0:entries-view" [c "nik:list-view" [v "formal"], c "nik:list-view" [v "expressions"], v "index"]⟩,
  ⟨"entries-formal-empty", "mm0:entries-view", [.sym "List:Nil", v "expressions", v "index"], .list []⟩,
  ⟨"entries-expressions-empty", "mm0:entries-view",
    [c "List:Cons" [v "binder", v "formal"], .sym "List:Nil", v "index"], .list []⟩,
  ⟨"entries-cons", "mm0:entries-view",
    [c "List:Cons" [v "binder", v "formal"], c "List:Cons" [v "expression", v "expressions"], v "index"],
    c "nik:list-cons" [c "MM0:Entry" [v "binder", v "expression", v "index"],
      c "mm0:entries" [v "formal", v "expressions", c "nik:nat-add" [v "index", natural 1]]]⟩,
  ⟨"pairs", "mm0:check-pairs", [v "target", v "formal-bound", v "target-bound", v "entries"],
    c "mm0:pairs-view" [c "nik:list-view" [v "entries"], v "target", v "formal-bound", v "target-bound"]⟩,
  ⟨"pairs-empty", "mm0:pairs-view", [.sym "List:Nil", v "target", v "formal-bound", v "target-bound"], .sym "True"⟩,
  ⟨"pairs-cons", "mm0:pairs-view",
    [c "List:Cons" [c "MM0:Entry" [v "binder", v "expression", v "position"], v "rest"],
      v "target", v "formal-bound", v "target-bound"],
    c "mm0:pairs-next" [c "mm0:check-pair" [v "target", v "formal-bound", v "target-bound",
      v "binder", v "position", v "expression"], v "target", v "formal-bound", v "target-bound", v "rest"]⟩,
  ⟨"pairs-refuse", "mm0:pairs-next",
    [.sym "False", v "target", v "formal-bound", v "target-bound", v "rest"], .sym "False"⟩,
  ⟨"pairs-next", "mm0:pairs-next",
    [.sym "True", v "target", v "formal-bound", v "target-bound", v "rest"],
    c "mm0:check-pairs" [v "target", v "formal-bound", v "target-bound", v "rest"]⟩,
  ⟨"row-bound", "mm0:check-row",
    [v "target", v "all", c "MM0:Entry" [.list [.sym "MM0:Bound", v "sort"], c "MM0:Var" [v "image"], v "position"]],
    c "mm0:check-pairs" [v "target", v "position", v "image", v "all"]⟩,
  ⟨"row-bound-term", "mm0:check-row",
    [v "target", v "all", c "MM0:Entry" [.list [.sym "MM0:Bound", v "sort"], c "MM0:Term" [v "symbol"], v "position"]],
    .sym "True"⟩,
  ⟨"row-bound-application", "mm0:check-row",
    [v "target", v "all", c "MM0:Entry" [.list [.sym "MM0:Bound", v "sort"],
      c "MM0:App" [v "function", v "argument"], v "position"]], .sym "True"⟩,
  ⟨"row-regular", "mm0:check-row",
    [v "target", v "all", c "MM0:Entry" [.list [.sym "MM0:Regular", v "sort", v "dependencies"], v "expression", v "position"]],
    .sym "True"⟩,
  ⟨"rows", "mm0:check-rows", [v "target", v "all", v "entries"],
    c "mm0:rows-view" [c "nik:list-view" [v "entries"], v "target", v "all"]⟩,
  ⟨"rows-empty", "mm0:rows-view", [.sym "List:Nil", v "target", v "all"], .sym "True"⟩,
  ⟨"rows-cons", "mm0:rows-view", [c "List:Cons" [v "entry", v "rest"], v "target", v "all"],
    c "mm0:rows-next" [c "mm0:check-row" [v "target", v "all", v "entry"], v "target", v "all", v "rest"]⟩,
  ⟨"rows-refuse", "mm0:rows-next", [.sym "False", v "target", v "all", v "rest"], .sym "False"⟩,
  ⟨"rows-next", "mm0:rows-next", [.sym "True", v "target", v "all", v "rest"],
    c "mm0:check-rows" [v "target", v "all", v "rest"]⟩,
  ⟨"admissible", "mm0:check-admissible", [v "table", v "formal", v "target", v "expressions"],
    c "mm0:admissible-typed" [c "mm0:check-arguments" [v "table", v "target", v "expressions", v "formal"],
      v "target", v "formal", v "expressions"]⟩,
  ⟨"admissible-ill-typed", "mm0:admissible-typed", [.sym "False", v "target", v "formal", v "expressions"], .sym "False"⟩,
  ⟨"admissible-typed", "mm0:admissible-typed", [.sym "True", v "target", v "formal", v "expressions"],
    c "mm0:admissible-entries" [v "target", c "mm0:entries" [v "formal", v "expressions", natural 0]]⟩,
  ⟨"admissible-entries", "mm0:admissible-entries", [v "target", v "entries"],
    c "mm0:check-rows" [v "target", v "entries", v "entries"]⟩]

def admissibleProgram : Program := argumentProgram ++ admissibleEquations

theorem admissibleProgram_leftLinear : LeftLinear admissibleProgram := by
  simp only [admissibleProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨argumentProgram_leftLinear, ?_⟩
  simp [admissibleEquations, c, v, patternVarsList, patternVars]

theorem admissibleProgram_dataSeparated : DataSeparated admissibleProgram computationalHost where
  undefined := by
    intro head member
    have prior := argumentProgram_dataSeparated.undefined head member
    simp only [admissibleProgram, Program.defines, List.any_append]
    change (argumentProgram.defines head || admissibleEquations.defines head) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := argumentProgram_dataSeparated.unhandled

theorem arguments_reused (table : ComputationalTyping.SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context) :
    Applies admissibleProgram computationalHost "mm0:check-arguments"
      [ComputationalTyping.encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal]
      (boolean (Substitution.checkArguments (ComputationalTyping.signatureOf table) target expressions formal)) := by
  exact (Applies.append_iff argumentProgram admissibleEquations computationalHost (by decide)
    "mm0:check-arguments" (by decide) _ _).mpr (arguments_computes table target expressions formal)

theorem pair_reused (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) :
    Applies admissibleProgram computationalHost "mm0:check-pair"
      [encodeContext target, natural formalBound, natural targetBound,
        encodeBinder binder, natural position, encode expression]
      (boolean (Substitution.checkPair target formalBound targetBound ((binder, expression), position))) := by
  have first := (Applies.append_iff ComputationalDependency.dependencyProgram argumentEquations computationalHost
    (by decide) "mm0:check-pair" (by decide) _ _).mpr
      (ComputationalDependency.pair_computes target formalBound targetBound binder position expression)
  exact (Applies.append_iff argumentProgram admissibleEquations computationalHost (by decide)
    "mm0:check-pair" (by decide) _ _).mpr first

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible
