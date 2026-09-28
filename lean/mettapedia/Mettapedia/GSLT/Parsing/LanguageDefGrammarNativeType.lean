import Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation

/-!
# Grammar-derived folds and their operational native types

A source grammar's typed constructor routes enter the generic evaluation
GSLT without changing constructor identity, order, or child sorts. OSLF of
that computation supplies exact-result native types. An admitted direct
interpreter computes without allocating the reference machine states; its
native-type evidence establishes reference reachability of the result.

The syntax interpretation additionally connects this operational native type
to the original `LanguageDef` derivation relation, in both directions. A
compact interpretation still needs its own representation-preservation law,
and no native C backend correspondence is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeType

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation
open Mettapedia.OSLF.Framework.PathTypeSynthesis

mutual
  /-- Reference evaluation states retain precisely the grammar's constructors. -/
  def initialState {rules : List CompiledRule} (interpretation : Interpretation rules)
      {sort : String} : ConstructionTree (syntaxAlgebra rules) sort →
      State interpretation.algebra sort
    | .source impossible => Empty.elim impossible
    | .apply operation arguments =>
        .apply operation (initialArguments interpretation arguments)

  def initialArguments {rules : List CompiledRule} (interpretation : Interpretation rules)
      {sorts : List String} : ConstructionArguments (syntaxAlgebra rules) sorts →
      Arguments interpretation.algebra sorts
    | .nil => .nil
    | .cons head tail =>
        .cons (initialState interpretation head) (initialArguments interpretation tail)
end

mutual
  theorem initialState_evaluates {rules : List CompiledRule}
      (interpretation : Interpretation rules) {sort : String}
      (route : ConstructionTree (syntaxAlgebra rules) sort) :
      (valueAlgebra interpretation.algebra).evaluate (initialState interpretation route) =
        interpret interpretation route := by
    match route with
    | .source impossible => exact Empty.elim impossible
    | .apply operation arguments =>
        change interpretation.operation operation
          ((valueAlgebra interpretation.algebra).evaluateArguments
            (initialArguments interpretation arguments)) = _
        rw [initialArguments_evaluate interpretation arguments]
        rfl
    termination_by structural route

  theorem initialArguments_evaluate {rules : List CompiledRule}
      (interpretation : Interpretation rules) {sorts : List String}
      (arguments : ConstructionArguments (syntaxAlgebra rules) sorts) :
      (valueAlgebra interpretation.algebra).evaluateArguments
        (initialArguments interpretation arguments) = interpretArguments interpretation arguments := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        change FamilyList.cons
          ((valueAlgebra interpretation.algebra).evaluate (initialState interpretation head))
          ((valueAlgebra interpretation.algebra).evaluateArguments
            (initialArguments interpretation tail)) = _
        rw [initialState_evaluates interpretation head,
          initialArguments_evaluate interpretation tail]
        rfl
    termination_by structural arguments
end

/-- The result is a native type of the interpreting computation, not a type
of an unrelated static AST or an inert output carrier. -/
theorem result_native_iff {rules : List CompiledRule}
    (interpretation : Interpretation rules) {sort : String}
    (route : ConstructionTree (syntaxAlgebra rules) sort)
    (value : interpretation.Carrier sort) :
    (pathOSLF (evaluationGSLT interpretation.algebra sort)).satisfies
      (initialState interpretation route)
      (resultNativeType interpretation.algebra value).pred ↔
        interpret interpretation route = value :=
  (satisfies_result_iff interpretation.algebra _ value).trans
    (by rw [initialState_evaluates]; rfl)

/-- Admission of a specialized grammar interpreter consumes the native-type
judgment for the exact source-indexed interpretation being specialized. -/
structure AdmittedInterpreter {rules : List CompiledRule}
    (interpretation : Interpretation rules) where
  run : {sort : String} → ConstructionTree (syntaxAlgebra rules) sort →
    interpretation.Carrier sort
  admitted : ∀ {sort : String} (route : ConstructionTree (syntaxAlgebra rules) sort),
    (pathOSLF (evaluationGSLT interpretation.algebra sort)).satisfies
      (initialState interpretation route)
      (resultNativeType interpretation.algebra (run route)).pred

/-- Execute the direct structural fold; reference-state construction occurs
only in the erased correctness proof. -/
def directInterpreter {rules : List CompiledRule}
    (interpretation : Interpretation rules) : AdmittedInterpreter interpretation where
  run := interpret interpretation
  admitted route := (result_native_iff interpretation route _).mpr rfl

theorem admitted_interpreter_agrees {rules : List CompiledRule}
    {interpretation : Interpretation rules} (interpreter : AdmittedInterpreter interpretation)
    {sort : String} (route : ConstructionTree (syntaxAlgebra rules) sort) :
    interpreter.run route = interpret interpretation route :=
  ((result_native_iff interpretation route _).mp (interpreter.admitted route)).symm

theorem admitted_interpreter_reachable {rules : List CompiledRule}
    {interpretation : Interpretation rules} (interpreter : AdmittedInterpreter interpretation)
    {sort : String} (route : ConstructionTree (syntaxAlgebra rules) sort) :
    Steps interpretation.algebra (initialState interpretation route)
      (.source (interpreter.run route)) := by
  have result := initialState_evaluates interpretation route
  rw [← admitted_interpreter_agrees interpreter route] at result
  rw [← result]
  exact normalize interpretation.algebra _

/-- The syntax observation uses exactly the existing compiler's source rows. -/
def syntaxInterpretation (rules : List CompiledRule) : Interpretation rules where
  Carrier := fun _ => Observation
  operation := observeOperation rules

mutual
  theorem interpret_syntax {rules : List CompiledRule} {sort : String}
      (route : ConstructionTree (syntaxAlgebra rules) sort) :
      interpret (syntaxInterpretation rules) route = (syntaxAlgebra rules).evaluate route := by
    match route with
    | .source impossible => exact Empty.elim impossible
    | .apply operation arguments =>
        change observeOperation rules operation
          (interpretArguments (syntaxInterpretation rules) arguments) = _
        rw [interpret_syntax_arguments arguments]
        rfl
    termination_by structural route

  theorem interpret_syntax_arguments {rules : List CompiledRule} {sorts : List String}
      (arguments : ConstructionArguments (syntaxAlgebra rules) sorts) :
      interpretArguments (syntaxInterpretation rules) arguments =
        (syntaxAlgebra rules).evaluateArguments arguments := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        change FamilyList.cons (interpret (syntaxInterpretation rules) head)
          (interpretArguments (syntaxInterpretation rules) tail) = _
        rw [interpret_syntax head, interpret_syntax_arguments tail]
        rfl
    termination_by structural arguments
end

/-- Source grammar derivability is equivalent to existence of a constructor
route inhabiting the native type generated by its interpretation computation.
No finite enumeration of example trees is used. -/
theorem source_derives_iff_native_result
    {binding : Binding} {language : LanguageDef} {rules : List CompiledRule}
    (compiled : compileRules? binding language = some rules)
    (sort : String) (tokens : List String) (tree : Pattern) :
    Derives language sort tokens tree ↔
      ∃ route : ConstructionTree (syntaxAlgebra rules) sort,
        (pathOSLF (evaluationGSLT (syntaxInterpretation rules).algebra sort)).satisfies
          (initialState (syntaxInterpretation rules) route)
          (resultNativeType (syntaxInterpretation rules).algebra
            (⟨tokens, tree⟩ : Observation)).pred := by
  refine (source_derives_iff_route compiled sort tokens tree).trans ?_
  apply exists_congr
  intro route
  exact (result_native_iff (syntaxInterpretation rules) route _).trans
    (by rw [interpret_syntax]; rfl) |>.symm

#print axioms result_native_iff
#print axioms admitted_interpreter_reachable
#print axioms source_derives_iff_native_result

end Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeType
