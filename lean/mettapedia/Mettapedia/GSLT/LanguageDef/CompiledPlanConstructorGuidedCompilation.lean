import Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics
import Mettapedia.GSLT.LanguageDef.ConstructorGuidedUnificationCompilation

/-!
# Constructor-guided unification for compiled plans

An admitted compiled-plan application already stores its rigid constructor and
ordered children.  When a dynamic query exposes the same constructor and
arity, the runtime can feed the child pairs directly to unification instead of
materializing the rule-side application and asking the unifier to decompose it
again.

This module embeds the exact compiled-plan term carrier into MeTTapedia's
existing Martelli--Montanari signature.  Query and rule variables receive
different origins, so standardization apart is structural.  The optimization
then reuses the generic constructor-decomposition theorem rather than proving a
second unifier correct.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanConstructorGuidedCompilation

open CompiledPlanAdmission
open Mettapedia.Logic.LP

inductive Constant where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  deriving DecidableEq, Repr

structure FunctionSymbol where
  name : List UInt8
  arity : Nat
  deriving DecidableEq, Repr

inductive VariableOrigin where
  | query
  | rule
  deriving DecidableEq, Repr

structure ScopedVariable where
  origin : VariableOrigin
  slot : UInt32
  deriving DecidableEq, Repr

abbrev signature : LPSignature where
  constants := Constant
  vars := ScopedVariable
  relationSymbols := Unit
  relationArity := fun _ => 0
  functionSymbols := FunctionSymbol
  functionArity := FunctionSymbol.arity

mutual

/-- Encode one admitted plan term into the shared first-order unification
signature while preserving the origin of every variable. -/
def encodeTerm (origin : VariableOrigin) :
    CompiledPlanAdmission.Term -> Mettapedia.Logic.LP.Term signature
  | .symbol name => .const (.symbol name)
  | .variable slot => .var { origin, slot }
  | .string value => .const (.string value)
  | .integer value => .const (.integer value)
  | .application name arguments =>
      let encoded := encodeTerms origin arguments
      .app { name, arity := encoded.length } fun index => encoded.get index

def encodeTerms (origin : VariableOrigin) :
    CompiledPlanAdmission.Terms ->
      List (Mettapedia.Logic.LP.Term signature)
  | .nil => []
  | .cons head tail => encodeTerm origin head :: encodeTerms origin tail

end

abbrev Equation :=
  Mettapedia.Logic.LP.Term signature × Mettapedia.Logic.LP.Term signature

/-- Recognize the exact exposed-constructor case used by the generic C
machine.  Every other pair fails closed and remains on the ordinary unifier
path. -/
def decompose?
    (ruleHead query : CompiledPlanAdmission.Term)
    (rest : List Equation) : Option (List Equation) :=
  ConstructorGuidedUnificationCompilation.decompose?
    (encodeTerm .rule ruleHead) (encodeTerm .query query) rest

/-- Successful plan-level decomposition is exactly one ordinary
Martelli--Montanari step, including fuel accounting. -/
theorem unifyFuel_decompose?
    (fuel : Nat) (ruleHead query : CompiledPlanAdmission.Term)
    (rest equations : List Equation)
    (accepted : decompose? ruleHead query rest = some equations) :
    Mettapedia.Logic.LP.unifyFuel (fuel + 1)
        ((encodeTerm .rule ruleHead, encodeTerm .query query) :: rest) =
      Mettapedia.Logic.LP.unifyFuel fuel equations := by
  exact ConstructorGuidedUnificationCompilation.unifyFuel_decompose?
    fuel (encodeTerm .rule ruleHead) (encodeTerm .query query)
    rest equations accepted

/-- The admitted transform retains the source pair and exact emitted equation
program. -/
structure AdmittedDecomposition where
  ruleHead : CompiledPlanAdmission.Term
  query : CompiledPlanAdmission.Term
  rest : List Equation
  equations : List Equation
  compile_eq : decompose? ruleHead query rest = some equations

def admit?
    (ruleHead query : CompiledPlanAdmission.Term)
    (rest : List Equation) : Option AdmittedDecomposition :=
  match accepted : decompose? ruleHead query rest with
  | none => none
  | some equations => some {
      ruleHead, query, rest, equations, compile_eq := accepted }

/-- The source route constructs one temporary rule-side application before
the unifier immediately decomposes it. -/
def sourceConstructorMaterializations (_ : AdmittedDecomposition) : Nat := 1

/-- The generated route schedules the child equations directly. -/
def compiledConstructorMaterializations (_ : AdmittedDecomposition) : Nat := 0

theorem compiledConstructorMaterializations_lt_source
    (admitted : AdmittedDecomposition) :
    compiledConstructorMaterializations admitted <
      sourceConstructorMaterializations admitted := by
  simp [compiledConstructorMaterializations, sourceConstructorMaterializations]

/-! ## Independent witnesses and rejecting controls -/

private def parserRule : CompiledPlanAdmission.Term :=
  .application [1]
    (.cons (.symbol [2])
      (.cons (.application [3] (.cons (.variable 0) .nil)) .nil))

private def parserQuery : CompiledPlanAdmission.Term :=
  .application [1]
    (.cons (.variable 4)
      (.cons (.application [3] (.cons (.string [5]) .nil)) .nil))

/-- A parser-list-shaped constructor pair emits child equations. -/
example : (decompose? parserRule parserQuery []).isSome = true := by
  decide

private def proofRule : CompiledPlanAdmission.Term :=
  .application [10]
    (.cons (.application [11] (.cons (.variable 0) .nil))
      (.cons (.symbol [12]) .nil))

private def proofQuery : CompiledPlanAdmission.Term :=
  .application [10]
    (.cons (.variable 7) (.cons (.variable 8) .nil))

/-- A proof-step-shaped constructor pair independently inhabits the same
fragment. -/
example : (decompose? proofRule proofQuery []).isSome = true := by
  decide

/-- Differing constructors fail closed. -/
example :
    (decompose? parserRule
      (.application [9]
        (.cons (.variable 4) (.cons (.variable 5) .nil))) []).isSome =
      false := by
  decide

/-- A variable query does not falsely expose a constructor. -/
example : (decompose? parserRule (.variable 4) []).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanConstructorGuidedCompilation
