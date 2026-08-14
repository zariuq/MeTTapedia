import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Parsing.HornUnification

/-!
# Constructor-guided unification compilation

A generated rule plan already exposes every rigid constructor in a rule head.
When the dynamic candidate exposes the same constructor and arity, a general
unifier would immediately decompose the pair into its ordered child equations.
The generated machine can perform that decomposition directly, without first
materializing the rule-side constructor node.

This module states that optimization at the Martelli--Montanari equation
boundary.  The recognizer is local and decidable, the transformed equation
list is explicit, and the realization theorem preserves the complete returned
substitution.  Variables and constructor disagreements fail recognition and
remain the responsibility of the general unifier.
-/

namespace Mettapedia.GSLT.LanguageDef.ConstructorGuidedUnificationCompilation

open Mettapedia.Logic.LP

variable {signature : LPSignature}
  [DecidableEq signature.vars]
  [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]

abbrev Equation (signature : LPSignature) :=
  Term signature × Term signature

/-- Recognize one rigid constructor pair and emit exactly the child equations
that Martelli--Montanari would schedule next. -/
def decompose?
    (left right : Term signature)
    (rest : List (Equation signature)) :
    Option (List (Equation signature)) :=
  match left, right with
  | .app leftHead leftArguments, .app rightHead rightArguments =>
      if same : leftHead = rightHead then
        some (finPairsToList leftArguments (same ▸ rightArguments) ++ rest)
      else none
  | _, _ => none

/-- An admitted decomposition retains both source equation and exact emitted
equation list. -/
structure AdmittedDecomposition (signature : LPSignature)
    [DecidableEq signature.functionSymbols] where
  left : Term signature
  right : Term signature
  rest : List (Equation signature)
  equations : List (Equation signature)
  compile_eq : decompose? left right rest = some equations

/-- Run the local recognizer and retain its successful equation compiler
witness. -/
def admit?
    (left right : Term signature)
    (rest : List (Equation signature)) :
    Option (AdmittedDecomposition signature) :=
  match accepted : decompose? left right rest with
  | none => none
  | some equations => some {
      left, right, rest, equations, compile_eq := accepted }

/-- Direct constructor decomposition is exactly one ordinary unifier step.
The transformed path consumes the same one unit of fuel in advance. -/
theorem unifyFuel_decompose?
    (fuel : Nat) (left right : Term signature)
    (rest equations : List (Equation signature))
    (accepted : decompose? left right rest = some equations) :
    unifyFuel (fuel + 1) ((left, right) :: rest) =
      unifyFuel fuel equations := by
  cases left <;> cases right <;> simp [decompose?] at accepted
  rename_i leftHead leftArguments rightHead rightArguments
  obtain ⟨same, rfl⟩ := accepted
  subst rightHead
  simp [unifyFuel]

/-- Constructor decomposition as a composable computed realization. -/
def constructorDecompositionRealization :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedDecomposition signature)
      (List (Equation signature))
      (Nat → Option (Subst signature)) where
  compile := fun _ admitted => admitted.equations
  observeSource := fun _ admitted fuel =>
    unifyFuel (fuel + 1)
      ((admitted.left, admitted.right) :: admitted.rest)
  observeArtifact := fun _ equations fuel => unifyFuel fuel equations
  adequate := by
    intro _ admitted
    funext fuel
    exact (unifyFuel_decompose? fuel admitted.left admitted.right
      admitted.rest admitted.equations admitted.compile_eq).symm

/-! ## Work accounting -/

/-- The source route materializes one rule-side constructor before the
unifier decomposes it. -/
def sourceConstructorMaterializations
    (_ : AdmittedDecomposition signature) : Nat := 1

/-- The admitted direct route emits child equations without that temporary
constructor. -/
def compiledConstructorMaterializations
    (_ : AdmittedDecomposition signature) : Nat := 0

omit [DecidableEq signature.vars] [DecidableEq signature.constants] in
theorem compiledConstructorMaterializations_lt_source
    (admitted : AdmittedDecomposition signature) :
    compiledConstructorMaterializations admitted <
      sourceConstructorMaterializations admitted := by
  simp [compiledConstructorMaterializations,
    sourceConstructorMaterializations]

/-! ## Independent witnesses and rejection boundaries -/

namespace Canaries

open Mettapedia.GSLT.Parsing.HornCertificate
open Mettapedia.GSLT.Parsing.HornUnification

private def parserLeft : Term compilerSignature :=
  encodeScopedTerm .query
    (.app "cons" (.ofList [.atom "token", .var 0]))

private def parserRight : Term compilerSignature :=
  encodeScopedTerm .rule
    (.app "cons" (.ofList [.var 4, .var 5]))

private def proofLeft : Term compilerSignature :=
  encodeScopedTerm .query
    (.app "step" (.ofList [
      .app "claim" (.ofList [.var 0]), .atom "label"]))

private def proofRight : Term compilerSignature :=
  encodeScopedTerm .rule
    (.app "step" (.ofList [.var 7, .var 8]))

/-- A parser-list constructor is recognized independently of its variables. -/
example : (decompose? parserLeft parserRight []).isSome = true := by
  decide

/-- A proof-like constructor with a different shape is admitted by the same
recognizer. -/
example : (decompose? proofLeft proofRight []).isSome = true := by
  decide

/-- Differing rigid constructors fail closed. -/
example :
    (decompose? parserLeft
      (encodeScopedTerm .rule
        (.app "nil" (.ofList [.var 4, .var 5]))) []).isSome = false := by
  decide

/-- A dynamic variable is not falsely treated as an exposed constructor. -/
example :
    (decompose? parserLeft
      (encodeScopedTerm .rule (.var 4)) []).isSome = false := by
  decide

end Canaries

end Mettapedia.GSLT.LanguageDef.ConstructorGuidedUnificationCompilation
