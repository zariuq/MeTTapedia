import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.CertificateGSLTJudgmentAuthority
import Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender
import Mettapedia.Languages.TPTP.GroundCNFAuthority

/-!
# Ground resolution as an authored calculus GSLT

This definition is the first semantic rule environment used by TSTP
verification.  It does not search for proofs and it does not assign meaning to
an arbitrary TSTP rule name.  Instead, it declares ordered-list operations and
binary ground resolution as ordinary inference judgments.  A checked
derivation must expose the selected pivot occurrence through the recursive
`RemovePositive` / `RemoveNegative` judgments and must construct the resolvent
through `Append`.

The separately stated Boolean-model semantics below proves that every checked
`Resolve` judgment preserves truth.  The finite-Horn projection is the exact
source consumed by CeTTa's generic inference machinery; no resolution branch
is added to the runtime.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def schema (id : String) (metavariables : List String)
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema := {
  id := ⟨id⟩
  metavariables := metavariables.map fun name => (name, 0)
  premises := premises
  conclusion := conclusion
}

def positive (atom : Pattern) : Pattern :=
  a "ground-resolution:positive" [atom]

def negative (atom : Pattern) : Pattern :=
  a "ground-resolution:negative" [atom]

def nil : Pattern := a "ground-resolution:nil"

def cons (head tail : Pattern) : Pattern :=
  a "ground-resolution:cons" [head, tail]

def positiveLeft : Pattern := a "ground-resolution:positive-left"

def positiveRight : Pattern := a "ground-resolution:positive-right"

@[simp] theorem positive_eq_apply (atom : Pattern) :
    positive atom = .apply "ground-resolution:positive" [atom] := rfl

@[simp] theorem negative_eq_apply (atom : Pattern) :
    negative atom = .apply "ground-resolution:negative" [atom] := rfl

@[simp] theorem nil_eq_apply :
    nil = .apply "ground-resolution:nil" [] := rfl

@[simp] theorem cons_eq_apply (head tail : Pattern) :
    cons head tail = .apply "ground-resolution:cons" [head, tail] := rfl

@[simp] theorem positiveLeft_eq_apply :
    positiveLeft = .apply "ground-resolution:positive-left" [] := rfl

@[simp] theorem positiveRight_eq_apply :
    positiveRight = .apply "ground-resolution:positive-right" [] := rfl

def removePositiveJ (pivot source result : Pattern) : Pattern :=
  a "GroundRemovePositive" [pivot, source, result]

def removeNegativeJ (pivot source result : Pattern) : Pattern :=
  a "GroundRemoveNegative" [pivot, source, result]

def appendJ (left right result : Pattern) : Pattern :=
  a "GroundAppend" [left, right, result]

def literalsJ (value : Pattern) : Pattern :=
  a "GroundLiterals" [value]

def resolveJ (orientation pivot left right result : Pattern) : Pattern :=
  a "GroundResolve" [orientation, pivot, left, right, result]

private def p := Pattern.fvar "pivot"
private def h := Pattern.fvar "head"
private def xs := Pattern.fvar "xs"
private def ys := Pattern.fvar "ys"
private def zs := Pattern.fvar "zs"
private def left := Pattern.fvar "left"
private def right := Pattern.fvar "right"
private def leftRest := Pattern.fvar "leftRest"
private def rightRest := Pattern.fvar "rightRest"
private def result := Pattern.fvar "result"

def removePositiveHead : RuleSchema :=
  schema "ground-resolution:remove-positive-head" ["pivot", "xs"] []
    (removePositiveJ p (cons (positive p) xs) xs)

def removePositiveTail : RuleSchema :=
  schema "ground-resolution:remove-positive-tail"
    ["pivot", "head", "xs", "ys"]
    [removePositiveJ p xs ys]
    (removePositiveJ p (cons h xs) (cons h ys))

def removeNegativeHead : RuleSchema :=
  schema "ground-resolution:remove-negative-head" ["pivot", "xs"] []
    (removeNegativeJ p (cons (negative p) xs) xs)

def removeNegativeTail : RuleSchema :=
  schema "ground-resolution:remove-negative-tail"
    ["pivot", "head", "xs", "ys"]
    [removeNegativeJ p xs ys]
    (removeNegativeJ p (cons h xs) (cons h ys))

def appendNil : RuleSchema :=
  schema "ground-resolution:append-nil" ["ys"] []
    (appendJ nil ys ys)

def appendCons : RuleSchema :=
  schema "ground-resolution:append-cons"
    ["head", "xs", "ys", "zs"]
    [appendJ xs ys zs]
    (appendJ (cons h xs) ys (cons h zs))

def literalsNil : RuleSchema :=
  schema "ground-resolution:literals-nil" [] [] (literalsJ nil)

def literalsPositive : RuleSchema :=
  schema "ground-resolution:literals-positive" ["pivot", "xs"]
    [literalsJ xs]
    (literalsJ (cons (positive p) xs))

def literalsNegative : RuleSchema :=
  schema "ground-resolution:literals-negative" ["pivot", "xs"]
    [literalsJ xs]
    (literalsJ (cons (negative p) xs))

def resolvePositiveLeft : RuleSchema :=
  schema "ground-resolution:resolve-positive-left"
    ["pivot", "left", "right", "leftRest", "rightRest", "result"]
    [removePositiveJ p left leftRest,
     removeNegativeJ p right rightRest,
     appendJ leftRest rightRest result,
     literalsJ left, literalsJ right, literalsJ result]
    (resolveJ positiveLeft p left right result)

def resolvePositiveRight : RuleSchema :=
  schema "ground-resolution:resolve-positive-right"
    ["pivot", "left", "right", "leftRest", "rightRest", "result"]
    [removeNegativeJ p left leftRest,
     removePositiveJ p right rightRest,
     appendJ leftRest rightRest result,
     literalsJ left, literalsJ right, literalsJ result]
    (resolveJ positiveRight p left right result)

/-- The complete first slice of the TSTP rule environment. -/
def definition : CalculusLanguageDef where
  name := "TptpGroundResolutionCalculus"
  types := ["Atom", "Literal", "Literals", "Orientation"]
  terms := [
    ctor "ground-resolution:positive" "Literal" [("atom", "Atom")],
    ctor "ground-resolution:negative" "Literal" [("atom", "Atom")],
    ctor "ground-resolution:nil" "Literals" [],
    ctor "ground-resolution:cons" "Literals"
      [("head", "Literal"), ("tail", "Literals")],
    ctor "ground-resolution:positive-left" "Orientation" [],
    ctor "ground-resolution:positive-right" "Orientation" []]
  equations := []
  rewrites := []
  judgments := [
    { head := "GroundRemovePositive", arity := 3 },
    { head := "GroundRemoveNegative", arity := 3 },
    { head := "GroundAppend", arity := 3 },
    { head := "GroundLiterals", arity := 1 },
    { head := "GroundResolve", arity := 5 }]
  rules := [removePositiveHead, removePositiveTail,
    removeNegativeHead, removeNegativeTail,
    appendNil, appendCons, literalsNil, literalsPositive, literalsNegative,
    resolvePositiveLeft, resolvePositiveRight]

theorem definition_admitted : definition.isValid = true := by
  decide +kernel

def validated : ValidatedCalculusLanguageDef :=
  ⟨definition, definition_admitted⟩

theorem definition_inventory :
    definition.types.length = 4 ∧ definition.terms.length = 6 ∧
      definition.judgments.length = 5 ∧ definition.rules.length = 11 := by
  decide

/-- The calculus is in the constructor-only finite-Horn fragment consumed by
the generic CeTTa compiler. -/
theorem finiteHornSource_isSome :
    (renderDefinition? definition).isSome = true := by
  decide +kernel

def finiteHornSource : String :=
  (renderDefinition? definition).getD ""

theorem finiteHornSource_nonempty : finiteHornSource ≠ "" := by
  decide +kernel

/-! ## Canonical proof constructors

These constructors compile the authored rule schemata themselves into typed
CertificateGSLT derivations.  They are the proof-producing boundary used by
TSTP evidence reconstruction; no parallel resolution relation is consulted. -/

def deriveRemovePositiveHead (pivot rest : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (restValid : argumentValidAt 0 rest = true) :
    Derivation validated (removePositiveJ pivot (cons (positive pivot) rest) rest) := by
  let ruleInstance : RuleInstance := {
    ruleId := removePositiveHead.id
    arguments := [pivot, rest]
  }
  exact .byRule ruleInstance (premises := [])
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? removePositiveHead.id =
          some removePositiveHead :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, removePositiveHead, schema, p, xs,
        removePositiveJ, cons, positive, a, argumentsValidAt,
        RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        pivotValid, restValid]))
    .nil

def deriveRemovePositiveTail (pivot head source result : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (headValid : argumentValidAt 0 head = true)
    (sourceValid : argumentValidAt 0 source = true)
    (resultValid : argumentValidAt 0 result = true)
    (child : Derivation validated (removePositiveJ pivot source result)) :
    Derivation validated
      (removePositiveJ pivot (cons head source) (cons head result)) := by
  let ruleInstance : RuleInstance := {
    ruleId := removePositiveTail.id
    arguments := [pivot, head, source, result]
  }
  exact .byRule ruleInstance
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? removePositiveTail.id =
          some removePositiveTail :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, removePositiveTail, schema, p, h, xs, ys,
        removePositiveJ, cons, a, argumentsValidAt,
        RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        pivotValid, headValid, sourceValid, resultValid]))
    (.cons child .nil)

def deriveRemoveNegativeHead (pivot rest : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (restValid : argumentValidAt 0 rest = true) :
    Derivation validated (removeNegativeJ pivot (cons (negative pivot) rest) rest) := by
  let ruleInstance : RuleInstance := {
    ruleId := removeNegativeHead.id
    arguments := [pivot, rest]
  }
  exact .byRule ruleInstance (premises := [])
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? removeNegativeHead.id =
          some removeNegativeHead :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, removeNegativeHead, schema, p, xs,
        removeNegativeJ, cons, negative, a, argumentsValidAt,
        RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        pivotValid, restValid]))
    .nil

def deriveRemoveNegativeTail (pivot head source result : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (headValid : argumentValidAt 0 head = true)
    (sourceValid : argumentValidAt 0 source = true)
    (resultValid : argumentValidAt 0 result = true)
    (child : Derivation validated (removeNegativeJ pivot source result)) :
    Derivation validated
      (removeNegativeJ pivot (cons head source) (cons head result)) := by
  let ruleInstance : RuleInstance := {
    ruleId := removeNegativeTail.id
    arguments := [pivot, head, source, result]
  }
  exact .byRule ruleInstance
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? removeNegativeTail.id =
          some removeNegativeTail :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, removeNegativeTail, schema, p, h, xs, ys,
        removeNegativeJ, cons, a, argumentsValidAt,
        RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        pivotValid, headValid, sourceValid, resultValid]))
    (.cons child .nil)

def deriveAppendNil (right : Pattern)
    (rightValid : argumentValidAt 0 right = true) :
    Derivation validated (appendJ nil right right) := by
  let ruleInstance : RuleInstance := {
    ruleId := appendNil.id
    arguments := [right]
  }
  exact .byRule ruleInstance (premises := [])
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? appendNil.id = some appendNil :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, appendNil, schema, ys, appendJ, nil, a,
        argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
        instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
        lookupArgumentAt?, rightValid]))
    .nil

def deriveAppendCons (head left right result : Pattern)
    (headValid : argumentValidAt 0 head = true)
    (leftValid : argumentValidAt 0 left = true)
    (rightValid : argumentValidAt 0 right = true)
    (resultValid : argumentValidAt 0 result = true)
    (child : Derivation validated (appendJ left right result)) :
    Derivation validated (appendJ (cons head left) right (cons head result)) := by
  let ruleInstance : RuleInstance := {
    ruleId := appendCons.id
    arguments := [head, left, right, result]
  }
  exact .byRule ruleInstance
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? appendCons.id = some appendCons :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, appendCons, schema, h, xs, ys, zs, appendJ,
        cons, a, argumentsValidAt, RuleSchema.sideConditionsHold,
        instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
        instantiateSchemaAt?, lookupArgumentAt?, headValid, leftValid,
        rightValid, resultValid]))
    (.cons child .nil)

def deriveLiteralsNil : Derivation validated (literalsJ nil) := by
  let ruleInstance : RuleInstance := {
    ruleId := literalsNil.id
    arguments := []
  }
  exact .byRule ruleInstance (premises := [])
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? literalsNil.id = some literalsNil :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, literalsNil, schema, literalsJ, nil, a,
        argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
        instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?]))
    .nil

def deriveLiteralsPositive (pivot rest : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (restValid : argumentValidAt 0 rest = true)
    (child : Derivation validated (literalsJ rest)) :
    Derivation validated (literalsJ (cons (positive pivot) rest)) := by
  let ruleInstance : RuleInstance := {
    ruleId := literalsPositive.id
    arguments := [pivot, rest]
  }
  exact .byRule ruleInstance
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? literalsPositive.id =
          some literalsPositive :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, literalsPositive, schema, p, xs, literalsJ, cons,
        positive, a, argumentsValidAt, RuleSchema.sideConditionsHold,
        instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
        instantiateSchemaAt?, lookupArgumentAt?, pivotValid, restValid]))
    (.cons child .nil)

def deriveLiteralsNegative (pivot rest : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (restValid : argumentValidAt 0 rest = true)
    (child : Derivation validated (literalsJ rest)) :
    Derivation validated (literalsJ (cons (negative pivot) rest)) := by
  let ruleInstance : RuleInstance := {
    ruleId := literalsNegative.id
    arguments := [pivot, rest]
  }
  exact .byRule ruleInstance
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? literalsNegative.id =
          some literalsNegative :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, literalsNegative, schema, p, xs, literalsJ, cons,
        negative, a, argumentsValidAt, RuleSchema.sideConditionsHold,
        instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
        instantiateSchemaAt?, lookupArgumentAt?, pivotValid, restValid]))
    (.cons child .nil)

def deriveResolvePositiveLeft
    (pivot left right leftRest rightRest result : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (leftValid : argumentValidAt 0 left = true)
    (rightValid : argumentValidAt 0 right = true)
    (leftRestValid : argumentValidAt 0 leftRest = true)
    (rightRestValid : argumentValidAt 0 rightRest = true)
    (resultValid : argumentValidAt 0 result = true)
    (removeLeft : Derivation validated (removePositiveJ pivot left leftRest))
    (removeRight : Derivation validated (removeNegativeJ pivot right rightRest))
    (append : Derivation validated (appendJ leftRest rightRest result))
    (leftLiterals : Derivation validated (literalsJ left))
    (rightLiterals : Derivation validated (literalsJ right))
    (resultLiterals : Derivation validated (literalsJ result)) :
    Derivation validated (resolveJ positiveLeft pivot left right result) := by
  let ruleInstance : RuleInstance := {
    ruleId := resolvePositiveLeft.id
    arguments := [pivot, left, right, leftRest, rightRest, result]
  }
  exact .byRule ruleInstance
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? resolvePositiveLeft.id =
          some resolvePositiveLeft :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, resolvePositiveLeft, schema, p,
        TptpGroundResolutionCalculus.left,
        TptpGroundResolutionCalculus.right,
        TptpGroundResolutionCalculus.leftRest,
        TptpGroundResolutionCalculus.rightRest,
        TptpGroundResolutionCalculus.result,
        removePositiveJ, removeNegativeJ,
        appendJ, literalsJ, resolveJ, positiveLeft, a, argumentsValidAt,
        RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        pivotValid, leftValid, rightValid, leftRestValid, rightRestValid,
        resultValid]))
    (.cons removeLeft (.cons removeRight (.cons append
      (.cons leftLiterals (.cons rightLiterals (.cons resultLiterals .nil))))))

def deriveResolvePositiveRight
    (pivot left right leftRest rightRest result : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (leftValid : argumentValidAt 0 left = true)
    (rightValid : argumentValidAt 0 right = true)
    (leftRestValid : argumentValidAt 0 leftRest = true)
    (rightRestValid : argumentValidAt 0 rightRest = true)
    (resultValid : argumentValidAt 0 result = true)
    (removeLeft : Derivation validated (removeNegativeJ pivot left leftRest))
    (removeRight : Derivation validated (removePositiveJ pivot right rightRest))
    (append : Derivation validated (appendJ leftRest rightRest result))
    (leftLiterals : Derivation validated (literalsJ left))
    (rightLiterals : Derivation validated (literalsJ right))
    (resultLiterals : Derivation validated (literalsJ result)) :
    Derivation validated (resolveJ positiveRight pivot left right result) := by
  let ruleInstance : RuleInstance := {
    ruleId := resolvePositiveRight.id
    arguments := [pivot, left, right, leftRest, rightRest, result]
  }
  exact .byRule ruleInstance
    (instantiateRule?_eq_some_iff_application.mp (by
      have lookup : validated.1.lookupRule? resolvePositiveRight.id =
          some resolvePositiveRight :=
        lookupRule?_eq_some_of_mem validated (by
          simp [validated, definition])
      rw [instantiateRule?, lookup]
      simp [ruleInstance, resolvePositiveRight, schema, p,
        TptpGroundResolutionCalculus.left,
        TptpGroundResolutionCalculus.right,
        TptpGroundResolutionCalculus.leftRest,
        TptpGroundResolutionCalculus.rightRest,
        TptpGroundResolutionCalculus.result,
        removePositiveJ, removeNegativeJ,
        appendJ, literalsJ, resolveJ, positiveRight, a, argumentsValidAt,
        RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
        instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?,
        pivotValid, leftValid, rightValid, leftRestValid, rightRestValid,
        resultValid]))
    (.cons removeLeft (.cons removeRight (.cons append
      (.cons leftLiterals (.cons rightLiterals (.cons resultLiterals .nil))))))

/-! ## Independent relational meaning -/

/-- Ground clause-list well-formedness is explicit evidence.  The generic
inference checker intentionally leaves metavariable payloads unclassified,
so a resolution rule must not obtain list well-formedness merely by having a
`Literals` type declaration nearby. -/
inductive LiteralsWF : Pattern → Prop where
  | nil : LiteralsWF nil
  | positive {atom rest} : LiteralsWF rest →
      LiteralsWF (cons (positive atom) rest)
  | negative {atom rest} : LiteralsWF rest →
      LiteralsWF (cons (negative atom) rest)

/-- Delete one selected positive occurrence, retaining authored order. -/
inductive RemovePositive (pivot : Pattern) : Pattern → Pattern → Prop where
  | head (rest) : RemovePositive pivot (cons (positive pivot) rest) rest
  | tail {head source result} : RemovePositive pivot source result →
      RemovePositive pivot (cons head source) (cons head result)

/-- Delete one selected negative occurrence, retaining authored order. -/
inductive RemoveNegative (pivot : Pattern) : Pattern → Pattern → Prop where
  | head (rest) : RemoveNegative pivot (cons (negative pivot) rest) rest
  | tail {head source result} : RemoveNegative pivot source result →
      RemoveNegative pivot (cons head source) (cons head result)

/-- Ordered append over the authored clause-list constructors. -/
inductive Append : Pattern → Pattern → Pattern → Prop where
  | nil (right) : Append nil right right
  | cons {head left right result} : Append left right result →
      Append (cons head left) right (cons head result)

/-- Binary ground resolution, with the selected pivot orientation retained
as proof-relevant data. -/
inductive Resolve : Pattern → Pattern → Pattern → Pattern → Pattern → Prop where
  | positiveLeft {pivot left right leftRest rightRest result} :
      RemovePositive pivot left leftRest →
      RemoveNegative pivot right rightRest →
      Append leftRest rightRest result →
      LiteralsWF left → LiteralsWF right → LiteralsWF result →
      Resolve positiveLeft pivot left right result
  | positiveRight {pivot left right leftRest rightRest result} :
      RemoveNegative pivot left leftRest →
      RemovePositive pivot right rightRest →
      Append leftRest rightRest result →
      LiteralsWF left → LiteralsWF right → LiteralsWF result →
      Resolve positiveRight pivot left right result

/-- The non-vacuous semantic fibre of every declared judgment. -/
def JudgmentMeaning : Pattern → Prop
  | .apply "GroundRemovePositive" [pivot, source, result] =>
      RemovePositive pivot source result
  | .apply "GroundRemoveNegative" [pivot, source, result] =>
      RemoveNegative pivot source result
  | .apply "GroundAppend" [left, right, result] => Append left right result
  | .apply "GroundLiterals" [value] => LiteralsWF value
  | .apply "GroundResolve" [orientation, pivot, left, right, result] =>
      Resolve orientation pivot left right result
  | _ => False

private theorem argumentsValidAt_two_shape
    {firstName secondName : String} {arguments : List Pattern}
    (valid : argumentsValidAt [(firstName, 0), (secondName, 0)] arguments = true) :
    ∃ first second, arguments = [first, second] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => exact ⟨first, second, rfl⟩
          | cons third rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_four_shape
    {firstName secondName thirdName fourthName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0)]
      arguments = true) :
    ∃ first second third fourth,
      arguments = [first, second, third, fourth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => exact ⟨first, second, third, fourth, rfl⟩
                  | cons fifth rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_zero_shape {arguments : List Pattern}
    (valid : argumentsValidAt [] arguments = true) : arguments = [] := by
  cases arguments with
  | nil => rfl
  | cons first rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_one_shape
    {name : String} {arguments : List Pattern}
    (valid : argumentsValidAt [(name, 0)] arguments = true) :
    ∃ first, arguments = [first] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_six_shape
    {firstName secondName thirdName fourthName fifthName sixthName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0),
       (fifthName, 0), (sixthName, 0)] arguments = true) :
    ∃ first second third fourth fifth sixth,
      arguments = [first, second, third, fourth, fifth, sixth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => simp [argumentsValidAt] at valid
                  | cons fifth rest =>
                      cases rest with
                      | nil => simp [argumentsValidAt] at valid
                      | cons sixth rest =>
                          cases rest with
                          | nil =>
                              exact ⟨first, second, third, fourth, fifth,
                                sixth, rfl⟩
                          | cons seventh rest =>
                              simp [argumentsValidAt] at valid

private theorem removePositiveHead_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId =
      some removePositiveHead) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = removePositiveHead := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨pivot, rest, argumentsEq⟩ :=
      argumentsValidAt_two_shape (by
        simpa [removePositiveHead, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup,
      removePositiveHead, schema, a, p, xs,
      removePositiveJ, positive, cons,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact RemovePositive.head rest

private theorem removePositiveTail_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId =
      some removePositiveTail)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = removePositiveTail := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨pivot, head, source, result, argumentsEq⟩ :=
      argumentsValidAt_four_shape (by
        simpa [removePositiveTail, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup,
      removePositiveTail, schema, a, p, h, xs, ys,
      removePositiveJ, cons,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply RemovePositive.tail
    have premiseMember : removePositiveJ pivot source result ∈ premises := by
      rw [← premisesEq]
      simp [removePositiveJ, a]
    have premiseMeaning := premiseSound (removePositiveJ pivot source result)
      premiseMember
    simpa [JudgmentMeaning, removePositiveJ, a] using premiseMeaning

private theorem removeNegativeHead_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId =
      some removeNegativeHead) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = removeNegativeHead := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨pivot, rest, argumentsEq⟩ :=
      argumentsValidAt_two_shape (by
        simpa [removeNegativeHead, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup,
      removeNegativeHead, schema, a, p, xs,
      removeNegativeJ, negative, cons,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, _, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact RemoveNegative.head rest

private theorem removeNegativeTail_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId =
      some removeNegativeTail)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = removeNegativeTail := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨pivot, head, source, result, argumentsEq⟩ :=
      argumentsValidAt_four_shape (by
        simpa [removeNegativeTail, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup,
      removeNegativeTail, schema, a, p, h, xs, ys,
      removeNegativeJ, cons,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply RemoveNegative.tail
    have premiseMember : removeNegativeJ pivot source result ∈ premises := by
      rw [← premisesEq]
      simp [removeNegativeJ, a]
    have premiseMeaning := premiseSound (removeNegativeJ pivot source result)
      premiseMember
    simpa [JudgmentMeaning, removeNegativeJ, a] using premiseMeaning

private theorem appendNil_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId = some appendNil) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = appendNil := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨right, argumentsEq⟩ := argumentsValidAt_one_shape (by
      simpa [appendNil, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, appendNil, schema, a, ys, appendJ, nil,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, _, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact Append.nil right

private theorem appendCons_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId = some appendCons)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = appendCons := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨head, left, right, result, argumentsEq⟩ :=
      argumentsValidAt_four_shape (by
        simpa [appendCons, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, appendCons, schema, a, h, xs, ys, zs,
      appendJ, cons,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Append.cons
    have premiseMember : appendJ left right result ∈ premises := by
      rw [← premisesEq]
      simp [appendJ, a]
    have premiseMeaning := premiseSound (appendJ left right result) premiseMember
    simpa [JudgmentMeaning, appendJ, a] using premiseMeaning

private theorem literalsNil_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId = some literalsNil) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = literalsNil := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    have argumentsEq : ruleInstance.arguments = [] :=
      argumentsValidAt_zero_shape (by
        simpa [literalsNil, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, literalsNil, schema, a, literalsJ, nil,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?]
      at executable
    rcases executable with ⟨_, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact LiteralsWF.nil

private theorem literalsPositive_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId = some literalsPositive)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = literalsPositive := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨atom, rest, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [literalsPositive, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, literalsPositive, schema, a, p, xs,
      literalsJ, positive, cons,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply LiteralsWF.positive
    have premiseMember : literalsJ rest ∈ premises := by
      rw [← premisesEq]
      simp [literalsJ, a]
    have premiseMeaning := premiseSound (literalsJ rest) premiseMember
    simpa [JudgmentMeaning, literalsJ, a] using premiseMeaning

private theorem literalsNegative_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId = some literalsNegative)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = literalsNegative := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨atom, rest, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [literalsNegative, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, literalsNegative, schema, a, p, xs,
      literalsJ, negative, cons,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply LiteralsWF.negative
    have premiseMember : literalsJ rest ∈ premises := by
      rw [← premisesEq]
      simp [literalsJ, a]
    have premiseMeaning := premiseSound (literalsJ rest) premiseMember
    simpa [JudgmentMeaning, literalsJ, a] using premiseMeaning

private theorem resolvePositiveLeft_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId =
      some resolvePositiveLeft)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = resolvePositiveLeft := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨pivot, leftValue, rightValue, leftResult, rightResult,
        resultValue, argumentsEq⟩ := argumentsValidAt_six_shape (by
      simpa [resolvePositiveLeft, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, resolvePositiveLeft, schema, a, p, left, right,
      leftRest, rightRest, result,
      removePositiveJ, removeNegativeJ, appendJ, literalsJ, resolveJ,
      positiveLeft,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Resolve.positiveLeft
    · have member : removePositiveJ pivot leftValue leftResult ∈ premises := by
        rw [← premisesEq]
        simp [removePositiveJ, a]
      simpa [JudgmentMeaning, removePositiveJ, a] using
        premiseSound _ member
    · have member : removeNegativeJ pivot rightValue rightResult ∈ premises := by
        rw [← premisesEq]
        simp [removeNegativeJ, a]
      simpa [JudgmentMeaning, removeNegativeJ, a] using
        premiseSound _ member
    · have member : appendJ leftResult rightResult resultValue ∈ premises := by
        rw [← premisesEq]
        simp [appendJ, a]
      simpa [JudgmentMeaning, appendJ, a] using premiseSound _ member
    · have member : literalsJ leftValue ∈ premises := by
        rw [← premisesEq]
        simp [literalsJ, a]
      simpa [JudgmentMeaning, literalsJ, a] using premiseSound _ member
    · have member : literalsJ rightValue ∈ premises := by
        rw [← premisesEq]
        simp [literalsJ, a]
      simpa [JudgmentMeaning, literalsJ, a] using premiseSound _ member
    · have member : literalsJ resultValue ∈ premises := by
        rw [← premisesEq]
        simp [literalsJ, a]
      simpa [JudgmentMeaning, literalsJ, a] using premiseSound _ member

private theorem resolvePositiveRight_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (lookup : validated.1.lookupRule? ruleInstance.ruleId =
      some resolvePositiveRight)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = resolvePositiveRight := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨pivot, leftValue, rightValue, leftResult, rightResult,
        resultValue, argumentsEq⟩ := argumentsValidAt_six_shape (by
      simpa [resolvePositiveRight, schema] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, resolvePositiveRight, schema, a, p, left, right,
      leftRest, rightRest, result,
      removePositiveJ, removeNegativeJ, appendJ, literalsJ, resolveJ,
      positiveRight,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Resolve.positiveRight
    · have member : removeNegativeJ pivot leftValue leftResult ∈ premises := by
        rw [← premisesEq]
        simp [removeNegativeJ, a]
      simpa [JudgmentMeaning, removeNegativeJ, a] using
        premiseSound _ member
    · have member : removePositiveJ pivot rightValue rightResult ∈ premises := by
        rw [← premisesEq]
        simp [removePositiveJ, a]
      simpa [JudgmentMeaning, removePositiveJ, a] using
        premiseSound _ member
    · have member : appendJ leftResult rightResult resultValue ∈ premises := by
        rw [← premisesEq]
        simp [appendJ, a]
      simpa [JudgmentMeaning, appendJ, a] using premiseSound _ member
    · have member : literalsJ leftValue ∈ premises := by
        rw [← premisesEq]
        simp [literalsJ, a]
      simpa [JudgmentMeaning, literalsJ, a] using premiseSound _ member
    · have member : literalsJ rightValue ∈ premises := by
        rw [← premisesEq]
        simp [literalsJ, a]
      simpa [JudgmentMeaning, literalsJ, a] using premiseSound _ member
    · have member : literalsJ resultValue ∈ premises := by
        rw [← premisesEq]
        simp [literalsJ, a]
      simpa [JudgmentMeaning, literalsJ, a] using premiseSound _ member

/-- Every application admitted by the generic checker has the independently
stated meaning of its authored rule.  This is the semantic boundary between
finite-Horn replay and ground resolution; it does not trust rule labels. -/
theorem ruleApplication_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  cases application with
  | intro rule lookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have application' :
        RuleApplication validated ruleInstance premises conclusion :=
      .intro rule lookup argumentsValid sideConditionsValid
        premisesInstantiate conclusionInstantiates
    have ruleCases :
        rule = removePositiveHead ∨ rule = removePositiveTail ∨
        rule = removeNegativeHead ∨ rule = removeNegativeTail ∨
        rule = appendNil ∨ rule = appendCons ∨ rule = literalsNil ∨
        rule = literalsPositive ∨ rule = literalsNegative ∨
        rule = resolvePositiveLeft ∨ rule = resolvePositiveRight := by
      have found := lookup
      simp only [validated, definition, CalculusLanguageDef.lookupRule?] at found
      aesop
    rcases ruleCases with ruleEq | ruleEq | ruleEq | ruleEq | ruleEq |
        ruleEq | ruleEq | ruleEq | ruleEq | ruleEq | ruleEq
    · subst rule
      exact removePositiveHead_application_sound ruleInstance premises
        conclusion application' lookup
    · subst rule
      exact removePositiveTail_application_sound ruleInstance premises
        conclusion application' lookup premiseSound
    · subst rule
      exact removeNegativeHead_application_sound ruleInstance premises
        conclusion application' lookup
    · subst rule
      exact removeNegativeTail_application_sound ruleInstance premises
        conclusion application' lookup premiseSound
    · subst rule
      exact appendNil_application_sound ruleInstance premises conclusion
        application' lookup
    · subst rule
      exact appendCons_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · subst rule
      exact literalsNil_application_sound ruleInstance premises conclusion
        application' lookup
    · subst rule
      exact literalsPositive_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · subst rule
      exact literalsNegative_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · subst rule
      exact resolvePositiveLeft_application_sound ruleInstance premises
        conclusion application' lookup premiseSound
    · subst rule
      exact resolvePositiveRight_application_sound ruleInstance premises
        conclusion application' lookup premiseSound

/-- Any derivation accepted by the generic checker has the relational meaning
of its final judgment. -/
theorem derivation_sound {goal : Pattern}
    (derivation : Derivation validated goal) : JudgmentMeaning goal :=
  derivation.sound_of_ruleApplications JudgmentMeaning ruleApplication_sound

/-! ## Boolean-model soundness -/

/-- Truth of one encoded literal.  Atoms remain arbitrary ground patterns;
the calculus never inspects their internal syntax. -/
def LiteralHolds (valuation : Pattern → Bool) : Pattern → Prop
  | .apply "ground-resolution:positive" [atom] => valuation atom = true
  | .apply "ground-resolution:negative" [atom] => valuation atom = false
  | _ => False

/-- Disjunctive truth of one encoded clause list. -/
def ClauseHolds (valuation : Pattern → Bool) : Pattern → Prop
  | .apply "ground-resolution:nil" [] => False
  | .apply "ground-resolution:cons" [head, tail] =>
      LiteralHolds valuation head ∨ ClauseHolds valuation tail
  | _ => False

private theorem removePositive_preserves_when_pivot_false
    {valuation : Pattern → Bool} {pivot source result : Pattern}
    (removed : RemovePositive pivot source result)
    (pivotFalse : valuation pivot = false)
    (sourceHolds : ClauseHolds valuation source) :
    ClauseHolds valuation result := by
  induction removed with
  | head rest =>
      simpa [ClauseHolds, LiteralHolds, cons, positive, a, pivotFalse]
        using sourceHolds
  | tail removed inductionHypothesis =>
      rcases sourceHolds with headHolds | tailHolds
      · exact Or.inl headHolds
      · exact Or.inr (inductionHypothesis tailHolds)

private theorem removeNegative_preserves_when_pivot_true
    {valuation : Pattern → Bool} {pivot source result : Pattern}
    (removed : RemoveNegative pivot source result)
    (pivotTrue : valuation pivot = true)
    (sourceHolds : ClauseHolds valuation source) :
    ClauseHolds valuation result := by
  induction removed with
  | head rest =>
      simpa [ClauseHolds, LiteralHolds, cons, negative, a, pivotTrue]
        using sourceHolds
  | tail removed inductionHypothesis =>
      rcases sourceHolds with headHolds | tailHolds
      · exact Or.inl headHolds
      · exact Or.inr (inductionHypothesis tailHolds)

private theorem append_clauseHolds_iff
    {valuation : Pattern → Bool} {left right result : Pattern}
    (appended : Append left right result) :
    ClauseHolds valuation result ↔
      ClauseHolds valuation left ∨ ClauseHolds valuation right := by
  induction appended with
  | nil right => simp [ClauseHolds, nil, a]
  | cons appended inductionHypothesis =>
      simp only [cons, a, ClauseHolds, inductionHypothesis]
      tauto

/-- Each authored ground-resolution judgment preserves Boolean-model truth
of the parent clauses. -/
theorem resolve_sound
    {orientation pivot left right result : Pattern}
    (resolved : Resolve orientation pivot left right result) :
    ∀ valuation,
      ClauseHolds valuation left → ClauseHolds valuation right →
      ClauseHolds valuation result := by
  intro valuation leftHolds rightHolds
  cases resolved with
  | positiveLeft removePositive removeNegative appended =>
      cases pivotValue : valuation pivot with
      | false =>
          have leftRestHolds :=
            removePositive_preserves_when_pivot_false
              removePositive pivotValue leftHolds
          exact (append_clauseHolds_iff appended).2 (Or.inl leftRestHolds)
      | true =>
          have rightRestHolds :=
            removeNegative_preserves_when_pivot_true
              removeNegative pivotValue rightHolds
          exact (append_clauseHolds_iff appended).2 (Or.inr rightRestHolds)
  | positiveRight removeNegative removePositive appended =>
      cases pivotValue : valuation pivot with
      | false =>
          have rightRestHolds :=
            removePositive_preserves_when_pivot_false
              removePositive pivotValue rightHolds
          exact (append_clauseHolds_iff appended).2 (Or.inr rightRestHolds)
      | true =>
          have leftRestHolds :=
            removeNegative_preserves_when_pivot_true
              removeNegative pivotValue leftHolds
          exact (append_clauseHolds_iff appended).2 (Or.inl leftRestHolds)

/-- Decode the authored list representation into the independent ground-CNF
semantic carrier.  Malformed lists fail rather than receiving a meaning. -/
def decodeLiterals : Pattern →
    Option (Mettapedia.Languages.TPTP.GroundCNFAuthority.Clause Pattern)
  | .apply "ground-resolution:nil" [] => some []
  | .apply "ground-resolution:cons"
      [.apply "ground-resolution:positive" [atom], rest] =>
      (decodeLiterals rest).map fun literals =>
        .positive atom :: literals
  | .apply "ground-resolution:cons"
      [.apply "ground-resolution:negative" [atom], rest] =>
      (decodeLiterals rest).map fun literals =>
        .negative atom :: literals
  | _ => none

theorem decodeLiterals_exists_of_wf {value : Pattern}
    (wellFormed : LiteralsWF value) :
    ∃ literals, decodeLiterals value = some literals := by
  induction wellFormed with
  | nil => exact ⟨[], rfl⟩
  | @positive atom rest restWellFormed inductionHypothesis =>
      obtain ⟨literals, decoded⟩ := inductionHypothesis
      exact ⟨.positive atom :: literals,
        by simp [decodeLiterals, cons, positive, a, decoded]⟩
  | @negative atom rest restWellFormed inductionHypothesis =>
      obtain ⟨literals, decoded⟩ := inductionHypothesis
      exact ⟨.negative atom :: literals,
        by simp [decodeLiterals, cons, negative, a, decoded]⟩

theorem clauseHolds_iff_formulaSatisfies_of_decode
    {valuation : Pattern → Bool} {value : Pattern}
    {literals : Mettapedia.Languages.TPTP.GroundCNFAuthority.Clause Pattern}
    (wellFormed : LiteralsWF value)
    (decoded : decodeLiterals value = some literals) :
    ClauseHolds valuation value ↔
      Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.Satisfies
        valuation (.clause literals) := by
  induction wellFormed generalizing literals with
  | nil =>
      simp [decodeLiterals, nil, a] at decoded
      subst literals
      simp [ClauseHolds, nil, a,
        Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.Satisfies]
  | @positive atom rest restWellFormed inductionHypothesis =>
      simp only [cons, positive, a, decodeLiterals] at decoded
      cases restDecoded : decodeLiterals rest with
      | none => simp [restDecoded] at decoded
      | some restLiterals =>
          have literalsEq :
              Mettapedia.Languages.TPTP.GroundCNFAuthority.Literal.positive atom ::
                restLiterals = literals := by
            simpa [restDecoded] using decoded
          subst literals
          simp only [cons, positive, a, ClauseHolds]
          rw [inductionHypothesis restDecoded]
          simp [LiteralHolds,
            Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.Satisfies,
            Mettapedia.Languages.TPTP.GroundCNFAuthority.Literal.Holds]
  | @negative atom rest restWellFormed inductionHypothesis =>
      simp only [cons, negative, a, decodeLiterals] at decoded
      cases restDecoded : decodeLiterals rest with
      | none => simp [restDecoded] at decoded
      | some restLiterals =>
          have literalsEq :
              Mettapedia.Languages.TPTP.GroundCNFAuthority.Literal.negative atom ::
                restLiterals = literals := by
            simpa [restDecoded] using decoded
          subst literals
          simp only [cons, negative, a, ClauseHolds]
          rw [inductionHypothesis restDecoded]
          simp [LiteralHolds,
            Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.Satisfies,
            Mettapedia.Languages.TPTP.GroundCNFAuthority.Literal.Holds]

/-- A decoded authored resolution step is a theorem relation in the
independent ground-CNF model semantics. -/
theorem resolve_decoded_theoremRelation
    {orientation pivot left right result : Pattern}
    {leftClause rightClause resultClause :
      Mettapedia.Languages.TPTP.GroundCNFAuthority.Clause Pattern}
    (resolved : Resolve orientation pivot left right result)
    (leftDecoded : decodeLiterals left = some leftClause)
    (rightDecoded : decodeLiterals right = some rightClause)
    (resultDecoded : decodeLiterals result = some resultClause) :
    (Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.semantics
      (Atom := Pattern)).TheoremRelation
      { parents := [.clause leftClause, .clause rightClause]
        inferred := .clause resultClause } := by
  intro valuation parentsSatisfied
  have leftWellFormed : LiteralsWF left := by
    cases resolved <;> assumption
  have rightWellFormed : LiteralsWF right := by
    cases resolved <;> assumption
  have resultWellFormed : LiteralsWF result := by
    cases resolved <;> assumption
  have leftHolds : ClauseHolds valuation left :=
    (clauseHolds_iff_formulaSatisfies_of_decode
      leftWellFormed leftDecoded).2
      (parentsSatisfied (.clause leftClause) (by simp))
  have rightHolds : ClauseHolds valuation right :=
    (clauseHolds_iff_formulaSatisfies_of_decode
      rightWellFormed rightDecoded).2
      (parentsSatisfied (.clause rightClause) (by simp))
  exact (clauseHolds_iff_formulaSatisfies_of_decode
    resultWellFormed resultDecoded).1
    (resolve_sound resolved valuation leftHolds rightHolds)

/-! ## Single-pass CertificateGSLT authority -/

abbrev SemanticClause :=
  Mettapedia.Languages.TPTP.GroundCNFAuthority.Clause Pattern

/-- A semantic resolution claim retains both the authored representation and
its independently decoded ground-CNF clauses. -/
structure DecodedResolutionClaim where
  orientation : Pattern
  pivot : Pattern
  left : Pattern
  right : Pattern
  result : Pattern
  leftClause : SemanticClause
  rightClause : SemanticClause
  resultClause : SemanticClause
  leftDecoded : decodeLiterals left = some leftClause
  rightDecoded : decodeLiterals right = some rightClause
  resultDecoded : decodeLiterals result = some resultClause

def DecodedResolutionClaim.Meaning (claim : DecodedResolutionClaim) : Prop :=
  (Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.semantics
    (Atom := Pattern)).TheoremRelation
    { parents := [.clause claim.leftClause, .clause claim.rightClause]
      inferred := .clause claim.resultClause }

def DecodedResolutionClaim.encode (claim : DecodedResolutionClaim) : Pattern :=
  resolveJ claim.orientation claim.pivot claim.left claim.right claim.result

/-- The generic one-pass article checker is adequate for the independently
stated model-theoretic meaning of decoded ground resolution. -/
def decodedResolutionAdequacy :
    JudgmentEncodingAdequacy DecodedResolutionClaim
      DecodedResolutionClaim.Meaning validated where
  encode := DecodedResolutionClaim.encode
  derivation_sound := by
    intro claim derivation
    obtain ⟨checked⟩ := derivation
    have meaning := derivation_sound checked
    have resolved : Resolve claim.orientation claim.pivot claim.left
        claim.right claim.result := by
      simpa [DecodedResolutionClaim.encode, resolveJ, a, JudgmentMeaning]
        using meaning
    exact resolve_decoded_theoremRelation resolved claim.leftDecoded
      claim.rightDecoded claim.resultDecoded

def authorityId : String := "tptp-ground-resolution-v1"

def semanticAuthority :=
  judgmentWireAuthority authorityId decodedResolutionAdequacy

/-- Acceptance of one versioned wire article implies the semantic theorem
relation.  The authority performs structural checking once; it does not run
proof search. -/
theorem accepted_article_sound (claim : DecodedResolutionClaim)
    (article : WireArticle)
    (accepted : semanticAuthority.check claim article = true) :
    claim.Meaning :=
  semanticAuthority.sound accepted

/-! ## Executable positive and negative controls -/

namespace Canary

def atomP : Pattern := .apply "p" []
def atomQ : Pattern := .apply "q" []

def positiveP : Pattern := cons (positive atomP) nil
def negativeP : Pattern := cons (negative atomP) nil
def empty : Pattern := nil

private def node (id : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ⟨id⟩, arguments := arguments } children

def literalsNilProof : RawProof :=
  node "ground-resolution:literals-nil" []

def literalsPositivePProof : RawProof :=
  node "ground-resolution:literals-positive" [atomP, nil]
    [literalsNilProof]

def literalsNegativePProof : RawProof :=
  node "ground-resolution:literals-negative" [atomP, nil]
    [literalsNilProof]

def refutationProof : RawProof :=
  node "ground-resolution:resolve-positive-left"
    [atomP, positiveP, negativeP, nil, nil, nil]
    [node "ground-resolution:remove-positive-head" [atomP, nil],
     node "ground-resolution:remove-negative-head" [atomP, nil],
     node "ground-resolution:append-nil" [nil],
     literalsPositivePProof,
     literalsNegativePProof,
     literalsNilProof]

def refutationGoal : Pattern :=
  resolveJ positiveLeft atomP positiveP negativeP empty

theorem refutation_accepted :
    checkRaw validated refutationGoal refutationProof = true := by
  decide +kernel

theorem refutation_has_relational_meaning : JudgmentMeaning refutationGoal := by
  obtain ⟨derivation⟩ := checkRaw_soundness refutation_accepted
  exact derivation_sound derivation

theorem refutation_is_decoded_theoremRelation :
    (Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.semantics
      (Atom := Pattern)).TheoremRelation
      { parents :=
          [.clause [.positive atomP], .clause [.negative atomP]]
        inferred := .clause [] } := by
  have resolved : Resolve positiveLeft atomP positiveP negativeP empty := by
    simpa [refutationGoal, resolveJ, positiveLeft, a, JudgmentMeaning]
      using refutation_has_relational_meaning
  apply resolve_decoded_theoremRelation resolved
  · rfl
  · rfl
  · simp [empty, nil, a, decodeLiterals]

def refutationClaim : DecodedResolutionClaim where
  orientation := positiveLeft
  pivot := atomP
  left := positiveP
  right := negativeP
  result := empty
  leftClause := [.positive atomP]
  rightClause := [.negative atomP]
  resultClause := []
  leftDecoded := rfl
  rightDecoded := rfl
  resultDecoded := rfl

theorem refutation_has_accepted_wire_article :
    ∃ article : WireArticle,
      semanticAuthority.check refutationClaim article = true := by
  obtain ⟨derivation⟩ := checkRaw_soundness refutation_accepted
  refine ⟨articleOfDerivation derivation, ?_⟩
  exact wireArticleAuthority_complete authorityId derivation

def wrongPivotProof : RawProof :=
  node "ground-resolution:resolve-positive-left"
    [atomQ, positiveP, negativeP, nil, nil, nil]
    [node "ground-resolution:remove-positive-head" [atomP, nil],
     node "ground-resolution:remove-negative-head" [atomP, nil],
     node "ground-resolution:append-nil" [nil],
     literalsPositivePProof,
     literalsNegativePProof,
     literalsNilProof]

theorem wrong_pivot_rejected :
    checkRaw validated refutationGoal wrongPivotProof = false := by
  decide +kernel

def missingPremiseProof : RawProof :=
  node "ground-resolution:resolve-positive-left"
    [atomP, positiveP, negativeP, nil, nil, nil]
    [node "ground-resolution:remove-positive-head" [atomP, nil],
     node "ground-resolution:remove-negative-head" [atomP, nil],
     node "ground-resolution:append-nil" [nil],
     literalsPositivePProof,
     literalsNegativePProof]

theorem missing_premise_rejected :
    checkRaw validated refutationGoal missingPremiseProof = false := by
  decide +kernel

def inventedResultGoal : Pattern :=
  resolveJ positiveLeft atomP positiveP negativeP positiveP

theorem invented_result_rejected :
    checkRaw validated inventedResultGoal refutationProof = false := by
  decide +kernel

end Canary

#print axioms definition_admitted
#print axioms finiteHornSource_isSome
#print axioms finiteHornSource_nonempty
#print axioms ruleApplication_sound
#print axioms derivation_sound
#print axioms resolve_sound
#print axioms resolve_decoded_theoremRelation
#print axioms accepted_article_sound
#print axioms Canary.refutation_accepted
#print axioms Canary.refutation_is_decoded_theoremRelation
#print axioms Canary.refutation_has_accepted_wire_article
#print axioms Canary.wrong_pivot_rejected
#print axioms Canary.missing_premise_rejected
#print axioms Canary.invented_result_rejected

end Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCalculus
