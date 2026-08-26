import Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
import Mettapedia.GSLT.LanguageDef.C1DigitMachine

/-!
# Presentation-sensitive Walters--Zantema DA to C1 compilation

This module inspects a supplied finite DA `LanguageDef`, extracts its rule
families structurally, and derives finite C1 tables and instruction graphs.
Rule names are retained only as provenance.  Digit/carry behavior is read from
the supplied left- and right-hand sides.
-/

namespace Mettapedia.GSLT.LanguageDef.WaltersZantemaDAToC1

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
open Mettapedia.GSLT.LanguageDef.C1DigitMachine

structure Origin where
  index : Nat
  name : String
deriving Repr, DecidableEq

def Origin.render (origin : Origin) : String :=
  s!"{origin.index}:{origin.name}"

structure Vocabulary where
  radix : Nat
  digitLabels : List String
  starLabels : List String
deriving Repr, DecidableEq

structure AddEntry where
  first : Nat
  second : Nat
  output : Nat
  carry : Bool
  origin : Origin
deriving Repr, DecidableEq

structure SuccEntry where
  input : Nat
  output : Nat
  carry : Bool
  origin : Origin
deriving Repr, DecidableEq

structure DigitEntry where
  digit : Nat
  origin : Origin
deriving Repr, DecidableEq

structure ProductEntry where
  first : Nat
  second : Nat
  productDigits : List Nat
  origin : Origin
deriving Repr, DecidableEq

structure Profile where
  vocabulary : Vocabulary
  rule1 : Origin
  rule2 : Origin
  rule3 : Origin
  additions : List AddEntry
  rule5 : Origin
  multiplications : List DigitEntry
  rule7 : Origin
  successors : List SuccEntry
  starZeros : List DigitEntry
  products : List ProductEntry
deriving Repr, DecidableEq

private def ensure (condition : Bool) : Option Unit :=
  if condition then some () else none

private def exactlyOne? : List alpha -> Option alpha
  | [value] => some value
  | _ => none

private def origin (index : Nat) (rule : RewriteRule) : Origin :=
  ⟨index, rule.name⟩

private def ruleEntries (language : LanguageDef) : List (Nat × RewriteRule) :=
  language.rewrites.zipIdx.map fun entry => (entry.2, entry.1)

private def isNatParameter : TermParam -> Bool
  | .simple _ (.base "Nat") => true
  | _ => false

private def grammarShape (label : String) (arity : Nat)
    (policy : Option TermEvalPolicy) (rule : GrammarRule) : Bool :=
  rule.label == label &&
  rule.category == "Nat" &&
  rule.params.length == arity &&
  rule.params.all isNatParameter &&
  rule.syntaxPattern == [.terminal label] &&
  rule.evalPolicy? == policy

private def grammarAccepted (vocabulary : Vocabulary)
    (rule : GrammarRule) : Bool :=
  if rule.label == "da:empty" then
    grammarShape "da:empty" 0 none rule
  else if rule.label == "da:add" then
    grammarShape "da:add" 2 (some .rewrite) rule
  else if rule.label == "da:mul" then
    grammarShape "da:mul" 2 (some .rewrite) rule
  else if rule.label == "da:succ" then
    grammarShape "da:succ" 1 (some .rewrite) rule
  else if vocabulary.digitLabels.contains rule.label then
    grammarShape rule.label 1 none rule
  else if vocabulary.starLabels.contains rule.label then
    grammarShape rule.label 1 (some .rewrite) rule
  else
    false

private def inferVocabulary? (language : LanguageDef) : Option Vocabulary := do
  let digitLabels := language.terms.filterMap fun rule =>
    if rule.label.startsWith "da:digit:" then some rule.label else none
  let starLabels := language.terms.filterMap fun rule =>
    if rule.label.startsWith "da:star:" then some rule.label else none
  let radix := digitLabels.length
  ensure (2 <= radix)
  ensure (starLabels.length == radix)
  ensure (digitLabels == (List.range radix).map digitLabel)
  ensure (starLabels == (List.range radix).map starLabel)
  let expectedLabels :=
    ["da:empty"] ++ digitLabels ++ ["da:add", "da:mul", "da:succ"] ++ starLabels
  ensure (language.terms.map (fun rule => rule.label) == expectedLabels)
  let vocabulary := { radix, digitLabels, starLabels }
  ensure (language.terms.all (grammarAccepted vocabulary))
  pure vocabulary

private def digitView? (vocabulary : Vocabulary) :
    Pattern -> Option (Nat × Pattern)
  | .apply label [body] => do
      let index <- vocabulary.digitLabels.findIdx? (fun candidate => candidate == label)
      pure (index, body)
  | _ => none

private def starView? (vocabulary : Vocabulary) :
    Pattern -> Option (Nat × Pattern)
  | .apply label [body] => do
      let index <- vocabulary.starLabels.findIdx? (fun candidate => candidate == label)
      pure (index, body)
  | _ => none

private def numeralDigits? (vocabulary : Vocabulary) :
    Pattern -> Option (List Nat)
  | .apply "da:empty" [] => some []
  | .apply label [body] => do
      let digit <- vocabulary.digitLabels.findIdx?
        (fun candidate => candidate == label)
      let digits <- numeralDigits? vocabulary body
      pure (digit :: digits)
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp_wf
  all_goals
    have _smaller := List.sizeOf_lt_of_mem (show body ∈ [body] by simp)
    omega

private def addBodyCarry? (firstVariable secondVariable : String) :
    Pattern -> Option Bool
  | .apply "da:add" [.fvar first, .fvar second] =>
      if first == firstVariable && second == secondVariable then some false else none
  | .apply "da:succ" [
      .apply "da:add" [.fvar first, .fvar second]] =>
      if first == firstVariable && second == secondVariable then some true else none
  | _ => none

private def succBodyCarry? (variableName : String) : Pattern -> Option Bool
  | .fvar body => if body == variableName then some false else none
  | .apply "da:succ" [.fvar body] =>
      if body == variableName then some true else none
  | _ => none

private def parseRule1? (vocabulary : Vocabulary) :
    Nat × RewriteRule -> Option Origin
  | (index, rule) =>
      match digitView? vocabulary rule.left, rule.right with
      | some (0, .apply "da:empty" []), .apply "da:empty" [] =>
          if rule.premises.isEmpty then some (origin index rule) else none
      | _, _ => none

private def parseRule2? : Nat × RewriteRule -> Option Origin
  | (index, rule) =>
      match rule.left, rule.right with
      | .apply "da:add" [.apply "da:empty" [], .fvar input], .fvar output =>
          if rule.premises.isEmpty && input == output then some (origin index rule)
          else none
      | _, _ => none

private def parseRule3? : Nat × RewriteRule -> Option Origin
  | (index, rule) =>
      match rule.left, rule.right with
      | .apply "da:add" [.fvar input, .apply "da:empty" []], .fvar output =>
          if rule.premises.isEmpty && input == output then some (origin index rule)
          else none
      | _, _ => none

private def parseRule4? (vocabulary : Vocabulary) :
    Nat × RewriteRule -> Option AddEntry
  | (index, rule) => do
      ensure rule.premises.isEmpty
      match rule.left, digitView? vocabulary rule.right with
      | .apply "da:add" [left, right], some (output, body) => do
          let (first, firstBody) <- digitView? vocabulary left
          let (second, secondBody) <- digitView? vocabulary right
          match firstBody, secondBody with
          | .fvar firstVariable, .fvar secondVariable => do
              let carry <- addBodyCarry? firstVariable secondVariable body
              pure { first, second, output, carry, origin := origin index rule }
          | _, _ => none
      | _, _ => none

private def parseRule5? : Nat × RewriteRule -> Option Origin
  | (index, rule) =>
      match rule.left, rule.right with
      | .apply "da:mul" [.apply "da:empty" [], .fvar _],
          .apply "da:empty" [] =>
          if rule.premises.isEmpty then some (origin index rule) else none
      | _, _ => none

private def parseRule6? (vocabulary : Vocabulary) :
    Nat × RewriteRule -> Option DigitEntry
  | (index, rule) => do
      ensure rule.premises.isEmpty
      match rule.left, rule.right with
      | .apply "da:mul" [left, .fvar rightVariable],
          .apply "da:add" [shifted, starred] => do
          let (digitIndex, leftBody) <- digitView? vocabulary left
          let (zeroDigit, recursiveBody) <- digitView? vocabulary shifted
          let (starIndex, starBody) <- starView? vocabulary starred
          ensure (zeroDigit == 0 && digitIndex == starIndex)
          match leftBody, recursiveBody, starBody with
          | .fvar leftVariable,
              .apply "da:mul" [.fvar recursiveLeft, .fvar recursiveRight],
              .fvar starRight =>
              if leftVariable == recursiveLeft &&
                  rightVariable == recursiveRight &&
                  rightVariable == starRight then
                pure { digit := digitIndex, origin := origin index rule }
              else none
          | _, _, _ => none
      | _, _ => none

private def parseRule7? (vocabulary : Vocabulary) :
    Nat × RewriteRule -> Option Origin
  | (index, rule) =>
      match rule.left, digitView? vocabulary rule.right with
      | .apply "da:succ" [.apply "da:empty" []],
          some (1, .apply "da:empty" []) =>
          if rule.premises.isEmpty then some (origin index rule) else none
      | _, _ => none

private def parseRule8? (vocabulary : Vocabulary) :
    Nat × RewriteRule -> Option SuccEntry
  | (index, rule) => do
      ensure rule.premises.isEmpty
      match rule.left, digitView? vocabulary rule.right with
      | .apply "da:succ" [inputPattern], some (output, body) => do
          let (input, inputBody) <- digitView? vocabulary inputPattern
          match inputBody with
          | .fvar variableName => do
              let carry <- succBodyCarry? variableName body
              pure { input, output, carry, origin := origin index rule }
          | _ => none
      | _, _ => none

private def parseRule9? (vocabulary : Vocabulary) :
    Nat × RewriteRule -> Option DigitEntry
  | (index, rule) =>
      match starView? vocabulary rule.left, rule.right with
      | some (digitIndex, .apply "da:empty" []), .apply "da:empty" [] =>
          if rule.premises.isEmpty then
            some { digit := digitIndex, origin := origin index rule }
          else none
      | _, _ => none

private def parseRule10? (vocabulary : Vocabulary) :
    Nat × RewriteRule -> Option ProductEntry
  | (index, rule) => do
      ensure rule.premises.isEmpty
      match starView? vocabulary rule.left, rule.right with
      | some (first, input), .apply "da:add" [shifted, product] => do
          match input with
          | .apply digitLabel [body] => do
              let second <- vocabulary.digitLabels.findIdx?
                (fun candidate => candidate == digitLabel)
              match body with
              | .fvar variableName => do
                  let (zeroDigit, recursive) <- digitView? vocabulary shifted
                  let (recursiveStar, recursiveBody) <- starView? vocabulary recursive
                  ensure (zeroDigit == 0 && recursiveStar == first)
                  match recursiveBody with
                  | .fvar recursiveVariable => do
                      ensure (variableName == recursiveVariable)
                      let productDigits <- numeralDigits? vocabulary product
                      pure {
                        first, second, productDigits,
                        origin := origin index rule
                      }
                  | _ => none
              | _ => none
          | _ => none
      | _, _ => none

private def uniqueBy? (entries : List alpha) (predicate : alpha -> Bool) :
    Option alpha :=
  exactlyOne? (entries.filter predicate)

private def completeDigits (radix : Nat) (entries : List DigitEntry) : Bool :=
  entries.length == radix &&
    (List.range radix).all fun digit =>
      (entries.filter fun entry => entry.digit == digit).length == 1

private def completeAdditions (radix : Nat) (entries : List AddEntry) : Bool :=
  entries.length == radix * radix &&
    (List.range radix).all fun first =>
      (List.range radix).all fun second =>
        (entries.filter fun entry =>
          entry.first == first && entry.second == second).length == 1

private def completeSuccessors (radix : Nat) (entries : List SuccEntry) : Bool :=
  entries.length == radix &&
    (List.range radix).all fun input =>
      (entries.filter fun entry => entry.input == input).length == 1

private def completeProducts (radix : Nat) (entries : List ProductEntry) : Bool :=
  entries.length == radix * radix &&
    (List.range radix).all fun first =>
      (List.range radix).all fun second =>
        (entries.filter fun entry =>
          entry.first == first && entry.second == second).length == 1

/-- Structurally inspect the supplied DA presentation.  Names are never used
to classify rules; every family is identified by its patterns. -/
def inspect? (language : LanguageDef) : Option Profile := do
  ensure language.equations.isEmpty
  ensure (language.types == ["Nat"])
  let vocabulary <- inferVocabulary? language
  let indexed := ruleEntries language
  let rule1s := indexed.filterMap (parseRule1? vocabulary)
  let rule2s := indexed.filterMap parseRule2?
  let rule3s := indexed.filterMap parseRule3?
  let additions := indexed.filterMap (parseRule4? vocabulary)
  let rule5s := indexed.filterMap parseRule5?
  let multiplications := indexed.filterMap (parseRule6? vocabulary)
  let rule7s := indexed.filterMap (parseRule7? vocabulary)
  let successors := indexed.filterMap (parseRule8? vocabulary)
  let starZeros := indexed.filterMap (parseRule9? vocabulary)
  let products := indexed.filterMap (parseRule10? vocabulary)
  let rule1 <- exactlyOne? rule1s
  let rule2 <- exactlyOne? rule2s
  let rule3 <- exactlyOne? rule3s
  let rule5 <- exactlyOne? rule5s
  let rule7 <- exactlyOne? rule7s
  ensure (completeAdditions vocabulary.radix additions)
  ensure (completeDigits vocabulary.radix multiplications)
  ensure (completeSuccessors vocabulary.radix successors)
  ensure (completeDigits vocabulary.radix starZeros)
  ensure (completeProducts vocabulary.radix products)
  let classifiedCount :=
    rule1s.length + rule2s.length + rule3s.length + additions.length +
    rule5s.length + multiplications.length + rule7s.length +
    successors.length + starZeros.length + products.length
  ensure (classifiedCount == language.rewrites.length)
  pure {
    vocabulary, rule1, rule2, rule3, additions, rule5,
    multiplications, rule7, successors, starZeros, products
  }

def findAddition? (profile : Profile) (first second : Nat) : Option AddEntry :=
  uniqueBy? profile.additions fun entry =>
    entry.first == first && entry.second == second

def findSuccessor? (profile : Profile) (input : Nat) : Option SuccEntry :=
  uniqueBy? profile.successors fun entry => entry.input == input

def findProduct? (profile : Profile) (first second : Nat) : Option ProductEntry :=
  uniqueBy? profile.products fun entry =>
    entry.first == first && entry.second == second

def additionRow? (profile : Profile) (first second carryIn : Nat) :
    Option TableRow := do
  ensure (carryIn <= 1)
  let addition <- findAddition? profile first second
  if carryIn == 0 then
    pure {
      inputs := [first, second, carryIn]
      outputs := [addition.output, if addition.carry then 1 else 0]
      origins := [addition.origin.render]
    }
  else
    let successor <- findSuccessor? profile addition.output
    ensure (!(addition.carry && successor.carry))
    pure {
      inputs := [first, second, carryIn]
      outputs := [successor.output,
        if addition.carry || successor.carry then 1 else 0]
      origins := [addition.origin.render, successor.origin.render]
    }

def additionTableFromProfile? (profile : Profile) : Option FiniteTable := do
  let firstRows <- (List.range profile.vocabulary.radix).mapM fun first => do
    let secondRows <- (List.range profile.vocabulary.radix).mapM fun second =>
      [0, 1].mapM fun carry => additionRow? profile first second carry
    pure secondRows.flatten
  pure firstRows.flatten

/-- The first target instruction graph: a generic digit/carry loop whose finite
lookup table is derived from the supplied DA rules. -/
def additionProgram (table : FiniteTable) : Program := [
  ⟨"left-length", .length 0 1 1⟩,
  ⟨"right-length", .length 1 2 2⟩,
  ⟨"index-zero", .set 0 0 3⟩,
  ⟨"carry-zero", .set 5 0 4⟩,
  ⟨"left-present?", .branchLt 0 1 5 6⟩,
  ⟨"read-left", .readOrZero 0 0 3 7⟩,
  ⟨"left-zero", .set 3 0 7⟩,
  ⟨"right-present?", .branchLt 0 2 8 9⟩,
  ⟨"read-right", .readOrZero 1 0 4 10⟩,
  ⟨"right-zero", .set 4 0 10⟩,
  ⟨"left-active?", .branchLt 0 1 13 11⟩,
  ⟨"right-active?", .branchLt 0 2 13 12⟩,
  ⟨"carry-active?", .branchEq 5 0 16 13⟩,
  ⟨"rules-4+8", .lookup [3, 4, 5] [6, 5] table 14⟩,
  ⟨"write-digit", .write 2 0 6 15⟩,
  ⟨"next-digit", .increment 0 4⟩,
  ⟨"return", .returnBuffer 2⟩
]

def compileAddition? (source : LanguageDef) : Option Program := do
  let profile <- inspect? source
  let table <- additionTableFromProfile? profile
  pure (additionProgram table)

def initialAdditionConfig (program : Program) (left right : List Nat)
    (fuel : Nat) : Config :=
  .running program 0 [left, right, []] (List.replicate 7 0) fuel []

def terminalOutcome? : Config -> Option Outcome
  | .halted outcome _ => some outcome
  | _ => none

structure DigitVectorResult where
  digits : List Nat
  origins : List String
deriving Repr, DecidableEq

/-- Read and consume one least-significant digit, padding an exhausted input
with zero. -/
def popDigit : List Nat -> Nat × List Nat
  | [] => (0, [])
  | digit :: digits => (digit, digits)

/-- Independent finite evaluation of one source-derived digit-addition table.
The target-loop proof relates this recursion to the lower-level C1 program. -/
def addUsingTableFuel (table : FiniteTable) :
    Nat -> List Nat -> List Nat -> Nat -> Option DigitVectorResult
  | 0, _, _, _ => none
  | fuel + 1, left, right, carry => do
      if left.isEmpty && right.isEmpty && carry == 0 then
        pure { digits := [], origins := [] }
      else
        let (first, leftRest) := popDigit left
        let (second, rightRest) := popDigit right
        let (_, row) <- lookupTable? [first, second, carry] table
        match row.outputs with
        | [digit, nextCarry] => do
            let rest <- addUsingTableFuel table fuel leftRest rightRest nextCarry
            pure {
              digits := digit :: rest.digits
              origins := row.origins ++ rest.origins
            }
        | _ => none

def addUsingTable? (table : FiniteTable) (left right : List Nat)
    (carry : Nat := 0) : Option DigitVectorResult :=
  addUsingTableFuel table (left.length + right.length + 2) left right carry

def findMultiplication? (profile : Profile) (digit : Nat) :
    Option DigitEntry :=
  uniqueBy? profile.multiplications fun entry => entry.digit == digit

def splitProduct? : List Nat -> Option (Nat × Nat)
  | [] => some (0, 0)
  | [low] => some (low, 0)
  | [low, high] => some (low, high)
  | _ => none

def productAccumulationRow? (profile : Profile) (additionTable : FiniteTable)
    (first second accumulated carry : Nat) : Option TableRow := do
  let multiplication <- findMultiplication? profile first
  let product <- findProduct? profile first second
  let withAccumulated <- addUsingTable? additionTable product.productDigits [accumulated]
  let withCarry <- addUsingTable? additionTable withAccumulated.digits [carry]
  let (digit, nextCarry) <- splitProduct? withCarry.digits
  ensure (digit < profile.vocabulary.radix &&
    nextCarry < profile.vocabulary.radix)
  pure {
    inputs := [first, second, accumulated, carry]
    outputs := [digit, nextCarry]
    origins := [multiplication.origin.render, product.origin.render] ++
      withAccumulated.origins ++ withCarry.origins
  }

def multiplicationTableFromProfile? (profile : Profile)
    (additionTable : FiniteTable) : Option FiniteTable := do
  let firstRows <- (List.range profile.vocabulary.radix).mapM fun first => do
    let secondRows <- (List.range profile.vocabulary.radix).mapM fun second => do
      let accumulatedRows <-
        (List.range profile.vocabulary.radix).mapM fun accumulated =>
          (List.range profile.vocabulary.radix).mapM fun carry =>
            productAccumulationRow? profile additionTable
              first second accumulated carry
      pure accumulatedRows.flatten
    pure secondRows.flatten
  pure firstRows.flatten

/-- Grade-school digit multiplication over a rule-derived bounded table.  The
loop graph is fixed C1 control; every digit product and carry result is literal
data derived from Rules 4, 6, 8, and 10. -/
def multiplicationProgram (table : FiniteTable) : Program := [
  ⟨"left-length", .length 0 1 1⟩,
  ⟨"right-length", .length 1 2 2⟩,
  ⟨"outer-index-zero", .set 0 0 3⟩,
  ⟨"left-active?", .branchLt 0 1 4 19⟩,
  ⟨"read-left", .readOrZero 0 0 3 5⟩,
  ⟨"inner-index-zero", .set 4 0 6⟩,
  ⟨"output-index", .copy 0 6 7⟩,
  ⟨"carry-zero", .set 8 0 8⟩,
  ⟨"right-active?", .branchLt 4 2 9 15⟩,
  ⟨"read-right", .readOrZero 1 4 5 10⟩,
  ⟨"read-accumulated", .readOrZero 2 6 7 11⟩,
  ⟨"rules-4+6+8+10", .lookup [3, 5, 7, 8] [9, 8] table 12⟩,
  ⟨"write-product-digit", .write 2 6 9 13⟩,
  ⟨"next-right-digit", .increment 4 14⟩,
  ⟨"next-output-digit", .increment 6 8⟩,
  ⟨"carry-active?", .branchEq 8 0 18 16⟩,
  ⟨"right-zero", .set 5 0 17⟩,
  ⟨"read-carry-target", .readOrZero 2 6 7 11⟩,
  ⟨"next-left-digit", .increment 0 3⟩,
  ⟨"return", .returnBuffer 2⟩
]

def compileMultiplication? (source : LanguageDef) : Option Program := do
  let profile <- inspect? source
  let additionTable <- additionTableFromProfile? profile
  let multiplicationTable <- multiplicationTableFromProfile? profile additionTable
  pure (multiplicationProgram multiplicationTable)

def initialMultiplicationConfig (program : Program) (left right : List Nat)
    (fuel : Nat) : Config :=
  .running program 0 [left, right, []] (List.replicate 10 0) fuel []

def tableBehavior (table : FiniteTable) : List (List Nat × List Nat) :=
  table.map fun row => (row.inputs, row.outputs)

def additionProgramBehavior? (program : Program) :
    Option (List (List Nat × List Nat)) := do
  let cell <- C1DigitMachine.at? program 13
  match cell.instruction with
  | .lookup _ _ table _ => some (tableBehavior table)
  | _ => none

def droppedCarryLanguage : LanguageDef :=
  let base := language radixTwo
  let changed : RewriteRule := {
    rule4 radixTwo 1 1 with
    right := digit 0 (add (v "x") (v "y"))
  }
  { base with rewrites := base.rewrites.set 6 changed }

def deletedCarryLanguage : LanguageDef :=
  let base := language radixTwo
  { base with rewrites := base.rewrites.eraseIdx 6 }

def renamedCarryLanguage : LanguageDef :=
  let base := language radixTwo
  let changed : RewriteRule := {
    rule4 radixTwo 1 1 with
    name := "renamed-carry-rule"
  }
  { base with rewrites := base.rewrites.set 6 changed }

def addChangedToMulLanguage : LanguageDef :=
  let base := language radixTwo
  let changed : RewriteRule := {
    rule4 radixTwo 1 1 with
    left := mul (digit 1 (v "x")) (digit 1 (v "y"))
  }
  { base with rewrites := base.rewrites.set 6 changed }

def deletedRule6Language : LanguageDef :=
  let base := language radixTwo
  { base with rewrites := base.rewrites.eraseIdx 8 }

def changedRule10ProductLanguage : LanguageDef :=
  let base := language radixTwo
  let changed : RewriteRule := {
    rule10 radixTwo 1 1 with
    right := add (digit 0 (star 1 (v "x"))) empty
  }
  { base with rewrites := base.rewrites.set 18 changed }

theorem radixTwo_inspects : (inspect? (language radixTwo)).isSome := by
  decide +kernel

theorem radixTwo_addition_compiles :
    (compileAddition? (language radixTwo)).isSome := by
  decide +kernel

theorem radixTwo_multiplication_compiles :
    (compileMultiplication? (language radixTwo)).isSome := by
  decide +kernel

theorem radixTwo_seven_plus_one_c1 :
    let program := (compileAddition? (language radixTwo)).getD []
    terminalOutcome?
        (runSteps C1DigitMachine.radixTwo 100
          (initialAdditionConfig program [1, 1, 1] [1] 100)) =
      some (.value [0, 0, 0, 1]) := by
  decide +kernel

theorem radixTwo_seven_times_six_c1 :
    let program := (compileMultiplication? (language radixTwo)).getD []
    terminalOutcome?
        (runSteps { C1DigitMachine.radixTwo with registerLimit := 10 } 1000
          (initialMultiplicationConfig program [1, 1, 1] [0, 1, 1] 1000)) =
      some (.value [0, 1, 0, 1, 0, 1]) := by
  decide +kernel

theorem dropped_carry_changes_compiled_behavior :
    let original := (compileAddition? (language radixTwo)).getD []
    let changed := (compileAddition? droppedCarryLanguage).getD []
    terminalOutcome?
        (runSteps C1DigitMachine.radixTwo 100
          (initialAdditionConfig original [1] [1] 100)) =
        some (.value [0, 1]) ∧
      terminalOutcome?
        (runSteps C1DigitMachine.radixTwo 100
          (initialAdditionConfig changed [1] [1] 100)) =
        some (.value [0]) := by
  decide +kernel

theorem deleted_carry_rejects_compilation :
    compileAddition? deletedCarryLanguage = none := by
  decide +kernel

theorem add_changed_to_mul_rejects_compilation :
    compileAddition? addChangedToMulLanguage = none := by
  decide +kernel

theorem deleted_rule6_rejects_multiplication :
    compileMultiplication? deletedRule6Language = none := by
  decide +kernel

theorem changed_rule10_changes_multiplication :
    let original := (compileMultiplication? (language radixTwo)).getD []
    let changed := (compileMultiplication? changedRule10ProductLanguage).getD []
    terminalOutcome?
        (runSteps { C1DigitMachine.radixTwo with registerLimit := 10 } 100
          (initialMultiplicationConfig original [1] [1] 100)) =
        some (.value [1]) ∧
      terminalOutcome?
        (runSteps { C1DigitMachine.radixTwo with registerLimit := 10 } 100
          (initialMultiplicationConfig changed [1] [1] 100)) =
        some (.value [0]) := by
  decide +kernel

theorem rename_only_preserves_behavior_table :
    (compileAddition? renamedCarryLanguage).bind additionProgramBehavior? =
      (compileAddition? (language radixTwo)).bind additionProgramBehavior? := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.WaltersZantemaDAToC1
