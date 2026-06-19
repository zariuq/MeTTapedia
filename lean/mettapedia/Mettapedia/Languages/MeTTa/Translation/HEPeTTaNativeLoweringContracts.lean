import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# HE to PeTTa Native Lowering Contracts

Small decidable contracts for the native-first HE to PeTTa lowering boundary.
These predicates do not model the full Prolog translator; they pin the local
design obligations that decide when a lowering may use native PeTTa directly
and when it must stay on the compatibility path.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

mutual
  def isLogicVar : Atom → Bool
    | .var _ => true
    | .expression xs => isLogicVarList xs
    | _ => false

  def isLogicVarList : List Atom → Bool
    | [] => false
    | x :: xs => isLogicVar x || isLogicVarList xs
end

def isNativeNumberLiteral : Atom → Bool
  | .grounded (.int _) => true
  | _ => false

def nativeNumericHead (head : String) : Bool :=
  head == "+" || head == "-" || head == "*" || head == "/" ||
    head == "%" || head == "<" || head == ">"

def safeNativeNumericCall : Atom → Bool
  | .expression (.symbol head :: args) =>
      nativeNumericHead head && args.all isNativeNumberLiteral
  | _ => false

def reservedPeTTaDataHead : String → Bool
  | "Predicate" => true
  | _ => false

mutual
  def containsReservedDataHead : Atom → Bool
    | .expression (.symbol head :: args) =>
        reservedPeTTaDataHead head || containsReservedDataHeadList args
    | .expression xs => containsReservedDataHeadList xs
    | _ => false

  def containsReservedDataHeadList : List Atom → Bool
    | [] => false
    | x :: xs => containsReservedDataHead x || containsReservedDataHeadList xs
end

def safeNativeDataEquality : Atom → Bool
  | .expression [.symbol "==", left, right] =>
      !isLogicVar left && !isLogicVar right &&
        !containsReservedDataHead left && !containsReservedDataHead right
  | .expression [.symbol "!=", left, right] =>
      !isLogicVar left && !isLogicVar right &&
        !containsReservedDataHead left && !containsReservedDataHead right
  | _ => false

def renameReservedDataHead : Atom → Atom
  | .expression (.symbol "Predicate" :: args) =>
      .expression (.symbol "Predicate-he" :: args.map renameReservedDataHead)
  | .expression xs => .expression (xs.map renameReservedDataHead)
  | other => other

def headSymbol? : Atom → Option String
  | .expression (.symbol head :: _) => some head
  | _ => none

def sourceHeadNeedsCompat (sourceHeads : List String) (a : Atom) : Bool :=
  match headSymbol? a with
  | some head => sourceHeads.contains head && !safeNativeNumericCall a
  | none => false

def b2DeduceAndKernelRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "deduce", .expression [.symbol "And", .var "$a", .var "$b"]],
      .expression [.symbol "And",
        .expression [.symbol "deduce", .var "$a"],
        .expression [.symbol "deduce", .var "$b"]]]

def obsoleteBoolAndRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "And", .symbol "T", .symbol "T"], .symbol "T"]

mutual
  def containsAndTerm : Atom → Bool
    | .expression (.symbol "And" :: _ :: _) => true
    | .expression xs => containsAndTermList xs
    | _ => false

  def containsAndTermList : List Atom → Bool
    | [] => false
    | x :: xs => containsAndTerm x || containsAndTermList xs
end

def hasDeduceAndKernelRule (atoms : List Atom) : Bool :=
  atoms.contains b2DeduceAndKernelRule

def hasObsoleteBoolAndRule (atoms : List Atom) : Bool :=
  atoms.contains obsoleteBoolAndRule

def hasLiveValueAndUse : List Atom → Bool
  | [] => false
  | atom :: rest =>
      if atom == b2DeduceAndKernelRule || atom == obsoleteBoolAndRule then
        hasLiveValueAndUse rest
      else
        match atom with
        | .expression [.symbol "=", _, rhs] =>
            containsAndTerm rhs || hasLiveValueAndUse rest
        | .expression (.symbol "!" :: expr :: _) =>
            containsAndTerm expr || hasLiveValueAndUse rest
        | _ => hasLiveValueAndUse rest

def shouldDropDeadBoolAndHelper (atoms : List Atom) : Bool :=
  hasDeduceAndKernelRule atoms &&
    hasObsoleteBoolAndRule atoms &&
    !hasLiveValueAndUse atoms

def d4DirectTruthRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
      .expression
        [.symbol "match", .symbol "&self",
          .expression [.symbol ":", .var "$x", .var "$type"],
          .symbol "T"]]

def d4ImplicationTruthRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
      .expression
        [.symbol "match", .symbol "&self",
          .expression
            [.symbol ":", .var "$impl",
              .expression [.symbol "->", .var "$cause", .var "$type"]],
          .expression
            [.symbol "if",
              .expression [.symbol "==", .var "$cause", .var "$type"],
              .expression [.symbol "empty"],
              .expression [.symbol "=-he", .var "$cause", .symbol "T"]]]]

def d4GuardedImplicationTruthRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
      .expression
        [.symbol "let", .var "$direct",
          .expression
            [.symbol "collapse",
              .expression
                [.symbol "match", .symbol "&self",
                  .expression [.symbol ":", .var "$witness", .var "$type"],
                  .symbol "T"]],
          .expression
            [.symbol "if",
              .expression [.symbol "==", .var "$direct", .expression []],
              .expression
                [.symbol "let", .var "$cause",
                  .expression
                    [.symbol "match", .symbol "&self",
                      .expression
                        [.symbol ":", .var "$impl",
                          .expression [.symbol "->", .var "$cause", .var "$type"]],
                      .var "$cause"],
                  .expression
                    [.symbol "if",
                      .expression [.symbol "==", .var "$cause", .var "$type"],
                      .expression [.symbol "empty"],
                      .expression
                        [.symbol "call-or-inert",
                          .expression
                            [.symbol "quote",
                              .expression [.symbol "=-he", .var "$cause", .symbol "T"]]]]],
              .expression [.symbol "empty"]]]]

def guardedImplicationTruthRuleShape : Atom → Bool
  | .expression
      [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
        .expression
          [.symbol "let", .var "$direct",
            .expression
              [.symbol "collapse",
                .expression
                  [.symbol "match", .symbol "&self",
                    .expression [.symbol ":", .var "$witness", .var "$type"],
                    .symbol "T"]],
            .expression
              [.symbol "if",
                .expression [.symbol "==", .var "$direct", .expression []],
                .expression
                  [.symbol "let", .var "$cause",
                    .expression
                      [.symbol "match", .symbol "&self",
                        .expression
                          [.symbol ":", .var "$impl",
                            .expression [.symbol "->", .var "$cause", .var "$type"]],
                        .var "$cause"],
                    .expression
                      [.symbol "if",
                        .expression [.symbol "==", .var "$cause", .var "$type"],
                        .expression [.symbol "empty"],
                        .expression
                          [.symbol "call-or-inert",
                            .expression
                              [.symbol "quote",
                                .expression [.symbol "=-he", .var "$cause", .symbol "T"]]]]],
                .expression [.symbol "empty"]]]] => true
  | _ => false

def intAtom (n : Int) : Atom := .grounded (.int n)

example :
    safeNativeNumericCall
      (.expression [.symbol "+", intAtom 2, intAtom 1]) = true := by
  native_decide

example :
    safeNativeNumericCall
      (.expression [.symbol "+", .var "$x", intAtom 1]) = false := by
  native_decide

example :
    safeNativeDataEquality
      (.expression [.symbol "==", .symbol "A", .symbol "A"]) = true := by
  native_decide

example :
    safeNativeDataEquality
      (.expression [.symbol "==",
        .expression [.symbol "Predicate", .symbol "P"],
        .expression [.symbol "Predicate", .symbol "P"]]) = false := by
  native_decide

example :
    renameReservedDataHead
      (.expression [.symbol "Evaluation",
        .expression [.symbol "Predicate", .symbol "P"]]) =
      (.expression [.symbol "Evaluation",
        .expression [.symbol "Predicate-he", .symbol "P"]]) := by
  native_decide

example :
    sourceHeadNeedsCompat ["foo"]
      (.expression [.symbol "foo", .symbol "B"]) = true := by
  native_decide

example :
    sourceHeadNeedsCompat ["foo"]
      (.expression [.symbol "+", intAtom 2, intAtom 1]) = false := by
  native_decide

def b2RuleDataAnd : Atom :=
  .expression
    [.symbol "Implication",
      .expression [.symbol "And",
        .expression [.symbol "Evaluation", .expression [.symbol "philosopher", .var "$x"]],
        .expression [.symbol "Evaluation", .expression [.symbol "likes-to-wrestle", .var "$x"]]],
      .expression [.symbol "Evaluation", .expression [.symbol "human", .var "$x"]]]

example :
    shouldDropDeadBoolAndHelper
      [b2RuleDataAnd, b2DeduceAndKernelRule, obsoleteBoolAndRule] = true := by
  native_decide

example :
    shouldDropDeadBoolAndHelper
      [b2RuleDataAnd, b2DeduceAndKernelRule, obsoleteBoolAndRule,
        .expression [.symbol "=", .expression [.symbol "pair"],
          .expression [.symbol "And", .symbol "A", .symbol "B"]]] = false := by
  native_decide

example :
    guardedImplicationTruthRuleShape d4GuardedImplicationTruthRule = true := by
  native_decide

example :
    guardedImplicationTruthRuleShape d4ImplicationTruthRule = false := by
  native_decide

example :
    guardedImplicationTruthRuleShape d4DirectTruthRule = false := by
  native_decide

end Mettapedia.Languages.MeTTa.Translation
