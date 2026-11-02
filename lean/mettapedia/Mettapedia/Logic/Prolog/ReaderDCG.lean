import Mettapedia.Logic.Prolog.ReaderSource

/-!
# Canonical DCG expansion

This module adapts the term-expansion structure of SWI-Prolog V10.1.9
`boot/dcg.pl` to the canonical `Logic.LP.Term` representation. It adds the two
difference-list arguments, translates terminals to list unification, and
threads conjunction and control through explicit state terms.

Expansion produces an ordinary head term and body term first. The existing
`ReaderSource.toHead` and `ReaderSource.toGoal` functions then perform the only
clause/control interpretation. This module is a source desugaring pass, not a
resolver or a second Prolog semantics.

Module qualification and malformed terminal lists fail visibly. Runtime
support for `phrase/3` remains a separate obligation for variable grammar
bodies.
-/

namespace Mettapedia.Logic.Prolog.ReaderDCG

open SourceSignature

inductive Error where
  | exhaustedInputMeasure
  | nonCallable
  | moduleQualification
  | improperTerminalList
  | head (error : ReaderSource.Error)
  | body (error : ReaderSource.Error)
deriving DecidableEq, Repr

/-- The ordinary source terms produced before canonical clause
classification. `nextFresh` is the first unused source occurrence. -/
structure ExpandedRule where
  head : SourceSignature.Term
  body : SourceSignature.Term
  nextFresh : Nat

private structure ExpandedBody where
  term : SourceSignature.Term
  nextFresh : Nat

private def application? : SourceSignature.Term ->
    Option (String × List SourceSignature.Term)
  | .const (.atom name) => some (name, [])
  | .app indicator arguments =>
      some (indicator.name, List.ofFn arguments)
  | _ => none

private def termVariables : SourceSignature.Term ->
    List SourceSignature.Variable
  | .var identity => [identity]
  | .const _ => []
  | .app _ arguments =>
      (List.ofFn fun index => termVariables (arguments index)).flatten

private def firstFresh (head body : SourceSignature.Term) : Nat :=
  (termVariables head ++ termVariables body).foldl
    (fun next identity => max next (identity.occurrence + 1)) 0

private def fresh (next : Nat) : SourceSignature.Term × Nat :=
  (SourceSignature.var "_DCG" next, next + 1)

private def properListAux : Nat -> SourceSignature.Term ->
    Option (List SourceSignature.Term)
  | 0, _ => none
  | _ + 1, .const .nil => some []
  | fuel + 1, term => do
      let (name, arguments) <- application? term
      let [head, tail] := arguments | none
      if name = "[|]" then
        let rest <- properListAux fuel tail
        pure (head :: rest)
      else none

private def properList? (term : SourceSignature.Term) :
    Option (List SourceSignature.Term) :=
  properListAux (term.size + 1) term

private def conjunction (left right : SourceSignature.Term) :
    SourceSignature.Term :=
  SourceSignature.compound "," [left, right]

private def unification (left right : SourceSignature.Term) :
    SourceSignature.Term :=
  SourceSignature.compound "=" [left, right]

private def extendCallable (term input output : SourceSignature.Term) :
    Except Error SourceSignature.Term :=
  match term with
  | .const (.atom name) =>
      .ok (SourceSignature.compound name [input, output])
  | .app indicator arguments =>
      if indicator.name = ":" && indicator.arity = 2 then
        .error .moduleQualification
      else
        .ok (SourceSignature.compound indicator.name
          (List.ofFn arguments ++ [input, output]))
  | _ => .error .nonCallable

private def stringCodes (value : String) : List SourceSignature.Term :=
  value.toList.map fun character =>
    SourceSignature.integer (Int.ofNat character.toNat)

private def bodyAux : Nat -> SourceSignature.Term -> SourceSignature.Term ->
    SourceSignature.Term -> Nat -> Except Error ExpandedBody
  | 0, _, _, _, _ => .error .exhaustedInputMeasure
  | fuel + 1, body, input, output, nextFresh =>
      match body with
      | .var _ => .ok {
          term := SourceSignature.compound "phrase" [body, input, output]
          nextFresh
        }
      | .const .nil => .ok {
          term := unification input output
          nextFresh
        }
      | .const (.string value) => .ok {
          term := unification input
            (SourceSignature.list (stringCodes value) output)
          nextFresh
        }
      | .const (.atom "!") => .ok {
          term := conjunction (SourceSignature.atom "!")
            (unification output input)
          nextFresh
        }
      | .const (.atom "{}") => .ok {
          term := unification output input
          nextFresh
        }
      | .app indicator arguments =>
          let arguments := List.ofFn arguments
          match indicator.name, arguments with
          | "[|]", _ =>
              match properList? body with
              | some elements => .ok {
                  term := unification input
                    (SourceSignature.list elements output)
                  nextFresh
                }
              | none => .error .improperTerminalList
          | "{}", [goal] => .ok {
              term := conjunction goal (unification output input)
              nextFresh
            }
          | ",", [left, right] => do
              let (middle, afterMiddle) := fresh nextFresh
              let expandedLeft <- bodyAux fuel left input middle afterMiddle
              let expandedRight <- bodyAux fuel right middle output
                expandedLeft.nextFresh
              pure {
                term := conjunction expandedLeft.term expandedRight.term
                nextFresh := expandedRight.nextFresh
              }
          | ";", [choice, elseBranch] =>
              match application? choice with
              | some ("->", [condition, thenBranch]) => do
                  let (middle, afterMiddle) := fresh nextFresh
                  let expandedCondition <-
                    bodyAux fuel condition input middle afterMiddle
                  let expandedThen <- bodyAux fuel thenBranch middle output
                    expandedCondition.nextFresh
                  let expandedElse <- bodyAux fuel elseBranch input output
                    expandedThen.nextFresh
                  pure {
                    term := SourceSignature.compound ";" [
                      SourceSignature.compound "->"
                        [expandedCondition.term, expandedThen.term],
                      expandedElse.term
                    ]
                    nextFresh := expandedElse.nextFresh
                  }
              | some ("*->", [condition, thenBranch]) => do
                  let (middle, afterMiddle) := fresh nextFresh
                  let expandedCondition <-
                    bodyAux fuel condition input middle afterMiddle
                  let expandedThen <- bodyAux fuel thenBranch middle output
                    expandedCondition.nextFresh
                  let expandedElse <- bodyAux fuel elseBranch input output
                    expandedThen.nextFresh
                  pure {
                    term := SourceSignature.compound ";" [
                      SourceSignature.compound "*->"
                        [expandedCondition.term, expandedThen.term],
                      expandedElse.term
                    ]
                    nextFresh := expandedElse.nextFresh
                  }
              | _ => do
                  let expandedLeft <-
                    bodyAux fuel choice input output nextFresh
                  let expandedRight <- bodyAux fuel elseBranch input output
                    expandedLeft.nextFresh
                  pure {
                    term := SourceSignature.compound ";"
                      [expandedLeft.term, expandedRight.term]
                    nextFresh := expandedRight.nextFresh
                  }
          | "|", [left, right] => do
              let expandedLeft <- bodyAux fuel left input output nextFresh
              let expandedRight <- bodyAux fuel right input output
                expandedLeft.nextFresh
              pure {
                term := SourceSignature.compound ";"
                  [expandedLeft.term, expandedRight.term]
                nextFresh := expandedRight.nextFresh
              }
          | "->", [condition, thenBranch] => do
              let (middle, afterMiddle) := fresh nextFresh
              let expandedCondition <-
                bodyAux fuel condition input middle afterMiddle
              let expandedThen <- bodyAux fuel thenBranch middle output
                expandedCondition.nextFresh
              pure {
                term := SourceSignature.compound "->"
                  [expandedCondition.term, expandedThen.term]
                nextFresh := expandedThen.nextFresh
              }
          | "*->", [condition, thenBranch] => do
              let (middle, afterMiddle) := fresh nextFresh
              let expandedCondition <-
                bodyAux fuel condition input middle afterMiddle
              let expandedThen <- bodyAux fuel thenBranch middle output
                expandedCondition.nextFresh
              pure {
                term := SourceSignature.compound "*->"
                  [expandedCondition.term, expandedThen.term]
                nextFresh := expandedThen.nextFresh
              }
          | "\\+", [condition] => do
              let (ignored, afterIgnored) := fresh nextFresh
              let expandedCondition <-
                bodyAux fuel condition input ignored afterIgnored
              pure {
                term := conjunction
                  (SourceSignature.compound "\\+" [expandedCondition.term])
                  (unification output input)
                nextFresh := expandedCondition.nextFresh
              }
          | ":", [_, _] => .error .moduleQualification
          | _, _ => do
              let extended <- extendCallable body input output
              pure { term := extended, nextFresh }
      | .const (.atom _) => do
          let extended <- extendCallable body input output
          pure { term := extended, nextFresh }
      | .const _ => .error .nonCallable

/-- Expand one DCG rule to ordinary canonical source terms. Generated
difference-list identities start strictly above every source occurrence in
the original rule. -/
def expandTerms (head body : SourceSignature.Term) : Except Error ExpandedRule := do
  let start := firstFresh head body
  let (input, afterInput) := fresh start
  let (output, afterOutput) := fresh afterInput
  let expandedHead <- extendCallable head input output
  let expandedBody <- bodyAux (body.size + 1) body input output afterOutput
  pure {
    head := expandedHead
    body := expandedBody.term
    nextFresh := expandedBody.nextFresh
  }

/-- Expand and classify one DCG rule as the same canonical clause consumed by
the source runtime. -/
def expand (head body : SourceSignature.Term) :
    Except Error SourceSignature.Clause :=
  match expandTerms head body with
  | .error error => .error error
  | .ok expanded =>
      match ReaderSource.toHead expanded.head with
      | .error error => .error (.head error)
      | .ok parsedHead =>
          match ReaderSource.toGoal expanded.body with
          | .error error => .error (.body error)
          | .ok parsedBody => .ok {
              head := parsedHead
              body := parsedBody
              sourceTerm := some
                (ReaderSource.normalizedClauseTerm expanded.head expanded.body)
            }

/-- Successful expansion retains the exact ordinary clause term used for
canonical head/body classification and later database reflection. -/
theorem expand_sourceTerm_present {head body : SourceSignature.Term}
    {clause : SourceSignature.Clause}
    (hExpand : expand head body = .ok clause) :
    clause.sourceTerm.isSome := by
  unfold expand at hExpand
  cases hTerms : expandTerms head body with
  | error error => simp [hTerms] at hExpand
  | ok expanded =>
      cases hHead : ReaderSource.toHead expanded.head with
      | error error => simp [hTerms, hHead] at hExpand
      | ok parsedHead =>
          cases hBody : ReaderSource.toGoal expanded.body with
          | error error => simp [hTerms, hHead, hBody] at hExpand
          | ok parsedBody =>
              simp [hTerms, hHead, hBody] at hExpand
              subst clause
              rfl

end Mettapedia.Logic.Prolog.ReaderDCG
