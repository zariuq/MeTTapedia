import MeTTailCore.MeTTaIL.Syntax
import MeTTailCore.MeTTaIL.Substitution

namespace MeTTailCore.MeTTaIL.Match

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Substitution

abbrev Bindings := List (String × Pattern)

def Bindings.lookup (b : Bindings) (name : String) : Option Pattern :=
  b.find? (·.1 == name) |>.map (·.2)

def mergeBindings (b1 b2 : Bindings) : Option Bindings :=
  b2.foldlM (init := b1) fun acc (name, val) =>
    match acc.find? (·.1 == name) with
    | none => some ((name, val) :: acc)
    | some (_, existing) => if existing == val then some acc else none

/-- Enumerate every choice of one element together with the remaining list. -/
def pickEach : List α → List (α × List α)
  | [] => []
  | x :: xs =>
      let head := (x, xs)
      let tail := (pickEach xs).map (fun (y, ys) => (y, x :: ys))
      head :: tail

/-- MeTTa tuple/list view used by `cons`-style matching and construction.
`(a b c)` is represented as `.apply "a" [b, c]`, while `()` is empty. -/
def tupleElems : Pattern → List Pattern
  | .apply "()" [] => []
  | .apply "Expr" elems => elems
  | .apply ctor args => (.apply ctor []) :: args
  | p => [p]

/-- Inverse of `tupleElems` under the same MeTTa tuple/list convention. -/
def tupleOfElems : List Pattern → Pattern
  | [] => .apply "()" []
  | h :: tl =>
      match h with
      | .apply ctor [] => .apply ctor tl
      | _ => .apply "Expr" (h :: tl)

private def dollarVarName? : Pattern → Option String
  | .apply ctor [] =>
      if ctor.startsWith "$" then
        let name := (ctor.drop 1).toString
        if name.isEmpty then none else some name
      else
        none
  | _ => none

mutual

def matchArgs : List Pattern → List Pattern → List Bindings
  | [], [] => [[]]
  | p :: ps, t :: ts =>
    (matchPattern p t).flatMap fun hb =>
      (matchArgs ps ts).filterMap fun tb =>
        mergeBindings hb tb
  | _, _ => []
termination_by pats => sizeOf pats

def matchBag : List Pattern → Option String → CollType → List Pattern → List Bindings
  | [], restVar, ct, termElems =>
    match restVar with
    | none => if termElems.isEmpty then [[]] else []
    | some rv => [[(rv, .collection ct termElems none)]]
  | ppat :: prest, restVar, ct, termElems =>
    (pickEach termElems).flatMap fun (telem, remaining) =>
      (matchPattern ppat telem).flatMap fun hb =>
        (matchBag prest restVar ct remaining).filterMap fun restB =>
          mergeBindings hb restB
termination_by ppats => sizeOf ppats

def matchPattern (pat term : Pattern) : List Bindings :=
  match pat, term with
  | .fvar x, t => [[(x, t)]]
  | .bvar n, .bvar m => if n == m then [[]] else []
  | .apply c1 pargs, .apply c2 targs =>
    if c1 == c2 && pargs.length == targs.length then
      matchArgs pargs targs
    else if !pargs.isEmpty then
      match dollarVarName? (.apply c1 []) with
      | some name =>
          match tupleElems (.apply c2 targs) with
          | [] => []
          | head :: tail =>
              if pargs.length == tail.length then
                (matchArgs pargs tail).filterMap fun tb =>
                  mergeBindings [(name, head)] tb
              else
                []
      | none => []
    else []
  | .lambda bodyPat, .lambda bodyConcrete =>
    matchPattern bodyPat bodyConcrete
  | .multiLambda npat bodyPat, .multiLambda nconc bodyConcrete =>
    if npat == nconc then matchPattern bodyPat bodyConcrete
    else []
  | .collection ct1 pelems rest1, .collection ct2 telems _rest2 =>
    if ct1 == ct2 then matchBag pelems rest1 ct1 telems
    else []
  | .subst pbody prepl, .subst tbody trepl =>
    (matchPattern pbody tbody).flatMap fun b1 =>
      (matchPattern prepl trepl).filterMap fun b2 =>
        mergeBindings b1 b2
  | _, _ => []
termination_by sizeOf pat

end

/-- Shared MeTTa-family matcher:
first tries exact structural matching (`matchPattern`), then supports the
standard `cons` pattern decomposition over tuple/list-shaped terms. -/
def matchPatternMeTTa (pat term : Pattern) : List Bindings :=
  let direct := matchPattern pat term
  if !direct.isEmpty then
    direct
  else
    match pat with
    | .apply "cons" [patHead, patTail] =>
        match tupleElems term with
        | [] => []
        | headVal :: tailVals =>
            let tailVal := tupleOfElems tailVals
            (matchPatternMeTTa patHead headVal).flatMap fun bsHead =>
              (matchPatternMeTTa patTail tailVal).filterMap fun bsTail =>
                mergeBindings bsHead bsTail
    | _ => []
termination_by sizeOf pat

theorem matchPatternMeTTa_dollar_head_application :
    matchPatternMeTTa
        (.apply "$pred" [.fvar "x"])
        (.apply "frog" [.apply "sam" []]) =
      [[("x", .apply "sam" []), ("pred", .apply "frog" [])]] := by
  native_decide

theorem matchPatternMeTTa_nested_dollar_head_application :
    matchPatternMeTTa
        (.apply "Expr" [.apply "$f" [.apply "leaf2" []], .apply "leaf3" []])
        (.apply "Expr" [.apply "leaf1" [.apply "leaf2" []], .apply "leaf3" []]) =
      [[("f", .apply "leaf1" [])]] := by
  native_decide

def applyBindings (bindings : Bindings) (rhs : Pattern) : Pattern :=
  match rhs with
  | .fvar x =>
    match bindings.find? (·.1 == x) with
    | some (_, val) => val
    | none => .fvar x
  | .bvar n => .bvar n
  | .apply c [] =>
    if c.startsWith "$" then
      let name := (c.drop 1).toString
      if name.isEmpty then
        .apply c []
      else
        match bindings.find? (·.1 == name) with
        | some (_, val) => val
        | none => .apply c []
    else
      .apply c []
  | .apply c args =>
    .apply c (args.map (applyBindings bindings))
  | .lambda body =>
    .lambda (applyBindings bindings body)
  | .multiLambda n body =>
    .multiLambda n (applyBindings bindings body)
  | .subst body repl =>
    let body' := applyBindings bindings body
    let repl' := applyBindings bindings repl
    openBVar 0 repl' body'
  | .collection ct elems rest =>
    let elems' := elems.map (applyBindings bindings)
    let restElems := match rest with
      | some rv =>
        match bindings.find? (·.1 == rv) with
        | some (_, .collection _ relems _) => relems
        | _ => []
      | none => []
    .collection ct (elems' ++ restElems) none
termination_by sizeOf rhs

mutual

def isMatchCorrectAux : Pattern → Bool
  | .fvar _           => true
  | .bvar _           => true
  | .apply _ args     => isMatchCorrectListAux args
  | .lambda body      => isMatchCorrectAux body
  | .multiLambda _ b  => isMatchCorrectAux b
  | .subst _ _        => false
  | .collection _ _ _ => false

def isMatchCorrectListAux : List Pattern → Bool
  | []      => true
  | p :: ps => isMatchCorrectAux p && isMatchCorrectListAux ps

end

def Pattern.isMatchCorrect (p : Pattern) : Bool := isMatchCorrectAux p

def applyRule (rule : RewriteRule) (term : Pattern) : List Pattern :=
  if rule.premises.isEmpty then
    (matchPattern rule.left term).map fun b => applyBindings b rule.right
  else []

def rewriteStep (lang : LanguageDef) (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRule rule term

def rewriteToNormalForm (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteStep lang term with
    | [] => term
    | q :: _ => rewriteToNormalForm lang q fuel

end MeTTailCore.MeTTaIL.Match
