import MeTTailCore.MeTTaIL.Syntax

namespace MeTTailCore.MeTTaIL.Substitution

open MeTTailCore.MeTTaIL.Syntax

abbrev SubstEnv := List (String × Pattern)

namespace SubstEnv

def empty : SubstEnv := []

def extend (env : SubstEnv) (name : String) (term : Pattern) : SubstEnv :=
  (name, term) :: env

def find (env : SubstEnv) (name : String) : Option Pattern :=
  match env.find? (fun p => p.1 == name) with
  | some (_, term) => some term
  | none => none

end SubstEnv

/-- Replace `BVar k` with term `u` (opening a binder scope). -/
def openBVar (k : Nat) (u : Pattern) : Pattern → Pattern
  | .bvar n => if n == k then u else .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map (openBVar k u))
  | .lambda body => .lambda (openBVar (k + 1) u body)
  | .multiLambda n body => .multiLambda n (openBVar (k + n) u body)
  | .subst body repl => .subst (openBVar (k + 1) u body) (openBVar k u repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (openBVar k u)) rest
termination_by p => sizeOf p

/-- Replace `FVar x` with `BVar k` (abstracting a free variable). -/
def closeFVar (k : Nat) (x : String) : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar y => if y == x then .bvar k else .fvar y
  | .apply c args => .apply c (args.map (closeFVar k x))
  | .lambda body => .lambda (closeFVar (k + 1) x body)
  | .multiLambda n body => .multiLambda n (closeFVar (k + n) x body)
  | .subst body repl => .subst (closeFVar (k + 1) x body) (closeFVar k x repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (closeFVar k x)) rest
termination_by p => sizeOf p

/-- Shift bound variable indices ≥ `cutoff` by `shift`. -/
def liftBVars (cutoff shift : Nat) : Pattern → Pattern
  | .bvar n => if n >= cutoff then .bvar (n + shift) else .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map (liftBVars cutoff shift))
  | .lambda body => .lambda (liftBVars (cutoff + 1) shift body)
  | .multiLambda n body => .multiLambda n (liftBVars (cutoff + n) shift body)
  | .subst body repl =>
    .subst (liftBVars (cutoff + 1) shift body) (liftBVars cutoff shift repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (liftBVars cutoff shift)) rest
termination_by p => sizeOf p

/-! `openBVar` opens a locally nameless binder but does not remove an
ambient de Bruijn level. Executing an explicit `Pattern.subst` does remove its
bound level, so it uses the separate instantiation operation below. -/

/-- Eliminate the bound-variable level at `depth` from `body`, replacing its
occurrences with `replacement`. Inner-bound indices are preserved, the
replacement is lifted beneath inner binders, and indices outside the removed
level are decremented. -/
def instantiateBVarAt (depth : Nat) (replacement : Pattern) : Pattern → Pattern
  | .bvar index =>
      if index < depth then
        .bvar index
      else if index = depth then
        liftBVars 0 depth replacement
      else
        .bvar (index - 1)
  | .fvar name => .fvar name
  | .apply constructor args =>
      .apply constructor (args.map (instantiateBVarAt depth replacement))
  | .lambda body =>
      .lambda (instantiateBVarAt (depth + 1) replacement body)
  | .multiLambda arity body =>
      .multiLambda arity (instantiateBVarAt (depth + arity) replacement body)
  | .subst body nestedReplacement =>
      .subst (instantiateBVarAt (depth + 1) replacement body)
        (instantiateBVarAt depth replacement nestedReplacement)
  | .collection collectionType elems rest =>
      .collection collectionType
        (elems.map (instantiateBVarAt depth replacement)) rest
termination_by body => sizeOf body

/-- Execute the binder-eliminating substitution represented by
`Pattern.subst body replacement`. -/
def instantiateBVar (replacement body : Pattern) : Pattern :=
  instantiateBVarAt 0 replacement body

section InstantiateBVarParityFixtures

private def kData : Pattern := .apply "K" []

-- Target replacement and removal of the surrounding de Bruijn level.
#guard decide (instantiateBVar kData (.bvar 0) = kData)
#guard decide (instantiateBVar kData (.bvar 1) = .bvar 0)

-- Insertion beneath a binder lifts an ambient replacement, while an index
-- owned by that inner binder remains unchanged.
#guard decide
    (instantiateBVar (.bvar 0) (.lambda (.bvar 1)) = .lambda (.bvar 1))
#guard decide
    (instantiateBVar kData (.lambda (.bvar 0)) = .lambda (.bvar 0))

-- The same three index classes are handled across a two-binder scope.
#guard decide
    (instantiateBVar (.bvar 0)
      (.multiLambda 2 (.apply "T" [.bvar 0, .bvar 1, .bvar 2, .bvar 3])) =
      .multiLambda 2 (.apply "T" [.bvar 0, .bvar 1, .bvar 2, .bvar 2]))

-- A nested explicit substitution contributes one binder only in its body.
#guard decide
    (instantiateBVar kData
      (.subst (.apply "T" [.bvar 0, .bvar 1, .bvar 2])
        (.apply "U" [.bvar 0, .bvar 1])) =
      .subst (.apply "T" [.bvar 0, kData, .bvar 1])
        (.apply "U" [kData, .bvar 0]))

end InstantiateBVarParityFixtures

/-- Apply substitution environment to a pattern. -/
def applySubst (env : SubstEnv) : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar name =>
    match env.find name with
    | some replacement => replacement
    | none => .fvar name
  | .apply constructor args =>
    .apply constructor (args.map (applySubst env))
  | .lambda body =>
    .lambda (applySubst env body)
  | .multiLambda n body =>
    .multiLambda n (applySubst env body)
  | .subst body replacement =>
    let body' := applySubst env body
    let repl' := applySubst env replacement
    instantiateBVar repl' body'
  | .collection ct elements rest =>
    .collection ct (elements.map (applySubst env)) rest
termination_by p => sizeOf p

section ApplySubstExplicitBinderParityFixtures

private def kReplacement : Pattern := .apply "K" []

#guard decide
    (applySubst SubstEnv.empty
      (.lambda (.subst (.bvar 1) kReplacement)) = .lambda (.bvar 0))

-- Eager evaluation eliminates the inner explicit binder before the outer one.
#guard decide
    (applySubst SubstEnv.empty
      (.subst
        (.subst (.apply "T" [.bvar 0, .bvar 1, .bvar 2]) (.bvar 0))
        kReplacement) =
      .apply "T" [kReplacement, kReplacement, .bvar 0])

end ApplySubstExplicitBinderParityFixtures

def freeVars : Pattern → List String
  | .bvar _ => []
  | .fvar name => [name]
  | .apply _ args => args.flatMap freeVars
  | .lambda body => freeVars body
  | .multiLambda _ body => freeVars body
  | .subst body replacement => freeVars body ++ freeVars replacement
  | .collection _ elements _ => elements.flatMap freeVars
termination_by p => sizeOf p

def isFresh (x : String) (p : Pattern) : Bool :=
  !((freeVars p).contains x)

def checkFreshness (fc : FreshnessCondition) : Bool :=
  isFresh fc.varName fc.term

def allVars : Pattern → List String := freeVars

def isGloballyFresh (x : String) (p : Pattern) : Bool := isFresh x p

/-- Apply the ρ-calculus COMM-style substitution. -/
def commSubst (pBody q : Pattern) : Pattern :=
  openBVar 0 (.apply "NQuote" [q]) pBody

mutual
  def noExplicitSubst : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply _ args => allNoExplicitSubst args
    | .lambda body => noExplicitSubst body
    | .multiLambda _ body => noExplicitSubst body
    | .subst _ _ => false
    | .collection _ elems _ => allNoExplicitSubst elems

  def allNoExplicitSubst : List Pattern → Bool
    | [] => true
    | p :: ps => noExplicitSubst p && allNoExplicitSubst ps
end

mutual
  def lc_at : Nat → Pattern → Bool
    | k, .bvar n => n < k
    | _, .fvar _ => true
    | k, .apply _ args => lc_at_list k args
    | k, .lambda body => lc_at (k + 1) body
    | k, .multiLambda n body => lc_at (k + n) body
    | k, .subst body repl => lc_at (k + 1) body && lc_at k repl
    | k, .collection _ elems _ => lc_at_list k elems

  def lc_at_list : Nat → List Pattern → Bool
    | _, [] => true
    | k, p :: ps => lc_at k p && lc_at_list k ps
end

def lc (p : Pattern) : Bool := lc_at 0 p

end MeTTailCore.MeTTaIL.Substitution
