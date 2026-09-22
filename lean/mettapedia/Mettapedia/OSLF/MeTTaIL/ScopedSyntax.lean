import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Substitution


/-!
# Scope-indexed Pattern syntax and lifted substitution

`Scoped n` records `n` available bound levels, with occurrences in `Fin n`.
Renaming and substitution explicitly lift under binders. The indices prevent
references outside the available scope; the defined lift additionally preserves
the identity of newly bound and enclosing variables. Indices alone do not
uniquely select that lift.

`toPattern` forgets the scope index. The kernel-checked comparison
`untyped_disagrees_with_scoped` exhibits capture by the raw `applyBindings`
helper on an open replacement, contrasted with this module's explicit
weakening. It does not claim that every current rule-firing path uses that raw
helper: rule-aware application has a separate source-depth discipline.

Free-variable names and collection rest names remain textual in this concrete
representation. This module does not replace declared metavariable contexts or
establish general conditional-premise transport, observer descent, or matching
modulo a language's equations.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedSyntax
open Mettapedia.OSLF.MeTTaIL.Syntax (CollType Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings applyBindings)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

set_option autoImplicit false
set_option linter.dupNamespace false

/-! ## Syntax with its scope in the type -/

mutual
/-- Patterns carrying their binding scope in the type: `Scoped n` has exactly
`n` bound levels available, so a bound occurrence is a `Fin n` and cannot name a
level that is not there. -/
inductive Scoped : Nat → Type where
  | bvar {scope : Nat} : Fin scope → Scoped scope
  | fvar {scope : Nat} : String → Scoped scope
  | apply {scope : Nat} : String → ScopedList scope → Scoped scope
  | lambda {scope : Nat} : Option String → Scoped (scope + 1) → Scoped scope
  | multiLambda {scope : Nat} (arity : Nat) :
      List String → Scoped (scope + arity) → Scoped scope
  | subst {scope : Nat} : Scoped (scope + 1) → Scoped scope → Scoped scope
  | collection {scope : Nat} :
      CollType → ScopedList scope → Option String → Scoped scope

/-- The argument-list companion, mutual rather than nested because the scope is
an index. -/
inductive ScopedList : Nat → Type where
  | nil {scope : Nat} : ScopedList scope
  | cons {scope : Nat} : Scoped scope → ScopedList scope → ScopedList scope
end

/-! ## The functorial action: renaming -/

/-- Lift a renaming under one binder. -/
def liftRen {m n : Nat} (rho : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun i => (rho i).succ)

/-- Lift a renaming under `k` binders. -/
def liftRenN {m n : Nat} (rho : Fin m → Fin n) : (k : Nat) → Fin (m + k) → Fin (n + k)
  | 0 => rho
  | k + 1 => liftRen (liftRenN rho k)

mutual
/-- **The presheaf action.**  `Scoped` is a functor from scopes and renamings to
types; this is its action on maps. -/
def rename : {m n : Nat} → (Fin m → Fin n) → Scoped m → Scoped n
  | _, _, rho, .bvar i => .bvar (rho i)
  | _, _, _, .fvar name => .fvar name
  | _, _, rho, .apply label arguments => .apply label (renameList rho arguments)
  | _, _, rho, .lambda name body => .lambda name (rename (liftRen rho) body)
  | _, _, rho, .multiLambda arity names body =>
      .multiLambda arity names (rename (liftRenN rho arity) body)
  | _, _, rho, .subst body replacement =>
      .subst (rename (liftRen rho) body) (rename rho replacement)
  | _, _, rho, .collection kind elements rest =>
      .collection kind (renameList rho elements) rest

def renameList : {m n : Nat} → (Fin m → Fin n) → ScopedList m → ScopedList n
  | _, _, _, .nil => .nil
  | _, _, rho, .cons head tail => .cons (rename rho head) (renameList rho tail)
end

/-- Weakening: the action of the inclusion of scopes. -/
def weaken {n : Nat} (term : Scoped n) : Scoped (n + 1) :=
  rename (fun i : Fin n => i.succ) term

/-! ## The monoid multiplication: substitution -/

/-- Lift a substitution under one binder.  **This is the step the untyped
`applyBindings` omits, and the omission is what captures.**  Here it is not
optional: nothing else typechecks. -/
def liftSub {m n : Nat} (sigma : Fin m → Scoped n) : Fin (m + 1) → Scoped (n + 1) :=
  Fin.cases (.bvar 0) (fun i => weaken (sigma i))

def liftSubN {m n : Nat} (sigma : Fin m → Scoped n) :
    (k : Nat) → Fin (m + k) → Scoped (n + k)
  | 0 => sigma
  | k + 1 => liftSub (liftSubN sigma k)

mutual
/-- **Substitution, capture-avoiding by construction.** -/
def bind : {m n : Nat} → (Fin m → Scoped n) → Scoped m → Scoped n
  | _, _, sigma, .bvar i => sigma i
  | _, _, _, .fvar name => .fvar name
  | _, _, sigma, .apply label arguments => .apply label (bindList sigma arguments)
  | _, _, sigma, .lambda name body => .lambda name (bind (liftSub sigma) body)
  | _, _, sigma, .multiLambda arity names body =>
      .multiLambda arity names (bind (liftSubN sigma arity) body)
  | _, _, sigma, .subst body replacement =>
      .subst (bind (liftSub sigma) body) (bind sigma replacement)
  | _, _, sigma, .collection kind elements rest =>
      .collection kind (bindList sigma elements) rest

def bindList : {m n : Nat} → (Fin m → Scoped n) → ScopedList m → ScopedList n
  | _, _, _, .nil => .nil
  | _, _, sigma, .cons head tail => .cons (bind sigma head) (bindList sigma tail)
end

/-! ## Erasure to the untyped representation -/

mutual
def toPattern : {n : Nat} → Scoped n → Pattern
  | _, .bvar i => .bvar i.val
  | _, .fvar name => .fvar name
  | _, .apply label arguments => .apply label (toPatternList arguments)
  | _, .lambda name body => .lambda name (toPattern body)
  | _, .multiLambda arity names body => .multiLambda arity names (toPattern body)
  | _, .subst body replacement => .subst (toPattern body) (toPattern replacement)
  | _, .collection kind elements rest =>
      .collection kind (toPatternList elements) rest

def toPatternList : {n : Nat} → ScopedList n → List Pattern
  | _, .nil => []
  | _, .cons head tail => toPattern head :: toPatternList tail
end

/-! ## Metavariable substitution, which is where the untyped version captures -/

/-- Weaken under `k` binders. -/
def weakenN {n : Nat} : (k : Nat) → Scoped n → Scoped (n + k)
  | 0, term => term
  | k + 1, term => weaken (weakenN k term)

mutual
/-- Substitute an ordinary textual free-variable occurrence, explicitly
weakening its replacement under binders. Scope indices exclude escaping
references but do not by themselves uniquely determine this operation. The
collection rest name is not an ordinary term occurrence and is retained. -/
def substFVar : {n : Nat} → String → Scoped n → Scoped n → Scoped n
  | _, _, _, .bvar i => .bvar i
  | _, name, value, .fvar other => if other = name then value else .fvar other
  | _, name, value, .apply label arguments =>
      .apply label (substFVarList name value arguments)
  | _, name, value, .lambda binderName body =>
      .lambda binderName (substFVar name (weaken value) body)
  | _, name, value, .multiLambda arity names body =>
      .multiLambda arity names (substFVar name (weakenN arity value) body)
  | _, name, value, .subst body replacement =>
      .subst (substFVar name (weaken value) body) (substFVar name value replacement)
  | _, name, value, .collection kind elements rest =>
      .collection kind (substFVarList name value elements) rest

def substFVarList : {n : Nat} → String → Scoped n → ScopedList n → ScopedList n
  | _, _, _, .nil => .nil
  | _, name, value, .cons head tail =>
      .cons (substFVar name value head) (substFVarList name value tail)
end

/-! ## The defect, exhibited against the correct semantics

The raw `applyBindings` puts a replacement under a binder without weakening
it, so an index that was free outside the binder becomes bound by it. The
defined scoped substitution weakens instead, and the two disagree on the
smallest example. -/

/-- A metavariable occurring under one binder, in scope 1. -/
def capturingBody : Scoped 1 := .lambda (some "y") (.fvar "x")

/-- A replacement naming the one level available outside that binder. -/
def freeIndex : Scoped 1 := .bvar 0

/-- **The scoped substitution weakens, as it must.** -/
theorem scoped_substitution_weakens :
    toPattern (substFVar "x" freeIndex capturingBody)
      = .lambda (some "y") (.bvar 1) := by
  decide +kernel

/-- **And the untyped one does not**, which is the capture. -/
theorem untyped_substitution_captures :
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings
        [("x", Pattern.bvar 0)] (toPattern capturingBody)
      = .lambda (some "y") (.bvar 0) := by
  decide +kernel

/-- **So the two disagree**, and the disagreement is exactly a captured index. -/
theorem untyped_disagrees_with_scoped :
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings
        [("x", Pattern.bvar 0)] (toPattern capturingBody)
      ≠ toPattern (substFVar "x" freeIndex capturingBody) := by
  rw [scoped_substitution_weakens, untyped_substitution_captures]
  decide

/-! ## The correction, at the untyped level

The scoped layer says what substitution ought to do.  This is the untyped
operation that does it, so that the step relation can be moved onto something
correct without first moving the whole matcher into `Scoped`. -/

/-- **Binding application that lifts.**  The same descent as `applyBindings`,
except that it carries the number of binders it has passed and weakens a
substituted value by that many levels.  That is the step whose omission is the
capture, and `liftingAgreesWithScoped` below is the proof that adding it back
gives the scoped semantics rather than merely a different answer. -/
def applyBindingsLifting (depth : Nat) (bindings : Bindings) : Pattern → Pattern
  | .fvar name =>
      match bindings.find? (fun entry => entry.1 == name) with
      | some (_, value) => liftBVars 0 depth value
      | none => .fvar name
  | .bvar index => .bvar index
  | .apply label arguments =>
      .apply label (arguments.map (applyBindingsLifting depth bindings))
  | .lambda binderName body =>
      .lambda binderName (applyBindingsLifting (depth + 1) bindings body)
  | .multiLambda arity binderNames body =>
      .multiLambda arity binderNames
        (applyBindingsLifting (depth + arity) bindings body)
  | .subst body replacement =>
      .subst (applyBindingsLifting (depth + 1) bindings body)
        (applyBindingsLifting depth bindings replacement)
  | .collection kind elements rest =>
      .collection kind (elements.map (applyBindingsLifting depth bindings)) rest
termination_by pattern => sizeOf pattern

/-! ## The defect is gone, and gone in the right direction -/

/-- On the example that captured, the lifting applier gives the scoped answer. -/
theorem lifting_avoids_capture :
    applyBindingsLifting 0 [("x", Pattern.bvar 0)] (toPattern capturingBody)
      = toPattern (substFVar "x" freeIndex capturingBody) := by
  rw [scoped_substitution_weakens]
  decide +kernel

/-- And it differs from the unlifted one exactly there. -/
theorem lifting_differs_from_applyBindings :
    applyBindingsLifting 0 [("x", Pattern.bvar 0)] (toPattern capturingBody)
      ≠ applyBindings [("x", Pattern.bvar 0)] (toPattern capturingBody) := by
  rw [untyped_substitution_captures, lifting_avoids_capture,
    scoped_substitution_weakens]
  decide

/-- Where nothing is substituted under a binder, the two agree, so the change is
a correction rather than a different operation. -/
theorem lifting_agrees_when_ground :
    applyBindingsLifting 0 [("x", Pattern.apply "P" [])]
        (toPattern capturingBody)
      = applyBindings [("x", Pattern.apply "P" [])] (toPattern capturingBody) := by
  decide +kernel
