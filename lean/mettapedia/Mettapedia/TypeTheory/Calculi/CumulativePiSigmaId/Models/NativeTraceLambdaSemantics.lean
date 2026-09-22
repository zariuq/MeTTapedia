import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual

/-!
# Typed trace semantics for the native lambda/application fragment

This module gives the actual native variable, lambda and application syntax a
typed denotation in the contextual model of Aczel trace products.  A semantic
context records the family and projection denoted by every de Bruijn variable.
Context extension therefore supplies the genuine newest projection and pulls
older projections back along weakening.

The syntax carries no source proof node and no semantic value. Erasure lands
in the existing cumulative-tower terms, while denotation is a separate indexed
relation. Supplied derivations retain semantic binder domains absent from an
unannotated native lambda. A resulting product-family code alone need not
determine that domain. This relation is not indexed by a formed native typing
derivation and does not establish arbitrary native conversion soundness.
No untyped universal domain or interpretation of arbitrary native constants
is introduced.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceLambdaSemantics

open Presentation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension extensionSubstitution)

universe u

/-- A semantic telescope for a native scope of length `n`.  Its environment
type is the meaning of the whole telescope; every raw variable position has
an actual set family and its projection section. -/
structure Context (n : Nat) where
  Environment : Type (u + 1)
  family : Fin n → SetFamily Environment
  projection : (index : Fin n) → Section (family index)

def Context.nil : Context 0 where
  Environment := PUnit
  family := fun index => Fin.elim0 index
  projection := fun index => Fin.elim0 index

/-- Context comprehension, aligned with the tower syntax's newest variable at
de Bruijn index zero. -/
def Context.snoc {n : Nat} (context : Context.{u} n)
    (a : SetFamily context.Environment) : Context (n + 1) where
  Environment := Extension a
  family := Fin.cases (fun point => a point.1)
    (fun index point => context.family index point.1)
  projection := Fin.cases (fun point => point.2)
    (fun index point => context.projection index point.1)

@[simp] theorem Context.snoc_family_zero {n : Nat} (context : Context.{u} n)
    (a : SetFamily context.Environment) :
    (context.snoc a).family 0 = fun point => a point.1 := rfl

@[simp] theorem Context.snoc_family_succ {n : Nat} (context : Context.{u} n)
    (a : SetFamily context.Environment) (index : Fin n) :
    (context.snoc a).family index.succ = fun point => context.family index point.1 := rfl

@[simp] theorem Context.snoc_projection_zero {n : Nat} (context : Context.{u} n)
    (a : SetFamily context.Environment) :
    (context.snoc a).projection 0 = fun (point : Extension a) => point.2 := rfl

@[simp] theorem Context.snoc_projection_succ {n : Nat} (context : Context.{u} n)
    (a : SetFamily context.Environment) (index : Fin n) :
    (context.snoc a).projection index.succ =
      fun (point : Extension a) => context.projection index point.1 := rfl

/-- Exactly the native lambda/application syntax fragment.  In particular,
there is no constructor carrying a source proof or a denotation. -/
inductive Tm : Nat → Type where
  | var {n : Nat} (index : Fin n) : Tm n
  | lam {n : Nat} (body : Tm (n + 1)) : Tm n
  | app {n : Nat} (function argument : Tm n) : Tm n
  deriving DecidableEq

/-- Forget only the intrinsic fragment boundary, retaining the exact native
syntax tree. -/
def Tm.erase {n : Nat} : Tm n → Tower.Tm n
  | .var index => .var index
  | .lam body => .lam body.erase
  | .app function argument => .app function.erase argument.erase

/-- Recognize the fragment inside an existing native term.  Native constants,
types, pairs and identity constructors are rejected rather than hidden behind
an opaque node. -/
def Tm.ofTower? {n : Nat} : Tower.Tm n → Option (Tm n)
  | .var index => some (.var index)
  | .lam body => return .lam (← Tm.ofTower? body)
  | .app function argument =>
      return .app (← Tm.ofTower? function) (← Tm.ofTower? argument)
  | _ => none

@[simp] theorem Tm.ofTower?_erase {n : Nat} (term : Tm n) :
    Tm.ofTower? term.erase = some term := by
  induction term with
  | var => rfl
  | lam body inductionHypothesis => simp [Tm.erase, Tm.ofTower?, inductionHypothesis]
  | app function argument functionInduction argumentInduction =>
      simp [Tm.erase, Tm.ofTower?, functionInduction, argumentInduction]

@[simp] theorem Tm.ofTower?_rejects_const {n : Nat} (name : DeclName) :
    Tm.ofTower? (Presentation.Tm.const name : Tower.Tm n) = none := rfl

theorem Tm.ofTower?_sound {n : Nat} {native : Tower.Tm n} {term : Tm n}
    (success : Tm.ofTower? native = some term) : term.erase = native := by
  induction native with
  | var index =>
      simp only [Tm.ofTower?, Option.some.injEq] at success
      subst term
      rfl
  | lam body inductionHypothesis =>
      cases recognized : Tm.ofTower? body with
      | none => simp [Tm.ofTower?, recognized] at success
      | some recognizedBody =>
          simp [Tm.ofTower?, recognized] at success
          subst term
          exact congrArg (fun inner : Tower.Tm _ => Presentation.Tm.lam inner)
            (inductionHypothesis recognized)
  | app function argument functionInduction argumentInduction =>
      cases functionRecognized : Tm.ofTower? function with
      | none => simp [Tm.ofTower?, functionRecognized] at success
      | some recognizedFunction =>
          cases argumentRecognized : Tm.ofTower? argument with
          | none => simp [Tm.ofTower?, functionRecognized, argumentRecognized] at success
          | some recognizedArgument =>
              simp [Tm.ofTower?, functionRecognized, argumentRecognized] at success
              subst term
              exact congrArg₂ (fun f x : Tower.Tm _ => Presentation.Tm.app f x)
                (functionInduction functionRecognized)
                (argumentInduction argumentRecognized)
  | const | head | pi | sigma | id | pair | fst | snd | refl =>
      simp [Tm.ofTower?] at success

/-- Capture-avoiding renaming for the fragment. -/
def Tm.rename {n m : Nat} (rho : Ren n m) : Tm n → Tm m
  | .var index => .var (rho index)
  | .lam body => .lam (body.rename (liftRen rho))
  | .app function argument => .app (function.rename rho) (argument.rename rho)

/-- Lift a fragment substitution beneath one binder. -/
def liftSubTm {n m : Nat} (sigma : Fin n → Tm m) : Fin (n + 1) → Tm (m + 1) :=
  Fin.cases (.var 0) (fun index => (sigma index).rename wk)

/-- Capture-avoiding simultaneous substitution for the fragment. -/
def Tm.subst {n m : Nat} (sigma : Fin n → Tm m) : Tm n → Tm m
  | .var index => sigma index
  | .lam body => .lam (body.subst (liftSubTm sigma))
  | .app function argument => .app (function.subst sigma) (argument.subst sigma)

@[simp] theorem Tm.erase_rename {n m : Nat} (rho : Ren n m) (term : Tm n) :
    (term.rename rho).erase = Presentation.rename rho term.erase := by
  induction term generalizing m with
  | var => rfl
  | lam body inductionHypothesis =>
      simp only [Tm.rename, Tm.erase, Presentation.rename, inductionHypothesis]
  | app function argument functionInduction argumentInduction =>
      simp only [Tm.rename, Tm.erase, Presentation.rename,
        functionInduction, argumentInduction]

@[simp] theorem erase_liftSubTm {n m : Nat} (sigma : Fin n → Tm m)
    (index : Fin (n + 1)) :
    (liftSubTm sigma index).erase = liftSub (fun i => (sigma i).erase) index := by
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · simp only [liftSubTm, Fin.cases_succ, Tm.erase_rename, liftSub]

@[simp] theorem Tm.erase_subst {n m : Nat} (sigma : Fin n → Tm m) (term : Tm n) :
    (term.subst sigma).erase = Presentation.subst (fun i => (sigma i).erase) term.erase := by
  induction term generalizing m with
  | var index => rfl
  | lam body inductionHypothesis =>
      simp only [Tm.subst, Tm.erase, Presentation.subst, inductionHypothesis]
      exact congrArg (fun inner : Tower.Tm (m + 1) => Presentation.Tm.lam inner)
        (congrArg (fun tau => Presentation.subst tau body.erase)
          (funext (erase_liftSubTm sigma)))
  | app function argument functionInduction argumentInduction =>
      simp only [Tm.subst, Tm.erase, Presentation.subst,
        functionInduction, argumentInduction]

/-- Set-family-indexed denotation of fragment syntax. Each abstraction
derivation supplies its domain; equality of product-family codes need not
recover it. The raw term itself remains unannotated. -/
inductive Denotes : {n : Nat} → (context : Context.{u} n) →
    (term : Tm n) → (a : SetFamily context.Environment) → Section a → Prop where
  | var {n : Nat} (context : Context.{u} n) (index : Fin n) :
      Denotes context (.var index) (context.family index) (context.projection index)
  | lam {n : Nat} {context : Context.{u} n} {a : SetFamily context.Environment}
      {b : SetFamily (Extension a)} {body : Tm (n + 1)} {value : Section b} :
      Denotes (context.snoc a) body b value →
      Denotes context (.lam body) (ZFSetTraceContextual.piFamily a b)
        (ZFSetTraceContextual.lam value)
  | app {n : Nat} {context : Context.{u} n} {a : SetFamily context.Environment}
      {b : SetFamily (Extension a)} {function argument : Tm n}
      {functionValue : Section (ZFSetTraceContextual.piFamily a b)}
      {argumentValue : Section a} :
      Denotes context function (ZFSetTraceContextual.piFamily a b) functionValue →
      Denotes context argument a argumentValue →
      Denotes context (.app function argument)
        (fun environment => b ⟨environment, argumentValue environment⟩)
        (ZFSetTraceContextual.app functionValue argumentValue)

/-- Transport along literal family equality. This does not install a native
conversion rule or establish preservation by arbitrary native computation. -/
theorem Denotes.cast {n : Nat} {context : Context.{u} n} {term : Tm n}
    {a b : SetFamily context.Environment} {value : Section a}
    (meaning : Denotes context term a value) (equal : a = b) :
    Denotes context term b (equal ▸ value) := by
  cases equal
  exact meaning

/-- Equality changes only the section indexing an existing interpretation. -/
theorem Denotes.change_value {n : Nat} {context : Context.{u} n} {term : Tm n}
    {family : SetFamily context.Environment} {first second : Section family}
    (meaning : Denotes context term family first) (equal : first = second) :
    Denotes context term family second := by
  cases equal
  exact meaning

/-- Native beta is validated by the actual trace application/lambda inverse,
while erasure exposes the corresponding tower redex. -/
theorem beta {n : Nat} {context : Context.{u} n} {a : SetFamily context.Environment}
    {b : SetFamily (Extension a)} {body : Tm (n + 1)} {argument : Tm n}
    {bodyValue : Section b} {argumentValue : Section a}
    (bodyMeaning : Denotes (context.snoc a) body b bodyValue)
    (argumentMeaning : Denotes context argument a argumentValue) :
    Denotes context (.app (.lam body) argument)
      (fun environment => b ⟨environment, argumentValue environment⟩)
      (fun environment => bodyValue ⟨environment, argumentValue environment⟩) := by
  have application := Denotes.app (Denotes.lam bodyMeaning) argumentMeaning
  rw [ZFSetTraceContextual.app_lam] at application
  exact application

theorem beta_erase {n : Nat} {body : Tm (n + 1)} {argument : Tm n} :
    (Tm.app (Tm.lam body) argument).erase = .app (.lam body.erase) argument.erase := rfl

#print axioms Tm.erase_rename
#print axioms Tm.erase_subst
#print axioms Tm.ofTower?_erase
#print axioms Tm.ofTower?_sound
#print axioms Tm.ofTower?_rejects_const
#print axioms Denotes.cast
#print axioms Denotes.change_value
#print axioms beta

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceLambdaSemantics
