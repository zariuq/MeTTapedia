import Mathlib.Data.Fin.Basic

/-!
# External dependent types, terms and contextual declarations

This presentation has an external judgment of type formation. A context may
extend by any authored type, including a dependent function or pair type.
The syntax does not contain an internal universe or identity-type constructor,
and is independent of any semantic carrier or interpretation.

Primitive families and terms have independently authored parameter telescopes.
Ranks require every declaration header to use only earlier primitive symbols.
The rank condition concerns syntax, rather than assuming that a whole term or
typed substitution has a semantic interpretation.

This module owns the universe-free external dependent presentation. It neither
changes nor erases the universe witnesses of the separate parameterized
Pi/Sigma/identity calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

universe u

/-- Primitive symbols specify their number of ordered contextual arguments. -/
structure Symbols where
  TypeSymbol : Type u
  TermSymbol : Type u
  typeArity : TypeSymbol → Nat
  termArity : TermSymbol → Nat

mutual

/-- Types are syntax, not semantic families packaged as syntax. -/
inductive TypeExpr (S : Symbols.{u}) : Nat → Type u where
  | family {n : Nat} (symbol : S.TypeSymbol)
      (arguments : Fin (S.typeArity symbol) → TermExpr S n) : TypeExpr S n
  | pi {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) : TypeExpr S n
  | sigma {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) : TypeExpr S n

/-- Annotations identify the domains used by each dependent rule. The pair
eliminator's motive binds a complete pair; its branch binds both components. -/
inductive TermExpr (S : Symbols.{u}) : Nat → Type u where
  | var {n : Nat} (index : Fin n) : TermExpr S n
  | primitive {n : Nat} (symbol : S.TermSymbol)
      (arguments : Fin (S.termArity symbol) → TermExpr S n) : TermExpr S n
  | lam {n : Nat} (domain : TypeExpr S n) (codomain : TypeExpr S (n + 1))
      (body : TermExpr S (n + 1)) : TermExpr S n
  | app {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
      (function argument : TermExpr S n) : TermExpr S n
  | pair {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
      (first second : TermExpr S n) : TermExpr S n
  | fst {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
      (pair : TermExpr S n) : TermExpr S n
  | snd {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
      (pair : TermExpr S n) : TermExpr S n
  | sigmaElim {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
      (motive : TypeExpr S (n + 1)) (branch : TermExpr S (n + 2))
      (pair : TermExpr S n) : TermExpr S n

end

/-- An arbitrary variable-type telescope, authored independently of formation. -/
inductive ContextExpr (S : Symbols.{u}) : Nat → Type u where
  | nil : ContextExpr S 0
  | snoc {n : Nat} (previous : ContextExpr S n) (type : TypeExpr S n) : ContextExpr S (n + 1)

variable {S : Symbols.{u}}

mutual

/-- Every primitive occurrence in a type precedes the supplied rank. -/
def TypeExpr.before (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (bound : Nat) : {n : Nat} → TypeExpr S n → Prop
  | _, .family symbol arguments => typeRank symbol < bound ∧
      ∀ position, TermExpr.before typeRank termRank bound (arguments position)
  | _, .pi domain body => domain.before typeRank termRank bound ∧
      body.before typeRank termRank bound
  | _, .sigma domain body => domain.before typeRank termRank bound ∧
      body.before typeRank termRank bound

/-- Annotations and full dependent motives participate in declaration order. -/
def TermExpr.before (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (bound : Nat) : {n : Nat} → TermExpr S n → Prop
  | _, .var _ => True
  | _, .primitive symbol arguments => termRank symbol < bound ∧
      ∀ position, TermExpr.before typeRank termRank bound (arguments position)
  | _, .lam domain codomain body => domain.before typeRank termRank bound ∧
      codomain.before typeRank termRank bound ∧ body.before typeRank termRank bound
  | _, .app domain body function argument => domain.before typeRank termRank bound ∧
      body.before typeRank termRank bound ∧ function.before typeRank termRank bound ∧
      argument.before typeRank termRank bound
  | _, .pair domain body first second => domain.before typeRank termRank bound ∧
      body.before typeRank termRank bound ∧ first.before typeRank termRank bound ∧
      second.before typeRank termRank bound
  | _, .fst domain body pair => domain.before typeRank termRank bound ∧
      body.before typeRank termRank bound ∧ pair.before typeRank termRank bound
  | _, .snd domain body pair => domain.before typeRank termRank bound ∧
      body.before typeRank termRank bound ∧ pair.before typeRank termRank bound
  | _, .sigmaElim domain body motive branch pair => domain.before typeRank termRank bound ∧
      body.before typeRank termRank bound ∧ motive.before typeRank termRank bound ∧
      branch.before typeRank termRank bound ∧ pair.before typeRank termRank bound

end

def ContextExpr.before (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (bound : Nat) : {n : Nat} → ContextExpr S n → Prop
  | _, .nil => True
  | _, .snoc previous type => previous.before typeRank termRank bound ∧
      type.before typeRank termRank bound

/-- Ordered declaration headers contain raw syntax and its dependency bounds.
Formation and typing of the headers are separate generated judgments. -/
structure Signature (S : Symbols.{u}) where
  typeRank : S.TypeSymbol → Nat
  termRank : S.TermSymbol → Nat
  typeParameters : (symbol : S.TypeSymbol) → ContextExpr S (S.typeArity symbol)
  termParameters : (symbol : S.TermSymbol) → ContextExpr S (S.termArity symbol)
  termResult : (symbol : S.TermSymbol) → TypeExpr S (S.termArity symbol)
  typeParameters_before : ∀ symbol,
    (typeParameters symbol).before typeRank termRank (typeRank symbol)
  termParameters_before : ∀ symbol,
    (termParameters symbol).before typeRank termRank (termRank symbol)
  termResult_before : ∀ symbol,
    (termResult symbol).before typeRank termRank (termRank symbol)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
