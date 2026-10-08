import Mathlib.Data.Fin.Basic

/-!
# Variable-dependent propositions and refinement syntax

Types, terms and propositions are independently authored raw syntax. The
ordinary type of propositions supports first-class predicates; it is not an
internal universe of types. A refinement binds its tested value, and its
introduction term keeps the supplied value. The corresponding generated
judgment retains the separate entailment derivation.

Primitive declarations have ordered contextual parameters. Their ranks bound
all symbol occurrences, including those in predicates and type annotations.
Formation of declaration headers is a separate syntactic obligation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u

structure Symbols where
  TypeSymbol : Type u
  TermSymbol : Type u
  PredicateSymbol : Type u
  typeArity : TypeSymbol → Nat
  termArity : TermSymbol → Nat
  predicateArity : PredicateSymbol → Nat

mutual

inductive TypeExpr (S : Symbols.{u}) : Nat → Type u where
  | family {n : Nat} (symbol : S.TypeSymbol)
      (arguments : Fin (S.typeArity symbol) → TermExpr S n) : TypeExpr S n
  | propositions {n : Nat} : TypeExpr S n
  | pi {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) : TypeExpr S n
  | sigma {n : Nat} (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) : TypeExpr S n
  | comprehension {n : Nat} (domain : TypeExpr S n)
      (predicate : PropExpr S (n + 1)) : TypeExpr S n

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
  | quote {n : Nat} (predicate : PropExpr S n) : TermExpr S n
  | refine {n : Nat} (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
      (value : TermExpr S n) : TermExpr S n
  | forget {n : Nat} (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
      (value : TermExpr S n) : TermExpr S n

inductive PropExpr (S : Symbols.{u}) : Nat → Type u where
  | atom {n : Nat} (symbol : S.PredicateSymbol)
      (arguments : Fin (S.predicateArity symbol) → TermExpr S n) : PropExpr S n
  | truth {n : Nat} : PropExpr S n
  | falsehood {n : Nat} : PropExpr S n
  | and {n : Nat} (first second : PropExpr S n) : PropExpr S n
  | or {n : Nat} (first second : PropExpr S n) : PropExpr S n
  | implies {n : Nat} (antecedent consequent : PropExpr S n) : PropExpr S n
  | all {n : Nat} (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) : PropExpr S n
  | exists {n : Nat} (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) : PropExpr S n
  | holds {n : Nat} (proposition : TermExpr S n) : PropExpr S n
  | image {n : Nat} (type : TypeExpr S n) : PropExpr S n

end

inductive ContextExpr (S : Symbols.{u}) : Nat → Type u where
  | nil : ContextExpr S 0
  | snoc {n : Nat} (previous : ContextExpr S n) (type : TypeExpr S n) : ContextExpr S (n + 1)
  | assume {n : Nat} (previous : ContextExpr S n) (predicate : PropExpr S n) : ContextExpr S n

abbrev Assumptions (S : Symbols.{u}) (n : Nat) := List (PropExpr S n)

variable {S : Symbols.{u}}

mutual

def TypeExpr.before (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (predicateRank : S.PredicateSymbol → Nat) (bound : Nat) : {n : Nat} → TypeExpr S n → Prop
  | _, .family symbol arguments => typeRank symbol < bound ∧
      ∀ position, (arguments position).before typeRank termRank predicateRank bound
  | _, .propositions => True
  | _, .pi domain body => domain.before typeRank termRank predicateRank bound ∧
      body.before typeRank termRank predicateRank bound
  | _, .sigma domain body => domain.before typeRank termRank predicateRank bound ∧
      body.before typeRank termRank predicateRank bound
  | _, .comprehension domain predicate => domain.before typeRank termRank predicateRank bound ∧
      predicate.before typeRank termRank predicateRank bound

def TermExpr.before (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (predicateRank : S.PredicateSymbol → Nat) (bound : Nat) : {n : Nat} → TermExpr S n → Prop
  | _, .var _ => True
  | _, .primitive symbol arguments => termRank symbol < bound ∧
      ∀ position, (arguments position).before typeRank termRank predicateRank bound
  | _, .lam domain codomain body => domain.before typeRank termRank predicateRank bound ∧
      codomain.before typeRank termRank predicateRank bound ∧ body.before typeRank termRank predicateRank bound
  | _, .app domain body function argument => domain.before typeRank termRank predicateRank bound ∧
      body.before typeRank termRank predicateRank bound ∧ function.before typeRank termRank predicateRank bound ∧
      argument.before typeRank termRank predicateRank bound
  | _, .pair domain body first second => domain.before typeRank termRank predicateRank bound ∧
      body.before typeRank termRank predicateRank bound ∧ first.before typeRank termRank predicateRank bound ∧
      second.before typeRank termRank predicateRank bound
  | _, .fst domain body pair => domain.before typeRank termRank predicateRank bound ∧
      body.before typeRank termRank predicateRank bound ∧ pair.before typeRank termRank predicateRank bound
  | _, .snd domain body pair => domain.before typeRank termRank predicateRank bound ∧
      body.before typeRank termRank predicateRank bound ∧ pair.before typeRank termRank predicateRank bound
  | _, .sigmaElim domain body motive branch pair => domain.before typeRank termRank predicateRank bound ∧
      body.before typeRank termRank predicateRank bound ∧ motive.before typeRank termRank predicateRank bound ∧
      branch.before typeRank termRank predicateRank bound ∧ pair.before typeRank termRank predicateRank bound
  | _, .quote predicate => predicate.before typeRank termRank predicateRank bound
  | _, .refine domain predicate value => domain.before typeRank termRank predicateRank bound ∧
      predicate.before typeRank termRank predicateRank bound ∧ value.before typeRank termRank predicateRank bound
  | _, .forget domain predicate value => domain.before typeRank termRank predicateRank bound ∧
      predicate.before typeRank termRank predicateRank bound ∧ value.before typeRank termRank predicateRank bound

def PropExpr.before (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (predicateRank : S.PredicateSymbol → Nat) (bound : Nat) : {n : Nat} → PropExpr S n → Prop
  | _, .atom symbol arguments => predicateRank symbol < bound ∧
      ∀ position, (arguments position).before typeRank termRank predicateRank bound
  | _, .truth => True
  | _, .falsehood => True
  | _, .and first second => first.before typeRank termRank predicateRank bound ∧
      second.before typeRank termRank predicateRank bound
  | _, .or first second => first.before typeRank termRank predicateRank bound ∧
      second.before typeRank termRank predicateRank bound
  | _, .implies first second => first.before typeRank termRank predicateRank bound ∧
      second.before typeRank termRank predicateRank bound
  | _, .all domain predicate => domain.before typeRank termRank predicateRank bound ∧
      predicate.before typeRank termRank predicateRank bound
  | _, .exists domain predicate => domain.before typeRank termRank predicateRank bound ∧
      predicate.before typeRank termRank predicateRank bound
  | _, .holds proposition => proposition.before typeRank termRank predicateRank bound
  | _, .image type => type.before typeRank termRank predicateRank bound

end

def ContextExpr.before (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (predicateRank : S.PredicateSymbol → Nat) (bound : Nat) : {n : Nat} → ContextExpr S n → Prop
  | _, .nil => True
  | _, .snoc previous type => previous.before typeRank termRank predicateRank bound ∧
      type.before typeRank termRank predicateRank bound
  | _, .assume previous predicate => previous.before typeRank termRank predicateRank bound ∧
      predicate.before typeRank termRank predicateRank bound

structure Signature (S : Symbols.{u}) where
  typeRank : S.TypeSymbol → Nat
  termRank : S.TermSymbol → Nat
  predicateRank : S.PredicateSymbol → Nat
  typeParameters : (symbol : S.TypeSymbol) → ContextExpr S (S.typeArity symbol)
  termParameters : (symbol : S.TermSymbol) → ContextExpr S (S.termArity symbol)
  predicateParameters : (symbol : S.PredicateSymbol) → ContextExpr S (S.predicateArity symbol)
  termResult : (symbol : S.TermSymbol) → TypeExpr S (S.termArity symbol)
  typeParameters_before : ∀ symbol,
    (typeParameters symbol).before typeRank termRank predicateRank (typeRank symbol)
  termParameters_before : ∀ symbol,
    (termParameters symbol).before typeRank termRank predicateRank (termRank symbol)
  predicateParameters_before : ∀ symbol,
    (predicateParameters symbol).before typeRank termRank predicateRank (predicateRank symbol)
  termResult_before : ∀ symbol,
    (termResult symbol).before typeRank termRank predicateRank (termRank symbol)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
