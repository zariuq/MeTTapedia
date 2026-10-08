import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntax

/-!
# Actions on propositions, refinement annotations and dependent binders

The simultaneous operations traverse the independently authored type, term
and proposition grammars. Refinement predicates and quantified formulas protect
one variable; a dependent pair branch protects both component variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u

abbrev Renaming (n m : Nat) := Fin n → Fin m

def liftRenaming {n m : Nat} (mapping : Renaming n m) : Renaming (n + 1) (m + 1) :=
  Fin.cases 0 (fun index => (mapping index).succ)

@[simp] theorem liftRenaming_zero {n m : Nat} (mapping : Renaming n m) :
    liftRenaming mapping 0 = 0 := rfl

@[simp] theorem liftRenaming_succ {n m : Nat} (mapping : Renaming n m) (index : Fin n) :
    liftRenaming mapping index.succ = (mapping index).succ := rfl

@[simp] theorem liftRenaming_identity {n : Nat} :
    liftRenaming (id : Renaming n n) = id := by
  funext index
  cases index using Fin.cases <;> rfl

theorem liftRenaming_comp {n m k : Nat} (first : Renaming n m) (second : Renaming m k) :
    liftRenaming (second ∘ first) = liftRenaming second ∘ liftRenaming first := by
  funext index
  cases index using Fin.cases <;> rfl

variable {S : Symbols.{u}}

mutual

def TypeExpr.rename : {n m : Nat} → Renaming n m → TypeExpr S n → TypeExpr S m
  | _, _, mapping, .family symbol arguments => .family symbol (fun position => (arguments position).rename (mapping))
  | _, _, _, .propositions => .propositions
  | _, _, mapping, .pi domain body => .pi (domain.rename (mapping)) (body.rename (liftRenaming (mapping)))
  | _, _, mapping, .sigma domain body => .sigma (domain.rename (mapping)) (body.rename (liftRenaming (mapping)))
  | _, _, mapping, .comprehension domain predicate => .comprehension (domain.rename (mapping)) (predicate.rename (liftRenaming (mapping)))

def TermExpr.rename : {n m : Nat} → Renaming n m → TermExpr S n → TermExpr S m
  | _, _, mapping, .var index => .var (mapping index)
  | _, _, mapping, .primitive symbol arguments => .primitive symbol (fun position => (arguments position).rename (mapping))
  | _, _, mapping, .lam domain codomain body => .lam (domain.rename (mapping)) (codomain.rename (liftRenaming (mapping))) (body.rename (liftRenaming (mapping)))
  | _, _, mapping, .app domain body function argument => .app (domain.rename (mapping)) (body.rename (liftRenaming (mapping))) (function.rename (mapping)) (argument.rename (mapping))
  | _, _, mapping, .pair domain body left right => .pair (domain.rename (mapping)) (body.rename (liftRenaming (mapping))) (left.rename (mapping)) (right.rename (mapping))
  | _, _, mapping, .fst domain body pair => .fst (domain.rename (mapping)) (body.rename (liftRenaming (mapping))) (pair.rename (mapping))
  | _, _, mapping, .snd domain body pair => .snd (domain.rename (mapping)) (body.rename (liftRenaming (mapping))) (pair.rename (mapping))
  | _, _, mapping, .sigmaElim domain body motive branch pair => .sigmaElim (domain.rename (mapping)) (body.rename (liftRenaming (mapping))) (motive.rename (liftRenaming (mapping))) (branch.rename (liftRenaming (liftRenaming (mapping)))) (pair.rename (mapping))
  | _, _, mapping, .quote predicate => .quote (predicate.rename (mapping))
  | _, _, mapping, .refine domain predicate value => .refine (domain.rename (mapping)) (predicate.rename (liftRenaming (mapping))) (value.rename (mapping))
  | _, _, mapping, .forget domain predicate value => .forget (domain.rename (mapping)) (predicate.rename (liftRenaming (mapping))) (value.rename (mapping))

def PropExpr.rename : {n m : Nat} → Renaming n m → PropExpr S n → PropExpr S m
  | _, _, mapping, .atom symbol arguments => .atom symbol (fun position => (arguments position).rename (mapping))
  | _, _, _, .truth => .truth
  | _, _, _, .falsehood => .falsehood
  | _, _, mapping, .and left right => .and (left.rename (mapping)) (right.rename (mapping))
  | _, _, mapping, .or left right => .or (left.rename (mapping)) (right.rename (mapping))
  | _, _, mapping, .implies antecedent consequent => .implies (antecedent.rename (mapping)) (consequent.rename (mapping))
  | _, _, mapping, .all domain predicate => .all (domain.rename (mapping)) (predicate.rename (liftRenaming (mapping)))
  | _, _, mapping, .exists domain predicate => .exists (domain.rename (mapping)) (predicate.rename (liftRenaming (mapping)))
  | _, _, mapping, .holds proposition => .holds (proposition.rename (mapping))
  | _, _, mapping, .image type => .image (type.rename (mapping))

end

mutual

@[simp] theorem TypeExpr.rename_identity : ∀ {n : Nat} (expression : TypeExpr S n),
    expression.rename id = expression
  | _, .family symbol arguments => by
      simp only [TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_identity (arguments position)
  | _, .propositions => by
      rfl
  | _, .pi domain body => by
      simp only [TypeExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity body]
  | _, .sigma domain body => by
      simp only [TypeExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity body]
  | _, .comprehension domain predicate => by
      simp only [TypeExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, PropExpr.rename_identity predicate]

@[simp] theorem TermExpr.rename_identity : ∀ {n : Nat} (expression : TermExpr S n),
    expression.rename id = expression
  | _, .var index => by
      rfl
  | _, .primitive symbol arguments => by
      simp only [TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_identity (arguments position)
  | _, .lam domain codomain body => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity codomain, TermExpr.rename_identity body]
  | _, .app domain body function argument => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity body, TermExpr.rename_identity function, TermExpr.rename_identity argument]
  | _, .pair domain body left right => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity body, TermExpr.rename_identity left, TermExpr.rename_identity right]
  | _, .fst domain body pair => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity body, TermExpr.rename_identity pair]
  | _, .snd domain body pair => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity body, TermExpr.rename_identity pair]
  | _, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, TypeExpr.rename_identity body, TypeExpr.rename_identity motive, TermExpr.rename_identity branch, TermExpr.rename_identity pair]
  | _, .quote predicate => by
      simp only [TermExpr.rename, PropExpr.rename_identity predicate]
  | _, .refine domain predicate value => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, PropExpr.rename_identity predicate, TermExpr.rename_identity value]
  | _, .forget domain predicate value => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, PropExpr.rename_identity predicate, TermExpr.rename_identity value]

@[simp] theorem PropExpr.rename_identity : ∀ {n : Nat} (expression : PropExpr S n),
    expression.rename id = expression
  | _, .atom symbol arguments => by
      simp only [PropExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_identity (arguments position)
  | _, .truth => by
      rfl
  | _, .falsehood => by
      rfl
  | _, .and left right => by
      simp only [PropExpr.rename, PropExpr.rename_identity left, PropExpr.rename_identity right]
  | _, .or left right => by
      simp only [PropExpr.rename, PropExpr.rename_identity left, PropExpr.rename_identity right]
  | _, .implies antecedent consequent => by
      simp only [PropExpr.rename, PropExpr.rename_identity antecedent, PropExpr.rename_identity consequent]
  | _, .all domain predicate => by
      simp only [PropExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, PropExpr.rename_identity predicate]
  | _, .exists domain predicate => by
      simp only [PropExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain, PropExpr.rename_identity predicate]
  | _, .holds proposition => by
      simp only [PropExpr.rename, TermExpr.rename_identity proposition]
  | _, .image type => by
      simp only [PropExpr.rename, TypeExpr.rename_identity type]

end

mutual

theorem TypeExpr.rename_comp : ∀ {n m k : Nat} (first : Renaming n m) (second : Renaming m k)
    (expression : TypeExpr S n),
    (expression.rename first).rename second = expression.rename (second ∘ first)
  | _, _, _, first, second, .family symbol arguments => by
      simp only [TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_comp first second (arguments position)
  | _, _, _, first, second, .propositions => by
      rfl
  | _, _, _, first, second, .pi domain body => by
      simp only [TypeExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, liftRenaming_comp]
  | _, _, _, first, second, .sigma domain body => by
      simp only [TypeExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, liftRenaming_comp]
  | _, _, _, first, second, .comprehension domain predicate => by
      simp only [TypeExpr.rename, TypeExpr.rename_comp (first) (second) domain, PropExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) predicate, liftRenaming_comp]

theorem TermExpr.rename_comp : ∀ {n m k : Nat} (first : Renaming n m) (second : Renaming m k)
    (expression : TermExpr S n),
    (expression.rename first).rename second = expression.rename (second ∘ first)
  | _, _, _, first, second, .var index => by
      rfl
  | _, _, _, first, second, .primitive symbol arguments => by
      simp only [TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_comp first second (arguments position)
  | _, _, _, first, second, .lam domain codomain body => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) codomain, TermExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, liftRenaming_comp]
  | _, _, _, first, second, .app domain body function argument => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, TermExpr.rename_comp (first) (second) function, TermExpr.rename_comp (first) (second) argument, liftRenaming_comp]
  | _, _, _, first, second, .pair domain body left right => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, TermExpr.rename_comp (first) (second) left, TermExpr.rename_comp (first) (second) right, liftRenaming_comp]
  | _, _, _, first, second, .fst domain body pair => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, TermExpr.rename_comp (first) (second) pair, liftRenaming_comp]
  | _, _, _, first, second, .snd domain body pair => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, TermExpr.rename_comp (first) (second) pair, liftRenaming_comp]
  | _, _, _, first, second, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) body, TypeExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) motive, TermExpr.rename_comp (liftRenaming (liftRenaming (first))) (liftRenaming (liftRenaming (second))) branch, TermExpr.rename_comp (first) (second) pair, liftRenaming_comp]
  | _, _, _, first, second, .quote predicate => by
      simp only [TermExpr.rename, PropExpr.rename_comp (first) (second) predicate]
  | _, _, _, first, second, .refine domain predicate value => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, PropExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) predicate, TermExpr.rename_comp (first) (second) value, liftRenaming_comp]
  | _, _, _, first, second, .forget domain predicate value => by
      simp only [TermExpr.rename, TypeExpr.rename_comp (first) (second) domain, PropExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) predicate, TermExpr.rename_comp (first) (second) value, liftRenaming_comp]

theorem PropExpr.rename_comp : ∀ {n m k : Nat} (first : Renaming n m) (second : Renaming m k)
    (expression : PropExpr S n),
    (expression.rename first).rename second = expression.rename (second ∘ first)
  | _, _, _, first, second, .atom symbol arguments => by
      simp only [PropExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_comp first second (arguments position)
  | _, _, _, first, second, .truth => by
      rfl
  | _, _, _, first, second, .falsehood => by
      rfl
  | _, _, _, first, second, .and left right => by
      simp only [PropExpr.rename, PropExpr.rename_comp (first) (second) left, PropExpr.rename_comp (first) (second) right]
  | _, _, _, first, second, .or left right => by
      simp only [PropExpr.rename, PropExpr.rename_comp (first) (second) left, PropExpr.rename_comp (first) (second) right]
  | _, _, _, first, second, .implies antecedent consequent => by
      simp only [PropExpr.rename, PropExpr.rename_comp (first) (second) antecedent, PropExpr.rename_comp (first) (second) consequent]
  | _, _, _, first, second, .all domain predicate => by
      simp only [PropExpr.rename, TypeExpr.rename_comp (first) (second) domain, PropExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) predicate, liftRenaming_comp]
  | _, _, _, first, second, .exists domain predicate => by
      simp only [PropExpr.rename, TypeExpr.rename_comp (first) (second) domain, PropExpr.rename_comp (liftRenaming (first)) (liftRenaming (second)) predicate, liftRenaming_comp]
  | _, _, _, first, second, .holds proposition => by
      simp only [PropExpr.rename, TermExpr.rename_comp (first) (second) proposition]
  | _, _, _, first, second, .image type => by
      simp only [PropExpr.rename, TypeExpr.rename_comp (first) (second) type]

end

/-- Looking up a declaration weakens its type past every later declaration. -/
def ContextExpr.lookup : {n : Nat} → ContextExpr S n → Fin n → TypeExpr S n
  | _, .assume previous _, index => previous.lookup index
  | _, .snoc previous type, index =>
      Fin.cases (type.rename Fin.succ) (fun prior => (previous.lookup prior).rename Fin.succ) index

@[simp] theorem ContextExpr.lookup_zero {n : Nat} (context : ContextExpr S n) (type : TypeExpr S n) :
    (context.snoc type).lookup 0 = type.rename Fin.succ := rfl

@[simp] theorem ContextExpr.lookup_succ {n : Nat} (context : ContextExpr S n) (type : TypeExpr S n)
    (index : Fin n) : (context.snoc type).lookup index.succ = (context.lookup index).rename Fin.succ := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
