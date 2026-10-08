import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenaming

/-!
# Actions on propositions, refinement annotations and dependent binders

The simultaneous operations traverse the independently authored type, term
and proposition grammars. Refinement predicates and quantified formulas protect
one variable; a dependent pair branch protects both component variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u

variable {S : Symbols.{u}}

abbrev Substitution (S : Symbols.{u}) (n m : Nat) := Fin n → TermExpr S m

def liftSubstitution {n m : Nat} (substitution : Substitution S n m) :
    Substitution S (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun index => (substitution index).rename Fin.succ)

@[simp] theorem liftSubstitution_zero {n m : Nat} (substitution : Substitution S n m) :
    liftSubstitution substitution 0 = .var 0 := rfl

@[simp] theorem liftSubstitution_succ {n m : Nat} (substitution : Substitution S n m) (index : Fin n) :
    liftSubstitution substitution index.succ = (substitution index).rename Fin.succ := rfl

mutual

def TypeExpr.substitute : {n m : Nat} → Substitution S n m → TypeExpr S n → TypeExpr S m
  | _, _, substitution, .family symbol arguments => .family symbol (fun position => (arguments position).substitute (substitution))
  | _, _, _, .propositions => .propositions
  | _, _, substitution, .pi domain body => .pi (domain.substitute (substitution)) (body.substitute (liftSubstitution (substitution)))
  | _, _, substitution, .sigma domain body => .sigma (domain.substitute (substitution)) (body.substitute (liftSubstitution (substitution)))
  | _, _, substitution, .comprehension domain predicate => .comprehension (domain.substitute (substitution)) (predicate.substitute (liftSubstitution (substitution)))

def TermExpr.substitute : {n m : Nat} → Substitution S n m → TermExpr S n → TermExpr S m
  | _, _, substitution, .var index => substitution index
  | _, _, substitution, .primitive symbol arguments => .primitive symbol (fun position => (arguments position).substitute (substitution))
  | _, _, substitution, .lam domain codomain body => .lam (domain.substitute (substitution)) (codomain.substitute (liftSubstitution (substitution))) (body.substitute (liftSubstitution (substitution)))
  | _, _, substitution, .app domain body function argument => .app (domain.substitute (substitution)) (body.substitute (liftSubstitution (substitution))) (function.substitute (substitution)) (argument.substitute (substitution))
  | _, _, substitution, .pair domain body left right => .pair (domain.substitute (substitution)) (body.substitute (liftSubstitution (substitution))) (left.substitute (substitution)) (right.substitute (substitution))
  | _, _, substitution, .fst domain body pair => .fst (domain.substitute (substitution)) (body.substitute (liftSubstitution (substitution))) (pair.substitute (substitution))
  | _, _, substitution, .snd domain body pair => .snd (domain.substitute (substitution)) (body.substitute (liftSubstitution (substitution))) (pair.substitute (substitution))
  | _, _, substitution, .sigmaElim domain body motive branch pair => .sigmaElim (domain.substitute (substitution)) (body.substitute (liftSubstitution (substitution))) (motive.substitute (liftSubstitution (substitution))) (branch.substitute (liftSubstitution (liftSubstitution (substitution)))) (pair.substitute (substitution))
  | _, _, substitution, .quote predicate => .quote (predicate.substitute (substitution))
  | _, _, substitution, .refine domain predicate value => .refine (domain.substitute (substitution)) (predicate.substitute (liftSubstitution (substitution))) (value.substitute (substitution))
  | _, _, substitution, .forget domain predicate value => .forget (domain.substitute (substitution)) (predicate.substitute (liftSubstitution (substitution))) (value.substitute (substitution))

def PropExpr.substitute : {n m : Nat} → Substitution S n m → PropExpr S n → PropExpr S m
  | _, _, substitution, .atom symbol arguments => .atom symbol (fun position => (arguments position).substitute (substitution))
  | _, _, _, .truth => .truth
  | _, _, _, .falsehood => .falsehood
  | _, _, substitution, .and left right => .and (left.substitute (substitution)) (right.substitute (substitution))
  | _, _, substitution, .or left right => .or (left.substitute (substitution)) (right.substitute (substitution))
  | _, _, substitution, .implies antecedent consequent => .implies (antecedent.substitute (substitution)) (consequent.substitute (substitution))
  | _, _, substitution, .all domain predicate => .all (domain.substitute (substitution)) (predicate.substitute (liftSubstitution (substitution)))
  | _, _, substitution, .exists domain predicate => .exists (domain.substitute (substitution)) (predicate.substitute (liftSubstitution (substitution)))
  | _, _, substitution, .holds proposition => .holds (proposition.substitute (substitution))
  | _, _, substitution, .image type => .image (type.substitute (substitution))

end

theorem liftSubstitution_variables {n m : Nat} (mapping : Renaming n m) :
    liftSubstitution (S := S) (fun index => .var (mapping index)) =
      fun index => .var (liftRenaming mapping index) := by
  funext index
  cases index using Fin.cases <;> rfl

mutual

theorem TypeExpr.substitute_variables : ∀ {n m : Nat} (mapping : Renaming n m) (expression : TypeExpr S n),
    expression.substitute (fun index => .var (mapping index)) = expression.rename mapping
  | _, _, mapping, .family symbol arguments => by
      simp only [TypeExpr.substitute, TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.substitute_variables mapping (arguments position)
  | _, _, mapping, .propositions => by
      rfl
  | _, _, mapping, .pi domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) body]
  | _, _, mapping, .sigma domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) body]
  | _, _, mapping, .comprehension domain predicate => by
      simp only [TypeExpr.substitute, TypeExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, PropExpr.substitute_variables (liftRenaming (mapping)) predicate]

theorem TermExpr.substitute_variables : ∀ {n m : Nat} (mapping : Renaming n m) (expression : TermExpr S n),
    expression.substitute (fun index => .var (mapping index)) = expression.rename mapping
  | _, _, mapping, .var index => by
      rfl
  | _, _, mapping, .primitive symbol arguments => by
      simp only [TermExpr.substitute, TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.substitute_variables mapping (arguments position)
  | _, _, mapping, .lam domain codomain body => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) codomain, TermExpr.substitute_variables (liftRenaming (mapping)) body]
  | _, _, mapping, .app domain body function argument => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) body, TermExpr.substitute_variables (mapping) function, TermExpr.substitute_variables (mapping) argument]
  | _, _, mapping, .pair domain body left right => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) body, TermExpr.substitute_variables (mapping) left, TermExpr.substitute_variables (mapping) right]
  | _, _, mapping, .fst domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) body, TermExpr.substitute_variables (mapping) pair]
  | _, _, mapping, .snd domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) body, TermExpr.substitute_variables (mapping) pair]
  | _, _, mapping, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, TypeExpr.substitute_variables (liftRenaming (mapping)) body, TypeExpr.substitute_variables (liftRenaming (mapping)) motive, TermExpr.substitute_variables (liftRenaming (liftRenaming (mapping))) branch, TermExpr.substitute_variables (mapping) pair]
  | _, _, mapping, .quote predicate => by
      simp only [TermExpr.substitute, TermExpr.rename, PropExpr.substitute_variables (mapping) predicate]
  | _, _, mapping, .refine domain predicate value => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, PropExpr.substitute_variables (liftRenaming (mapping)) predicate, TermExpr.substitute_variables (mapping) value]
  | _, _, mapping, .forget domain predicate value => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, PropExpr.substitute_variables (liftRenaming (mapping)) predicate, TermExpr.substitute_variables (mapping) value]

theorem PropExpr.substitute_variables : ∀ {n m : Nat} (mapping : Renaming n m) (expression : PropExpr S n),
    expression.substitute (fun index => .var (mapping index)) = expression.rename mapping
  | _, _, mapping, .atom symbol arguments => by
      simp only [PropExpr.substitute, PropExpr.rename]
      congr 1
      funext position
      exact TermExpr.substitute_variables mapping (arguments position)
  | _, _, mapping, .truth => by
      rfl
  | _, _, mapping, .falsehood => by
      rfl
  | _, _, mapping, .and left right => by
      simp only [PropExpr.substitute, PropExpr.rename, PropExpr.substitute_variables (mapping) left, PropExpr.substitute_variables (mapping) right]
  | _, _, mapping, .or left right => by
      simp only [PropExpr.substitute, PropExpr.rename, PropExpr.substitute_variables (mapping) left, PropExpr.substitute_variables (mapping) right]
  | _, _, mapping, .implies antecedent consequent => by
      simp only [PropExpr.substitute, PropExpr.rename, PropExpr.substitute_variables (mapping) antecedent, PropExpr.substitute_variables (mapping) consequent]
  | _, _, mapping, .all domain predicate => by
      simp only [PropExpr.substitute, PropExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, PropExpr.substitute_variables (liftRenaming (mapping)) predicate]
  | _, _, mapping, .exists domain predicate => by
      simp only [PropExpr.substitute, PropExpr.rename, liftSubstitution_variables, TypeExpr.substitute_variables (mapping) domain, PropExpr.substitute_variables (liftRenaming (mapping)) predicate]
  | _, _, mapping, .holds proposition => by
      simp only [PropExpr.substitute, PropExpr.rename, TermExpr.substitute_variables (mapping) proposition]
  | _, _, mapping, .image type => by
      simp only [PropExpr.substitute, PropExpr.rename, TypeExpr.substitute_variables (mapping) type]

end

@[simp] theorem TypeExpr.substitute_identity {n : Nat} (expression : TypeExpr S n) :
    expression.substitute TermExpr.var = expression := by
  simpa only [id_eq, TypeExpr.rename_identity] using expression.substitute_variables id

@[simp] theorem TermExpr.substitute_identity {n : Nat} (expression : TermExpr S n) :
    expression.substitute TermExpr.var = expression := by
  simpa only [id_eq, TermExpr.rename_identity] using expression.substitute_variables id

@[simp] theorem PropExpr.substitute_identity {n : Nat} (expression : PropExpr S n) :
    expression.substitute TermExpr.var = expression := by
  simpa only [id_eq, PropExpr.rename_identity] using expression.substitute_variables id

theorem liftSubstitution_rename {n m k : Nat} (substitution : Substitution S n m)
    (mapping : Renaming m k) :
    liftSubstitution (fun index => (substitution index).rename mapping) =
      fun index => (liftSubstitution substitution index).rename (liftRenaming mapping) := by
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      simp only [liftSubstitution_succ, TermExpr.rename_comp]
      rfl

theorem liftSubstitution_precompose {n m k : Nat} (mapping : Renaming n m)
    (substitution : Substitution S m k) :
    liftSubstitution (substitution ∘ mapping) =
      liftSubstitution substitution ∘ liftRenaming mapping := by
  funext index
  cases index using Fin.cases <;> rfl

mutual

theorem TypeExpr.rename_substitute : ∀ {n m k : Nat} (substitution : Substitution S n m)
    (mapping : Renaming m k) (expression : TypeExpr S n),
    (expression.substitute substitution).rename mapping = expression.substitute (fun index => (substitution index).rename mapping)
  | _, _, _, substitution, mapping, .family symbol arguments => by
      simp only [TypeExpr.substitute, TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_substitute substitution mapping (arguments position)
  | _, _, _, substitution, mapping, .propositions => by
      rfl
  | _, _, _, substitution, mapping, .pi domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .sigma domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .comprehension domain predicate => by
      simp only [TypeExpr.substitute, TypeExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, PropExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) predicate, liftSubstitution_rename]

theorem TermExpr.rename_substitute : ∀ {n m k : Nat} (substitution : Substitution S n m)
    (mapping : Renaming m k) (expression : TermExpr S n),
    (expression.substitute substitution).rename mapping = expression.substitute (fun index => (substitution index).rename mapping)
  | _, _, _, substitution, mapping, .var index => by
      rfl
  | _, _, _, substitution, mapping, .primitive symbol arguments => by
      simp only [TermExpr.substitute, TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_substitute substitution mapping (arguments position)
  | _, _, _, substitution, mapping, .lam domain codomain body => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) codomain, TermExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .app domain body function argument => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, TermExpr.rename_substitute (substitution) (mapping) function, TermExpr.rename_substitute (substitution) (mapping) argument, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .pair domain body left right => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, TermExpr.rename_substitute (substitution) (mapping) left, TermExpr.rename_substitute (substitution) (mapping) right, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .fst domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, TermExpr.rename_substitute (substitution) (mapping) pair, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .snd domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, TermExpr.rename_substitute (substitution) (mapping) pair, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) body, TypeExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) motive, TermExpr.rename_substitute (liftSubstitution (liftSubstitution (substitution))) (liftRenaming (liftRenaming (mapping))) branch, TermExpr.rename_substitute (substitution) (mapping) pair, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .quote predicate => by
      simp only [TermExpr.substitute, TermExpr.rename, PropExpr.rename_substitute (substitution) (mapping) predicate]
  | _, _, _, substitution, mapping, .refine domain predicate value => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, PropExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) predicate, TermExpr.rename_substitute (substitution) (mapping) value, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .forget domain predicate value => by
      simp only [TermExpr.substitute, TermExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, PropExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) predicate, TermExpr.rename_substitute (substitution) (mapping) value, liftSubstitution_rename]

theorem PropExpr.rename_substitute : ∀ {n m k : Nat} (substitution : Substitution S n m)
    (mapping : Renaming m k) (expression : PropExpr S n),
    (expression.substitute substitution).rename mapping = expression.substitute (fun index => (substitution index).rename mapping)
  | _, _, _, substitution, mapping, .atom symbol arguments => by
      simp only [PropExpr.substitute, PropExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_substitute substitution mapping (arguments position)
  | _, _, _, substitution, mapping, .truth => by
      rfl
  | _, _, _, substitution, mapping, .falsehood => by
      rfl
  | _, _, _, substitution, mapping, .and left right => by
      simp only [PropExpr.substitute, PropExpr.rename, PropExpr.rename_substitute (substitution) (mapping) left, PropExpr.rename_substitute (substitution) (mapping) right]
  | _, _, _, substitution, mapping, .or left right => by
      simp only [PropExpr.substitute, PropExpr.rename, PropExpr.rename_substitute (substitution) (mapping) left, PropExpr.rename_substitute (substitution) (mapping) right]
  | _, _, _, substitution, mapping, .implies antecedent consequent => by
      simp only [PropExpr.substitute, PropExpr.rename, PropExpr.rename_substitute (substitution) (mapping) antecedent, PropExpr.rename_substitute (substitution) (mapping) consequent]
  | _, _, _, substitution, mapping, .all domain predicate => by
      simp only [PropExpr.substitute, PropExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, PropExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) predicate, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .exists domain predicate => by
      simp only [PropExpr.substitute, PropExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) domain, PropExpr.rename_substitute (liftSubstitution (substitution)) (liftRenaming (mapping)) predicate, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .holds proposition => by
      simp only [PropExpr.substitute, PropExpr.rename, TermExpr.rename_substitute (substitution) (mapping) proposition]
  | _, _, _, substitution, mapping, .image type => by
      simp only [PropExpr.substitute, PropExpr.rename, TypeExpr.rename_substitute (substitution) (mapping) type]

end

mutual

theorem TypeExpr.substitute_rename : ∀ {n m k : Nat} (mapping : Renaming n m)
    (substitution : Substitution S m k) (expression : TypeExpr S n),
    (expression.rename mapping).substitute substitution = expression.substitute (substitution ∘ mapping)
  | _, _, _, mapping, substitution, .family symbol arguments => by
      simp only [TypeExpr.rename, TypeExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_rename mapping substitution (arguments position)
  | _, _, _, mapping, substitution, .propositions => by
      rfl
  | _, _, _, mapping, substitution, .pi domain body => by
      simp only [TypeExpr.rename, TypeExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .sigma domain body => by
      simp only [TypeExpr.rename, TypeExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .comprehension domain predicate => by
      simp only [TypeExpr.rename, TypeExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, PropExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) predicate, liftSubstitution_precompose]

theorem TermExpr.substitute_rename : ∀ {n m k : Nat} (mapping : Renaming n m)
    (substitution : Substitution S m k) (expression : TermExpr S n),
    (expression.rename mapping).substitute substitution = expression.substitute (substitution ∘ mapping)
  | _, _, _, mapping, substitution, .var index => by
      rfl
  | _, _, _, mapping, substitution, .primitive symbol arguments => by
      simp only [TermExpr.rename, TermExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_rename mapping substitution (arguments position)
  | _, _, _, mapping, substitution, .lam domain codomain body => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) codomain, TermExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .app domain body function argument => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, TermExpr.substitute_rename (mapping) (substitution) function, TermExpr.substitute_rename (mapping) (substitution) argument, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .pair domain body left right => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, TermExpr.substitute_rename (mapping) (substitution) left, TermExpr.substitute_rename (mapping) (substitution) right, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .fst domain body pair => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, TermExpr.substitute_rename (mapping) (substitution) pair, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .snd domain body pair => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, TermExpr.substitute_rename (mapping) (substitution) pair, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) body, TypeExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) motive, TermExpr.substitute_rename (liftRenaming (liftRenaming (mapping))) (liftSubstitution (liftSubstitution (substitution))) branch, TermExpr.substitute_rename (mapping) (substitution) pair, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .quote predicate => by
      simp only [TermExpr.rename, TermExpr.substitute, PropExpr.substitute_rename (mapping) (substitution) predicate]
  | _, _, _, mapping, substitution, .refine domain predicate value => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, PropExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) predicate, TermExpr.substitute_rename (mapping) (substitution) value, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .forget domain predicate value => by
      simp only [TermExpr.rename, TermExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, PropExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) predicate, TermExpr.substitute_rename (mapping) (substitution) value, liftSubstitution_precompose]

theorem PropExpr.substitute_rename : ∀ {n m k : Nat} (mapping : Renaming n m)
    (substitution : Substitution S m k) (expression : PropExpr S n),
    (expression.rename mapping).substitute substitution = expression.substitute (substitution ∘ mapping)
  | _, _, _, mapping, substitution, .atom symbol arguments => by
      simp only [PropExpr.rename, PropExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_rename mapping substitution (arguments position)
  | _, _, _, mapping, substitution, .truth => by
      rfl
  | _, _, _, mapping, substitution, .falsehood => by
      rfl
  | _, _, _, mapping, substitution, .and left right => by
      simp only [PropExpr.rename, PropExpr.substitute, PropExpr.substitute_rename (mapping) (substitution) left, PropExpr.substitute_rename (mapping) (substitution) right]
  | _, _, _, mapping, substitution, .or left right => by
      simp only [PropExpr.rename, PropExpr.substitute, PropExpr.substitute_rename (mapping) (substitution) left, PropExpr.substitute_rename (mapping) (substitution) right]
  | _, _, _, mapping, substitution, .implies antecedent consequent => by
      simp only [PropExpr.rename, PropExpr.substitute, PropExpr.substitute_rename (mapping) (substitution) antecedent, PropExpr.substitute_rename (mapping) (substitution) consequent]
  | _, _, _, mapping, substitution, .all domain predicate => by
      simp only [PropExpr.rename, PropExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, PropExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) predicate, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .exists domain predicate => by
      simp only [PropExpr.rename, PropExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) domain, PropExpr.substitute_rename (liftRenaming (mapping)) (liftSubstitution (substitution)) predicate, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .holds proposition => by
      simp only [PropExpr.rename, PropExpr.substitute, TermExpr.substitute_rename (mapping) (substitution) proposition]
  | _, _, _, mapping, substitution, .image type => by
      simp only [PropExpr.rename, PropExpr.substitute, TypeExpr.substitute_rename (mapping) (substitution) type]

end

theorem liftSubstitution_comp {n m k : Nat} (first : Substitution S n m)
    (second : Substitution S m k) :
    liftSubstitution (fun index => (first index).substitute second) =
      fun index => (liftSubstitution first index).substitute (liftSubstitution second) := by
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      simp only [liftSubstitution_succ, TermExpr.rename_substitute, TermExpr.substitute_rename]
      rfl

mutual

theorem TypeExpr.substitute_comp : ∀ {n m k : Nat} (first : Substitution S n m)
    (second : Substitution S m k) (expression : TypeExpr S n),
    (expression.substitute first).substitute second =
      expression.substitute (fun index => (first index).substitute second)
  | _, _, _, first, second, .family symbol arguments => by
      simp only [TypeExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_comp first second (arguments position)
  | _, _, _, first, second, .propositions => by
      rfl
  | _, _, _, first, second, .pi domain body => by
      simp only [TypeExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, liftSubstitution_comp]
  | _, _, _, first, second, .sigma domain body => by
      simp only [TypeExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, liftSubstitution_comp]
  | _, _, _, first, second, .comprehension domain predicate => by
      simp only [TypeExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, PropExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) predicate, liftSubstitution_comp]

theorem TermExpr.substitute_comp : ∀ {n m k : Nat} (first : Substitution S n m)
    (second : Substitution S m k) (expression : TermExpr S n),
    (expression.substitute first).substitute second =
      expression.substitute (fun index => (first index).substitute second)
  | _, _, _, first, second, .var index => by
      rfl
  | _, _, _, first, second, .primitive symbol arguments => by
      simp only [TermExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_comp first second (arguments position)
  | _, _, _, first, second, .lam domain codomain body => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) codomain, TermExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, liftSubstitution_comp]
  | _, _, _, first, second, .app domain body function argument => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, TermExpr.substitute_comp (first) (second) function, TermExpr.substitute_comp (first) (second) argument, liftSubstitution_comp]
  | _, _, _, first, second, .pair domain body left right => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, TermExpr.substitute_comp (first) (second) left, TermExpr.substitute_comp (first) (second) right, liftSubstitution_comp]
  | _, _, _, first, second, .fst domain body pair => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, TermExpr.substitute_comp (first) (second) pair, liftSubstitution_comp]
  | _, _, _, first, second, .snd domain body pair => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, TermExpr.substitute_comp (first) (second) pair, liftSubstitution_comp]
  | _, _, _, first, second, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) body, TypeExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) motive, TermExpr.substitute_comp (liftSubstitution (liftSubstitution (first))) (liftSubstitution (liftSubstitution (second))) branch, TermExpr.substitute_comp (first) (second) pair, liftSubstitution_comp]
  | _, _, _, first, second, .quote predicate => by
      simp only [TermExpr.substitute, PropExpr.substitute_comp (first) (second) predicate]
  | _, _, _, first, second, .refine domain predicate value => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, PropExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) predicate, TermExpr.substitute_comp (first) (second) value, liftSubstitution_comp]
  | _, _, _, first, second, .forget domain predicate value => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, PropExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) predicate, TermExpr.substitute_comp (first) (second) value, liftSubstitution_comp]

theorem PropExpr.substitute_comp : ∀ {n m k : Nat} (first : Substitution S n m)
    (second : Substitution S m k) (expression : PropExpr S n),
    (expression.substitute first).substitute second =
      expression.substitute (fun index => (first index).substitute second)
  | _, _, _, first, second, .atom symbol arguments => by
      simp only [PropExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_comp first second (arguments position)
  | _, _, _, first, second, .truth => by
      rfl
  | _, _, _, first, second, .falsehood => by
      rfl
  | _, _, _, first, second, .and left right => by
      simp only [PropExpr.substitute, PropExpr.substitute_comp (first) (second) left, PropExpr.substitute_comp (first) (second) right]
  | _, _, _, first, second, .or left right => by
      simp only [PropExpr.substitute, PropExpr.substitute_comp (first) (second) left, PropExpr.substitute_comp (first) (second) right]
  | _, _, _, first, second, .implies antecedent consequent => by
      simp only [PropExpr.substitute, PropExpr.substitute_comp (first) (second) antecedent, PropExpr.substitute_comp (first) (second) consequent]
  | _, _, _, first, second, .all domain predicate => by
      simp only [PropExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, PropExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) predicate, liftSubstitution_comp]
  | _, _, _, first, second, .exists domain predicate => by
      simp only [PropExpr.substitute, TypeExpr.substitute_comp (first) (second) domain, PropExpr.substitute_comp (liftSubstitution (first)) (liftSubstitution (second)) predicate, liftSubstitution_comp]
  | _, _, _, first, second, .holds proposition => by
      simp only [PropExpr.substitute, TermExpr.substitute_comp (first) (second) proposition]
  | _, _, _, first, second, .image type => by
      simp only [PropExpr.substitute, TypeExpr.substitute_comp (first) (second) type]

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
