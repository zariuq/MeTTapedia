import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalRenaming

/-!
# Simultaneous substitution for external dependent syntax

Substitution replaces variables throughout types, term annotations and ordered
primitive arguments. Every dependent binder is protected by lifting, including
both component binders of full dependent pair elimination.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

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
  | _, _, substitution, .family symbol arguments =>
      .family symbol (fun position => (arguments position).substitute substitution)
  | _, _, substitution, .pi domain body =>
      .pi (domain.substitute substitution) (body.substitute (liftSubstitution substitution))
  | _, _, substitution, .sigma domain body =>
      .sigma (domain.substitute substitution) (body.substitute (liftSubstitution substitution))

def TermExpr.substitute : {n m : Nat} → Substitution S n m → TermExpr S n → TermExpr S m
  | _, _, substitution, .var index => substitution index
  | _, _, substitution, .primitive symbol arguments =>
      .primitive symbol (fun position => (arguments position).substitute substitution)
  | _, _, substitution, .lam domain codomain body =>
      .lam (domain.substitute substitution) (codomain.substitute (liftSubstitution substitution))
        (body.substitute (liftSubstitution substitution))
  | _, _, substitution, .app domain body function argument =>
      .app (domain.substitute substitution) (body.substitute (liftSubstitution substitution))
        (function.substitute substitution) (argument.substitute substitution)
  | _, _, substitution, .pair domain body first second =>
      .pair (domain.substitute substitution) (body.substitute (liftSubstitution substitution))
        (first.substitute substitution) (second.substitute substitution)
  | _, _, substitution, .fst domain body pair =>
      .fst (domain.substitute substitution) (body.substitute (liftSubstitution substitution))
        (pair.substitute substitution)
  | _, _, substitution, .snd domain body pair =>
      .snd (domain.substitute substitution) (body.substitute (liftSubstitution substitution))
        (pair.substitute substitution)
  | _, _, substitution, .sigmaElim domain body motive branch pair =>
      .sigmaElim (domain.substitute substitution) (body.substitute (liftSubstitution substitution))
        (motive.substitute (liftSubstitution substitution))
        (branch.substitute (liftSubstitution (liftSubstitution substitution)))
        (pair.substitute substitution)

end

theorem liftSubstitution_variables {n m : Nat} (mapping : Renaming n m) :
    liftSubstitution (S := S) (fun index => .var (mapping index)) =
      fun index => .var (liftRenaming mapping index) := by
  funext index
  cases index using Fin.cases <;> rfl

mutual

theorem TypeExpr.substitute_variables : ∀ {n m : Nat} (mapping : Renaming n m) (type : TypeExpr S n),
    type.substitute (fun index => .var (mapping index)) = type.rename mapping
  | _, _, mapping, .family symbol arguments => by
      simp only [TypeExpr.substitute, TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.substitute_variables mapping (arguments position)
  | _, _, mapping, .pi domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) body]
  | _, _, mapping, .sigma domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) body]

theorem TermExpr.substitute_variables : ∀ {n m : Nat} (mapping : Renaming n m) (term : TermExpr S n),
    term.substitute (fun index => .var (mapping index)) = term.rename mapping
  | _, _, _, .var _ => rfl
  | _, _, mapping, .primitive symbol arguments => by
      simp only [TermExpr.substitute, TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.substitute_variables mapping (arguments position)
  | _, _, mapping, .lam domain codomain body => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) codomain,
        TermExpr.substitute_variables (liftRenaming mapping) body]
  | _, _, mapping, .app domain body function argument => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) body,
        TermExpr.substitute_variables mapping function, TermExpr.substitute_variables mapping argument]
  | _, _, mapping, .pair domain body first second => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) body,
        TermExpr.substitute_variables mapping first, TermExpr.substitute_variables mapping second]
  | _, _, mapping, .fst domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) body,
        TermExpr.substitute_variables mapping pair]
  | _, _, mapping, .snd domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) body,
        TermExpr.substitute_variables mapping pair]
  | _, _, mapping, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, TermExpr.rename, liftSubstitution_variables,
        TypeExpr.substitute_variables mapping domain, TypeExpr.substitute_variables (liftRenaming mapping) body,
        TypeExpr.substitute_variables (liftRenaming mapping) motive,
        TermExpr.substitute_variables (liftRenaming (liftRenaming mapping)) branch,
        TermExpr.substitute_variables mapping pair]

end

@[simp] theorem TypeExpr.substitute_identity {n : Nat} (type : TypeExpr S n) :
    type.substitute TermExpr.var = type := by
  simpa only [id_eq, TypeExpr.rename_identity] using type.substitute_variables id

@[simp] theorem TermExpr.substitute_identity {n : Nat} (term : TermExpr S n) :
    term.substitute TermExpr.var = term := by
  simpa only [id_eq, TermExpr.rename_identity] using term.substitute_variables id

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
    (mapping : Renaming m k) (type : TypeExpr S n),
    (type.substitute substitution).rename mapping =
      type.substitute (fun index => (substitution index).rename mapping)
  | _, _, _, substitution, mapping, .family symbol arguments => by
      simp only [TypeExpr.substitute, TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_substitute substitution mapping (arguments position)
  | _, _, _, substitution, mapping, .pi domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        liftSubstitution_rename]
  | _, _, _, substitution, mapping, .sigma domain body => by
      simp only [TypeExpr.substitute, TypeExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        liftSubstitution_rename]

theorem TermExpr.rename_substitute : ∀ {n m k : Nat} (substitution : Substitution S n m)
    (mapping : Renaming m k) (term : TermExpr S n),
    (term.substitute substitution).rename mapping =
      term.substitute (fun index => (substitution index).rename mapping)
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, substitution, mapping, .primitive symbol arguments => by
      simp only [TermExpr.substitute, TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_substitute substitution mapping (arguments position)
  | _, _, _, substitution, mapping, .lam domain codomain body => by
      simp only [TermExpr.substitute, TermExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) codomain,
        TermExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        liftSubstitution_rename]
  | _, _, _, substitution, mapping, .app domain body function argument => by
      simp only [TermExpr.substitute, TermExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        TermExpr.rename_substitute substitution mapping function,
        TermExpr.rename_substitute substitution mapping argument, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .pair domain body first second => by
      simp only [TermExpr.substitute, TermExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        TermExpr.rename_substitute substitution mapping first,
        TermExpr.rename_substitute substitution mapping second, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .fst domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        TermExpr.rename_substitute substitution mapping pair, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .snd domain body pair => by
      simp only [TermExpr.substitute, TermExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        TermExpr.rename_substitute substitution mapping pair, liftSubstitution_rename]
  | _, _, _, substitution, mapping, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, TermExpr.rename,
        TypeExpr.rename_substitute substitution mapping domain,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) body,
        TypeExpr.rename_substitute (liftSubstitution substitution) (liftRenaming mapping) motive,
        TermExpr.rename_substitute (liftSubstitution (liftSubstitution substitution))
          (liftRenaming (liftRenaming mapping)) branch,
        TermExpr.rename_substitute substitution mapping pair, liftSubstitution_rename]

end

mutual

theorem TypeExpr.substitute_rename : ∀ {n m k : Nat} (mapping : Renaming n m)
    (substitution : Substitution S m k) (type : TypeExpr S n),
    (type.rename mapping).substitute substitution = type.substitute (substitution ∘ mapping)
  | _, _, _, mapping, substitution, .family symbol arguments => by
      simp only [TypeExpr.rename, TypeExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_rename mapping substitution (arguments position)
  | _, _, _, mapping, substitution, .pi domain body => by
      simp only [TypeExpr.rename, TypeExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .sigma domain body => by
      simp only [TypeExpr.rename, TypeExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        liftSubstitution_precompose]

theorem TermExpr.substitute_rename : ∀ {n m k : Nat} (mapping : Renaming n m)
    (substitution : Substitution S m k) (term : TermExpr S n),
    (term.rename mapping).substitute substitution = term.substitute (substitution ∘ mapping)
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, mapping, substitution, .primitive symbol arguments => by
      simp only [TermExpr.rename, TermExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_rename mapping substitution (arguments position)
  | _, _, _, mapping, substitution, .lam domain codomain body => by
      simp only [TermExpr.rename, TermExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) codomain,
        TermExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .app domain body function argument => by
      simp only [TermExpr.rename, TermExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        TermExpr.substitute_rename mapping substitution function,
        TermExpr.substitute_rename mapping substitution argument, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .pair domain body first second => by
      simp only [TermExpr.rename, TermExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        TermExpr.substitute_rename mapping substitution first,
        TermExpr.substitute_rename mapping substitution second, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .fst domain body pair => by
      simp only [TermExpr.rename, TermExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        TermExpr.substitute_rename mapping substitution pair, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .snd domain body pair => by
      simp only [TermExpr.rename, TermExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        TermExpr.substitute_rename mapping substitution pair, liftSubstitution_precompose]
  | _, _, _, mapping, substitution, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, TermExpr.substitute,
        TypeExpr.substitute_rename mapping substitution domain,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) body,
        TypeExpr.substitute_rename (liftRenaming mapping) (liftSubstitution substitution) motive,
        TermExpr.substitute_rename (liftRenaming (liftRenaming mapping))
          (liftSubstitution (liftSubstitution substitution)) branch,
        TermExpr.substitute_rename mapping substitution pair, liftSubstitution_precompose]

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
    (second : Substitution S m k) (type : TypeExpr S n),
    (type.substitute first).substitute second =
      type.substitute (fun index => (first index).substitute second)
  | _, _, _, first, second, .family symbol arguments => by
      simp only [TypeExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_comp first second (arguments position)
  | _, _, _, first, second, .pi domain body => by
      simp only [TypeExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        liftSubstitution_comp]
  | _, _, _, first, second, .sigma domain body => by
      simp only [TypeExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        liftSubstitution_comp]

theorem TermExpr.substitute_comp : ∀ {n m k : Nat} (first : Substitution S n m)
    (second : Substitution S m k) (term : TermExpr S n),
    (term.substitute first).substitute second =
      term.substitute (fun index => (first index).substitute second)
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, first, second, .primitive symbol arguments => by
      simp only [TermExpr.substitute]
      congr 1
      funext position
      exact TermExpr.substitute_comp first second (arguments position)
  | _, _, _, first, second, .lam domain codomain body => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) codomain,
        TermExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        liftSubstitution_comp]
  | _, _, _, first, second, .app domain body function argument => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        TermExpr.substitute_comp first second function, TermExpr.substitute_comp first second argument,
        liftSubstitution_comp]
  | _, _, _, first, second, .pair domain body left right => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        TermExpr.substitute_comp first second left, TermExpr.substitute_comp first second right,
        liftSubstitution_comp]
  | _, _, _, first, second, .fst domain body pair => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        TermExpr.substitute_comp first second pair, liftSubstitution_comp]
  | _, _, _, first, second, .snd domain body pair => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        TermExpr.substitute_comp first second pair, liftSubstitution_comp]
  | _, _, _, first, second, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.substitute, TypeExpr.substitute_comp first second domain,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) body,
        TypeExpr.substitute_comp (liftSubstitution first) (liftSubstitution second) motive,
        TermExpr.substitute_comp (liftSubstitution (liftSubstitution first))
          (liftSubstitution (liftSubstitution second)) branch,
        TermExpr.substitute_comp first second pair, liftSubstitution_comp]

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
