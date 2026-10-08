import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntax

/-!
# Renaming external dependent types and all their binders

Type annotations and primitive argument tuples are renamed together with
terms. Dependent codomains and the pair motive use one lifted mapping;
the full pair-elimination branch uses two.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

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
  | _, _, mapping, .family symbol arguments =>
      .family symbol (fun position => (arguments position).rename mapping)
  | _, _, mapping, .pi domain body =>
      .pi (domain.rename mapping) (body.rename (liftRenaming mapping))
  | _, _, mapping, .sigma domain body =>
      .sigma (domain.rename mapping) (body.rename (liftRenaming mapping))

def TermExpr.rename : {n m : Nat} → Renaming n m → TermExpr S n → TermExpr S m
  | _, _, mapping, .var index => .var (mapping index)
  | _, _, mapping, .primitive symbol arguments =>
      .primitive symbol (fun position => (arguments position).rename mapping)
  | _, _, mapping, .lam domain codomain body =>
      .lam (domain.rename mapping) (codomain.rename (liftRenaming mapping))
        (body.rename (liftRenaming mapping))
  | _, _, mapping, .app domain body function argument =>
      .app (domain.rename mapping) (body.rename (liftRenaming mapping))
        (function.rename mapping) (argument.rename mapping)
  | _, _, mapping, .pair domain body first second =>
      .pair (domain.rename mapping) (body.rename (liftRenaming mapping))
        (first.rename mapping) (second.rename mapping)
  | _, _, mapping, .fst domain body pair =>
      .fst (domain.rename mapping) (body.rename (liftRenaming mapping)) (pair.rename mapping)
  | _, _, mapping, .snd domain body pair =>
      .snd (domain.rename mapping) (body.rename (liftRenaming mapping)) (pair.rename mapping)
  | _, _, mapping, .sigmaElim domain body motive branch pair =>
      .sigmaElim (domain.rename mapping) (body.rename (liftRenaming mapping))
        (motive.rename (liftRenaming mapping))
        (branch.rename (liftRenaming (liftRenaming mapping))) (pair.rename mapping)

end

mutual

@[simp] theorem TypeExpr.rename_identity : ∀ {n : Nat} (type : TypeExpr S n),
    type.rename id = type
  | _, .family symbol arguments => by
      simp only [TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_identity (arguments position)
  | _, .pi domain body => by
      simp only [TypeExpr.rename, liftRenaming_identity,
        TypeExpr.rename_identity domain, TypeExpr.rename_identity body]
  | _, .sigma domain body => by
      simp only [TypeExpr.rename, liftRenaming_identity,
        TypeExpr.rename_identity domain, TypeExpr.rename_identity body]

@[simp] theorem TermExpr.rename_identity : ∀ {n : Nat} (term : TermExpr S n),
    term.rename id = term
  | _, .var _ => rfl
  | _, .primitive symbol arguments => by
      simp only [TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_identity (arguments position)
  | _, .lam domain codomain body => by
      simp only [TermExpr.rename, liftRenaming_identity,
        TypeExpr.rename_identity domain, TypeExpr.rename_identity codomain, TermExpr.rename_identity body]
  | _, .app domain body function argument => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain,
        TypeExpr.rename_identity body, TermExpr.rename_identity function, TermExpr.rename_identity argument]
  | _, .pair domain body first second => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain,
        TypeExpr.rename_identity body, TermExpr.rename_identity first, TermExpr.rename_identity second]
  | _, .fst domain body pair => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain,
        TypeExpr.rename_identity body, TermExpr.rename_identity pair]
  | _, .snd domain body pair => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain,
        TypeExpr.rename_identity body, TermExpr.rename_identity pair]
  | _, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, liftRenaming_identity, TypeExpr.rename_identity domain,
        TypeExpr.rename_identity body, TypeExpr.rename_identity motive,
        TermExpr.rename_identity branch, TermExpr.rename_identity pair]

end

mutual

theorem TypeExpr.rename_comp : ∀ {n m k : Nat} (first : Renaming n m) (second : Renaming m k)
    (type : TypeExpr S n), (type.rename first).rename second = type.rename (second ∘ first)
  | _, _, _, first, second, .family symbol arguments => by
      simp only [TypeExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_comp first second (arguments position)
  | _, _, _, first, second, .pi domain body => by
      simp only [TypeExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) body, liftRenaming_comp]
  | _, _, _, first, second, .sigma domain body => by
      simp only [TypeExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) body, liftRenaming_comp]

theorem TermExpr.rename_comp : ∀ {n m k : Nat} (first : Renaming n m) (second : Renaming m k)
    (term : TermExpr S n), (term.rename first).rename second = term.rename (second ∘ first)
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, first, second, .primitive symbol arguments => by
      simp only [TermExpr.rename]
      congr 1
      funext position
      exact TermExpr.rename_comp first second (arguments position)
  | _, _, _, first, second, .lam domain codomain body => by
      simp only [TermExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) codomain,
        TermExpr.rename_comp (liftRenaming first) (liftRenaming second) body, liftRenaming_comp]
  | _, _, _, first, second, .app domain body function argument => by
      simp only [TermExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) body,
        TermExpr.rename_comp first second function, TermExpr.rename_comp first second argument,
        liftRenaming_comp]
  | _, _, _, first, second, .pair domain body left right => by
      simp only [TermExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) body,
        TermExpr.rename_comp first second left, TermExpr.rename_comp first second right,
        liftRenaming_comp]
  | _, _, _, first, second, .fst domain body pair => by
      simp only [TermExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) body,
        TermExpr.rename_comp first second pair, liftRenaming_comp]
  | _, _, _, first, second, .snd domain body pair => by
      simp only [TermExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) body,
        TermExpr.rename_comp first second pair, liftRenaming_comp]
  | _, _, _, first, second, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename, TypeExpr.rename_comp first second domain,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) body,
        TypeExpr.rename_comp (liftRenaming first) (liftRenaming second) motive,
        TermExpr.rename_comp (liftRenaming (liftRenaming first))
          (liftRenaming (liftRenaming second)) branch,
        TermExpr.rename_comp first second pair, liftRenaming_comp]

end

/-- Looking up a declaration weakens its type past every later declaration. -/
def ContextExpr.lookup : {n : Nat} → ContextExpr S n → Fin n → TypeExpr S n
  | _, .snoc previous type, index =>
      Fin.cases (type.rename Fin.succ) (fun prior => (previous.lookup prior).rename Fin.succ) index

@[simp] theorem ContextExpr.lookup_zero {n : Nat} (context : ContextExpr S n) (type : TypeExpr S n) :
    (context.snoc type).lookup 0 = type.rename Fin.succ := rfl

@[simp] theorem ContextExpr.lookup_succ {n : Nat} (context : ContextExpr S n) (type : TypeExpr S n)
    (index : Fin n) : (context.snoc type).lookup index.succ = (context.lookup index).rename Fin.succ := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
