import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementBinderSubstitution

/-!
# Assumption positions and dependent suffix substitution

Proposition assumptions preserve the number of data variables. Membership
retains each assumption's position, including duplicate assumptions. An authored
suffix may contain arbitrary variable types and further proposition assumptions.
Its substitution protects precisely the variables introduced in that suffix.

The comprehension projection replaces the original newest variable by the
forgetting of a refined variable. The substitution traverses every dependent
type and proposition in the remaining suffix.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u

variable {S : Symbols.{u}}

@[simp] theorem ContextExpr.lookup_assume {n : Nat} (context : ContextExpr S n)
    (predicate : PropExpr S n) (index : Fin n) :
    (context.assume predicate).lookup index = context.lookup index := rfl

inductive Hypothesis : {n : Nat} → ContextExpr S n → PropExpr S n → Type u where
  | here {n : Nat} (context : ContextExpr S n) (predicate : PropExpr S n) :
      Hypothesis (.assume context predicate) predicate
  | assumptionThere {n : Nat} {context : ContextExpr S n} {predicate : PropExpr S n}
      (member : Hypothesis context predicate) (newer : PropExpr S n) :
      Hypothesis (.assume context newer) predicate
  | variableThere {n : Nat} {context : ContextExpr S n} {predicate : PropExpr S n}
      (member : Hypothesis context predicate) (type : TypeExpr S n) :
      Hypothesis (.snoc context type) (predicate.rename Fin.succ)

namespace Hypothesis

def position : {n : Nat} → {context : ContextExpr S n} → {predicate : PropExpr S n} →
    Hypothesis context predicate → Nat
  | _, _, _, .here _ _ => 0
  | _, _, _, .assumptionThere member _ => member.position + 1
  | _, _, _, .variableThere member _ => member.position

theorem duplicate_positions_differ {n : Nat} (context : ContextExpr S n)
    (predicate : PropExpr S n) :
    Hypothesis.here (.assume context predicate) predicate ≠
      Hypothesis.assumptionThere (.here context predicate) predicate := by
  intro equal
  have impossible := congrArg position equal
  exact Nat.zero_ne_add_one 0 impossible

end Hypothesis

/-- Data and assumption declarations in a suffix remain independent raw syntax. -/
inductive ContextSuffix (S : Symbols.{u}) (n : Nat) : Nat → Type u where
  | nil : ContextSuffix S n 0
  | snoc {k : Nat} (previous : ContextSuffix S n k) (type : TypeExpr S (n + k)) :
      ContextSuffix S n (k + 1)
  | assume {k : Nat} (previous : ContextSuffix S n k) (predicate : PropExpr S (n + k)) :
      ContextSuffix S n k

def liftSubstitutionN {n m : Nat} (substitution : Substitution S n m) :
    (k : Nat) → Substitution S (n + k) (m + k)
  | 0 => substitution
  | k + 1 => liftSubstitution (liftSubstitutionN substitution k)

def weakenRenaming {n : Nat} : (k : Nat) → Renaming n (n + k)
  | 0 => id
  | k + 1 => Fin.succ ∘ weakenRenaming k

@[simp] theorem liftSubstitutionN_zero {n m : Nat} (substitution : Substitution S n m) :
    liftSubstitutionN substitution 0 = substitution := rfl

@[simp] theorem liftSubstitutionN_succ {n m : Nat} (substitution : Substitution S n m)
    (k : Nat) : liftSubstitutionN substitution (k + 1) =
      liftSubstitution (liftSubstitutionN substitution k) := rfl

theorem liftSubstitutionN_identity {n : Nat} (k : Nat) :
    liftSubstitutionN (TermExpr.var : Substitution S n n) k = TermExpr.var := by
  induction k with
  | zero => rfl
  | succ k previous => rw [liftSubstitutionN_succ, previous, liftSubstitution_identity]

theorem liftSubstitutionN_compose {n m l : Nat} (first : Substitution S n m)
    (second : Substitution S m l) (k : Nat) :
    liftSubstitutionN (composeSubstitution first second) k =
      composeSubstitution (liftSubstitutionN first k) (liftSubstitutionN second k) := by
  induction k with
  | zero => rfl
  | succ k previous =>
      rw [liftSubstitutionN_succ, previous, liftSubstitution_compose]
      rfl

namespace ContextSuffix

def plug {n : Nat} (context : ContextExpr S n) :
    {k : Nat} → ContextSuffix S n k → ContextExpr S (n + k)
  | _, .nil => context
  | _, .snoc previous type => .snoc (previous.plug context) type
  | _, .assume previous predicate => .assume (previous.plug context) predicate

def substitute {n m : Nat} (substitution : Substitution S n m) :
    {k : Nat} → ContextSuffix S n k → ContextSuffix S m k
  | _, .nil => .nil
  | k + 1, .snoc previous type =>
      .snoc (previous.substitute substitution) (type.substitute (liftSubstitutionN substitution k))
  | k, .assume previous predicate =>
      .assume (previous.substitute substitution) (predicate.substitute (liftSubstitutionN substitution k))

@[simp] theorem substitute_identity {n : Nat} : ∀ {k : Nat} (suffix : ContextSuffix S n k),
    suffix.substitute TermExpr.var = suffix
  | _, .nil => rfl
  | _, .snoc previous type => by
      simp only [substitute, substitute_identity previous, liftSubstitutionN_identity,
        TypeExpr.substitute_identity]
  | _, .assume previous predicate => by
      simp only [substitute, substitute_identity previous, liftSubstitutionN_identity,
        PropExpr.substitute_identity]

theorem substitute_composition {n m l : Nat} (first : Substitution S n m)
    (second : Substitution S m l) : ∀ {k : Nat} (suffix : ContextSuffix S n k),
    (suffix.substitute first).substitute second = suffix.substitute (composeSubstitution first second)
  | _, .nil => rfl
  | _, .snoc previous type => by
      simp only [substitute, substitute_composition first second previous,
        TypeExpr.substitute_comp]
      rw [liftSubstitutionN_compose]
      rfl
  | _, .assume previous predicate => by
      simp only [substitute, substitute_composition first second previous,
        PropExpr.substitute_comp]
      rw [liftSubstitutionN_compose]
      rfl

end ContextSuffix

theorem PropExpr.substitute_protected_weaken {n m : Nat} (substitution : Substitution S n m)
    (predicate : PropExpr S (n + 1)) :
    (predicate.rename (liftRenaming Fin.succ)).substitute
        (liftSubstitution (liftSubstitution substitution)) =
      (predicate.substitute (liftSubstitution substitution)).rename (liftRenaming Fin.succ) := by
  rw [PropExpr.substitute_rename, PropExpr.rename_substitute]
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      simp only [Function.comp_apply, liftRenaming_succ, liftSubstitution_succ,
        TermExpr.rename_comp]
      rfl

/-- The typed comprehension rules admit this substitution from the refined
variable context to the original variable context. -/
def comprehensionProjection {n : Nat} (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) : Substitution S (n + 1) (n + 1) :=
  Fin.cases (.forget (domain.rename Fin.succ)
    (predicate.rename (liftRenaming Fin.succ)) (.var 0)) (fun index => .var index.succ)

@[simp] theorem comprehensionProjection_zero {n : Nat} (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) :
    comprehensionProjection domain predicate 0 =
      .forget (domain.rename Fin.succ) (predicate.rename (liftRenaming Fin.succ)) (.var 0) := rfl

@[simp] theorem comprehensionProjection_succ {n : Nat} (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (index : Fin n) :
    comprehensionProjection domain predicate index.succ = .var index.succ := rfl

theorem comprehensionProjection_substitution {n m : Nat} (substitution : Substitution S n m)
    (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) :
    composeSubstitution (comprehensionProjection domain predicate) (liftSubstitution substitution) =
      composeSubstitution (liftSubstitution substitution)
        (comprehensionProjection (domain.substitute substitution)
          (predicate.substitute (liftSubstitution substitution))) := by
  funext index
  cases index using Fin.cases with
  | zero =>
      simp only [composeSubstitution, comprehensionProjection_zero, liftSubstitution_zero,
        TermExpr.substitute, TypeExpr.substitute_weaken, PropExpr.substitute_protected_weaken]
  | succ index =>
      change (substitution index).rename Fin.succ =
        ((substitution index).rename Fin.succ).substitute
          (comprehensionProjection (domain.substitute substitution)
            (predicate.substitute (liftSubstitution substitution)))
      rw [TermExpr.substitute_rename]
      exact (TermExpr.substitute_variables Fin.succ (substitution index)).symm

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
