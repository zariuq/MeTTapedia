import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitution

/-!
# Opening proposition and refinement binders

The pair-context substitution is an actual substitution of authored terms.
Its newest value packs the two component variables with their renamed type
annotations. The resulting commuting square earns substitution of a motive
over a complete pair and of the corresponding two-component branch.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u

variable {S : Symbols.{u}} {n m k : Nat}

def composeSubstitution (first : Substitution S n m) (second : Substitution S m k) :
    Substitution S n k := fun index => (first index).substitute second

def extendSubstitution (substitution : Substitution S n m) (term : TermExpr S m) :
    Substitution S (n + 1) m := Fin.cases term substitution

def instantiate (term : TermExpr S n) : Substitution S (n + 1) n :=
  extendSubstitution TermExpr.var term

@[simp] theorem extendSubstitution_zero (substitution : Substitution S n m) (term : TermExpr S m) :
    extendSubstitution substitution term 0 = term := rfl

@[simp] theorem extendSubstitution_succ (substitution : Substitution S n m) (term : TermExpr S m)
    (index : Fin n) : extendSubstitution substitution term index.succ = substitution index := rfl

@[simp] theorem instantiate_zero (term : TermExpr S n) : instantiate term 0 = term := rfl

@[simp] theorem instantiate_succ (term : TermExpr S n) (index : Fin n) :
    instantiate term index.succ = .var index := rfl

@[simp] theorem liftSubstitution_identity :
    liftSubstitution (S := S) (TermExpr.var : Substitution S n n) = TermExpr.var := by
  funext index
  cases index using Fin.cases <;> rfl

@[simp] theorem composeSubstitution_identity (substitution : Substitution S n m) :
    composeSubstitution substitution TermExpr.var = substitution := by
  funext index
  exact TermExpr.substitute_identity _

@[simp] theorem identity_composeSubstitution (substitution : Substitution S n m) :
    composeSubstitution TermExpr.var substitution = substitution := rfl

theorem composeSubstitution_assoc {l : Nat} (first : Substitution S n m)
    (second : Substitution S m k) (third : Substitution S k l) :
    composeSubstitution (composeSubstitution first second) third =
      composeSubstitution first (composeSubstitution second third) := by
  funext index
  exact TermExpr.substitute_comp _ _ _

theorem composeSubstitution_extend (first : Substitution S n m) (term : TermExpr S m)
    (second : Substitution S m k) :
    composeSubstitution (extendSubstitution first term) second =
      extendSubstitution (composeSubstitution first second) (term.substitute second) := by
  funext index
  cases index using Fin.cases <;> rfl

theorem liftSubstitution_compose (first : Substitution S n m) (second : Substitution S m k) :
    liftSubstitution (composeSubstitution first second) =
      composeSubstitution (liftSubstitution first) (liftSubstitution second) :=
  liftSubstitution_comp first second

@[simp] theorem TypeExpr.instantiate_weaken (argument : TermExpr S n) (type : TypeExpr S n) :
    (type.rename Fin.succ).substitute (instantiate argument) = type := by
  rw [TypeExpr.substitute_rename]
  exact type.substitute_identity

@[simp] theorem TermExpr.instantiate_weaken (argument : TermExpr S n) (term : TermExpr S n) :
    (term.rename Fin.succ).substitute (instantiate argument) = term := by
  rw [TermExpr.substitute_rename]
  exact term.substitute_identity

theorem TypeExpr.substitute_weaken (substitution : Substitution S n m) (type : TypeExpr S n) :
    (type.rename Fin.succ).substitute (liftSubstitution substitution) =
      (type.substitute substitution).rename Fin.succ := by
  rw [TypeExpr.substitute_rename, TypeExpr.rename_substitute]
  rfl

theorem TermExpr.substitute_weaken (substitution : Substitution S n m) (term : TermExpr S n) :
    (term.rename Fin.succ).substitute (liftSubstitution substitution) =
      (term.substitute substitution).rename Fin.succ := by
  rw [TermExpr.substitute_rename, TermExpr.rename_substitute]
  rfl

theorem instantiate_lift (substitution : Substitution S n m) (argument : TermExpr S n) :
    composeSubstitution (instantiate argument) substitution =
      composeSubstitution (liftSubstitution substitution) (instantiate (argument.substitute substitution)) := by
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      exact (TermExpr.instantiate_weaken _ (substitution index)).symm

theorem TypeExpr.substitute_instantiate (substitution : Substitution S n m)
    (type : TypeExpr S (n + 1)) (argument : TermExpr S n) :
    (type.substitute (instantiate argument)).substitute substitution =
      (type.substitute (liftSubstitution substitution)).substitute
        (instantiate (argument.substitute substitution)) := by
  rw [TypeExpr.substitute_comp, TypeExpr.substitute_comp]
  exact congrArg (fun mapping => type.substitute mapping) (instantiate_lift substitution argument)

theorem TermExpr.substitute_instantiate (substitution : Substitution S n m)
    (term : TermExpr S (n + 1)) (argument : TermExpr S n) :
    (term.substitute (instantiate argument)).substitute substitution =
      (term.substitute (liftSubstitution substitution)).substitute
        (instantiate (argument.substitute substitution)) := by
  rw [TermExpr.substitute_comp, TermExpr.substitute_comp]
  exact congrArg (fun mapping => term.substitute mapping) (instantiate_lift substitution argument)

theorem TypeExpr.rename_instantiate (mapping : Renaming n m)
    (type : TypeExpr S (n + 1)) (argument : TermExpr S n) :
    (type.substitute (instantiate argument)).rename mapping =
      (type.rename (liftRenaming mapping)).substitute (instantiate (argument.rename mapping)) := by
  rw [← TypeExpr.substitute_variables mapping,
    TypeExpr.substitute_instantiate, liftSubstitution_variables,
    TypeExpr.substitute_variables, TermExpr.substitute_variables]

theorem TermExpr.rename_instantiate (mapping : Renaming n m)
    (term : TermExpr S (n + 1)) (argument : TermExpr S n) :
    (term.substitute (instantiate argument)).rename mapping =
      (term.rename (liftRenaming mapping)).substitute (instantiate (argument.rename mapping)) := by
  rw [← TermExpr.substitute_variables mapping,
    TermExpr.substitute_instantiate, liftSubstitution_variables,
    TermExpr.substitute_variables, TermExpr.substitute_variables]

/-- The generic pair in the context containing its two components. -/
def genericPair (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) : TermExpr S (n + 2) :=
  .pair (domain.rename (Fin.succ ∘ Fin.succ))
    (body.rename (liftRenaming (Fin.succ ∘ Fin.succ))) (.var 1) (.var 0)

/-- Replace the newest pair variable by its two-component introduction. -/
def packSubstitution (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) :
    Substitution S (n + 1) (n + 2) :=
  Fin.cases (genericPair domain body) (fun index => .var index.succ.succ)

@[simp] theorem packSubstitution_zero (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) :
    packSubstitution domain body 0 = genericPair domain body := rfl

@[simp] theorem packSubstitution_succ (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (index : Fin n) : packSubstitution domain body index.succ = .var index.succ.succ := rfl

/-- The second-component annotation has precisely the original codomain
weakened past the new second component. -/
theorem genericPair_body (body : TypeExpr S (n + 1)) :
    (body.rename (liftRenaming (Fin.succ ∘ Fin.succ))).substitute
        (instantiate (.var (1 : Fin (n + 2)))) = body.rename Fin.succ := by
  rw [TypeExpr.substitute_rename, ← TypeExpr.substitute_variables Fin.succ]
  congr 1
  funext index
  cases index using Fin.cases <;> rfl

theorem TypeExpr.substitute_weaken_twice (substitution : Substitution S n m) (type : TypeExpr S n) :
    (type.rename (Fin.succ ∘ Fin.succ)).substitute
        (liftSubstitution (liftSubstitution substitution)) =
      (type.substitute substitution).rename (Fin.succ ∘ Fin.succ) := by
  rw [TypeExpr.substitute_rename, TypeExpr.rename_substitute]
  congr 1
  funext index
  exact TermExpr.rename_comp _ _ _

theorem genericPair_substitute (substitution : Substitution S n m)
    (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) :
    (genericPair domain body).substitute (liftSubstitution (liftSubstitution substitution)) =
      genericPair (domain.substitute substitution) (body.substitute (liftSubstitution substitution)) := by
  unfold genericPair
  simp only [TermExpr.substitute, TypeExpr.substitute_weaken_twice]
  congr 1
  rw [TypeExpr.substitute_rename, TypeExpr.rename_substitute]
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      simp only [Function.comp_apply, liftRenaming_succ, liftSubstitution_succ,
        TermExpr.rename_comp]
      rfl

/-- Packing a pair is natural for actual simultaneous substitutions. -/
theorem packSubstitution_square (substitution : Substitution S n m)
    (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) :
    composeSubstitution (packSubstitution domain body)
        (liftSubstitution (liftSubstitution substitution)) =
      composeSubstitution (liftSubstitution substitution)
        (packSubstitution (domain.substitute substitution) (body.substitute (liftSubstitution substitution))) := by
  funext index
  cases index using Fin.cases with
  | zero => exact genericPair_substitute substitution domain body
  | succ index =>
      change ((substitution index).rename Fin.succ).rename Fin.succ =
        ((substitution index).rename Fin.succ).substitute
          (packSubstitution (domain.substitute substitution) (body.substitute (liftSubstitution substitution)))
      rw [TermExpr.rename_comp, TermExpr.substitute_rename]
      exact ((substitution index).substitute_variables (Fin.succ ∘ Fin.succ)).symm

/-- A motive over the complete pair and its two-binder branch agree under
substitution through the actual packing map. -/
theorem TypeExpr.pairMotive_substitute (substitution : Substitution S n m)
    (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1)) :
    (motive.substitute (packSubstitution domain body)).substitute
        (liftSubstitution (liftSubstitution substitution)) =
      (motive.substitute (liftSubstitution substitution)).substitute
        (packSubstitution (domain.substitute substitution) (body.substitute (liftSubstitution substitution))) := by
  rw [TypeExpr.substitute_comp, TypeExpr.substitute_comp]
  exact congrArg (fun mapping => motive.substitute mapping) (packSubstitution_square substitution domain body)

/-- Opening both component binders preserves their ordered positions. -/
def instantiateComponents (first second : TermExpr S n) : Substitution S (n + 2) n :=
  extendSubstitution (instantiate first) second

@[simp] theorem instantiateComponents_zero (first second : TermExpr S n) :
    instantiateComponents first second 0 = second := rfl

@[simp] theorem instantiateComponents_one (first second : TermExpr S n) :
    instantiateComponents first second 1 = first := rfl

@[simp] theorem instantiateComponents_older (first second : TermExpr S n) (index : Fin n) :
    instantiateComponents first second index.succ.succ = .var index := rfl

theorem genericPair_instantiate (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) :
    (genericPair domain body).substitute (instantiateComponents first second) =
      .pair domain body first second := by
  unfold genericPair
  simp only [TermExpr.substitute, instantiateComponents_zero, instantiateComponents_one]
  have domainSame :
      (domain.rename (Fin.succ ∘ Fin.succ)).substitute (instantiateComponents first second) = domain := by
    rw [TypeExpr.substitute_rename]
    exact domain.substitute_identity
  rw [domainSame]
  congr 1
  rw [TypeExpr.substitute_rename]
  have mappingSame : liftSubstitution (instantiateComponents first second) ∘
      liftRenaming (Fin.succ ∘ Fin.succ) = (TermExpr.var : Substitution S (n + 1) (n + 1)) := by
    funext index
    cases index using Fin.cases <;> rfl
  rw [mappingSame, TypeExpr.substitute_identity]

/-- The motive of a supplied pair is the instantiated two-component motive. -/
theorem packSubstitution_instantiate (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) :
    composeSubstitution (packSubstitution domain body) (instantiateComponents first second) =
      instantiate (.pair domain body first second) := by
  funext index
  cases index using Fin.cases with
  | zero => exact genericPair_instantiate domain body first second
  | succ index => rfl

theorem TypeExpr.pairMotive_instantiate (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (first second : TermExpr S n) :
    (motive.substitute (packSubstitution domain body)).substitute (instantiateComponents first second) =
      motive.substitute (instantiate (.pair domain body first second)) := by
  rw [TypeExpr.substitute_comp]
  exact congrArg (fun mapping => motive.substitute mapping)
    (packSubstitution_instantiate domain body first second)

theorem TypeExpr.etaBody_instantiate (body : TypeExpr S (n + 1)) :
    (body.rename (liftRenaming (Fin.succ : Renaming n (n + 1)))).substitute
        (instantiate (.var (0 : Fin (n + 1)))) = body := by
  rw [TypeExpr.substitute_rename]
  have mappingSame : instantiate (S := S) (.var (0 : Fin (n + 1))) ∘
      liftRenaming (Fin.succ : Renaming n (n + 1)) = TermExpr.var := by
    funext index
    cases index using Fin.cases <;> rfl
  rw [mappingSame, TypeExpr.substitute_identity]


@[simp] theorem PropExpr.instantiate_weaken (argument : TermExpr S n) (type : PropExpr S n) :
    (type.rename Fin.succ).substitute (instantiate argument) = type := by
  rw [PropExpr.substitute_rename]
  exact type.substitute_identity

theorem PropExpr.substitute_weaken (substitution : Substitution S n m) (type : PropExpr S n) :
    (type.rename Fin.succ).substitute (liftSubstitution substitution) =
      (type.substitute substitution).rename Fin.succ := by
  rw [PropExpr.substitute_rename, PropExpr.rename_substitute]
  rfl

theorem PropExpr.substitute_instantiate (substitution : Substitution S n m)
    (type : PropExpr S (n + 1)) (argument : TermExpr S n) :
    (type.substitute (instantiate argument)).substitute substitution =
      (type.substitute (liftSubstitution substitution)).substitute
        (instantiate (argument.substitute substitution)) := by
  rw [PropExpr.substitute_comp, PropExpr.substitute_comp]
  exact congrArg (fun mapping => type.substitute mapping) (instantiate_lift substitution argument)

theorem PropExpr.rename_instantiate (mapping : Renaming n m)
    (type : PropExpr S (n + 1)) (argument : TermExpr S n) :
    (type.substitute (instantiate argument)).rename mapping =
      (type.rename (liftRenaming mapping)).substitute (instantiate (argument.rename mapping)) := by
  rw [← PropExpr.substitute_variables mapping,
    PropExpr.substitute_instantiate, liftSubstitution_variables,
    PropExpr.substitute_variables, TermExpr.substitute_variables]

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
