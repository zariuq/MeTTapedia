import Mathlib.Data.Fin.Basic

/-!
# A scoped dependent quantifier presentation

This grammar has one object sort, named atomic predicates of one object,
dependent products and dependent sums over that object sort, and explicit
object substitutions. It is independent of its semantic interpretation.
It presents a fixed-object-sort quantifier fragment, rather than arbitrary
variable-type context comprehension or universes.

Proof terms retain their declaration names and each introduction, application
and substitution node. Equalities are generated separately from those trees.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent

universe u v w

inductive ObjectTerm (Constant : Type u) : Nat → Type u where
  | var {n : Nat} (index : Fin n) : ObjectTerm Constant n
  | constant {n : Nat} (name : Constant) : ObjectTerm Constant n
  deriving DecidableEq

abbrev ObjectSubstitution (Constant : Type u) (n m : Nat) :=
  Fin m → ObjectTerm Constant n

namespace ObjectTerm

variable {Constant : Type u} {n m k : Nat}

def substitute (substitution : ObjectSubstitution Constant n m) :
    ObjectTerm Constant m → ObjectTerm Constant n
  | .var index => substitution index
  | .constant name => .constant name

def weaken : ObjectTerm Constant n → ObjectTerm Constant (n + 1)
  | .var index => .var index.succ
  | .constant name => .constant name

@[simp] theorem substitute_identity (term : ObjectTerm Constant n) :
    substitute (fun index => .var index) term = term := by
  cases term <;> rfl

@[simp] theorem substitute_compose
    (earlier : ObjectSubstitution Constant n m)
    (later : ObjectSubstitution Constant m k) (term : ObjectTerm Constant k) :
    substitute earlier (substitute later term) =
      substitute (fun index => substitute earlier (later index)) term := by
  cases term <;> rfl

end ObjectTerm

namespace ObjectSubstitution

variable {Constant : Type u} {n m k : Nat}

def identity : ObjectSubstitution Constant n n := fun index => .var index

def compose (earlier : ObjectSubstitution Constant n m)
    (later : ObjectSubstitution Constant m k) : ObjectSubstitution Constant n k :=
  fun index => ObjectTerm.substitute earlier (later index)

def weaken : ObjectSubstitution Constant (n + 1) n := fun index => .var index.succ

def lift (substitution : ObjectSubstitution Constant n m) :
    ObjectSubstitution Constant (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun index => ObjectTerm.weaken (substitution index))

def instantiate (argument : ObjectTerm Constant n) :
    ObjectSubstitution Constant n (n + 1) :=
  Fin.cases argument (fun index => .var index)

@[simp] theorem compose_identity (substitution : ObjectSubstitution Constant n m) :
    compose substitution identity = substitution := by
  funext index
  rfl

@[simp] theorem identity_compose (substitution : ObjectSubstitution Constant n m) :
    compose identity substitution = substitution := by
  funext index
  exact ObjectTerm.substitute_identity _

@[simp] theorem compose_assoc (first : ObjectSubstitution Constant n m)
    (second : ObjectSubstitution Constant m k) {l : Nat}
    (third : ObjectSubstitution Constant k l) :
    compose first (compose second third) = compose (compose first second) third := by
  funext index
  exact ObjectTerm.substitute_compose _ _ _

@[simp] theorem lift_zero (substitution : ObjectSubstitution Constant n m) :
    lift substitution 0 = .var 0 := rfl

@[simp] theorem lift_succ (substitution : ObjectSubstitution Constant n m) (index : Fin m) :
    lift substitution index.succ = ObjectTerm.weaken (substitution index) := rfl

@[simp] theorem instantiate_zero (argument : ObjectTerm Constant n) :
    instantiate argument 0 = argument := rfl

@[simp] theorem instantiate_succ (argument : ObjectTerm Constant n) (index : Fin n) :
    instantiate argument index.succ = .var index := rfl

/-- Lifting substitution protects the newly bound object. -/
theorem substitute_lift_weaken (substitution : ObjectSubstitution Constant n m)
    (term : ObjectTerm Constant m) :
    ObjectTerm.substitute (lift substitution) (ObjectTerm.weaken term) =
      ObjectTerm.weaken (ObjectTerm.substitute substitution term) := by
  cases term <;> rfl

theorem instantiate_weaken (argument : ObjectTerm Constant n) (term : ObjectTerm Constant n) :
    ObjectTerm.substitute (instantiate argument) (ObjectTerm.weaken term) = term := by
  cases term <;> rfl

@[simp] theorem lift_identity : lift (identity : ObjectSubstitution Constant n n) = identity := by
  funext index
  refine Fin.cases rfl (fun prior => rfl) index

/-- The same bound variable survives either order of composing lifted substitutions. -/
theorem lift_compose (earlier : ObjectSubstitution Constant n m)
    (later : ObjectSubstitution Constant m k) :
    lift (compose earlier later) = compose (lift earlier) (lift later) := by
  funext index
  refine Fin.cases rfl (fun prior => ?_) index
  exact (substitute_lift_weaken earlier (later prior)).symm

/-- Opening a binder commutes with substitution when its argument and
older tuple are both changed by the same substitution. -/
theorem instantiate_compose (substitution : ObjectSubstitution Constant n m)
    (argument : ObjectTerm Constant m) :
    compose substitution (instantiate argument) =
      compose (instantiate (ObjectTerm.substitute substitution argument)) (lift substitution) := by
  funext index
  refine Fin.cases rfl (fun prior => ?_) index
  exact (instantiate_weaken _ (substitution prior)).symm

end ObjectSubstitution

inductive Formula (Constant : Type u) (Predicate : Type v) : Nat → Type (max u v) where
  | atom {n : Nat} (name : Predicate) (argument : ObjectTerm Constant n) : Formula Constant Predicate n
  | pi {n : Nat} (body : Formula Constant Predicate (n + 1)) : Formula Constant Predicate n
  | sigma {n : Nat} (body : Formula Constant Predicate (n + 1)) : Formula Constant Predicate n
  | substitute {n m : Nat} (body : Formula Constant Predicate m)
      (substitution : ObjectSubstitution Constant n m) : Formula Constant Predicate n

/-- A declaration is indexed by its independently authored judgment. -/
inductive Proof {Constant : Type u} {Predicate : Type v}
    (Declaration : (n : Nat) → Formula Constant Predicate n → Type w) :
    (n : Nat) → Formula Constant Predicate n → Type (max u v w) where
  | declaration {n : Nat} {formula : Formula Constant Predicate n}
      (name : Declaration n formula) : Proof Declaration n formula
  | substitute {n m : Nat} {formula : Formula Constant Predicate m}
      (body : Proof Declaration m formula) (substitution : ObjectSubstitution Constant n m) :
      Proof Declaration n (.substitute formula substitution)
  | lam {n : Nat} {body : Formula Constant Predicate (n + 1)}
      (proof : Proof Declaration (n + 1) body) : Proof Declaration n (.pi body)
  | app {n : Nat} {body : Formula Constant Predicate (n + 1)}
      (function : Proof Declaration n (.pi body)) (argument : ObjectTerm Constant n) :
      Proof Declaration n (.substitute body (ObjectSubstitution.instantiate argument))
  | pair {n : Nat} {body : Formula Constant Predicate (n + 1)}
      (first : ObjectTerm Constant n)
      (second : Proof Declaration n (.substitute body (ObjectSubstitution.instantiate first))) :
      Proof Declaration n (.sigma body)

/-- Computation identifies proof terms, while the authored trees remain
available as distinct terms before that equation is imposed. -/
inductive ProofEquation {Constant : Type u} {Predicate : Type v}
    {Declaration : (n : Nat) → Formula Constant Predicate n → Type w} :
    {n : Nat} → {formula : Formula Constant Predicate n} →
      Proof Declaration n formula → Proof Declaration n formula → Prop where
  | refl {n : Nat} {formula : Formula Constant Predicate n} (term : Proof Declaration n formula) :
      ProofEquation term term
  | symm {n : Nat} {formula : Formula Constant Predicate n}
      {first second : Proof Declaration n formula} :
      ProofEquation first second → ProofEquation second first
  | trans {n : Nat} {formula : Formula Constant Predicate n}
      {first middle last : Proof Declaration n formula} :
      ProofEquation first middle → ProofEquation middle last → ProofEquation first last
  | beta {n : Nat} {body : Formula Constant Predicate (n + 1)}
      (proof : Proof Declaration (n + 1) body) (argument : ObjectTerm Constant n) :
      ProofEquation (.app (.lam proof) argument)
        (.substitute proof (ObjectSubstitution.instantiate argument))
  | substitute {n m : Nat} {formula : Formula Constant Predicate m}
      {first second : Proof Declaration m formula} :
      ProofEquation first second → (substitution : ObjectSubstitution Constant n m) →
      ProofEquation (.substitute first substitution) (.substitute second substitution)
  | lam {n : Nat} {body : Formula Constant Predicate (n + 1)}
      {first second : Proof Declaration (n + 1) body} :
      ProofEquation first second → ProofEquation (.lam first) (.lam second)
  | app {n : Nat} {body : Formula Constant Predicate (n + 1)}
      {first second : Proof Declaration n (.pi body)} :
      ProofEquation first second → (argument : ObjectTerm Constant n) →
      ProofEquation (.app first argument) (.app second argument)
  | pair {n : Nat} {body : Formula Constant Predicate (n + 1)}
      (argument : ObjectTerm Constant n)
      {first second : Proof Declaration n (.substitute body (ObjectSubstitution.instantiate argument))} :
      ProofEquation first second → ProofEquation (.pair argument first) (.pair argument second)

namespace Proof

variable {Constant : Type u} {Predicate : Type v}
variable {Declaration : (n : Nat) → Formula Constant Predicate n → Type w}

/-- The originating declaration retains its own original scope and formula. -/
abbrev Origin := Σ n : Nat, Σ formula : Formula Constant Predicate n, Declaration n formula

def origin {n : Nat} {formula : Formula Constant Predicate n} :
    Proof Declaration n formula → Origin (Declaration := Declaration)
  | .declaration name => ⟨_, _, name⟩
  | .substitute body _ => body.origin
  | .lam body => body.origin
  | .app function _ => function.origin
  | .pair _ second => second.origin

/-- Generated beta and congruence can change the administrative tree but
cannot change its supplied primitive declaration. -/
theorem equation_origin {n : Nat} {formula : Formula Constant Predicate n}
    {first second : Proof Declaration n formula} (equation : ProofEquation first second) :
    first.origin = second.origin := by
  induction equation with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | beta _ _ => rfl
  | substitute _ _ ih => exact ih
  | lam _ ih => exact ih
  | app _ _ ih => exact ih
  | pair _ _ ih => exact ih

theorem declaration_origin_injective {n : Nat} {formula : Formula Constant Predicate n}
    {first second : Declaration n formula}
    (same : origin (.declaration first) = origin (.declaration second)) : first = second := by
  have tail : (⟨formula, first⟩ : Σ formula : Formula Constant Predicate n, Declaration n formula) =
      ⟨formula, second⟩ := eq_of_heq (Sigma.mk.inj same).2
  exact eq_of_heq (Sigma.mk.inj tail).2

/-- Administrative substitution and an application are retained separately. -/
def nodes {n : Nat} {formula : Formula Constant Predicate n} : Proof Declaration n formula → Nat
  | .declaration _ => 1
  | .substitute body _ => body.nodes + 1
  | .lam body => body.nodes + 1
  | .app function _ => function.nodes + 1
  | .pair _ second => second.nodes + 1

theorem beta_trees_distinct {n : Nat} {body : Formula Constant Predicate (n + 1)}
    (proof : Proof Declaration (n + 1) body) (argument : ObjectTerm Constant n) :
    Proof.app (Proof.lam proof) argument ≠
      Proof.substitute proof (ObjectSubstitution.instantiate argument) := by
  intro same
  have count := congrArg nodes same
  simp only [nodes] at count
  omega

end Proof

end Mettapedia.TypeTheory.Calculi.NativeDependent
