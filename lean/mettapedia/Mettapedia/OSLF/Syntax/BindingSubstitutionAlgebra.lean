import Mettapedia.OSLF.Syntax.FreeBindingTerms
import Mettapedia.OSLF.Syntax.TermClone

/-!
# Typed semantic substitution and the established multisorted clone

Raw binding algebras interpret constructors but cannot yet interpret
substitution of semantic values. A substitution algebra supplies typed
variables and simultaneous substitution at every context and sort. Its
unit and associativity laws yield the repository's established multisorted
clone, with positional environments recovered from typed variables.

The actual term algebra is an instance. The comparison below relates its
semantic substitution to `termClone` pointwise rather than presenting a
second unconnected clone calculus. Binding-operation compatibility and
equation models are subsequent obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra

open Mettapedia.GSLT.LanguageDef

universe u

variable {S : Signature}

/-- A semantic environment assigns a value to each typed variable. -/
abbrev Environment (S : Signature)
    (F : Ctx S → S.Srt → Type u) (Γ Δ : Ctx S) : Type u :=
  (s : S.Srt) → Var Γ s → F Δ s

/-- Read a positional environment as a typed semantic environment. -/
def fromPositions {F : Ctx S → S.Srt → Type u} :
    (Γ : Ctx S) → {Δ : Ctx S} →
      ((i : Fin Γ.length) → F Δ (Γ.get i)) → Environment S F Γ Δ
  | [], _, _ => fun _ v => nomatch v
  | _ :: Γ, _, env => fun _ v =>
      match v with
      | .zero => env ⟨0, Nat.succ_pos _⟩
      | .succ w => fromPositions Γ (fun i => env i.succ) _ w

theorem fromPositions_varOfIdx {F : Ctx S → S.Srt → Type u} :
    ∀ (Γ : Ctx S) {Δ : Ctx S}
      (env : (i : Fin Γ.length) → F Δ (Γ.get i))
      (i : Fin Γ.length),
      fromPositions Γ env _ (varOfIdx Γ i) = env i
  | _ :: _, _, _, ⟨0, _⟩ => rfl
  | _ :: Γ, _, env, ⟨k + 1, h⟩ => by
      exact fromPositions_varOfIdx Γ (fun i => env i.succ)
        ⟨k, Nat.lt_of_succ_lt_succ h⟩

theorem fromPositions_ofEnvironment {F : Ctx S → S.Srt → Type u} :
    ∀ {Γ Δ : Ctx S} (env : Environment S F Γ Δ)
      {s : S.Srt} (x : Var Γ s),
      fromPositions Γ (fun i => env _ (varOfIdx Γ i)) s x = env s x
  | _ :: _, _, _env, _, .zero => rfl
  | _ :: Γ, _, env, _, .succ x =>
      fromPositions_ofEnvironment
        (Γ := Γ) (fun s v => env s (.succ v)) x

/-- A semantic carrier with positional variables and simultaneous
substitution. These are the clone laws in the typed-variable notation. -/
structure Algebra (S : Signature) where
  Carrier : Ctx S → S.Srt → Type u
  injectVar : {Γ : Ctx S} → {s : S.Srt} → Var Γ s → Carrier Γ s
  substitute : {Γ Δ : Ctx S} → {s : S.Srt} →
    Environment S Carrier Γ Δ → Carrier Γ s → Carrier Δ s
  substitute_var : ∀ {Γ Δ : Ctx S}
    (env : Environment S Carrier Γ Δ) {s : S.Srt} (x : Var Γ s),
    substitute env (injectVar x) = env s x
  substitute_identity : ∀ {Γ : Ctx S} {s : S.Srt} (x : Carrier Γ s),
    substitute (fun _ v => injectVar v) x = x
  substitute_comp : ∀ {Γ Δ Θ : Ctx S} {s : S.Srt}
    (first : Environment S Carrier Γ Δ)
    (second : Environment S Carrier Δ Θ)
    (x : Carrier Γ s),
    substitute second (substitute first x) =
      substitute (fun sort v => substitute second (first sort v)) x

/-- Reindex one semantic value into a context with one fresh leading
variable. Its implementation uses semantic substitution, not syntax. -/
def Algebra.weaken (A : Algebra.{u} S) {Γ : Ctx S} {sort fresh : S.Srt}
    (x : A.Carrier Γ sort) : A.Carrier (fresh :: Γ) sort :=
  A.substitute (fun _ v => A.injectVar (.succ v)) x

/-- Extend a semantic environment beneath an authored binder list. Bound
variables remain projections; older values are weakened past them. -/
def Algebra.liftEnvironment (A : Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Environment S A.Carrier Γ Δ) :
    (binders : List S.Srt) →
      Environment S A.Carrier (binders ++ Γ) (binders ++ Δ)
  | [] => env
  | _ :: binders => fun _ v =>
      match v with
      | .zero => A.injectVar .zero
      | .succ old => A.weaken (A.liftEnvironment env binders _ old)

theorem Algebra.liftEnvironment_zero (A : Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Environment S A.Carrier Γ Δ)
    {fresh : S.Srt} (binders : List S.Srt) :
    A.liftEnvironment env (fresh :: binders) fresh Var.zero =
    A.injectVar Var.zero := rfl

/-- Substitute a vector of semantic operator arguments. Each head uses the
environment lifted past that argument's own binder list. -/
def Algebra.substituteArgs (A : Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Environment S A.Carrier Γ Δ) :
    {arity : List (List S.Srt × S.Srt)} →
      FreeBindingTerms.FamilyArgs S A.Carrier arity Γ →
        FreeBindingTerms.FamilyArgs S A.Carrier arity Δ
  | _, .nil => .nil
  | _, .cons (bs := binders) head tail =>
      .cons (A.substitute (A.liftEnvironment env binders) head)
        (A.substituteArgs env tail)

/-- If two same-sort projections collapse, semantic substitution cannot
respect arbitrary environments distinguishing those projections. This is the
precise reason the raw operator-count algebra is not yet a substitution model. -/
theorem no_zero_projection_substitution (sort : S.Srt) :
    ¬ ∃ substitute :
      Environment S (fun _ _ => Nat) [sort, sort] [] → Nat → Nat,
      ∀ (env : Environment S (fun _ _ => Nat) [sort, sort] [])
        (x : Var [sort, sort] sort), substitute env 0 = env sort x := by
  rintro ⟨substitute, law⟩
  let env : Environment S (fun _ _ => Nat) [sort, sort] [] :=
    fun _ v =>
      match v with
      | .zero => 0
      | .succ .zero => 1
  have first := law env Var.zero
  have second := law env (Var.succ Var.zero)
  have contradictory : (0 : Nat) = 1 := first.symm.trans second
  cases contradictory

theorem fromPositions_substitute (A : Algebra.{u} S) :
    ∀ {Γ Δ Θ : Ctx S}
      (env : (i : Fin Γ.length) → A.Carrier Δ (Γ.get i))
      (later : Environment S A.Carrier Δ Θ)
      {s : S.Srt} (x : Var Γ s),
      fromPositions Γ (fun i => A.substitute later (env i)) s x =
        A.substitute later (fromPositions Γ env s x)
  | _ :: _, _, _, _, _, _, .zero => rfl
  | _ :: Γ, _, _, env, later, _, .succ x =>
      fromPositions_substitute A (Γ := Γ) (fun i => env i.succ) later x

/-- Typed semantic substitution induces the already established abstract
multisorted clone; no new substitution laws are postulated here. -/
def Algebra.toClone (A : Algebra.{u} S) : MultiSortedClone.{0, u} S.Srt where
  Hom := A.Carrier
  project i := A.injectVar (varOfIdx _ i)
  substitute x env := A.substitute (fromPositions _ env) x
  substitute_project env i := by
    rw [A.substitute_var]
    exact fromPositions_varOfIdx _ env i
  substitute_projects := by
    intro Γ output x
    have env_eq :
        fromPositions Γ (fun i => A.injectVar (varOfIdx Γ i)) =
          (fun s v => A.injectVar v : Environment S A.Carrier Γ Γ) := by
      funext s v
      exact fromPositions_ofEnvironment
        (fun s v => A.injectVar v : Environment S A.Carrier Γ Γ) v
    rw [env_eq]
    exact A.substitute_identity x
  substitute_assoc x first second := by
    rw [A.substitute_comp]
    congr 1
    funext s v
    exact (fromPositions_substitute A first (fromPositions _ second) v).symm

/-- The repository's actual term substitution supplies the semantic laws. -/
def terms (S : Signature) : Algebra S where
  Carrier := Term S
  injectVar := Term.var
  substitute := bind
  substitute_var := by intro Γ Δ env s x; rfl
  substitute_identity := by intro Γ s x; exact bind_id x
  substitute_comp := by
    intro Γ Δ Θ s first second x
    exact bind_comp first second x

/-- Semantic lifting in the actual term algebra agrees with the existing
capture-avoiding syntactic lift beneath an arbitrary binder list. -/
theorem terms_liftEnvironment_eq_liftSub {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) :
    ∀ (binders : List S.Srt),
      (terms S).liftEnvironment sigma binders = liftSub sigma binders
  | [] => rfl
  | _ :: binders => by
      funext sort v
      cases v with
      | zero => rfl
      | succ old =>
          change bind (fun _ v => Term.var (.succ v))
              ((terms S).liftEnvironment sigma binders sort old) =
            weaken (liftSub sigma binders sort old)
          rw [terms_liftEnvironment_eq_liftSub sigma binders]
          exact bind_var_eq_rename (fun _ v => Var.succ v) _

/-- The generic semantic argument operation specializes to the existing
capture-avoiding `bindArgs` for every arity and binder list. -/
theorem terms_substituteArgs_syntaxToFamily {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : Args S arity Γ),
      (terms S).substituteArgs sigma (FreeBindingTerms.syntaxToFamily args) =
        FreeBindingTerms.syntaxToFamily (bindArgs sigma args)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      simp only [FreeBindingTerms.syntaxToFamily,
        Algebra.substituteArgs, bindArgs]
      rw [terms_liftEnvironment_eq_liftSub sigma binders]
      exact congrArg (FreeBindingTerms.FamilyArgs.cons
        (bind (liftSub sigma binders) head))
          (terms_substituteArgs_syntaxToFamily sigma tail)

theorem fromPositions_terms_apply :
    ∀ {Γ Δ : Ctx S}
      (env : (i : Fin Γ.length) → Term S Δ (Γ.get i))
      {s : S.Srt} (v : Var Γ s),
      fromPositions Γ env s v = substVar env s v
  | _ :: _, _, _, _, .zero => rfl
  | _ :: Γ, _, env, _, .succ v =>
      fromPositions_terms_apply (Γ := Γ) (fun i => env i.succ) v

/-- The positional action derived from typed semantic substitution agrees
pointwise with the established `termClone` action. -/
theorem terms_substitution_eq_termClone {Γ Δ : Ctx S} {s : S.Srt}
    (term : Term S Γ s)
    (env : (i : Fin Γ.length) → Term S Δ (Γ.get i)) :
    bind (fromPositions Γ env) term = (termClone S).substitute term env := by
  change bind (fromPositions Γ env) term = bind (substVar env) term
  have env_eq : fromPositions Γ env = substVar env := by
    funext sort v
    exact fromPositions_terms_apply env v
  rw [env_eq]

theorem terms_projection_eq_termClone {Γ : Ctx S}
    (i : Fin Γ.length) :
    (Term.var (varOfIdx Γ i) : Term S Γ (Γ.get i)) =
      (termClone S).project i := rfl

end Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
