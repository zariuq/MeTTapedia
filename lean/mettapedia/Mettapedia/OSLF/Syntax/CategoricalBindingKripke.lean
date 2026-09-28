import Mettapedia.OSLF.Syntax.CategoricalBindingModel
import Mettapedia.OSLF.Syntax.BindingCloneFoldSubstitution

/-!
# Interpreting terms with metavariables by natural families of elements

At a metavariable context `N`, a term in context `Γ` of sort `s` is interpreted
by a family of generalized elements: at every stage `Z`, given an element of
the metavariable family and an environment for `Γ`, an element of the sort
object, natural in the stage. These families form a binding clone algebra for
the signature extended by the metavariables. Variables are read from the
environment, an operator is applied to the curried interpretations of its
arguments beneath their binders, and a metavariable is evaluated at its
arguments.

The interpretation of a term is the existing fold into this algebra, so the
substitution lemma is the existing `interpret_bind`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable {S : Signature} (M : Model S D)

/-- A natural family of generalized elements: the interpretation of a term at
metavariable context `N`, term context `Γ` and sort `s`. -/
@[ext]
structure Elem (N : List (MetaArity S)) (Γ : Ctx S) (s : S.Srt) : Type (max u v) where
  value : ∀ (Z : D), (Z ⟶ M.family N) → M.Env Z Γ → (Z ⟶ M.sort s)
  natural : ∀ {Z Z' : D} (h : Z' ⟶ Z) (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
    value Z' (h ≫ m) (M.restage h ρ) = h ≫ value Z m ρ

variable {M}

/-- The values of a semantic environment at a stage. -/
def envValue {N : List (MetaArity S)} {Γ Δ : Ctx S}
    (env : ∀ (γ : S.Srt), Var Γ γ → M.Elem N Δ γ) (Z : D) (m : Z ⟶ M.family N)
    (ρ : M.Env Z Δ) : M.Env Z Γ :=
  fun γ v => (env γ v).value Z m ρ

theorem envValue_restage {N : List (MetaArity S)} {Γ Δ : Ctx S}
    (env : ∀ (γ : S.Srt), Var Γ γ → M.Elem N Δ γ) {Z Z' : D} (h : Z' ⟶ Z)
    (m : Z ⟶ M.family N) (ρ : M.Env Z Δ) :
    envValue env Z' (h ≫ m) (M.restage h ρ) = M.restage h (envValue env Z m ρ) := by
  funext γ v
  exact (env γ v).natural h m ρ

variable (M)

/-- The tuple of curried argument interpretations, each beneath its binders. -/
def tupleArgs {N N' : List (MetaArity S)} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S},
      FamilyArgs (withMetas S N') (M.Elem N) arity Γ →
        ∀ (Z : D), (Z ⟶ M.family N) → M.Env Z Γ → (Z ⟶ M.family arity)
  | _, _, .nil, Z, _, _ => toUnit Z
  | _, _, .cons (bs := bs) head tail, Z, m, ρ =>
      lift (M.curry (head.value (M.ctx bs ⊗ Z) (snd _ _ ≫ m) (M.extendEnv bs ρ)))
        (tupleArgs tail Z m ρ)

/-- The tuple of interpretations of the arguments of a metavariable. -/
def tupleCtx {N N' : List (MetaArity S)} :
    ∀ (bs : List S.Srt) {Γ : Ctx S},
      FamilyArgs (withMetas S N') (M.Elem N) (bs.map fun b => ([], b)) Γ →
        ∀ (Z : D), (Z ⟶ M.family N) → M.Env Z Γ → (Z ⟶ M.ctx bs)
  | [], _, .nil, Z, _, _ => toUnit Z
  | _ :: bs, _, .cons head tail, Z, m, ρ => lift (head.value Z m ρ) (tupleCtx bs tail Z m ρ)

theorem tupleArgs_natural {N N' : List (MetaArity S)} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs (withMetas S N') (M.Elem N) arity Γ) {Z Z' : D} (h : Z' ⟶ Z)
      (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      M.tupleArgs args Z' (h ≫ m) (M.restage h ρ) = h ≫ M.tupleArgs args Z m ρ
  | _, _, .nil, _, _, _, _, _ => toUnit_unique _ _
  | _, _, .cons (bs := bs) head tail, _, _, h, m, ρ => by
      show lift _ _ = h ≫ lift _ _
      rw [comp_lift, tupleArgs_natural tail h m ρ, M.extendEnv_restage,
        ← M.curry_natural, ← head.natural, whiskerLeft_snd_assoc]

theorem tupleCtx_natural {N N' : List (MetaArity S)} :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (args : FamilyArgs (withMetas S N') (M.Elem N) (bs.map fun b => ([], b)) Γ)
      {Z Z' : D} (h : Z' ⟶ Z) (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      M.tupleCtx bs args Z' (h ≫ m) (M.restage h ρ) = h ≫ M.tupleCtx bs args Z m ρ
  | [], _, .nil, _, _, _, _, _ => toUnit_unique _ _
  | _ :: bs, _, .cons head tail, _, _, h, m, ρ => by
      show lift _ _ = h ≫ lift _ _
      rw [comp_lift, tupleCtx_natural bs tail h m ρ, head.natural]

/-- The substitution structure of natural families. -/
abbrev kripkeSubstitution (N : List (MetaArity S)) :
    BindingSubstitutionAlgebra.Algebra.{max u v} (withMetas S N) where
  Carrier := fun Γ s => M.Elem N Γ s
  injectVar := fun v => ⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩
  substitute := fun env x =>
    ⟨fun Z m ρ => x.value Z m (envValue env Z m ρ), fun h m ρ => by
      rw [envValue_restage, x.natural]⟩
  substitute_var := by intros; rfl
  substitute_identity := by intros; rfl
  substitute_comp := by intros; rfl

/-- The operator applied to the tupled arguments. -/
def opElem {N N' : List (MetaArity S)} {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : FamilyArgs (withMetas S N') (M.Elem N) (S.arity o) Γ) : M.Elem N Γ s where
  value := fun Z m ρ => M.tupleArgs args Z m ρ ≫ M.op o
  natural := fun h m ρ => by rw [M.tupleArgs_natural, Category.assoc]

/-- A metavariable evaluated at its arguments. -/
def metaElem {N : List (MetaArity S)} {Γ : Ctx S} (i : Fin N.length)
    (args : FamilyArgs (withMetas S N) (M.Elem N) ((N.get i).1.map fun b => ([], b)) Γ) :
    M.Elem N Γ (N.get i).2 where
  value := fun Z m ρ =>
    lift (M.tupleCtx (N.get i).1 args Z m ρ) (m ≫ M.familyProj N i) ≫ M.eval _ _
  natural := fun h m ρ => by
    rw [M.tupleCtx_natural, Category.assoc, ← comp_lift_assoc]

/-! ## Substitution commutes with the operations -/

theorem liftEnvironment_value {N : List (MetaArity S)} {Γ Δ : Ctx S}
    (env : ∀ (γ : S.Srt), Var Γ γ → M.Elem N Δ γ) (Z : D) (m : Z ⟶ M.family N)
    (ρ : M.Env Z Δ) :
    ∀ (bs : List S.Srt) {γ : S.Srt} (v : Var (bs ++ Γ) γ),
      ((M.kripkeSubstitution N).liftEnvironment env bs γ v).value (M.ctx bs ⊗ Z) (snd _ _ ≫ m)
        (M.extendEnv bs ρ) = M.extendEnv bs (envValue env Z m ρ) γ v
  | [], γ, v => by
      change (env γ v).value (𝟙_ D ⊗ Z) (snd _ _ ≫ m) (M.restage (snd _ _) ρ) = snd _ _ ≫ _
      rw [(env γ v).natural]
      rfl
  | b :: bs, γ, v => by
      revert v
      show ∀ v : Var (b :: (bs ++ Γ)) γ, _
      intro v
      cases v with
      | zero => rfl
      | succ w =>
          change ((M.kripkeSubstitution N).liftEnvironment env bs γ w).value
              ((M.sort b ⊗ M.ctx bs) ⊗ Z) (snd _ _ ≫ m)
              (M.restage (lift (fst _ _ ≫ snd _ _) (snd _ _)) (M.extendEnv bs ρ)) =
            lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ M.extendEnv bs (envValue env Z m ρ) γ w
          rw [← liftEnvironment_value env Z m ρ bs w,
            ← ((M.kripkeSubstitution N).liftEnvironment env bs γ w).natural, lift_snd_assoc]

theorem tupleArgs_substituteArgs {N : List (MetaArity S)} {Γ Δ : Ctx S}
    (env : ∀ (γ : S.Srt), Var Γ γ → M.Elem N Δ γ) (Z : D) (m : Z ⟶ M.family N)
    (ρ : M.Env Z Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)} (args : FamilyArgs (withMetas S N) (M.Elem N) arity Γ),
      M.tupleArgs ((M.kripkeSubstitution N).substituteArgs env args) Z m ρ =
        M.tupleArgs args Z m (envValue env Z m ρ)
  | _, .nil => rfl
  | _, .cons (bs := bs) head tail => by
      show lift _ _ = lift _ _
      rw [tupleArgs_substituteArgs env Z m ρ tail]
      congr 2
      change head.value (M.ctx bs ⊗ Z) (snd _ _ ≫ m)
          (envValue ((M.kripkeSubstitution N).liftEnvironment env bs) (M.ctx bs ⊗ Z) (snd _ _ ≫ m)
            (M.extendEnv bs ρ)) = _
      congr 1
      funext γ v
      exact M.liftEnvironment_value env Z m ρ bs v

theorem tupleCtx_substituteArgs {N : List (MetaArity S)} {Γ Δ : Ctx S}
    (env : ∀ (γ : S.Srt), Var Γ γ → M.Elem N Δ γ) (Z : D) (m : Z ⟶ M.family N)
    (ρ : M.Env Z Δ) :
    ∀ (bs : List S.Srt) (args : FamilyArgs (withMetas S N) (M.Elem N) (bs.map fun b => ([], b)) Γ),
      M.tupleCtx bs ((M.kripkeSubstitution N).substituteArgs env args) Z m ρ =
        M.tupleCtx bs args Z m (envValue env Z m ρ)
  | [], .nil => rfl
  | _ :: bs, .cons head tail => by
      show lift _ _ = lift _ _
      rw [tupleCtx_substituteArgs env Z m ρ bs tail]
      rfl

/-- The binding clone algebra of natural families at metavariable context `N`. -/
def kripke (N : List (MetaArity S)) : BindingCloneAlgebra.Algebra.{max u v} (withMetas S N) where
  substitution := M.kripkeSubstitution N
  operation := fun o args =>
    match o, args with
    | .inl o, args => M.opElem o args
    | .inr (.mk i), args => M.metaElem i args
  operation_substitute := by
    intro Γ Δ s env o args
    match o, args with
    | .inl o, args =>
        apply Elem.ext
        funext Z m ρ
        exact congrArg (· ≫ M.op o) (M.tupleArgs_substituteArgs env Z m ρ args).symm
    | .inr (.mk i), args =>
        apply Elem.ext
        funext Z m ρ
        exact congrArg (fun t => lift t (m ≫ M.familyProj N i) ≫ M.eval _ _)
          (M.tupleCtx_substituteArgs env Z m ρ _ args).symm

/-- The interpretation of a term with metavariables. -/
def interp (N : List (MetaArity S)) {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S N) Γ s) :
    M.Elem N Γ s :=
  BindingCloneFoldSubstitution.interpret (M.kripke N) t

theorem interp_var (N : List (MetaArity S)) {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    M.interp N (Term.var (S := withMetas S N) v) = ⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩ :=
  rfl

theorem interp_op (N : List (MetaArity S)) {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Args (withMetas S N) (S.arity o) Γ) :
    M.interp N (Term.op (S := withMetas S N) (Sum.inl o) args) =
      M.opElem o (BindingCloneFoldSubstitution.interpretArgs (M.kripke N) args) :=
  rfl

theorem interp_meta (N : List (MetaArity S)) {Γ : Ctx S} (i : Fin N.length)
    (args : Args (withMetas S N) ((N.get i).1.map fun b => ([], b)) Γ) :
    M.interp N (Term.op (S := withMetas S N) (Sum.inr (MetaOp.mk i)) args) =
      M.metaElem i (BindingCloneFoldSubstitution.interpretArgs (M.kripke N) args) :=
  rfl

/-- **The substitution lemma**, from the generic fold. -/
theorem interp_bind (N : List (MetaArity S)) {Γ Δ : Ctx S} {s : S.Srt}
    (σ : Sub (withMetas S N) Γ Δ) (t : Term (withMetas S N) Γ s) (Z : D) (m : Z ⟶ M.family N)
    (ρ : M.Env Z Δ) :
    (M.interp N (bind σ t)).value Z m ρ =
      (M.interp N t).value Z m (fun γ v => (M.interp N (σ γ v)).value Z m ρ) := by
  unfold interp
  rw [BindingCloneFoldSubstitution.interpret_bind]
  rfl

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
