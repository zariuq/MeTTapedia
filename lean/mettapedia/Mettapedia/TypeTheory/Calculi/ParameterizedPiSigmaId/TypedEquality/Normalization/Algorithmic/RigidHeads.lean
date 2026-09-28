import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness

/-!
# Rigid heads are discriminated

A rigid constant never computes. An elimination spine headed by one is
neutral, hence a weak-head normal form, and every rule of the algorithmic
equality that compares two such spines keeps both heads: the typed reductions
it starts from are identities, η applies both sides to the same fresh
variable, Σ-η projects both, and a spine is compared head first, where the
constant rule requires one name. So the algorithm never relates spines with
different rigid heads, and by completeness neither does the typed equality,
at any type and without any hypothesis on the types of the two terms.

The rigidity hypothesis is necessary: a constant with a defining computation
is equal to its unfolding, whose head is another constant.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- The constant heading an elimination spine of applications and
projections, if there is one. -/
def spineConst {n : Nat} : Tm Head n → Option DeclName
  | .const c => some c
  | .app f _ => spineConst f
  | .fst p => spineConst p
  | .snd p => spineConst p
  | _ => none

theorem spineConst_rename {n : Nat} (t : Tm Head n) :
    ∀ {m : Nat} (ρ : Ren n m), spineConst (rename ρ t) = spineConst t := by
  induction t with
  | var i => intro m ρ; rfl
  | const c => intro m ρ; rfl
  | head h => intro m ρ; rfl
  | pi A B _ _ => intro m ρ; rfl
  | sigma A B _ _ => intro m ρ; rfl
  | id A a b _ _ _ => intro m ρ; rfl
  | lam body _ => intro m ρ; rfl
  | app f a ihf _ => intro m ρ; simpa [rename, spineConst] using ihf ρ
  | pair a b _ _ => intro m ρ; rfl
  | fst p ih => intro m ρ; simpa [rename, spineConst] using ih ρ
  | snd p ih => intro m ρ; simpa [rename, spineConst] using ih ρ
  | refl a _ => intro m ρ; rfl

/-- A spine headed by a rigid constant is neutral. -/
theorem Neutral.of_spineConst {roles : Roles Head} {c : DeclName}
    (rigid : roles c = .rigid) {n : Nat} (t : Tm Head n)
    (head : spineConst t = some c) : Neutral roles t := by
  induction t with
  | const c' =>
      simp only [spineConst, Option.some.injEq] at head
      subst head
      exact Neutral.rigid (roles := roles) [] rigid
  | app f a ihf _ => exact .app (ihf head)
  | fst p ih => exact .fst (ih head)
  | snd p ih => exact .snd (ih head)
  | var i => simp [spineConst] at head
  | head h => simp [spineConst] at head
  | pi A B _ _ => simp [spineConst] at head
  | sigma A B _ _ => simp [spineConst] at head
  | id A a b _ _ _ => simp [spineConst] at head
  | lam body _ => simp [spineConst] at head
  | pair a b _ _ => simp [spineConst] at head
  | refl a _ => simp [spineConst] at head

/-- The constant heading an application spine is the one heading its function. -/
theorem spineConst_appSpine {n : Nat} :
    ∀ (args : List (Tm Head n)) (f : Tm Head n), spineConst (appSpine f args) = spineConst f
  | [], _ => rfl
  | a :: args, f => spineConst_appSpine args (.app f a)

/-- A neutral term is headed by no constructor. -/
theorem Neutral.spineConst_not_constructor {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) {c : DeclName} {arity : Nat} (head : spineConst t = some c) :
    roles c ≠ .constructor arity := by
  induction neutral with
  | var i => simp [spineConst] at head
  | app _ ih => exact ih head
  | fst _ ih => exact ih head
  | snd _ ih => exact ih head
  | rigid args rigid =>
      rw [spineConst_appSpine] at head
      simp only [spineConst, Option.some.injEq] at head
      subst head
      rw [rigid]
      exact nofun
  | stuck role _ _ _ _ _ =>
      rw [spineConst_appSpine] at head
      simp only [spineConst, Option.some.injEq] at head
      subst head
      rw [role]
      exact nofun

/-- The heads of two terms coincide whenever both are rigid constants. -/
def RigidHeadsAgree (roles : Roles Head) {n : Nat} (left right : Tm Head n) : Prop :=
  ∀ c d, spineConst left = some c → spineConst right = some d →
    roles c = .rigid → roles d = .rigid → c = d

/-- The same condition on the two terms a statement of the algorithmic
equality compares. -/
def AlgorithmicStatement.rigidHeadsAgree (roles : Roles Head) :
    AlgorithmicStatement Head → Prop
  | .types _ left right => RigidHeadsAgree roles left right
  | .typesW _ left right => RigidHeadsAgree roles left right
  | .terms _ left right _ => RigidHeadsAgree roles left right
  | .termsW _ left right _ => RigidHeadsAgree roles left right
  | .spines _ left right _ => RigidHeadsAgree roles left right
  | .spinesW _ left right _ => RigidHeadsAgree roles left right

variable {S : Setting Head L}

/-- The algorithmic equality relates two spines with rigid heads only when the
heads are the same constant. -/
theorem Algorithmic.rigidHeadsAgree {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : st.rigidHeadsAgree S.roles := by
  induction derivation with
  | types redA redB _ _ _ ih =>
      intro c d hc hd rc rd
      have eA := WhRed.eq_of_whnf (S := S)
        ((Neutral.of_spineConst rc _ hc).whnf S.shape) redA.red
      have eB := WhRed.eq_of_whnf (S := S)
        ((Neutral.of_spineConst rd _ hd).whnf S.shape) redB.red
      subst eA
      subst eB
      exact ih c d hc hd rc rd
  | heads _ _ _ _ => intro c d hc; simp [spineConst] at hc
  | pi _ _ _ _ _ => intro c d hc; simp [spineConst] at hc
  | sigma _ _ _ _ _ => intro c d hc; simp [spineConst] at hc
  | id _ _ _ _ _ _ => intro c d hc; simp [spineConst] at hc
  | inductiveType _ _ =>
      intro c d hc hd _ _
      simp only [spineConst, Option.some.injEq] at hc hd
      exact hc.symm.trans hd
  | neutralTypes _ _ _ _ ih => exact ih
  | terms _ _ redT redU _ ih =>
      intro c d hc hd rc rd
      have eT := WhRed.eq_of_whnf (S := S)
        ((Neutral.of_spineConst rc _ hc).whnf S.shape) redT.red
      have eU := WhRed.eq_of_whnf (S := S)
        ((Neutral.of_spineConst rd _ hd).whnf S.shape) redU.red
      subst eT
      subst eU
      exact ih c d hc hd rc rd
  | univ _ _ _ _ ih => exact ih
  | eta _ _ _ _ _ _ ih =>
      intro c d hc hd rc rd
      exact ih c d (by simpa [spineConst, spineConst_rename] using hc)
        (by simpa [spineConst, spineConst_rename] using hd) rc rd
  | sigmaEta _ _ _ _ _ _ ihFst _ =>
      intro c d hc hd rc rd
      exact ihFst c d (by simpa [spineConst] using hc) (by simpa [spineConst] using hd) rc rd
  | refl _ _ _ _ => intro c d hc; simp [spineConst] at hc
  | spine _ _ _ _ _ _ ih => exact ih
  | var i => intro c d hc; simp [spineConst] at hc
  | const _ _ =>
      intro c d hc hd _ _
      simp only [spineConst, Option.some.injEq] at hc hd
      exact hc.symm.trans hd
  | app _ _ ihf _ =>
      intro c d hc hd rc rd
      exact ihf c d (by simpa [spineConst] using hc) (by simpa [spineConst] using hd) rc rd
  | fst _ ih =>
      intro c d hc hd rc rd
      exact ih c d (by simpa [spineConst] using hc) (by simpa [spineConst] using hd) rc rd
  | snd _ ih =>
      intro c d hc hd rc rd
      exact ih c d (by simpa [spineConst] using hc) (by simpa [spineConst] using hd) rc rd
  | spinesW _ _ _ ih => exact ih

section Discrimination

variable (complete : AlgorithmicComplete S.R S.roles)
include complete

/-- Terms headed by different rigid constants are equal at no type. -/
theorem not_equal_of_rigid_heads {n : Nat} {Γ : Ctx Head n} {t u C : Tm Head n}
    {c d : DeclName} (formed : CtxFormed S.R Γ) (distinct : c ≠ d)
    (headT : spineConst t = some c) (headU : spineConst u = some d)
    (rigidC : S.roles c = .rigid) (rigidD : S.roles d = .rigid) :
    ¬ Equal S.R Γ t u C := fun equal =>
  distinct (Algorithmic.rigidHeadsAgree
    (complete formed equal)
    c d headT headU rigidC rigidD)

/-- Distinct rigid constants are equal at no type. -/
theorem not_equal_of_distinct_rigid {n : Nat} {Γ : Ctx Head n} {C : Tm Head n}
    {c d : DeclName} (formed : CtxFormed S.R Γ) (distinct : c ≠ d)
    (rigidC : S.roles c = .rigid) (rigidD : S.roles d = .rigid) :
    ¬ Equal S.R Γ (.const c) (.const d) C :=
  not_equal_of_rigid_heads complete formed distinct
    rfl rfl rigidC rigidD

end Discrimination

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
