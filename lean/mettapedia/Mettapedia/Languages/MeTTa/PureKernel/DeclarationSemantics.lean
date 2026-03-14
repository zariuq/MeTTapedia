import Mathlib.Logic.Relation
import Mettapedia.Languages.MeTTa.PureKernel.Typing
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv

namespace Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv

/-- Declaration-aware one-step reduction.
Includes the base Pure reduction plus fail-closed constant unfolding from `DeclEnv`. -/
inductive RedDecl (E : DeclEnv) : PureTm n → PureTm n → Prop where
  | core {t u : PureTm n} :
      Red t u → RedDecl E t u
  | deltaConst {c : DeclName} {v : PureTm 0} :
      valueOf? E c = some v →
      RedDecl E (.const c) (liftClosed v)
  | congPiDom {A A' : PureTm n} {B : PureTm (n + 1)} :
      RedDecl E A A' → RedDecl E (.pi A B) (.pi A' B)
  | congPiCod {A : PureTm n} {B B' : PureTm (n + 1)} :
      RedDecl E B B' → RedDecl E (.pi A B) (.pi A B')
  | congSigmaDom {A A' : PureTm n} {B : PureTm (n + 1)} :
      RedDecl E A A' → RedDecl E (.sigma A B) (.sigma A' B)
  | congSigmaCod {A : PureTm n} {B B' : PureTm (n + 1)} :
      RedDecl E B B' → RedDecl E (.sigma A B) (.sigma A B')
  | congIdTy {A A' a b : PureTm n} :
      RedDecl E A A' → RedDecl E (.id A a b) (.id A' a b)
  | congIdLeft {A a a' b : PureTm n} :
      RedDecl E a a' → RedDecl E (.id A a b) (.id A a' b)
  | congIdRight {A a b b' : PureTm n} :
      RedDecl E b b' → RedDecl E (.id A a b) (.id A a b')
  | congLam {b b' : PureTm (n + 1)} :
      RedDecl E b b' → RedDecl E (.lam b) (.lam b')
  | congAppFun {f f' a : PureTm n} :
      RedDecl E f f' → RedDecl E (.app f a) (.app f' a)
  | congAppArg {f a a' : PureTm n} :
      RedDecl E a a' → RedDecl E (.app f a) (.app f a')
  | congPairFst {a a' b : PureTm n} :
      RedDecl E a a' → RedDecl E (.pair a b) (.pair a' b)
  | congPairSnd {a b b' : PureTm n} :
      RedDecl E b b' → RedDecl E (.pair a b) (.pair a b')
  | congFst {p p' : PureTm n} :
      RedDecl E p p' → RedDecl E (.fst p) (.fst p')
  | congSnd {p p' : PureTm n} :
      RedDecl E p p' → RedDecl E (.snd p) (.snd p')
  | congRefl {a a' : PureTm n} :
      RedDecl E a a' → RedDecl E (.refl a) (.refl a')

abbrev RedStarDecl (E : DeclEnv) (t u : PureTm n) : Prop :=
  Relation.ReflTransGen (RedDecl E) t u

abbrev ConvDecl (E : DeclEnv) (t u : PureTm n) : Prop :=
  Relation.EqvGen (RedDecl E) t u

theorem redDecl_implies_conv {E : DeclEnv} {t u : PureTm n} (h : RedDecl E t u) :
    ConvDecl E t u :=
  Relation.EqvGen.rel _ _ h

theorem conv_core_to_decl {E : DeclEnv} {t u : PureTm n} (h : Conv t u) :
    ConvDecl E t u := by
  induction h with
  | rel x y hred =>
      exact .rel _ _ (.core hred)
  | refl x =>
      exact .refl x
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

theorem redDecl_monotone {Epre Efull : DeclEnv}
    (hExt : Extends Epre Efull)
    {t u : PureTm n}
    (h : RedDecl Epre t u) :
    RedDecl Efull t u := by
  induction h with
  | core hred =>
      exact .core hred
  | deltaConst hVal =>
      exact .deltaConst (Extends.valueOf hExt hVal)
  | congPiDom hred ih =>
      exact .congPiDom ih
  | congPiCod hred ih =>
      exact .congPiCod ih
  | congSigmaDom hred ih =>
      exact .congSigmaDom ih
  | congSigmaCod hred ih =>
      exact .congSigmaCod ih
  | congIdTy hred ih =>
      exact .congIdTy ih
  | congIdLeft hred ih =>
      exact .congIdLeft ih
  | congIdRight hred ih =>
      exact .congIdRight ih
  | congLam hred ih =>
      exact .congLam ih
  | congAppFun hred ih =>
      exact .congAppFun ih
  | congAppArg hred ih =>
      exact .congAppArg ih
  | congPairFst hred ih =>
      exact .congPairFst ih
  | congPairSnd hred ih =>
      exact .congPairSnd ih
  | congFst hred ih =>
      exact .congFst ih
  | congSnd hred ih =>
      exact .congSnd ih
  | congRefl hred ih =>
      exact .congRefl ih

theorem convDecl_monotone {Epre Efull : DeclEnv}
    (hExt : Extends Epre Efull)
    {t u : PureTm n}
    (h : ConvDecl Epre t u) :
    ConvDecl Efull t u := by
  induction h with
  | rel x y hred =>
      exact .rel _ _ (redDecl_monotone hExt hred)
  | refl x =>
      exact .refl x
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

theorem redDecl_rename {E : DeclEnv} {t u : PureTm n} (h : RedDecl E t u) :
    ∀ {m : Nat} (ρ : Ren n m), RedDecl E (rename ρ t) (rename ρ u) := by
  induction h with
  | core hred =>
      intro m ρ
      exact .core (red_rename hred ρ)
  | @deltaConst n c v hVal =>
      intro m ρ
      have hdelta : RedDecl E ((.const c : PureTm m)) (liftClosed (n := m) v) := .deltaConst hVal
      simpa [rename, rename_liftClosed] using hdelta
  | congPiDom hred ih =>
      intro m ρ
      exact .congPiDom (ih ρ)
  | congPiCod hred ih =>
      intro m ρ
      exact .congPiCod (ih (liftRen ρ))
  | congSigmaDom hred ih =>
      intro m ρ
      exact .congSigmaDom (ih ρ)
  | congSigmaCod hred ih =>
      intro m ρ
      exact .congSigmaCod (ih (liftRen ρ))
  | congIdTy hred ih =>
      intro m ρ
      exact .congIdTy (ih ρ)
  | congIdLeft hred ih =>
      intro m ρ
      exact .congIdLeft (ih ρ)
  | congIdRight hred ih =>
      intro m ρ
      exact .congIdRight (ih ρ)
  | congLam hred ih =>
      intro m ρ
      exact .congLam (ih (liftRen ρ))
  | congAppFun hred ih =>
      intro m ρ
      exact .congAppFun (ih ρ)
  | congAppArg hred ih =>
      intro m ρ
      exact .congAppArg (ih ρ)
  | congPairFst hred ih =>
      intro m ρ
      exact .congPairFst (ih ρ)
  | congPairSnd hred ih =>
      intro m ρ
      exact .congPairSnd (ih ρ)
  | congFst hred ih =>
      intro m ρ
      exact .congFst (ih ρ)
  | congSnd hred ih =>
      intro m ρ
      exact .congSnd (ih ρ)
  | congRefl hred ih =>
      intro m ρ
      exact .congRefl (ih ρ)

theorem convDecl_rename {E : DeclEnv} (ρ : Ren n m) {t u : PureTm n}
    (h : ConvDecl E t u) :
    ConvDecl E (rename ρ t) (rename ρ u) := by
  induction h with
  | rel x y hred =>
      exact .rel _ _ (redDecl_rename hred ρ)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem subst_vars_eq_rename (ρ : Ren n m) (t : PureTm n) :
    subst (fun i => (.var (ρ i) : PureTm m)) t = rename ρ t := by
  calc
    subst (fun i => (.var (ρ i) : PureTm m)) t
        = subst (ids (n := m)) (rename ρ t) := by
            symm
            simpa using (subst_rename (σ := ids (n := m)) (ρ := ρ) (t := t))
    _ = rename ρ t := by
          exact subst_ids (t := rename ρ t)

@[simp] theorem subst_liftClosed {n m : Nat} (σ : Sub n m) (t : PureTm 0) :
    subst σ (liftClosed (n := n) t) = liftClosed (n := m) t := by
  let ρ0 : Ren 0 m := fun i => nomatch i
  unfold liftClosed
  calc
    subst σ (rename (fun i : Fin 0 => nomatch i) t)
        = subst (fun i : Fin 0 => σ ((fun j : Fin 0 => nomatch j) i)) t := by
            simpa using (subst_rename (σ := σ) (ρ := (fun i : Fin 0 => nomatch i)) (t := t))
    _ = subst (fun i : Fin 0 => nomatch i) t := by
          apply subst_ext
          intro i
          nomatch i
    _ = subst (fun i : Fin 0 => (.var (ρ0 i) : PureTm m)) t := by
          apply subst_ext
          intro i
          nomatch i
    _ = rename ρ0 t := subst_vars_eq_rename ρ0 t

theorem redDecl_subst {E : DeclEnv} {t u : PureTm n} (h : RedDecl E t u) :
    ∀ {m : Nat} (σ : Sub n m), RedDecl E (subst σ t) (subst σ u) := by
  induction h with
  | core hred =>
      intro m σ
      exact .core (red_subst hred σ)
  | @deltaConst n c v hVal =>
      intro m σ
      have hdelta : RedDecl E ((.const c : PureTm m)) (liftClosed (n := m) v) := .deltaConst hVal
      simpa [subst, subst_liftClosed] using hdelta
  | congPiDom hred ih =>
      intro m σ
      exact .congPiDom (ih σ)
  | congPiCod hred ih =>
      intro m σ
      exact .congPiCod (ih (liftSub σ))
  | congSigmaDom hred ih =>
      intro m σ
      exact .congSigmaDom (ih σ)
  | congSigmaCod hred ih =>
      intro m σ
      exact .congSigmaCod (ih (liftSub σ))
  | congIdTy hred ih =>
      intro m σ
      exact .congIdTy (ih σ)
  | congIdLeft hred ih =>
      intro m σ
      exact .congIdLeft (ih σ)
  | congIdRight hred ih =>
      intro m σ
      exact .congIdRight (ih σ)
  | congLam hred ih =>
      intro m σ
      exact .congLam (ih (liftSub σ))
  | congAppFun hred ih =>
      intro m σ
      exact .congAppFun (ih σ)
  | congAppArg hred ih =>
      intro m σ
      exact .congAppArg (ih σ)
  | congPairFst hred ih =>
      intro m σ
      exact .congPairFst (ih σ)
  | congPairSnd hred ih =>
      intro m σ
      exact .congPairSnd (ih σ)
  | congFst hred ih =>
      intro m σ
      exact .congFst (ih σ)
  | congSnd hred ih =>
      intro m σ
      exact .congSnd (ih σ)
  | congRefl hred ih =>
      intro m σ
      exact .congRefl (ih σ)

theorem convDecl_subst {E : DeclEnv} (σ : Sub n m) {t u : PureTm n}
    (h : ConvDecl E t u) :
    ConvDecl E (subst σ t) (subst σ u) := by
  induction h with
  | rel x y hred =>
      exact .rel _ _ (redDecl_subst hred σ)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congPiDom {E : DeclEnv} {A A' : PureTm n} {B : PureTm (n + 1)}
    (h : ConvDecl E A A') :
    ConvDecl E (.pi A B) (.pi A' B) := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congPiDom hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congPiCod {E : DeclEnv} {A : PureTm n} {B B' : PureTm (n + 1)}
    (h : ConvDecl E B B') :
    ConvDecl E (.pi A B) (.pi A B') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congPiCod hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congSigmaDom {E : DeclEnv} {A A' : PureTm n} {B : PureTm (n + 1)}
    (h : ConvDecl E A A') :
    ConvDecl E (.sigma A B) (.sigma A' B) := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congSigmaDom hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congSigmaCod {E : DeclEnv} {A : PureTm n} {B B' : PureTm (n + 1)}
    (h : ConvDecl E B B') :
    ConvDecl E (.sigma A B) (.sigma A B') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congSigmaCod hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congIdTy {E : DeclEnv} {A A' a b : PureTm n}
    (h : ConvDecl E A A') :
    ConvDecl E (.id A a b) (.id A' a b) := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congIdTy hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congIdLeft {E : DeclEnv} {A a a' b : PureTm n}
    (h : ConvDecl E a a') :
    ConvDecl E (.id A a b) (.id A a' b) := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congIdLeft hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congIdRight {E : DeclEnv} {A a b b' : PureTm n}
    (h : ConvDecl E b b') :
    ConvDecl E (.id A a b) (.id A a b') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congIdRight hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congLam {E : DeclEnv} {b b' : PureTm (n + 1)}
    (h : ConvDecl E b b') :
    ConvDecl E (.lam b) (.lam b') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congLam hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congAppFun {E : DeclEnv} {f f' a : PureTm n}
    (h : ConvDecl E f f') :
    ConvDecl E (.app f a) (.app f' a) := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congAppFun hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congAppArg {E : DeclEnv} {f a a' : PureTm n}
    (h : ConvDecl E a a') :
    ConvDecl E (.app f a) (.app f a') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congAppArg hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congPairFst {E : DeclEnv} {a a' b : PureTm n}
    (h : ConvDecl E a a') :
    ConvDecl E (.pair a b) (.pair a' b) := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congPairFst hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congPairSnd {E : DeclEnv} {a b b' : PureTm n}
    (h : ConvDecl E b b') :
    ConvDecl E (.pair a b) (.pair a b') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congPairSnd hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congFst {E : DeclEnv} {p p' : PureTm n}
    (h : ConvDecl E p p') :
    ConvDecl E (.fst p) (.fst p') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congFst hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congSnd {E : DeclEnv} {p p' : PureTm n}
    (h : ConvDecl E p p') :
    ConvDecl E (.snd p) (.snd p') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congSnd hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_congRefl {E : DeclEnv} {a a' : PureTm n}
    (h : ConvDecl E a a') :
    ConvDecl E (.refl a) (.refl a') := by
  induction h with
  | rel _ _ hred =>
      exact .rel _ _ (.congRefl hred)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

private theorem convDecl_liftSub_congr {E : DeclEnv} {σ τ : Sub n m}
    (hστ : ∀ i : Fin n, ConvDecl E (σ i) (τ i)) :
    ∀ i : Fin (n + 1), ConvDecl E (liftSub σ i) (liftSub τ i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact .refl _
  · intro j
    simpa [liftSub] using (convDecl_rename (E := E) (ρ := wk) (hστ j))

/-- Conversion congruence under pointwise-convertible substitutions. -/
theorem convDecl_subst_congr {E : DeclEnv} {σ τ : Sub n m}
    (hστ : ∀ i : Fin n, ConvDecl E (σ i) (τ i)) :
    ∀ t : PureTm n, ConvDecl E (subst σ t) (subst τ t) := by
  intro t
  induction t generalizing m with
  | var i =>
      simpa [subst] using hστ i
  | const c =>
      exact .refl _
  | u0 =>
      exact .refl _
  | u1 =>
      exact .refl _
  | pi A B ihA ihB =>
      have hA : ConvDecl E (subst σ A) (subst τ A) := ihA hστ
      have hB : ConvDecl E (subst (liftSub σ) B) (subst (liftSub τ) B) :=
        ihB (convDecl_liftSub_congr (E := E) hστ)
      exact Relation.EqvGen.trans _ _ _ (convDecl_congPiDom hA) (convDecl_congPiCod hB)
  | sigma A B ihA ihB =>
      have hA : ConvDecl E (subst σ A) (subst τ A) := ihA hστ
      have hB : ConvDecl E (subst (liftSub σ) B) (subst (liftSub τ) B) :=
        ihB (convDecl_liftSub_congr (E := E) hστ)
      exact Relation.EqvGen.trans _ _ _ (convDecl_congSigmaDom hA) (convDecl_congSigmaCod hB)
  | id A a b ihA iha ihb =>
      have hA : ConvDecl E (subst σ A) (subst τ A) := ihA hστ
      have ha : ConvDecl E (subst σ a) (subst τ a) := iha hστ
      have hb : ConvDecl E (subst σ b) (subst τ b) := ihb hστ
      exact Relation.EqvGen.trans _ _ _ (convDecl_congIdTy hA)
        (Relation.EqvGen.trans _ _ _ (convDecl_congIdLeft ha) (convDecl_congIdRight hb))
  | lam b ih =>
      have hb : ConvDecl E (subst (liftSub σ) b) (subst (liftSub τ) b) :=
        ih (convDecl_liftSub_congr (E := E) hστ)
      exact convDecl_congLam hb
  | app f a ihf iha =>
      have hf : ConvDecl E (subst σ f) (subst τ f) := ihf hστ
      have ha : ConvDecl E (subst σ a) (subst τ a) := iha hστ
      exact Relation.EqvGen.trans _ _ _ (convDecl_congAppFun hf) (convDecl_congAppArg ha)
  | pair a b iha ihb =>
      have ha : ConvDecl E (subst σ a) (subst τ a) := iha hστ
      have hb : ConvDecl E (subst σ b) (subst τ b) := ihb hστ
      exact Relation.EqvGen.trans _ _ _ (convDecl_congPairFst ha) (convDecl_congPairSnd hb)
  | fst p ih =>
      exact convDecl_congFst (ih hστ)
  | snd p ih =>
      exact convDecl_congSnd (ih hστ)
  | refl a iha =>
      exact convDecl_congRefl (iha hστ)

/-- Argument convertibility implies convertibility after single-variable instantiation. -/
theorem inst0_arg_conv_decl {E : DeclEnv} {a a' : PureTm n} {B : PureTm (n + 1)}
    (h : ConvDecl E a a') :
    ConvDecl E (inst0 a B) (inst0 a' B) := by
  have hσσ : ∀ i : Fin (n + 1), ConvDecl E (subst0 a i) (subst0 a' i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [subst0]
        using h
    · intro j
      exact .refl _
  simpa [inst0] using
    (convDecl_subst_congr (E := E) (σ := subst0 a) (τ := subst0 a') hσσ B)

/-- Declaration-aware typing judgment.
This extends the kernel typing rules with global constants looked up from `DeclEnv`. -/
inductive HasTypeDecl (E : DeclEnv) : Ctx n → PureTm n → PureTm n → Prop where
  | u0_type (Γ : Ctx n) :
      HasTypeDecl E Γ .u0 .u1
  | var {Γ : Ctx n} (i : Fin n) :
      HasTypeDecl E Γ (.var i) (lookup Γ i)
  | const {Γ : Ctx n} {c : DeclName} {A0 : PureTm 0} :
      typeOf? E c = some A0 →
      HasTypeDecl E Γ (.const c) (liftClosed A0)
  | pi_form {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)} :
      HasTypeDecl E Γ A .u1 →
      HasTypeDecl E (.snoc Γ A) B .u1 →
      HasTypeDecl E Γ (.pi A B) .u1
  | sigma_form {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)} :
      HasTypeDecl E Γ A .u1 →
      HasTypeDecl E (.snoc Γ A) B .u1 →
      HasTypeDecl E Γ (.sigma A B) .u1
  | lam_intro {Γ : Ctx n} {A : PureTm n} {body B : PureTm (n + 1)} :
      HasTypeDecl E (.snoc Γ A) body B →
      HasTypeDecl E Γ (.lam body) (.pi A B)
  | app_elim {Γ : Ctx n} {f a A : PureTm n} {B : PureTm (n + 1)} :
      HasTypeDecl E Γ f (.pi A B) →
      HasTypeDecl E Γ a A →
      HasTypeDecl E Γ (.app f a) (inst0 a B)
  | pair_intro {Γ : Ctx n} {a b A : PureTm n} {B : PureTm (n + 1)} :
      HasTypeDecl E Γ a A →
      HasTypeDecl E Γ b (inst0 a B) →
      HasTypeDecl E Γ (.pair a b) (.sigma A B)
  | fst_elim {Γ : Ctx n} {p A : PureTm n} {B : PureTm (n + 1)} :
      HasTypeDecl E Γ p (.sigma A B) →
      HasTypeDecl E Γ (.fst p) A
  | snd_elim {Γ : Ctx n} {p A : PureTm n} {B : PureTm (n + 1)} :
      HasTypeDecl E Γ p (.sigma A B) →
      HasTypeDecl E Γ (.snd p) (inst0 (.fst p) B)
  | id_form {Γ : Ctx n} {A a b : PureTm n} :
      HasTypeDecl E Γ A .u1 →
      HasTypeDecl E Γ a A →
      HasTypeDecl E Γ b A →
      HasTypeDecl E Γ (.id A a b) .u1
  | refl_intro {Γ : Ctx n} {a A : PureTm n} :
      HasTypeDecl E Γ a A →
      HasTypeDecl E Γ (.refl a) (.id A a a)
  | conv {Γ : Ctx n} {t A B : PureTm n} :
      HasTypeDecl E Γ t A →
      ConvDecl E A B →
      HasTypeDecl E Γ t B

theorem hasTypeDecl_monotone {Epre Efull : DeclEnv}
    (hExt : Extends Epre Efull)
    {Γ : Ctx n} {t A : PureTm n}
    (ht : HasTypeDecl Epre Γ t A) :
    HasTypeDecl Efull Γ t A := by
  induction ht with
  | u0_type Γ =>
      exact .u0_type Γ
  | var i =>
      exact .var i
  | @const n Γ c A0 hLookup =>
      exact .const (Extends.typeOf hExt hLookup)
  | pi_form hA hB ihA ihB =>
      exact .pi_form ihA ihB
  | sigma_form hA hB ihA ihB =>
      exact .sigma_form ihA ihB
  | lam_intro hBody ihBody =>
      exact .lam_intro ihBody
  | app_elim hf ha ihf iha =>
      exact .app_elim ihf iha
  | pair_intro ha hb iha ihb =>
      exact .pair_intro iha ihb
  | fst_elim hp ihp =>
      exact .fst_elim ihp
  | snd_elim hp ihp =>
      exact .snd_elim ihp
  | id_form hA ha hb ihA iha ihb =>
      exact .id_form ihA iha ihb
  | refl_intro ha iha =>
      exact .refl_intro iha
  | conv ht hAB iht =>
      exact .conv iht (convDecl_monotone hExt hAB)

theorem hasType_core_to_decl {E : DeclEnv} {Γ : Ctx n} {t A : PureTm n}
    (h : HasType Γ t A) : HasTypeDecl E Γ t A := by
  induction h with
  | u0_type Γ =>
      exact .u0_type Γ
  | var i =>
      exact .var i
  | pi_form hA hB ihA ihB =>
      exact .pi_form ihA ihB
  | sigma_form hA hB ihA ihB =>
      exact .sigma_form ihA ihB
  | lam_intro hBody ihBody =>
      exact .lam_intro ihBody
  | app_elim hf ha ihf iha =>
      exact .app_elim ihf iha
  | pair_intro ha hb iha ihb =>
      exact .pair_intro iha ihb
  | fst_elim hp ihp =>
      exact .fst_elim ihp
  | snd_elim hp ihp =>
      exact .snd_elim ihp
  | id_form hA ha hb ihA iha ihb =>
      exact .id_form ihA iha ihb
  | refl_intro ha iha =>
      exact .refl_intro iha
  | conv ht hAB iht =>
      exact .conv iht (conv_core_to_decl hAB)

/-- Typed context morphism for declaration-aware simultaneous substitution. -/
def CtxMorDecl (E : DeclEnv) (Γ : Ctx n) (Δ : Ctx m) (σ : Sub n m) : Prop :=
  ∀ i : Fin n, HasTypeDecl E Δ (σ i) (subst σ (lookup Γ i))

theorem typing_rename_decl {E : DeclEnv} {Γ : Ctx n} {t A : PureTm n}
    (ht : HasTypeDecl E Γ t A) :
    ∀ {m : Nat} {Δ : Ctx m} {ρ : Ren n m},
      CtxRen Γ Δ ρ →
      HasTypeDecl E Δ (rename ρ t) (rename ρ A) := by
  induction ht with
  | u0_type Γ =>
      intro m Δ ρ hρ
      simpa [rename] using (HasTypeDecl.u0_type (E := E) (Γ := Δ))
  | var i =>
      intro m Δ ρ hρ
      simpa [hρ i] using (HasTypeDecl.var (E := E) (Γ := Δ) (i := ρ i))
  | @const n Γ c A0 hLookup =>
      intro m Δ ρ hρ
      simpa [rename, rename_liftClosed] using
        (HasTypeDecl.const (E := E) (Γ := Δ) (c := c) (A0 := A0) hLookup)
  | @pi_form n Γ A B hA hB ihA ihB =>
      intro m Δ ρ hρ
      have hA' := ihA (m := m) (Δ := Δ) (ρ := ρ) hρ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (rename ρ A)) (ρ := liftRen ρ)
        (CtxRen.snoc hρ A)
      simpa [rename] using (HasTypeDecl.pi_form hA' hB')
  | @sigma_form n Γ A B hA hB ihA ihB =>
      intro m Δ ρ hρ
      have hA' := ihA (m := m) (Δ := Δ) (ρ := ρ) hρ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (rename ρ A)) (ρ := liftRen ρ)
        (CtxRen.snoc hρ A)
      simpa [rename] using (HasTypeDecl.sigma_form hA' hB')
  | @lam_intro n Γ A body B hBody ihBody =>
      intro m Δ ρ hρ
      have hBody' := ihBody (m := m + 1) (Δ := .snoc Δ (rename ρ A)) (ρ := liftRen ρ)
        (CtxRen.snoc hρ A)
      simpa [rename] using (HasTypeDecl.lam_intro hBody')
  | @app_elim n Γ f a A B hf ha ihf iha =>
      intro m Δ ρ hρ
      simpa [rename, rename_inst0] using
        (HasTypeDecl.app_elim
          (ihf (m := m) (Δ := Δ) (ρ := ρ) hρ)
          (iha (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      intro m Δ ρ hρ
      have ha' := iha (m := m) (Δ := Δ) (ρ := ρ) hρ
      have hb' :
          HasTypeDecl E Δ (rename ρ b) (inst0 (rename ρ a) (rename (liftRen ρ) B)) := by
        simpa [rename_inst0] using (ihb (m := m) (Δ := Δ) (ρ := ρ) hρ)
      simpa [rename] using (HasTypeDecl.pair_intro ha' hb')
  | @fst_elim n Γ p A B hp ihp =>
      intro m Δ ρ hρ
      simpa [rename] using
        (HasTypeDecl.fst_elim (ihp (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @snd_elim n Γ p A B hp ihp =>
      intro m Δ ρ hρ
      simpa [rename, rename_inst0] using
        (HasTypeDecl.snd_elim (ihp (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      intro m Δ ρ hρ
      simpa [rename] using
        (HasTypeDecl.id_form
          (ihA (m := m) (Δ := Δ) (ρ := ρ) hρ)
          (iha (m := m) (Δ := Δ) (ρ := ρ) hρ)
          (ihb (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @refl_intro n Γ a A ha iha =>
      intro m Δ ρ hρ
      simpa [rename] using
        (HasTypeDecl.refl_intro (iha (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @conv n Γ t A B ht hAB iht =>
      intro m Δ ρ hρ
      exact HasTypeDecl.conv
        (iht (m := m) (Δ := Δ) (ρ := ρ) hρ)
        (convDecl_rename ρ hAB)

theorem weakening_decl {E : DeclEnv} {Γ : Ctx n} {t A U : PureTm n}
    (ht : HasTypeDecl E Γ t A) :
    HasTypeDecl E (.snoc Γ U) (rename wk t) (rename wk A) := by
  have hwk : CtxRen Γ (.snoc Γ U) wk := by
    intro i
    simp [wk]
  simpa using
    (typing_rename_decl ht (m := n + 1) (Δ := .snoc Γ U) (ρ := wk) hwk)

theorem CtxMorDecl.lift {E : DeclEnv} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m}
    (hσ : CtxMorDecl E Γ Δ σ) (A : PureTm n) :
    CtxMorDecl E (.snoc Γ A) (.snoc Δ (subst σ A)) (liftSub σ) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [CtxMorDecl, lookup_snoc_zero, liftSub, subst_liftSub_wk] using
      (HasTypeDecl.var (E := E) (Γ := .snoc Δ (subst σ A)) (i := (0 : Fin (m + 1))))
  · intro j
    have hwk : CtxRen Δ (.snoc Δ (subst σ A)) wk := by
      intro i
      simp [wk]
    have hj : HasTypeDecl E (.snoc Δ (subst σ A))
        (rename wk (σ j))
        (rename wk (subst σ (lookup Γ j))) := by
      exact typing_rename_decl (ht := hσ j) (m := m + 1) (Δ := .snoc Δ (subst σ A))
        (ρ := wk) hwk
    simpa [CtxMorDecl, lookup_snoc_succ, liftSub, subst_liftSub_wk] using hj

/-- Generic declaration-aware simultaneous typing substitution along a typed context morphism. -/
theorem typing_subst_decl {E : DeclEnv} {Γ : Ctx n} {t A : PureTm n} (ht : HasTypeDecl E Γ t A) :
    ∀ {m : Nat} {Δ : Ctx m} {σ : Sub n m},
      CtxMorDecl E Γ Δ σ → HasTypeDecl E Δ (subst σ t) (subst σ A) := by
  induction ht with
  | u0_type Γ =>
      intro m Δ σ hσ
      simpa [subst] using (HasTypeDecl.u0_type (E := E) (Γ := Δ))
  | var i =>
      intro m Δ σ hσ
      simpa [CtxMorDecl] using hσ i
  | @const n Γ c A0 hLookup =>
      intro m Δ σ hσ
      simpa [subst, subst_liftClosed] using
        (HasTypeDecl.const (E := E) (Γ := Δ) (c := c) (A0 := A0) hLookup)
  | @pi_form n Γ A B hA hB ihA ihB =>
      intro m Δ σ hσ
      have hA' := ihA (m := m) (Δ := Δ) (σ := σ) hσ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (subst σ A)) (σ := liftSub σ)
        (CtxMorDecl.lift hσ A)
      simpa [subst] using (HasTypeDecl.pi_form hA' hB')
  | @sigma_form n Γ A B hA hB ihA ihB =>
      intro m Δ σ hσ
      have hA' := ihA (m := m) (Δ := Δ) (σ := σ) hσ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (subst σ A)) (σ := liftSub σ)
        (CtxMorDecl.lift hσ A)
      simpa [subst] using (HasTypeDecl.sigma_form hA' hB')
  | @lam_intro n Γ A body B hBody ihBody =>
      intro m Δ σ hσ
      have hBody' := ihBody (m := m + 1) (Δ := .snoc Δ (subst σ A)) (σ := liftSub σ)
        (CtxMorDecl.lift hσ A)
      simpa [subst] using (HasTypeDecl.lam_intro hBody')
  | @app_elim n Γ f a A B hf ha ihf iha =>
      intro m Δ σ hσ
      simpa [subst, subst_inst0] using
        (HasTypeDecl.app_elim
          (ihf (m := m) (Δ := Δ) (σ := σ) hσ)
          (iha (m := m) (Δ := Δ) (σ := σ) hσ))
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      intro m Δ σ hσ
      have ha' := iha (m := m) (Δ := Δ) (σ := σ) hσ
      have hb' :
          HasTypeDecl E Δ (subst σ b) (inst0 (subst σ a) (subst (liftSub σ) B)) := by
        simpa [subst_inst0] using (ihb (m := m) (Δ := Δ) (σ := σ) hσ)
      simpa [subst] using (HasTypeDecl.pair_intro ha' hb')
  | @fst_elim n Γ p A B hp ihp =>
      intro m Δ σ hσ
      simpa [subst] using
        (HasTypeDecl.fst_elim (ihp (m := m) (Δ := Δ) (σ := σ) hσ))
  | @snd_elim n Γ p A B hp ihp =>
      intro m Δ σ hσ
      simpa [subst, subst_inst0] using
        (HasTypeDecl.snd_elim (ihp (m := m) (Δ := Δ) (σ := σ) hσ))
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      intro m Δ σ hσ
      simpa [subst] using
        (HasTypeDecl.id_form
          (ihA (m := m) (Δ := Δ) (σ := σ) hσ)
          (iha (m := m) (Δ := Δ) (σ := σ) hσ)
          (ihb (m := m) (Δ := Δ) (σ := σ) hσ))
  | @refl_intro n Γ a A ha iha =>
      intro m Δ σ hσ
      simpa [subst] using
        (HasTypeDecl.refl_intro (iha (m := m) (Δ := Δ) (σ := σ) hσ))
  | @conv n Γ t A B ht hAB iht =>
      intro m Δ σ hσ
      exact HasTypeDecl.conv
        (iht (m := m) (Δ := Δ) (σ := σ) hσ)
        (convDecl_subst σ hAB)

/-- Transport declaration-aware typing along pointwise context conversion. -/
theorem context_conv_decl {E : DeclEnv} {Γ Δ : Ctx n} {t T : PureTm n}
    (hctx : ∀ i : Fin n, ConvDecl E (lookup Γ i) (lookup Δ i))
    (ht : HasTypeDecl E Γ t T) :
    HasTypeDecl E Δ t T := by
  induction ht with
  | u0_type Γ =>
      exact .u0_type _
  | var i =>
      exact .conv
        (HasTypeDecl.var (E := E) (Γ := Δ) (i := i))
        (Relation.EqvGen.symm _ _ (hctx i))
  | @const n Γ c A0 hLookup =>
      exact .const hLookup
  | @pi_form n Γ A B hA hB ihA ihB =>
      have hA' : HasTypeDecl E Δ A .u1 := ihA hctx
      have hctx' : ∀ i : Fin (n + 1), ConvDecl E (lookup (.snoc Γ A) i) (lookup (.snoc Δ A) i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .refl _
        · intro j
          simpa [lookup_snoc_succ] using (convDecl_rename wk (hctx j))
      have hB' : HasTypeDecl E (.snoc Δ A) B .u1 := ihB hctx'
      exact .pi_form hA' hB'
  | @sigma_form n Γ A B hA hB ihA ihB =>
      have hA' : HasTypeDecl E Δ A .u1 := ihA hctx
      have hctx' : ∀ i : Fin (n + 1), ConvDecl E (lookup (.snoc Γ A) i) (lookup (.snoc Δ A) i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .refl _
        · intro j
          simpa [lookup_snoc_succ] using (convDecl_rename wk (hctx j))
      have hB' : HasTypeDecl E (.snoc Δ A) B .u1 := ihB hctx'
      exact .sigma_form hA' hB'
  | @lam_intro n Γ A body B hBody ihBody =>
      have hctx' : ∀ i : Fin (n + 1), ConvDecl E (lookup (.snoc Γ A) i) (lookup (.snoc Δ A) i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .refl _
        · intro j
          simpa [lookup_snoc_succ] using (convDecl_rename wk (hctx j))
      exact .lam_intro (ihBody hctx')
  | @app_elim n Γ f a A B hf ha ihf iha =>
      exact .app_elim (ihf hctx) (iha hctx)
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      exact .pair_intro (iha hctx) (ihb hctx)
  | @fst_elim n Γ p A B hp ihp =>
      exact .fst_elim (ihp hctx)
  | @snd_elim n Γ p A B hp ihp =>
      exact .snd_elim (ihp hctx)
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      exact .id_form (ihA hctx) (iha hctx) (ihb hctx)
  | @refl_intro n Γ a A ha iha =>
      exact .refl_intro (iha hctx)
  | @conv n Γ t A B ht hAB iht =>
      exact .conv (iht hctx) hAB

/-- Specialization of `context_conv_decl` to changing only the head binder type. -/
theorem context_conv_head_decl {E : DeclEnv} {Γ : Ctx n} {A A' : PureTm n} {t T : PureTm (n + 1)}
    (hAA' : ConvDecl E A A') (ht : HasTypeDecl E (.snoc Γ A) t T) :
    HasTypeDecl E (.snoc Γ A') t T := by
  have hctx : ∀ i : Fin (n + 1),
      ConvDecl E (lookup (.snoc Γ A) i) (lookup (.snoc Γ A') i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [lookup_snoc_zero] using (convDecl_rename (ρ := wk) hAA')
    · intro j
      simpa [lookup_snoc_succ] using (Relation.EqvGen.refl (lookup (.snoc Γ A) j.succ))
  exact context_conv_decl hctx ht

private theorem app_generation_decl_aux {E : DeclEnv} {Γ : Ctx n} {t C : PureTm n}
    (ht : HasTypeDecl E Γ t C) :
    ∀ {f a : PureTm n}, t = .app f a →
      ∃ A B, HasTypeDecl E Γ f (.pi A B) ∧ HasTypeDecl E Γ a A ∧ ConvDecl E (inst0 a B) C := by
  induction ht with
  | app_elim hf ha =>
      intro f a hEq
      cases hEq
      exact ⟨_, _, hf, ha, .refl _⟩
  | conv ht hconv ih =>
      intro f a hEq
      rcases ih hEq with ⟨A, B, hf, ha, hC⟩
      exact ⟨A, B, hf, ha, .trans _ _ _ hC hconv⟩
  | u0_type =>
      intro f a hEq
      cases hEq
  | var =>
      intro f a hEq
      cases hEq
  | const =>
      intro f a hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro f a hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro f a hEq
      cases hEq
  | lam_intro hBody ihBody =>
      intro f a hEq
      cases hEq
  | pair_intro ha hb iha ihb =>
      intro f a hEq
      cases hEq
  | fst_elim hp ihp =>
      intro f a hEq
      cases hEq
  | snd_elim hp ihp =>
      intro f a hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro f a hEq
      cases hEq
  | refl_intro ha iha =>
      intro f a hEq
      cases hEq

theorem app_generation_decl {E : DeclEnv} {Γ : Ctx n} {f a C : PureTm n}
    (ht : HasTypeDecl E Γ (.app f a) C) :
    ∃ A B, HasTypeDecl E Γ f (.pi A B) ∧ HasTypeDecl E Γ a A ∧ ConvDecl E (inst0 a B) C :=
  app_generation_decl_aux ht rfl

private theorem lam_generation_decl_aux {E : DeclEnv} {Γ : Ctx n} {t C : PureTm n}
    (ht : HasTypeDecl E Γ t C) :
    ∀ {body : PureTm (n + 1)}, t = .lam body →
      ∃ A B, HasTypeDecl E (.snoc Γ A) body B ∧ ConvDecl E (.pi A B) C := by
  induction ht with
  | lam_intro hBody =>
      intro body hEq
      cases hEq
      exact ⟨_, _, hBody, .refl _⟩
  | conv ht hconv ih =>
      intro body hEq
      rcases ih hEq with ⟨A, B, hBody, hPi⟩
      exact ⟨A, B, hBody, .trans _ _ _ hPi hconv⟩
  | u0_type =>
      intro body hEq
      cases hEq
  | var =>
      intro body hEq
      cases hEq
  | const =>
      intro body hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro body hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro body hEq
      cases hEq
  | app_elim hf ha ihf iha =>
      intro body hEq
      cases hEq
  | pair_intro ha hb iha ihb =>
      intro body hEq
      cases hEq
  | fst_elim hp ihp =>
      intro body hEq
      cases hEq
  | snd_elim hp ihp =>
      intro body hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro body hEq
      cases hEq
  | refl_intro ha iha =>
      intro body hEq
      cases hEq

theorem lam_generation_decl {E : DeclEnv} {Γ : Ctx n} {body : PureTm (n + 1)} {C : PureTm n}
    (ht : HasTypeDecl E Γ (.lam body) C) :
    ∃ A B, HasTypeDecl E (.snoc Γ A) body B ∧ ConvDecl E (.pi A B) C :=
  lam_generation_decl_aux ht rfl

private theorem pair_generation_decl_aux {E : DeclEnv} {Γ : Ctx n} {t C : PureTm n}
    (ht : HasTypeDecl E Γ t C) :
    ∀ {a b : PureTm n}, t = .pair a b →
      ∃ A B, HasTypeDecl E Γ a A ∧ HasTypeDecl E Γ b (inst0 a B) ∧ ConvDecl E (.sigma A B) C := by
  induction ht with
  | pair_intro ha hb =>
      intro a b hEq
      cases hEq
      exact ⟨_, _, ha, hb, .refl _⟩
  | conv ht hconv ih =>
      intro a b hEq
      rcases ih hEq with ⟨A, B, ha, hb, hSigma⟩
      exact ⟨A, B, ha, hb, .trans _ _ _ hSigma hconv⟩
  | u0_type =>
      intro a b hEq
      cases hEq
  | var =>
      intro a b hEq
      cases hEq
  | const =>
      intro a b hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro a b hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro a b hEq
      cases hEq
  | lam_intro hBody ihBody =>
      intro a b hEq
      cases hEq
  | app_elim hf ha ihf iha =>
      intro a b hEq
      cases hEq
  | fst_elim hp ihp =>
      intro a b hEq
      cases hEq
  | snd_elim hp ihp =>
      intro a b hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro a b hEq
      cases hEq
  | refl_intro ha iha =>
      intro a b hEq
      cases hEq

theorem pair_generation_decl {E : DeclEnv} {Γ : Ctx n} {a b C : PureTm n}
    (ht : HasTypeDecl E Γ (.pair a b) C) :
    ∃ A B, HasTypeDecl E Γ a A ∧ HasTypeDecl E Γ b (inst0 a B) ∧ ConvDecl E (.sigma A B) C :=
  pair_generation_decl_aux ht rfl

private theorem subst0_wk_cancel_decl (a t : PureTm n) :
    subst (subst0 a) (rename wk t) = t := by
  calc
    subst (subst0 a) (rename wk t)
        = subst (fun i => subst0 a (wk i)) t := by
            simpa using (subst_rename (σ := subst0 a) (ρ := wk) (t := t))
    _ = subst ids t := by
          apply subst_ext
          intro i
          rfl
    _ = t := by
          exact subst_ids (t := t)

private theorem ctxMorDecl_subst0 {E : DeclEnv} {Γ : Ctx n} {A a : PureTm n}
    (ha : HasTypeDecl E Γ a A) :
    CtxMorDecl E (.snoc Γ A) Γ (subst0 a) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [CtxMorDecl, lookup_snoc_zero, subst0_wk_cancel_decl] using ha
  · intro j
    simpa [CtxMorDecl, lookup_snoc_succ, subst0_wk_cancel_decl] using
      (HasTypeDecl.var (E := E) (Γ := Γ) (i := j))

private theorem typing_inst0_decl {E : DeclEnv} {Γ : Ctx n} {A a : PureTm n}
    {body B : PureTm (n + 1)}
    (hBody : HasTypeDecl E (.snoc Γ A) body B) (ha : HasTypeDecl E Γ a A) :
    HasTypeDecl E Γ (inst0 a body) (inst0 a B) := by
  simpa [inst0] using
    (typing_subst_decl (E := E) (Γ := .snoc Γ A) (Δ := Γ) (σ := subst0 a) hBody
      (ctxMorDecl_subst0 (E := E) ha))

private def tmOfDecl {E : DeclEnv} {Γ : Ctx n} {t A : PureTm n}
    (_ : HasTypeDecl E Γ t A) : PureTm n := t

/-- Core-kernel one-step preservation inside declaration-aware typing, assuming
Pi/Sigma convertibility injectivity and argument-instantiation compatibility. -/
theorem core_step_preserves_type_decl_of_assumptions
    {E : DeclEnv}
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (inst0ArgConv :
      ∀ {k : Nat} {a a' : PureTm k} {B : PureTm (k + 1)},
        ConvDecl E a a' → ConvDecl E (inst0 a B) (inst0 a' B))
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl E Γ t A) (hr : Red t t') :
    HasTypeDecl E Γ t' A := by
  induction ht with
  | u0_type =>
      cases hr
  | var =>
      cases hr
  | const =>
      cases hr
  | @pi_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | congPiDom hred =>
          have hA' : HasTypeDecl E Γ _ .u1 := ihA hred
          have hB' : HasTypeDecl E (.snoc Γ _) B .u1 :=
            context_conv_head_decl
              (hAA' := redDecl_implies_conv (.core hred)) hB
          exact .pi_form hA' hB'
      | congPiCod hred =>
          exact .pi_form hA (ihB hred)
  | @sigma_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | congSigmaDom hred =>
          have hA' : HasTypeDecl E Γ _ .u1 := ihA hred
          have hB' : HasTypeDecl E (.snoc Γ _) B .u1 :=
            context_conv_head_decl
              (hAA' := redDecl_implies_conv (.core hred)) hB
          exact .sigma_form hA' hB'
      | congSigmaCod hred =>
          exact .sigma_form hA (ihB hred)
  | @lam_intro n Γ A body B hBody ihBody =>
      cases hr with
      | congLam hred =>
          exact .lam_intro (ihBody hred)
  | @app_elim n Γ f a A B hf ha ihf iha =>
      cases hr with
      | betaPi body _ =>
          have hfLam : HasTypeDecl E Γ (.lam body) (.pi A B) := by
            simpa using hf
          have haArg : HasTypeDecl E Γ a A := by
            simpa using ha
          rcases lam_generation_decl hfLam with ⟨A1, B1, hBody, hPiConv⟩
          have hAB : ConvDecl E A1 A ∧ ConvDecl E B1 B := piInjective hPiConv
          have ha1 : HasTypeDecl E Γ a A1 :=
            .conv haArg (Relation.EqvGen.symm _ _ hAB.1)
          have hSub : HasTypeDecl E Γ (inst0 a body) (inst0 a B1) :=
            typing_inst0_decl hBody ha1
          have hTy : ConvDecl E (inst0 a B1) (inst0 a B) :=
            convDecl_subst (E := E) (σ := subst0 a) hAB.2
          have hRes : HasTypeDecl E Γ (inst0 a body) (inst0 a B) :=
            .conv hSub hTy
          simpa using hRes
      | congAppFun hred =>
          exact .app_elim (ihf hred) ha
      | congAppArg hred =>
          have ha' : HasTypeDecl E Γ _ A := iha hred
          have hApp' : HasTypeDecl E Γ (.app f _) (inst0 _ B) := .app_elim hf ha'
          have hArgConv : ConvDecl E _ a :=
            Relation.EqvGen.symm _ _ (redDecl_implies_conv (.core hred))
          have hTy : ConvDecl E (inst0 _ B) (inst0 a B) := inst0ArgConv hArgConv
          exact .conv hApp' hTy
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      cases hr with
      | congPairFst hred =>
          have ha' : HasTypeDecl E Γ _ A := iha hred
          have hArgConv : ConvDecl E a _ := redDecl_implies_conv (.core hred)
          have hTy : ConvDecl E (inst0 a B) (inst0 _ B) := inst0ArgConv hArgConv
          have hb' : HasTypeDecl E Γ b (inst0 _ B) := .conv hb hTy
          exact .pair_intro ha' hb'
      | congPairSnd hred =>
          exact .pair_intro ha (ihb hred)
  | @fst_elim n Γ p A B hp ihp =>
      cases hr with
      | betaSigmaFst _ _ =>
          rcases pair_generation_decl hp with ⟨A1, B1, ha1, hb1, hSigma⟩
          have hAB : ConvDecl E A1 A ∧ ConvDecl E B1 B := sigmaInjective hSigma
          exact .conv ha1 hAB.1
      | congFst hred =>
          exact .fst_elim (ihp hred)
  | @snd_elim n Γ p A B hp ihp =>
      cases hr with
      | betaSigmaSnd _ _ =>
          rcases pair_generation_decl hp with ⟨A1, B1, ha1, hb1, hSigma⟩
          have hAB : ConvDecl E A1 A ∧ ConvDecl E B1 B := sigmaInjective hSigma
          let a0 : PureTm n := tmOfDecl ha1
          let b0 : PureTm n := tmOfDecl hb1
          have hb1' : HasTypeDecl E Γ b0 (inst0 a0 B1) := by
            simpa [a0, b0, tmOfDecl] using hb1
          have hCod : ConvDecl E (inst0 a0 B1) (inst0 a0 B) :=
            convDecl_subst (E := E) (σ := subst0 a0) hAB.2
          have hFst : ConvDecl E a0 (.fst (.pair a0 b0)) :=
            Relation.EqvGen.symm _ _ (redDecl_implies_conv (.core (Red.betaSigmaFst a0 b0)))
          have hArg : ConvDecl E (inst0 a0 B) (inst0 (.fst (.pair a0 b0)) B) :=
            inst0ArgConv hFst
          exact .conv hb1' (Relation.EqvGen.trans _ _ _ hCod hArg)
      | congSnd hred =>
          have hp' : HasTypeDecl E Γ _ (.sigma A B) := ihp hred
          have hsnd' : HasTypeDecl E Γ (.snd _) (inst0 (.fst _) B) := .snd_elim hp'
          have hFst : ConvDecl E (.fst _) (.fst p) :=
            Relation.EqvGen.symm _ _ (redDecl_implies_conv (.core (Red.congFst hred)))
          have hTy : ConvDecl E (inst0 (.fst _) B) (inst0 (.fst p) B) :=
            inst0ArgConv hFst
          exact .conv hsnd' hTy
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      cases hr with
      | congIdTy hred =>
          have hA' : HasTypeDecl E Γ _ .u1 := ihA hred
          have hAA' : ConvDecl E A _ := redDecl_implies_conv (.core hred)
          have ha' : HasTypeDecl E Γ a _ := .conv ha hAA'
          have hb' : HasTypeDecl E Γ b _ := .conv hb hAA'
          exact .id_form hA' ha' hb'
      | congIdLeft hred =>
          exact .id_form hA (iha hred) hb
      | congIdRight hred =>
          exact .id_form hA ha (ihb hred)
  | @refl_intro n Γ a A ha iha =>
      cases hr with
      | congRefl hred =>
          have ha' : HasTypeDecl E Γ _ A := iha hred
          let a' : PureTm n := tmOfDecl ha'
          have hidL : ConvDecl E (.id A a a) (.id A a' a) :=
            redDecl_implies_conv (.core (Red.congIdLeft hred))
          have hidR : ConvDecl E (.id A a' a) (.id A a' a') :=
            redDecl_implies_conv (.core (Red.congIdRight (A := A) (a := a') hred))
          have hid : ConvDecl E (.id A a a) (.id A a' a') :=
            Relation.EqvGen.trans _ _ _ hidL hidR
          exact .conv (.refl_intro ha') (Relation.EqvGen.symm _ _ hid)
  | @conv n Γ t A B ht hAB ih =>
      exact .conv (ih hr) hAB

/-- Core-kernel one-step preservation with only Pi/Sigma injectivity assumptions;
the instantiation compatibility premise is discharged by `inst0_arg_conv_decl`. -/
theorem core_step_preserves_type_decl_of_injective
    {E : DeclEnv}
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl E Γ t A) (hr : Red t t') :
    HasTypeDecl E Γ t' A := by
  exact core_step_preserves_type_decl_of_assumptions
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (inst0ArgConv := inst0_arg_conv_decl)
    ht hr

private theorem const_generation_aux {E : DeclEnv} {Γ : Ctx n} {t C : PureTm n}
    (ht : HasTypeDecl E Γ t C) :
    ∀ {c : DeclName}, t = .const c →
      ∃ A0 : PureTm 0, typeOf? E c = some A0 ∧ ConvDecl E (liftClosed (n := n) A0) C := by
  induction ht with
  | @const n Γ c A0 hLookup =>
      intro c' hEq
      cases hEq
      exact ⟨A0, hLookup, .refl _⟩
  | conv ht hconv ih =>
      intro c hEq
      rcases ih hEq with ⟨A0, hType, hConv⟩
      exact ⟨A0, hType, .trans _ _ _ hConv hconv⟩
  | u0_type =>
      intro c hEq
      cases hEq
  | var =>
      intro c hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro c hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro c hEq
      cases hEq
  | lam_intro hBody ihBody =>
      intro c hEq
      cases hEq
  | app_elim hf ha ihf iha =>
      intro c hEq
      cases hEq
  | pair_intro ha hb iha ihb =>
      intro c hEq
      cases hEq
  | fst_elim hp ihp =>
      intro c hEq
      cases hEq
  | snd_elim hp ihp =>
      intro c hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro c hEq
      cases hEq
  | refl_intro ha iha =>
      intro c hEq
      cases hEq

theorem const_generation {E : DeclEnv} {Γ : Ctx n} {c : DeclName} {C : PureTm n}
    (ht : HasTypeDecl E Γ (.const c) C) :
    ∃ A0 : PureTm 0, typeOf? E c = some A0 ∧ ConvDecl E (liftClosed (n := n) A0) C :=
  const_generation_aux ht rfl

/-- Soundness invariant for declaration-level unfolding:
every definitional value stored in `DeclEnv` is typed at its declared type. -/
def DeclValuesWellTyped (E : DeclEnv) : Prop :=
  ∀ {c : DeclName} {A0 v0 : PureTm 0},
    typeOf? E c = some A0 →
    valueOf? E c = some v0 →
    HasTypeDecl E .nil (liftClosed v0) (liftClosed A0)

/-- Packaged declaration-environment well-formedness for the current
declaration-aware kernel layer.
Closedness of stored declaration types and values is already enforced by
`DeclEntry` using `PureTm 0`; the packaged proof obligations here are the
semantic invariants used by declaration-aware reduction and preservation. -/
structure DeclEnvWellFormed (E : DeclEnv) : Prop where
  valuesWellTyped : DeclValuesWellTyped E
  noSelfDelta : ∀ {c : DeclName} {v0 : PureTm 0},
    valueOf? E c = some v0 → v0 ≠ (.const c)

theorem DeclEnvWellFormed.toDeclValuesWellTyped {E : DeclEnv}
    (hWf : DeclEnvWellFormed E) :
    DeclValuesWellTyped E :=
  hWf.valuesWellTyped

private theorem redDecl_const_step_inv {E : DeclEnv} {c : DeclName} {v : PureTm 0}
    (h : RedDecl E ((.const c : PureTm 0)) v) :
    ∃ v0 : PureTm 0, v = liftClosed v0 ∧ valueOf? E c = some v0 := by
  cases h with
  | core hred =>
      cases hred
  | deltaConst hVal =>
      exact ⟨_, rfl, hVal⟩

private theorem redDecl_const_step_inv_any {E : DeclEnv} {n : Nat} {c : DeclName} {u : PureTm n}
    (h : RedDecl E ((.const c : PureTm n)) u) :
    ∃ v0 : PureTm 0, u = liftClosed (n := n) v0 ∧ valueOf? E c = some v0 := by
  cases h with
  | core hred =>
      cases hred
  | deltaConst hVal =>
      exact ⟨_, rfl, hVal⟩

private theorem closed_typing_lift_to_ctx {E : DeclEnv} {Γ : Ctx n} {t A : PureTm 0}
    (h : HasTypeDecl E .nil (liftClosed t) (liftClosed A)) :
    HasTypeDecl E Γ (liftClosed (n := n) t) (liftClosed (n := n) A) := by
  let ρ0 : Ren 0 n := fun i => nomatch i
  have hρ : CtxRen .nil Γ ρ0 := by
    intro i
    nomatch i
  simpa [rename_liftClosed] using
    (typing_rename_decl (ht := h) (m := n) (Δ := Γ) (ρ := ρ0) hρ)

/-- Declaration-aware one-step preservation for `δ`-unfolding from a successful
value lookup in a well-formed declaration environment. -/
theorem deltaConst_preserves_type_of_lookup {E : DeclEnv} {Γ : Ctx n} {c : DeclName} {v0 : PureTm 0} {C : PureTm n}
    (hVal : valueOf? E c = some v0)
    (hTy : HasTypeDecl E Γ ((.const c : PureTm n)) C)
    (hWf : DeclEnvWellFormed E) :
    HasTypeDecl E Γ (liftClosed (n := n) v0) C := by
  rcases const_generation hTy with ⟨A0, hType, hConv⟩
  have hClosed : HasTypeDecl E .nil (liftClosed v0) (liftClosed A0) :=
    hWf.valuesWellTyped hType hVal
  have hLifted : HasTypeDecl E Γ (liftClosed (n := n) v0) (liftClosed (n := n) A0) :=
    closed_typing_lift_to_ctx (Γ := Γ) hClosed
  exact .conv hLifted hConv

theorem deltaConst_preserves_type {E : DeclEnv} {Γ : Ctx n} {c : DeclName} {v0 : PureTm 0} {C : PureTm n}
    (hStep : RedDecl E ((.const c : PureTm n)) (liftClosed (n := n) v0))
    (hTy : HasTypeDecl E Γ ((.const c : PureTm n)) C)
    (hWf : DeclEnvWellFormed E) :
    HasTypeDecl E Γ (liftClosed (n := n) v0) C := by
  rcases redDecl_const_step_inv_any hStep with ⟨v1, hEq, hVal⟩
  have hTyped : HasTypeDecl E Γ (liftClosed (n := n) v1) C :=
    deltaConst_preserves_type_of_lookup (Γ := Γ) (c := c) (v0 := v1) (C := C)
      (hVal := hVal) (hTy := hTy) (hWf := hWf)
  simpa [hEq] using hTyped

theorem const_head_step_preserves_type {E : DeclEnv} {Γ : Ctx n} {c : DeclName} {u C : PureTm n}
    (hStep : RedDecl E ((.const c : PureTm n)) u)
    (hTy : HasTypeDecl E Γ ((.const c : PureTm n)) C)
    (hWf : DeclEnvWellFormed E) :
    HasTypeDecl E Γ u C := by
  rcases redDecl_const_step_inv_any hStep with ⟨v0, hEq, hVal⟩
  have hDelta : HasTypeDecl E Γ (liftClosed (n := n) v0) C :=
    deltaConst_preserves_type_of_lookup
      (Γ := Γ) (c := c) (v0 := v0) (C := C)
      (hVal := hVal) (hTy := hTy) (hWf := hWf)
  simpa [hEq] using hDelta

/-- One-step subject reduction for declaration-aware reduction, under the same
Pi/Sigma conversion injectivity assumptions as the core theorem plus a well-formed
declaration environment for `δ`-unfolding. -/
theorem redDecl_step_preserves_type_of_assumptions
    {E : DeclEnv}
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (inst0ArgConv :
      ∀ {k : Nat} {a a' : PureTm k} {B : PureTm (k + 1)},
        ConvDecl E a a' → ConvDecl E (inst0 a B) (inst0 a' B))
    (hWf : DeclEnvWellFormed E)
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl E Γ t A) (hr : RedDecl E t t') :
    HasTypeDecl E Γ t' A := by
  induction ht with
  | u0_type =>
      cases hr with
      | core hred =>
          cases hred
  | var =>
      cases hr with
      | core hred =>
          cases hred
  | @const n Γ c A0 hLookup =>
      cases hr with
      | core hred =>
          cases hred
      | deltaConst hVal =>
          exact const_head_step_preserves_type
            (hStep := .deltaConst hVal)
            (hTy := .const hLookup)
            (hWf := hWf)
  | @pi_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .pi_form hA hB)
            (hr := hred)
      | congPiDom hred =>
          have hA' : HasTypeDecl E Γ _ .u1 := ihA hred
          have hB' : HasTypeDecl E (.snoc Γ _) B .u1 :=
            context_conv_head_decl (hAA' := redDecl_implies_conv hred) hB
          exact .pi_form hA' hB'
      | congPiCod hred =>
          exact .pi_form hA (ihB hred)
  | @sigma_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .sigma_form hA hB)
            (hr := hred)
      | congSigmaDom hred =>
          have hA' : HasTypeDecl E Γ _ .u1 := ihA hred
          have hB' : HasTypeDecl E (.snoc Γ _) B .u1 :=
            context_conv_head_decl (hAA' := redDecl_implies_conv hred) hB
          exact .sigma_form hA' hB'
      | congSigmaCod hred =>
          exact .sigma_form hA (ihB hred)
  | @lam_intro n Γ A body B hBody ihBody =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .lam_intro hBody)
            (hr := hred)
      | congLam hred =>
          exact .lam_intro (ihBody hred)
  | @app_elim n Γ f a A B hf ha ihf iha =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .app_elim hf ha)
            (hr := hred)
      | congAppFun hred =>
          exact .app_elim (ihf hred) ha
      | congAppArg hred =>
          have ha' : HasTypeDecl E Γ _ A := iha hred
          have hApp' : HasTypeDecl E Γ (.app f _) (inst0 _ B) := .app_elim hf ha'
          have hArgConv : ConvDecl E _ a :=
            Relation.EqvGen.symm _ _ (redDecl_implies_conv hred)
          have hTy : ConvDecl E (inst0 _ B) (inst0 a B) := inst0ArgConv hArgConv
          exact .conv hApp' hTy
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .pair_intro ha hb)
            (hr := hred)
      | congPairFst hred =>
          have ha' : HasTypeDecl E Γ _ A := iha hred
          have hArgConv : ConvDecl E a _ := redDecl_implies_conv hred
          have hTy : ConvDecl E (inst0 a B) (inst0 _ B) := inst0ArgConv hArgConv
          have hb' : HasTypeDecl E Γ b (inst0 _ B) := .conv hb hTy
          exact .pair_intro ha' hb'
      | congPairSnd hred =>
          exact .pair_intro ha (ihb hred)
  | @fst_elim n Γ p A B hp ihp =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .fst_elim hp)
            (hr := hred)
      | congFst hred =>
          exact .fst_elim (ihp hred)
  | @snd_elim n Γ p A B hp ihp =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .snd_elim hp)
            (hr := hred)
      | congSnd hred =>
          have hp' : HasTypeDecl E Γ _ (.sigma A B) := ihp hred
          have hsnd' : HasTypeDecl E Γ (.snd _) (inst0 (.fst _) B) := .snd_elim hp'
          have hFst : ConvDecl E (.fst _) (.fst p) :=
            Relation.EqvGen.symm _ _ (redDecl_implies_conv (.congFst hred))
          have hTy : ConvDecl E (inst0 (.fst _) B) (inst0 (.fst p) B) :=
            inst0ArgConv hFst
          exact .conv hsnd' hTy
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .id_form hA ha hb)
            (hr := hred)
      | congIdTy hred =>
          have hA' : HasTypeDecl E Γ _ .u1 := ihA hred
          have hAA' : ConvDecl E A _ := redDecl_implies_conv hred
          have ha' : HasTypeDecl E Γ a _ := .conv ha hAA'
          have hb' : HasTypeDecl E Γ b _ := .conv hb hAA'
          exact .id_form hA' ha' hb'
      | congIdLeft hred =>
          exact .id_form hA (iha hred) hb
      | congIdRight hred =>
          exact .id_form hA ha (ihb hred)
  | @refl_intro n Γ a A ha iha =>
      cases hr with
      | core hred =>
          exact core_step_preserves_type_decl_of_assumptions
            (piInjective := piInjective)
            (sigmaInjective := sigmaInjective)
            (inst0ArgConv := inst0ArgConv)
            (ht := .refl_intro ha)
            (hr := hred)
      | congRefl hred =>
          have ha' : HasTypeDecl E Γ _ A := iha hred
          let a' : PureTm n := tmOfDecl ha'
          have hidL : ConvDecl E (.id A a a) (.id A a' a) :=
            redDecl_implies_conv (.congIdLeft hred)
          have hidR : ConvDecl E (.id A a' a) (.id A a' a') :=
            redDecl_implies_conv (.congIdRight (A := A) (a := a') hred)
          have hid : ConvDecl E (.id A a a) (.id A a' a') :=
            Relation.EqvGen.trans _ _ _ hidL hidR
          exact .conv (.refl_intro ha') (Relation.EqvGen.symm _ _ hid)
  | @conv n Γ t A B ht hAB iht =>
      exact .conv (iht hr) hAB

/-- One-step declaration-aware preservation with only Pi/Sigma injectivity
assumptions; argument-instantiation compatibility is discharged by
`inst0_arg_conv_decl`. -/
theorem redDecl_step_preserves_type_of_injective
    {E : DeclEnv}
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (hWf : DeclEnvWellFormed E)
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl E Γ t A) (hr : RedDecl E t t') :
    HasTypeDecl E Γ t' A := by
  exact redDecl_step_preserves_type_of_assumptions
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (inst0ArgConv := inst0_arg_conv_decl)
    (hWf := hWf)
    ht hr

/-- Star-closure subject reduction for declaration-aware reduction under the
same assumptions as `redDecl_step_preserves_type_of_assumptions`. -/
theorem redStarDecl_preserves_type_of_assumptions
    {E : DeclEnv}
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (inst0ArgConv :
      ∀ {k : Nat} {a a' : PureTm k} {B : PureTm (k + 1)},
        ConvDecl E a a' → ConvDecl E (inst0 a B) (inst0 a' B))
    (hWf : DeclEnvWellFormed E)
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl E Γ t A) (hs : RedStarDecl E t u) :
    HasTypeDecl E Γ u A := by
  induction hs with
  | refl =>
      simpa using ht
  | tail hxy hyz ih =>
      exact redDecl_step_preserves_type_of_assumptions
        (piInjective := piInjective)
        (sigmaInjective := sigmaInjective)
        (inst0ArgConv := inst0ArgConv)
        (hWf := hWf)
        (ht := ih)
        (hr := hyz)

/-- Star-closure declaration-aware preservation with only Pi/Sigma injectivity
assumptions; argument-instantiation compatibility is discharged by
`inst0_arg_conv_decl`. -/
theorem redStarDecl_preserves_type_of_injective
    {E : DeclEnv}
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (hWf : DeclEnvWellFormed E)
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl E Γ t A) (hs : RedStarDecl E t u) :
    HasTypeDecl E Γ u A := by
  exact redStarDecl_preserves_type_of_assumptions
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (inst0ArgConv := inst0_arg_conv_decl)
    (hWf := hWf)
    ht hs

theorem deltaConst_preserves_type_closed {E : DeclEnv} {c : DeclName} {v0 C : PureTm 0}
    (hStep : RedDecl E ((.const c : PureTm 0)) (liftClosed v0))
    (hTy : HasTypeDecl E .nil ((.const c : PureTm 0)) C)
    (hWf : DeclEnvWellFormed E) :
    HasTypeDecl E .nil (liftClosed v0) C := by
  exact deltaConst_preserves_type
    (hStep := hStep)
    (hTy := hTy)
    (hWf := hWf)

/-- Generic closed checked-step for declaration unfolding (`δ`) from an explicit typed-value witness. -/
theorem checked_delta_step_closed_of_typed_value {E : DeclEnv} {c : DeclName} {A0 v0 : PureTm 0}
    (hType : typeOf? E c = some A0)
    (hVal : valueOf? E c = some v0)
    (hValTy : HasTypeDecl E .nil (liftClosed v0) (liftClosed A0)) :
    ∃ A : PureTm 0,
      HasTypeDecl E .nil ((.const c : PureTm 0)) A ∧
      RedDecl E ((.const c : PureTm 0)) (liftClosed v0) ∧
      HasTypeDecl E .nil (liftClosed v0) A := by
  exact ⟨liftClosed A0, .const hType, .deltaConst hVal, hValTy⟩

/-- Closed checked-step for declaration unfolding (`δ`) under the global declaration typed-value invariant. -/
theorem checked_delta_step_closed {E : DeclEnv} {c : DeclName} {A0 v0 : PureTm 0}
    (hType : typeOf? E c = some A0)
    (hVal : valueOf? E c = some v0)
    (hWf : DeclValuesWellTyped E) :
    ∃ A : PureTm 0,
      HasTypeDecl E .nil ((.const c : PureTm 0)) A ∧
      RedDecl E ((.const c : PureTm 0)) (liftClosed v0) ∧
      HasTypeDecl E .nil (liftClosed v0) A := by
  exact checked_delta_step_closed_of_typed_value hType hVal (hWf hType hVal)

theorem checked_delta_step_closed_wf {E : DeclEnv} {c : DeclName} {A0 v0 : PureTm 0}
    (hType : typeOf? E c = some A0)
    (hVal : valueOf? E c = some v0)
    (hWf : DeclEnvWellFormed E) :
    ∃ A : PureTm 0,
      HasTypeDecl E .nil ((.const c : PureTm 0)) A ∧
      RedDecl E ((.const c : PureTm 0)) (liftClosed v0) ∧
      HasTypeDecl E .nil (liftClosed v0) A := by
  exact checked_delta_step_closed hType hVal hWf.valuesWellTyped

end Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
