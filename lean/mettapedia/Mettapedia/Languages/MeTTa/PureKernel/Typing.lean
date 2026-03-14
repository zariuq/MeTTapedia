import Mettapedia.Languages.MeTTa.PureKernel.Context
import Mettapedia.Languages.MeTTa.PureKernel.Reduction

namespace Mettapedia.Languages.MeTTa.PureKernel.Typing

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction

abbrev Conv (t u : PureTm n) : Prop := Relation.EqvGen (@Red n) t u

inductive HasType : Ctx n → PureTm n → PureTm n → Prop where
  | u0_type (Γ : Ctx n) :
      HasType Γ .u0 .u1
  | var {Γ : Ctx n} (i : Fin n) :
      HasType Γ (.var i) (lookup Γ i)
  | pi_form {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)} :
      HasType Γ A .u1 →
      HasType (.snoc Γ A) B .u1 →
      HasType Γ (.pi A B) .u1
  | sigma_form {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)} :
      HasType Γ A .u1 →
      HasType (.snoc Γ A) B .u1 →
      HasType Γ (.sigma A B) .u1
  | lam_intro {Γ : Ctx n} {A : PureTm n} {body B : PureTm (n + 1)} :
      HasType (.snoc Γ A) body B →
      HasType Γ (.lam body) (.pi A B)
  | app_elim {Γ : Ctx n} {f a A : PureTm n} {B : PureTm (n + 1)} :
      HasType Γ f (.pi A B) →
      HasType Γ a A →
      HasType Γ (.app f a) (inst0 a B)
  | pair_intro {Γ : Ctx n} {a b A : PureTm n} {B : PureTm (n + 1)} :
      HasType Γ a A →
      HasType Γ b (inst0 a B) →
      HasType Γ (.pair a b) (.sigma A B)
  | fst_elim {Γ : Ctx n} {p A : PureTm n} {B : PureTm (n + 1)} :
      HasType Γ p (.sigma A B) →
      HasType Γ (.fst p) A
  | snd_elim {Γ : Ctx n} {p A : PureTm n} {B : PureTm (n + 1)} :
      HasType Γ p (.sigma A B) →
      HasType Γ (.snd p) (inst0 (.fst p) B)
  | id_form {Γ : Ctx n} {A a b : PureTm n} :
      HasType Γ A .u1 →
      HasType Γ a A →
      HasType Γ b A →
      HasType Γ (.id A a b) .u1
  | refl_intro {Γ : Ctx n} {a A : PureTm n} :
      HasType Γ a A →
      HasType Γ (.refl a) (.id A a a)
  | conv {Γ : Ctx n} {t A B : PureTm n} :
      HasType Γ t A →
      Conv A B →
      HasType Γ t B

theorem conv_refl (t : PureTm n) : Conv t t :=
  Relation.EqvGen.refl t

theorem red_implies_conv {t u : PureTm n} (h : Red t u) : Conv t u :=
  Relation.EqvGen.rel t u h

def renToSub (ρ : Ren n m) : Sub n m := fun i => .var (ρ i)

@[simp] theorem liftSub_renToSub (ρ : Ren n m) :
    liftSub (renToSub ρ) = renToSub (liftRen ρ) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem subst_renToSub (ρ : Ren n m) (t : PureTm n) :
    subst (renToSub ρ) t = rename ρ t := by
  induction t generalizing m with
  | var i =>
      rfl
  | const c =>
      rfl
  | u0 =>
      rfl
  | u1 =>
      rfl
  | pi A B ihA ihB =>
      simp [subst, rename, ihA, ihB, liftSub_renToSub]
  | sigma A B ihA ihB =>
      simp [subst, rename, ihA, ihB, liftSub_renToSub]
  | id A a b ihA iha ihb =>
      simp [subst, rename, ihA, iha, ihb]
  | lam b ih =>
      simp [subst, rename, ih, liftSub_renToSub]
  | app f a ihf iha =>
      simp [subst, rename, ihf, iha]
  | pair a b iha ihb =>
      simp [subst, rename, iha, ihb]
  | fst p ih =>
      simp [subst, rename, ih]
  | snd p ih =>
      simp [subst, rename, ih]
  | refl a iha =>
      simp [subst, rename, iha]

theorem red_rename {t u : PureTm n} (h : Red t u) :
    ∀ {m : Nat} (ρ : Ren n m), Red (rename ρ t) (rename ρ u) := by
  induction h with
  | betaPi body a =>
      intro m ρ
      simpa [rename, rename_inst0] using
        (Red.betaPi (rename (liftRen ρ) body) (rename ρ a))
  | betaSigmaFst a b =>
      intro m ρ
      simpa [rename] using (Red.betaSigmaFst (rename ρ a) (rename ρ b))
  | betaSigmaSnd a b =>
      intro m ρ
      simpa [rename] using (Red.betaSigmaSnd (rename ρ a) (rename ρ b))
  | congPiDom hA ih =>
      intro m ρ
      exact .congPiDom (ih ρ)
  | congPiCod hB ih =>
      intro m ρ
      exact .congPiCod (ih (liftRen ρ))
  | congSigmaDom hA ih =>
      intro m ρ
      exact .congSigmaDom (ih ρ)
  | congSigmaCod hB ih =>
      intro m ρ
      exact .congSigmaCod (ih (liftRen ρ))
  | congIdTy hA ih =>
      intro m ρ
      exact .congIdTy (ih ρ)
  | congIdLeft ha ih =>
      intro m ρ
      exact .congIdLeft (ih ρ)
  | congIdRight hb ih =>
      intro m ρ
      exact .congIdRight (ih ρ)
  | congLam hb ih =>
      intro m ρ
      exact .congLam (ih (liftRen ρ))
  | congAppFun hf ih =>
      intro m ρ
      exact .congAppFun (ih ρ)
  | congAppArg ha ih =>
      intro m ρ
      exact .congAppArg (ih ρ)
  | congPairFst ha ih =>
      intro m ρ
      exact .congPairFst (ih ρ)
  | congPairSnd hb ih =>
      intro m ρ
      exact .congPairSnd (ih ρ)
  | congFst hp ih =>
      intro m ρ
      exact .congFst (ih ρ)
  | congSnd hp ih =>
      intro m ρ
      exact .congSnd (ih ρ)
  | congRefl ha ih =>
      intro m ρ
      exact .congRefl (ih ρ)

theorem conv_rename (ρ : Ren n m) {t u : PureTm n} (h : Conv t u) :
    Conv (rename ρ t) (rename ρ u) := by
  induction h with
  | rel x y hred =>
      exact .rel _ _ (red_rename hred ρ)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

theorem typing_rename {Γ : Ctx n} {t A : PureTm n} (ht : HasType Γ t A) :
    ∀ {m : Nat} {Δ : Ctx m} {ρ : Ren n m},
      CtxRen Γ Δ ρ → HasType Δ (rename ρ t) (rename ρ A) := by
  induction ht with
  | u0_type Γ =>
      intro m Δ ρ hρ
      simpa [rename] using (HasType.u0_type (Γ := Δ))
  | var i =>
      intro m Δ ρ hρ
      simpa [hρ i] using (HasType.var (Γ := Δ) (i := ρ i))
  | @pi_form n Γ A B hA hB ihA ihB =>
      intro m Δ ρ hρ
      have hA' := ihA (m := m) (Δ := Δ) (ρ := ρ) hρ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (rename ρ A)) (ρ := liftRen ρ)
        (CtxRen.snoc hρ A)
      simpa [rename] using (HasType.pi_form hA' hB')
  | @sigma_form n Γ A B hA hB ihA ihB =>
      intro m Δ ρ hρ
      have hA' := ihA (m := m) (Δ := Δ) (ρ := ρ) hρ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (rename ρ A)) (ρ := liftRen ρ)
        (CtxRen.snoc hρ A)
      simpa [rename] using (HasType.sigma_form hA' hB')
  | @lam_intro n Γ A body B hBody ihBody =>
      intro m Δ ρ hρ
      have hBody' := ihBody (m := m + 1) (Δ := .snoc Δ (rename ρ A)) (ρ := liftRen ρ)
        (CtxRen.snoc hρ A)
      simpa [rename] using (HasType.lam_intro hBody')
  | @app_elim n Γ f a A B hf ha ihf iha =>
      intro m Δ ρ hρ
      simpa [rename, rename_inst0] using
        (HasType.app_elim
          (ihf (m := m) (Δ := Δ) (ρ := ρ) hρ)
          (iha (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      intro m Δ ρ hρ
      have ha' := iha (m := m) (Δ := Δ) (ρ := ρ) hρ
      have hb' : HasType Δ (rename ρ b) (inst0 (rename ρ a) (rename (liftRen ρ) B)) := by
        simpa [rename_inst0] using (ihb (m := m) (Δ := Δ) (ρ := ρ) hρ)
      simpa [rename] using (HasType.pair_intro ha' hb')
  | @fst_elim n Γ p A B hp ihp =>
      intro m Δ ρ hρ
      simpa [rename] using
        (HasType.fst_elim (ihp (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @snd_elim n Γ p A B hp ihp =>
      intro m Δ ρ hρ
      simpa [rename, rename_inst0] using
        (HasType.snd_elim (ihp (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      intro m Δ ρ hρ
      simpa [rename] using
        (HasType.id_form
          (ihA (m := m) (Δ := Δ) (ρ := ρ) hρ)
          (iha (m := m) (Δ := Δ) (ρ := ρ) hρ)
          (ihb (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @refl_intro n Γ a A ha iha =>
      intro m Δ ρ hρ
      simpa [rename] using
        (HasType.refl_intro (iha (m := m) (Δ := Δ) (ρ := ρ) hρ))
  | @conv n Γ t A B ht hAB iht =>
      intro m Δ ρ hρ
      exact HasType.conv
        (iht (m := m) (Δ := Δ) (ρ := ρ) hρ)
        (conv_rename ρ hAB)

/-- Weakening by one binder. -/
theorem weakening {Γ : Ctx n} {t A U : PureTm n}
    (ht : HasType Γ t A) :
    HasType (.snoc Γ U) (rename wk t) (rename wk A) := by
  have hwk : CtxRen Γ (.snoc Γ U) wk := by
    intro i
    simp [wk]
  simpa using (typing_rename ht (m := n + 1) (Δ := .snoc Γ U) (ρ := wk) hwk)

/-- Typed context morphism via simultaneous substitution. -/
def CtxMor (Γ : Ctx n) (Δ : Ctx m) (σ : Sub n m) : Prop :=
  ∀ i : Fin n, HasType Δ (σ i) (subst σ (lookup Γ i))

theorem CtxMor.lift {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m}
    (hσ : CtxMor Γ Δ σ) (A : PureTm n) :
    CtxMor (.snoc Γ A) (.snoc Δ (subst σ A)) (liftSub σ) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [CtxMor, lookup_snoc_zero, liftSub, subst_liftSub_wk] using
      (HasType.var (Γ := .snoc Δ (subst σ A)) (i := (0 : Fin (m + 1))))
  · intro j
    have hj : HasType (.snoc Δ (subst σ A))
        (rename wk (σ j))
        (rename wk (subst σ (lookup Γ j))) := by
      simpa using (weakening (Γ := Δ) (U := subst σ A) (ht := hσ j))
    simpa [CtxMor, lookup_snoc_succ, liftSub, subst_liftSub_wk] using hj

theorem red_subst {t u : PureTm n} (h : Red t u) :
    ∀ {m : Nat} (σ : Sub n m), Red (subst σ t) (subst σ u) := by
  induction h with
  | betaPi body a =>
      intro m σ
      simpa [subst, subst_inst0] using
        (Red.betaPi (subst (liftSub σ) body) (subst σ a))
  | betaSigmaFst a b =>
      intro m σ
      simpa [subst] using (Red.betaSigmaFst (subst σ a) (subst σ b))
  | betaSigmaSnd a b =>
      intro m σ
      simpa [subst] using (Red.betaSigmaSnd (subst σ a) (subst σ b))
  | congPiDom hA ih =>
      intro m σ
      exact .congPiDom (ih σ)
  | congPiCod hB ih =>
      intro m σ
      exact .congPiCod (ih (liftSub σ))
  | congSigmaDom hA ih =>
      intro m σ
      exact .congSigmaDom (ih σ)
  | congSigmaCod hB ih =>
      intro m σ
      exact .congSigmaCod (ih (liftSub σ))
  | congIdTy hA ih =>
      intro m σ
      exact .congIdTy (ih σ)
  | congIdLeft ha ih =>
      intro m σ
      exact .congIdLeft (ih σ)
  | congIdRight hb ih =>
      intro m σ
      exact .congIdRight (ih σ)
  | congLam hb ih =>
      intro m σ
      exact .congLam (ih (liftSub σ))
  | congAppFun hf ih =>
      intro m σ
      exact .congAppFun (ih σ)
  | congAppArg ha ih =>
      intro m σ
      exact .congAppArg (ih σ)
  | congPairFst ha ih =>
      intro m σ
      exact .congPairFst (ih σ)
  | congPairSnd hb ih =>
      intro m σ
      exact .congPairSnd (ih σ)
  | congFst hp ih =>
      intro m σ
      exact .congFst (ih σ)
  | congSnd hp ih =>
      intro m σ
      exact .congSnd (ih σ)
  | congRefl ha ih =>
      intro m σ
      exact .congRefl (ih σ)

theorem conv_subst (σ : Sub n m) {t u : PureTm n} (h : Conv t u) :
    Conv (subst σ t) (subst σ u) := by
  induction h with
  | rel x y hred =>
      exact .rel _ _ (red_subst hred σ)
  | refl x =>
      exact .refl _
  | symm x y hxy ih =>
      exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact .trans _ _ _ ihxy ihyz

/-- Generic simultaneous typing substitution along a typed context morphism. -/
theorem typing_subst {Γ : Ctx n} {t A : PureTm n} (ht : HasType Γ t A) :
    ∀ {m : Nat} {Δ : Ctx m} {σ : Sub n m},
      CtxMor Γ Δ σ → HasType Δ (subst σ t) (subst σ A) := by
  induction ht with
  | u0_type Γ =>
      intro m Δ σ hσ
      simpa [subst] using (HasType.u0_type (Γ := Δ))
  | var i =>
      intro m Δ σ hσ
      simpa [CtxMor] using hσ i
  | @pi_form n Γ A B hA hB ihA ihB =>
      intro m Δ σ hσ
      have hA' := ihA (m := m) (Δ := Δ) (σ := σ) hσ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (subst σ A)) (σ := liftSub σ)
        (CtxMor.lift hσ A)
      simpa [subst] using (HasType.pi_form hA' hB')
  | @sigma_form n Γ A B hA hB ihA ihB =>
      intro m Δ σ hσ
      have hA' := ihA (m := m) (Δ := Δ) (σ := σ) hσ
      have hB' := ihB (m := m + 1) (Δ := .snoc Δ (subst σ A)) (σ := liftSub σ)
        (CtxMor.lift hσ A)
      simpa [subst] using (HasType.sigma_form hA' hB')
  | @lam_intro n Γ A body B hBody ihBody =>
      intro m Δ σ hσ
      have hBody' := ihBody (m := m + 1) (Δ := .snoc Δ (subst σ A)) (σ := liftSub σ)
        (CtxMor.lift hσ A)
      simpa [subst] using (HasType.lam_intro hBody')
  | @app_elim n Γ f a A B hf ha ihf iha =>
      intro m Δ σ hσ
      simpa [subst, subst_inst0] using
        (HasType.app_elim
          (ihf (m := m) (Δ := Δ) (σ := σ) hσ)
          (iha (m := m) (Δ := Δ) (σ := σ) hσ))
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      intro m Δ σ hσ
      have ha' := iha (m := m) (Δ := Δ) (σ := σ) hσ
      have hb' : HasType Δ (subst σ b) (inst0 (subst σ a) (subst (liftSub σ) B)) := by
        simpa [subst_inst0] using (ihb (m := m) (Δ := Δ) (σ := σ) hσ)
      simpa [subst] using (HasType.pair_intro ha' hb')
  | @fst_elim n Γ p A B hp ihp =>
      intro m Δ σ hσ
      simpa [subst] using
        (HasType.fst_elim (ihp (m := m) (Δ := Δ) (σ := σ) hσ))
  | @snd_elim n Γ p A B hp ihp =>
      intro m Δ σ hσ
      simpa [subst, subst_inst0] using
        (HasType.snd_elim (ihp (m := m) (Δ := Δ) (σ := σ) hσ))
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      intro m Δ σ hσ
      simpa [subst] using
        (HasType.id_form
          (ihA (m := m) (Δ := Δ) (σ := σ) hσ)
          (iha (m := m) (Δ := Δ) (σ := σ) hσ)
          (ihb (m := m) (Δ := Δ) (σ := σ) hσ))
  | @refl_intro n Γ a A ha iha =>
      intro m Δ σ hσ
      simpa [subst] using
        (HasType.refl_intro (iha (m := m) (Δ := Δ) (σ := σ) hσ))
  | @conv n Γ t A B ht hAB iht =>
      intro m Δ σ hσ
      exact HasType.conv
        (iht (m := m) (Δ := Δ) (σ := σ) hσ)
        (conv_subst σ hAB)

/-- Transport typing along pointwise context conversion. -/
theorem context_conv {Γ Δ : Ctx n} {t T : PureTm n}
    (hctx : ∀ i : Fin n, Conv (lookup Γ i) (lookup Δ i))
    (ht : HasType Γ t T) :
    HasType Δ t T := by
  induction ht with
  | u0_type Γ =>
      exact .u0_type _
  | var i =>
      exact .conv
        (HasType.var (Γ := Δ) (i := i))
        (Relation.EqvGen.symm _ _ (hctx i))
  | @pi_form n Γ A B hA hB ihA ihB =>
      have hA' : HasType Δ A .u1 := ihA hctx
      have hctx' : ∀ i : Fin (n + 1), Conv (lookup (.snoc Γ A) i) (lookup (.snoc Δ A) i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact conv_refl _
        · intro j
          simpa [lookup_snoc_succ] using (conv_rename (ρ := wk) (hctx j))
      have hB' : HasType (.snoc Δ A) B .u1 := ihB hctx'
      exact .pi_form hA' hB'
  | @sigma_form n Γ A B hA hB ihA ihB =>
      have hA' : HasType Δ A .u1 := ihA hctx
      have hctx' : ∀ i : Fin (n + 1), Conv (lookup (.snoc Γ A) i) (lookup (.snoc Δ A) i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact conv_refl _
        · intro j
          simpa [lookup_snoc_succ] using (conv_rename (ρ := wk) (hctx j))
      have hB' : HasType (.snoc Δ A) B .u1 := ihB hctx'
      exact .sigma_form hA' hB'
  | @lam_intro n Γ A body B hBody ihBody =>
      have hctx' : ∀ i : Fin (n + 1), Conv (lookup (.snoc Γ A) i) (lookup (.snoc Δ A) i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact conv_refl _
        · intro j
          simpa [lookup_snoc_succ] using (conv_rename (ρ := wk) (hctx j))
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

/-- Specialization of `context_conv` to changing only the head binder type. -/
theorem context_conv_head {Γ : Ctx n} {A A' : PureTm n} {t T : PureTm (n + 1)}
    (hAA' : Conv A A') (ht : HasType (.snoc Γ A) t T) :
    HasType (.snoc Γ A') t T := by
  have hctx : ∀ i : Fin (n + 1),
      Conv (lookup (.snoc Γ A) i) (lookup (.snoc Γ A') i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [lookup_snoc_zero] using (conv_rename (ρ := wk) hAA')
    · intro j
      simpa [lookup_snoc_succ] using (conv_refl (rename wk (lookup Γ j)))
  exact context_conv hctx ht

end Mettapedia.Languages.MeTTa.PureKernel.Typing
