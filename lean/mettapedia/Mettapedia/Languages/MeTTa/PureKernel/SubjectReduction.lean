import Mettapedia.Languages.MeTTa.PureKernel.Confluence

namespace Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Parallel
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.Confluence

private theorem subst0_wk_cancel (a t : PureTm n) :
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

private theorem ctxMor_subst0 {Γ : Ctx n} {A a : PureTm n}
    (ha : HasType Γ a A) :
    CtxMor (.snoc Γ A) Γ (subst0 a) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [CtxMor, lookup_snoc_zero, subst0_wk_cancel] using ha
  · intro j
    simpa [CtxMor, lookup_snoc_succ, subst0_wk_cancel] using
      (HasType.var (Γ := Γ) (i := j))

private theorem typing_inst0 {Γ : Ctx n} {A a : PureTm n} {body B : PureTm (n + 1)}
    (hbody : HasType (.snoc Γ A) body B) (ha : HasType Γ a A) :
    HasType Γ (inst0 a body) (inst0 a B) := by
  simpa [inst0] using
    (typing_subst (Γ := .snoc Γ A) (Δ := Γ) (σ := subst0 a) hbody (ctxMor_subst0 ha))

private def tmOf {Γ : Ctx n} {t A : PureTm n} (_ : HasType Γ t A) : PureTm n := t

private theorem parStar_inst0_arg {a a' : PureTm n} {B : PureTm (n + 1)}
    (h : ParStar a a') : ParStar (inst0 a B) (inst0 a' B) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih (par_inst0 hyz (par_refl B))

private theorem redStar_inst0_arg {a a' : PureTm n} {B : PureTm (n + 1)}
    (h : RedStar a a') : RedStar (inst0 a B) (inst0 a' B) := by
  exact parStar_to_redStar (parStar_inst0_arg (redStar_to_parStar h))

private theorem conv_inst0_arg {a a' : PureTm n} {B : PureTm (n + 1)}
    (h : Conv a a') : Conv (inst0 a B) (inst0 a' B) := by
  rcases church_rosser_conv h with ⟨u, ha, ha'⟩
  have h1 : RedStar (inst0 a B) (inst0 u B) := redStar_inst0_arg ha
  have h2 : RedStar (inst0 a' B) (inst0 u B) := redStar_inst0_arg ha'
  have hc1 : Conv (inst0 a B) (inst0 u B) := redStar_implies_conv h1
  have hc2 : Conv (inst0 a' B) (inst0 u B) := redStar_implies_conv h2
  exact Relation.EqvGen.trans _ _ _ hc1 (Relation.EqvGen.symm _ _ hc2)

private theorem app_generation_aux {Γ : Ctx n} {t C : PureTm n}
    (ht : HasType Γ t C) :
    ∀ {f a : PureTm n}, t = .app f a →
      ∃ A B, HasType Γ f (.pi A B) ∧ HasType Γ a A ∧ Conv (inst0 a B) C := by
  induction ht with
  | app_elim hf ha =>
      intro f a hEq
      cases hEq
      exact ⟨_, _, hf, ha, conv_refl _⟩
  | conv ht hconv ih =>
      intro f a hEq
      rcases ih hEq with ⟨A, B, hf, ha, hC⟩
      exact ⟨A, B, hf, ha, Relation.EqvGen.trans _ _ _ hC hconv⟩
  | u0_type =>
      intro f a hEq
      cases hEq
  | var =>
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

theorem app_generation {Γ : Ctx n} {f a C : PureTm n}
    (ht : HasType Γ (.app f a) C) :
    ∃ A B, HasType Γ f (.pi A B) ∧ HasType Γ a A ∧ Conv (inst0 a B) C :=
  app_generation_aux ht rfl

private theorem lam_generation_aux {Γ : Ctx n} {t C : PureTm n}
    (ht : HasType Γ t C) :
    ∀ {body : PureTm (n + 1)}, t = .lam body →
      ∃ A B, HasType (.snoc Γ A) body B ∧ Conv (.pi A B) C := by
  induction ht with
  | lam_intro hBody =>
      intro body hEq
      cases hEq
      exact ⟨_, _, hBody, conv_refl _⟩
  | conv ht hconv ih =>
      intro body hEq
      rcases ih hEq with ⟨A, B, hBody, hPi⟩
      exact ⟨A, B, hBody, Relation.EqvGen.trans _ _ _ hPi hconv⟩
  | u0_type =>
      intro body hEq
      cases hEq
  | var =>
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

theorem lam_generation {Γ : Ctx n} {body : PureTm (n + 1)} {C : PureTm n}
    (ht : HasType Γ (.lam body) C) :
    ∃ A B, HasType (.snoc Γ A) body B ∧ Conv (.pi A B) C :=
  lam_generation_aux ht rfl

private theorem pair_generation_aux {Γ : Ctx n} {t C : PureTm n}
    (ht : HasType Γ t C) :
    ∀ {a b : PureTm n}, t = .pair a b →
      ∃ A B, HasType Γ a A ∧ HasType Γ b (inst0 a B) ∧ Conv (.sigma A B) C := by
  induction ht with
  | pair_intro ha hb =>
      intro a b hEq
      cases hEq
      exact ⟨_, _, ha, hb, conv_refl _⟩
  | conv ht hconv ih =>
      intro a b hEq
      rcases ih hEq with ⟨A, B, ha, hb, hSigma⟩
      exact ⟨A, B, ha, hb, Relation.EqvGen.trans _ _ _ hSigma hconv⟩
  | u0_type =>
      intro a b hEq
      cases hEq
  | var =>
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

theorem pair_generation {Γ : Ctx n} {a b C : PureTm n}
    (ht : HasType Γ (.pair a b) C) :
    ∃ A B, HasType Γ a A ∧ HasType Γ b (inst0 a B) ∧ Conv (.sigma A B) C :=
  pair_generation_aux ht rfl

/-- One-step subject reduction for the Pure kernel. -/
theorem subject_reduction {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasType Γ t A) (hr : Red t t') :
    HasType Γ t' A := by
  induction ht with
  | u0_type =>
      cases hr
  | var =>
      cases hr
  | @pi_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | congPiDom hred =>
          have hA' : HasType Γ _ .u1 := ihA hred
          have hB' : HasType (.snoc Γ _) B .u1 := context_conv_head (red_implies_conv hred) hB
          exact .pi_form hA' hB'
      | congPiCod hred =>
          exact .pi_form hA (ihB hred)
  | @sigma_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | congSigmaDom hred =>
          have hA' : HasType Γ _ .u1 := ihA hred
          have hB' : HasType (.snoc Γ _) B .u1 := context_conv_head (red_implies_conv hred) hB
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
          have hfLam : HasType Γ (.lam body) (.pi A B) := by
            simpa using hf
          have haArg : HasType Γ a A := by
            simpa using ha
          rcases lam_generation hfLam with ⟨A1, B1, hBody, hPiConv⟩
          have hAB : Conv A1 A ∧ Conv B1 B := pi_injectivity hPiConv
          have ha1 : HasType Γ a A1 :=
            .conv haArg (Relation.EqvGen.symm _ _ hAB.1)
          have hSub : HasType Γ (inst0 a body) (inst0 a B1) :=
            typing_inst0 hBody ha1
          have hTy : Conv (inst0 a B1) (inst0 a B) :=
            conv_subst (σ := subst0 a) hAB.2
          have hRes : HasType Γ (inst0 a body) (inst0 a B) :=
            .conv hSub hTy
          simpa using hRes
      | congAppFun hred =>
          exact .app_elim (ihf hred) ha
      | congAppArg hred =>
          have ha' : HasType Γ _ A := iha hred
          have hApp' : HasType Γ (.app f _) (inst0 _ B) := .app_elim hf ha'
          have hArgConv : Conv a _ := red_implies_conv hred
          have hTy : Conv (inst0 _ B) (inst0 a B) :=
            conv_inst0_arg (Relation.EqvGen.symm _ _ hArgConv)
          exact .conv hApp' hTy
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      cases hr with
      | congPairFst hred =>
          have ha' : HasType Γ _ A := iha hred
          have hArgConv : Conv a _ := red_implies_conv hred
          have hTy : Conv (inst0 a B) (inst0 _ B) := conv_inst0_arg hArgConv
          have hb' : HasType Γ b (inst0 _ B) := .conv hb hTy
          exact .pair_intro ha' hb'
      | congPairSnd hred =>
          exact .pair_intro ha (ihb hred)
  | @fst_elim n Γ p A B hp ihp =>
      cases hr with
      | betaSigmaFst _ _ =>
          rcases pair_generation hp with ⟨A1, B1, ha1, hb1, hSigma⟩
          have hAB : Conv A1 A ∧ Conv B1 B := sigma_injectivity hSigma
          exact .conv ha1 hAB.1
      | congFst hred =>
          exact .fst_elim (ihp hred)
  | @snd_elim n Γ p A B hp ihp =>
      cases hr with
      | betaSigmaSnd _ _ =>
          rcases pair_generation hp with ⟨A1, B1, ha1, hb1, hSigma⟩
          have hAB : Conv A1 A ∧ Conv B1 B := sigma_injectivity hSigma
          let a0 : PureTm n := tmOf ha1
          let b0 : PureTm n := tmOf hb1
          have hb1' : HasType Γ b0 (inst0 a0 B1) := by
            simpa [a0, b0, tmOf] using hb1
          have hCod : Conv (inst0 a0 B1) (inst0 a0 B) :=
            conv_subst (σ := subst0 a0) hAB.2
          have hFst : Conv a0 (.fst (.pair a0 b0)) :=
            Relation.EqvGen.symm _ _ (red_implies_conv (Red.betaSigmaFst a0 b0))
          have hArg : Conv (inst0 a0 B) (inst0 (.fst (.pair a0 b0)) B) :=
            conv_inst0_arg hFst
          exact .conv hb1' (Relation.EqvGen.trans _ _ _ hCod hArg)
      | congSnd hred =>
          have hp' : HasType Γ _ (.sigma A B) := ihp hred
          have hsnd' : HasType Γ (.snd _) (inst0 (.fst _) B) := .snd_elim hp'
          have hFst : Conv (.fst _) (.fst p) :=
            Relation.EqvGen.symm _ _ (red_implies_conv (Red.congFst hred))
          have hTy : Conv (inst0 (.fst _) B) (inst0 (.fst p) B) :=
            conv_inst0_arg hFst
          exact .conv hsnd' hTy
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      cases hr with
      | congIdTy hred =>
          have hA' : HasType Γ _ .u1 := ihA hred
          have hAA' : Conv A _ := red_implies_conv hred
          have ha' : HasType Γ a _ := .conv ha hAA'
          have hb' : HasType Γ b _ := .conv hb hAA'
          exact .id_form hA' ha' hb'
      | congIdLeft hred =>
          exact .id_form hA (iha hred) hb
      | congIdRight hred =>
          exact .id_form hA ha (ihb hred)
  | @refl_intro n Γ a A ha iha =>
      cases hr with
      | congRefl hred =>
          have ha' : HasType Γ _ A := iha hred
          let a' : PureTm n := tmOf ha'
          have hidL : Conv (.id A a a) (.id A a' a) :=
            red_implies_conv (Red.congIdLeft hred)
          have hidR : Conv (.id A a' a) (.id A a' a') :=
            red_implies_conv (Red.congIdRight (A := A) (a := a') hred)
          have hid : Conv (.id A a a) (.id A a' a') :=
            Relation.EqvGen.trans _ _ _ hidL hidR
          exact .conv (.refl_intro ha') (Relation.EqvGen.symm _ _ hid)
  | @conv n Γ t A B ht hAB ih =>
      exact .conv (ih hr) hAB

end Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
