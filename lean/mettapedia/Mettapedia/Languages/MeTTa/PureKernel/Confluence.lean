import Mathlib.Logic.Relation
import Mettapedia.Languages.MeTTa.PureKernel.Parallel
import Mettapedia.Languages.MeTTa.PureKernel.Typing

namespace Mettapedia.Languages.MeTTa.PureKernel.Confluence

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Parallel
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-- Complete development for parallel reduction. -/
def cdev : PureTm n → PureTm n
  | .var i => .var i
  | .u0 => .u0
  | .u1 => .u1
  | .pi A B => .pi (cdev A) (cdev B)
  | .sigma A B => .sigma (cdev A) (cdev B)
  | .id A a b => .id (cdev A) (cdev a) (cdev b)
  | .lam b => .lam (cdev b)
  | .app (.lam b) a => inst0 (cdev a) (cdev b)
  | .app f a => .app (cdev f) (cdev a)
  | .pair a b => .pair (cdev a) (cdev b)
  | .fst (.pair a _) => cdev a
  | .fst p => .fst (cdev p)
  | .snd (.pair _ b) => cdev b
  | .snd p => .snd (cdev p)
  | .refl a => .refl (cdev a)

/-- Parallel reduction always reaches complete development. -/
theorem par_to_cdev : ∀ {t u : PureTm n}, ParRed t u → ParRed u (cdev t) := by
  intro t u h
  induction h with
  | var i =>
      simp [cdev]
  | u0 =>
      simp [cdev]
  | u1 =>
      simp [cdev]
  | pi hA hB ihA ihB =>
      simpa [cdev] using ParRed.pi ihA ihB
  | sigma hA hB ihA ihB =>
      simpa [cdev] using ParRed.sigma ihA ihB
  | id hA ha hb ihA iha ihb =>
      simpa [cdev] using ParRed.id ihA iha ihb
  | lam hb ih =>
      simpa [cdev] using ParRed.lam ih
  | @app _ f f' a a' hf ha ihf iha =>
      cases f with
      | var i =>
          simpa [cdev] using ParRed.app ihf iha
      | u0 =>
          simpa [cdev] using ParRed.app ihf iha
      | u1 =>
          simpa [cdev] using ParRed.app ihf iha
      | pi A B =>
          simpa [cdev] using ParRed.app ihf iha
      | sigma A B =>
          simpa [cdev] using ParRed.app ihf iha
      | id A a b =>
          simpa [cdev] using ParRed.app ihf iha
      | lam b =>
          cases hf with
          | lam hb =>
              cases ihf with
              | lam hbc =>
                  simpa [cdev] using (ParRed.betaPi hbc iha)
      | app f a =>
          simpa [cdev] using ParRed.app ihf iha
      | pair a b =>
          simpa [cdev] using ParRed.app ihf iha
      | fst p =>
          simpa [cdev] using ParRed.app ihf iha
      | snd p =>
          simpa [cdev] using ParRed.app ihf iha
      | refl a =>
          simpa [cdev] using ParRed.app ihf iha
  | pair ha hb iha ihb =>
      simpa [cdev] using ParRed.pair iha ihb
  | @fst _ p p' hp ih =>
      cases p with
      | var i =>
          simpa [cdev] using ParRed.fst ih
      | u0 =>
          simpa [cdev] using ParRed.fst ih
      | u1 =>
          simpa [cdev] using ParRed.fst ih
      | pi A B =>
          simpa [cdev] using ParRed.fst ih
      | sigma A B =>
          simpa [cdev] using ParRed.fst ih
      | id A a b =>
          simpa [cdev] using ParRed.fst ih
      | lam b =>
          simpa [cdev] using ParRed.fst ih
      | app f a =>
          simpa [cdev] using ParRed.fst ih
      | pair a b =>
          cases hp with
          | pair ha hb =>
              cases ih with
              | pair ha' hb' =>
                  simpa [cdev] using (ParRed.betaSigmaFst ha' hb')
      | fst q =>
          simpa [cdev] using ParRed.fst ih
      | snd q =>
          simpa [cdev] using ParRed.fst ih
      | refl a =>
          simpa [cdev] using ParRed.fst ih
  | @snd _ p p' hp ih =>
      cases p with
      | var i =>
          simpa [cdev] using ParRed.snd ih
      | u0 =>
          simpa [cdev] using ParRed.snd ih
      | u1 =>
          simpa [cdev] using ParRed.snd ih
      | pi A B =>
          simpa [cdev] using ParRed.snd ih
      | sigma A B =>
          simpa [cdev] using ParRed.snd ih
      | id A a b =>
          simpa [cdev] using ParRed.snd ih
      | lam b =>
          simpa [cdev] using ParRed.snd ih
      | app f a =>
          simpa [cdev] using ParRed.snd ih
      | pair a b =>
          cases hp with
          | pair ha hb =>
              cases ih with
              | pair ha' hb' =>
                  simpa [cdev] using (ParRed.betaSigmaSnd ha' hb')
      | fst q =>
          simpa [cdev] using ParRed.snd ih
      | snd q =>
          simpa [cdev] using ParRed.snd ih
      | refl a =>
          simpa [cdev] using ParRed.snd ih
  | refl ha iha =>
      simpa [cdev] using ParRed.refl iha
  | betaPi hbody ha ihbody iha =>
      simpa [cdev] using par_inst0 iha ihbody
  | betaSigmaFst ha hb iha ihb =>
      simpa [cdev] using iha
  | betaSigmaSnd ha hb iha ihb =>
      simpa [cdev] using ihb

theorem par_to_cdev_self (t : PureTm n) : ParRed t (cdev t) :=
  par_to_cdev (par_refl t)

/-- Diamond property for parallel reduction via complete development. -/
theorem diamond_parRed {s t₁ t₂ : PureTm n}
    (h₁ : ParRed s t₁) (h₂ : ParRed s t₂) :
    ∃ u, ParRed t₁ u ∧ ParRed t₂ u :=
  ⟨cdev s, par_to_cdev h₁, par_to_cdev h₂⟩

abbrev ParStar (t u : PureTm n) : Prop := Relation.ReflTransGen ParRed t u

theorem redStar_to_parStar {t u : PureTm n} (h : RedStar t u) : ParStar t u := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih (red_to_par hyz)

theorem parStar_to_redStar {t u : PureTm n} (h : ParStar t u) : RedStar t u := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact RedStar.trans ih (par_to_redStar hyz)

/-- Confluence of parallel-star by local diamond. -/
theorem parStar_confluence {s t₁ t₂ : PureTm n}
    (h₁ : ParStar s t₁) (h₂ : ParStar s t₂) :
    ∃ u, ParStar t₁ u ∧ ParStar t₂ u := by
  have hlocal : ∀ (a b c : PureTm n), ParRed a b → ParRed a c →
      ∃ d : PureTm n, Relation.ReflGen ParRed b d ∧ Relation.ReflTransGen ParRed c d := by
    intro a b c hab hac
    rcases diamond_parRed hab hac with ⟨d, hbd, hcd⟩
    exact ⟨d, Relation.ReflGen.single hbd,
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hcd⟩
  rcases Relation.church_rosser (r := ParRed) hlocal h₁ h₂ with ⟨u, hu₁, hu₂⟩
  exact ⟨u, hu₁, hu₂⟩

/-- Confluence of multi-step β-reduction. -/
theorem redStar_confluence {s t₁ t₂ : PureTm n}
    (h₁ : RedStar s t₁) (h₂ : RedStar s t₂) :
    ∃ u, RedStar t₁ u ∧ RedStar t₂ u := by
  rcases parStar_confluence (redStar_to_parStar h₁) (redStar_to_parStar h₂) with
    ⟨u, hu₁, hu₂⟩
  exact ⟨u, parStar_to_redStar hu₁, parStar_to_redStar hu₂⟩

theorem redStar_implies_conv {t u : PureTm n} (h : RedStar t u) : Conv t u := by
  induction h with
  | refl =>
      exact Relation.EqvGen.refl _
  | tail hxy hyz ih =>
      exact Relation.EqvGen.trans _ _ _ ih (red_implies_conv hyz)

/-- Church-Rosser for conversion generated by one-step reduction. -/
theorem church_rosser_conv {s t : PureTm n} (h : Conv s t) :
    ∃ u, RedStar s u ∧ RedStar t u := by
  refine Relation.EqvGen.rec ?hrel ?hrefl ?hsymm ?htrans h
  · intro a b hab
    exact ⟨b, red_to_redStar hab, RedStar.refl _⟩
  · intro a
    exact ⟨a, RedStar.refl _, RedStar.refl _⟩
  · intro a b hab ih
    rcases ih with ⟨u, ha, hb⟩
    exact ⟨u, hb, ha⟩
  · intro a b c hab hbc ihab ihbc
    rcases ihab with ⟨u₁, ha_u₁, hb_u₁⟩
    rcases ihbc with ⟨u₂, hb_u₂, hc_u₂⟩
    rcases redStar_confluence hb_u₁ hb_u₂ with ⟨w, hu₁_w, hu₂_w⟩
    exact ⟨w, RedStar.trans ha_u₁ hu₁_w, RedStar.trans hc_u₂ hu₂_w⟩

/-- One-step reduction from Pi keeps Pi head. -/
private theorem red_pi_head {A : PureTm n} {B : PureTm (n + 1)} {t : PureTm n}
    (h : Red (.pi A B) t) :
    ∃ (A' : PureTm n) (B' : PureTm (n + 1)), t = .pi A' B' := by
  cases h with
  | congPiDom hA => exact ⟨_, _, rfl⟩
  | congPiCod hB => exact ⟨_, _, rfl⟩

/-- One-step reduction from Sigma keeps Sigma head. -/
private theorem red_sigma_head {A : PureTm n} {B : PureTm (n + 1)} {t : PureTm n}
    (h : Red (.sigma A B) t) :
    ∃ (A' : PureTm n) (B' : PureTm (n + 1)), t = .sigma A' B' := by
  cases h with
  | congSigmaDom hA => exact ⟨_, _, rfl⟩
  | congSigmaCod hB => exact ⟨_, _, rfl⟩

theorem redStar_pi_head {A : PureTm n} {B : PureTm (n + 1)} {t : PureTm n}
    (h : RedStar (.pi A B) t) :
    ∃ (A' : PureTm n) (B' : PureTm (n + 1)), t = .pi A' B' :=
by
  induction h with
  | refl =>
      exact ⟨A, B, rfl⟩
  | tail hxy hyz ih =>
      rcases ih with ⟨Am, Bm, hm⟩
      subst hm
      exact red_pi_head hyz

theorem redStar_sigma_head {A : PureTm n} {B : PureTm (n + 1)} {t : PureTm n}
    (h : RedStar (.sigma A B) t) :
    ∃ (A' : PureTm n) (B' : PureTm (n + 1)), t = .sigma A' B' := by
  induction h with
  | refl =>
      exact ⟨A, B, rfl⟩
  | tail hxy hyz ih =>
      rcases ih with ⟨Am, Bm, hm⟩
      subst hm
      exact red_sigma_head hyz

private theorem redStar_pi_decomp_full {A : PureTm n} {B : PureTm (n + 1)}
    {t : PureTm n} (h : RedStar (.pi A B) t) :
    ∃ (A' : PureTm n) (B' : PureTm (n + 1)), t = .pi A' B' ∧
      RedStar A A' ∧ RedStar B B' := by
  induction h with
  | refl =>
      exact ⟨A, B, rfl, RedStar.refl _, RedStar.refl _⟩
  | tail hxy hyz ih =>
      rcases ih with ⟨Am, Bm, hm, hA, hB⟩
      subst hm
      cases hyz with
      | congPiDom hAstep =>
          exact ⟨_, _, rfl, RedStar.tail hA hAstep, hB⟩
      | congPiCod hBstep =>
          exact ⟨_, _, rfl, hA, RedStar.tail hB hBstep⟩

theorem redStar_pi_decomp {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : RedStar (.pi A B) (.pi A' B')) :
    RedStar A A' ∧ RedStar B B' := by
  rcases redStar_pi_decomp_full h with ⟨A₁, B₁, ht, hA, hB⟩
  simp at ht
  obtain ⟨rfl, rfl⟩ := ht
  exact ⟨hA, hB⟩

private theorem redStar_sigma_decomp_full {A : PureTm n} {B : PureTm (n + 1)}
    {t : PureTm n} (h : RedStar (.sigma A B) t) :
    ∃ (A' : PureTm n) (B' : PureTm (n + 1)), t = .sigma A' B' ∧
      RedStar A A' ∧ RedStar B B' := by
  induction h with
  | refl =>
      exact ⟨A, B, rfl, RedStar.refl _, RedStar.refl _⟩
  | tail hxy hyz ih =>
      rcases ih with ⟨Am, Bm, hm, hA, hB⟩
      subst hm
      cases hyz with
      | congSigmaDom hAstep =>
          exact ⟨_, _, rfl, RedStar.tail hA hAstep, hB⟩
      | congSigmaCod hBstep =>
          exact ⟨_, _, rfl, hA, RedStar.tail hB hBstep⟩

theorem redStar_sigma_decomp {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : RedStar (.sigma A B) (.sigma A' B')) :
    RedStar A A' ∧ RedStar B B' := by
  rcases redStar_sigma_decomp_full h with ⟨A₁, B₁, ht, hA, hB⟩
  simp at ht
  obtain ⟨rfl, rfl⟩ := ht
  exact ⟨hA, hB⟩

/-- Pi injectivity under conversion, via Church-Rosser + decomposition. -/
theorem pi_injectivity {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : Conv (.pi A B) (.pi A' B')) :
    Conv A A' ∧ Conv B B' := by
  rcases church_rosser_conv h with ⟨u, h₁, h₂⟩
  rcases redStar_pi_head h₁ with ⟨U, V, hu⟩
  have h₂' : RedStar (.pi A' B') (.pi U V) := by simpa [hu] using h₂
  have h₁' : RedStar (.pi A B) (.pi U V) := by simpa [hu] using h₁
  have hdec₁ := redStar_pi_decomp h₁'
  have hdec₂ := redStar_pi_decomp h₂'
  have hAU : Conv A U := redStar_implies_conv hdec₁.1
  have hA'U : Conv A' U := redStar_implies_conv hdec₂.1
  have hBV : Conv B V := redStar_implies_conv hdec₁.2
  have hB'V : Conv B' V := redStar_implies_conv hdec₂.2
  have hUA' : Conv U A' := Relation.EqvGen.symm _ _ hA'U
  have hVB' : Conv V B' := Relation.EqvGen.symm _ _ hB'V
  exact ⟨Relation.EqvGen.trans _ _ _ hAU hUA', Relation.EqvGen.trans _ _ _ hBV hVB'⟩

/-- Sigma injectivity under conversion, via Church-Rosser + decomposition. -/
theorem sigma_injectivity {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : Conv (.sigma A B) (.sigma A' B')) :
    Conv A A' ∧ Conv B B' := by
  rcases church_rosser_conv h with ⟨u, h₁, h₂⟩
  rcases redStar_sigma_head h₁ with ⟨U, V, hu⟩
  have h₂' : RedStar (.sigma A' B') (.sigma U V) := by simpa [hu] using h₂
  have h₁' : RedStar (.sigma A B) (.sigma U V) := by simpa [hu] using h₁
  have hdec₁ := redStar_sigma_decomp h₁'
  have hdec₂ := redStar_sigma_decomp h₂'
  have hAU : Conv A U := redStar_implies_conv hdec₁.1
  have hA'U : Conv A' U := redStar_implies_conv hdec₂.1
  have hBV : Conv B V := redStar_implies_conv hdec₁.2
  have hB'V : Conv B' V := redStar_implies_conv hdec₂.2
  have hUA' : Conv U A' := Relation.EqvGen.symm _ _ hA'U
  have hVB' : Conv V B' := Relation.EqvGen.symm _ _ hB'V
  exact ⟨Relation.EqvGen.trans _ _ _ hAU hUA', Relation.EqvGen.trans _ _ _ hBV hVB'⟩

end Mettapedia.Languages.MeTTa.PureKernel.Confluence
