import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Parallel

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction

/-- Parallel one-step reduction for the two-sort kernel. -/
inductive ParRed : ScopedTerm n → ScopedTerm n → Prop where
  | var (i : Fin n) : ParRed (.var i) (.var i)
  | const (c : DeclName) : ParRed (.const c : ScopedTerm n) (.const c)
  | u0 : ParRed (.u0 : ScopedTerm n) .u0
  | u1 : ParRed (.u1 : ScopedTerm n) .u1
  | pi {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)} :
      ParRed A A' → ParRed B B' → ParRed (.pi A B) (.pi A' B')
  | sigma {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)} :
      ParRed A A' → ParRed B B' → ParRed (.sigma A B) (.sigma A' B')
  | id {A A' a a' b b' : ScopedTerm n} :
      ParRed A A' → ParRed a a' → ParRed b b' → ParRed (.id A a b) (.id A' a' b')
  | lam {b b' : ScopedTerm (n + 1)} :
      ParRed b b' → ParRed (.lam b) (.lam b')
  | app {f f' a a' : ScopedTerm n} :
      ParRed f f' → ParRed a a' → ParRed (.app f a) (.app f' a')
  | pair {a a' b b' : ScopedTerm n} :
      ParRed a a' → ParRed b b' → ParRed (.pair a b) (.pair a' b')
  | fst {p p' : ScopedTerm n} :
      ParRed p p' → ParRed (.fst p) (.fst p')
  | snd {p p' : ScopedTerm n} :
      ParRed p p' → ParRed (.snd p) (.snd p')
  | refl {a a' : ScopedTerm n} :
      ParRed a a' → ParRed (.refl a) (.refl a')
  | betaPi {body body' : ScopedTerm (n + 1)} {a a' : ScopedTerm n} :
      ParRed body body' → ParRed a a' →
      ParRed (.app (.lam body) a) (inst0 a' body')
  | betaSigmaFst {a a' b b' : ScopedTerm n} :
      ParRed a a' → ParRed b b' →
      ParRed (.fst (.pair a b)) a'
  | betaSigmaSnd {a a' b b' : ScopedTerm n} :
      ParRed a a' → ParRed b b' →
      ParRed (.snd (.pair a b)) b'

@[simp] theorem par_refl : ∀ t : ScopedTerm n, ParRed t t := by
  intro t
  induction t with
  | var i => exact .var i
  | const c => exact .const c
  | u0 => exact .u0
  | u1 => exact .u1
  | pi A B ihA ihB => exact .pi ihA ihB
  | sigma A B ihA ihB => exact .sigma ihA ihB
  | id A a b ihA iha ihb => exact .id ihA iha ihb
  | lam b ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | pair a b iha ihb => exact .pair iha ihb
  | fst p ih => exact .fst ih
  | snd p ih => exact .snd ih
  | refl a iha => exact .refl iha

theorem red_to_par {t u : ScopedTerm n} (h : Red t u) : ParRed t u := by
  induction h with
  | betaPi body a =>
      exact .betaPi (par_refl body) (par_refl a)
  | betaSigmaFst a b =>
      exact .betaSigmaFst (par_refl a) (par_refl b)
  | betaSigmaSnd a b =>
      exact .betaSigmaSnd (par_refl a) (par_refl b)
  | congPiDom h ih =>
      exact .pi ih (par_refl _)
  | congPiCod h ih =>
      exact .pi (par_refl _) ih
  | congSigmaDom h ih =>
      exact .sigma ih (par_refl _)
  | congSigmaCod h ih =>
      exact .sigma (par_refl _) ih
  | congIdTy h ih =>
      exact .id ih (par_refl _) (par_refl _)
  | congIdLeft h ih =>
      exact .id (par_refl _) ih (par_refl _)
  | congIdRight h ih =>
      exact .id (par_refl _) (par_refl _) ih
  | congLam h ih =>
      exact .lam ih
  | congAppFun h ih =>
      exact .app ih (par_refl _)
  | congAppArg h ih =>
      exact .app (par_refl _) ih
  | congPairFst h ih =>
      exact .pair ih (par_refl _)
  | congPairSnd h ih =>
      exact .pair (par_refl _) ih
  | congFst h ih =>
      exact .fst ih
  | congSnd h ih =>
      exact .snd ih
  | congRefl h ih =>
      exact .refl ih

theorem par_rename {n m : Nat} (ρ : Ren n m) {t u : ScopedTerm n}
    (h : ParRed t u) : ParRed (rename ρ t) (rename ρ u) := by
  induction h generalizing m with
  | var i =>
      exact .var (ρ i)
  | const c =>
      exact .const c
  | u0 =>
      exact .u0
  | u1 =>
      exact .u1
  | pi hA hB ihA ihB =>
      simpa [rename] using .pi (ihA (ρ := ρ)) (ihB (ρ := liftRen ρ))
  | sigma hA hB ihA ihB =>
      simpa [rename] using .sigma (ihA (ρ := ρ)) (ihB (ρ := liftRen ρ))
  | id hA ha hb ihA iha ihb =>
      simpa [rename] using .id (ihA (ρ := ρ)) (iha (ρ := ρ)) (ihb (ρ := ρ))
  | lam hb ih =>
      simpa [rename] using .lam (ih (ρ := liftRen ρ))
  | app hf ha ihf iha =>
      simpa [rename] using .app (ihf (ρ := ρ)) (iha (ρ := ρ))
  | pair ha hb iha ihb =>
      simpa [rename] using .pair (iha (ρ := ρ)) (ihb (ρ := ρ))
  | fst hp ih =>
      simpa [rename] using .fst (ih (ρ := ρ))
  | snd hp ih =>
      simpa [rename] using .snd (ih (ρ := ρ))
  | refl ha ih =>
      simpa [rename] using .refl (ih (ρ := ρ))
  | betaPi hbody ha ihbody iha =>
      simpa [rename, rename_inst0] using
        (ParRed.betaPi (ihbody (ρ := liftRen ρ)) (iha (ρ := ρ)))
  | betaSigmaFst ha hb iha ihb =>
      simpa [rename] using
        (ParRed.betaSigmaFst (iha (ρ := ρ)) (ihb (ρ := ρ)))
  | betaSigmaSnd ha hb iha ihb =>
      simpa [rename] using
        (ParRed.betaSigmaSnd (iha (ρ := ρ)) (ihb (ρ := ρ)))

theorem par_subst {n m : Nat} {σ σ' : Sub n m}
    (hσ : ∀ i, ParRed (σ i) (σ' i))
    {t u : ScopedTerm n} (h : ParRed t u) :
    ParRed (subst σ t) (subst σ' u) := by
  induction h generalizing m with
  | var i =>
      exact hσ i
  | const c =>
      exact .const c
  | u0 =>
      exact .u0
  | u1 =>
      exact .u1
  | pi hA hB ihA ihB =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst] using .pi (ihA hσ) (ihB hσlift)
  | sigma hA hB ihA ihB =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst] using .sigma (ihA hσ) (ihB hσlift)
  | id hA ha hb ihA iha ihb =>
      simpa [subst] using .id (ihA hσ) (iha hσ) (ihb hσ)
  | lam hb ih =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst] using .lam (ih hσlift)
  | app hf ha ihf iha =>
      simpa [subst] using .app (ihf hσ) (iha hσ)
  | pair ha hb iha ihb =>
      simpa [subst] using .pair (iha hσ) (ihb hσ)
  | fst hp ih =>
      simpa [subst] using .fst (ih hσ)
  | snd hp ih =>
      simpa [subst] using .snd (ih hσ)
  | refl ha ih =>
      simpa [subst] using .refl (ih hσ)
  | betaPi hbody ha ihbody iha =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst, subst_inst0] using (ParRed.betaPi (ihbody hσlift) (iha hσ))
  | betaSigmaFst ha hb iha ihb =>
      simpa [subst] using (ParRed.betaSigmaFst (iha hσ) (ihb hσ))
  | betaSigmaSnd ha hb iha ihb =>
      simpa [subst] using (ParRed.betaSigmaSnd (iha hσ) (ihb hσ))

theorem par_inst0 {a a' : ScopedTerm n} {b b' : ScopedTerm (n + 1)}
    (ha : ParRed a a') (hb : ParRed b b') :
    ParRed (inst0 a b) (inst0 a' b') := by
  have hσ : ∀ i, ParRed (subst0 a i) (subst0 a' i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using ha
    · intro j
      exact .var j
  simpa [inst0] using (par_subst (σ := subst0 a) (σ' := subst0 a') hσ hb)

theorem par_to_redStar {t u : ScopedTerm n} (h : ParRed t u) : RedStar t u := by
  induction h with
  | var i =>
      exact .refl _
  | const c =>
      exact .refl _
  | u0 =>
      exact .refl _
  | u1 =>
      exact .refl _
  | pi hA hB ihA ihB =>
      exact .trans (.congPiDom ihA) (.congPiCod ihB)
  | sigma hA hB ihA ihB =>
      exact .trans (.congSigmaDom ihA) (.congSigmaCod ihB)
  | id hA ha hb ihA iha ihb =>
      exact .trans
        (.trans
          (RedStar.map (F := fun t => .id t _ _) (fun hstep => .congIdTy hstep) ihA)
          (RedStar.map (F := fun t => .id _ t _) (fun hstep => .congIdLeft hstep) iha))
        (RedStar.map (F := fun t => .id _ _ t) (fun hstep => .congIdRight hstep) ihb)
  | lam hb ih =>
      exact .congLam ih
  | app hf ha ihf iha =>
      exact .trans (.congAppFun ihf) (.congAppArg iha)
  | pair ha hb iha ihb =>
      exact .trans (.congPairFst iha) (.congPairSnd ihb)
  | fst hp ih =>
      exact .congFst ih
  | snd hp ih =>
      exact .congSnd ih
  | refl ha iha =>
      exact .congRefl iha
  | betaPi hb ha ihb iha =>
      exact .trans
        (.trans
          (.congAppFun (.congLam ihb))
          (.congAppArg iha))
        (red_to_redStar (.betaPi _ _))
  | betaSigmaFst ha hb iha ihb =>
      exact .trans
        (.trans
          (.congFst (.congPairFst iha))
          (.congFst (.congPairSnd ihb)))
        (red_to_redStar (.betaSigmaFst _ _))
  | betaSigmaSnd ha hb iha ihb =>
      exact .trans
        (.trans
          (.congSnd (.congPairFst iha))
          (.congSnd (.congPairSnd ihb)))
        (red_to_redStar (.betaSigmaSnd _ _))

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Parallel
