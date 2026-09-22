import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Legacy-to-tower preservation and conservativity boundary

This module first proves that the named `Legacy` presentation is an exact
re-presentation of the existing sealed `TwoSortPiSigmaId` grammar and typing
judgment.  It then transports legacy derivations into the cumulative tower.
No old occurrence of `u0` is interpreted as a universe: it remains the opaque
`legacyGround`, whose type is `U 0`.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Legacy

/-! ## Exact correspondence with the existing sealed grammar -/

/-- The old and shared definitions of lifting a renaming are extensionally
the same. -/
theorem old_liftRen_eq
    (ρ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.Ren n m) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.liftRen ρ =
      liftRen ρ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Re-presentation commutes with old term-variable renaming. -/
@[simp] theorem ofTwoSort_rename
    (ρ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.Ren n m)
    (t : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n) :
    ofTwoSort (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename ρ t) =
      rename ρ (ofTwoSort t) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | u0 => rfl
  | u1 => rfl
  | pi A B ihA ihB => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ihA, ihB, old_liftRen_eq]
  | sigma A B ihA ihB => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ihA, ihB, old_liftRen_eq]
  | id A a b ihA iha ihb => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ihA, iha, ihb]
  | lam body ih => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ih, old_liftRen_eq]
  | app g a ihg iha => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ihg, iha]
  | pair a b iha ihb => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, iha, ihb]
  | fst p ih => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ih]
  | snd p ih => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ih]
  | refl a ih => simp only [
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename, ofTwoSort,
      rename, ih]

/-- Mapping an old substitution across the presentation commutes with
lifting it under a binder. -/
theorem ofTwoSort_liftSub
    (σ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m) :
    (fun i => ofTwoSort
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.liftSub σ i)) =
      liftSub (fun i => ofTwoSort (σ i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact ofTwoSort_rename
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk (σ j)

/-- Re-presentation commutes with simultaneous substitution. -/
@[simp] theorem ofTwoSort_subst
    (σ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.Sub n m)
    (t : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n) :
    ofTwoSort (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst σ t) =
      subst (fun i => ofTwoSort (σ i)) (ofTwoSort t) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | u0 => rfl
  | u1 => rfl
  | pi A B ihA ihB =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ihA, ihB, ofTwoSort_liftSub]
  | sigma A B ihA ihB =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ihA, ihB, ofTwoSort_liftSub]
  | id A a b ihA iha ihb =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ihA, iha, ihb]
  | lam body ih =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ih, ofTwoSort_liftSub]
  | app g a ihg iha =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ihg, iha]
  | pair a b iha ihb =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, iha, ihb]
  | fst p ih =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ih]
  | snd p ih =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ih]
  | refl a ih =>
      simp only [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.subst,
        ofTwoSort, subst, ih]

@[simp] theorem ofTwoSort_inst0
    (u : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n)
    (body : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm (n + 1)) :
    ofTwoSort (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.inst0 u body) =
      inst0 (ofTwoSort u) (ofTwoSort body) := by
  rw [Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.inst0,
    inst0, ofTwoSort_subst]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Translate old telescope contexts into the explicitly named legacy
presentation. -/
def ofTwoSortCtx :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx n → Legacy.Ctx n
  | .nil => .nil
  | .snoc Γ A => .snoc (ofTwoSortCtx Γ) (ofTwoSort A)

/-- Inverse context translation. -/
def toTwoSortCtx : Legacy.Ctx n →
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx n
  | .nil => .nil
  | .snoc Γ A => .snoc (toTwoSortCtx Γ) (toTwoSort A)

@[simp] theorem toTwoSortCtx_ofTwoSortCtx
    (Γ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx n) :
    toTwoSortCtx (ofTwoSortCtx Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp only [ofTwoSortCtx, toTwoSortCtx, ih, toTwoSort_ofTwoSort]

@[simp] theorem ofTwoSortCtx_toTwoSortCtx (Γ : Legacy.Ctx n) :
    ofTwoSortCtx (toTwoSortCtx Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp only [toTwoSortCtx, ofTwoSortCtx, ih, ofTwoSort_toTwoSort]

/-- Old and re-presented context lookup agree exactly. -/
@[simp] theorem lookup_ofTwoSortCtx
    (Γ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx n)
    (i : Fin n) :
    Ctx.lookup (ofTwoSortCtx Γ) i = ofTwoSort
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup Γ i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A ih =>
      refine Fin.cases ?_ ?_ i
      · exact (ofTwoSort_rename
          Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk A).symm
      · intro j
        change rename wk (Ctx.lookup (ofTwoSortCtx Γ) j) =
          ofTwoSort (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.rename
            Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk
            (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup Γ j))
        rw [ih]
        exact (ofTwoSort_rename
          Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming.wk
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup Γ j)).symm

/-- The inverse lookup square. -/
@[simp] theorem lookup_toTwoSortCtx (Γ : Legacy.Ctx n) (i : Fin n) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup (toTwoSortCtx Γ) i =
      toTwoSort (Ctx.lookup Γ i) := by
  have h := lookup_ofTwoSortCtx (toTwoSortCtx Γ) i
  rw [ofTwoSortCtx_toTwoSortCtx] at h
  calc
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup (toTwoSortCtx Γ) i =
        toTwoSort (ofTwoSort
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.lookup
            (toTwoSortCtx Γ) i)) := (toTwoSort_ofTwoSort _).symm
    _ = toTwoSort (Ctx.lookup Γ i) := congrArg toTwoSort h.symm

/-! ### Conversion correspondence -/

/-- Every old beta/congruence step has the corresponding legacy step. -/
theorem step_of_oldRed {t u :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n}
    (h : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red t u) :
    Step HeadEq (ofTwoSort t) (ofTwoSort u) := by
  induction h with
  | betaPi body a =>
      simpa only [ofTwoSort, ofTwoSort_inst0] using
        Step.betaPi (ofTwoSort body) (ofTwoSort a)
  | betaSigmaFst a b => exact .betaSigmaFst (ofTwoSort a) (ofTwoSort b)
  | betaSigmaSnd a b => exact .betaSigmaSnd (ofTwoSort a) (ofTwoSort b)
  | congPiDom h ih => exact .congPiDom ih
  | congPiCod h ih => exact .congPiCod ih
  | congSigmaDom h ih => exact .congSigmaDom ih
  | congSigmaCod h ih => exact .congSigmaCod ih
  | congIdTy h ih => exact .congIdTy ih
  | congIdLeft h ih => exact .congIdLeft ih
  | congIdRight h ih => exact .congIdRight ih
  | congLam h ih => exact .congLam ih
  | congAppFun h ih => exact .congAppFun ih
  | congAppArg h ih => exact .congAppArg ih
  | congPairFst h ih => exact .congPairFst ih
  | congPairSnd h ih => exact .congPairSnd ih
  | congFst h ih => exact .congFst ih
  | congSnd h ih => exact .congSnd ih
  | congRefl h ih => exact .congRefl ih

/-- Old conversion is preserved by exact re-presentation. -/
theorem conv_of_oldConv {t u :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n}
    (h : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv t u) :
    Conv HeadEq (ofTwoSort t) (ofTwoSort u) := by
  induction h with
  | rel x y hred => exact .rel _ _ (step_of_oldRed hred)
  | refl x => exact .refl _
  | symm x y hxy ih => exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact .trans _ _ _ ihxy ihyz

/-- The inverse translation commutes with opening a binder. -/
@[simp] theorem toTwoSort_inst0 (u : Legacy.Tm n) (body : Legacy.Tm (n + 1)) :
    toTwoSort (inst0 u body) =
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.inst0
        (toTwoSort u) (toTwoSort body) := by
  apply Function.LeftInverse.injective (fun t => toTwoSort_ofTwoSort t)
  simp only [ofTwoSort_toTwoSort, ofTwoSort_inst0]

/-- Old conversion is closed under any old reduction-compatible context. -/
private theorem oldConv_map
    {F : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n →
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm m}
    (hF : ∀ {left right},
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red left right →
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red (F left) (F right))
    {left right : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n}
    (h : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv left right) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv (F left) (F right) := by
  induction h with
  | rel x y hred =>
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.red_implies_conv
        (hF hred)
  | refl x => exact .refl _
  | symm x y hxy ih => exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact .trans _ _ _ ihxy ihyz

/-- Mapping a legacy step back gives an old conversion.  Reflexive head
steps map to conversion reflexivity rather than to a fake reduction. -/
theorem oldConv_of_step {t u : Legacy.Tm n} (h : Step HeadEq t u) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv (toTwoSort t) (toTwoSort u) := by
  induction h with
  | betaPi body a =>
      simpa only [toTwoSort, toTwoSort_inst0] using
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.red_implies_conv
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red.betaPi
            (toTwoSort body) (toTwoSort a)))
  | betaSigmaFst a b =>
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.red_implies_conv
        (.betaSigmaFst (toTwoSort a) (toTwoSort b))
  | betaSigmaSnd a b =>
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.red_implies_conv
        (.betaSigmaSnd (toTwoSort a) (toTwoSort b))
  | head hEq =>
      subst hEq
      exact .refl _
  | root impossible => exact False.elim impossible
  | congPiDom h ih =>
      exact oldConv_map (F := fun term => .pi term _)
        (fun hred => .congPiDom hred) ih
  | congPiCod h ih =>
      exact oldConv_map (F := fun term => .pi _ term)
        (fun hred => .congPiCod hred) ih
  | congSigmaDom h ih =>
      exact oldConv_map (F := fun term => .sigma term _)
        (fun hred => .congSigmaDom hred) ih
  | congSigmaCod h ih =>
      exact oldConv_map (F := fun term => .sigma _ term)
        (fun hred => .congSigmaCod hred) ih
  | congIdTy h ih =>
      exact oldConv_map (F := fun term => .id term _ _)
        (fun hred => .congIdTy hred) ih
  | congIdLeft h ih =>
      exact oldConv_map (F := fun term => .id _ term _)
        (fun hred => .congIdLeft hred) ih
  | congIdRight h ih =>
      exact oldConv_map (F := fun term => .id _ _ term)
        (fun hred => .congIdRight hred) ih
  | congLam h ih =>
      exact oldConv_map (F := fun term => .lam term)
        (fun hred => .congLam hred) ih
  | congAppFun h ih =>
      exact oldConv_map (F := fun term => .app term _)
        (fun hred => .congAppFun hred) ih
  | congAppArg h ih =>
      exact oldConv_map (F := fun term => .app _ term)
        (fun hred => .congAppArg hred) ih
  | congPairFst h ih =>
      exact oldConv_map (F := fun term => .pair term _)
        (fun hred => .congPairFst hred) ih
  | congPairSnd h ih =>
      exact oldConv_map (F := fun term => .pair _ term)
        (fun hred => .congPairSnd hred) ih
  | congFst h ih =>
      exact oldConv_map (F := fun term => .fst term)
        (fun hred => .congFst hred) ih
  | congSnd h ih =>
      exact oldConv_map (F := fun term => .snd term)
        (fun hred => .congSnd hred) ih
  | congRefl h ih =>
      exact oldConv_map (F := fun term => .refl term)
        (fun hred => .congRefl hred) ih

/-- Legacy conversion reflects to the existing sealed conversion relation. -/
theorem oldConv_of_conv {t u : Legacy.Tm n} (h : Conv HeadEq t u) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv (toTwoSort t) (toTwoSort u) := by
  induction h with
  | rel x y hstep => exact oldConv_of_step hstep
  | refl x => exact .refl _
  | symm x y hxy ih => exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact .trans _ _ _ ihxy ihyz

/-! ### Typing correspondence -/

/-- Every existing sealed typing derivation has an exact derivation in the
named Legacy presentation. -/
theorem hasType_of_oldHasType
    {Γ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx n}
    {t A : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n}
    (h : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A) :
    Legacy.HasType (ofTwoSortCtx Γ) (ofTwoSort t) (ofTwoSort A) := by
  induction h with
  | u0_type Γ => exact .headType .groundMarker
  | @var n Γ i =>
      simpa only [ofTwoSort, lookup_ofTwoSortCtx] using
        (Presentation.HasType.var (R := rules) (Γ := ofTwoSortCtx Γ) i)
  | pi_form hA hB ihA ihB =>
      exact .piForm ihA .marker ihB .marker .marker
  | sigma_form hA hB ihA ihB =>
      exact .sigmaForm ihA .marker ihB .marker .marker
  | lam_intro hBody ihBody => exact .lamIntro ihBody
  | app_elim hg ha ihg iha =>
      simpa only [ofTwoSort, ofTwoSort_inst0] using
        (Presentation.HasType.appElim ihg iha)
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      have ihb' : Legacy.HasType (ofTwoSortCtx Γ) (ofTwoSort b)
          (inst0 (ofTwoSort a) (ofTwoSort B)) := by
        simpa only [ofTwoSort_inst0] using ihb
      exact Presentation.HasType.pairIntro iha ihb'
  | fst_elim hp ihp => exact .fstElim ihp
  | snd_elim hp ihp =>
      simpa only [ofTwoSort, ofTwoSort_inst0] using
        (Presentation.HasType.sndElim ihp)
  | id_form hA ha hb ihA iha ihb =>
      exact .idForm ihA .marker iha ihb
  | refl_intro ha iha => exact .reflIntro iha
  | conv ht hAB iht => exact .conv iht (conv_of_oldConv hAB)

/-- Every Legacy derivation maps back to the existing sealed judgment. -/
theorem oldHasType_of_hasType {Γ : Legacy.Ctx n} {t A : Legacy.Tm n}
    (h : Legacy.HasType Γ t A) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType
      (toTwoSortCtx Γ) (toTwoSort t) (toTwoSort A) := by
  induction h with
  | headType hHead =>
      cases hHead
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.u0_type _
  | @var n Γ i =>
      simpa only [toTwoSort, lookup_toTwoSortCtx] using
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.var
          (Γ := toTwoSortCtx Γ) i)
  | const impossible => simp [Legacy.rules] at impossible
  | piForm hA hu hB hv hj ihA ihB =>
      cases hu
      cases hv
      cases hj
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.pi_form
        ihA ihB
  | sigmaForm hA hu hB hv hj ihA ihB =>
      cases hu
      cases hv
      cases hj
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.sigma_form
        ihA ihB
  | lamIntro hBody ihBody =>
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.lam_intro
        ihBody
  | appElim hg ha ihg iha =>
      simpa only [toTwoSort, toTwoSort_inst0] using
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.app_elim
          ihg iha)
  | @pairIntro n Γ a b A B ha hb iha ihb =>
      have ihb' : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType
          (toTwoSortCtx Γ) (toTwoSort b)
          (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution.inst0
            (toTwoSort a) (toTwoSort B)) := by
        simpa only [toTwoSort_inst0] using ihb
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.pair_intro
        iha ihb'
  | fstElim hp ihp =>
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.fst_elim ihp
  | sndElim hp ihp =>
      simpa only [toTwoSort, toTwoSort_inst0] using
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.snd_elim ihp)
  | idForm hA hu ha hb ihA iha ihb =>
      cases hu
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.id_form
        ihA iha ihb
  | reflIntro ha iha =>
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.refl_intro iha
  | cumul ht hFalse iht => exact False.elim hFalse
  | conv ht hAB iht =>
      exact Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType.conv
        iht (oldConv_of_conv hAB)

/-- **Exact old-grammar theorem.** The named Legacy presentation neither
loses nor adds any judgment of the existing sealed kernel. -/
theorem old_hasType_iff
    (Γ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx n)
    (t A : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A ↔
      Legacy.HasType (ofTwoSortCtx Γ) (ofTwoSort t) (ofTwoSort A) := by
  constructor
  · exact hasType_of_oldHasType
  · intro h
    simpa using oldHasType_of_hasType h

end Legacy

/-! ## Sound embedding into the tower -/

namespace Legacy

/-- Legacy head equality is respected by the migration map. -/
theorem towerHeadEq_of_headEq {left right : Legacy.Head}
    (h : Legacy.HeadEq left right) :
    Tower.HeadEq left.embed right.embed := by
  subst right
  cases left <;>
    simp [Legacy.Head.embed, Tower.HeadEq, Tower.zero,
      Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval]

/-- Every legacy computation/equality generator maps to a tower generator. -/
theorem towerStep_of_step {left right : Legacy.Tm n}
    (h : Step Legacy.HeadEq left right) :
    Step Tower.HeadEq (embed left) (embed right) := by
  induction h with
  | betaPi body a =>
      simpa only [embed, Tm.mapHead, Tm.mapHead_inst0] using
        Step.betaPi (embed body) (embed a)
  | betaSigmaFst a b => exact .betaSigmaFst (embed a) (embed b)
  | betaSigmaSnd a b => exact .betaSigmaSnd (embed a) (embed b)
  | head hEq => exact .head (towerHeadEq_of_headEq hEq)
  | root impossible => exact False.elim impossible
  | congPiDom h ih => exact .congPiDom ih
  | congPiCod h ih => exact .congPiCod ih
  | congSigmaDom h ih => exact .congSigmaDom ih
  | congSigmaCod h ih => exact .congSigmaCod ih
  | congIdTy h ih => exact .congIdTy ih
  | congIdLeft h ih => exact .congIdLeft ih
  | congIdRight h ih => exact .congIdRight ih
  | congLam h ih => exact .congLam ih
  | congAppFun h ih => exact .congAppFun ih
  | congAppArg h ih => exact .congAppArg ih
  | congPairFst h ih => exact .congPairFst ih
  | congPairSnd h ih => exact .congPairSnd ih
  | congFst h ih => exact .congFst ih
  | congSnd h ih => exact .congSnd ih
  | congRefl h ih => exact .congRefl ih

/-- Legacy conversion is preserved by the migration map. -/
theorem towerConv_of_conv {left right : Legacy.Tm n}
    (h : Conv Legacy.HeadEq left right) :
    Conv Tower.HeadEq (embed left) (embed right) := by
  induction h with
  | rel x y hstep => exact .rel _ _ (towerStep_of_step hstep)
  | refl x => exact .refl _
  | symm x y hxy ih => exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact .trans _ _ _ ihxy ihyz

/-- Forgetting levels maps every Tower head equality to Legacy head
equality.  This direction intentionally forgets whether a sort was above
level zero; it is a conversion projection, not a typing projection. -/
theorem headEq_of_towerHeadEq {left right : Tower.Head}
    (h : Tower.HeadEq left right) :
    Legacy.HeadEq left.forget right.forget := by
  cases left <;> cases right <;>
    simp [Tower.HeadEq, Tower.Head.forget, Legacy.HeadEq] at h ⊢

/-- Tower conversion generators project to Legacy conversion generators
after level erasure. -/
theorem step_of_towerStep {left right : Tower.Tm n}
    (h : Step Tower.HeadEq left right) :
    Step Legacy.HeadEq (forget left) (forget right) := by
  induction h with
  | betaPi body a =>
      simpa only [forget, Tm.mapHead, Tm.mapHead_inst0] using
        Step.betaPi (forget body) (forget a)
  | betaSigmaFst a b => exact .betaSigmaFst (forget a) (forget b)
  | betaSigmaSnd a b => exact .betaSigmaSnd (forget a) (forget b)
  | head hEq => exact .head (headEq_of_towerHeadEq hEq)
  | root impossible => exact False.elim impossible
  | congPiDom h ih => exact .congPiDom ih
  | congPiCod h ih => exact .congPiCod ih
  | congSigmaDom h ih => exact .congSigmaDom ih
  | congSigmaCod h ih => exact .congSigmaCod ih
  | congIdTy h ih => exact .congIdTy ih
  | congIdLeft h ih => exact .congIdLeft ih
  | congIdRight h ih => exact .congIdRight ih
  | congLam h ih => exact .congLam ih
  | congAppFun h ih => exact .congAppFun ih
  | congAppArg h ih => exact .congAppArg ih
  | congPairFst h ih => exact .congPairFst ih
  | congPairSnd h ih => exact .congPairSnd ih
  | congFst h ih => exact .congFst ih
  | congSnd h ih => exact .congSnd ih
  | congRefl h ih => exact .congRefl ih

/-- Every Tower conversion projects to a Legacy conversion. -/
theorem conv_of_towerConv {left right : Tower.Tm n}
    (h : Conv Tower.HeadEq left right) :
    Conv Legacy.HeadEq (forget left) (forget right) := by
  induction h with
  | rel x y hstep => exact .rel _ _ (step_of_towerStep hstep)
  | refl x => exact .refl _
  | symm x y hxy ih => exact .symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact .trans _ _ _ ihxy ihyz

/-- **Conversion conservativity on the exact legacy image.** -/
theorem conv_iff_towerConv (left right : Legacy.Tm n) :
    Conv Legacy.HeadEq left right ↔
      Conv Tower.HeadEq (embed left) (embed right) := by
  constructor
  · exact towerConv_of_conv
  · intro h
    simpa using conv_of_towerConv h

/-- At level zero the Tower formation join is convertible back to `U 0`. -/
theorem tower_zero_join_headEq :
    Tower.HeadEq
      (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero) := by
  intro v
  simp [Tower.zero,
    Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval]

theorem towerZeroJoinConv : Conv Tower.HeadEq
    (.head (.sort (.max Tower.zero Tower.zero)) : Tower.Tm n)
    (.head (.sort Tower.zero) : Tower.Tm n) :=
  .rel _ _ (.head tower_zero_join_headEq)

/-- **Legacy sound embedding.** Every derivation of the explicitly sealed
presentation transports to the cumulative tower. -/
theorem towerHasType_of_hasType {Γ : Legacy.Ctx n} {t A : Legacy.Tm n}
    (h : Legacy.HasType Γ t A) :
    Tower.HasType (embedCtx Γ) (embed t) (embed A) := by
  induction h with
  | headType hHead =>
      cases hHead
      exact .headType .legacyGround
  | @var n Γ i =>
      simpa only [embed, embedCtx, Tm.mapHead,
        Presentation.Ctx.lookup_mapHead] using
        (Presentation.HasType.var (R := Tower.rules) (Γ := embedCtx Γ) i)
  | const impossible => simp [Legacy.rules] at impossible
  | @piForm n Γ A B u v w hA hu hB hv hj ihA ihB =>
      cases hu
      cases hv
      cases hj
      have hPi : Tower.HasType (embedCtx Γ)
          (.pi (embed _) (embed _))
          (.head (.sort (.max Tower.zero Tower.zero))) :=
        .piForm ihA (.sort Tower.zero) ihB (.sort Tower.zero)
          (.sorts Tower.zero Tower.zero)
      simpa only [embed, Tm.mapHead, Legacy.Head.embed] using
        (Presentation.HasType.conv hPi towerZeroJoinConv)
  | @sigmaForm n Γ A B u v w hA hu hB hv hj ihA ihB =>
      cases hu
      cases hv
      cases hj
      have hSigma : Tower.HasType (embedCtx Γ)
          (.sigma (embed _) (embed _))
          (.head (.sort (.max Tower.zero Tower.zero))) :=
        .sigmaForm ihA (.sort Tower.zero) ihB (.sort Tower.zero)
          (.sorts Tower.zero Tower.zero)
      simpa only [embed, Tm.mapHead, Legacy.Head.embed] using
        (Presentation.HasType.conv hSigma towerZeroJoinConv)
  | lamIntro hBody ihBody => exact .lamIntro ihBody
  | appElim hg ha ihg iha =>
      simpa only [embed, Tm.mapHead, Tm.mapHead_inst0] using
        (Presentation.HasType.appElim ihg iha)
  | @pairIntro n Γ a b A B ha hb iha ihb =>
      have ihb' : Tower.HasType (embedCtx Γ) (embed b)
          (inst0 (embed a) (embed B)) := by
        simpa only [embed, Tm.mapHead_inst0] using ihb
      exact Presentation.HasType.pairIntro iha ihb'
  | fstElim hp ihp => exact .fstElim ihp
  | sndElim hp ihp =>
      simpa only [embed, Tm.mapHead, Tm.mapHead_inst0] using
        (Presentation.HasType.sndElim ihp)
  | idForm hA hu ha hb ihA iha ihb =>
      cases hu
      exact .idForm ihA (.sort Tower.zero) iha ihb
  | reflIntro ha iha => exact .reflIntro iha
  | cumul ht hFalse iht => exact False.elim hFalse
  | conv ht hAB iht => exact .conv iht (towerConv_of_conv hAB)

/-- Direct old-kernel corollary of the sound embedding theorem. -/
theorem towerHasType_of_oldHasType
    {Γ : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context.Ctx n}
    {t A : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n}
    (h : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.HasType Γ t A) :
    Tower.HasType (embedCtx (ofTwoSortCtx Γ))
      (embed (ofTwoSort t)) (embed (ofTwoSort A)) :=
  towerHasType_of_hasType (hasType_of_oldHasType h)

end Legacy

/-! ## The exact conservative subcalculus inside Tower

The unrestricted tower has one genuinely new formation rule:
`U l : U (succ l)`.  The migration interface below is the largest direct
rule-subset obtained by omitting precisely that rule while retaining tower
levels, joins, cumulativity, computation, and conversion.  It is useful both
as an executable compatibility boundary and as an honest statement of what
has been proved: unrestricted judgment reflection still requires a separate
normalization/conservativity argument; it is not smuggled in by notation. -/

namespace Tower

/-- Tower typing with the universe-successor formation rule omitted.  The
opaque legacy ground rule remains, so this is a genuine Tower subjudgment,
not a definition in terms of Legacy typing. -/
inductive SealedHasType : Tower.Ctx n → Tower.Tm n → Tower.Tm n → Prop where
  | legacyGround (Γ : Tower.Ctx n) :
      SealedHasType Γ (.head .legacyGround) (.head (.sort Tower.zero))
  | var {Γ : Tower.Ctx n} (i : Fin n) :
      SealedHasType Γ (.var i) (Ctx.lookup Γ i)
  | piForm {Γ : Tower.Ctx n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
      {u v w : Tower.Head} :
      SealedHasType Γ A (.head u) → Tower.IsUniverse u →
      SealedHasType (.snoc Γ A) B (.head v) → Tower.IsUniverse v →
      Tower.Join u v w →
      SealedHasType Γ (.pi A B) (.head w)
  | sigmaForm {Γ : Tower.Ctx n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
      {u v w : Tower.Head} :
      SealedHasType Γ A (.head u) → Tower.IsUniverse u →
      SealedHasType (.snoc Γ A) B (.head v) → Tower.IsUniverse v →
      Tower.Join u v w →
      SealedHasType Γ (.sigma A B) (.head w)
  | lamIntro {Γ : Tower.Ctx n} {A : Tower.Tm n}
      {body B : Tower.Tm (n + 1)} :
      SealedHasType (.snoc Γ A) body B →
      SealedHasType Γ (.lam body) (.pi A B)
  | appElim {Γ : Tower.Ctx n} {g a A : Tower.Tm n}
      {B : Tower.Tm (n + 1)} :
      SealedHasType Γ g (.pi A B) → SealedHasType Γ a A →
      SealedHasType Γ (.app g a) (inst0 a B)
  | pairIntro {Γ : Tower.Ctx n} {a b A : Tower.Tm n}
      {B : Tower.Tm (n + 1)} :
      SealedHasType Γ a A → SealedHasType Γ b (inst0 a B) →
      SealedHasType Γ (.pair a b) (.sigma A B)
  | fstElim {Γ : Tower.Ctx n} {p A : Tower.Tm n}
      {B : Tower.Tm (n + 1)} :
      SealedHasType Γ p (.sigma A B) → SealedHasType Γ (.fst p) A
  | sndElim {Γ : Tower.Ctx n} {p A : Tower.Tm n}
      {B : Tower.Tm (n + 1)} :
      SealedHasType Γ p (.sigma A B) →
      SealedHasType Γ (.snd p) (inst0 (.fst p) B)
  | idForm {Γ : Tower.Ctx n} {A a b : Tower.Tm n} {u : Tower.Head} :
      SealedHasType Γ A (.head u) → Tower.IsUniverse u →
      SealedHasType Γ a A → SealedHasType Γ b A →
      SealedHasType Γ (.id A a b) (.head u)
  | reflIntro {Γ : Tower.Ctx n} {a A : Tower.Tm n} :
      SealedHasType Γ a A → SealedHasType Γ (.refl a) (.id A a a)
  | cumul {Γ : Tower.Ctx n} {t : Tower.Tm n} {u v : Tower.Head} :
      SealedHasType Γ t (.head u) → Tower.Cumulative u v →
      SealedHasType Γ t (.head v)
  | conv {Γ : Tower.Ctx n} {t A B : Tower.Tm n} :
      SealedHasType Γ t A → Conv Tower.HeadEq A B →
      SealedHasType Γ t B

/-- The sealed migration lane is a literal rule-subset of Tower typing. -/
theorem SealedHasType.toHasType {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (h : SealedHasType Γ t A) : Tower.HasType Γ t A := by
  induction h with
  | legacyGround Γ => exact .headType .legacyGround
  | var i => exact .var i
  | piForm hA hu hB hv hj ihA ihB => exact .piForm ihA hu ihB hv hj
  | sigmaForm hA hu hB hv hj ihA ihB => exact .sigmaForm ihA hu ihB hv hj
  | lamIntro hBody ihBody => exact .lamIntro ihBody
  | appElim hg ha ihg iha => exact .appElim ihg iha
  | pairIntro ha hb iha ihb => exact .pairIntro iha ihb
  | fstElim hp ihp => exact .fstElim ihp
  | sndElim hp ihp => exact .sndElim ihp
  | idForm hA hu ha hb ihA iha ihb => exact .idForm ihA hu iha ihb
  | reflIntro ha iha => exact .reflIntro iha
  | cumul ht huv iht => exact .cumul iht huv
  | conv ht hAB iht => exact .conv iht hAB

/-- Level erasure reflects the sealed Tower lane into Legacy typing. -/
theorem SealedHasType.forget {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (h : SealedHasType Γ t A) :
    Legacy.HasType (Legacy.forgetCtx Γ) (Legacy.forget t) (Legacy.forget A) := by
  induction h with
  | legacyGround Γ => exact .headType .groundMarker
  | @var n Γ i =>
      simpa only [Legacy.forget, Legacy.forgetCtx, Tm.mapHead,
        Ctx.lookup_mapHead] using
        (Presentation.HasType.var (R := Legacy.rules)
          (Γ := Legacy.forgetCtx Γ) i)
  | piForm hA hu hB hv hj ihA ihB =>
      cases hu with
      | sort left =>
          cases hv with
          | sort right =>
              cases hj
              exact .piForm ihA .marker ihB .marker .marker
  | sigmaForm hA hu hB hv hj ihA ihB =>
      cases hu with
      | sort left =>
          cases hv with
          | sort right =>
              cases hj
              exact .sigmaForm ihA .marker ihB .marker .marker
  | lamIntro hBody ihBody => exact .lamIntro ihBody
  | appElim hg ha ihg iha =>
      simpa only [Legacy.forget, Tm.mapHead, Tm.mapHead_inst0] using
        (Presentation.HasType.appElim ihg iha)
  | pairIntro ha hb iha ihb =>
      exact .pairIntro iha (by
        simpa only [Legacy.forget, Tm.mapHead_inst0] using ihb)
  | fstElim hp ihp => exact .fstElim ihp
  | sndElim hp ihp =>
      simpa only [Legacy.forget, Tm.mapHead, Tm.mapHead_inst0] using
        (Presentation.HasType.sndElim ihp)
  | idForm hA hu ha hb ihA iha ihb =>
      cases hu
      exact .idForm ihA .marker iha ihb
  | reflIntro ha iha => exact .reflIntro iha
  | @cumul n Γ t u v ht huv iht =>
      cases u <;> cases v <;>
        simp [Tower.Cumulative] at huv
      exact iht
  | conv ht hAB iht => exact .conv iht (Legacy.conv_of_towerConv hAB)

end Tower

namespace Legacy

/-- Every Legacy derivation lands in the sealed Tower subcalculus. -/
theorem sealedHasType_of_hasType {Γ : Legacy.Ctx n} {t A : Legacy.Tm n}
    (h : Legacy.HasType Γ t A) :
    Tower.SealedHasType (embedCtx Γ) (embed t) (embed A) := by
  induction h with
  | headType hHead =>
      cases hHead
      exact .legacyGround _
  | @var n Γ i =>
      simpa only [embed, embedCtx, Tm.mapHead, Ctx.lookup_mapHead] using
        (Tower.SealedHasType.var (Γ := embedCtx Γ) i)
  | const impossible => simp [Legacy.rules] at impossible
  | @piForm n Γ A B u v w hA hu hB hv hj ihA ihB =>
      cases hu
      cases hv
      cases hj
      have hPi : Tower.SealedHasType (embedCtx Γ)
          (.pi (embed A) (embed B))
          (.head (.sort (.max Tower.zero Tower.zero))) :=
        .piForm ihA (.sort Tower.zero) ihB (.sort Tower.zero)
          (.sorts Tower.zero Tower.zero)
      simpa only [embed, Tm.mapHead, Legacy.Head.embed] using
        (Tower.SealedHasType.conv hPi towerZeroJoinConv)
  | @sigmaForm n Γ A B u v w hA hu hB hv hj ihA ihB =>
      cases hu
      cases hv
      cases hj
      have hSigma : Tower.SealedHasType (embedCtx Γ)
          (.sigma (embed A) (embed B))
          (.head (.sort (.max Tower.zero Tower.zero))) :=
        .sigmaForm ihA (.sort Tower.zero) ihB (.sort Tower.zero)
          (.sorts Tower.zero Tower.zero)
      simpa only [embed, Tm.mapHead, Legacy.Head.embed] using
        (Tower.SealedHasType.conv hSigma towerZeroJoinConv)
  | lamIntro hBody ihBody => exact .lamIntro ihBody
  | appElim hg ha ihg iha =>
      simpa only [embed, Tm.mapHead, Tm.mapHead_inst0] using
        (Tower.SealedHasType.appElim ihg iha)
  | @pairIntro n Γ a b A B ha hb iha ihb =>
      exact .pairIntro iha (by
        simpa only [embed, Tm.mapHead_inst0] using ihb)
  | fstElim hp ihp => exact .fstElim ihp
  | sndElim hp ihp =>
      simpa only [embed, Tm.mapHead, Tm.mapHead_inst0] using
        (Tower.SealedHasType.sndElim ihp)
  | idForm hA hu ha hb ihA iha ihb =>
      cases hu
      exact .idForm ihA (.sort Tower.zero) iha ihb
  | reflIntro ha iha => exact .reflIntro iha
  | cumul ht hFalse iht => exact False.elim hFalse
  | conv ht hAB iht => exact .conv iht (towerConv_of_conv hAB)

/-- **Sealed-lane conservativity.** This is full preservation and reflection
for the explicit Tower rule-subset that contains every migrated Legacy
derivation and excludes universe-successor formation. -/
theorem hasType_iff_sealedHasType (Γ : Legacy.Ctx n)
    (t A : Legacy.Tm n) :
    Legacy.HasType Γ t A ↔
      Tower.SealedHasType (embedCtx Γ) (embed t) (embed A) := by
  constructor
  · exact sealedHasType_of_hasType
  · intro h
    simpa using h.forget

/-! ### Executable boundary examples -/

def sealedIdentity : Legacy.Tm 0 := .lam (.var 0)

def sealedIdentityType : Legacy.Tm 0 :=
  .pi (.head .ground) (.head .ground)

/-- Positive: a closed monomorphic identity derivation exists in Legacy. -/
theorem sealedIdentity_hasType :
    Legacy.HasType (.nil : Legacy.Ctx 0) sealedIdentity sealedIdentityType := by
  apply Presentation.HasType.lamIntro
  simpa [sealedIdentity, sealedIdentityType, Ctx.lookup, rename] using
    (Presentation.HasType.var (R := Legacy.rules)
      (Γ := (.snoc (.nil : Legacy.Ctx 0) (.head .ground))) (0 : Fin 1))

/-- Positive: the same derivation crosses the conservative migration lane
and therefore the full Tower judgment. -/
theorem embedded_sealedIdentity_hasType :
    Tower.HasType (embedCtx (.nil : Legacy.Ctx 0))
      (embed sealedIdentity) (embed sealedIdentityType) :=
  (sealedHasType_of_hasType sealedIdentity_hasType).toHasType

/-- Negative: the sealed migration lane contains no universe-successor
formation rule. -/
theorem sealed_sort_has_no_type {n : Nat} (Γ : Tower.Ctx n) (level :
    Mettapedia.TypeTheory.UniverseLevel.LevelExpr)
    (A : Tower.Tm n) :
    ¬ Tower.SealedHasType Γ (.head (.sort level)) A := by
  intro h
  generalize hterm : (.head (.sort level) : Tower.Tm n) = term at h
  induction h with
  | legacyGround => cases hterm
  | var => cases hterm
  | piForm => cases hterm
  | sigmaForm => cases hterm
  | lamIntro => cases hterm
  | appElim => cases hterm
  | pairIntro => cases hterm
  | fstElim => cases hterm
  | sndElim => cases hterm
  | idForm => cases hterm
  | reflIntro => cases hterm
  | cumul ht huv ih => exact ih hterm
  | conv ht hAB ih => exact ih hterm

/-- Contrast: universe-successor formation is present only in unrestricted
Tower typing. -/
theorem tower_sort_has_successor_type (level :
    Mettapedia.TypeTheory.UniverseLevel.LevelExpr) :
    Tower.HasType (.nil : Tower.Ctx 0) (.head (.sort level))
      (.head (.sort (.succ level))) :=
  .headType (.sort level)

/-! ### Why unrestricted raw-syntax conservativity is false -/

/-- A raw Legacy term that uses the old formation marker as a computational
argument.  It is syntactically legal but untypable in the sealed calculus. -/
def legacyUniverseLeak : Legacy.Tm 0 :=
  .app (.lam (.head .ground)) (.head .marker)

def towerUniverseLeak : Tower.Tm 0 := embed legacyUniverseLeak

/-- Unrestricted Tower typing makes the embedded old marker usable as `U 0`:
this is a genuine new derivation stated at an embedded old type. -/
theorem towerUniverseLeak_hasType :
    Tower.HasType (.nil : Tower.Ctx 0) towerUniverseLeak
      (embed (.head .marker : Legacy.Tm 0)) := by
  unfold towerUniverseLeak legacyUniverseLeak embed
  simp only [Tm.mapHead, Legacy.Head.embed]
  have hfun : Tower.HasType (.nil : Tower.Ctx 0)
      (.lam (.head .legacyGround))
      (.pi (.head (.sort (.succ Tower.zero)))
        (.head (.sort Tower.zero))) := by
    apply Presentation.HasType.lamIntro
    exact Presentation.HasType.headType .legacyGround
  have harg : Tower.HasType (.nil : Tower.Ctx 0)
      (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) :=
    Presentation.HasType.headType (.sort Tower.zero)
  simpa [inst0, subst] using
    (Presentation.HasType.appElim hfun harg)

/-- The sealed migration lane cannot type the same raw term at any type,
because doing so would require typing the old marker as a computational
argument. -/
theorem sealedUniverseApplication_hasNoType {n : Nat} (Γ : Tower.Ctx n)
    (level : Mettapedia.TypeTheory.UniverseLevel.LevelExpr)
    (A : Tower.Tm n) :
    ¬ Tower.SealedHasType Γ
      (.app (.lam (.head .legacyGround)) (.head (.sort level))) A := by
  intro h
  generalize hterm :
    (.app (.lam (.head .legacyGround)) (.head (.sort level)) : Tower.Tm n) =
      term at h
  induction h with
  | legacyGround => cases hterm
  | var => cases hterm
  | piForm => cases hterm
  | sigmaForm => cases hterm
  | lamIntro => cases hterm
  | appElim hg ha ihg iha =>
      cases hterm
      exact sealed_sort_has_no_type _ level _ ha
  | pairIntro => cases hterm
  | fstElim => cases hterm
  | sndElim => cases hterm
  | idForm => cases hterm
  | reflIntro => cases hterm
  | cumul ht huv ih => exact ih hterm
  | conv ht hAB ih => exact ih hterm

theorem sealedUniverseLeak_hasNoType (A : Tower.Tm 0) :
    ¬ Tower.SealedHasType (.nil : Tower.Ctx 0) towerUniverseLeak A := by
  unfold towerUniverseLeak legacyUniverseLeak embed
  simp only [Tm.mapHead, Legacy.Head.embed]
  exact sealedUniverseApplication_hasNoType .nil Tower.zero A

/-- Therefore the exact Legacy preimage is untypable. -/
theorem legacyUniverseLeak_not_hasType :
    ¬ Legacy.HasType (.nil : Legacy.Ctx 0) legacyUniverseLeak
      (.head .marker) := by
  intro h
  exact sealedUniverseLeak_hasNoType _ (sealedHasType_of_hasType h)

/-- The unrestricted raw-syntax reflection implication has a concrete
counterexample. -/
theorem unrestricted_raw_reflection_is_false :
    ¬ (∀ (Γ : Legacy.Ctx 0) (t A : Legacy.Tm 0),
      Tower.HasType (embedCtx Γ) (embed t) (embed A) →
        Legacy.HasType Γ t A) := by
  intro h
  exact legacyUniverseLeak_not_hasType
    (h .nil legacyUniverseLeak (.head .marker) towerUniverseLeak_hasType)

end Legacy

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
