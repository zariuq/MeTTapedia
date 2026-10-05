import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Carriers

/-!
# Validity of the rules of the annotated calculus

The rules of the annotated calculus not treated in `LogicalRelationValidity` and
`LogicalRelationConstants` preserve validity (`CStatement.Valid`): from valid premises,
over a formed context, the conclusion is valid.

**Tokens.** The tokens typed at a compact type below an identity type are the tag and
the point tokens of reflexivity (`tyTok_below_ident`), so a typed token of a
reflexivity is its tag or the point token of a typed token of its point
(`typed_refl_token`). The outputs of a typed entry of an element of a dependent
function type are tokens of its value at the projection of the entry's input, typed at
the family's value there (`typed_fnEntry_app`, the η token lemma).

**Parts and instances of adequate types.** The domain and the family of an adequate
dependent pair type are adequate (`AdequateType.sigma_dom`, `AdequateType.sigma_cod`).
An adequate type over an extended context, or an adequate term there, opened at an
adequate argument is adequate (`AdequateType.inst0`, `Adequate.inst0`); hence the
family of an adequate dependent pair type at an adequate argument
(`AdequateType.instSigma`).

**From the cross relation.** A type related, at one substitution, to a type that
denotes alike is adequate when the first is (`AdequateType.of_cross`); likewise for
terms at an adequate type (`Adequate.of_cross`). So a rule concluding an equation needs
the left side's adequacy and the relation of the two sides at one substitution.

**Abstraction at an equal annotation** (`Adequate.lamAt`): an abstraction whose
annotation is equal to the domain of a dependent function type is adequate at it when
its body is adequate over the domain; its β-step is typed through the congruence of
abstractions.

**The rules.** Typing: `pairIntro`, `fstElim`, `sndElim`, `reflIntro`. Equivalence and
conversion: `refl`, `symm`, `trans`, `convEq`, `subEq`. Congruence: `piCong`,
`sigmaCong`, `idCong`, `lamCong`, `appCong`, `pairCong`, `fstCong`, `sndCong`,
`reflCong`. Computation: `betaPi`, `betaFst`, `betaSnd`, `root`. η: `etaPi`,
`etaSigma`. Subtyping: `subEqual`, `subUniv`, `subPi`, `subSigma`, `subTrans`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypedAt principal)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## Tokens -/

section Tokens

/-- A compact element below an identity type has no tag but that of identity types. -/
theorem tag_of_below_ident {A I J : Ideal} {a : List Tok} (ha : Ideal.Below a (Ideal.ident A I J))
    {k : Kind} (h : Tok.tag k ∈ a) : k = .ident := by
  rcases Ideal.closure_tag (ha _ h) with e | ⟨d, e, -⟩ | ⟨C, s, e, -, -⟩ | ⟨C, s, e, -, -⟩
  · exact Tok.tag.inj e
  · cases e
  · cases e
  · cases e

/-- **The tokens typed at a compact type below an identity type** are the tag of
reflexivity and point tokens, whose component is typed at the carrier part. -/
theorem tyTok_below_ident {A I J : Ideal} {a : List Tok} (ha : Ideal.Below a (Ideal.ident A I J))
    {t : Tok} (ht : TyTok a t) :
    t = .tag .refl ∨ ∃ s, t = .arg .refl 0 [] s ∧ TyTok (args .ident 0 a) s := by
  have notTag : ∀ {k : Kind}, k ≠ .ident → Tok.tag k ∉ a := fun hk h =>
    hk (tag_of_below_ident ha h)
  have notUniv : ¬ IsUniv a := by
    rintro (h | h)
    · exact notTag (by decide) h
    · exact notTag (by decide) h
  cases t with
  | tag k =>
      rcases tag_cases k with hk | rfl | rfl | rfl | rfl | rfl | hk
      · exact absurd ((tyTok_tag_former hk).1 ht) notUniv
      · exact absurd (tyTok_tag_zero.1 ht) (notTag (by decide))
      · exact absurd (tyTok_tag_succ.1 ht) (notTag (by decide))
      · exact .inl rfl
      · exact absurd ht tyTok_tag_lam
      · exact absurd ht tyTok_tag_pair
      · obtain ⟨d, c, fs, rfl⟩ := hk
        exact absurd (tyTok_tag_ctor.1 ht) (notTag (k := .data _) nofun)
  | arg k i C s =>
      rcases Decidable.em ((k, i) ∈ argSlots) with hs | hother
      swap
      · rcases decl_cases k with ⟨d, rfl⟩ | ⟨d, c, fs, rfl⟩ | hk
        · exact absurd (tyTok_param.1 ht).1 notUniv
        · exact absurd (tyTok_field.1 ht).1 (notTag (k := .data _) nofun)
        · exact absurd ht (tyTok_arg_other hother hk)
      simp only [argSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd ((tyTok_dom (.inl rfl)).1 ht).1 notUniv
      · exact absurd ((tyTok_dom (.inr (.inl rfl))).1 ht).1 notUniv
      · exact absurd ((tyTok_dom (.inr (.inr rfl))).1 ht).1 notUniv
      · exact absurd ((tyTok_endpoint (.inl rfl)).1 ht).1 notUniv
      · exact absurd ((tyTok_endpoint (.inr rfl)).1 ht).1 notUniv
      · exact absurd (tyTok_pred.1 ht).1 (notTag (by decide))
      · obtain ⟨-, rfl, hs, -⟩ := tyTok_reflPoint.1 ht
        exact .inr ⟨s, rfl, hs⟩
      · exact absurd (tyTok_fst.1 ht).1 (notTag (by decide))
      · exact absurd (tyTok_snd.1 ht).1 (notTag (by decide))
  | fn k C X Y =>
      rcases fn_cases k with hk | rfl | hother
      · exact absurd ((tyTok_family hk).1 ht).1 notUniv
      · exact absurd (tyTok_lam.1 ht).1 (notTag (by decide))
      · exact absurd ht (tyTok_fn_other hother)

/-- **The typed tokens of a reflexivity**: a token of `refl I` typed at a compact type
below an identity type is the tag of reflexivity, or the point token of a token of `I`
typed at the carrier part of the type. -/
theorem typed_refl_token {A I' J' I : Ideal} {c : List Tok}
    (hc : Ideal.Below c (Ideal.ident A I' J')) {t : Tok} (ht : (Ideal.refl I).Mem t)
    (hct : TyTok c t) :
    t = .tag .refl ∨ ∃ s, t = .arg .refl 0 [] s ∧ I.Mem s ∧ TyTok (args .ident 0 c) s := by
  rcases tyTok_below_ident hc hct with rfl | ⟨s, rfl, hs⟩
  · exact .inl rfl
  · refine .inr ⟨s, rfl, ?_, hs⟩
    rw [← Ideal.reflPoint_refl I]
    exact Ideal.subset_closure ht

/-- **The η token lemma**: the outputs of a typed entry `X ↦ Y` of an element of a
dependent function type `cpi A G` are tokens of its value at the projection of `X` onto
the domain, typed at the family's value there. -/
theorem typed_fnEntry_app {A : Ideal} {G : Ideal → Ideal} (hG : Ideal.Cont G) {f : Ideal}
    {X Y : List Tok} (hf : f.Mem (.fn .lam [] X Y))
    (hT : TypedAt (Ideal.cpi A G) (.fn .lam [] X Y)) :
    ∀ y ∈ Y, (Ideal.app f (projT A (principal X))).Mem y ∧
      TypedAt (G (projT A (principal X))) y := by
  intro y hy
  obtain ⟨b, hb, hbu, hbt⟩ := hT
  have hbF : Ideal.Below b (Ideal.former .pi A fun X => G (projT A (principal X))) := hb
  obtain ⟨X', Y', e, hX, hY⟩ := Ideal.tyTok_below_pi hbF hbt
  injection e with _ _ eX eY
  subst eX eY
  refine ⟨Ideal.mem_app.2 ⟨X, Y, fun x hx => Ideal.subset_closure ⟨ent_of_mem hx,
    args .pi 0 b, Ideal.below_args_former hbF, Ideal.ty_args_dom (.inl rfl) hbu, hX x hx⟩, hf,
    ent_of_mem hy⟩, fnApp .pi b X, ?_, Ideal.ty_fnApp (.inl rfl) hbu X, hY y hy⟩
  have h := Ideal.below_fam_fnApp (k := .pi) (y := principal X) hb fun x hx => ent_of_mem hx
  rwa [Ideal.fam_cpi hG] at h

end Tokens

/-! ## Parts and instances of adequate types -/

section Parts

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

/-- **The domain of an adequate dependent pair type is adequate**: a type token of the
domain is the component of a domain token of the dependent pair type. -/
theorem AdequateType.sigma_dom {n : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {B : CTm Head (n + 1)} (hS : AdequateType Rd H Γ (.sigma A B)) : AdequateType Rd H Γ A := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  have hmem : (cinterp Rd (.sigma A B) ρ).Mem (.arg .sigma 0 [] r) := Ideal.mem_former_dom.2 hr
  have hty : TyTok Elem.univ (.arg .sigma 0 [] r) :=
    (tyTok_dom (.inr (.inl rfl))).2 ⟨Elem.isUniv_univ, rfl, hrU⟩
  rcases RT.ty_argSigma_iff.1 (hS ρ fits formed hσ _ hmem hty) with hvac |
    ⟨D, E, D', E', hp, -, hd⟩
  · exact RT.of_vacuous (vacuous_arg hvac)
  have e₁ := H.red_normal (H.normal_sigma _ _) hp.1.1
  have e₂ := H.red_normal (H.normal_sigma _ _) hp.2.1.1
  injection e₁ with _ e₁D e₁E
  injection e₂ with _ e₂D e₂E
  subst e₁D e₁E e₂D e₂E
  exact hd rfl

include levels in
/-- **The family of an adequate dependent pair type is adequate** over the extended
context, as for dependent function types (`AdequateType.pi_cod`). -/
theorem AdequateType.sigma_cod {n : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {B : CTm Head (n + 1)} (hS : AdequateType Rd H Γ (.sigma A B)) :
    AdequateType Rd H (.snoc Γ A) B := by
  intro ρ' fits' m Δ τ τ' formed hτ r hr hrU
  obtain ⟨x, ρ, rfl⟩ : ∃ x ρ, ρ' = Env.cons x ρ := ⟨_, _, env_eq_cons_tail ρ'⟩
  obtain ⟨N, σ, rfl⟩ : ∃ N σ, τ = CTm.consSub N σ := ⟨_, _, CTm.eq_consSub_tail τ⟩
  obtain ⟨N', σ', rfl⟩ : ∃ N' σ', τ' = CTm.consSub N' σ' := ⟨_, _, CTm.eq_consSub_tail τ'⟩
  have fits : Fits Rd Γ ρ := fits'.1
  have hx : projT (cinterp Rd A ρ) x = x := fits'.2.2
  obtain ⟨hσ, hNN, hNx⟩ := SubstRel.of_cons hτ
  rw [← hx] at hr
  have hG := cinterp_cont_cons Rd B ρ
  -- a finite typed part of the newest value that the token observes
  obtain ⟨X, hX, hrX⟩ := (hG.comp (Ideal.cont_projT (cinterp Rd A ρ))).finite hr
  obtain ⟨w, hwX, hwT, hrw⟩ := Ideal.family_typedObservations hG X r hrX
  have hwx : Ideal.Below w x := Ideal.Below.of_le hwX hX
  obtain ⟨c, hc, hcu, hwc⟩ := Ideal.typedAt_list hwT
  -- the typed family entry of the dependent pair type
  have hF : Ideal.Monotone fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    hG.mono (Ideal.projT_mono (principal_mono h))
  have hmem : (cinterp Rd (.sigma A B) ρ).Mem (.fn .sigma c w [r]) :=
    (Ideal.mem_former_fn hF).2 ⟨hc, fun y hy => by rw [List.mem_singleton.1 hy]; exact hrw⟩
  have hty : TyTok Elem.univ (.fn .sigma c w [r]) :=
    (tyTok_family (.inr rfl)).2 ⟨Elem.isUniv_univ, hcu, hwc,
      fun y hy => by rw [List.mem_singleton.1 hy]; exact hrU⟩
  rcases RT.ty_fnSigma_iff.1 (hS ρ fits formed hσ _ hmem hty) with hvac |
    ⟨D, E, D', E', hp, -, hf, hg⟩
  · exact RT.of_vacuous (vacuous_out hvac List.mem_cons_self)
  have e₁ := H.red_normal (H.normal_sigma _ _) hp.1.1
  have e₂ := H.red_normal (H.normal_sigma _ _) hp.2.1.1
  injection e₁ with _ e₁D e₁E
  injection e₂ with _ e₂D e₂E
  subst e₁D e₁E e₂D e₂E
  -- the newest arguments, related as far as the part observes
  have hNw : ∀ z ∈ w, RT H Δ true z (A.subst σ) N N' := fun z hz => hNx z (hwx z hz) (hwT z hz)
  have tN : CTyped P Δ N (A.subst σ) := (CEqual.typed levels hNN formed).1
  have h₁ := hg N tN (fun z hz => RT.left (hNw z hz)) r List.mem_cons_self
  have h₂ := (hf N N' hNN hNw r List.mem_cons_self).2
  rw [CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub] at h₁
  rw [CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub] at h₂
  exact RT.trans_ty levels formed hrU h₁ h₂

variable (sound : SoundnessFacts Rd P)

include levels sound in
/-- **An adequate type over an extended context, opened at an adequate argument, is
adequate**: related substitutions, extended by the two substituted arguments, are
related over the environment extended by the argument's value. -/
theorem AdequateType.inst0 {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n}
    {B : CTm Head (n + 1)} (tA : CIsType P Γ A) (hA : AdequateType Rd H Γ A)
    (hB : AdequateType Rd H (.snoc Γ A) B) (ha : Adequate Rd H Γ a A) (ta : CTyped P Γ a A) :
    AdequateType Rd H Γ (CTm.inst0 a B) := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  obtain ⟨w, hw, tA⟩ := tA
  have hsem := sound.typing ta ρ fits
  have hsub : SubstRel Rd H (.snoc Γ A) (Env.cons (cinterp Rd a ρ) ρ) Δ
      (CTm.consSub (a.subst σ) σ) (CTm.consSub (a.subst σ') σ') :=
    SubstRel.cons levels formed hσ (CDerivable.functional ta hσ.1)
      ⟨w, hw, CDerivable.functional tA hσ.1⟩ (fun q hq hqU => hA ρ fits formed hσ q hq hqU)
      (fun s hs hsT => ha ρ fits formed hσ s hs hsT)
  rw [cinterp_inst0] at hr
  rw [CTm.subst_inst0, CTm.subst_inst0, CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub]
  exact hB _ (Fits.cons fits hsem.1 hsem.2) formed hsub r hr hrU

include levels sound in
/-- **An adequate term over an extended context, opened at an adequate argument, is
adequate** at its type opened there. -/
theorem Adequate.inst0 {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n}
    {b B : CTm Head (n + 1)} (tA : CIsType P Γ A) (hA : AdequateType Rd H Γ A)
    (hb : Adequate Rd H (.snoc Γ A) b B) (ha : Adequate Rd H Γ a A) (ta : CTyped P Γ a A) :
    Adequate Rd H Γ (CTm.inst0 a b) (CTm.inst0 a B) := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsT
  obtain ⟨w, hw, tA⟩ := tA
  have hsem := sound.typing ta ρ fits
  have hsub : SubstRel Rd H (.snoc Γ A) (Env.cons (cinterp Rd a ρ) ρ) Δ
      (CTm.consSub (a.subst σ) σ) (CTm.consSub (a.subst σ') σ') :=
    SubstRel.cons levels formed hσ (CDerivable.functional ta hσ.1)
      ⟨w, hw, CDerivable.functional tA hσ.1⟩ (fun q hq hqU => hA ρ fits formed hσ q hq hqU)
      (fun s hs hsT => ha ρ fits formed hσ s hs hsT)
  rw [cinterp_inst0] at hs hsT
  rw [CTm.subst_inst0, CTm.subst_inst0, CTm.subst_inst0, CTm.inst0_subst_liftSub,
    CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub]
  exact hb _ (Fits.cons fits hsem.1 hsem.2) formed hsub s hs hsT

include levels sound in
/-- **The family of an adequate dependent pair type at an adequate argument of its
domain is an adequate type.** -/
theorem AdequateType.instSigma {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n}
    {B : CTm Head (n + 1)} (tS : CIsType P Γ (.sigma A B))
    (hS : AdequateType Rd H Γ (.sigma A B)) (ha : Adequate Rd H Γ a A) (ta : CTyped P Γ a A) :
    AdequateType Rd H Γ (CTm.inst0 a B) :=
  AdequateType.inst0 levels sound (CIsType.sigma_parts tS).1 hS.sigma_dom (hS.sigma_cod levels) ha
    ta

end Parts

/-! ## From the cross relation -/

section Cross

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

include levels in
/-- **A type related to an adequate type at one substitution is adequate**, when the two
denote alike: at two related substitutions, the second type is related to the first at
the left one, the first to itself across them, and the first to the second at the right
one. -/
theorem AdequateType.of_cross {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}
    (hA : AdequateType Rd H Γ A)
    (cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ r, (cinterp Rd A ρ).Mem r →
        TyTok Elem.univ r → RT H Δ false r (A.subst σ) (A.subst σ) (B.subst σ))
    (same : ∀ ρ, Fits Rd Γ ρ → cinterp Rd A ρ = cinterp Rd B ρ) : AdequateType Rd H Γ B := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  rw [← same ρ fits] at hr
  have h₁ := cross ρ fits formed hσ.left r hr hrU
  have h₂ := hA ρ fits formed hσ r hr hrU
  have h₃ := cross ρ fits formed (hσ.symm levels formed).left r hr hrU
  exact RT.trans_ty levels formed hrU
    (RT.trans_ty levels formed hrU (RT.symm_ty levels formed hrU h₁) h₂) h₃

include levels in
/-- **A term related to an adequate term at one substitution is adequate**, at an
adequate type, when the two denote alike: at two related substitutions, the second term
is related to the first at the left one, the first to itself across them, and the first
to the second at the right one, converted to the left substitution's type. -/
theorem Adequate.of_cross {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n}
    (tA : CIsType P Γ A) (hT : AdequateType Rd H Γ A) (ha : Adequate Rd H Γ a A)
    (cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ s, (cinterp Rd a ρ).Mem s →
        TypedAt (cinterp Rd A ρ) s → RT H Δ true s (A.subst σ) (a.subst σ) (b.subst σ))
    (same : ∀ ρ, Fits Rd Γ ρ → cinterp Rd a ρ = cinterp Rd b ρ) : Adequate Rd H Γ b A := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsT
  rw [← same ρ fits] at hs
  obtain ⟨c, hc, hcu, hct⟩ := hsT
  have hσ' := hσ.symm levels formed
  obtain ⟨w, hw, tA⟩ := tA
  have eA : CTypeEq P Δ (A.subst σ) (A.subst σ') := ⟨w, hw, CDerivable.functional tA hσ.1⟩
  have self : ∀ q ∈ c, RT H Δ false q (A.subst σ) (A.subst σ) (A.subst σ) := fun q hq =>
    hT ρ fits formed hσ.left q (hc q hq) (hcu q hq)
  have across : ∀ q ∈ c, RT H Δ false q (A.subst σ) (A.subst σ) (A.subst σ') := fun q hq =>
    hT ρ fits formed hσ q (hc q hq) (hcu q hq)
  have h₁ := cross ρ fits formed hσ.left s hs ⟨c, hc, hcu, hct⟩
  have h₂ := ha ρ fits formed hσ s hs ⟨c, hc, hcu, hct⟩
  have h₃ := (RT.conv_iff levels formed hcu hct across eA).2
    (cross ρ fits formed hσ'.left s hs ⟨c, hc, hcu, hct⟩)
  exact RT.trans levels formed hcu hct self
    (RT.trans levels formed hcu hct self (RT.symm levels formed hcu hct self h₁) h₂) h₃

end Cross

/-! ## Equations: symmetry, transitivity, conversion and subsumption -/

section Equations

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

include levels in
/-- **Symmetry of adequate equations**, at an adequate type, of terms that denote
alike. -/
theorem AdequateEq.symm {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n}
    (hT : AdequateType Rd H Γ A) (h : AdequateEq Rd H Γ a b A)
    (same : ∀ ρ, Fits Rd Γ ρ → cinterp Rd a ρ = cinterp Rd b ρ) :
    AdequateEq Rd H Γ b a A := by
  refine ⟨h.2.1, h.1, fun ρ fits m Δ σ formed hσ s hs hsT => ?_⟩
  rw [← same ρ fits] at hs
  obtain ⟨c, hc, hcu, hct⟩ := hsT
  exact RT.symm levels formed hcu hct (fun q hq => hT ρ fits formed hσ q (hc q hq) (hcu q hq))
    (h.2.2 ρ fits formed hσ s hs ⟨c, hc, hcu, hct⟩)

include levels in
/-- **Transitivity of adequate equations**, at an adequate type. -/
theorem AdequateEq.trans {n : Nat} {Γ : CCtx Head n} {a b c A : CTm Head n}
    (hT : AdequateType Rd H Γ A) (h₁ : AdequateEq Rd H Γ a b A)
    (h₂ : AdequateEq Rd H Γ b c A) (same : ∀ ρ, Fits Rd Γ ρ → cinterp Rd a ρ = cinterp Rd b ρ) :
    AdequateEq Rd H Γ a c A := by
  refine ⟨h₁.1, h₂.2.1, fun ρ fits m Δ σ formed hσ s hs hsT => ?_⟩
  have hs' : (cinterp Rd b ρ).Mem s := by rw [← same ρ fits]; exact hs
  obtain ⟨d, hd, hdu, hdt⟩ := hsT
  exact RT.trans levels formed hdu hdt (fun q hq => hT ρ fits formed hσ q (hd q hq) (hdu q hq))
    (h₁.2.2 ρ fits formed hσ s hs ⟨d, hd, hdu, hdt⟩)
    (h₂.2.2 ρ fits formed hσ s hs' ⟨d, hd, hdu, hdt⟩)

variable (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Conversion of adequate equations** along an adequate equation of types. -/
theorem AdequateEq.conv {n : Nat} {Γ : CCtx Head n} {a b A B : CTm Head n} {u : Head}
    (hu : R.isUniverse u) (h : AdequateEq Rd H Γ a b A) (hAB : AdequateEq Rd H Γ A B (.head u))
    (eAB : CEqual P Γ A B (.head u)) : AdequateEq Rd H Γ a b B := by
  refine ⟨Adequate.conv levels sound hu h.1 hAB eAB, Adequate.conv levels sound hu h.2.1 hAB eAB,
    fun ρ fits m Δ σ formed hσ s hs hsB => ?_⟩
  rw [← sound.equality eAB ρ fits] at hsB
  obtain ⟨c, hc, hcu, hct⟩ := hsB
  refine (RT.conv_iff levels formed hcu hct (fun r hr => ?_)
    ⟨u, hu, eAB.substitute hσ.1.1⟩).1 (h.2.2 ρ fits formed hσ s hs ⟨c, hc, hcu, hct⟩)
  exact RT.toType (typeKind_of_tyTok_univ (hcu r hr))
    (CRedTy.refl (CIsType.head_of_universe levels hu))
    (hAB.2.2 ρ fits formed hσ r (hc r hr) (sound.typedAt_head hu ρ (hcu r hr)))

omit sound in
include levels in
/-- **Subsumption of adequate equations** along an adequate subtyping statement. -/
theorem AdequateEq.sub (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n}
    {a b A B : CTm Head n} (h : AdequateEq Rd H Γ a b A) (hAB : AdequateSub Rd H Γ A B)
    (le : CBelow P Γ A B) : AdequateEq Rd H Γ a b B := by
  have conv : ∀ {t : CTm Head n}, Adequate Rd H Γ t A → Adequate Rd H Γ t B := fun ht =>
    (CStatement.Valid.sub levels valid ⟨ht, hAB.1⟩ hAB le).1
  refine ⟨conv h.1, conv h.2.1, fun ρ fits m Δ σ formed hσ s hs hsB => ?_⟩
  rw [← CBelow.sound valid le fits] at hsB
  obtain ⟨c, hc, hcu, hct⟩ := hsB
  exact RT.subConv levels formed hcu hct
    (fun r hr => hAB.2.2 ρ fits formed hσ r (hc r hr) (hcu r hr)) (le.substitute hσ.1.1)
    (h.2.2 ρ fits formed hσ s hs ⟨c, hc, hcu, hct⟩)

end Equations

/-! ## Abstraction at an equal annotation -/

section Abstraction

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}

/-- **The β-step of an abstraction at an equal annotation**, typed at the family: its
typing goes through the congruence of the abstraction with the one annotated by the
domain. -/
theorem CRedTm.betaAt {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m} {A A' : CTm Head n}
    {b B : CTm Head (n + 1)} {u w : Head} (hw : R.isUniverse w) (hu : R.isUniverse u)
    (tPi : CTyped P Γ (.pi A B) (.head u)) (tb : CTyped P (.snoc Γ A) b B)
    (eA : CEqual P Γ A A' (.head w)) {τ : CSub Head n m} (mτ : CSubstMor P Γ Δ τ)
    {N : CTm Head m} (tN : CTyped P Δ N (A.subst τ)) :
    CRedTm H Δ (.app (.lam (A'.subst τ) (b.subst (CTm.liftSub τ))) N) (b.subst (CTm.consSub N τ))
      (B.subst (CTm.consSub N τ)) := by
  have e := CDerivable.betaPi (tPi.substitute mτ) hu (tb.substitute (mτ.lift A)) tN
  have eLam : CEqual P Δ (.lam (A.subst τ) (b.subst (CTm.liftSub τ)))
      (.lam (A'.subst τ) (b.subst (CTm.liftSub τ))) (.pi (A.subst τ) (B.subst (CTm.liftSub τ))) :=
    CEqual.substitute (.lamCong eA hw tPi hu (.refl tb)) mτ
  have eApp := CDerivable.appCong eLam (.refl tN)
  rw [CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub] at e
  rw [CTm.inst0_subst_liftSub] at eApp
  refine ⟨.single ?_, .trans (.symm eApp) e⟩
  have st := H.beta (A'.subst τ) (b.subst (CTm.liftSub τ)) N
  rwa [CTm.inst0_subst_liftSub] at st

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Abstraction at an equal annotation.** An abstraction whose annotation `A'` is equal
to the domain `A` of an adequate dependent function type is adequate at it when its body
is adequate over `A`: the annotation denotes as the domain does, and the proof of
`Adequate.lam` goes through with the β-steps of `CRedTm.betaAt`. -/
theorem Adequate.lamAt {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {b B : CTm Head (n + 1)}
    {u w : Head} (hw : R.isUniverse w) (hu : R.isUniverse u)
    (hA : Adequate Rd H Γ A (.head w)) (hPi : Adequate Rd H Γ (.pi A B) (.head u))
    (hb : Adequate Rd H (.snoc Γ A) b B) (tA : CTyped P Γ A (.head w))
    (tPi : CTyped P Γ (.pi A B) (.head u)) (tb : CTyped P (.snoc Γ A) b B)
    (eA : CEqual P Γ A A' (.head w)) : Adequate Rd H Γ (.lam A' b) (.pi A B) := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsT
  have eSem : cinterp Rd (.lam A' b) ρ = cinterp Rd (.lam A b) ρ := by
    show Ideal.clam _ _ = Ideal.clam _ _
    rw [sound.equality eA ρ fits]
  rw [eSem] at hs
  obtain ⟨b', hb', hb'u, hts⟩ := hsT
  have hbF : Ideal.Below b' (Ideal.former .pi (cinterp Rd A ρ) fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hb'
  obtain ⟨X, Y, rfl, -, hYt⟩ := Ideal.tyTok_below_pi hbF hts
  have hmono : Ideal.Monotone fun X =>
      cinterp Rd b (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    (cinterp_envCont Rd b).mono
      (Env.Le.cons (Ideal.projT_mono (principal_mono h)) (Env.Le.refl ρ))
  have hs' : (Ideal.lam fun X =>
      cinterp Rd b (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)).Mem
        (.fn .lam [] X Y) := hs
  have hY := (Ideal.mem_lam_fn hmono).1 hs'
  have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
    ⟨fits, sound.typeGenerated_of_head hw tA fits, Ideal.projT_projT _ _⟩
  have hyT : ∀ y ∈ Y, TypedAt
      (cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) y := by
    intro y hy
    refine ⟨fnApp .pi b' X, ?_, Ideal.ty_fnApp (.inl rfl) hb'u X, hYt y hy⟩
    rw [← fam_cinterp_pi]
    exact Ideal.below_fam_fnApp hb' fun x hx => ent_of_mem hx
  -- the facts of the substitutions
  have hσ' := hσ.symm levels formed
  have eAσ : CTypeEq P Δ (A.subst σ) (A.subst σ') := ⟨w, hw, CDerivable.functional tA hσ.1⟩
  have relA : ∀ {τ τ' : CSub Head n m}, SubstRel Rd H Γ ρ Δ τ τ' → ∀ r,
      (cinterp Rd A ρ).Mem r → TyTok Elem.univ r →
        RT H Δ false r (A.subst τ) (A.subst τ) (A.subst τ') := fun hτ _ hr hrU =>
    Adequate.toType levels sound hw hA fits formed hτ hr hrU
  obtain ⟨v, hv, tB⟩ := (CIsType.pi_parts ⟨u, hu, tPi⟩).2
  have eB : ∀ {τ τ' : CSub Head (n + 1) m}, CSubstEq P (.snoc Γ A) Δ τ τ' →
      CTypeEq P Δ (B.subst τ) (B.subst τ') := fun hττ' =>
    ⟨v, hv, CDerivable.functional tB hττ'⟩
  have beta : ∀ {τ : CSub Head n m} {N : CTm Head m}, CSubstMor P Γ Δ τ →
      CTyped P Δ N (A.subst τ) →
        CRedTm H Δ (.app (.lam (A'.subst τ) (b.subst (CTm.liftSub τ))) N)
          (b.subst (CTm.consSub N τ)) (B.subst (CTm.consSub N τ)) := fun mτ tN =>
    CRedTm.betaAt hw hu tPi tb eA mτ tN
  -- the function clause
  show RT H Δ true (.fn .lam [] X Y) (.pi (A.subst σ) (B.subst (CTm.liftSub σ)))
    (.lam (A'.subst σ) (b.subst (CTm.liftSub σ)))
    (.lam (A'.subst σ') (b.subst (CTm.liftSub σ')))
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨fun N N' hNN hNX y hy => ?_, fun N tN hNX y hy => ?_⟩
  · rw [CTm.inst0_subst_liftSub]
    obtain ⟨tN, tN'⟩ := CEqual.typed levels hNN formed
    constructor
    · have hsub := SubstRel.cons levels formed hσ.left hNN eAσ.left (relA hσ.left)
        (y := projT (cinterp Rd A ρ) (principal X))
        (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
      refine RT.expand levels formed (beta hσ.1.1 tN) ?_
        (hb _ fits' formed hsub y (hY y hy) (hyT y hy))
      exact (beta hσ.1.1 tN').convType (eB (CSubstEq.cons hσ.left.1 tN' (.symm hNN)))
    · have tNr : CTyped P Δ N (A.subst σ') := tN.convType eAσ
      have tN'r : CTyped P Δ N' (A.subst σ') := tN'.convType eAσ
      have hsub := SubstRel.cons levels formed hσ'.left (hNN.convType eAσ) eAσ.symm.left
        (relA hσ'.left) (y := projT (cinterp Rd A ρ) (principal X)) (fun s' hs' hsT' => by
          obtain ⟨a, ha, hau, hta⟩ := hsT'
          exact (RT.conv_iff levels formed hau hta (fun r hr => relA hσ r (ha r hr) (hau r hr))
            eAσ).1 (RT.of_projT_principal _ hNX hs'))
      have ih := hb _ fits' formed hsub y (hY y hy) (hyT y hy)
      have eBN : CTypeEq P Δ (B.subst (CTm.consSub N σ')) (B.subst (CTm.consSub N σ)) :=
        eB (CSubstEq.cons hσ'.1 tNr (.refl tNr))
      have famRel : ∀ r ∈ fnApp .pi b' X, RT H Δ false r (B.subst (CTm.consSub N σ'))
          (B.subst (CTm.consSub N σ')) (B.subst (CTm.consSub N σ)) := by
        intro r hr
        obtain ⟨C, Z, W, hmem, hZX, hrW⟩ := mem_fnApp'.1 hr
        have relPi := RT.toType rfl (CRedTy.refl (CIsType.head_of_universe levels hu))
          (hPi ρ fits formed hσ _ (hb' _ hmem) (sound.typedAt_head hu ρ (hb'u _ hmem)))
        rcases RT.ty_fnPi_iff.1 relPi with hvac | ⟨D₁, E₁, D₁', E₁', hp, -, -, hg⟩
        · exact RT.of_vacuous (vacuous_out hvac hrW)
        have e₁ := H.red_normal (H.normal_pi _ _) hp.1.1
        have e₂ := H.red_normal (H.normal_pi _ _) hp.2.1.1
        injection e₁ with _ e₁D e₁E
        injection e₂ with _ e₂D e₂E
        subst e₁D e₁E e₂D e₂E
        have hr' := hg N tN (fun z hz => RT.closed' (hZX z hz) fun x hx => RT.left (hNX x hx))
          r hrW
        rw [CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub] at hr'
        exact RT.symm_ty levels formed (Ideal.ty_fnApp (.inl rfl) hb'u X r hr) hr'
      refine RT.expand levels formed ((beta hσ'.1.1 tNr).convType eBN)
        ((beta hσ'.1.1 tN'r).convType
          (eB (CSubstEq.cons hσ'.1 tN'r (CEqual.convType (.symm hNN) eAσ)))) ?_
      exact (RT.conv_iff levels formed (Ideal.ty_fnApp (.inl rfl) hb'u X) (hYt y hy) famRel
        eBN).1 ih
  · rw [CTm.inst0_subst_liftSub]
    have tNr : CTyped P Δ N (A.subst σ') := tN.convType eAσ
    have hsub := SubstRel.cons levels formed hσ (.refl tN) eAσ (relA hσ)
      (y := projT (cinterp Rd A ρ) (principal X))
      (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
    refine RT.expand levels formed (beta hσ.1.1 tN) ?_
      (hb _ fits' formed hsub y (hY y hy) (hyT y hy))
    exact (beta hσ'.1.1 tNr).convType (eB (CSubstEq.cons hσ'.1 tNr (.refl tNr)))

end Abstraction

/-! ## Reflexivity -/

section Reflexivity

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

include levels in
/-- **Reflexivities at equal points are related** at the identity type of the left point,
at its tag, and at a point token whose component relates the left point to itself and to
the right one. -/
theorem RT.reflPoints {m : Nat} {Δ : CCtx Head m} (formed : CCtxFormed P Δ) {B x x' : CTm Head m}
    (e : CEqual P Δ x x' B) {t : Tok}
    (ht : t = .tag .refl ∨
      ∃ s, t = .arg .refl 0 [] s ∧ RT H Δ true s B x x ∧ RT H Δ true s B x x') :
    RT H Δ true t (.id B x x) (.refl x) (.refl x') := by
  have tx := (CEqual.typed levels e formed).1
  obtain ⟨tR, tR'⟩ := CEqual.typed levels (CDerivable.reflCong e) formed
  have red : ReflRed H Δ (.id B x x) (.refl x) (.refl x') B x x x x' :=
    ⟨CRedTy.refl (CTyped.isType levels tR formed), CRedTm.refl tR, CRedTm.refl tR', .refl tx,
      .refl tx, e⟩
  rcases ht with rfl | ⟨s, rfl, h₁, h₂⟩
  · exact RT.tm_reflTag_iff.2 ⟨_, _, _, _, _, red⟩
  · exact RT.tm_argRefl_iff.2 (.inr ⟨_, _, _, _, _, red, fun _ h => absurd h List.not_mem_nil,
      fun _ => ⟨h₁, h₁, h₂⟩⟩)

include levels in
/-- **Reflexivity is adequate** at the identity type of its point: a typed token of it is
its tag, or the point token of a token of the point typed at the carrier, at which the
point's adequacy relates the substituted points. -/
theorem Adequate.refl {n : Nat} {Γ : CCtx Head n} {a A : CTm Head n}
    (ha : Adequate Rd H Γ a A) (ta : CTyped P Γ a A) :
    Adequate Rd H Γ (.refl a) (.id A a a) := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsT
  obtain ⟨c, hc, hcu, hct⟩ := hsT
  have hc' : Ideal.Below c (Ideal.ident (cinterp Rd A ρ) (cinterp Rd a ρ) (cinterp Rd a ρ)) := hc
  have e : CEqual P Δ (a.subst σ) (a.subst σ') (A.subst σ) := CDerivable.functional ta hσ.1
  rcases typed_refl_token hc' hs hct with rfl | ⟨t, rfl, ht, htc⟩
  · exact RT.reflPoints levels formed e (.inl rfl)
  · have htT : TypedAt (cinterp Rd A ρ) t :=
      ⟨args .ident 0 c, Ideal.below_args_ident hc', ty_args_ident hcu, htc⟩
    exact RT.reflPoints levels formed e (.inr ⟨t, rfl, ha ρ fits formed hσ.left t ht htT,
      ha ρ fits formed hσ t ht htT⟩)

end Reflexivity

/-! ## The typing rules -/

section Typing

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Validity of pair introduction.** -/
theorem CStatement.Valid.pairIntro {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n}
    {B : CTm Head (n + 1)} {u : Head}
    (hS : (CStatement.typing Γ (.sigma A B) (.head u)).Valid Rd H)
    (hu : R.isUniverse u) (ha : (CStatement.typing Γ a A).Valid Rd H)
    (hb : (CStatement.typing Γ b (CTm.inst0 a B)).Valid Rd H)
    (tS : CTyped P Γ (.sigma A B) (.head u)) (ta : CTyped P Γ a A)
    (tb : CTyped P Γ b (CTm.inst0 a B)) :
    (CStatement.typing Γ (.pair a b) (.sigma A B)).Valid Rd H :=
  ⟨Adequate.pair levels sound hu hS.1 ha.1 hb.1 tS ta tb, hS.1.adequateType levels sound hu⟩

omit sound in
include levels in
/-- **Validity of the first projection.** -/
theorem CStatement.Valid.fstElim {n : Nat} {Γ : CCtx Head n} {p A : CTm Head n}
    {B : CTm Head (n + 1)} (hp : (CStatement.typing Γ p (.sigma A B)).Valid Rd H)
    (tp : CTyped P Γ p (.sigma A B)) : (CStatement.typing Γ (.fst p) A).Valid Rd H :=
  ⟨Adequate.fst levels hp.1 tp, hp.2.sigma_dom⟩

include levels sound in
/-- **Validity of the second projection**, in a formed context: the family of the
dependent pair type at the first projection is adequate. -/
theorem CStatement.Valid.sndElim {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {p A : CTm Head n} {B : CTm Head (n + 1)}
    (hp : (CStatement.typing Γ p (.sigma A B)).Valid Rd H)
    (tp : CTyped P Γ p (.sigma A B)) :
    (CStatement.typing Γ (.snd p) (CTm.inst0 (.fst p) B)).Valid Rd H :=
  ⟨Adequate.snd levels sound hp.1 tp, AdequateType.instSigma levels sound
    (CTyped.isType levels tp formed) hp.2 (Adequate.fst levels hp.1 tp) (.fstElim tp)⟩

omit sound in
include levels in
/-- **Validity of reflexivity**, in a formed context, where the carrier is a type of a
universe. -/
theorem CStatement.Valid.reflIntro {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {a A : CTm Head n} (ha : (CStatement.typing Γ a A).Valid Rd H) (ta : CTyped P Γ a A) :
    (CStatement.typing Γ (.refl a) (.id A a a)).Valid Rd H := by
  obtain ⟨u, hu, tA⟩ := CTyped.isType levels ta formed
  exact ⟨Adequate.refl levels ha.1 ta, AdequateType.ident levels hu tA ta ta ha.2 ha.1 ha.1⟩

end Typing

/-! ## Equivalence and conversion of equality -/

section Equality

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

/-- **Validity of reflexivity of equality.** -/
theorem CStatement.Valid.refl {n : Nat} {Γ : CCtx Head n} {a A : CTm Head n}
    (ha : (CStatement.typing Γ a A).Valid Rd H) : (CStatement.equality Γ a a A).Valid Rd H :=
  ⟨⟨ha.1, ha.1, fun ρ fits _ _ _ formed hσ s hs hsT => ha.1 ρ fits formed hσ s hs hsT⟩, ha.2⟩

include levels sound in
/-- **Validity of symmetry.** -/
theorem CStatement.Valid.symm {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n}
    (h : (CStatement.equality Γ a b A).Valid Rd H) (e : CEqual P Γ a b A) :
    (CStatement.equality Γ b a A).Valid Rd H :=
  ⟨AdequateEq.symm levels h.2 h.1 fun ρ fits => sound.equality e ρ fits, h.2⟩

include levels sound in
/-- **Validity of transitivity.** -/
theorem CStatement.Valid.trans {n : Nat} {Γ : CCtx Head n} {a b c A : CTm Head n}
    (h₁ : (CStatement.equality Γ a b A).Valid Rd H)
    (h₂ : (CStatement.equality Γ b c A).Valid Rd H)
    (e₁ : CEqual P Γ a b A) : (CStatement.equality Γ a c A).Valid Rd H :=
  ⟨AdequateEq.trans levels h₁.2 h₁.1 h₂.1 fun ρ fits => sound.equality e₁ ρ fits, h₁.2⟩

include levels sound in
/-- **Validity of the conversion of an equation.** -/
theorem CStatement.Valid.convEq {n : Nat} {Γ : CCtx Head n} {a b A B : CTm Head n} {u : Head}
    (h : (CStatement.equality Γ a b A).Valid Rd H)
    (hAB : (CStatement.equality Γ A B (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (eAB : CEqual P Γ A B (.head u)) : (CStatement.equality Γ a b B).Valid Rd H :=
  ⟨AdequateEq.conv levels sound hu h.1 hAB.1 eAB, hAB.1.2.1.adequateType levels sound hu⟩

include levels in
/-- **Validity of the subsumption of an equation.** -/
theorem CStatement.Valid.subEq (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n}
    {a b A B : CTm Head n} (h : (CStatement.equality Γ a b A).Valid Rd H)
    (hAB : (CStatement.sub Γ A B).Valid Rd H) (le : CBelow P Γ A B) :
    (CStatement.equality Γ a b B).Valid Rd H :=
  ⟨AdequateEq.sub levels valid h.1 hAB le, hAB.2.1⟩

end Equality

/-! ## Congruence of the type formers -/

section Formers

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Validity of the congruence of dependent function types.** The left type is adequate
from its components. At one substitution the two types are related: both are dependent
function types with equal components; the domain tokens relate the domains by the
domains' equation; a family entry relates each family at two related arguments by its
adequacy, and the two families at one argument by the families' equation. So the right
type is adequate too (`AdequateType.of_cross`). -/
theorem CStatement.Valid.piCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A A' : CTm Head n} {B B' : CTm Head (n + 1)} {u v w : Head}
    (hA : (CStatement.equality Γ A A' (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (hB : (CStatement.equality (.snoc Γ A) B B' (.head v)).Valid Rd H) (hv : R.isUniverse v)
    (join : R.join u v w) (eA : CEqual P Γ A A' (.head u))
    (eB : CEqual P (.snoc Γ A) B B' (.head v)) :
    (CStatement.equality Γ (.pi A B) (.pi A' B') (.head w)).Valid Rd H := by
  have hw := (levels.join_level join).1
  have ePi : CEqual P Γ (.pi A B) (.pi A' B') (.head w) := .piCong eA hu eB hv join
  obtain ⟨tPi, tPi'⟩ := CEqual.typed levels ePi formed
  obtain ⟨tA, -⟩ := CEqual.typed levels eA formed
  have hAty : AdequateType Rd H Γ A := hA.1.1.adequateType levels sound hu
  have hBty : AdequateType Rd H (.snoc Γ A) B := hB.1.1.adequateType levels sound hv
  have hB'ty : AdequateType Rd H (.snoc Γ A) B' := hB.1.2.1.adequateType levels sound hv
  have hPi : AdequateType Rd H Γ (.pi A B) :=
    AdequateType.pi levels sound ⟨w, hw, tPi⟩ hAty hBty
  have cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ r, (cinterp Rd (.pi A B) ρ).Mem r →
        TyTok Elem.univ r → RT H Δ false r ((CTm.pi A B).subst σ) ((CTm.pi A B).subst σ)
          ((CTm.pi A' B').subst σ) := by
    intro ρ fits m Δ σ formed' hσ r hr hrU
    have piRed : PiRed H Δ ((CTm.pi A B).subst σ) ((CTm.pi A' B').subst σ) (A.subst σ)
        (B.subst (CTm.liftSub σ)) (A'.subst σ) (B'.subst (CTm.liftSub σ)) :=
      ⟨CRedTy.refl ⟨w, hw, tPi.substitute hσ.1.1⟩,
        CRedTy.refl ⟨w, hw, tPi'.substitute hσ.1.1⟩,
        ⟨u, hu, eA.substitute hσ.1.1⟩, ⟨v, hv, eB.substitute (hσ.1.1.lift A)⟩⟩
    have crossA : ∀ q, (cinterp Rd A ρ).Mem q → TyTok Elem.univ q →
        RT H Δ false q (A.subst σ) (A.subst σ) (A'.subst σ) := fun q hq hqU =>
      RT.toType (typeKind_of_tyTok_univ hqU) (CRedTy.refl (CIsType.head_of_universe levels hu))
        (hA.1.2.2 ρ fits formed' hσ q hq (sound.typedAt_head hu ρ hqU))
    have hG := cinterp_cont_cons Rd B ρ
    have hF : Ideal.Monotone fun X =>
        cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
      hG.mono (Ideal.projT_mono (principal_mono h))
    rcases typed_former_token (.inl rfl) hF hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
      ⟨C, X, Y, rfl, hCA, hYF, hC, -, hY⟩
    · exact RT.of_vacuous hvac
    · exact RT.ty_pi_iff.2 ⟨_, _, _, _, piRed⟩
    · exact RT.ty_argPi_iff.2 (.inr ⟨_, _, _, _, piRed, fun c hc => absurd hc List.not_mem_nil,
        fun _ => crossA d hd hdU⟩)
    · have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
        ⟨fits, sound.typeGenerated_of_head hu tA fits, Ideal.projT_projT _ _⟩
      have hsub : ∀ {N N' : CTm Head m}, CEqual P Δ N N' (A.subst σ) →
          (∀ z ∈ X, RT H Δ true z (A.subst σ) N N') →
            SubstRel Rd H (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ
              (CTm.consSub N σ) (CTm.consSub N' σ) := fun hNN hNX =>
        SubstRel.cons levels formed' hσ hNN ⟨u, hu, .refl (tA.substitute hσ.1.1)⟩
          (fun q hq hqU => hAty ρ fits formed' hσ q hq hqU)
          (fun s hs _ => RT.of_projT_principal _ hNX hs)
      refine RT.ty_fnPi_iff.2 (.inr ⟨_, _, _, _, piRed, fun c hc => crossA c (hCA c hc) (hC c hc),
        fun N N' hNN hNX y hy => ?_, fun N tN hNX y hy => ?_⟩)
      · simp only [CTm.inst0_subst_liftSub]
        have hyB' : (cinterp Rd B' (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)).Mem y := by
          rw [← sound.equality eB _ fits']
          exact hYF y hy
        exact ⟨hBty _ fits' formed' (hsub hNN hNX) y (hYF y hy) (hY y hy),
          hB'ty _ fits' formed' (hsub hNN hNX) y hyB' (hY y hy)⟩
      · simp only [CTm.inst0_subst_liftSub]
        exact RT.toType (typeKind_of_tyTok_univ (hY y hy))
          (CRedTy.refl (CIsType.head_of_universe levels hv))
          (hB.1.2.2 _ fits' formed' (hsub (.refl tN) hNX) y (hYF y hy)
            (sound.typedAt_head hv _ (hY y hy)))
  have hPi' := AdequateType.of_cross levels hPi cross fun ρ fits => sound.equality ePi ρ fits
  refine ⟨⟨hPi.adequate levels sound hw, hPi'.adequate levels sound hw,
    fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩, AdequateType.universe levels sound hw⟩
  have hsU := sound.tyTok_of_typedAt_head hw hsT
  exact RT.ofType (typeKind_of_tyTok_univ hsU) hw (CRedTy.refl (CIsType.head_of_universe levels hw))
    (cross ρ fits formed' hσ s hs hsU)

include levels sound in
/-- **Validity of the congruence of dependent pair types**, as for dependent function
types. -/
theorem CStatement.Valid.sigmaCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A A' : CTm Head n} {B B' : CTm Head (n + 1)} {u v w : Head}
    (hA : (CStatement.equality Γ A A' (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (hB : (CStatement.equality (.snoc Γ A) B B' (.head v)).Valid Rd H) (hv : R.isUniverse v)
    (join : R.join u v w) (eA : CEqual P Γ A A' (.head u))
    (eB : CEqual P (.snoc Γ A) B B' (.head v)) :
    (CStatement.equality Γ (.sigma A B) (.sigma A' B') (.head w)).Valid Rd H := by
  have hw := (levels.join_level join).1
  have eS : CEqual P Γ (.sigma A B) (.sigma A' B') (.head w) := .sigmaCong eA hu eB hv join
  obtain ⟨tS, tS'⟩ := CEqual.typed levels eS formed
  obtain ⟨tA, -⟩ := CEqual.typed levels eA formed
  have hAty : AdequateType Rd H Γ A := hA.1.1.adequateType levels sound hu
  have hBty : AdequateType Rd H (.snoc Γ A) B := hB.1.1.adequateType levels sound hv
  have hB'ty : AdequateType Rd H (.snoc Γ A) B' := hB.1.2.1.adequateType levels sound hv
  have hS : AdequateType Rd H Γ (.sigma A B) :=
    AdequateType.sigma levels sound ⟨w, hw, tS⟩ hAty hBty
  have cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ r, (cinterp Rd (.sigma A B) ρ).Mem r →
        TyTok Elem.univ r → RT H Δ false r ((CTm.sigma A B).subst σ) ((CTm.sigma A B).subst σ)
          ((CTm.sigma A' B').subst σ) := by
    intro ρ fits m Δ σ formed' hσ r hr hrU
    have sigRed : SigmaRed H Δ ((CTm.sigma A B).subst σ) ((CTm.sigma A' B').subst σ) (A.subst σ)
        (B.subst (CTm.liftSub σ)) (A'.subst σ) (B'.subst (CTm.liftSub σ)) :=
      ⟨CRedTy.refl ⟨w, hw, tS.substitute hσ.1.1⟩,
        CRedTy.refl ⟨w, hw, tS'.substitute hσ.1.1⟩,
        ⟨u, hu, eA.substitute hσ.1.1⟩, ⟨v, hv, eB.substitute (hσ.1.1.lift A)⟩⟩
    have crossA : ∀ q, (cinterp Rd A ρ).Mem q → TyTok Elem.univ q →
        RT H Δ false q (A.subst σ) (A.subst σ) (A'.subst σ) := fun q hq hqU =>
      RT.toType (typeKind_of_tyTok_univ hqU) (CRedTy.refl (CIsType.head_of_universe levels hu))
        (hA.1.2.2 ρ fits formed' hσ q hq (sound.typedAt_head hu ρ hqU))
    have hG := cinterp_cont_cons Rd B ρ
    have hF : Ideal.Monotone fun X =>
        cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
      hG.mono (Ideal.projT_mono (principal_mono h))
    rcases typed_former_token (.inr rfl) hF hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
      ⟨C, X, Y, rfl, hCA, hYF, hC, -, hY⟩
    · exact RT.of_vacuous hvac
    · exact RT.ty_sigma_iff.2 ⟨_, _, _, _, sigRed⟩
    · exact RT.ty_argSigma_iff.2 (.inr ⟨_, _, _, _, sigRed,
        fun c hc => absurd hc List.not_mem_nil, fun _ => crossA d hd hdU⟩)
    · have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
        ⟨fits, sound.typeGenerated_of_head hu tA fits, Ideal.projT_projT _ _⟩
      have hsub : ∀ {N N' : CTm Head m}, CEqual P Δ N N' (A.subst σ) →
          (∀ z ∈ X, RT H Δ true z (A.subst σ) N N') →
            SubstRel Rd H (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ
              (CTm.consSub N σ) (CTm.consSub N' σ) := fun hNN hNX =>
        SubstRel.cons levels formed' hσ hNN ⟨u, hu, .refl (tA.substitute hσ.1.1)⟩
          (fun q hq hqU => hAty ρ fits formed' hσ q hq hqU)
          (fun s hs _ => RT.of_projT_principal _ hNX hs)
      refine RT.ty_fnSigma_iff.2 (.inr ⟨_, _, _, _, sigRed,
        fun c hc => crossA c (hCA c hc) (hC c hc), fun N N' hNN hNX y hy => ?_,
        fun N tN hNX y hy => ?_⟩)
      · simp only [CTm.inst0_subst_liftSub]
        have hyB' : (cinterp Rd B' (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)).Mem y := by
          rw [← sound.equality eB _ fits']
          exact hYF y hy
        exact ⟨hBty _ fits' formed' (hsub hNN hNX) y (hYF y hy) (hY y hy),
          hB'ty _ fits' formed' (hsub hNN hNX) y hyB' (hY y hy)⟩
      · simp only [CTm.inst0_subst_liftSub]
        exact RT.toType (typeKind_of_tyTok_univ (hY y hy))
          (CRedTy.refl (CIsType.head_of_universe levels hv))
          (hB.1.2.2 _ fits' formed' (hsub (.refl tN) hNX) y (hYF y hy)
            (sound.typedAt_head hv _ (hY y hy)))
  have hS' := AdequateType.of_cross levels hS cross fun ρ fits => sound.equality eS ρ fits
  refine ⟨⟨hS.adequate levels sound hw, hS'.adequate levels sound hw,
    fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩, AdequateType.universe levels sound hw⟩
  have hsU := sound.tyTok_of_typedAt_head hw hsT
  exact RT.ofType (typeKind_of_tyTok_univ hsU) hw (CRedTy.refl (CIsType.head_of_universe levels hw))
    (cross ρ fits formed' hσ s hs hsU)

include levels sound in
/-- **Validity of the congruence of identity types.** At one substitution the two
identity types are related: they have equal carriers and endpoints, the carrier tokens
relate the carriers by their equation, and the endpoint tokens relate the endpoints by
theirs. -/
theorem CStatement.Valid.idCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A A' a a' b b' : CTm Head n} {u : Head}
    (hA : (CStatement.equality Γ A A' (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (ha : (CStatement.equality Γ a a' A).Valid Rd H)
    (hb : (CStatement.equality Γ b b' A).Valid Rd H)
    (eA : CEqual P Γ A A' (.head u)) (ea : CEqual P Γ a a' A) (eb : CEqual P Γ b b' A) :
    (CStatement.equality Γ (.id A a b) (.id A' a' b') (.head u)).Valid Rd H := by
  have eId : CEqual P Γ (.id A a b) (.id A' a' b') (.head u) := .idCong eA hu ea eb
  obtain ⟨tId, tId'⟩ := CEqual.typed levels eId formed
  obtain ⟨tA, -⟩ := CEqual.typed levels eA formed
  obtain ⟨ta, -⟩ := CEqual.typed levels ea formed
  obtain ⟨tb, -⟩ := CEqual.typed levels eb formed
  have hId : AdequateType Rd H Γ (.id A a b) :=
    AdequateType.ident levels hu tA ta tb (hA.1.1.adequateType levels sound hu) ha.1.1 hb.1.1
  have cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ r, (cinterp Rd (.id A a b) ρ).Mem r →
        TyTok Elem.univ r → RT H Δ false r ((CTm.id A a b).subst σ) ((CTm.id A a b).subst σ)
          ((CTm.id A' a' b').subst σ) := by
    intro ρ fits m Δ σ formed' hσ r hr hrU
    have idRed : IdRed H Δ ((CTm.id A a b).subst σ) ((CTm.id A' a' b').subst σ) (A.subst σ)
        (a.subst σ) (b.subst σ) (A'.subst σ) (a'.subst σ) (b'.subst σ) :=
      ⟨CRedTy.refl ⟨u, hu, tId.substitute hσ.1.1⟩,
        CRedTy.refl ⟨u, hu, tId'.substitute hσ.1.1⟩,
        ⟨u, hu, eA.substitute hσ.1.1⟩, ea.substitute hσ.1.1, eb.substitute hσ.1.1⟩
    have crossA : ∀ q, (cinterp Rd A ρ).Mem q → TyTok Elem.univ q →
        RT H Δ false q (A.subst σ) (A.subst σ) (A'.subst σ) := fun q hq hqU =>
      RT.toType (typeKind_of_tyTok_univ hqU) (CRedTy.refl (CIsType.head_of_universe levels hu))
        (hA.1.2.2 ρ fits formed' hσ q hq (sound.typedAt_head hu ρ hqU))
    rcases typed_ident_token hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
      ⟨C, s, rfl, hCA, hs, hC, hsC⟩ | ⟨C, s, rfl, hCA, hs, hC, hsC⟩
    · exact RT.of_vacuous hvac
    · exact RT.ty_ident_iff.2 ⟨_, _, _, _, _, _, idRed⟩
    · exact RT.ty_argIdent_iff.2 (.inr ⟨_, _, _, _, _, _, idRed,
        fun c hc => absurd hc List.not_mem_nil, fun _ => crossA d hd hdU,
        fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
    · exact RT.ty_argIdent_iff.2 (.inr ⟨_, _, _, _, _, _, idRed,
        fun c hc => crossA c (hCA c hc) (hC c hc), fun h => absurd h (by decide),
        fun _ => ha.1.2.2 ρ fits formed' hσ s hs ⟨C, hCA, hC, hsC⟩,
        fun h => absurd h (by decide)⟩)
    · exact RT.ty_argIdent_iff.2 (.inr ⟨_, _, _, _, _, _, idRed,
        fun c hc => crossA c (hCA c hc) (hC c hc), fun h => absurd h (by decide),
        fun h => absurd h (by decide),
        fun _ => hb.1.2.2 ρ fits formed' hσ s hs ⟨C, hCA, hC, hsC⟩⟩)
  have hId' := AdequateType.of_cross levels hId cross fun ρ fits => sound.equality eId ρ fits
  refine ⟨⟨hId.adequate levels sound hu, hId'.adequate levels sound hu,
    fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩, AdequateType.universe levels sound hu⟩
  have hsU := sound.tyTok_of_typedAt_head hu hsT
  exact RT.ofType (typeKind_of_tyTok_univ hsU) hu (CRedTy.refl (CIsType.head_of_universe levels hu))
    (cross ρ fits formed' hσ s hs hsU)

end Formers

/-! ## Congruence of the term formers -/

section Terms

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Validity of the congruence of abstractions.** Both abstractions are adequate at the
left one's type (`Adequate.lamAt`). At one substitution, a typed token relates each to
itself at two related arguments, and the two at one argument after the β-steps, by the
bodies' equation. -/
theorem CStatement.Valid.lamCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A A' : CTm Head n} {body body' B : CTm Head (n + 1)} {u w : Head}
    (hA : (CStatement.equality Γ A A' (.head w)).Valid Rd H) (hw : R.isUniverse w)
    (hPi : (CStatement.typing Γ (.pi A B) (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (hb : (CStatement.equality (.snoc Γ A) body body' B).Valid Rd H)
    (eA : CEqual P Γ A A' (.head w)) (tPi : CTyped P Γ (.pi A B) (.head u))
    (eb : CEqual P (.snoc Γ A) body body' B) :
    (CStatement.equality Γ (.lam A body) (.lam A' body') (.pi A B)).Valid Rd H := by
  obtain ⟨tA, -⟩ := CEqual.typed levels eA formed
  obtain ⟨tb, tb'⟩ := CEqual.typed levels eb (.snoc formed ⟨w, hw, tA⟩)
  have eLam : CEqual P Γ (.lam A body) (.lam A' body') (.pi A B) := .lamCong eA hw tPi hu eb
  have hAty : AdequateType Rd H Γ A := hA.1.1.adequateType levels sound hw
  have hL := Adequate.lamAt levels sound hw hu hA.1.1 hPi.1 hb.1.1 tA tPi tb (.refl tA)
  have hR := Adequate.lamAt levels sound hw hu hA.1.1 hPi.1 hb.1.2.1 tA tPi tb' eA
  refine ⟨⟨hL, hR, fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩,
    hPi.1.adequateType levels sound hu⟩
  have hs' : (cinterp Rd (.lam A' body') ρ).Mem s := by
    rw [← sound.equality eLam ρ fits]
    exact hs
  have left := hL ρ fits formed' hσ s hs hsT
  have right := hR ρ fits formed' hσ s hs' hsT
  obtain ⟨b', hb', hb'u, hts⟩ := hsT
  have hbF : Ideal.Below b' (Ideal.former .pi (cinterp Rd A ρ) fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hb'
  obtain ⟨X, Y, rfl, -, -⟩ := Ideal.tyTok_below_pi hbF hts
  have hmono : Ideal.Monotone fun X =>
      cinterp Rd body (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    (cinterp_envCont Rd body).mono
      (Env.Le.cons (Ideal.projT_mono (principal_mono h)) (Env.Le.refl ρ))
  have hY := (Ideal.mem_lam_fn hmono).1 hs
  have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
    ⟨fits, sound.typeGenerated_of_head hw tA fits, Ideal.projT_projT _ _⟩
  have piType : CIsType P Δ (.pi (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    ⟨u, hu, tPi.substitute hσ.1.1⟩
  rcases RT.tm_lam_iff.1 left with hvac | hcl
  · exact RT.of_vacuous hvac
  rcases RT.tm_lam_iff.1 right with hvac | hcr
  · exact RT.of_vacuous hvac
  obtain ⟨hl, -⟩ := hcl _ _ (CRedTy.refl piType)
  obtain ⟨hr, -⟩ := hcr _ _ (CRedTy.refl piType)
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨fun N N' hNN hNX y hy => ⟨(hl N N' hNN hNX y hy).1, (hr N N' hNN hNX y hy).1⟩,
    fun N tN hNX y hy => ?_⟩
  have hsub : SubstRel Rd H (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ
      (CTm.consSub N σ) (CTm.consSub N σ) :=
    SubstRel.cons levels formed' hσ (.refl tN) ⟨w, hw, .refl (tA.substitute hσ.1.1)⟩
      (fun q hq hqU => hAty ρ fits formed' hσ q hq hqU)
      (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
  have hyT : TypedAt (cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) y :=
    (typed_fnEntry_app (cinterp_cont_cons Rd B ρ) (f := cinterp Rd (.lam A body) ρ) hs
      ⟨b', hb', hb'u, hts⟩ y hy).2
  rw [CTm.inst0_subst_liftSub]
  exact RT.expand levels formed' (CRedTm.betaAt hw hu tPi tb (.refl tA) hσ.1.1 tN)
    (CRedTm.betaAt hw hu tPi tb' eA hσ.1.1 tN) (hb.1.2.2 _ fits' formed' hsub y (hY y hy) hyT)

include levels sound in
/-- **Validity of the congruence of applications.** The left application is valid
(`CStatement.Valid.appElim`). At one substitution, a token of it is entailed by outputs
of typed entries of the function whose inputs the argument entails; at each, the
functions' equation relates `f a` to `g a`, and the right function's clause relates
`g a` to `g b` at the arguments' equation; transitivity composes them at the family's
value, related to itself by the function type's relation. -/
theorem CStatement.Valid.appCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {f g a b A : CTm Head n} {B : CTm Head (n + 1)}
    (hf : (CStatement.equality Γ f g (.pi A B)).Valid Rd H)
    (ha : (CStatement.equality Γ a b A).Valid Rd H) (ef : CEqual P Γ f g (.pi A B))
    (ea : CEqual P Γ a b A) :
    (CStatement.equality Γ (.app f a) (.app g b) (CTm.inst0 a B)).Valid Rd H := by
  obtain ⟨tf, -⟩ := CEqual.typed levels ef formed
  obtain ⟨ta, -⟩ := CEqual.typed levels ea formed
  have eApp : CEqual P Γ (.app f a) (.app g b) (CTm.inst0 a B) := .appCong ef ea
  have hL := CStatement.Valid.appElim levels sound ⟨hf.1.1, hf.2⟩ ⟨ha.1.1, ha.2⟩ tf ta
  have cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ s, (cinterp Rd (.app f a) ρ).Mem s →
        TypedAt (cinterp Rd (CTm.inst0 a B) ρ) s → RT H Δ true s ((CTm.inst0 a B).subst σ)
          ((CTm.app f a).subst σ) ((CTm.app g b).subst σ) := by
    intro ρ fits m Δ σ formed' hσ s hs _
    rw [CTm.subst_inst0]
    obtain ⟨X, Y, hX, hfXY, hYs⟩ := Ideal.mem_app.1 hs
    rw [← (sound.typing tf ρ fits).2] at hfXY
    obtain ⟨v, hvf, hvT, hve⟩ := Ideal.projT_eq_iSup.1 hfXY
    obtain ⟨c, hc, hcu, hvc⟩ := Ideal.typedAt_list hvT
    have hcF : Ideal.Below c (Ideal.former .pi (cinterp Rd A ρ) fun X =>
        cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hc
    have piType : CIsType P Δ (.pi (A.subst σ) (B.subst (CTm.liftSub σ))) :=
      CTyped.isType levels (tf.substitute hσ.1.1) formed'
    have taσ : CTyped P Δ (a.subst σ) (A.subst σ) := ta.substitute hσ.1.1
    have key : ∀ w ∈ fnApp .lam v X, RT H Δ true w
        (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ)))
        (.app (f.subst σ) (a.subst σ)) (.app (g.subst σ) (b.subst σ)) := by
      intro w hw
      obtain ⟨C, Z, W, hmem, hZX, hwW⟩ := mem_fnApp'.1 hw
      obtain ⟨Z', W', e, hZ, hW⟩ := Ideal.tyTok_below_pi hcF (hvc _ hmem)
      injection e with _ eC eZ eW
      subst eC eZ eW
      have relfg := hf.1.2.2 ρ fits formed' hσ _ (hvf _ hmem) ⟨c, hc, hcu, hvc _ hmem⟩
      rcases RT.tm_lam_iff.1 relfg with hvac | hcl
      · exact RT.of_vacuous (vacuous_out hvac hwW)
      obtain ⟨hi, hii⟩ := hcl _ _ (CRedTy.refl piType)
      have hzT : ∀ z ∈ Z, (cinterp Rd a ρ).Mem z ∧ TypedAt (cinterp Rd A ρ) z := fun z hz =>
        ⟨(cinterp Rd a ρ).closed hX (hZX z hz),
          args .pi 0 c, Ideal.below_args_former hcF, Ideal.ty_args_dom (.inl rfl) hcu, hZ z hz⟩
      have hself : ∀ z ∈ Z, RT H Δ true z (A.subst σ) (a.subst σ) (a.subst σ) := fun z hz =>
        ha.1.1 ρ fits formed' hσ z (hzT z hz).1 (hzT z hz).2
      have hab : ∀ z ∈ Z, RT H Δ true z (A.subst σ) (a.subst σ) (b.subst σ) := fun z hz =>
        ha.1.2.2 ρ fits formed' hσ z (hzT z hz).1 (hzT z hz).2
      have h₁ := hii (a.subst σ) taσ hself w hwW
      have h₂ := (hi (a.subst σ) (b.subst σ) (ea.substitute hσ.1.1) hab w hwW).2
      have hPiSelf : ∀ r ∈ c, RT H Δ false r (.pi (A.subst σ) (B.subst (CTm.liftSub σ)))
          (.pi (A.subst σ) (B.subst (CTm.liftSub σ)))
          (.pi (A.subst σ) (B.subst (CTm.liftSub σ))) :=
        fun r hr => hf.2 ρ fits formed' hσ r (hc r hr) (hcu r hr)
      have hp := RT.pi_self hPiSelf (tyTok_lam.1 (hvc _ hmem)).1 (CRedTy.refl piType)
      exact RT.trans levels formed' (Ideal.ty_fnApp (.inl rfl) hcu Z) (hW w hwW)
        (RT.pi_fam_at hp hPiSelf (.refl taσ) hself) h₁ h₂
    rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hve
    exact RT.closed' (ent_cut hYs fun y hy => hve.2 y hy) key
  have hR := Adequate.of_cross levels (CTyped.isType levels (.appElim tf ta) formed) hL.2 hL.1 cross
    fun ρ fits => sound.equality eApp ρ fits
  exact ⟨⟨hL.1, hR, cross⟩, hL.2⟩

include levels sound in
/-- **Validity of the congruence of pairs.** The left pair is adequate (`Adequate.pair`).
At one substitution, the projections of the two pairs reduce to their components, related
by the components' equations; the second components move from the family at the left
first component to the family at a term with a common reduct with it, along the
dependent pair type related to itself. -/
theorem CStatement.Valid.pairCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {a a' b b' A : CTm Head n} {B : CTm Head (n + 1)} {u : Head}
    (hS : (CStatement.typing Γ (.sigma A B) (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (ha : (CStatement.equality Γ a a' A).Valid Rd H)
    (hb : (CStatement.equality Γ b b' (CTm.inst0 a B)).Valid Rd H)
    (tS : CTyped P Γ (.sigma A B) (.head u)) (ea : CEqual P Γ a a' A)
    (eb : CEqual P Γ b b' (CTm.inst0 a B)) :
    (CStatement.equality Γ (.pair a b) (.pair a' b') (.sigma A B)).Valid Rd H := by
  obtain ⟨ta, ta'⟩ := CEqual.typed levels ea formed
  obtain ⟨tb, tb'₀⟩ := CEqual.typed levels eb formed
  obtain ⟨-, famB⟩ := CIsType.sigma_parts ⟨u, hu, tS⟩
  have tb' : CTyped P Γ b' (CTm.inst0 a' B) := tb'₀.convType (famB.instantiateEq ta ea)
  have ePair : CEqual P Γ (.pair a b) (.pair a' b') (.sigma A B) := .pairCong tS hu ea eb
  have hL := Adequate.pair levels sound hu hS.1 ha.1.1 hb.1.1 tS ta tb
  have hTy : AdequateType Rd H Γ (.sigma A B) := hS.1.adequateType levels sound hu
  have cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ t, (cinterp Rd (.pair a b) ρ).Mem t →
        TypedAt (cinterp Rd (.sigma A B) ρ) t → RT H Δ true t ((CTm.sigma A B).subst σ)
          ((CTm.pair a b).subst σ) ((CTm.pair a' b').subst σ) := by
    intro ρ fits m Δ σ formed' hσ t ht htT
    obtain ⟨c₀, hc₀, hc₀u, hc₀t⟩ := htT
    have hG := cinterp_cont_cons Rd B ρ
    have taSem : projT (cinterp Rd A ρ) (cinterp Rd a ρ) = cinterp Rd a ρ :=
      (sound.typing ta ρ fits).2
    have hfst : Ideal.fst (cinterp Rd (.pair a b) ρ) = cinterp Rd a ρ := Ideal.fst_pair _ _
    have hsnd : Ideal.snd (cinterp Rd (.pair a b) ρ) = cinterp Rd b ρ := Ideal.snd_pair _ _
    -- the substituted typings
    have tSσ : CTyped P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) (.head u) :=
      tS.substitute hσ.1.1
    have taσ : CTyped P Δ (a.subst σ) (A.subst σ) := ta.substitute hσ.1.1
    have ta'σ : CTyped P Δ (a'.subst σ) (A.subst σ) := ta'.substitute hσ.1.1
    have tbσ : CTyped P Δ (b.subst σ) (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ))) := by
      have h := tb.substitute hσ.1.1
      rwa [CTm.subst_inst0] at h
    have tb'σ : CTyped P Δ (b'.subst σ)
        (CTm.inst0 (a'.subst σ) (B.subst (CTm.liftSub σ))) := by
      have h := tb'.substitute hσ.1.1
      rwa [CTm.subst_inst0] at h
    obtain ⟨-, v, hv, tB⟩ := CIsType.sigma_parts ⟨u, hu, tS⟩
    have eaσ : CEqual P Δ (a.subst σ) (a'.subst σ) (A.subst σ) := ea.substitute hσ.1.1
    have eBa : CTypeEq P Δ (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ)))
        (CTm.inst0 (a'.subst σ) (B.subst (CTm.liftSub σ))) :=
      ⟨v, hv, (tB.substitute (hσ.1.1.lift A)).instantiateEq taσ eaσ⟩
    -- the projections of the two pairs reduce to the components
    have fstσ : CRedTm H Δ (.fst (.pair (a.subst σ) (b.subst σ))) (a.subst σ) (A.subst σ) :=
      ⟨.single (H.fstPair _ _), .betaFst tSσ hu taσ tbσ⟩
    have fstσ' : CRedTm H Δ (.fst (.pair (a'.subst σ) (b'.subst σ))) (a'.subst σ)
        (A.subst σ) :=
      ⟨.single (H.fstPair _ _), .betaFst tSσ hu ta'σ tb'σ⟩
    have sndσ : CRedTm H Δ (.snd (.pair (a.subst σ) (b.subst σ))) (b.subst σ)
        (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ))) :=
      ⟨.single (H.sndPair _ _), .betaSnd tSσ hu taσ tbσ⟩
    have sndσ' : CRedTm H Δ (.snd (.pair (a'.subst σ) (b'.subst σ))) (b'.subst σ)
        (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ))) :=
      ⟨.single (H.sndPair _ _), CEqual.convType (.betaSnd tSσ hu ta'σ tb'σ) eBa.symm⟩
    have eFst : CEqual P Δ (.fst (.pair (a.subst σ) (b.subst σ)))
        (.fst (.pair (a'.subst σ) (b'.subst σ))) (A.subst σ) :=
      .trans fstσ.2 (.trans eaσ (.symm fstσ'.2))
    have sigType : CIsType P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) :=
      ⟨u, hu, tSσ⟩
    -- the first components, related as far as a typed token observes
    have relA : ∀ {s : Tok}, (cinterp Rd a ρ).Mem s → TypedAt (cinterp Rd A ρ) s →
        RT H Δ true s (A.subst σ) (.fst (.pair (a.subst σ) (b.subst σ)))
          (.fst (.pair (a'.subst σ) (b'.subst σ))) := fun hs hsA =>
      RT.expand levels formed' fstσ fstσ' (ha.1.2.2 ρ fits formed' hσ _ hs hsA)
    have hdomBelow : Ideal.Below (args .sigma 0 c₀) (cinterp Rd A ρ) :=
      Ideal.below_args_former hc₀
    have hdomTy : Ty (args .sigma 0 c₀) Elem.univ := Ideal.ty_args_dom (.inr rfl) hc₀u
    show RT H Δ true t (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
      (.pair (a.subst σ) (b.subst σ)) (.pair (a'.subst σ) (b'.subst σ))
    rcases Ideal.typed_pair_token ht hc₀ hc₀t with ⟨s, rfl, hs, hsty⟩ |
      ⟨C, s, rfl, hC, hCty, hs, hsty⟩
    · rw [hfst] at hs
      refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
      have e := H.red_normal (H.normal_sigma _ _) hT.1
      injection e with _ eD eE
      subst eD eE
      exact ⟨eFst, fun _ h => absurd h List.not_mem_nil,
        fun _ => relA hs ⟨_, hdomBelow, hdomTy, hsty⟩, fun h => absurd h (by decide)⟩
    · rw [hfst] at hC
      rw [hsnd] at hs
      have hCA : ∀ c ∈ C, TypedAt (cinterp Rd A ρ) c := fun c hc =>
        ⟨_, hdomBelow, hdomTy, hCty c hc⟩
      -- the second component's type witness is below the family's value at the first
      have hfamBelow : Ideal.Below (fnApp .sigma c₀ C) (cinterp Rd (CTm.inst0 a B) ρ) := by
        have h : Ideal.Below (fnApp .sigma c₀ C)
            (Ideal.fam .sigma (Ideal.csigma (cinterp Rd A ρ) fun y => cinterp Rd B (Env.cons y ρ))
              (cinterp Rd a ρ)) := Ideal.below_fam_fnApp hc₀ hC
        rw [Ideal.fam_csigma hG, taSem] at h
        rw [cinterp_inst0]
        exact h
      have hfamTy : Ty (fnApp .sigma c₀ C) Elem.univ := Ideal.ty_fnApp (.inr rfl) hc₀u C
      have relB := hb.1.2.2 ρ fits formed' hσ s hs ⟨_, hfamBelow, hfamTy, hsty⟩
      rw [CTm.subst_inst0] at relB
      have relB' : RT H Δ true s (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ)))
          (.snd (.pair (a.subst σ) (b.subst σ))) (.snd (.pair (a'.subst σ) (b'.subst σ))) :=
        RT.expand levels formed' sndσ sndσ' relB
      -- the dependent pair type, related to itself as far as its witness observes
      have hSself : ∀ r ∈ c₀, RT H Δ false r (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
          (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
          (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) := fun r hr =>
        hTy ρ fits formed' hσ r (hc₀ r hr) (hc₀u r hr)
      have hpS := RT.sigma_self hSself (tyTok_snd.1 hc₀t).1 (CRedTy.refl sigType)
      refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
      have e := H.red_normal (H.normal_sigma _ _) hT.1
      injection e with _ eD eE
      subst eD eE
      refine ⟨eFst, fun c hc => relA (hC c hc) (hCA c hc), fun h => absurd h (by decide),
        fun _ N Q hQ hNQ => ?_⟩
      obtain ⟨Q', haQ, hNQ'⟩ := CRedTm.join_of_red fstσ hQ hNQ
      have eaN : CEqual P Δ (a.subst σ) N (A.subst σ) := .trans haQ.2 (.symm hNQ'.2)
      have hNN : ∀ x ∈ C, RT H Δ true x (A.subst σ) (a.subst σ) N := fun x hx =>
        RT.retarget levels formed' taσ (ha.1.1 ρ fits formed' hσ _ (hC x hx) (hCA x hx)) haQ hNQ'
      have hE : CIsType P (.snoc Δ (A.subst σ)) (B.subst (CTm.liftSub σ)) :=
        (CIsType.sigma_parts sigType).2
      exact (RT.conv_iff levels formed' hfamTy hsty (RT.sigma_fam_at hpS hSself eaN hNN)
        (hE.instantiateEq taσ eaN)).1 relB'
  have hR := Adequate.of_cross levels ⟨u, hu, tS⟩ hTy hL cross
    fun ρ fits => sound.equality ePair ρ fits
  exact ⟨⟨hL, hR, cross⟩, hTy⟩

include levels in
/-- **Validity of the congruence of first projections**: a typed token of the first
projection is the component of a typed first-projection token, at which the pairs'
equation relates the first projections. -/
theorem CStatement.Valid.fstCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {p q A : CTm Head n} {B : CTm Head (n + 1)}
    (h : (CStatement.equality Γ p q (.sigma A B)).Valid Rd H) (e : CEqual P Γ p q (.sigma A B)) :
    (CStatement.equality Γ (.fst p) (.fst q) A).Valid Rd H := by
  obtain ⟨tp, tq⟩ := CEqual.typed levels e formed
  refine ⟨⟨Adequate.fst levels h.1.1 tp, Adequate.fst levels h.1.2.1 tq,
    fun ρ fits m Δ σ formed' hσ s hs hsA => ?_⟩, h.2.sigma_dom⟩
  obtain ⟨hmem, hty⟩ := Ideal.typed_fst_token (cinterp_cont_cons Rd B ρ) hs hsA
  have sigType : CIsType P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    CTyped.isType levels (tp.substitute hσ.1.1) formed'
  rcases RT.tm_argPair_iff.1 (h.1.2.2 ρ fits formed' hσ _ hmem hty) with hvac | hcl
  · exact RT.of_vacuous (vacuous_arg hvac)
  · exact (hcl _ _ (CRedTy.refl sigType)).2.2.1 rfl

include levels sound in
/-- **Validity of the congruence of second projections**: a typed token of the second
projection is the component of a typed second-projection token whose dependency is a
finite typed part of the first projection, at which the pairs' equation relates the
second projections. -/
theorem CStatement.Valid.sndCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {p q A : CTm Head n} {B : CTm Head (n + 1)}
    (h : (CStatement.equality Γ p q (.sigma A B)).Valid Rd H) (e : CEqual P Γ p q (.sigma A B)) :
    (CStatement.equality Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B)).Valid Rd H := by
  obtain ⟨tp, -⟩ := CEqual.typed levels e formed
  have eSnd : CEqual P Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B) := .sndCong e
  have hTy : AdequateType Rd H Γ (CTm.inst0 (.fst p) B) :=
    AdequateType.instSigma levels sound (CTyped.isType levels tp formed) h.2
      (Adequate.fst levels h.1.1 tp) (.fstElim tp)
  have hL := Adequate.snd levels sound h.1.1 tp
  have cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ s, (cinterp Rd (.snd p) ρ).Mem s →
        TypedAt (cinterp Rd (CTm.inst0 (.fst p) B) ρ) s →
          RT H Δ true s ((CTm.inst0 (.fst p) B).subst σ) ((CTm.snd p).subst σ)
            ((CTm.snd q).subst σ) := by
    intro ρ fits m Δ σ formed' hσ s hs hsT
    rw [CTm.subst_inst0]
    rw [cinterp_inst0] at hsT
    obtain ⟨w, hmem, hty⟩ := Ideal.typed_snd_token (cinterp_cont_cons Rd B ρ)
      (sound.typing tp ρ fits).2 hs hsT
    have sigType : CIsType P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) :=
      CTyped.isType levels (tp.substitute hσ.1.1) formed'
    rcases RT.tm_argPair_iff.1 (h.1.2.2 ρ fits formed' hσ _ hmem hty) with hvac | hcl
    · exact RT.of_vacuous (vacuous_arg hvac)
    obtain ⟨e₀, -, -, h1⟩ := hcl _ _ (CRedTy.refl sigType)
    have tfst := (CEqual.typed levels e₀ formed').1
    exact h1 rfl _ _ (CRedTm.refl tfst) (CRedTm.refl tfst)
  have hR := Adequate.of_cross levels (CTyped.isType levels (.sndElim tp) formed) hTy hL cross
    fun ρ fits => sound.equality eSnd ρ fits
  exact ⟨⟨hL, hR, cross⟩, hTy⟩

include levels sound in
/-- **Validity of the congruence of reflexivities**: a typed token of the left
reflexivity is its tag, or the point token of a typed token of its point, at which the
points' equation relates the points. -/
theorem CStatement.Valid.reflCong {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {a b A : CTm Head n} (h : (CStatement.equality Γ a b A).Valid Rd H) (e : CEqual P Γ a b A) :
    (CStatement.equality Γ (.refl a) (.refl b) (.id A a a)).Valid Rd H := by
  obtain ⟨ta, -⟩ := CEqual.typed levels e formed
  have eR : CEqual P Γ (.refl a) (.refl b) (.id A a a) := .reflCong e
  have hL := CStatement.Valid.reflIntro levels formed ⟨h.1.1, h.2⟩ ta
  have cross : ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m},
      CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ σ → ∀ s, (cinterp Rd (.refl a) ρ).Mem s →
        TypedAt (cinterp Rd (.id A a a) ρ) s → RT H Δ true s ((CTm.id A a a).subst σ)
          ((CTm.refl a).subst σ) ((CTm.refl b).subst σ) := by
    intro ρ fits m Δ σ formed' hσ s hs hsT
    obtain ⟨c, hc, hcu, hct⟩ := hsT
    have hc' : Ideal.Below c
        (Ideal.ident (cinterp Rd A ρ) (cinterp Rd a ρ) (cinterp Rd a ρ)) := hc
    rcases typed_refl_token hc' hs hct with rfl | ⟨t, rfl, ht, htc⟩
    · exact RT.reflPoints levels formed' (e.substitute hσ.1.1) (.inl rfl)
    · have htT : TypedAt (cinterp Rd A ρ) t :=
        ⟨args .ident 0 c, Ideal.below_args_ident hc', ty_args_ident hcu, htc⟩
      exact RT.reflPoints levels formed' (e.substitute hσ.1.1)
        (.inr ⟨t, rfl, h.1.1 ρ fits formed' hσ t ht htT,
          h.1.2.2 ρ fits formed' hσ t ht htT⟩)
  have hR := Adequate.of_cross levels (CTyped.isType levels (.reflIntro ta) formed) hL.2 hL.1 cross
    fun ρ fits => sound.equality eR ρ fits
  exact ⟨⟨hL.1, hR, cross⟩, hL.2⟩

end Terms

/-! ## Computation and η -/

section Computation

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Validity of β for functions.** The contractum is adequate at the family's value at
the argument (`Adequate.inst0`), and the redex reduces to it by one head step: head
expansion relates the two sides, and the redex is adequate from the contractum
(`Adequate.of_cross`). -/
theorem CStatement.Valid.betaPi {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A a : CTm Head n} {body B : CTm Head (n + 1)} {u : Head}
    (hPi : (CStatement.typing Γ (.pi A B) (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (hb : (CStatement.typing (.snoc Γ A) body B).Valid Rd H)
    (ha : (CStatement.typing Γ a A).Valid Rd H) (tPi : CTyped P Γ (.pi A B) (.head u))
    (tb : CTyped P (.snoc Γ A) body B) (ta : CTyped P Γ a A) :
    (CStatement.equality Γ (.app (.lam A body) a) (CTm.inst0 a body)
      (CTm.inst0 a B)).Valid Rd H := by
  obtain ⟨⟨w, hw, tA⟩, -⟩ := CIsType.pi_parts ⟨u, hu, tPi⟩
  have eβ : CEqual P Γ (.app (.lam A body) a) (CTm.inst0 a body) (CTm.inst0 a B) :=
    .betaPi tPi hu tb ta
  have hPiTy : AdequateType Rd H Γ (.pi A B) := hPi.1.adequateType levels sound hu
  have hTy : AdequateType Rd H Γ (CTm.inst0 a B) := AdequateType.inst levels sound hPiTy ha.1 ta
  have hR : Adequate Rd H Γ (CTm.inst0 a body) (CTm.inst0 a B) :=
    Adequate.inst0 levels sound ⟨w, hw, tA⟩ hPiTy.pi_dom hb.1 ha.1 ta
  have red : ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m}, CSubstMor P Γ Δ σ →
      CRedTm H Δ ((CTm.app (.lam A body) a).subst σ) ((CTm.inst0 a body).subst σ)
        ((CTm.inst0 a B).subst σ) := by
    intro m Δ σ mσ
    have r := CRedTm.betaAt (H := H) hw hu tPi tb (.refl tA) mσ (ta.substitute mσ)
    rw [CTm.subst_inst0, CTm.subst_inst0, CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub]
    exact r
  have tR : ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m}, CSubstMor P Γ Δ σ →
      CTyped P Δ ((CTm.inst0 a body).subst σ) ((CTm.inst0 a B).subst σ) := fun mσ =>
    (CTyped.instantiate tb ta).substitute mσ
  have hL : Adequate Rd H Γ (.app (.lam A body) a) (CTm.inst0 a B) :=
    Adequate.of_cross levels (CTyped.isType levels (CTyped.instantiate tb ta) formed) hTy hR
      (fun ρ fits m Δ σ formed' hσ s hs hsT => RT.expand levels formed'
        (CRedTm.refl (tR hσ.1.1)) (red hσ.1.1) (hR ρ fits formed' hσ s hs hsT))
      fun ρ fits => (sound.equality eβ ρ fits).symm
  refine ⟨⟨hL, hR, fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩, hTy⟩
  rw [sound.equality eβ ρ fits] at hs
  exact RT.expand levels formed' (red hσ.1.1) (CRedTm.refl (tR hσ.1.1))
    (hR ρ fits formed' hσ s hs hsT)

include levels sound in
/-- **Validity of β for first projections**: the redex is adequate as the projection of an
adequate pair, and reduces to the first component by one head step. -/
theorem CStatement.Valid.betaFst {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n}
    {B : CTm Head (n + 1)} {u : Head}
    (hS : (CStatement.typing Γ (.sigma A B) (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (ha : (CStatement.typing Γ a A).Valid Rd H)
    (hb : (CStatement.typing Γ b (CTm.inst0 a B)).Valid Rd H)
    (tS : CTyped P Γ (.sigma A B) (.head u)) (ta : CTyped P Γ a A)
    (tb : CTyped P Γ b (CTm.inst0 a B)) :
    (CStatement.equality Γ (.fst (.pair a b)) a A).Valid Rd H := by
  have eF : CEqual P Γ (.fst (.pair a b)) a A := .betaFst tS hu ta tb
  have hL : Adequate Rd H Γ (.fst (.pair a b)) A :=
    Adequate.fst levels (Adequate.pair levels sound hu hS.1 ha.1 hb.1 tS ta tb)
      (.pairIntro tS hu ta tb)
  refine ⟨⟨hL, ha.1, fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩, ha.2⟩
  rw [sound.equality eF ρ fits] at hs
  exact RT.expand levels formed' ⟨.single (H.fstPair _ _), eF.substitute hσ.1.1⟩
    (CRedTm.refl (ta.substitute hσ.1.1)) (ha.1 ρ fits formed' hσ s hs hsT)

include levels sound in
/-- **Validity of β for second projections**: the redex reduces to the second component by
one head step, so it is adequate from the component (`Adequate.of_cross`). -/
theorem CStatement.Valid.betaSnd {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A a b : CTm Head n} {B : CTm Head (n + 1)} {u : Head} (hu : R.isUniverse u)
    (hb : (CStatement.typing Γ b (CTm.inst0 a B)).Valid Rd H)
    (tS : CTyped P Γ (.sigma A B) (.head u)) (ta : CTyped P Γ a A)
    (tb : CTyped P Γ b (CTm.inst0 a B)) :
    (CStatement.equality Γ (.snd (.pair a b)) b (CTm.inst0 a B)).Valid Rd H := by
  have eS : CEqual P Γ (.snd (.pair a b)) b (CTm.inst0 a B) := .betaSnd tS hu ta tb
  have red : ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m}, CSubstMor P Γ Δ σ →
      CRedTm H Δ ((CTm.snd (.pair a b)).subst σ) (b.subst σ) ((CTm.inst0 a B).subst σ) :=
    fun mσ => ⟨.single (H.sndPair _ _), eS.substitute mσ⟩
  have hL : Adequate Rd H Γ (.snd (.pair a b)) (CTm.inst0 a B) :=
    Adequate.of_cross levels (CTyped.isType levels tb formed) hb.2 hb.1
      (fun ρ fits m Δ σ formed' hσ s hs hsT => RT.expand levels formed'
        (CRedTm.refl (tb.substitute hσ.1.1)) (red hσ.1.1) (hb.1 ρ fits formed' hσ s hs hsT))
      fun ρ fits => (sound.equality eS ρ fits).symm
  refine ⟨⟨hL, hb.1, fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩, hb.2⟩
  rw [sound.equality eS ρ fits] at hs
  exact RT.expand levels formed' (red hσ.1.1) (CRedTm.refl (tb.substitute hσ.1.1))
    (hb.1 ρ fits formed' hσ s hs hsT)

include levels sound in
/-- **Validity of a declared root computation.** -/
theorem CStatement.Valid.root {n : Nat} {Γ : CCtx Head n} {left right A : CTm Head n}
    (step : P.computation.step left right) (admits : P.Admits Γ left right)
    (hl : (CStatement.typing Γ left A).Valid Rd H)
    (hr : (CStatement.typing Γ right A).Valid Rd H) (tl : CTyped P Γ left A)
    (tr : CTyped P Γ right A) : (CStatement.equality Γ left right A).Valid Rd H :=
  ⟨AdequateEq.root levels sound step admits hl.1 hr.1 tl tr, hl.2⟩

include levels sound in
/-- **Validity of η for functions.** A typed token of the left function is a function
entry; at two related arguments each function is related to itself by its own adequacy,
and at one argument the two applications are related by the equation of the premise,
at the environment extended by the projection of the entry's input: the entry's
outputs are tokens of the left application there (`typed_fnEntry_app`). -/
theorem CStatement.Valid.etaPi {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {f g A : CTm Head n} {B : CTm Head (n + 1)}
    (hf : (CStatement.typing Γ f (.pi A B)).Valid Rd H)
    (hg : (CStatement.typing Γ g (.pi A B)).Valid Rd H)
    (happ : (CStatement.equality (.snoc Γ A) (.app (f.rename wk) (.var 0))
      (.app (g.rename wk) (.var 0)) B).Valid Rd H)
    (tf : CTyped P Γ f (.pi A B)) (tg : CTyped P Γ g (.pi A B))
    (eapp : CEqual P (.snoc Γ A) (.app (f.rename wk) (.var 0)) (.app (g.rename wk) (.var 0)) B) :
    (CStatement.equality Γ f g (.pi A B)).Valid Rd H := by
  have eη : CEqual P Γ f g (.pi A B) := .etaPi tf tg eapp
  obtain ⟨⟨w, hw, tA⟩, -⟩ := CIsType.pi_parts (CTyped.isType levels tf formed)
  have hAty : AdequateType Rd H Γ A := hf.2.pi_dom
  refine ⟨⟨hf.1, hg.1, fun ρ fits m Δ σ formed' hσ s hs hsT => ?_⟩, hf.2⟩
  have hsg : (cinterp Rd g ρ).Mem s := by
    rw [← sound.equality eη ρ fits]
    exact hs
  have left := hf.1 ρ fits formed' hσ s hs hsT
  have right := hg.1 ρ fits formed' hσ s hsg hsT
  have hsT' := hsT
  obtain ⟨b', hb', -, hts⟩ := hsT
  have hbF : Ideal.Below b' (Ideal.former .pi (cinterp Rd A ρ) fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hb'
  obtain ⟨X, Y, rfl, -, -⟩ := Ideal.tyTok_below_pi hbF hts
  have piType : CIsType P Δ (.pi (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    CTyped.isType levels (tf.substitute hσ.1.1) formed'
  rcases RT.tm_lam_iff.1 left with hvac | hcl
  · exact RT.of_vacuous hvac
  rcases RT.tm_lam_iff.1 right with hvac | hcr
  · exact RT.of_vacuous hvac
  obtain ⟨hl, -⟩ := hcl _ _ (CRedTy.refl piType)
  obtain ⟨hr, -⟩ := hcr _ _ (CRedTy.refl piType)
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨fun N N' hNN hNX y hy => ⟨(hl N N' hNN hNX y hy).1, (hr N N' hNN hNX y hy).1⟩,
    fun N tN hNX y hy => ?_⟩
  -- the entry's outputs are tokens of the left application at the projection of its input
  obtain ⟨hyApp, hyT⟩ := typed_fnEntry_app (cinterp_cont_cons Rd B ρ) hs hsT' y hy
  have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
    ⟨fits, sound.typeGenerated_of_head hw tA fits, Ideal.projT_projT _ _⟩
  have hsub : SubstRel Rd H (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ
      (CTm.consSub N σ) (CTm.consSub N σ) :=
    SubstRel.cons levels formed' hσ (.refl tN) ⟨w, hw, .refl (tA.substitute hσ.1.1)⟩
      (fun q hq hqU => hAty ρ fits formed' hσ q hq hqU)
      (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
  have hyApp' : (cinterp Rd (.app (f.rename wk) (.var 0))
      (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)).Mem y := by
    show (Ideal.app (cinterp Rd (f.rename wk) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ))
      (projT (cinterp Rd A ρ) (principal X))).Mem y
    rw [cinterp_rename_wk]
    exact hyApp
  have h := happ.1.2.2 _ fits' formed' hsub y hyApp' hyT
  simp only [CTm.subst, CTm.subst_consSub_wk, CTm.consSub_zero] at h
  rw [CTm.inst0_subst_liftSub]
  exact h

include levels sound in
/-- **Validity of η for pairs** (`AdequateEq.etaSigma`), at a universe of the dependent pair
type. -/
theorem CStatement.Valid.etaSigma {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {p q A : CTm Head n} {B : CTm Head (n + 1)}
    (hp : (CStatement.typing Γ p (.sigma A B)).Valid Rd H)
    (hq : (CStatement.typing Γ q (.sigma A B)).Valid Rd H)
    (hfst : (CStatement.equality Γ (.fst p) (.fst q) A).Valid Rd H)
    (hsnd : (CStatement.equality Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B)).Valid Rd H)
    (tp : CTyped P Γ p (.sigma A B)) (efst : CEqual P Γ (.fst p) (.fst q) A) :
    (CStatement.equality Γ p q (.sigma A B)).Valid Rd H := by
  obtain ⟨u, hu, -⟩ := CTyped.isType levels tp formed
  exact ⟨AdequateEq.etaSigma levels sound hu (hp.2.adequate levels sound hu) hp.1 hq.1 hfst.1
    hsnd.1 tp efst, hp.2⟩

end Computation

/-! ## Subtyping -/

section Subtyping

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Validity of subtyping by equality**: types related as far as a type token observes
are in the subtyping mode there (`RT.toSub`). -/
theorem CStatement.Valid.subEqual {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n} {u : Head}
    (h : (CStatement.equality Γ A B (.head u)).Valid Rd H) (hu : R.isUniverse u) :
    (CStatement.sub Γ A B).Valid Rd H :=
  ⟨h.1.1.adequateType levels sound hu, h.1.2.1.adequateType levels sound hu,
    fun ρ fits _ _ _ formed' hσ r hr hrU => RT.toSub levels formed' hrU
      (RT.toType (typeKind_of_tyTok_univ hrU) (CRedTy.refl (CIsType.head_of_universe levels hu))
        (h.1.2.2 ρ fits formed' hσ r hr (sound.typedAt_head hu ρ hrU)))⟩

include levels sound in
/-- **Validity of cumulativity**: the only type token of a universe that observes something
is the tag of universes, at which the two universe heads are in the order of heads. -/
theorem CStatement.Valid.subUniv {n : Nat} {Γ : CCtx Head n} {u v : Head}
    (c : R.cumulative u v) : (CStatement.sub Γ (.head u) (.head v)).Valid Rd H := by
  obtain ⟨hu, hv, -⟩ := levels.cumulative_universe c
  refine ⟨AdequateType.universe levels sound hu, AdequateType.universe levels sound hv,
    fun ρ fits m Δ σ formed' hσ r hr hrU => ?_⟩
  have hr' : ent Elem.univ r = true := by
    have h0 : (principal (Rd.head u)).Mem r := hr
    rwa [sound.universes hu] at h0
  cases hvac : ent [] r with
  | true => exact RTSub.of_vacuous hvac
  | false =>
    obtain rfl := eq_tag_univ_of_typed hr' hvac hrU
    exact RTSub.univ_iff.2 ⟨u, v, CRedTy.refl (CIsType.head_of_universe levels hu),
      CRedTy.refl (CIsType.head_of_universe levels hv), hu, hv, .single (.inr c)⟩

include levels sound in
/-- **Validity of subtyping of dependent function types.** At a type token of the smaller
type: its tag relates the two as dependent function types with equal domains and usable
codomains; a domain token relates the domains by their equation; a family entry puts the
codomains at an argument related to itself in the subtyping mode, by the codomains'
subtyping statement. -/
theorem CStatement.Valid.subPi {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A A' : CTm Head n} {B B' : CTm Head (n + 1)} {u u' w : Head}
    (hPi : (CStatement.typing Γ (.pi A B) (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (hPi' : (CStatement.typing Γ (.pi A' B') (.head u')).Valid Rd H) (hu' : R.isUniverse u')
    (hA : (CStatement.equality Γ A A' (.head w)).Valid Rd H) (hw : R.isUniverse w)
    (hB : (CStatement.sub (.snoc Γ A) B B').Valid Rd H)
    (tPi : CTyped P Γ (.pi A B) (.head u)) (tPi' : CTyped P Γ (.pi A' B') (.head u'))
    (eA : CEqual P Γ A A' (.head w)) (leB : CBelow P (.snoc Γ A) B B') :
    (CStatement.sub Γ (.pi A B) (.pi A' B')).Valid Rd H := by
  refine ⟨hPi.1.adequateType levels sound hu, hPi'.1.adequateType levels sound hu',
    fun ρ fits m Δ σ formed' hσ r hr hrU => ?_⟩
  obtain ⟨tA, -⟩ := CEqual.typed levels eA formed
  have hAty : AdequateType Rd H Γ A := hA.1.1.adequateType levels sound hw
  have piSub : PiSub H Δ ((CTm.pi A B).subst σ) ((CTm.pi A' B').subst σ) (A.subst σ)
      (B.subst (CTm.liftSub σ)) (A'.subst σ) (B'.subst (CTm.liftSub σ)) :=
    ⟨CRedTy.refl ⟨u, hu, tPi.substitute hσ.1.1⟩,
      CRedTy.refl ⟨u', hu', tPi'.substitute hσ.1.1⟩,
      ⟨w, hw, eA.substitute hσ.1.1⟩, leB.substitute (hσ.1.1.lift A)⟩
  have crossA : ∀ q, (cinterp Rd A ρ).Mem q → TyTok Elem.univ q →
      RT H Δ false q (A.subst σ) (A.subst σ) (A'.subst σ) := fun q hq hqU =>
    RT.toType (typeKind_of_tyTok_univ hqU) (CRedTy.refl (CIsType.head_of_universe levels hw))
      (hA.1.2.2 ρ fits formed' hσ q hq (sound.typedAt_head hw ρ hqU))
  have hG := cinterp_cont_cons Rd B ρ
  have hF : Ideal.Monotone fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    hG.mono (Ideal.projT_mono (principal_mono h))
  rcases typed_former_token (.inl rfl) hF hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
    ⟨C, X, Y, rfl, hCA, hYF, hC, -, hY⟩
  · exact RTSub.of_vacuous hvac
  · exact RTSub.pi_iff.2 ⟨_, _, _, _, piSub⟩
  · exact RTSub.argPi_iff.2 (.inr ⟨_, _, _, _, piSub, fun c hc => absurd hc List.not_mem_nil,
      fun _ => crossA d hd hdU⟩)
  · have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
      ⟨fits, sound.typeGenerated_of_head hw tA fits, Ideal.projT_projT _ _⟩
    refine RTSub.fnPi_iff.2 (.inr ⟨_, _, _, _, piSub, fun c hc => crossA c (hCA c hc) (hC c hc),
      fun N tN hNX y hy => ?_⟩)
    have hsub : SubstRel Rd H (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ
        (CTm.consSub N σ) (CTm.consSub N σ) :=
      SubstRel.cons levels formed' hσ (.refl tN) ⟨w, hw, .refl (tA.substitute hσ.1.1)⟩
        (fun q hq hqU => hAty ρ fits formed' hσ q hq hqU)
        (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
    rw [CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub]
    exact hB.2.2 _ fits' formed' hsub y (hYF y hy) (hY y hy)

include levels sound in
/-- **Validity of subtyping of dependent pair types.** At a type token of the smaller type:
its tag relates the two as dependent pair types with usable components; a domain token
puts the domains in the subtyping mode; a family entry is also an entry of the larger
type, which the two types denote alike, so the larger family's adequacy relates it at
related arguments of the larger domain, and the families' subtyping statement puts the
two families at an argument in the subtyping mode. -/
theorem CStatement.Valid.subSigma (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n}
    {A A' : CTm Head n} {B B' : CTm Head (n + 1)} {u u' : Head}
    (hS : (CStatement.typing Γ (.sigma A B) (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (hS' : (CStatement.typing Γ (.sigma A' B') (.head u')).Valid Rd H) (hu' : R.isUniverse u')
    (hA : (CStatement.sub Γ A A').Valid Rd H) (hB : (CStatement.sub (.snoc Γ A) B B').Valid Rd H)
    (tS : CTyped P Γ (.sigma A B) (.head u)) (tS' : CTyped P Γ (.sigma A' B') (.head u'))
    (leA : CBelow P Γ A A') (leB : CBelow P (.snoc Γ A) B B') :
    (CStatement.sub Γ (.sigma A B) (.sigma A' B')).Valid Rd H := by
  have hS'ty : AdequateType Rd H Γ (.sigma A' B') := hS'.1.adequateType levels sound hu'
  have hB'ty : AdequateType Rd H (.snoc Γ A') B' := hS'ty.sigma_cod levels
  refine ⟨hS.1.adequateType levels sound hu, hS'ty,
    fun ρ fits m Δ σ formed' hσ r hr hrU => ?_⟩
  obtain ⟨⟨wA, hwA, tA⟩, -⟩ := CIsType.sigma_parts ⟨u, hu, tS⟩
  obtain ⟨⟨wA', hwA', tA'⟩, -⟩ := CIsType.sigma_parts ⟨u', hu', tS'⟩
  have sigSub : SigmaSub H Δ ((CTm.sigma A B).subst σ) ((CTm.sigma A' B').subst σ) (A.subst σ)
      (B.subst (CTm.liftSub σ)) (A'.subst σ) (B'.subst (CTm.liftSub σ)) :=
    ⟨CRedTy.refl ⟨u, hu, tS.substitute hσ.1.1⟩,
      CRedTy.refl ⟨u', hu', tS'.substitute hσ.1.1⟩,
      leA.substitute hσ.1.1, leB.substitute (hσ.1.1.lift A)⟩
  have hSame : cinterp Rd (.sigma A B) ρ = cinterp Rd (.sigma A' B') ρ :=
    CBelow.sound valid (.subSigma tS hu tS' hu' leA leB) fits
  have hG := cinterp_cont_cons Rd B ρ
  have hF : Ideal.Monotone fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    hG.mono (Ideal.projT_mono (principal_mono h))
  have hG' := cinterp_cont_cons Rd B' ρ
  have hF' : Ideal.Monotone fun X =>
      cinterp Rd B' (Env.cons (projT (cinterp Rd A' ρ) (principal X)) ρ) := fun h =>
    hG'.mono (Ideal.projT_mono (principal_mono h))
  rcases typed_former_token (.inr rfl) hF hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
    ⟨C, X, Y, rfl, hCA, hYF, hC, -, hY⟩
  · exact RTSub.of_vacuous hvac
  · exact RTSub.sigma_iff.2 ⟨_, _, _, _, sigSub⟩
  · exact RTSub.argSigma_iff.2 (.inr ⟨_, _, _, _, sigSub, fun c hc => absurd hc List.not_mem_nil,
      fun _ => hA.2.2 ρ fits formed' hσ d hd hdU⟩)
  · have hr' : (cinterp Rd (.sigma A' B') ρ).Mem (.fn .sigma C X Y) := by
      rw [← hSame]
      exact hr
    have hYF' := ((Ideal.mem_former_fn hF').1 hr').2
    refine RTSub.fnSigma_iff.2 (.inr ⟨_, _, _, _, sigSub,
      fun c hc => hA.2.2 ρ fits formed' hσ c (hCA c hc) (hC c hc), fun N N' hNN hNX y hy => ?_,
      fun N tN hNX y hy => ?_⟩)
    · have fits' : Fits Rd (.snoc Γ A') (Env.cons (projT (cinterp Rd A' ρ) (principal X)) ρ) :=
        ⟨fits, sound.typeGenerated_of_head hwA' tA' fits, Ideal.projT_projT _ _⟩
      have hsub : SubstRel Rd H (.snoc Γ A') (Env.cons (projT (cinterp Rd A' ρ) (principal X)) ρ)
          Δ (CTm.consSub N σ) (CTm.consSub N' σ) :=
        SubstRel.cons levels formed' hσ hNN ⟨wA', hwA', .refl (tA'.substitute hσ.1.1)⟩
          (fun q hq hqU => hA.2.1 ρ fits formed' hσ q hq hqU)
          (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
      simp only [CTm.inst0_subst_liftSub]
      exact hB'ty _ fits' formed' hsub y (hYF' y hy) (hY y hy)
    · have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
        ⟨fits, sound.typeGenerated_of_head hwA tA fits, Ideal.projT_projT _ _⟩
      have hsub : SubstRel Rd H (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ
          (CTm.consSub N σ) (CTm.consSub N σ) :=
        SubstRel.cons levels formed' hσ (.refl tN) ⟨wA, hwA, .refl (tA.substitute hσ.1.1)⟩
          (fun q hq hqU => hA.1 ρ fits formed' hσ q hq hqU)
          (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
      rw [CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub]
      exact hB.2.2 _ fits' formed' hsub y (hYF y hy) (hY y hy)

include levels in
/-- **Validity of the transitivity of subtyping** (`RTSub.trans`): the two lower types
denote alike. -/
theorem CStatement.Valid.subTrans (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n}
    {A B C : CTm Head n} (h₁ : (CStatement.sub Γ A B).Valid Rd H)
    (h₂ : (CStatement.sub Γ B C).Valid Rd H) (le₁ : CBelow P Γ A B) :
    (CStatement.sub Γ A C).Valid Rd H := by
  refine ⟨h₁.1, h₂.2.1, fun ρ fits m Δ σ formed' hσ r hr hrU => ?_⟩
  have hr' : (cinterp Rd B ρ).Mem r := by
    rw [← CBelow.sound valid le₁ fits]
    exact hr
  exact RTSub.trans levels formed' hrU (h₁.2.2 ρ fits formed' hσ r hr hrU)
    (h₂.2.2 ρ fits formed' hσ r hr' hrU)

end Subtyping

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
