import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.PairTokens

/-!
# The relation at dependent pair types: η and the compatibility of the pair rules

**η in the relation.** At a type reducing to a dependent pair type the relation reads
only the projections, and the projections of `(fst M, snd M)` reduce to those of `M`
by one head step each. So a term related to `M'` is related to `(fst M', snd M')`
(`RT.eta_right`), and `(fst M, snd M)` is related to what `M` is related to
(`RT.eta_left`).

**Compatibility with the pair rules.** The typed tokens of an element of a dependent
pair type are its component tokens (`Ideal.typed_pair_token`), so adequacy at a
dependent pair type is adequacy of the components:

* **the first projection** (`Adequate.fst`): a typed token of the first projection of a
  term is the component of a typed first-projection token of the term;
* **the second projection** (`Adequate.snd`): a typed token of the second projection is
  the component of a typed second-projection token whose dependency is a finite typed
  part of the first projection, and the clause at the first projection itself gives
  the relation at the family's value there;
* **pair introduction** (`Adequate.pair`): the projections of the two pairs reduce to
  the components, and head expansion moves the components' relation to them; the
  second components are moved from the family at the first component to the family
  at every term with a common reduct with it, along the dependent pair type related to
  itself;
* **η** (`AdequateEq.etaSigma`): the typed tokens of the left term are component
  tokens, at which the equations of the projections relate the two terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypedAt)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## η in the relation -/

section Eta

variable {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
  (formed : CCtxFormed P Γ)

include levels formed in
/-- **η on the right**: at a type reducing to a dependent pair type, a term related to
`M'` is related to the pair of the projections of `M'`. -/
theorem RT.eta_right {t : Tok} {T D M M' : CTm Head n} {E : CTm Head (n + 1)}
    (hT : CRedTy H Γ T (.sigma D E)) (tM : CTyped P Γ M T) (tM' : CTyped P Γ M' T)
    (h : RT H Γ true t T M M') : RT H Γ true t T M (.pair (.fst M') (.snd M')) := by
  obtain ⟨u, hu, tS⟩ := (CTypeEq.isType levels hT.2 formed).2
  have hE : CIsType P (.snoc Γ D) E := (CIsType.sigma_parts ⟨u, hu, tS⟩).2
  have tMS : CTyped P Γ M (.sigma D E) := tM.convType hT.2
  have tM'S : CTyped P Γ M' (.sigma D E) := tM'.convType hT.2
  have tfst : CTyped P Γ (.fst M) D := .fstElim tMS
  have tfst' : CTyped P Γ (.fst M') D := .fstElim tM'S
  have redFst : CRedTm H Γ (.fst (.pair (.fst M') (.snd M'))) (.fst M') D :=
    ⟨.single (H.fstPair _ _), .betaFst tS hu tfst' (.sndElim tM'S)⟩
  have key : ∀ {D₁ : CTm Head n} {E₁ : CTm Head (n + 1)}, CRedTy H Γ T (.sigma D₁ E₁) →
      D₁ = D ∧ E₁ = E := fun h₁ => CRedTy.sigma_align hT h₁
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases htk : typeKind t.kind with
  | true =>
      rcases (RT.tm_type_iff htk).1 h with hvac | ⟨_, _, hU, _⟩ | ⟨hP, _⟩
      · exact RT.of_vacuous hvac
      · exact absurd (CRedTy.nf_unique hT hU (H.normal_sigma _ _) (H.normal_head _)) nofun
      · exact absurd (CRedTy.nf_unique hT hP (H.normal_sigma _ _) H.normal_prop) nofun
  | false =>
  cases t with
  | tag k =>
      cases k
      case zero =>
        exact absurd (CRedTy.nf_unique hT (RT.tm_zero_iff.1 h).1 (H.normal_sigma _ _)
          H.normal_num) nofun
      case succ =>
        obtain ⟨m, m', hs⟩ := RT.tm_succTag_iff.1 h
        exact absurd (CRedTy.nf_unique hT hs.1 (H.normal_sigma _ _) H.normal_num) nofun
      case refl =>
        obtain ⟨B, x, y, r, r', hr⟩ := RT.tm_reflTag_iff.1 h
        exact absurd (CRedTy.nf_unique hT hr.1 (H.normal_sigma _ _) (H.normal_id _ _ _)) nofun
      case pair =>
        refine RT.tm_pairTag_iff.2 fun D₁ E₁ hT₁ => ?_
        obtain ⟨e₁, e₂⟩ := key hT₁
        subst D₁ E₁
        exact .trans (RT.tm_pairTag_iff.1 h D E hT) (.symm redFst.2)
      case ctor d c fs =>
        obtain ⟨ms, ms', hs⟩ := RT.tm_ctorTag_iff.1 h
        exact absurd (CRedTy.nf_unique hT hs.2.1 (H.normal_sigma _ _)
          (H.normal_data (K.ctor_data hs.1))) nofun
      all_goals
        exact RT.tm_other htk (fun _ _ _ e => nomatch e) nofun nofun nofun nofun
          (fun _ _ _ e => nomatch e)
  | arg k i C d =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
      · exact RT.tm_other htk (fun _ _ _ e => nomatch e) nofun
          (fun e => nomatch e) nofun nofun (fun _ _ _ e => nomatch e)
      · obtain ⟨B, x, y, r, r', hr⟩ := RT.tm_refl_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hr.1 (H.normal_sigma _ _) (H.normal_id _ _ _)) nofun
      · obtain ⟨m, m', hs⟩ := RT.tm_succ_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.1 (H.normal_sigma _ _) H.normal_num) nofun
      · rcases RT.tm_argPair_iff.1 h with hvac | hcl
        · exact RT.of_vacuous hvac
        refine RT.tm_argPair_iff.2 (.inr fun D₁ E₁ hT₁ => ?_)
        obtain ⟨e₁, e₂⟩ := key hT₁
        subst D₁ E₁
        obtain ⟨e₀, hC, h0, h1⟩ := hcl D E hT
        refine ⟨.trans e₀ (.symm redFst.2),
          fun c hc => RT.expand levels formed (CRedTm.refl tfst) redFst (hC c hc),
          fun hi => RT.expand levels formed (CRedTm.refl tfst) redFst (h0 hi),
          fun hi N Q hQ hNQ => ?_⟩
        have eN : CEqual P Γ (.fst M) N D := .trans hQ.2 (.symm hNQ.2)
        have eN' : CEqual P Γ (.fst M') N D := .trans (.symm e₀) eN
        have redSnd : CRedTm H Γ (.snd (.pair (.fst M') (.snd M'))) (.snd M') (CTm.inst0 N E) :=
          ⟨.single (H.sndPair _ _), CEqual.convType (.betaSnd tS hu tfst' (.sndElim tM'S))
            (hE.instantiateEq tfst' eN')⟩
        have tsnd : CTyped P Γ (.snd M) (CTm.inst0 N E) :=
          CTyped.convType (.sndElim tMS) (hE.instantiateEq tfst eN)
        exact RT.expand levels formed (CRedTm.refl tsnd) redSnd (h1 hi N Q hQ hNQ)
      · obtain ⟨ms, ms', hs⟩ := RT.tm_ctor_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.2.1 (H.normal_sigma _ _)
          (H.normal_data (K.ctor_data hs.1))) nofun
      · exact RT.tm_other htk (fun _ _ _ e => nomatch e) hk.2.1
          (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
  | fn k C X Y =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
      · exact RT.tm_lam_iff.2 (.inr fun D₁ E₁ hpi =>
          absurd (CRedTy.nf_unique hT hpi (H.normal_sigma _ _) (H.normal_pi _ _)) nofun)
      · obtain ⟨B, x, y, r, r', hr⟩ := RT.tm_refl_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hr.1 (H.normal_sigma _ _) (H.normal_id _ _ _)) nofun
      · obtain ⟨m, m', hs⟩ := RT.tm_succ_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.1 (H.normal_sigma _ _) H.normal_num) nofun
      · rcases RT.tm_fnPair_iff.1 h with hvac | hcl
        · exact RT.of_vacuous hvac
        refine RT.tm_fnPair_iff.2 (.inr fun D₁ E₁ hT₁ => ?_)
        obtain ⟨e₁, e₂⟩ := key hT₁
        subst D₁ E₁
        obtain ⟨e₀, hC⟩ := hcl D E hT
        exact ⟨.trans e₀ (.symm redFst.2),
          fun c hc => RT.expand levels formed (CRedTm.refl tfst) redFst (hC c hc)⟩
      · obtain ⟨ms, ms', hs⟩ := RT.tm_ctor_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.2.1 (H.normal_sigma _ _)
          (H.normal_data (K.ctor_data hs.1))) nofun
      · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
          (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

include levels formed in
/-- **η on the left**: at a type reducing to a dependent pair type, the pair of the
projections of `M` is related to what `M` is related to. -/
theorem RT.eta_left {t : Tok} {T D M M' : CTm Head n} {E : CTm Head (n + 1)}
    (hT : CRedTy H Γ T (.sigma D E)) (tM : CTyped P Γ M T) (tM' : CTyped P Γ M' T)
    (h : RT H Γ true t T M M') : RT H Γ true t T (.pair (.fst M) (.snd M)) M' := by
  obtain ⟨u, hu, tS⟩ := (CTypeEq.isType levels hT.2 formed).2
  have hE : CIsType P (.snoc Γ D) E := (CIsType.sigma_parts ⟨u, hu, tS⟩).2
  have tMS : CTyped P Γ M (.sigma D E) := tM.convType hT.2
  have tM'S : CTyped P Γ M' (.sigma D E) := tM'.convType hT.2
  have tfst : CTyped P Γ (.fst M) D := .fstElim tMS
  have tfst' : CTyped P Γ (.fst M') D := .fstElim tM'S
  have redFst : CRedTm H Γ (.fst (.pair (.fst M) (.snd M))) (.fst M) D :=
    ⟨.single (H.fstPair _ _), .betaFst tS hu tfst (.sndElim tMS)⟩
  have key : ∀ {D₁ : CTm Head n} {E₁ : CTm Head (n + 1)}, CRedTy H Γ T (.sigma D₁ E₁) →
      D₁ = D ∧ E₁ = E := fun h₁ => CRedTy.sigma_align hT h₁
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases htk : typeKind t.kind with
  | true =>
      rcases (RT.tm_type_iff htk).1 h with hvac | ⟨_, _, hU, _⟩ | ⟨hP, _⟩
      · exact RT.of_vacuous hvac
      · exact absurd (CRedTy.nf_unique hT hU (H.normal_sigma _ _) (H.normal_head _)) nofun
      · exact absurd (CRedTy.nf_unique hT hP (H.normal_sigma _ _) H.normal_prop) nofun
  | false =>
  cases t with
  | tag k =>
      cases k
      case zero =>
        exact absurd (CRedTy.nf_unique hT (RT.tm_zero_iff.1 h).1 (H.normal_sigma _ _)
          H.normal_num) nofun
      case succ =>
        obtain ⟨m, m', hs⟩ := RT.tm_succTag_iff.1 h
        exact absurd (CRedTy.nf_unique hT hs.1 (H.normal_sigma _ _) H.normal_num) nofun
      case refl =>
        obtain ⟨B, x, y, r, r', hr⟩ := RT.tm_reflTag_iff.1 h
        exact absurd (CRedTy.nf_unique hT hr.1 (H.normal_sigma _ _) (H.normal_id _ _ _)) nofun
      case pair =>
        refine RT.tm_pairTag_iff.2 fun D₁ E₁ hT₁ => ?_
        obtain ⟨e₁, e₂⟩ := key hT₁
        subst D₁ E₁
        exact .trans redFst.2 (RT.tm_pairTag_iff.1 h D E hT)
      case ctor d c fs =>
        obtain ⟨ms, ms', hs⟩ := RT.tm_ctorTag_iff.1 h
        exact absurd (CRedTy.nf_unique hT hs.2.1 (H.normal_sigma _ _)
          (H.normal_data (K.ctor_data hs.1))) nofun
      all_goals
        exact RT.tm_other htk (fun _ _ _ e => nomatch e) nofun nofun nofun nofun
          (fun _ _ _ e => nomatch e)
  | arg k i C d =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
      · exact RT.tm_other htk (fun _ _ _ e => nomatch e) nofun
          (fun e => nomatch e) nofun nofun (fun _ _ _ e => nomatch e)
      · obtain ⟨B, x, y, r, r', hr⟩ := RT.tm_refl_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hr.1 (H.normal_sigma _ _) (H.normal_id _ _ _)) nofun
      · obtain ⟨m, m', hs⟩ := RT.tm_succ_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.1 (H.normal_sigma _ _) H.normal_num) nofun
      · rcases RT.tm_argPair_iff.1 h with hvac | hcl
        · exact RT.of_vacuous hvac
        refine RT.tm_argPair_iff.2 (.inr fun D₁ E₁ hT₁ => ?_)
        obtain ⟨e₁, e₂⟩ := key hT₁
        subst D₁ E₁
        obtain ⟨e₀, hC, h0, h1⟩ := hcl D E hT
        refine ⟨.trans redFst.2 e₀,
          fun c hc => RT.expand levels formed redFst (CRedTm.refl tfst') (hC c hc),
          fun hi => RT.expand levels formed redFst (CRedTm.refl tfst') (h0 hi),
          fun hi N Q hQ hNQ => ?_⟩
        -- a term with a common reduct with the pair's first projection has one with `fst M`
        obtain ⟨Q', hQ', hNQ'⟩ := CRedTm.join_of_red redFst hQ hNQ
        have eN : CEqual P Γ (.fst M) N D := .trans hQ'.2 (.symm hNQ'.2)
        have eN' : CEqual P Γ (.fst M') N D := .trans (.symm e₀) eN
        have redSnd : CRedTm H Γ (.snd (.pair (.fst M) (.snd M))) (.snd M) (CTm.inst0 N E) :=
          ⟨.single (H.sndPair _ _), CEqual.convType (.betaSnd tS hu tfst (.sndElim tMS))
            (hE.instantiateEq tfst eN)⟩
        have tsnd' : CTyped P Γ (.snd M') (CTm.inst0 N E) :=
          CTyped.convType (.sndElim tM'S) (hE.instantiateEq tfst' eN')
        exact RT.expand levels formed redSnd (CRedTm.refl tsnd') (h1 hi N Q' hQ' hNQ')
      · obtain ⟨ms, ms', hs⟩ := RT.tm_ctor_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.2.1 (H.normal_sigma _ _)
          (H.normal_data (K.ctor_data hs.1))) nofun
      · exact RT.tm_other htk (fun _ _ _ e => nomatch e) hk.2.1
          (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
  | fn k C X Y =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
      · exact RT.tm_lam_iff.2 (.inr fun D₁ E₁ hpi =>
          absurd (CRedTy.nf_unique hT hpi (H.normal_sigma _ _) (H.normal_pi _ _)) nofun)
      · obtain ⟨B, x, y, r, r', hr⟩ := RT.tm_refl_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hr.1 (H.normal_sigma _ _) (H.normal_id _ _ _)) nofun
      · obtain ⟨m, m', hs⟩ := RT.tm_succ_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.1 (H.normal_sigma _ _) H.normal_num) nofun
      · rcases RT.tm_fnPair_iff.1 h with hvac | hcl
        · exact RT.of_vacuous hvac
        refine RT.tm_fnPair_iff.2 (.inr fun D₁ E₁ hT₁ => ?_)
        obtain ⟨e₁, e₂⟩ := key hT₁
        subst D₁ E₁
        obtain ⟨e₀, hC⟩ := hcl D E hT
        exact ⟨.trans redFst.2 e₀,
          fun c hc => RT.expand levels formed redFst (CRedTm.refl tfst') (hC c hc)⟩
      · obtain ⟨ms, ms', hs⟩ := RT.tm_ctor_shape rfl hv h
        exact absurd (CRedTy.nf_unique hT hs.2.1 (H.normal_sigma _ _)
          (H.normal_data (K.ctor_data hs.1))) nofun
      · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
          (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

end Eta

/-! ## Compatibility with the pair rules -/

section Compatibility

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels in
/-- **The first projection.** -/
theorem Adequate.fst {n : Nat} {Γ : CCtx Head n} {p A : CTm Head n} {B : CTm Head (n + 1)}
    (hp : Adequate Rd H Γ p (.sigma A B)) (tp : CTyped P Γ p (.sigma A B)) :
    Adequate Rd H Γ (.fst p) A := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsA
  obtain ⟨hmem, hty⟩ := Ideal.typed_fst_token (cinterp_cont_cons Rd B ρ) hs hsA
  have sigType : CIsType P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    CTyped.isType levels (tp.substitute hσ.1.1) formed
  rcases RT.tm_argPair_iff.1 (hp ρ fits formed hσ _ hmem hty) with hvac | hcl
  · exact RT.of_vacuous (vacuous_arg hvac)
  · exact (hcl _ _ (CRedTy.refl sigType)).2.2.1 rfl

include levels sound in
/-- **The second projection.** -/
theorem Adequate.snd {n : Nat} {Γ : CCtx Head n} {p A : CTm Head n} {B : CTm Head (n + 1)}
    (hp : Adequate Rd H Γ p (.sigma A B)) (tp : CTyped P Γ p (.sigma A B)) :
    Adequate Rd H Γ (.snd p) (CTm.inst0 (.fst p) B) := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsT
  rw [CTm.subst_inst0]
  rw [cinterp_inst0] at hsT
  obtain ⟨w, hmem, hty⟩ := Ideal.typed_snd_token (cinterp_cont_cons Rd B ρ)
    (sound.typing tp ρ fits).2 hs hsT
  have sigType : CIsType P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    CTyped.isType levels (tp.substitute hσ.1.1) formed
  rcases RT.tm_argPair_iff.1 (hp ρ fits formed hσ _ hmem hty) with hvac | hcl
  · exact RT.of_vacuous (vacuous_arg hvac)
  obtain ⟨e₀, -, -, h1⟩ := hcl _ _ (CRedTy.refl sigType)
  have tfst := (CEqual.typed levels e₀ formed).1
  exact h1 rfl _ _ (CRedTm.refl tfst) (CRedTm.refl tfst)

include levels sound in
/-- **Pair introduction.** A typed token of a pair is a component token. The
projections of the two substituted pairs reduce to the components, which are related
by the components' adequacy; the second components are moved from the family at the
first component to the family at a term with a common reduct with it along the
dependent pair type, related to itself as far as the token's type witness observes. -/
theorem Adequate.pair {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n} {B : CTm Head (n + 1)}
    {u : Head} (hu : R.isUniverse u) (hS : Adequate Rd H Γ (.sigma A B) (.head u))
    (ha : Adequate Rd H Γ a A) (hb : Adequate Rd H Γ b (CTm.inst0 a B))
    (tS : CTyped P Γ (.sigma A B) (.head u)) (ta : CTyped P Γ a A)
    (tb : CTyped P Γ b (CTm.inst0 a B)) : Adequate Rd H Γ (.pair a b) (.sigma A B) := by
  intro ρ fits m Δ σ σ' formed hσ t ht htT
  obtain ⟨c₀, hc₀, hc₀u, hc₀t⟩ := htT
  have hG := cinterp_cont_cons Rd B ρ
  have taSem : projT (cinterp Rd A ρ) (cinterp Rd a ρ) = cinterp Rd a ρ := (sound.typing ta ρ fits).2
  have hfst : Ideal.fst (cinterp Rd (.pair a b) ρ) = cinterp Rd a ρ := Ideal.fst_pair _ _
  have hsnd : Ideal.snd (cinterp Rd (.pair a b) ρ) = cinterp Rd b ρ := Ideal.snd_pair _ _
  have hσ' := hσ.symm levels formed
  -- the substituted typings
  have tSσ : CTyped P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) (.head u) :=
    tS.substitute hσ.1.1
  have tSσ' : CTyped P Δ (.sigma (A.subst σ') (B.subst (CTm.liftSub σ'))) (.head u) :=
    tS.substitute hσ'.1.1
  have taσ : CTyped P Δ (a.subst σ) (A.subst σ) := ta.substitute hσ.1.1
  have taσ' : CTyped P Δ (a.subst σ') (A.subst σ') := ta.substitute hσ'.1.1
  have tbσ : CTyped P Δ (b.subst σ) (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ))) := by
    have h := tb.substitute hσ.1.1
    rwa [CTm.subst_inst0] at h
  have tbσ' : CTyped P Δ (b.subst σ') (CTm.inst0 (a.subst σ') (B.subst (CTm.liftSub σ'))) := by
    have h := tb.substitute hσ'.1.1
    rwa [CTm.subst_inst0] at h
  -- the domain and the family's value at the two substitutions
  obtain ⟨tA, tB⟩ := CIsType.sigma_parts ⟨u, hu, tS⟩
  obtain ⟨w, hw, tA⟩ := tA
  obtain ⟨v, hv, tB⟩ := tB
  have eA : CTypeEq P Δ (A.subst σ) (A.subst σ') := ⟨w, hw, CDerivable.functional tA hσ.1⟩
  have eaa : CEqual P Δ (a.subst σ) (a.subst σ') (A.subst σ) := CDerivable.functional ta hσ.1
  have eBa : CTypeEq P Δ (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ)))
      (CTm.inst0 (a.subst σ') (B.subst (CTm.liftSub σ'))) := by
    have h := CDerivable.functional tB (CSubstEq.cons hσ.1 taσ eaa)
    rw [← CTm.inst0_subst_liftSub, ← CTm.inst0_subst_liftSub] at h
    exact ⟨v, hv, h⟩
  -- the projections of the two pairs reduce to the components
  have fstσ : CRedTm H Δ (.fst (.pair (a.subst σ) (b.subst σ))) (a.subst σ) (A.subst σ) :=
    ⟨.single (H.fstPair _ _), .betaFst tSσ hu taσ tbσ⟩
  have fstσ' : CRedTm H Δ (.fst (.pair (a.subst σ') (b.subst σ'))) (a.subst σ') (A.subst σ) :=
    ⟨.single (H.fstPair _ _), CEqual.convType (.betaFst tSσ' hu taσ' tbσ') eA.symm⟩
  have sndσ : CRedTm H Δ (.snd (.pair (a.subst σ) (b.subst σ))) (b.subst σ)
      (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ))) :=
    ⟨.single (H.sndPair _ _), .betaSnd tSσ hu taσ tbσ⟩
  have sndσ' : CRedTm H Δ (.snd (.pair (a.subst σ') (b.subst σ'))) (b.subst σ')
      (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ))) :=
    ⟨.single (H.sndPair _ _), CEqual.convType (.betaSnd tSσ' hu taσ' tbσ') eBa.symm⟩
  have ePair : CEqual P Δ (.fst (.pair (a.subst σ) (b.subst σ)))
      (.fst (.pair (a.subst σ') (b.subst σ'))) (A.subst σ) :=
    .trans fstσ.2 (.trans eaa (.symm fstσ'.2))
  have sigType : CIsType P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) := ⟨u, hu, tSσ⟩
  -- the first components, related as far as a typed token observes
  have relA : ∀ {s : Tok}, (cinterp Rd a ρ).Mem s → TypedAt (cinterp Rd A ρ) s →
      RT H Δ true s (A.subst σ) (.fst (.pair (a.subst σ) (b.subst σ)))
        (.fst (.pair (a.subst σ') (b.subst σ'))) := fun hs hsA =>
    RT.expand levels formed fstσ fstσ' (ha ρ fits formed hσ _ hs hsA)
  have hdomBelow : Ideal.Below (args .sigma 0 c₀) (cinterp Rd A ρ) := Ideal.below_args_former hc₀
  have hdomTy : Ty (args .sigma 0 c₀) Elem.univ := Ideal.ty_args_dom (.inr rfl) hc₀u
  show RT H Δ true t (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
    (.pair (a.subst σ) (b.subst σ)) (.pair (a.subst σ') (b.subst σ'))
  rcases Ideal.typed_pair_token ht hc₀ hc₀t with ⟨s, rfl, hs, hsty⟩ |
    ⟨C, s, rfl, hC, hCty, hs, hsty⟩
  · rw [hfst] at hs
    refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
    have e := H.red_normal (H.normal_sigma _ _) hT.1
    injection e with _ eD eE
    subst eD eE
    exact ⟨ePair, fun _ h => absurd h List.not_mem_nil,
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
    have relB := hb ρ fits formed hσ s hs ⟨_, hfamBelow, hfamTy, hsty⟩
    rw [CTm.subst_inst0] at relB
    have relB' : RT H Δ true s (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ)))
        (.snd (.pair (a.subst σ) (b.subst σ))) (.snd (.pair (a.subst σ') (b.subst σ'))) :=
      RT.expand levels formed sndσ sndσ' relB
    -- the dependent pair type, related to itself as far as its witness observes
    have hSself : ∀ r ∈ c₀, RT H Δ false r (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
        (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
        (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) := fun r hr =>
      Adequate.toType levels sound hu hS fits formed hσ.left (hc₀ r hr) (hc₀u r hr)
    have hpS := RT.sigma_self hSself (tyTok_snd.1 hc₀t).1 (CRedTy.refl sigType)
    refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
    have e := H.red_normal (H.normal_sigma _ _) hT.1
    injection e with _ eD eE
    subst eD eE
    refine ⟨ePair, fun c hc => relA (hC c hc) (hCA c hc), fun h => absurd h (by decide),
      fun _ N Q hQ hNQ => ?_⟩
    obtain ⟨Q', haQ, hNQ'⟩ := CRedTm.join_of_red fstσ hQ hNQ
    have eaN : CEqual P Δ (a.subst σ) N (A.subst σ) := .trans haQ.2 (.symm hNQ'.2)
    have hNN : ∀ x ∈ C, RT H Δ true x (A.subst σ) (a.subst σ) N := fun x hx =>
      RT.retarget levels formed taσ (ha ρ fits formed hσ.left _ (hC x hx) (hCA x hx)) haQ hNQ'
    have hE : CIsType P (.snoc Δ (A.subst σ)) (B.subst (CTm.liftSub σ)) :=
      (CIsType.sigma_parts sigType).2
    exact (RT.conv_iff levels formed hfamTy hsty (RT.sigma_fam_at hpS hSself eaN hNN)
      (hE.instantiateEq taσ eaN)).1 relB'

include levels sound in
/-- **η for pairs.** The typed tokens of the left term are component tokens, at which
the equations of the projections relate the two terms; the second projections are
moved from the family at the first projection to the family at a term with a common
reduct with it along the dependent pair type, related to itself. -/
theorem AdequateEq.etaSigma {n : Nat} {Γ : CCtx Head n} {p q A : CTm Head n}
    {B : CTm Head (n + 1)} {u : Head} (hu : R.isUniverse u)
    (hS : Adequate Rd H Γ (.sigma A B) (.head u))
    (hp : Adequate Rd H Γ p (.sigma A B)) (hq : Adequate Rd H Γ q (.sigma A B))
    (hfst : AdequateEq Rd H Γ (.fst p) (.fst q) A)
    (hsnd : AdequateEq Rd H Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B))
    (tp : CTyped P Γ p (.sigma A B)) (efst : CEqual P Γ (.fst p) (.fst q) A) :
    AdequateEq Rd H Γ p q (.sigma A B) := by
  refine ⟨hp, hq, fun ρ fits m Δ σ formed hσ t ht htT => ?_⟩
  obtain ⟨c₀, hc₀, hc₀u, hc₀t⟩ := htT
  have hG := cinterp_cont_cons Rd B ρ
  have pSem : projT (cinterp Rd (.sigma A B) ρ) (cinterp Rd p ρ) = cinterp Rd p ρ :=
    (sound.typing tp ρ fits).2
  have fstSem : projT (cinterp Rd A ρ) (Ideal.fst (cinterp Rd p ρ)) =
      Ideal.fst (cinterp Rd p ρ) := Ideal.semTyped_fst hG pSem
  have hdomBelow : Ideal.Below (args .sigma 0 c₀) (cinterp Rd A ρ) := Ideal.below_args_former hc₀
  have hdomTy : Ty (args .sigma 0 c₀) Elem.univ := Ideal.ty_args_dom (.inr rfl) hc₀u
  have tpσ : CTyped P Δ (p.subst σ) (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    tp.substitute hσ.1.1
  have sigType : CIsType P Δ (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    CTyped.isType levels tpσ formed
  have efstσ : CEqual P Δ (.fst (p.subst σ)) (.fst (q.subst σ)) (A.subst σ) :=
    efst.substitute hσ.1.1
  show RT H Δ true t (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) (p.subst σ) (q.subst σ)
  rcases Ideal.typed_pair_token ht hc₀ hc₀t with ⟨s, rfl, hs, hsty⟩ |
    ⟨C, s, rfl, hC, hCty, hs, hsty⟩
  · refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
    have e := H.red_normal (H.normal_sigma _ _) hT.1
    injection e with _ eD eE
    subst eD eE
    exact ⟨efstσ, fun _ h => absurd h List.not_mem_nil,
      fun _ => hfst.2.2 ρ fits formed hσ s hs ⟨_, hdomBelow, hdomTy, hsty⟩,
      fun h => absurd h (by decide)⟩
  · have hCA : ∀ c ∈ C, TypedAt (cinterp Rd A ρ) c := fun c hc =>
      ⟨_, hdomBelow, hdomTy, hCty c hc⟩
    -- the second projection's type witness is below the family's value at the first
    have hfamBelow : Ideal.Below (fnApp .sigma c₀ C) (cinterp Rd (CTm.inst0 (.fst p) B) ρ) := by
      have h : Ideal.Below (fnApp .sigma c₀ C)
          (Ideal.fam .sigma (Ideal.csigma (cinterp Rd A ρ) fun y => cinterp Rd B (Env.cons y ρ))
            (Ideal.fst (cinterp Rd p ρ))) := Ideal.below_fam_fnApp hc₀ hC
      rw [Ideal.fam_csigma hG, fstSem] at h
      rw [cinterp_inst0]
      exact h
    have hfamTy : Ty (fnApp .sigma c₀ C) Elem.univ := Ideal.ty_fnApp (.inr rfl) hc₀u C
    have relB := hsnd.2.2 ρ fits formed hσ s hs ⟨_, hfamBelow, hfamTy, hsty⟩
    rw [CTm.subst_inst0] at relB
    -- the dependent pair type, related to itself as far as its witness observes
    have hSself : ∀ r ∈ c₀, RT H Δ false r (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
        (.sigma (A.subst σ) (B.subst (CTm.liftSub σ)))
        (.sigma (A.subst σ) (B.subst (CTm.liftSub σ))) := fun r hr =>
      Adequate.toType levels sound hu hS fits formed hσ (hc₀ r hr) (hc₀u r hr)
    have hpS := RT.sigma_self hSself (tyTok_snd.1 hc₀t).1 (CRedTy.refl sigType)
    have tfst : CTyped P Δ (.fst (p.subst σ)) (A.subst σ) := .fstElim tpσ
    refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
    have e := H.red_normal (H.normal_sigma _ _) hT.1
    injection e with _ eD eE
    subst eD eE
    refine ⟨efstσ, fun c hc => hfst.2.2 ρ fits formed hσ c (hC c hc) (hCA c hc),
      fun h => absurd h (by decide), fun _ N Q hQ hNQ => ?_⟩
    have eN : CEqual P Δ (.fst (p.subst σ)) N (A.subst σ) := .trans hQ.2 (.symm hNQ.2)
    have hNN : ∀ x ∈ C, RT H Δ true x (A.subst σ) (.fst (p.subst σ)) N := fun x hx =>
      RT.retarget levels formed tfst (hfst.1 ρ fits formed hσ x (hC x hx) (hCA x hx)) hQ hNQ
    have hE : CIsType P (.snoc Δ (A.subst σ)) (B.subst (CTm.liftSub σ)) :=
      (CIsType.sigma_parts sigType).2
    exact (RT.conv_iff levels formed hfamTy hsty (RT.sigma_fam_at hpS hSself eN hNN)
      (hE.instantiateEq tfst eN)).1 relB

end Compatibility

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
