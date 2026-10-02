import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Soundness

/-!
# Adequacy of the witness-indexed relation: compatibility lemmas

The relation of `LogicalRelation` is adequate for a typed term when, for every
environment fitting its context (`Fits`) and every pair of substitutions related
over that environment (`SubstRel`), the two substituted terms are related at the
substituted type as far as every token of the term's denotation typed at the
type's denotation observes (`Adequate`). An equation is adequate when both sides
are, and the two sides are related at one substitution (`AdequateEq`).

The facts of the domain interpretation used here are those of `SoundnessFacts`:
denotations of typed terms are elements of the denotations of their types, which
are type-generated; equal terms denote alike; and universes denote the universe.
Under them, and a formed context, this module proves the compatibility of the
relation with the rules

* conversion (`Adequate.conv`),
* application (`Adequate.app`), given the function type's adequacy at a universe,
* abstraction (`Adequate.lam`),
* the declared root computations (`AdequateEq.root`).

It also proves the extension of related substitutions by related terms
(`SubstRel.cons`), their left instance (`SubstRel.left`) and their symmetry
(`SubstRel.symm`).

**The identity eliminator.** An eliminator spine applied to a path that reduces to
`refl r` at `Id A x y` reduces to its method at the family's type at the path, given
its root step and the typing of the method under the equations `r ≡ x`, `r ≡ y`
(`CRedTm.eliminator`). So eliminator spines whose paths are related at the
reflexivity tag are related wherever their methods are (`RT.eliminator`). The
motive's instances `M x (refl x)` and `M y p` are related as types as far as an
entry of the motive observes whose inputs are observed through the point tokens
of the path, at a witness of those tokens at which the carrier is related to itself
(`RT.motive_reflPoint`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypedAt TypeGenerated principal univIdeal)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## Substitutions extended by one term -/

namespace CTm

/-- The substitution sending the newest variable to `N` and the others along `σ`. -/
def consSub {n m : Nat} (N : CTm Head m) (σ : CSub Head n m) : CSub Head (n + 1) m :=
  Fin.cases N σ

@[simp] theorem consSub_zero {n m : Nat} (N : CTm Head m) (σ : CSub Head n m) :
    consSub N σ 0 = N := rfl

@[simp] theorem consSub_succ {n m : Nat} (N : CTm Head m) (σ : CSub Head n m) (i : Fin n) :
    consSub N σ i.succ = σ i := rfl

/-- A weakened term under an extended substitution. -/
@[simp] theorem subst_consSub_wk {n m : Nat} (N : CTm Head m) (σ : CSub Head n m)
    (t : CTm Head n) : (t.rename wk).subst (consSub N σ) = t.subst σ := by
  rw [subst_rename]
  rfl

/-- Opening a substituted binder at `N` is substituting the extended substitution. -/
theorem inst0_subst_liftSub {n m : Nat} (N : CTm Head m) (σ : CSub Head n m)
    (B : CTm Head (n + 1)) : CTm.inst0 N (B.subst (liftSub σ)) = B.subst (consSub N σ) := by
  unfold inst0
  rw [subst_comp]
  apply subst_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact inst0_rename_wk N (σ j)

end CTm

section Substitutions

variable {P : ChurchRules R}

/-- Extending equal substitutions by equal terms at the type of the new variable. -/
theorem CSubstEq.cons {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m} {σ τ : CSub Head n m}
    {A : CTm Head n} {N N' : CTm Head m} (equal : CSubstEq P Γ Δ σ τ)
    (typed : CTyped P Δ N (A.subst σ)) (e : CEqual P Δ N N' (A.subst σ)) :
    CSubstEq P (.snoc Γ A) Δ (CTm.consSub N σ) (CTm.consSub N' τ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [CCtx.lookup_snoc_zero, CTm.subst_consSub_wk, CTm.consSub_zero] using typed
    · simpa only [CCtx.lookup_snoc_succ, CTm.subst_consSub_wk, CTm.consSub_succ] using equal.1 j
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [CCtx.lookup_snoc_zero, CTm.subst_consSub_wk, CTm.consSub_zero] using e
    · simpa only [CCtx.lookup_snoc_succ, CTm.subst_consSub_wk, CTm.consSub_succ] using equal.2 j

end Substitutions

/-! ## Related substitutions and adequacy -/

section Definitions

variable (Rd : Reading Head) {P : ChurchRules R} {K : RigidTypes P} (H : HeadReduction P K)

/-- **Related substitutions** over an environment: equal substitutions, sending
each variable's type to equal types related as far as its denotation's type
tokens observe, and each variable to terms related as far as the typed tokens of
its value observe. -/
def SubstRel {n m : Nat} (Γ : CCtx Head n) (ρ : Env n) (Δ : CCtx Head m)
    (σ σ' : CSub Head n m) : Prop :=
  CSubstEq P Γ Δ σ σ' ∧ ∀ i : Fin n,
    CTypeEq P Δ ((Γ.lookup i).subst σ) ((Γ.lookup i).subst σ') ∧
    (∀ r, (cinterp Rd (Γ.lookup i) ρ).Mem r → TyTok Elem.univ r →
      RT H Δ false r ((Γ.lookup i).subst σ) ((Γ.lookup i).subst σ) ((Γ.lookup i).subst σ')) ∧
    ∀ s, (ρ i).Mem s → TypedAt (cinterp Rd (Γ.lookup i) ρ) s →
      RT H Δ true s ((Γ.lookup i).subst σ) (σ i) (σ' i)

/-- **Adequacy of a typing**: in every environment fitting the context, related
substitutions send the term to terms related at the substituted type, as far as
every token of its denotation typed at the type's denotation observes. -/
def Adequate {n : Nat} (Γ : CCtx Head n) (t A : CTm Head n) : Prop :=
  ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ σ' : CSub Head n m}, CCtxFormed P Δ →
    SubstRel Rd H Γ ρ Δ σ σ' → ∀ s, (cinterp Rd t ρ).Mem s → TypedAt (cinterp Rd A ρ) s →
      RT H Δ true s (A.subst σ) (t.subst σ) (t.subst σ')

/-- **Adequacy of an equation**: both sides are adequate, and one substitution
sends the two sides to related terms. -/
def AdequateEq {n : Nat} (Γ : CCtx Head n) (a b A : CTm Head n) : Prop :=
  Adequate Rd H Γ a A ∧ Adequate Rd H Γ b A ∧
    ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m}, CCtxFormed P Δ →
      SubstRel Rd H Γ ρ Δ σ σ → ∀ s, (cinterp Rd a ρ).Mem s → TypedAt (cinterp Rd A ρ) s →
        RT H Δ true s (A.subst σ) (a.subst σ) (b.subst σ)

end Definitions

/-! ## Type tokens, and the universes -/

/-- A type token is of a type kind. -/
theorem typeKind_of_tyTok_univ {t : Tok} (ht : TyTok Elem.univ t) : typeKind t.kind = true := by
  have nmem : ∀ {k : Kind}, k ≠ .univ → Tok.tag k ∉ Elem.univ := fun hk h =>
    hk (Tok.tag.inj (List.mem_singleton.1 h))
  cases t with
  | tag k =>
      cases k
      all_goals first
        | rfl
        | exact absurd (tyTok_tag_zero.1 ht) (nmem (by intro e; cases e))
        | exact absurd (tyTok_tag_succ.1 ht) (nmem (by intro e; cases e))
        | exact absurd (tyTok_tag_refl.1 ht) (nmem (by intro e; cases e))
        | exact absurd ht tyTok_tag_lam
        | exact absurd ht tyTok_tag_pair
  | arg k i C s =>
      rcases Decidable.em ((k, i) ∈ argSlots) with hs | hother
      swap
      · exact absurd ht (tyTok_arg_other hother)
      simp only [argSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd (tyTok_pred.1 ht).1 (nmem (by intro e; cases e))
      · exact absurd (tyTok_reflPoint.1 ht).1 (nmem (by intro e; cases e))
      · exact absurd (tyTok_fst.1 ht).1 (nmem (by intro e; cases e))
      · exact absurd (tyTok_snd.1 ht).1 (nmem (by intro e; cases e))
  | fn k C X Y =>
      rcases fn_cases k with (rfl | rfl) | rfl | hother
      · rfl
      · rfl
      · exact absurd (tyTok_lam.1 ht).1 (nmem (by intro e; cases e))
      · exact absurd ht (tyTok_fn_other hother)

section Facts

variable {Rd : Reading Head} {P : ChurchRules R}

/-- A type token is typed at the denotation of a universe. -/
theorem SoundnessFacts.typedAt_head (sound : SoundnessFacts Rd P) {u : Head}
    (hu : R.isUniverse u) {n : Nat} (ρ : Env n) {r : Tok} (hr : TyTok Elem.univ r) :
    TypedAt (cinterp Rd (.head u : CTm Head n) ρ) r := by
  show TypedAt (principal (Rd.head u)) r
  rw [sound.universes hu]
  exact Ideal.typedAt_univ_iff.2 hr

/-- The tokens typed at the denotation of a universe are type tokens. -/
theorem SoundnessFacts.tyTok_of_typedAt_head (sound : SoundnessFacts Rd P) {u : Head}
    (hu : R.isUniverse u) {n : Nat} {ρ : Env n} {r : Tok}
    (hr : TypedAt (cinterp Rd (.head u : CTm Head n) ρ) r) : TyTok Elem.univ r := by
  have h : TypedAt (principal (Rd.head u)) r := hr
  rw [sound.universes hu] at h
  exact Ideal.typedAt_univ_iff.1 h

/-- The denotation of a term of a universe is type-generated. -/
theorem SoundnessFacts.typeGenerated_of_head (sound : SoundnessFacts Rd P) {n : Nat}
    {Γ : CCtx Head n} {A : CTm Head n} {u : Head} (hu : R.isUniverse u)
    (typing : CTyped P Γ A (.head u)) {ρ : Env n} (fits : Fits Rd Γ ρ) :
    TypeGenerated (cinterp Rd A ρ) := by
  have h : projT (principal (Rd.head u)) (cinterp Rd A ρ) = cinterp Rd A ρ :=
    (sound.typing typing ρ fits).2
  rw [sound.universes hu] at h
  exact Ideal.projT_univ_eq_self_iff.1 h

end Facts

/-! ## Related substitutions -/

section SubstRel

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L]

/-- The left instance of related substitutions. -/
theorem SubstRel.left {n m : Nat} {Γ : CCtx Head n} {ρ : Env n} {Δ : CCtx Head m}
    {σ σ' : CSub Head n m} (h : SubstRel Rd H Γ ρ Δ σ σ') : SubstRel Rd H Γ ρ Δ σ σ :=
  ⟨⟨h.1.1, fun i => .refl (h.1.1 i)⟩, fun i => ⟨(h.2 i).1.left,
    fun r hr hrU => RT.left ((h.2 i).2.1 r hr hrU),
    fun s hs hsT => RT.left ((h.2 i).2.2 s hs hsT)⟩⟩

/-- **Symmetry of related substitutions.** -/
theorem SubstRel.symm (levels : LevelModel R L) {n m : Nat} {Γ : CCtx Head n} {ρ : Env n}
    {Δ : CCtx Head m} {σ σ' : CSub Head n m} (formed : CCtxFormed P Δ)
    (h : SubstRel Rd H Γ ρ Δ σ σ') : SubstRel Rd H Γ ρ Δ σ' σ := by
  obtain ⟨⟨_, eq⟩, hi⟩ := h
  have mor' : CSubstMor P Γ Δ σ' := fun i =>
    ((CEqual.typed levels (eq i) formed).2).convType (hi i).1
  refine ⟨⟨mor', fun i => CEqual.convType (.symm (eq i)) (hi i).1⟩, fun i =>
    ⟨(hi i).1.symm, fun r hr hrU => RT.symm_ty levels formed hrU ((hi i).2.1 r hr hrU),
      fun s hs hsT => ?_⟩⟩
  obtain ⟨a, ha, hau, hta⟩ := hsT
  exact (RT.conv_iff levels formed hau hta (fun r hr => (hi i).2.1 r (ha r hr) (hau r hr))
    (hi i).1).1 (RT.symm levels formed hau hta (fun r hr => RT.left ((hi i).2.1 r (ha r hr) (hau r hr)))
      ((hi i).2.2 s hs ⟨a, ha, hau, hta⟩))

/-- **Extending related substitutions** by terms related at the type of the new
variable, over an environment extended by a value. -/
theorem SubstRel.cons (levels : LevelModel R L) {n m : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {ρ : Env n} {y : Ideal} {Δ : CCtx Head m} {σ σ' : CSub Head n m} {N N' : CTm Head m}
    (formed : CCtxFormed P Δ) (h : SubstRel Rd H Γ ρ Δ σ σ')
    (e : CEqual P Δ N N' (A.subst σ)) (eA : CTypeEq P Δ (A.subst σ) (A.subst σ'))
    (hA : ∀ r, (cinterp Rd A ρ).Mem r → TyTok Elem.univ r →
      RT H Δ false r (A.subst σ) (A.subst σ) (A.subst σ'))
    (hN : ∀ s, y.Mem s → TypedAt (cinterp Rd A ρ) s → RT H Δ true s (A.subst σ) N N') :
    SubstRel Rd H (.snoc Γ A) (Env.cons y ρ) Δ (CTm.consSub N σ) (CTm.consSub N' σ') := by
  refine ⟨CSubstEq.cons h.1 (CEqual.typed levels e formed).1 e, fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [CCtx.lookup_snoc_zero, CTm.subst_consSub_wk, CTm.consSub_zero, Env.cons_zero,
      cinterp_rename_wk]
    exact ⟨eA, hA, hN⟩
  · simp only [CCtx.lookup_snoc_succ, CTm.subst_consSub_wk, CTm.consSub_succ, Env.cons_succ,
      cinterp_rename_wk]
    exact h.2 j

/-- Terms related as far as a compact element observes are related as far as its
projection onto a type observes. -/
theorem RT.of_projT_principal {b : Bool} {m : Nat} {Δ : CCtx Head m} {X : List Tok}
    {T M M' : CTm Head m} (A : Ideal) (h : ∀ x ∈ X, RT H Δ b x T M M') {s : Tok}
    (hs : (projT A (principal X)).Mem s) : RT H Δ b s T M M' := by
  obtain ⟨v, hv, e⟩ := hs
  exact RT.closed' e fun t ht => RT.closed' (hv t ht).1 h

end SubstRel

/-! ## Compatibility with the rules -/

section Compatibility

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- Terms adequate at a universe are related as types, as far as the type tokens of
their denotation observe. -/
theorem Adequate.toType {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {u : Head}
    (hu : R.isUniverse u) (hA : Adequate Rd H Γ A (.head u)) {ρ : Env n} (fits : Fits Rd Γ ρ)
    {m : Nat} {Δ : CCtx Head m} {σ σ' : CSub Head n m} (formed : CCtxFormed P Δ)
    (hσ : SubstRel Rd H Γ ρ Δ σ σ') {r : Tok} (hr : (cinterp Rd A ρ).Mem r)
    (hrU : TyTok Elem.univ r) : RT H Δ false r (A.subst σ) (A.subst σ) (A.subst σ') :=
  RT.toType (typeKind_of_tyTok_univ hrU) (CRedTy.refl (CIsType.head_of_universe levels hu))
    (hA ρ fits formed hσ r hr (sound.typedAt_head hu ρ hrU))

include levels sound in
/-- **Conversion.** -/
theorem Adequate.conv {n : Nat} {Γ : CCtx Head n} {t A B : CTm Head n} {u : Head}
    (hu : R.isUniverse u) (ht : Adequate Rd H Γ t A) (hAB : AdequateEq Rd H Γ A B (.head u))
    (eAB : CEqual P Γ A B (.head u)) : Adequate Rd H Γ t B := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsB
  rw [← sound.equality eAB ρ fits] at hsB
  obtain ⟨a, ha, hau, hta⟩ := hsB
  refine (RT.conv_iff levels formed hau hta (fun r hr => ?_)
    ⟨u, hu, eAB.substitute hσ.1.1⟩).1 (ht ρ fits formed hσ s hs ⟨a, ha, hau, hta⟩)
  exact RT.toType (typeKind_of_tyTok_univ (hau r hr))
    (CRedTy.refl (CIsType.head_of_universe levels hu))
    (hAB.2.2 ρ fits formed hσ.left r (ha r hr) (sound.typedAt_head hu ρ (hau r hr)))

include levels sound in
/-- **A declared root computation** between two adequate terms of one type. -/
theorem AdequateEq.root {n : Nat} {Γ : CCtx Head n} {l r T : CTm Head n}
    (step : P.computation.step l r) (admits : P.Admits Γ l r) (hl : Adequate Rd H Γ l T)
    (hr : Adequate Rd H Γ r T) (tl : CTyped P Γ l T) (tr : CTyped P Γ r T) :
    AdequateEq Rd H Γ l r T := by
  refine ⟨hl, hr, fun ρ fits m Δ σ formed hσ s hs hsT => ?_⟩
  have e : CEqual P Γ l r T := .rootAdmitted step admits tl tr
  rw [sound.equality e ρ fits] at hs
  exact RT.expand levels formed
    ⟨.single (H.root (P.computation.substitute σ step)), e.substitute hσ.1.1⟩
    (CRedTm.refl (tr.substitute hσ.1.1)) (hr ρ fits formed hσ s hs hsT)

include levels sound in
/-- **Application.** A token of an application is entailed by outputs of typed
function entries of the function whose inputs are entailed by the argument's
tokens; at each, the function clause relates the applications. The two halves of the
clause are composed at the family's value at the argument, related to itself by the
function type's relation. -/
theorem Adequate.app {n : Nat} {Γ : CCtx Head n}
    {f a A : CTm Head n} {B : CTm Head (n + 1)} {u : Head} (hu : R.isUniverse u)
    (hPi : Adequate Rd H Γ (.pi A B) (.head u)) (hf : Adequate Rd H Γ f (.pi A B))
    (ha : Adequate Rd H Γ a A) (tf : CTyped P Γ f (.pi A B)) (ta : CTyped P Γ a A) :
    Adequate Rd H Γ (.app f a) (CTm.inst0 a B) := by
  intro ρ fits m Δ σ σ' formed hσ s hs _
  rw [CTm.subst_inst0]
  obtain ⟨X, Y, hX, hfXY, hYs⟩ := Ideal.mem_app.1 hs
  rw [← (sound.typing tf ρ fits).2] at hfXY
  obtain ⟨v, hvf, hvT, hve⟩ := Ideal.projT_eq_iSup.1 hfXY
  obtain ⟨b, hb, hbu, hvb⟩ := Ideal.typedAt_list hvT
  have hbF : Ideal.Below b (Ideal.former .pi (cinterp Rd A ρ) fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hb
  have piType : CIsType P Δ (.pi (A.subst σ) (B.subst (CTm.liftSub σ))) :=
    CTyped.isType levels (tf.substitute hσ.1.1) formed
  have key : ∀ w ∈ fnApp .lam v X, RT H Δ true w
      (CTm.inst0 (a.subst σ) (B.subst (CTm.liftSub σ)))
      (.app (f.subst σ) (a.subst σ)) (.app (f.subst σ') (a.subst σ')) := by
    intro w hw
    obtain ⟨C, Z, W, hmem, hZX, hwW⟩ := mem_fnApp'.1 hw
    obtain ⟨Z', W', e, hZ, hW⟩ := Ideal.tyTok_below_pi hbF (hvb _ hmem)
    injection e with _ eC eZ eW
    subst eC eZ eW
    have relf := hf ρ fits formed hσ _ (hvf _ hmem) ⟨b, hb, hbu, hvb _ hmem⟩
    rcases RT.tm_lam_iff.1 relf with hvac | hcl
    · exact RT.of_vacuous (vacuous_out hvac hwW)
    obtain ⟨hi, hii⟩ := hcl _ _ (CRedTy.refl piType)
    have hzT : ∀ z ∈ Z, (cinterp Rd a ρ).Mem z ∧ TypedAt (cinterp Rd A ρ) z := fun z hz =>
      ⟨(cinterp Rd a ρ).closed hX (hZX z hz),
        args .pi 0 b, Ideal.below_args_former hbF, Ideal.ty_args_dom (.inl rfl) hbu, hZ z hz⟩
    have h₁ := (hi (a.subst σ) (a.subst σ') (CDerivable.functional ta hσ.1)
      (fun z hz => ha ρ fits formed hσ z (hzT z hz).1 (hzT z hz).2) w hwW).2
    have hself : ∀ z ∈ Z, RT H Δ true z (A.subst σ) (a.subst σ) (a.subst σ) := fun z hz =>
      ha ρ fits formed hσ.left z (hzT z hz).1 (hzT z hz).2
    have h₂ := hii (a.subst σ) (ta.substitute hσ.1.1) hself w hwW
    -- the function type is related to itself as far as its witness observes
    have hPiSelf : ∀ r ∈ b, RT H Δ false r (.pi (A.subst σ) (B.subst (CTm.liftSub σ)))
        (.pi (A.subst σ) (B.subst (CTm.liftSub σ))) (.pi (A.subst σ) (B.subst (CTm.liftSub σ))) :=
      fun r hr => Adequate.toType levels sound hu hPi fits formed hσ.left (hb r hr) (hbu r hr)
    have hp := RT.pi_self hPiSelf (tyTok_lam.1 (hvb _ hmem)).1 (CRedTy.refl piType)
    exact RT.trans levels formed (Ideal.ty_fnApp (.inl rfl) hbu Z) (hW w hwW)
      (RT.pi_fam_at hp hPiSelf (.refl (ta.substitute hσ.1.1)) hself) h₂ h₁
  rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hve
  exact RT.closed' (ent_cut hYs fun y hy => hve.2 y hy) key

include levels sound in
/-- **Abstraction.** A typed token of an abstraction is a function entry whose
output lies in the body's denotation at the projection of its input onto the
domain; the body's adequacy there, over the substitutions extended by the
arguments, gives the function clause after β-expansion. The second component of
the triple clause is moved from the right substitution's codomain to the left
one's along the family clause of the function type's own adequacy. -/
theorem Adequate.lam {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {b B : CTm Head (n + 1)}
    {u w : Head} (hw : R.isUniverse w) (hu : R.isUniverse u)
    (hA : Adequate Rd H Γ A (.head w)) (hPi : Adequate Rd H Γ (.pi A B) (.head u))
    (hb : Adequate Rd H (.snoc Γ A) b B) (tA : CTyped P Γ A (.head w))
    (tPi : CTyped P Γ (.pi A B) (.head u)) (tb : CTyped P (.snoc Γ A) b B) :
    Adequate Rd H Γ (.lam A b) (.pi A B) := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsT
  obtain ⟨b', hb', hb'u, hts⟩ := hsT
  have hbF : Ideal.Below b' (Ideal.former .pi (cinterp Rd A ρ) fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hb'
  obtain ⟨X, Y, rfl, -, hYt⟩ := Ideal.tyTok_below_pi hbF hts
  have hmono : Ideal.Monotone fun X =>
      cinterp Rd b (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    (cinterp_envCont Rd b).mono
      (Env.Le.cons (Ideal.projT_mono (principal_mono h)) (Env.Le.refl ρ))
  have hs' : (Ideal.lam fun X =>
      cinterp Rd b (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)).Mem (.fn .lam [] X Y) := hs
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
  have eA : CTypeEq P Δ (A.subst σ) (A.subst σ') := ⟨w, hw, CDerivable.functional tA hσ.1⟩
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
        CRedTm H Δ (.app (.lam (A.subst τ) (b.subst (CTm.liftSub τ))) N)
          (b.subst (CTm.consSub N τ)) (B.subst (CTm.consSub N τ)) := by
    intro τ N mτ tN
    have e := CDerivable.betaPi (tPi.substitute mτ) hu (tb.substitute (mτ.lift A)) tN
    rw [CTm.inst0_subst_liftSub, CTm.inst0_subst_liftSub] at e
    refine ⟨.single ?_, e⟩
    have st := H.beta (A.subst τ) (b.subst (CTm.liftSub τ)) N
    rwa [CTm.inst0_subst_liftSub] at st
  -- the function clause
  show RT H Δ true (.fn .lam [] X Y) (.pi (A.subst σ) (B.subst (CTm.liftSub σ)))
    (.lam (A.subst σ) (b.subst (CTm.liftSub σ))) (.lam (A.subst σ') (b.subst (CTm.liftSub σ')))
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨fun N N' hNN hNX y hy => ?_, fun N tN hNX y hy => ?_⟩
  · rw [CTm.inst0_subst_liftSub]
    obtain ⟨tN, tN'⟩ := CEqual.typed levels hNN formed
    constructor
    · have hsub := SubstRel.cons levels formed hσ.left hNN eA.left (relA hσ.left)
        (y := projT (cinterp Rd A ρ) (principal X))
        (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
      refine RT.expand levels formed (beta hσ.1.1 tN) ?_
        (hb _ fits' formed hsub y (hY y hy) (hyT y hy))
      exact (beta hσ.1.1 tN').convType (eB (CSubstEq.cons hσ.left.1 tN' (.symm hNN)))
    · have tNr : CTyped P Δ N (A.subst σ') := tN.convType eA
      have tN'r : CTyped P Δ N' (A.subst σ') := tN'.convType eA
      have hsub := SubstRel.cons levels formed hσ'.left (hNN.convType eA) eA.symm.left
        (relA hσ'.left) (y := projT (cinterp Rd A ρ) (principal X)) (fun s' hs' hsT' => by
          obtain ⟨a, ha, hau, hta⟩ := hsT'
          exact (RT.conv_iff levels formed hau hta (fun r hr => relA hσ r (ha r hr) (hau r hr))
            eA).1 (RT.of_projT_principal _ hNX hs'))
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
          (eB (CSubstEq.cons hσ'.1 tN'r (CEqual.convType (.symm hNN) eA)))) ?_
      exact (RT.conv_iff levels formed (Ideal.ty_fnApp (.inl rfl) hb'u X) (hYt y hy) famRel
        eBN).1 ih
  · rw [CTm.inst0_subst_liftSub]
    have tNr : CTyped P Δ N (A.subst σ') := tN.convType eA
    have hsub := SubstRel.cons levels formed hσ (.refl tN) eA (relA hσ)
      (y := projT (cinterp Rd A ρ) (principal X))
      (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
    refine RT.expand levels formed (beta hσ.1.1 tN) ?_
      (hb _ fits' formed hsub y (hY y hy) (hyT y hy))
    exact (beta hσ'.1.1 tNr).convType (eB (CSubstEq.cons hσ'.1 tNr (.refl tNr)))

end Compatibility

/-! ## The identity eliminator's contraction -/

section Eliminator

variable {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

include levels in
/-- **The eliminator's contraction, typed.** An eliminator spine `S` applied to a
path that reduces to `refl r` at `Id A x y` reduces to its method `d` at the
type the spine's family takes at the path, when the spine takes a step with its
path, its instance at `refl r` computes to `d` at the root, and `d` has the
family's type at `refl r` (the typing the eliminator's template gives under the
equations of its reflexivity position). -/
theorem CRedTm.eliminator {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {S p d A x y r : CTm Head n} {E : CTm Head (n + 1)}
    (root : P.computation.step (.app S (.refl r)) d) (admits : P.Admits Γ (.app S (.refl r)) d)
    (path : ∀ {q q' : CTm Head n}, H.step q q' → H.step (.app S q) (.app S q'))
    (tS : CTyped P Γ S (.pi (.id A x y) E)) (rp : CRedTm H Γ p (.refl r) (.id A x y))
    (contractum : CTyped P Γ d (CTm.inst0 (.refl r) E)) :
    CRedTm H Γ (.app S p) d (CTm.inst0 p E) := by
  refine ⟨?_, ?_⟩
  · exact (Relation.ReflTransGen.lift (fun q => CTm.app S q) (fun _ _ s => path s) _ _ rp.1).tail
      (H.root root)
  · have tRefl : CTyped P Γ (.refl r) (.id A x y) := (CEqual.typed levels rp.2 formed).2
    obtain ⟨-, family⟩ := CIsType.pi_parts (CTyped.isType levels tS formed)
    have e₂ : CEqual P Γ (.app S (.refl r)) d (CTm.inst0 (.refl r) E) :=
      .rootAdmitted root admits (.appElim tS tRefl) contractum
    exact .trans (CDerivable.appCong (.refl tS) rp.2)
      (CEqual.convType e₂ (family.instantiateEq tRefl (.symm rp.2)))

include levels in
/-- **The eliminator step of the relation.** Two eliminator spines whose paths are
related at the reflexivity tag of `Id A x y` are related at the family's type at
the left path as far as a token observes, when their methods are: both spines
contract to their methods by the reflexivity clause, and head expansion moves
the relation back. -/
theorem RT.eliminator {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {S S' p p' d d' A x y : CTm Head n} {E : CTm Head (n + 1)} {t : Tok}
    (root : ∀ r, P.computation.step (.app S (.refl r)) d)
    (root' : ∀ r, P.computation.step (.app S' (.refl r)) d')
    (admits : ∀ r, CEqual P Γ r x A → CEqual P Γ r y A → P.Admits Γ (.app S (.refl r)) d)
    (admits' : ∀ r, CEqual P Γ r x A → CEqual P Γ r y A → P.Admits Γ (.app S' (.refl r)) d')
    (path : ∀ {q q' : CTm Head n}, H.step q q' → H.step (.app S q) (.app S q'))
    (path' : ∀ {q q' : CTm Head n}, H.step q q' → H.step (.app S' q) (.app S' q'))
    (tS : CTyped P Γ S (.pi (.id A x y) E)) (tS' : CTyped P Γ S' (.pi (.id A x y) E))
    (contractum : ∀ r, CEqual P Γ r x A → CEqual P Γ r y A → CTyped P Γ d (CTm.inst0 (.refl r) E))
    (contractum' : ∀ r, CEqual P Γ r x A → CEqual P Γ r y A →
      CTyped P Γ d' (CTm.inst0 (.refl r) E))
    (ep : CEqual P Γ p p' (.id A x y)) (hp : RT H Γ true (.tag .refl) (.id A x y) p p')
    (hd : RT H Γ true t (CTm.inst0 p E) d d') :
    RT H Γ true t (CTm.inst0 p E) (.app S p) (.app S' p') := by
  obtain ⟨B, x₁, y₁, r, r', hr⟩ := RT.tm_reflTag_iff.1 hp
  have e := H.red_normal (H.normal_id _ _ _) hr.1.1
  injection e with _ eB ex ey
  subst eB ex ey
  obtain ⟨-, rp, rp', erx, ery, err⟩ := hr
  have c₁ := CRedTm.eliminator levels formed (root r) (admits r erx ery) path tS rp
    (contractum r erx ery)
  have c₂ := CRedTm.eliminator levels formed (root' r')
    (admits' r' (.trans (.symm err) erx) (.trans (.symm err) ery)) path' tS' rp'
    (contractum' r' (.trans (.symm err) erx) (.trans (.symm err) ery))
  obtain ⟨-, family⟩ := CIsType.pi_parts (CTyped.isType levels tS formed)
  have tp' : CTyped P Γ p' (.id B x₁ y₁) := (CEqual.typed levels ep formed).2
  exact RT.expand levels formed c₁ (c₂.convType (family.instantiateEq tp' (.symm ep))) hd

include levels in
/-- **The motive's conversion at the reflexivity point.** Let the motive `M` of an
eliminator at `A` and `x`, of type `Π (y : A). Id A x y → U`, be related to itself
as far as a function entry whose inputs are observed through the point tokens `S`
of a path `p ⇝ refl r` at `Id A x y`: its first input as far as `S` observes, and
its second as far as the reflexivity tag and the point tokens over `S` observe. If
the point `r` is related to `x` and to `y` as far as `S` observes, at a type witness
of `S` at which the carrier `A` is related to itself, then the
instances `M x (refl x)` and `M y p` are related as types as far as the entry's
output observes: the motive's function clause at the related pair `(x, y)`, then
at `refl x` and at the related pair `(refl x, p)`, and transitivity. -/
theorem RT.motive_reflPoint {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A x y p r M : CTm Head n} {u : Head} (hu : R.isUniverse u) {Z₁ Z₂ W S c : List Tok}
    (tM : CTyped P Γ M (.pi A (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) (.head u))))
    (hM : RT H Γ true (.fn .lam [] Z₁ [.fn .lam [] Z₂ W])
      (.pi A (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) (.head u))) M M)
    (rp : CRedTm H Γ p (.refl r) (.id A x y)) (erx : CEqual P Γ r x A) (ery : CEqual P Γ r y A)
    (hc : Ty c Elem.univ) (hS : ∀ s ∈ S, TyTok c s) (hA : ∀ q ∈ c, RT H Γ false q A A A)
    (hrx : ∀ s ∈ S, RT H Γ true s A r x) (hry : ∀ s ∈ S, RT H Γ true s A r y)
    (h₁ : ∀ z ∈ Z₁, ent S z = true)
    (h₂ : ∀ z ∈ Z₂, ent (.tag .refl :: S.map (.arg .refl 0 [])) z = true)
    (hW : ∀ w ∈ W, TyTok Elem.univ w) :
    ∀ w ∈ W, RT H Γ false w (.app (.app M x) (.refl x)) (.app (.app M x) (.refl x))
      (.app (.app M y) p) := by
  intro w hw
  -- the point's relations
  have hxr : ∀ s ∈ S, RT H Γ true s A x r := fun s hs =>
    RT.symm levels formed hc (hS s hs) hA (hrx s hs)
  have hxy : ∀ s ∈ S, RT H Γ true s A x y := fun s hs =>
    RT.trans levels formed hc (hS s hs) hA (hxr s hs) (hry s hs)
  have hxx : ∀ s ∈ S, RT H Γ true s A x x := fun s hs => RT.left (hxr s hs)
  have tx : CTyped P Γ x A := (CEqual.typed levels erx formed).2
  have exx : CEqual P Γ x x A := .refl tx
  have exr : CEqual P Γ x r A := .symm erx
  -- the types
  obtain ⟨tA, -⟩ := CIsType.pi_parts (CTyped.isType levels tM formed)
  obtain ⟨v, hv, tA⟩ := tA
  have eId : CTypeEq P Γ (.id A x y) (.id A x x) :=
    ⟨v, hv, .idCong (.refl tA) hv exx (.trans (.symm ery) erx)⟩
  have hE : CTm.inst0 x (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) (.head u)) =
      (.pi (.id A x x) (.head u) : CTm Head n) := by
    change CTm.pi (.id (CTm.inst0 x (A.rename wk)) (CTm.inst0 x (x.rename wk)) x) (.head u) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]
  -- reflexivity at `x` and the path, related as far as the aligned tokens observe
  have tReflx : CTyped P Γ (.refl x) (.id A x x) := .reflIntro tx
  have idType : CIsType P Γ (.id A x x) := CTyped.isType levels tReflx formed
  have reflx : ReflRed H Γ (.id A x x) (.refl x) (.refl x) A x x x x :=
    ⟨CRedTy.refl idType, CRedTm.refl tReflx, CRedTm.refl tReflx, exx, exx, exx⟩
  have reflp : ReflRed H Γ (.id A x x) (.refl x) p A x x x r :=
    ⟨CRedTy.refl idType, CRedTm.refl tReflx, rp.convType eId, exx, exx, exr⟩
  have alignedx : ∀ z ∈ Z₂, RT H Γ true z (.id A x x) (.refl x) (.refl x) := by
    intro z hz
    refine RT.closed' (h₂ z hz) fun q hq => ?_
    rcases List.mem_cons.1 hq with rfl | hq
    · exact RT.tm_reflTag_iff.2 ⟨A, x, x, x, x, reflx⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hq
      exact RT.tm_argRefl_iff.2 (.inr ⟨A, x, x, x, x, reflx,
        fun _ h => absurd h List.not_mem_nil, fun _ => ⟨hxx s hs, hxx s hs, hxx s hs⟩⟩)
  have alignedp : ∀ z ∈ Z₂, RT H Γ true z (.id A x x) (.refl x) p := by
    intro z hz
    refine RT.closed' (h₂ z hz) fun q hq => ?_
    rcases List.mem_cons.1 hq with rfl | hq
    · exact RT.tm_reflTag_iff.2 ⟨A, x, x, x, r, reflp⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hq
      exact RT.tm_argRefl_iff.2 (.inr ⟨A, x, x, x, r, reflp,
        fun _ h => absurd h List.not_mem_nil, fun _ => ⟨hxx s hs, hxx s hs, hxr s hs⟩⟩)
  have epx : CEqual P Γ (.refl x) p (.id A x x) :=
    .trans (.reflCong exr) (CEqual.convType (.symm rp.2) eId)
  -- the motive's clauses
  have hU : CRedTy H Γ (.head u : CTm Head n) (.head u) :=
    CRedTy.refl (CIsType.head_of_universe levels hu)
  rcases RT.tm_lam_iff.1 hM with hvac | hcl
  · exact RT.of_vacuous (vacuous_out (vacuous_out hvac List.mem_cons_self) hw)
  obtain ⟨hi, -⟩ := hcl _ _ (CRedTy.refl (CTyped.isType levels tM formed))
  have hMxy := (hi x y (.trans (.symm erx) ery) (fun z hz => RT.closed' (h₁ z hz) hxy) _
    List.mem_cons_self).1
  rw [hE] at hMxy
  have tMx : CTyped P Γ (.app M x) (.pi (.id A x x) (.head u)) := by
    have h := CDerivable.appElim tM tx
    rwa [hE] at h
  rcases RT.tm_lam_iff.1 hMxy with hvac | hcl₂
  · exact RT.of_vacuous (vacuous_out hvac hw)
  obtain ⟨hi₂, hii₂⟩ := hcl₂ _ _ (CRedTy.refl (CTyped.isType levels tMx formed))
  have e₁ := hii₂ (.refl x) tReflx alignedx w hw
  have e₂ := (hi₂ (.refl x) p epx alignedp w hw).2
  exact RT.trans_ty levels formed (hW w hw)
    (RT.toType (typeKind_of_tyTok_univ (hW w hw)) hU e₁)
    (RT.toType (typeKind_of_tyTok_univ (hW w hw)) hU e₂)

end Eliminator

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
