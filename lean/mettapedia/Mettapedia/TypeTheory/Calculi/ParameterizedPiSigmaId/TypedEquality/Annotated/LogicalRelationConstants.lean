import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationValidity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationCodes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchDefinitions

/-!
# Constants that compute along a telescope, the quantifier at an adequate carrier, and head equality

**Telescopes** (`CTele`): annotated types from `n` variables to `m`, the first entry
outermost, with the dependent function type (`CTele.pis`) and the abstraction
(`CTele.lams`) over a telescope, and the context a telescope extends (`CTele.extend`).
A context is a telescope over the empty context (`CCtx.toTele`), with the dependent
function type and the abstraction of `ChurchDefinitions` (`CCtx.pis_toTele`,
`CCtx.lams_toTele`, `CCtx.extend_toTele`).

A closed term under any substitution or renaming is the term lifted into the context
(`CTm.subst_closed`, `CTm.rename_closed`).

**Head equality** (`CStatement.Valid.headEq`): let head equality be trivial on the heads
that are not universes (`GroundHeadEq`), and the decoder take no step at a universe head
(`HeadReduction.DecoderStuckAtUniverses`). Then heads equal by head equality are valid as
equal at every type at which both are valid.

**Related substitutions at an extended context** split at the newest variable
(`SubstRel.of_cons`).

**The parts of an adequate dependent function type are adequate**: its domain
(`AdequateType.pi_dom`) and its family over the extended context
(`AdequateType.pi_cod`). An adequate type stays adequate under weakening
(`AdequateType.weaken`).

**A head that reduces along a telescope** (`TeleReduces`): applied to arguments typed
along the telescope, it reduces, typed at the codomain, to the body at the substitution
extended by the arguments.

**The relation at a telescope** (`RT.telescope`): let the dependent function type over a
telescope be a type and adequate, and the body adequate at the codomain over the extended
context. Two heads that reduce along the telescope from related substitutions are
related at the dependent function type, as far as every token of the abstraction's
denotation typed at the type's denotation observes. At each entry the function clause
extends the substitutions by the related arguments; at the end both heads reduce to the
body, whose adequacy relates them there, and head expansion moves the relation back.

**A constant defined by one equation** (`ConstAdequateAt.ofDefinition`): a constant
declared at the dependent function type over a context, read as the abstraction of its
right side projected onto its declared type, whose applications reduce to its right
side, is adequate when its right side is adequate at the codomain.

**The quantifier over an adequate carrier** (`RT.allCodeAt`): a quantifier code whose
decoding is the dependent function type over a carrier `A` is related to itself at
`(A → prop) → prop` at every token of the quantifier's constant over a carrier ideal whose
type tokens relate `A` to itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypedAt principal codesIdeal)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## Telescopes -/

/-- A telescope of annotated types from `n` variables to `m`, its first entry
outermost. -/
inductive CTele (Head : Type) : Nat → Nat → Type where
  | nil {n : Nat} : CTele Head n n
  | cons {n m : Nat} (A : CTm Head n) (rest : CTele Head (n + 1) m) : CTele Head n m

namespace CTele

/-- The dependent function type over a telescope. -/
def pis : {n m : Nat} → CTele Head n m → CTm Head m → CTm Head n
  | _, _, .nil, T => T
  | _, _, .cons A rest, T => .pi A (pis rest T)

/-- The abstraction over a telescope. -/
def lams : {n m : Nat} → CTele Head n m → CTm Head m → CTm Head n
  | _, _, .nil, E => E
  | _, _, .cons A rest, E => .lam A (lams rest E)

/-- A context extended by a telescope. -/
def extend : {n m : Nat} → CCtx Head n → CTele Head n m → CCtx Head m
  | _, _, Γ, .nil => Γ
  | _, _, Γ, .cons A rest => extend (.snoc Γ A) rest

/-- A telescope with one more entry at its end. -/
def snoc : {n m : Nat} → CTele Head n m → CTm Head m → CTele Head n (m + 1)
  | _, _, .nil, A => .cons A .nil
  | _, _, .cons B rest, A => .cons B (snoc rest A)

theorem pis_snoc : ∀ {n m : Nat} (tele : CTele Head n m) (A : CTm Head m)
    (T : CTm Head (m + 1)), (tele.snoc A).pis T = tele.pis (.pi A T)
  | _, _, .nil, _, _ => rfl
  | _, _, .cons B rest, A, T => by
      show CTm.pi B ((rest.snoc A).pis T) = .pi B (rest.pis (.pi A T))
      rw [pis_snoc rest A T]

theorem lams_snoc : ∀ {n m : Nat} (tele : CTele Head n m) (A : CTm Head m)
    (E : CTm Head (m + 1)), (tele.snoc A).lams E = tele.lams (.lam A E)
  | _, _, .nil, _, _ => rfl
  | _, _, .cons B rest, A, E => by
      show CTm.lam B ((rest.snoc A).lams E) = .lam B (rest.lams (.lam A E))
      rw [lams_snoc rest A E]

theorem extend_snoc : ∀ {n m : Nat} (Γ : CCtx Head n) (tele : CTele Head n m) (A : CTm Head m),
    extend Γ (tele.snoc A) = .snoc (extend Γ tele) A
  | _, _, _, .nil, _ => rfl
  | _, _, Γ, .cons B rest, A => extend_snoc (.snoc Γ B) rest A

end CTele

/-- A context, as a telescope over the empty context. -/
def CCtx.toTele : {k : Nat} → CCtx Head k → CTele Head 0 k
  | _, .nil => .nil
  | _, .snoc Θ A => (CCtx.toTele Θ).snoc A

theorem CCtx.pis_toTele : ∀ {k : Nat} (Θ : CCtx Head k) (T : CTm Head k),
    (CCtx.toTele Θ).pis T = pisCtx Θ T
  | _, .nil, _ => rfl
  | _, .snoc Θ A, T => by
      show ((CCtx.toTele Θ).snoc A).pis T = pisCtx Θ (.pi A T)
      rw [CTele.pis_snoc, CCtx.pis_toTele Θ]

theorem CCtx.lams_toTele : ∀ {k : Nat} (Θ : CCtx Head k) (E : CTm Head k),
    (CCtx.toTele Θ).lams E = lamsCtx Θ E
  | _, .nil, _ => rfl
  | _, .snoc Θ A, E => by
      show ((CCtx.toTele Θ).snoc A).lams E = lamsCtx Θ (.lam A E)
      rw [CTele.lams_snoc, CCtx.lams_toTele Θ]

theorem CCtx.extend_toTele : ∀ {k : Nat} (Θ : CCtx Head k), (CCtx.toTele Θ).extend .nil = Θ
  | _, .nil => rfl
  | _, .snoc Θ A => by
      show CTele.extend .nil ((CCtx.toTele Θ).snoc A) = .snoc Θ A
      rw [CTele.extend_snoc, CCtx.extend_toTele Θ]

/-! ## Closed terms -/

/-- A closed term under any substitution is the term lifted into the context. -/
theorem CTm.subst_closed {m : Nat} (t : CTm Head 0) (σ : CSub Head 0 m) :
    t.subst σ = t.liftClosed := by
  rw [show σ = fun i => .var (Fin.elim0 i) from funext fun i => i.elim0, CTm.subst_var_comp]
  rfl

/-- A closed term under any renaming is the term lifted into the context. -/
theorem CTm.rename_closed {m : Nat} (t : CTm Head 0) (ξ : Ren 0 m) :
    t.rename ξ = t.liftClosed := by
  rw [show ξ = Fin.elim0 from funext fun i => i.elim0]
  rfl

/-! ## Head equality on the heads that are not universes -/

/-- **Head equality is trivial on the heads that are not universes**: heads equal by head
equality are universes, or the same head. -/
def GroundHeadEq (R : Rules Head) : Prop :=
  ∀ {h h' : Head}, R.headEq h h' → R.isUniverse h ∨ h = h'

/-- **The decoder is stuck at universes**: the decoder applied to a universe head takes no
step. -/
def HeadReduction.DecoderStuckAtUniverses {P : ChurchRules R} {K : RigidTypes P}
    (H : HeadReduction P K) : Prop :=
  ∀ {n : Nat} {h : Head}, R.isUniverse h → H.Normal (.app (.const K.holds) (.head h) : CTm Head n)

section HeadEquality

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

/-- A typed token of the universe that observes something is the tag of universes. -/
theorem eq_tag_univ_of_typed {s : Tok} (hs : ent Elem.univ s = true) (hv : ent [] s = false)
    {a : List Tok} (hta : TyTok a s) : s = .tag .univ := by
  obtain ⟨q, hq, hk, -⟩ := source_of_ent hs hv
  rw [List.mem_singleton.1 hq] at hk
  cases s with
  | tag k =>
      change Kind.univ = k at hk
      rw [hk]
  | arg k i C t =>
      change Kind.univ = k at hk
      subst hk
      exact absurd hta (tyTok_arg_other (by simp [argSlots]))
  | fn k C X Y =>
      change Kind.univ = k at hk
      subst hk
      exact absurd hta (tyTok_fn_other ⟨by decide, by decide, by decide⟩)

include levels sound in
/-- **Validity of head equality**, when head equality is trivial on the heads that are not
universes and the decoder is stuck at universes. At the same head, the equation's relation
is the typing's. At universes, the only typed token of a universe that observes something is
the tag of universes; the typing's relation there reduces the type to a universe head, at
which the two heads are related as the same up to head equality, or reduces the type to the
type of codes and a universe's decoding to a universe head, which the stuck decoder
excludes. -/
theorem CStatement.Valid.headEq (ground : GroundHeadEq R) (stuck : H.DecoderStuckAtUniverses)
    {n : Nat} {Γ : CCtx Head n} {h h' : Head} {A : CTm Head n} (same : R.headEq h h')
    (hh : (CStatement.typing Γ (.head h) A).Valid Rd H)
    (hh' : (CStatement.typing Γ (.head h') A).Valid Rd H) :
    (CStatement.equality Γ (.head h) (.head h') A).Valid Rd H := by
  refine ⟨⟨hh.1, hh'.1, fun ρ fits m Δ σ formed hσ s hs hsT => ?_⟩, hh.2⟩
  have hrel := hh.1 ρ fits formed hσ s hs hsT
  rcases ground same with hu | rfl
  · have hu' : R.isUniverse h' := (levels.headEq_level same).1.1 hu
    cases hv : ent [] s with
    | true => exact RT.of_vacuous hv
    | false =>
    have hs' : ent Elem.univ s = true := by
      have h0 : (principal (Rd.head h)).Mem s := hs
      rwa [sound.universes hu] at h0
    obtain ⟨a, -, -, hta⟩ := hsT
    obtain rfl := eq_tag_univ_of_typed hs' hv hta
    rcases (RT.tm_type_iff rfl).1 hrel with hvac | ⟨u, hu₀, hT, -⟩ | ⟨-, hdec⟩
    · exact RT.of_vacuous hvac
    · exact (RT.tm_type_iff rfl).2 (.inr (.inl ⟨u, hu₀, hT, RT.ty_univ_iff.2 ⟨h, h',
        CRedTy.refl (CIsType.head_of_universe levels hu),
        CRedTy.refl (CIsType.head_of_universe levels hu'), hu, hu', .inr same⟩⟩))
    · obtain ⟨u₁, -, r₁, -⟩ := RT.ty_univ_iff.1 hdec
      have e := H.red_normal (stuck hu) r₁.1
      cases e
  · exact hrel

end HeadEquality

/-! ## Heads that reduce along a telescope -/

/-- **A head reduces along a telescope** to a body at a codomain: applied to arguments
typed along the telescope, it reduces by typed weak-head reduction, at the codomain, to
the body at the substitution extended by the arguments. -/
def TeleReduces {P : ChurchRules R} {K : RigidTypes P} (H : HeadReduction P K) {k : Nat}
    (Δ : CCtx Head k) : {n m : Nat} → CTele Head n m → CTm Head m → CTm Head m →
      CTm Head k → CSub Head n k → Prop
  | _, _, .nil, T, E, h, σ => CRedTm H Δ h (E.subst σ) (T.subst σ)
  | _, _, .cons A rest, T, E, h, σ => ∀ N, CTyped P Δ N (A.subst σ) →
      TeleReduces H Δ rest T E (.app h N) (CTm.consSub N σ)

/-! ## Related substitutions at an extended context -/

section Split

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}

/-- **Related substitutions at an extended context**, split at the newest variable: the
older variables are related over the older entries, and the newest ones are equal and
related as far as the newest value observes. -/
theorem SubstRel.of_cons {n m : Nat} {Γ : CCtx Head n} {A : CTm Head n} {ρ : Env n}
    {x : Ideal} {Δ : CCtx Head m} {σ σ' : CSub Head n m} {N N' : CTm Head m}
    (h : SubstRel Rd H (.snoc Γ A) (Env.cons x ρ) Δ (CTm.consSub N σ) (CTm.consSub N' σ')) :
    SubstRel Rd H Γ ρ Δ σ σ' ∧ CEqual P Δ N N' (A.subst σ) ∧
      ∀ s, x.Mem s → TypedAt (cinterp Rd A ρ) s → RT H Δ true s (A.subst σ) N N' := by
  obtain ⟨⟨mor, eq⟩, hi⟩ := h
  refine ⟨⟨⟨fun i => ?_, fun i => ?_⟩, fun i => ?_⟩, ?_, ?_⟩
  · simpa only [CCtx.lookup_snoc_succ, CTm.subst_consSub_wk, CTm.consSub_succ] using mor i.succ
  · simpa only [CCtx.lookup_snoc_succ, CTm.subst_consSub_wk, CTm.consSub_succ] using eq i.succ
  · simpa only [CCtx.lookup_snoc_succ, CTm.subst_consSub_wk, CTm.consSub_succ, Env.cons_succ,
      cinterp_rename_wk] using hi i.succ
  · simpa only [CCtx.lookup_snoc_zero, CTm.subst_consSub_wk, CTm.consSub_zero] using eq 0
  · have h0 := (hi 0).2.2
    simp only [CCtx.lookup_snoc_zero, CTm.subst_consSub_wk, CTm.consSub_zero, Env.cons_zero,
      cinterp_rename_wk] at h0
    exact h0

/-- An environment of an extended context is the extension of its restriction. -/
theorem env_eq_cons_tail {n : Nat} (ρ : Env (n + 1)) : ρ = Env.cons (ρ 0) (fun i => ρ i.succ) :=
  Env.eq_cons rfl rfl

/-- A substitution of an extended context is the extension of its restriction. -/
theorem CTm.eq_consSub_tail {n m : Nat} (τ : CSub Head (n + 1) m) :
    τ = CTm.consSub (τ 0) (fun i => τ i.succ) :=
  funext fun i => Fin.cases rfl (fun _ => rfl) i

end Split

/-! ## The parts of an adequate dependent function type -/

section Parts

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

/-- **The domain of an adequate dependent function type is adequate**: a type token of
the domain is the component of a domain token of the dependent function type. -/
theorem AdequateType.pi_dom {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
    (hPi : AdequateType Rd H Γ (.pi A B)) : AdequateType Rd H Γ A := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  have hmem : (cinterp Rd (.pi A B) ρ).Mem (.arg .pi 0 [] r) := Ideal.mem_former_dom.2 hr
  have hty : TyTok Elem.univ (.arg .pi 0 [] r) :=
    (tyTok_dom (.inl rfl)).2 ⟨Elem.isUniv_univ, rfl, hrU⟩
  rcases RT.ty_argPi_iff.1 (hPi ρ fits formed hσ _ hmem hty) with hvac | ⟨D, E, D', E', hp, -, hd⟩
  · exact RT.of_vacuous (vacuous_arg hvac)
  have e₁ := H.red_normal (H.normal_pi _ _) hp.1.1
  have e₂ := H.red_normal (H.normal_pi _ _) hp.2.1.1
  injection e₁ with _ e₁D e₁E
  injection e₂ with _ e₂D e₂E
  subst e₁D e₁E e₂D e₂E
  exact hd rfl

include levels in
/-- **The family of an adequate dependent function type is adequate** over the extended
context. A type token of the family's value at the newest value is, by continuity, the
output of a typed family entry whose input is a finite typed part of that value. The
family clause relates the two substituted families at the left argument, and the right
family at the two arguments; transitivity composes them. -/
theorem AdequateType.pi_cod {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
    (hPi : AdequateType Rd H Γ (.pi A B)) : AdequateType Rd H (.snoc Γ A) B := by
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
  -- the typed family entry of the dependent function type
  have hF : Ideal.Monotone fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    hG.mono (Ideal.projT_mono (principal_mono h))
  have hmem : (cinterp Rd (.pi A B) ρ).Mem (.fn .pi c w [r]) :=
    (Ideal.mem_former_fn hF).2 ⟨hc, fun y hy => by rw [List.mem_singleton.1 hy]; exact hrw⟩
  have hty : TyTok Elem.univ (.fn .pi c w [r]) :=
    (tyTok_family (.inl rfl)).2 ⟨Elem.isUniv_univ, hcu, hwc,
      fun y hy => by rw [List.mem_singleton.1 hy]; exact hrU⟩
  rcases RT.ty_fnPi_iff.1 (hPi ρ fits formed hσ _ hmem hty) with hvac | ⟨D, E, D', E', hp, -, hf, hg⟩
  · exact RT.of_vacuous (vacuous_out hvac List.mem_cons_self)
  have e₁ := H.red_normal (H.normal_pi _ _) hp.1.1
  have e₂ := H.red_normal (H.normal_pi _ _) hp.2.1.1
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

/-- **Weakening**: an adequate type is adequate over a context extended by one more
entry. -/
theorem AdequateType.weaken {n : Nat} {Γ : CCtx Head n} {A E : CTm Head n}
    (hA : AdequateType Rd H Γ A) : AdequateType Rd H (.snoc Γ E) (A.rename wk) := by
  intro ρ' fits' m Δ τ τ' formed hτ r hr hrU
  obtain ⟨x, ρ, rfl⟩ : ∃ x ρ, ρ' = Env.cons x ρ := ⟨_, _, env_eq_cons_tail ρ'⟩
  obtain ⟨N, σ, rfl⟩ : ∃ N σ, τ = CTm.consSub N σ := ⟨_, _, CTm.eq_consSub_tail τ⟩
  obtain ⟨N', σ', rfl⟩ : ∃ N' σ', τ' = CTm.consSub N' σ' := ⟨_, _, CTm.eq_consSub_tail τ'⟩
  rw [cinterp_rename_wk] at hr
  rw [CTm.subst_consSub_wk, CTm.subst_consSub_wk]
  exact hA ρ fits'.1 formed (SubstRel.of_cons hτ).1 r hr hrU

end Parts

/-! ## The relation at a telescope -/

section Telescope

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **The relation at a telescope.** Let the dependent function type over a telescope be
a type and adequate, and the body adequate at the codomain over the extended context.
Two heads that reduce along the telescope to the body, from substitutions related over
an environment fitting the context, are related at the dependent function type as far as
every token of the abstraction's denotation typed at the type's denotation observes. -/
theorem RT.telescope : ∀ {n m : Nat} (tele : CTele Head n m) {Γ : CCtx Head n}
    {T E : CTm Head m}, CIsType P Γ (tele.pis T) → AdequateType Rd H Γ (tele.pis T) →
    Adequate Rd H (tele.extend Γ) E T → ∀ ρ, Fits Rd Γ ρ → ∀ {k : Nat} {Δ : CCtx Head k}
    {σ₁ σ₂ : CSub Head n k} {h₁ h₂ : CTm Head k}, CCtxFormed P Δ → SubstRel Rd H Γ ρ Δ σ₁ σ₂ →
      TeleReduces H Δ tele T E h₁ σ₁ → TeleReduces H Δ tele T E h₂ σ₂ →
      ∀ t, (cinterp Rd (tele.lams E) ρ).Mem t → TypedAt (cinterp Rd (tele.pis T) ρ) t →
        RT H Δ true t ((tele.pis T).subst σ₁) h₁ h₂
  | _, _, .nil, Γ, T, E, tT, _, hE, ρ, fits, k, Δ, σ₁, σ₂, h₁, h₂, formed, hσ, r₁, r₂,
      t, ht, htT => by
      obtain ⟨u, hu, tT⟩ := tT
      have eT : CTypeEq P Δ (T.subst σ₂) (T.subst σ₁) :=
        ⟨u, hu, CDerivable.functional tT (hσ.symm levels formed).1⟩
      exact RT.expand levels formed r₁ (CRedTm.convType r₂ eT) (hE ρ fits formed hσ t ht htT)
  | _, _, .cons A rest, Γ, T, E, tPi, hPi, hE, ρ, fits, k, Δ, σ₁, σ₂, h₁, h₂, formed, hσ, r₁,
      r₂, t, ht, htT => by
      obtain ⟨⟨w, hw, tA⟩, tU⟩ := CIsType.pi_parts tPi
      have hA : AdequateType Rd H Γ A := AdequateType.pi_dom hPi
      have hU : AdequateType Rd H (.snoc Γ A) (rest.pis T) := AdequateType.pi_cod levels hPi
      have ih := RT.telescope rest tU hU hE
      obtain ⟨b', hb', hb'u, hts⟩ := htT
      have hbF : Ideal.Below b' (Ideal.former .pi (cinterp Rd A ρ) fun X =>
          cinterp Rd (rest.pis T) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := hb'
      obtain ⟨X, Y, rfl, -, hYt⟩ := Ideal.tyTok_below_pi hbF hts
      have hmono : Ideal.Monotone fun X =>
          cinterp Rd (rest.lams E) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
        (cinterp_envCont Rd (rest.lams E)).mono
          (Env.Le.cons (Ideal.projT_mono (principal_mono h)) (Env.Le.refl ρ))
      have ht' : (Ideal.lam fun X =>
          cinterp Rd (rest.lams E) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)).Mem
            (.fn .lam [] X Y) := ht
      have hY := (Ideal.mem_lam_fn hmono).1 ht'
      have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
        ⟨fits, sound.typeGenerated_of_head hw tA fits, Ideal.projT_projT _ _⟩
      have famBelow : Ideal.Below (fnApp .pi b' X)
          (cinterp Rd (rest.pis T) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) := by
        have h := Ideal.below_fam_fnApp (k := .pi) (y := principal X) hb'
          fun x hx => ent_of_mem hx
        rwa [show CTele.pis (.cons A rest) T = .pi A (rest.pis T) from rfl, fam_cinterp_pi] at h
      have hyT : ∀ y ∈ Y, TypedAt
          (cinterp Rd (rest.pis T) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ)) y :=
        fun y hy => ⟨fnApp .pi b' X, famBelow, Ideal.ty_fnApp (.inl rfl) hb'u X, hYt y hy⟩
      -- the facts of the substitutions
      have hσ' := hσ.symm levels formed
      have eA : CTypeEq P Δ (A.subst σ₁) (A.subst σ₂) := ⟨w, hw, CDerivable.functional tA hσ.1⟩
      have relA : ∀ {τ τ' : CSub Head _ k}, SubstRel Rd H Γ ρ Δ τ τ' → ∀ r,
          (cinterp Rd A ρ).Mem r → TyTok Elem.univ r →
            RT H Δ false r (A.subst τ) (A.subst τ) (A.subst τ') := fun hτ r hr hrU =>
        hA ρ fits formed hτ r hr hrU
      obtain ⟨v, hv, tU'⟩ := tU
      have eU : ∀ {τ τ' : CSub Head _ k}, CSubstEq P (.snoc Γ A) Δ τ τ' →
          CTypeEq P Δ ((rest.pis T).subst τ) ((rest.pis T).subst τ') := fun hττ' =>
        ⟨v, hv, CDerivable.functional tU' hττ'⟩
      -- the function clause
      show RT H Δ true (.fn .lam [] X Y) (.pi (A.subst σ₁) ((rest.pis T).subst (CTm.liftSub σ₁)))
        h₁ h₂
      refine RT.tm_lam_iff.2 (.inr fun D E' hred => ?_)
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
          exact ih _ fits' formed hsub (r₁ N tN) (r₁ N' tN') y (hY y hy) (hyT y hy)
        · have tNr : CTyped P Δ N (A.subst σ₂) := tN.convType eA
          have tN'r : CTyped P Δ N' (A.subst σ₂) := tN'.convType eA
          have hsub := SubstRel.cons levels formed hσ'.left (hNN.convType eA) eA.symm.left
            (relA hσ'.left) (y := projT (cinterp Rd A ρ) (principal X)) (fun s' hs' hsT' => by
              obtain ⟨a, ha, hau, hta⟩ := hsT'
              exact (RT.conv_iff levels formed hau hta
                (fun r hr => relA hσ r (ha r hr) (hau r hr)) eA).1
                (RT.of_projT_principal _ hNX hs'))
          have hrel := ih _ fits' formed hsub (r₂ N tNr) (r₂ N' tN'r) y (hY y hy) (hyT y hy)
          -- the family at the left argument, from the right substitution to the left one
          have hself := SubstRel.cons levels formed hσ (.refl tN) eA (relA hσ)
            (y := projT (cinterp Rd A ρ) (principal X))
            (fun s' hs' _ => RT.of_projT_principal _ (fun x hx => RT.left (hNX x hx)) hs')
          have famRel : ∀ r ∈ fnApp .pi b' X, RT H Δ false r
              ((rest.pis T).subst (CTm.consSub N σ₂)) ((rest.pis T).subst (CTm.consSub N σ₂))
              ((rest.pis T).subst (CTm.consSub N σ₁)) := fun r hr =>
            RT.symm_ty levels formed (Ideal.ty_fnApp (.inl rfl) hb'u X r hr)
              (hU _ fits' formed hself r (famBelow r hr) (Ideal.ty_fnApp (.inl rfl) hb'u X r hr))
          exact (RT.conv_iff levels formed (Ideal.ty_fnApp (.inl rfl) hb'u X) (hYt y hy) famRel
            (eU (CSubstEq.cons hσ'.1 tNr (.refl tNr)))).1 hrel
      · rw [CTm.inst0_subst_liftSub]
        have tNr : CTyped P Δ N (A.subst σ₂) := tN.convType eA
        have hsub := SubstRel.cons levels formed hσ (.refl tN) eA (relA hσ)
          (y := projT (cinterp Rd A ρ) (principal X))
          (fun s' hs' _ => RT.of_projT_principal _ hNX hs')
        exact ih _ fits' formed hsub (r₁ N tN) (r₂ N tNr) y (hY y hy) (hyT y hy)

end Telescope

/-! ## Constants defined by one equation -/

section Definitions

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **A constant defined by one equation is adequate** when its right side is adequate at
its codomain: the constant is declared at the dependent function type over a context,
read as the abstraction of its right side projected onto its declared type, and every
application of it to arguments typed along the context reduces to its right side. -/
theorem ConstAdequateAt.ofDefinition {f : DeclName} {k : Nat} {Θ : CCtx Head k}
    {T E : CTm Head k} (declared : P.constantType f = some (pisCtx Θ T))
    (reading : Rd.const f = defConst Rd Θ T E) (rhs : Adequate Rd H Θ E T)
    (red : ∀ {m : Nat} {Δ : CCtx Head m}, CCtxFormed P Δ →
      TeleReduces H Δ (CCtx.toTele Θ) T E (.const f) fun i => .var (Fin.elim0 i)) :
    ConstAdequateAt Rd H f := by
  intro D u declared' hu tD hD m Δ formed s hs _
  obtain rfl : pisCtx Θ T = D := Option.some.inj (declared.symm.trans declared')
  rw [reading, defConst] at hs
  obtain ⟨v, hvE, hvT, e⟩ := Ideal.projT_eq_iSup.1 hs
  refine RT.closed' e fun t ht => ?_
  have htE := hvE t ht
  have htT := hvT t ht
  have tele := RT.telescope levels sound (CCtx.toTele Θ) (Γ := .nil)
    (by rw [CCtx.pis_toTele]; exact ⟨u, hu, tD⟩) (by rw [CCtx.pis_toTele]; exact hD)
    (by rw [CCtx.extend_toTele]; exact rhs) Env.nil trivial formed SubstRel.nil (red formed)
    (red formed) t (by rw [CCtx.lams_toTele]; exact htE) (by rw [CCtx.pis_toTele]; exact htT)
  rw [CCtx.pis_toTele, CTm.subst_var_comp] at tele
  exact tele

end Definitions

/-! ## The quantifier over an adequate carrier -/

section Codes

variable {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

include levels in
/-- **The quantifier over an adequate carrier, at its own type of codes.** Let `all` be a
quantifier code whose decoding at a family `f` is the dependent function type over the
carrier `A` of the decodings of `f`, and let the type tokens of a carrier ideal `C` relate
`A` to itself. For every token of the quantifier constant over `C` typed at
`(C → prop) → prop`, the quantifier is related to itself at `(A → prop) → prop`. The
codes of related families are related by the clause of the universe of codes: their
decodings, head-expanded along the decoder's root step, are dependent function types over
`A`, related at the domain tokens and the typed family entries of the decoded type; a
family entry's values are related by the families' clause at the function entries of the
witness whose inputs the entry's input entails. -/
theorem RT.allCodeAt {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) (all : DeclName)
    {A : CTm Head n} {C : Ideal}
    (hC : ∀ d, C.Mem d → TyTok Elem.univ d → RT H Γ false d A A A)
    {u₀ w₀ : Head} (hu₀ : R.isUniverse u₀) (hw₀ : R.isUniverse w₀)
    (tProp : ∀ {m : Nat} {Δ : CCtx Head m}, CTyped P Δ (.const K.prop) (.head u₀))
    (tA : CTyped P Γ A (.head w₀))
    (tAll : CTyped P Γ (.const all) (.pi (.pi A (.const K.prop)) (.const K.prop)))
    (decode : ∀ f : CTm Head n, P.computation.step (.app (.const K.holds) (.app (.const all) f))
      (.pi A (.app (.const K.holds) (.app (f.rename wk) (.var 0)))))
    (admits : ∀ {f : CTm Head n}, CTyped P Γ f (.pi A (.const K.prop)) →
      P.Admits Γ (.app (.const K.holds) (.app (.const all) f))
        (.pi A (.app (.const K.holds) (.app (f.rename wk) (.var 0))))) :
    ∀ s, (Ideal.allConst C).Mem s →
      TypedAt (Ideal.cpi (Ideal.cpi C fun _ => codesIdeal) fun _ => codesIdeal) s →
        RT H Γ true s (.pi (.pi A (.const K.prop)) (.const K.prop)) (.const all) (.const all) := by
  intro s hs hsT
  obtain ⟨b, hb, hbu, hts⟩ := hsT
  have hbF : Ideal.Below b (Ideal.former .pi (Ideal.cpi C fun _ => codesIdeal)
      fun _ => codesIdeal) := hb
  obtain ⟨X, Y, rfl, hXt, hYt⟩ := Ideal.tyTok_below_pi hbF hts
  -- the typed tokens
  have hYU : ∀ y ∈ Y, TyTok Elem.univ y := by
    intro y hy
    have hbelow : Ideal.Below (fnApp .pi b X) codesIdeal := by
      have h := Ideal.below_fam_fnApp (k := .pi) (y := principal X) hb
        (fun x hx => ent_of_mem hx)
      rwa [show Ideal.cpi (Ideal.cpi C fun _ => codesIdeal) (fun _ => codesIdeal) =
        Ideal.former .pi (Ideal.cpi C fun _ => codesIdeal) (fun _ => codesIdeal)
        from rfl, Ideal.fam_former_const] at h
    exact Ideal.typedAt_codes_iff.1 ⟨_, hbelow, Ideal.ty_fnApp (.inl rfl) hbu X, hYt y hy⟩
  have hdom : Ideal.Below (args .pi 0 b) (Ideal.former .pi C fun _ => codesIdeal) :=
    Ideal.below_args_former hbF
  have hdomU : Ty (args .pi 0 b) Elem.univ := Ideal.ty_args_dom (.inl rfl) hbu
  have hXU : ∀ C' Z W, Tok.fn .lam C' Z W ∈ X → ∀ w ∈ W, TyTok Elem.univ w := by
    intro C' Z W hx w hw
    obtain ⟨Z', W', e, -, hW'⟩ := Ideal.tyTok_below_pi hdom (hXt _ hx)
    injection e with _ eC eZ eW
    subst eC eZ eW
    have hbelow : Ideal.Below (fnApp .pi (args .pi 0 b) Z) codesIdeal := by
      have h := Ideal.below_fam_fnApp (k := .pi) (y := principal Z) hdom
        (fun x hx => ent_of_mem hx)
      rwa [Ideal.fam_former_const] at h
    exact Ideal.typedAt_codes_iff.1 ⟨_, hbelow, Ideal.ty_fnApp (.inl rfl) hdomU Z, hW' w hw⟩
  -- the value of the quantifier's function at the input
  have hY : Ideal.Below Y (Ideal.cpi C fun x => projT codesIdeal (Ideal.app (principal X) x)) :=
    (Ideal.mem_lam_fn (Ideal.allRaw_monotone C)).1 (Ideal.projT_le _ _ _ hs)
  -- the syntactic facts
  have propRed : CRedTy H Γ (.const K.prop) (.const K.prop) := CRedTy.refl ⟨u₀, hu₀, tProp⟩
  obtain ⟨u, hu, tHolds⟩ := K.holds_typed Γ
  have tProp' : CTyped P (.snoc Γ A) (.const K.prop) (.head u₀) := tProp
  obtain ⟨u', hu', tHolds'⟩ := K.holds_typed (.snoc Γ A)
  have holdsFam : ∀ {g : CTm Head n}, CTyped P Γ g (.pi A (.const K.prop)) →
      CTyped P (.snoc Γ A) (.app (.const K.holds) (.app (g.rename wk) (.var 0)))
        (.head u') := fun tg =>
    .appElim tHolds' (.appElim (CTyped.weaken tg) (.var 0))
  -- decoding a quantified code
  have decRed : ∀ {g : CTm Head n}, CTyped P Γ g (.pi A (.const K.prop)) →
      CRedTy H Γ (.app (.const K.holds) (.app (.const all) g))
        (.pi A (.app (.const K.holds) (.app (g.rename wk) (.var 0)))) := by
    intro g tg
    obtain ⟨w₁, join₁⟩ := levels.join_exists hw₀ hu'
    have tLeft : CTyped P Γ (.app (.const K.holds) (.app (.const all) g)) (.head u) :=
      .appElim tHolds (.appElim tAll tg)
    have tRight : CTyped P Γ (.pi A
        (.app (.const K.holds) (.app (g.rename wk) (.var 0)))) (.head w₁) :=
      .piForm tA hw₀ (holdsFam tg) hu' join₁
    obtain ⟨w₂, join₂⟩ := levels.join_exists (levels.join_level join₁).1 hu
    obtain ⟨c₁, c₂⟩ := levels.join_upper join₂
    exact ⟨.single (H.root (decode g)), w₂, (levels.join_level join₂).1,
      .rootAdmitted (decode g) (admits tg) (.cumul tLeft c₂) (.cumul tRight c₁)⟩
  -- the families' values at related arguments, as far as the value tokens observe
  have extract : ∀ {Z : List Tok} {g h : CTm Head n},
      (∀ C' Z'' W'', Tok.fn .lam C' Z'' W'' ∈ X →
        (∀ z ∈ Z'', (projT C (principal Z)).Mem z) → ∀ w'' ∈ W'',
          RT H Γ true w'' (.const K.prop) g h) →
      ∀ w, (projT codesIdeal (Ideal.app (principal X) (projT C (principal Z)))).Mem w →
          RT H Γ false w (.app (.const K.holds) g) (.app (.const K.holds) g)
            (.app (.const K.holds) h) := by
    intro Z g h hw₀' w hw
    obtain ⟨v, hv, e⟩ := hw
    refine RT.closed' e fun q hq => ?_
    obtain ⟨Z', Y', hZ', hXZY, hq'⟩ := Ideal.mem_app.1 (hv q hq).1
    have hent : ∀ y' ∈ Y', ent (fnApp .lam X Z') y' = true := by
      have h' : ent X (.fn .lam [] Z' Y') = true := hXZY
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h'
      exact h'.2
    refine RT.closed' (ent_cut hq' hent) fun w'' hw'' => ?_
    obtain ⟨C', Z'', W'', hmem, hZ''Z', hw''W⟩ := mem_fnApp'.1 hw''
    exact RT.toCodes (typeKind_of_tyTok_univ (hXU _ _ _ hmem w'' hw''W)) propRed
      (hw₀' C' Z'' W'' hmem (fun z hz => (projT C (principal Z)).closed hZ' (hZ''Z' z hz))
        w'' hw''W)
  -- the type of code-valued families over the carrier
  obtain ⟨w₃, join₃⟩ := levels.join_exists hw₀ hu₀
  have piProp : CIsType P Γ (.pi A (.const K.prop)) :=
    ⟨w₃, (levels.join_level join₃).1, .piForm tA hw₀ tProp' hu₀ join₃⟩
  have eA : CTypeEq P Γ A A := ⟨w₀, hw₀, .refl tA⟩
  have famOf : ∀ (g N : CTm Head n),
      CTm.inst0 N (.app (.const K.holds) (.app (g.rename wk) (.var 0))) =
        .app (.const K.holds) (.app g N) := by
    intro g N
    change CTm.app (.const K.holds) (.app (CTm.inst0 N (g.rename wk)) N) = _
    rw [CTm.inst0_rename_wk]
  -- the codes of related families are related
  have core : ∀ {f f' : CTm Head n}, CEqual P Γ f f' (.pi A (.const K.prop)) →
      (∀ x ∈ X, RT H Γ true x (.pi A (.const K.prop)) f f') →
        ∀ y ∈ Y, RT H Γ true y (.const K.prop) (.app (.const all) f) (.app (.const all) f') := by
    intro f f' hff hX y hy
    obtain ⟨tf, tf'⟩ := CEqual.typed levels hff formed
    refine RT.ofCodes (typeKind_of_tyTok_univ (hYU y hy)) propRed ?_
    refine RT.expand_ty levels (T := .const K.prop) (decRed tf) (decRed tf') ?_
    have eFam : CTypeEq P (.snoc Γ A)
        (.app (.const K.holds) (.app (f.rename wk) (.var 0)))
        (.app (.const K.holds) (.app (f'.rename wk) (.var 0))) :=
      ⟨u', hu', .appCong (.refl tHolds') (.appCong (CEqual.weaken hff) (.refl (.var 0)))⟩
    have PR : PiRed H Γ (.pi A (.app (.const K.holds) (.app (f.rename wk) (.var 0))))
        (.pi A (.app (.const K.holds) (.app (f'.rename wk) (.var 0))))
        A (.app (.const K.holds) (.app (f.rename wk) (.var 0)))
        A (.app (.const K.holds) (.app (f'.rename wk) (.var 0))) :=
      ⟨CRedTy.refl (CTypeEq.isType levels (decRed tf).2 formed).2,
        CRedTy.refl (CTypeEq.isType levels (decRed tf').2 formed).2, eA, eFam⟩
    have valI : ∀ {N N' : CTm Head n}, CEqual P Γ N N' A → ∀ {Z : List Tok},
        (∀ z ∈ Z, RT H Γ true z A N N') →
        ∀ C' Z'' W'', Tok.fn .lam C' Z'' W'' ∈ X →
          (∀ z ∈ Z'', (projT C (principal Z)).Mem z) → ∀ w'' ∈ W'',
            RT H Γ true w'' (.const K.prop) (.app f N) (.app f N') ∧
              RT H Γ true w'' (.const K.prop) (.app f' N) (.app f' N') := by
      intro N N' hNN Z hZ C' Z'' W'' hmem hZ'' w'' hw''
      rcases RT.tm_lam_iff.1 (hX _ hmem) with hvac | hcl
      · exact ⟨RT.of_vacuous (vacuous_out hvac hw''), RT.of_vacuous (vacuous_out hvac hw'')⟩
      exact (hcl _ _ (CRedTy.refl piProp)).1 N N' hNN
        (fun z hz => RT.of_projT_principal _ hZ (hZ'' z hz)) w'' hw''
    have valII : ∀ {N : CTm Head n}, CTyped P Γ N A → ∀ {Z : List Tok},
        (∀ z ∈ Z, RT H Γ true z A N N) →
        ∀ C' Z'' W'', Tok.fn .lam C' Z'' W'' ∈ X →
          (∀ z ∈ Z'', (projT C (principal Z)).Mem z) → ∀ w'' ∈ W'',
            RT H Γ true w'' (.const K.prop) (.app f N) (.app f' N) := by
      intro N tN Z hZ C' Z'' W'' hmem hZ'' w'' hw''
      rcases RT.tm_lam_iff.1 (hX _ hmem) with hvac | hcl
      · exact RT.of_vacuous (vacuous_out hvac hw'')
      exact (hcl _ _ (CRedTy.refl piProp)).2 N tN
        (fun z hz => RT.of_projT_principal _ hZ (hZ'' z hz)) w'' hw''
    have hF : Ideal.Monotone fun Z =>
        projT codesIdeal (Ideal.app (principal X) (projT C (principal Z))) := fun h =>
      Ideal.projT_mono (Ideal.app_mono (Ideal.le_refl _) (Ideal.projT_mono (principal_mono h)))
    rcases typed_former_token (.inl rfl) hF (hY y hy) (hYU y hy) with hvac | rfl |
      ⟨d, rfl, hd, hdU⟩ | ⟨D, Z, W, rfl, hD, hW, hDU, -, -⟩
    · exact RT.of_vacuous hvac
    · exact RT.ty_pi_iff.2 ⟨_, _, _, _, PR⟩
    · exact RT.ty_argPi_iff.2 (.inr ⟨_, _, _, _, PR, fun c hc => absurd hc List.not_mem_nil,
        fun _ => hC d hd hdU⟩)
    · refine RT.ty_fnPi_iff.2 (.inr ⟨_, _, _, _, PR, fun c hc => hC c (hD c hc) (hDU c hc),
        fun N N' hNN hZ w hw => ?_, fun N tN hZ w hw => ?_⟩)
      · rw [famOf f N, famOf f N', famOf f' N, famOf f' N']
        exact ⟨extract (fun C' Z'' W'' hmem hZ'' w'' hw'' =>
            (valI hNN hZ C' Z'' W'' hmem hZ'' w'' hw'').1) w (hW w hw),
          extract (fun C' Z'' W'' hmem hZ'' w'' hw'' =>
            (valI hNN hZ C' Z'' W'' hmem hZ'' w'' hw'').2) w (hW w hw)⟩
      · rw [famOf f N, famOf f' N]
        exact extract (fun C' Z'' W'' hmem hZ'' w'' hw'' =>
          valII tN hZ C' Z'' W'' hmem hZ'' w'' hw'') w (hW w hw)
  -- the function clause
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  exact ⟨fun f f' hff hX y hy => ⟨core hff hX y hy, core hff hX y hy⟩,
    fun f tf hX y hy => core (.refl tf) hX y hy⟩

end Codes

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
