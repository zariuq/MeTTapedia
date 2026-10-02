import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationSigma
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationSub

/-!
# Validity: the statement of the fundamental lemma of the relation

**Adequacy of a type** (`AdequateType`): in every environment fitting the context,
related substitutions send the type to types related as far as every type token of
its denotation observes. It names no universe; at every universe it is adequacy of the
type as a term of that universe (`Adequate.adequateType`, `AdequateType.adequate`).

**Adequacy of a subtyping statement** (`AdequateSub`): both types are adequate, and
one substitution sends the lower type to a type usable at the upper one, as far as
every type token of the lower type's denotation observes.

**Validity** (`CStatement.Valid`) carries the adequacy of the type along with every
typing and every equation:

* a typing is valid when the term is adequate at the type and the type is adequate;
* an equation is valid when it is adequate at the type and the type is adequate;
* a subtyping statement is valid when it is adequate.

The type's adequacy is what the laws of the relation presuppose: symmetry and
transitivity of the term relation read the type's relation to itself, and the
application rule composes the two halves of the function clause by transitivity at the
family's value at the argument.

**The application case** (`CStatement.Valid.appElim`). The family of an adequate
dependent function type at an adequate argument of its domain is an adequate type
(`AdequateType.inst`): a type token of the family's value at the argument is the
output of a typed family entry of the dependent function type whose input is a finite
typed part of the argument; the family clause relates the two instances of the family
at the two substituted arguments, and the two families at the right one; transitivity
of the type relation composes them.

**The variables** (`CStatement.Valid.var`): related substitutions carry the relation
of each variable's type and of its values. A formed context whose entries are adequate
types (`CtxAdequate`) has its variables related to themselves over the least
environment (`Fits.bot`), along every renaming into a formed context (`SubstRel.vars`).

**The type tokens** of a dependent function or pair type are its tag, the domain tokens
of its domain and its typed family entries (`typed_former_token`); those of an identity
type are its tag, the carrier tokens and the endpoint tokens (`typed_ident_token`).

**Formation.** A universe is an adequate type (`AdequateType.universe`), and so is a
head read as the ground type that is one of the rigid ground types
(`AdequateType.groundHead`); dependent function and pair types of adequate components
(`AdequateType.pi`, `AdequateType.sigma`) and identity types of an adequate carrier
between adequate endpoints (`AdequateType.ident`) are adequate. Hence the validity of
the formation rules: of a head's typing when the heads that are not universes are rigid
ground types (`RigidTypes.GroundHeads`, `CStatement.Valid.headType`), and of the
formation of dependent function, dependent pair and identity types
(`CStatement.Valid.piForm`, `CStatement.Valid.sigmaForm`, `CStatement.Valid.idForm`).

**Conversion, subsumption and abstraction** (`CStatement.Valid.conv`,
`CStatement.Valid.sub`, `CStatement.Valid.lamIntro`): subsumption moves the term's
relation along the lower type's usability at the upper one, the two types denoting
alike.

**Constants** (`CStatement.Valid.constAt`, `CStatement.Valid.const`): a declared constant
is valid at its declared type when it is adequate (`ConstAdequateAt`): related to itself at
its declared type, given that the declared type is an adequate type, which is the
validity of the declared type's own formation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypedAt TypeGenerated principal)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## Definitions -/

section Definitions

variable (Rd : Reading Head) {P : ChurchRules R} {K : RigidTypes P} (H : HeadReduction P K)

/-- **Adequacy of a type**: in every environment fitting the context, related
substitutions send the type to types related as far as every type token of its
denotation observes. -/
def AdequateType {n : Nat} (Γ : CCtx Head n) (A : CTm Head n) : Prop :=
  ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ σ' : CSub Head n m}, CCtxFormed P Δ →
    SubstRel Rd H Γ ρ Δ σ σ' → ∀ r, (cinterp Rd A ρ).Mem r → TyTok Elem.univ r →
      RT H Δ false r (A.subst σ) (A.subst σ) (A.subst σ')

/-- **Adequacy of a subtyping statement**: both types are adequate, and one
substitution sends the lower type to a type usable at the upper one, as far as every
type token of the lower type's denotation observes. -/
def AdequateSub {n : Nat} (Γ : CCtx Head n) (A B : CTm Head n) : Prop :=
  AdequateType Rd H Γ A ∧ AdequateType Rd H Γ B ∧
    ∀ ρ, Fits Rd Γ ρ → ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head n m}, CCtxFormed P Δ →
      SubstRel Rd H Γ ρ Δ σ σ → ∀ r, (cinterp Rd A ρ).Mem r → TyTok Elem.univ r →
        RTSub H Δ r (A.subst σ) (B.subst σ)

/-- **Validity** of an annotated statement: a typing is valid when the term is adequate
at the type and the type is adequate; an equation, when it is adequate at the type and
the type is adequate; a subtyping statement, when it is adequate. -/
def CStatement.Valid : CStatement Head → Prop
  | .typing Γ t A => Adequate Rd H Γ t A ∧ AdequateType Rd H Γ A
  | .equality Γ a b A => AdequateEq Rd H Γ a b A ∧ AdequateType Rd H Γ A
  | .sub Γ A B => AdequateSub Rd H Γ A B

/-- **An adequate context**: every entry is an adequate type over the entries before
it. -/
def CtxAdequate : {n : Nat} → CCtx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => CtxAdequate Γ ∧ AdequateType Rd H Γ A

/-- **Adequacy of a declared constant**: when its declared type is a type of a universe
and an adequate type, the constant is related to itself at its declared type, in every
formed context, as far as every token of its denotation typed at the declared type's
denotation observes. -/
def ConstAdequateAt (c : DeclName) : Prop :=
  ∀ {D : CTm Head 0} {u : Head}, P.constantType c = some D → R.isUniverse u →
    CTyped P .nil D (.head u) → AdequateType Rd H .nil D → ∀ {m : Nat} {Δ : CCtx Head m},
      CCtxFormed P Δ → ∀ s, (Rd.const c).Mem s → TypedAt (cinterp Rd D Env.nil) s →
        RT H Δ true s D.liftClosed (.const c) (.const c)

/-- **Adequacy of the declared constants**: every declared constant is adequate. -/
def ConstAdequate : Prop := ∀ {c : DeclName}, ConstAdequateAt Rd H c

end Definitions

/-! ## Adequate types are adequate terms of every universe -/

section Universes

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- A term adequate at a universe is an adequate type. -/
theorem Adequate.adequateType {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {u : Head}
    (hu : R.isUniverse u) (hA : Adequate Rd H Γ A (.head u)) : AdequateType Rd H Γ A := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  exact Adequate.toType levels sound hu hA fits formed hσ hr hrU

include levels sound in
/-- An adequate type is an adequate term of every universe. -/
theorem AdequateType.adequate {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {u : Head}
    (hu : R.isUniverse u) (hA : AdequateType Rd H Γ A) : Adequate Rd H Γ A (.head u) := by
  intro ρ fits m Δ σ σ' formed hσ s hs hsU
  have hsU' := sound.tyTok_of_typedAt_head hu hsU
  exact RT.ofType (typeKind_of_tyTok_univ hsU') hu
    (CRedTy.refl (CIsType.head_of_universe levels hu)) (hA ρ fits formed hσ s hs hsU')

end Universes

/-! ## The family of a dependent function type at an argument -/

section Instance

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **The family of an adequate dependent function type at an adequate argument is an
adequate type.** A type token of the family's value at the argument is the output of a
typed family entry of the dependent function type, whose input is a finite typed part
of the argument and whose dependency is a type witness of that part below the domain.
At that entry, the family clause relates the family's instances at the two substituted
arguments, and, at the right argument, the two substituted families; the right argument
is related to itself at the left domain by symmetry, at the domain related to itself
as far as the witness observes. Transitivity of the type relation composes the two. -/
theorem AdequateType.inst {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n} {B : CTm Head (n + 1)}
    (hPi : AdequateType Rd H Γ (.pi A B)) (ha : Adequate Rd H Γ a A) (ta : CTyped P Γ a A) :
    AdequateType Rd H Γ (CTm.inst0 a B) := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  rw [CTm.subst_inst0, CTm.subst_inst0]
  have hG := cinterp_cont_cons Rd B ρ
  have haSem : projT (cinterp Rd A ρ) (cinterp Rd a ρ) = cinterp Rd a ρ :=
    (sound.typing ta ρ fits).2
  rw [cinterp_inst0, ← haSem] at hr
  -- a finite typed part of the argument that the token observes
  obtain ⟨X, hX, hrX⟩ := (hG.comp (Ideal.cont_projT (cinterp Rd A ρ))).finite hr
  obtain ⟨w, hwX, hwT, hrw⟩ := Ideal.family_typedObservations hG X r hrX
  have hwa : Ideal.Below w (cinterp Rd a ρ) := Ideal.Below.of_le hwX hX
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
  rcases RT.ty_fnPi_iff.1 (hPi ρ fits formed hσ _ hmem hty) with hvac | ⟨D, E, D', E', hp, hC, hf, hg⟩
  · exact RT.of_vacuous (vacuous_out hvac List.mem_cons_self)
  have e₁ := H.red_normal (H.normal_pi _ _) hp.1.1
  have e₂ := H.red_normal (H.normal_pi _ _) hp.2.1.1
  injection e₁ with _ e₁D e₁E
  injection e₂ with _ e₂D e₂E
  subst e₁D e₁E e₂D e₂E
  -- the two substituted arguments, related as far as the part observes
  have eaa : CEqual P Δ (a.subst σ) (a.subst σ') (A.subst σ) := CDerivable.functional ta hσ.1
  have haa : ∀ z ∈ w, RT H Δ true z (A.subst σ) (a.subst σ) (a.subst σ') := fun z hz =>
    ha ρ fits formed hσ z (hwa z hz) (hwT z hz)
  have h₁ := (hf _ _ eaa haa r List.mem_cons_self).1
  -- the right argument, related to itself at the left domain
  have hAself : ∀ q ∈ c, RT H Δ false q (A.subst σ) (A.subst σ) (A.subst σ) := fun q hq =>
    RT.left (hC q hq)
  have ha' : ∀ z ∈ w, RT H Δ true z (A.subst σ) (a.subst σ') (a.subst σ') := fun z hz =>
    RT.left (RT.symm levels formed hcu (hwc z hz) hAself (haa z hz))
  have h₂ := hg _ (CEqual.typed levels eaa formed).2 ha' r List.mem_cons_self
  exact RT.trans_ty levels formed hrU h₁ h₂

end Instance

/-! ## Application -/

section Application

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **Validity of application.** The application is adequate at the family's value at
the argument by the application's compatibility lemma, at a universe of the substituted
dependent function type; the family's value is an adequate type by
`AdequateType.inst`. -/
theorem CStatement.Valid.appElim {n : Nat} {Γ : CCtx Head n} {g a A : CTm Head n}
    {B : CTm Head (n + 1)} (hg : (CStatement.typing Γ g (.pi A B)).Valid Rd H)
    (ha : (CStatement.typing Γ a A).Valid Rd H) (tg : CTyped P Γ g (.pi A B))
    (ta : CTyped P Γ a A) : (CStatement.typing Γ (.app g a) (CTm.inst0 a B)).Valid Rd H := by
  refine ⟨fun ρ fits m Δ σ σ' formed hσ => ?_, AdequateType.inst levels sound hg.2 ha.1 ta⟩
  obtain ⟨u, hu, -⟩ := CTyped.isType levels (tg.substitute hσ.1.1) formed
  exact Adequate.app levels sound hu (hg.2.adequate levels sound hu) hg.1 ha.1 tg ta ρ fits
    formed hσ

end Application

/-! ## Variables -/

section Variables

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}

/-- **Validity of a variable**: related substitutions relate each variable's values and
its type. -/
theorem CStatement.Valid.var {n : Nat} {Γ : CCtx Head n} (i : Fin n) :
    (CStatement.typing Γ (.var i) (Γ.lookup i)).Valid Rd H := by
  refine ⟨?_, ?_⟩
  · intro ρ fits m Δ σ σ' formed hσ s hs hsT
    exact (hσ.2 i).2.2 s hs hsT
  · intro ρ fits m Δ σ σ' formed hσ r hr hrU
    exact (hσ.2 i).2.1 r hr hrU

/-- A renaming, as a substitution, is renaming. -/
theorem CTm.subst_var_comp {n m : Nat} (ξ : Ren n m) (t : CTm Head n) :
    t.subst (fun i => .var (ξ i)) = t.rename ξ := by
  rw [← CTm.subst_ids (t.rename ξ), CTm.subst_rename]
  rfl

/-- **The variables of an adequate context are related over the least environment**:
along every renaming into a formed context, the variables of an adequate context that
the least environment fits go to variables related to themselves. The relation of each
entry comes from the entry's adequacy over the prefix, along the renaming restricted to
the prefix; the values of the least environment observe nothing. -/
theorem SubstRel.vars : ∀ {n : Nat} {Γ : CCtx Head n}, CtxAdequate Rd H Γ →
    Fits Rd Γ (fun _ => Ideal.bot) → ∀ {m : Nat} {Δ : CCtx Head m} {ξ : Ren n m},
      CCtxFormed P Δ → CCtxRen Γ Δ ξ →
        SubstRel Rd H Γ (fun _ => Ideal.bot) Δ (fun i => .var (ξ i)) (fun i => .var (ξ i))
  | _, .nil, _, _, _, _, _, _, _ => ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
  | _, .snoc Γ A, hΓ, fits, m, Δ, ξ, formed, hξ => by
      have typedVar : ∀ i, CTyped P Δ (.var (ξ i))
          (((CCtx.snoc Γ A).lookup i).subst fun j => .var (ξ j)) := fun i => by
        rw [CTm.subst_var_comp, ← hξ i]
        exact .var (ξ i)
      have hξ' : CCtxRen Γ Δ (fun j => ξ j.succ) := fun j => by
        rw [hξ j.succ, CCtx.lookup_snoc_succ, CTm.rename_comp]
        rfl
      have ih := SubstRel.vars hΓ.1 fits.1 formed hξ'
      refine ⟨⟨typedVar, fun i => .refl (typedVar i)⟩, fun i => ?_⟩
      have typeI : CIsType P Δ (((CCtx.snoc Γ A).lookup i).subst fun j => .var (ξ j)) := by
        rw [CTm.subst_var_comp, ← hξ i]
        exact formed.lookup (ξ i)
      refine ⟨typeI.refl, ?_, fun s hs _ => RT.of_vacuous hs⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · intro r hr hrU
        simp only [CCtx.lookup_snoc_zero, CTm.subst_rename] at hr ⊢
        rw [cinterp_rename] at hr
        exact hΓ.2 _ fits.1 formed ih r hr hrU
      · intro r hr hrU
        simp only [CCtx.lookup_snoc_succ, CTm.subst_rename] at hr ⊢
        rw [cinterp_rename] at hr
        exact (ih.2 j).2.1 r hr hrU

/-- **The least environment fits every formed context**: each entry denotes a
type-generated type, of which the least element is an element. -/
theorem Fits.bot (sound : SoundnessFacts Rd P) :
    ∀ {n : Nat} {Γ : CCtx Head n}, CCtxFormed P Γ → Fits Rd Γ (fun _ => Ideal.bot)
  | _, .nil, _ => trivial
  | _, .snoc _ _, .snoc formed ⟨_, hu, tA⟩ =>
      ⟨Fits.bot sound formed, sound.typeGenerated_of_head hu tA (Fits.bot sound formed),
        Ideal.le_antisymm (Ideal.projT_le _ _) (Ideal.bot_le _)⟩

end Variables

/-! ## The type tokens of dependent types and identity types -/

section TypeTokens

/-- The carrier component of a token of an identity type is in its carrier. -/
theorem mem_ident_carrier {A I J : Ideal} {d : Tok}
    (h : (Ideal.ident A I J).Mem (.arg .ident 0 [] d)) : A.Mem d := by
  obtain ⟨w, hw, h⟩ := h
  rw [ent_arg, List.all_nil, Bool.true_and] at h
  refine A.closed (v := args .ident 0 w) (fun c hc => ?_) h
  rcases mem_args_iff.1 hc with ⟨C, hC⟩ | ⟨-, t, ht, -, hd⟩
  · rcases hw _ hC with h' | ⟨d', h', hd'⟩ | ⟨C', r, h', -, -⟩ | ⟨C', r, h', -, -⟩
    · cases h'
    · cases h'
      exact hd'
    · simp at h'
    · simp at h'
  · rcases hw _ ht with rfl | ⟨d', rfl, -⟩ | ⟨C', r, rfl, hC', -⟩ | ⟨C', r, rfl, hC', -⟩
    · simp [Tok.dep] at hd
    · simp [Tok.dep] at hd
    · exact hC' c hd
    · exact hC' c hd

/-- **The type tokens of a dependent type built by `former`**: a type token of the
dependent function or pair type with domain `A` and family `F` is entailed by the empty
list, or it is the tag, a domain token whose component is a type token of the domain,
or a family entry whose dependency is in the domain and whose output is in the family's
value at its input, typed as a type token. -/
theorem typed_former_token {k : Kind} (hk : k = .pi ∨ k = .sigma) {A : Ideal}
    {F : List Tok → Ideal} (hF : Ideal.Monotone F) {t : Tok} (ht : (Ideal.former k A F).Mem t)
    (hty : TyTok Elem.univ t) :
    ent [] t = true ∨ t = .tag k ∨ (∃ d, t = .arg k 0 [] d ∧ A.Mem d ∧ TyTok Elem.univ d) ∨
      ∃ C X Y, t = .fn k C X Y ∧ Ideal.Below C A ∧ Ideal.Below Y (F X) ∧
        (∀ c ∈ C, TyTok Elem.univ c) ∧ (∀ x ∈ X, TyTok C x) ∧ ∀ y ∈ Y, TyTok Elem.univ y := by
  cases hv : ent [] t with
  | true => exact .inl rfl
  | false =>
  refine .inr ?_
  have htk : t.kind = k := by
    obtain ⟨v, hgen, hent⟩ := ht
    obtain ⟨s, hs, hks, -⟩ := source_of_ent hent hv
    rw [← hks]
    rcases hgen s hs with rfl | ⟨d, rfl, -⟩ | ⟨D, X, Y, rfl, -⟩ <;> rfl
  cases t with
  | tag k' =>
      cases htk
      exact .inl rfl
  | arg k' i C d =>
      change k' = k at htk
      subst htk
      rcases i with _ | i
      · obtain ⟨-, rfl, hd⟩ := (tyTok_dom (by rcases hk with rfl | rfl <;> simp)).1 hty
        exact .inr (.inl ⟨d, rfl, Ideal.mem_former_dom.1 ht, hd⟩)
      · rcases hk with rfl | rfl
        · exact absurd hty tyTok_argPi_succ
        · exact absurd hty tyTok_argSigma_succ
  | fn k' C X Y =>
      change k' = k at htk
      subst htk
      obtain ⟨-, hC, hX, hY⟩ := (tyTok_family hk).1 hty
      obtain ⟨hCA, hYF⟩ := (Ideal.mem_former_fn hF).1 ht
      exact .inr (.inr ⟨C, X, Y, rfl, hCA, hYF, hC, hX, hY⟩)

/-- **The type tokens of an identity type**: a type token of the identity type of
carrier `A` between `I` and `J` is entailed by the empty list, or it is the tag, a
carrier token whose component is a type token of the carrier, or an endpoint token
whose dependency is a compact type below the carrier at which its component, an
element of the endpoint, is typed. -/
theorem typed_ident_token {A I J : Ideal} {t : Tok} (ht : (Ideal.ident A I J).Mem t)
    (hty : TyTok Elem.univ t) :
    ent [] t = true ∨ t = .tag .ident ∨
      (∃ d, t = .arg .ident 0 [] d ∧ A.Mem d ∧ TyTok Elem.univ d) ∨
      (∃ C s, t = .arg .ident 1 C s ∧ Ideal.Below C A ∧ I.Mem s ∧
        (∀ c ∈ C, TyTok Elem.univ c) ∧ TyTok C s) ∨
      ∃ C s, t = .arg .ident 2 C s ∧ Ideal.Below C A ∧ J.Mem s ∧
        (∀ c ∈ C, TyTok Elem.univ c) ∧ TyTok C s := by
  cases hv : ent [] t with
  | true => exact .inl rfl
  | false =>
  refine .inr ?_
  have htk : t.kind = .ident := by
    obtain ⟨v, hgen, hent⟩ := ht
    obtain ⟨s, hs, hks, -⟩ := source_of_ent hent hv
    rw [← hks]
    rcases hgen s hs with rfl | ⟨d, rfl, -⟩ | ⟨C, r, rfl, -, -⟩ | ⟨C, r, rfl, -, -⟩ <;> rfl
  cases t with
  | tag k' =>
      cases htk
      exact .inl rfl
  | arg k' i C s =>
      change k' = .ident at htk
      subst htk
      rcases i with _ | _ | _ | i
      · obtain ⟨-, rfl, hd⟩ := (tyTok_dom (.inr (.inr rfl))).1 hty
        exact .inr (.inl ⟨s, rfl, mem_ident_carrier ht, hd⟩)
      · obtain ⟨-, hC, hs⟩ := (tyTok_endpoint (.inl rfl)).1 hty
        obtain ⟨hCA, hI, -⟩ := Ideal.mem_ident_arg ht
        exact .inr (.inr (.inl ⟨C, s, rfl, hCA, hI rfl, hC, hs⟩))
      · obtain ⟨-, hC, hs⟩ := (tyTok_endpoint (.inr rfl)).1 hty
        obtain ⟨hCA, -, hJ⟩ := Ideal.mem_ident_arg ht
        exact .inr (.inr (.inr ⟨C, s, rfl, hCA, hJ rfl, hC, hs⟩))
      · exact absurd hty tyTok_argIdent_high
  | fn k' C X Y =>
      change k' = .ident at htk
      subst htk
      exact absurd hty (tyTok_fn_other ⟨nofun, nofun, nofun⟩)

end TypeTokens

/-! ## Formation -/

/-- **The heads that are not universes are rigid ground types**: every head typed by a
head is a universe, or is read as the ground type and is one of the ground types of the
rigid types. -/
def RigidTypes.GroundHeads {P : ChurchRules R} (K : RigidTypes P) (Rd : Reading Head) : Prop :=
  ∀ {h u : Head}, R.headTyping h u → R.isUniverse h ∨
    (Rd.head h = Elem.ground ∧ ∀ {n : Nat}, K.ground (.head h : CTm Head n))

section Formation

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

include levels sound in
/-- **A universe is an adequate type**: the only type token of its denotation that the
empty list does not entail is the tag of universes, at which a universe head is related
to itself. -/
theorem AdequateType.universe {n : Nat} {Γ : CCtx Head n} {u : Head} (hu : R.isUniverse u) :
    AdequateType Rd H Γ (.head u) := by
  intro ρ fits m Δ σ σ' formed hσ r hr _
  have hr' : ent Elem.univ r = true := by
    have h : (principal (Rd.head u)).Mem r := hr
    rwa [sound.universes hu] at h
  refine RT.closed' hr' fun q hq => ?_
  rw [List.mem_singleton.1 hq]
  have hU : CRedTy H Δ (.head u : CTm Head m) (.head u) :=
    CRedTy.refl (CIsType.head_of_universe levels hu)
  exact RT.ty_univ_iff.2 ⟨u, u, hU, hU, hu, hu, .inl rfl⟩

include levels in
/-- **A ground head is an adequate type**: a head typed by a head, read as the ground
type and one of the rigid ground types, is related to itself at the tag of ground
types. -/
theorem AdequateType.groundHead {n : Nat} {Γ : CCtx Head n} {h u : Head}
    (typing : R.headTyping h u) (read : Rd.head h = Elem.ground)
    (ground : ∀ {n : Nat}, K.ground (.head h : CTm Head n)) : AdequateType Rd H Γ (.head h) := by
  intro ρ fits m Δ σ σ' formed hσ r hr _
  have hr' : ent Elem.ground r = true := by
    have h' : (principal (Rd.head h)).Mem r := hr
    rwa [read] at h'
  refine RT.closed' hr' fun q hq => ?_
  rw [List.mem_singleton.1 hq]
  have hG : CRedTy H Δ (.head h : CTm Head m) (.head h) :=
    CRedTy.refl ⟨u, levels.ground_typing typing, .headType typing⟩
  exact RT.ty_ground_iff.2 ⟨.head h, ground, hG, hG⟩

include levels sound in
/-- **A dependent function type of adequate components is adequate.** Its type tokens
are its tag, the domain tokens of its domain, and its typed family entries. At an entry
with input `X`, arguments related as far as `X` observes extend each substitution to
substitutions related over the environment extended by the projection of `X` onto the
domain, and the family's adequacy there relates its instances; the domain is moved from
the left substitution to the right one by conversion. -/
theorem AdequateType.pi {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
    (tPi : CIsType P Γ (.pi A B)) (hA : AdequateType Rd H Γ A)
    (hB : AdequateType Rd H (.snoc Γ A) B) : AdequateType Rd H Γ (.pi A B) := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  obtain ⟨⟨w, hw, tA⟩, ⟨v, hv, tB⟩⟩ := CIsType.pi_parts tPi
  have hσ' := hσ.symm levels formed
  have eA : CTypeEq P Δ (A.subst σ) (A.subst σ') := ⟨w, hw, CDerivable.functional tA hσ.1⟩
  have eB : CTypeEq P (.snoc Δ (A.subst σ)) (B.subst (CTm.liftSub σ))
      (B.subst (CTm.liftSub σ')) := ⟨v, hv, CDerivable.functional tB (hσ.1.lift A)⟩
  have piRed : PiRed H Δ ((CTm.pi A B).subst σ) ((CTm.pi A B).subst σ') (A.subst σ)
      (B.subst (CTm.liftSub σ)) (A.subst σ') (B.subst (CTm.liftSub σ')) := by
    obtain ⟨u, hu, tPi⟩ := tPi
    exact ⟨CRedTy.refl ⟨u, hu, tPi.substitute hσ.1.1⟩, CRedTy.refl ⟨u, hu, tPi.substitute hσ'.1.1⟩,
      eA, eB⟩
  have relA : ∀ {τ τ' : CSub Head n m}, SubstRel Rd H Γ ρ Δ τ τ' → ∀ q,
      (cinterp Rd A ρ).Mem q → TyTok Elem.univ q →
        RT H Δ false q (A.subst τ) (A.subst τ) (A.subst τ') := fun hτ q hq hqU =>
    hA ρ fits formed hτ q hq hqU
  have hG := cinterp_cont_cons Rd B ρ
  have hF : Ideal.Monotone fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    hG.mono (Ideal.projT_mono (principal_mono h))
  rcases typed_former_token (.inl rfl) hF hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
    ⟨C, X, Y, rfl, hCA, hYF, hC, -, hY⟩
  · exact RT.of_vacuous hvac
  · exact RT.ty_pi_iff.2 ⟨_, _, _, _, piRed⟩
  · exact RT.ty_argPi_iff.2 (.inr ⟨_, _, _, _, piRed, fun c hc => absurd hc List.not_mem_nil,
      fun _ => relA hσ d hd hdU⟩)
  · have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
      ⟨fits, sound.typeGenerated_of_head hw tA fits, Ideal.projT_projT _ _⟩
    have famAt : ∀ {τ τ' : CSub Head (n + 1) m}, SubstRel Rd H (.snoc Γ A)
        (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ τ τ' →
          ∀ y ∈ Y, RT H Δ false y (B.subst τ) (B.subst τ) (B.subst τ') := fun hτ y hy =>
      hB _ fits' formed hτ y (hYF y hy) (hY y hy)
    refine RT.ty_fnPi_iff.2 (.inr ⟨_, _, _, _, piRed, fun c hc => relA hσ c (hCA c hc) (hC c hc),
      fun N N' hNN hNX y hy => ?_, fun N tN hNX y hy => ?_⟩)
    · simp only [CTm.inst0_subst_liftSub]
      refine ⟨famAt (SubstRel.cons levels formed hσ.left hNN eA.left (relA hσ.left)
        (fun s hs _ => RT.of_projT_principal _ hNX hs)) y hy, famAt (SubstRel.cons levels formed
          hσ'.left (hNN.convType eA) eA.symm.left (relA hσ'.left) (fun s hs hsT => ?_)) y hy⟩
      obtain ⟨a, ha, hau, hta⟩ := hsT
      exact (RT.conv_iff levels formed hau hta (fun q hq => relA hσ q (ha q hq) (hau q hq)) eA).1
        (RT.of_projT_principal _ hNX hs)
    · simp only [CTm.inst0_subst_liftSub]
      exact famAt (SubstRel.cons levels formed hσ (.refl tN) eA (relA hσ)
        (fun s hs _ => RT.of_projT_principal _ hNX hs)) y hy

include levels sound in
/-- **A dependent pair type of adequate components is adequate**, as for dependent
function types. -/
theorem AdequateType.sigma {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
    (tSig : CIsType P Γ (.sigma A B)) (hA : AdequateType Rd H Γ A)
    (hB : AdequateType Rd H (.snoc Γ A) B) : AdequateType Rd H Γ (.sigma A B) := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  obtain ⟨⟨w, hw, tA⟩, ⟨v, hv, tB⟩⟩ := CIsType.sigma_parts tSig
  have hσ' := hσ.symm levels formed
  have eA : CTypeEq P Δ (A.subst σ) (A.subst σ') := ⟨w, hw, CDerivable.functional tA hσ.1⟩
  have eB : CTypeEq P (.snoc Δ (A.subst σ)) (B.subst (CTm.liftSub σ))
      (B.subst (CTm.liftSub σ')) := ⟨v, hv, CDerivable.functional tB (hσ.1.lift A)⟩
  have sigRed : SigmaRed H Δ ((CTm.sigma A B).subst σ) ((CTm.sigma A B).subst σ') (A.subst σ)
      (B.subst (CTm.liftSub σ)) (A.subst σ') (B.subst (CTm.liftSub σ')) := by
    obtain ⟨u, hu, tSig⟩ := tSig
    exact ⟨CRedTy.refl ⟨u, hu, tSig.substitute hσ.1.1⟩,
      CRedTy.refl ⟨u, hu, tSig.substitute hσ'.1.1⟩, eA, eB⟩
  have relA : ∀ {τ τ' : CSub Head n m}, SubstRel Rd H Γ ρ Δ τ τ' → ∀ q,
      (cinterp Rd A ρ).Mem q → TyTok Elem.univ q →
        RT H Δ false q (A.subst τ) (A.subst τ) (A.subst τ') := fun hτ q hq hqU =>
    hA ρ fits formed hτ q hq hqU
  have hG := cinterp_cont_cons Rd B ρ
  have hF : Ideal.Monotone fun X =>
      cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) := fun h =>
    hG.mono (Ideal.projT_mono (principal_mono h))
  rcases typed_former_token (.inr rfl) hF hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
    ⟨C, X, Y, rfl, hCA, hYF, hC, -, hY⟩
  · exact RT.of_vacuous hvac
  · exact RT.ty_sigma_iff.2 ⟨_, _, _, _, sigRed⟩
  · exact RT.ty_argSigma_iff.2 (.inr ⟨_, _, _, _, sigRed, fun c hc => absurd hc List.not_mem_nil,
      fun _ => relA hσ d hd hdU⟩)
  · have fits' : Fits Rd (.snoc Γ A) (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) :=
      ⟨fits, sound.typeGenerated_of_head hw tA fits, Ideal.projT_projT _ _⟩
    have famAt : ∀ {τ τ' : CSub Head (n + 1) m}, SubstRel Rd H (.snoc Γ A)
        (Env.cons (projT (cinterp Rd A ρ) (principal X)) ρ) Δ τ τ' →
          ∀ y ∈ Y, RT H Δ false y (B.subst τ) (B.subst τ) (B.subst τ') := fun hτ y hy =>
      hB _ fits' formed hτ y (hYF y hy) (hY y hy)
    refine RT.ty_fnSigma_iff.2 (.inr ⟨_, _, _, _, sigRed,
      fun c hc => relA hσ c (hCA c hc) (hC c hc), fun N N' hNN hNX y hy => ?_,
      fun N tN hNX y hy => ?_⟩)
    · simp only [CTm.inst0_subst_liftSub]
      refine ⟨famAt (SubstRel.cons levels formed hσ.left hNN eA.left (relA hσ.left)
        (fun s hs _ => RT.of_projT_principal _ hNX hs)) y hy, famAt (SubstRel.cons levels formed
          hσ'.left (hNN.convType eA) eA.symm.left (relA hσ'.left) (fun s hs hsT => ?_)) y hy⟩
      obtain ⟨a, ha, hau, hta⟩ := hsT
      exact (RT.conv_iff levels formed hau hta (fun q hq => relA hσ q (ha q hq) (hau q hq)) eA).1
        (RT.of_projT_principal _ hNX hs)
    · simp only [CTm.inst0_subst_liftSub]
      exact famAt (SubstRel.cons levels formed hσ (.refl tN) eA (relA hσ)
        (fun s hs _ => RT.of_projT_principal _ hNX hs)) y hy

include levels in
/-- **An identity type of an adequate carrier between adequate endpoints is adequate.**
Its type tokens are its tag, the carrier tokens, and the endpoint tokens, whose
dependency is a type witness below the carrier at which the endpoint's token is
typed. -/
theorem AdequateType.ident {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {u : Head}
    (hu : R.isUniverse u) (tA : CTyped P Γ A (.head u)) (ta : CTyped P Γ a A)
    (tb : CTyped P Γ b A) (hA : AdequateType Rd H Γ A) (ha : Adequate Rd H Γ a A)
    (hb : Adequate Rd H Γ b A) : AdequateType Rd H Γ (.id A a b) := by
  intro ρ fits m Δ σ σ' formed hσ r hr hrU
  have hσ' := hσ.symm levels formed
  have tId : CTyped P Γ (.id A a b) (.head u) := .idForm tA hu ta tb
  have idRed : IdRed H Δ ((CTm.id A a b).subst σ) ((CTm.id A a b).subst σ') (A.subst σ)
      (a.subst σ) (b.subst σ) (A.subst σ') (a.subst σ') (b.subst σ') :=
    ⟨CRedTy.refl ⟨u, hu, tId.substitute hσ.1.1⟩, CRedTy.refl ⟨u, hu, tId.substitute hσ'.1.1⟩,
      ⟨u, hu, CDerivable.functional tA hσ.1⟩, CDerivable.functional ta hσ.1,
      CDerivable.functional tb hσ.1⟩
  have relA : ∀ q, (cinterp Rd A ρ).Mem q → TyTok Elem.univ q →
      RT H Δ false q (A.subst σ) (A.subst σ) (A.subst σ') := fun q hq hqU =>
    hA ρ fits formed hσ q hq hqU
  rcases typed_ident_token hr hrU with hvac | rfl | ⟨d, rfl, hd, hdU⟩ |
    ⟨C, s, rfl, hCA, hs, hC, hsC⟩ | ⟨C, s, rfl, hCA, hs, hC, hsC⟩
  · exact RT.of_vacuous hvac
  · exact RT.ty_ident_iff.2 ⟨_, _, _, _, _, _, idRed⟩
  · exact RT.ty_argIdent_iff.2 (.inr ⟨_, _, _, _, _, _, idRed,
      fun c hc => absurd hc List.not_mem_nil, fun _ => relA d hd hdU,
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
  · exact RT.ty_argIdent_iff.2 (.inr ⟨_, _, _, _, _, _, idRed,
      fun c hc => relA c (hCA c hc) (hC c hc), fun h => absurd h (by decide),
      fun _ => ha ρ fits formed hσ s hs ⟨C, hCA, hC, hsC⟩, fun h => absurd h (by decide)⟩)
  · exact RT.ty_argIdent_iff.2 (.inr ⟨_, _, _, _, _, _, idRed,
      fun c hc => relA c (hCA c hc) (hC c hc), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun _ => hb ρ fits formed hσ s hs ⟨C, hCA, hC, hsC⟩⟩)

include levels sound in
/-- **Validity of a head's typing**, for heads that are universes or rigid ground
types. -/
theorem CStatement.Valid.headType (heads : K.GroundHeads Rd) {n : Nat} {Γ : CCtx Head n}
    {h u : Head} (typing : R.headTyping h u) :
    (CStatement.typing Γ (.head h) (.head u)).Valid Rd H := by
  have hu := levels.ground_typing typing
  refine ⟨AdequateType.adequate levels sound hu ?_, AdequateType.universe levels sound hu⟩
  rcases heads typing with hh | ⟨read, ground⟩
  · exact AdequateType.universe levels sound hh
  · exact AdequateType.groundHead levels typing read ground

include levels sound in
/-- **Validity of the formation of dependent function types.** -/
theorem CStatement.Valid.piForm {n : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {B : CTm Head (n + 1)} {u v w : Head} (hA : (CStatement.typing Γ A (.head u)).Valid Rd H)
    (hu : R.isUniverse u) (hB : (CStatement.typing (.snoc Γ A) B (.head v)).Valid Rd H)
    (hv : R.isUniverse v) (join : R.join u v w) (tA : CTyped P Γ A (.head u))
    (tB : CTyped P (.snoc Γ A) B (.head v)) :
    (CStatement.typing Γ (.pi A B) (.head w)).Valid Rd H := by
  have hw := (levels.join_level join).1
  exact ⟨(AdequateType.pi levels sound ⟨w, hw, .piForm tA hu tB hv join⟩
    (hA.1.adequateType levels sound hu) (hB.1.adequateType levels sound hv)).adequate levels
      sound hw, AdequateType.universe levels sound hw⟩

include levels sound in
/-- **Validity of the formation of dependent pair types.** -/
theorem CStatement.Valid.sigmaForm {n : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {B : CTm Head (n + 1)} {u v w : Head} (hA : (CStatement.typing Γ A (.head u)).Valid Rd H)
    (hu : R.isUniverse u) (hB : (CStatement.typing (.snoc Γ A) B (.head v)).Valid Rd H)
    (hv : R.isUniverse v) (join : R.join u v w) (tA : CTyped P Γ A (.head u))
    (tB : CTyped P (.snoc Γ A) B (.head v)) :
    (CStatement.typing Γ (.sigma A B) (.head w)).Valid Rd H := by
  have hw := (levels.join_level join).1
  exact ⟨(AdequateType.sigma levels sound ⟨w, hw, .sigmaForm tA hu tB hv join⟩
    (hA.1.adequateType levels sound hu) (hB.1.adequateType levels sound hv)).adequate levels
      sound hw, AdequateType.universe levels sound hw⟩

include levels sound in
/-- **Validity of the formation of identity types.** -/
theorem CStatement.Valid.idForm {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {u : Head}
    (hA : (CStatement.typing Γ A (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (ha : (CStatement.typing Γ a A).Valid Rd H) (hb : (CStatement.typing Γ b A).Valid Rd H)
    (tA : CTyped P Γ A (.head u)) (ta : CTyped P Γ a A) (tb : CTyped P Γ b A) :
    (CStatement.typing Γ (.id A a b) (.head u)).Valid Rd H :=
  ⟨(AdequateType.ident levels hu tA ta tb (hA.1.adequateType levels sound hu) ha.1 hb.1).adequate
    levels sound hu, AdequateType.universe levels sound hu⟩

end Formation

/-! ## Conversion, subsumption and abstraction -/

section Conversion

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L)

include levels in
/-- **Validity of conversion**: the term's relation moves along the adequate equation
of the two types, and the target type is the equation's right side. -/
theorem CStatement.Valid.conv (sound : SoundnessFacts Rd P) {n : Nat} {Γ : CCtx Head n}
    {t A B : CTm Head n} {u : Head} (ht : (CStatement.typing Γ t A).Valid Rd H)
    (hAB : (CStatement.equality Γ A B (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (eAB : CEqual P Γ A B (.head u)) : (CStatement.typing Γ t B).Valid Rd H :=
  ⟨Adequate.conv levels sound hu ht.1 hAB.1 eAB, hAB.1.2.1.adequateType levels sound hu⟩

include levels in
/-- **Validity of subsumption**: the two types denote alike, and subsumption of the
relation moves the term's relation along the lower type's usability at the upper one,
as far as the token's type witness observes. -/
theorem CStatement.Valid.sub (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n}
    {t A B : CTm Head n} (ht : (CStatement.typing Γ t A).Valid Rd H)
    (hAB : (CStatement.sub Γ A B).Valid Rd H) (le : CBelow P Γ A B) :
    (CStatement.typing Γ t B).Valid Rd H := by
  refine ⟨fun ρ fits m Δ σ σ' formed hσ s hs hsB => ?_, hAB.2.1⟩
  rw [← CBelow.sound valid le fits] at hsB
  obtain ⟨a, ha, hau, hta⟩ := hsB
  exact RT.subConv levels formed hau hta
    (fun r hr => hAB.2.2 ρ fits formed hσ.left r (ha r hr) (hau r hr)) (le.substitute hσ.1.1)
    (ht.1 ρ fits formed hσ s hs ⟨a, ha, hau, hta⟩)

include levels in
/-- **Validity of abstraction**: the abstraction's compatibility lemma, and the
dependent function type's adequacy from its own typing. -/
theorem CStatement.Valid.lamIntro (sound : SoundnessFacts Rd P) {n : Nat} {Γ : CCtx Head n}
    {A : CTm Head n} {body B : CTm Head (n + 1)} {u w : Head}
    (hA : (CStatement.typing Γ A (.head w)).Valid Rd H) (hw : R.isUniverse w)
    (hPi : (CStatement.typing Γ (.pi A B) (.head u)).Valid Rd H) (hu : R.isUniverse u)
    (hb : (CStatement.typing (.snoc Γ A) body B).Valid Rd H) (tA : CTyped P Γ A (.head w))
    (tPi : CTyped P Γ (.pi A B) (.head u)) (tb : CTyped P (.snoc Γ A) body B) :
    (CStatement.typing Γ (.lam A body) (.pi A B)).Valid Rd H :=
  ⟨Adequate.lam levels sound hw hu hA.1 hPi.1 hb.1 tA tPi tb, hPi.1.adequateType levels sound hu⟩

end Conversion

/-! ## Constants -/

section Constants

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (sound : SoundnessFacts Rd P)

/-- The substitution of the empty context. -/
theorem SubstRel.nil {m : Nat} {Δ : CCtx Head m} :
    SubstRel Rd H .nil Env.nil Δ (fun i => .var (Fin.elim0 i)) (fun i => .var (Fin.elim0 i)) :=
  ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩

include levels sound in
/-- **Validity of a declared constant**, given its adequacy: the constant is closed, so
its adequacy at its declared type is the constant's adequacy, whose premise, the
adequacy of the declared type, is the validity of the declared type's formation; the
declared type is closed and adequate in the empty context, whose only substitution
renames it into every context. -/
theorem CStatement.Valid.constAt {n : Nat} {Γ : CCtx Head n} {name : DeclName}
    (consts : ConstAdequateAt Rd H name) {type : CTm Head 0} {u : Head}
    (declared : P.constantType name = some type)
    (hType : (CStatement.typing .nil type (.head u)).Valid Rd H) (tType : CTyped P .nil type (.head u))
    (hu : R.isUniverse u) : (CStatement.typing Γ (.const name) type.liftClosed).Valid Rd H := by
  have hTy : AdequateType Rd H .nil type := hType.1.adequateType levels sound hu
  refine ⟨fun ρ fits m Δ σ σ' formed hσ s hs hsT => ?_, fun ρ fits m Δ σ σ' formed hσ r hr hrU => ?_⟩
  · rw [cinterp_liftClosed] at hsT
    rw [CTm.subst_liftClosed]
    exact consts declared hu tType hTy formed s hs hsT
  · rw [cinterp_liftClosed] at hr
    rw [CTm.subst_liftClosed, CTm.subst_liftClosed]
    have h := hTy Env.nil trivial formed SubstRel.nil r hr hrU
    rwa [CTm.subst_var_comp] at h

include levels sound in
/-- **Validity of a declared constant**, given the adequacy of the declared constants. -/
theorem CStatement.Valid.const (consts : ConstAdequate Rd H) {n : Nat} {Γ : CCtx Head n}
    {name : DeclName} {type : CTm Head 0} {u : Head} (declared : P.constantType name = some type)
    (hType : (CStatement.typing .nil type (.head u)).Valid Rd H) (tType : CTyped P .nil type (.head u))
    (hu : R.isUniverse u) : (CStatement.typing Γ (.const name) type.liftClosed).Valid Rd H :=
  CStatement.Valid.constAt levels sound consts declared hType tType hu

end Constants

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
