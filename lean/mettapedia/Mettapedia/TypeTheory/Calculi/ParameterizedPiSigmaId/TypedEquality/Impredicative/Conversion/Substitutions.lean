import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Validity

/-!
# Valuations of the conversion model

**Realizer types.** Realizer types related by the types of some universe are
types of the realizer side, typed-equal and related by the generic equality;
the relation is a partial equivalence, carried along renamings into formed
contexts (`TypesRel`).

**Related valuations.** Related valuations extend by related pairs. Their
realizer halves are typed substitutions into a formed context, and the two are
typed-equal there (`EqSubstN.substMor`, `EqSubstN.substEq`). They follow world
morphisms on the value side, since a renamed valid value has every realizer of
the value (`EqSubstN.rename`), and renamings into formed contexts on the
realizer side, since candidates are Kripke (`EqSubstN.renameReal`). In a valid
context they form a partial equivalence: the type of each variable has one
pack, related values have one realizer, and its two realizer instances are
typed-equal (`EqSubstN.symm`, `EqSubstN.trans`).

**The daimon valuation.** Sending every variable to the daimon on the value
side and to itself on the realizer side is a related valuation of every valid
context whose realizer side is formed: the daimon is a valid value of every
pack, and a variable is a neutral term, related to itself by every candidate
(`EqSubstN.daimon`). A valid context is formed in the realizer side
(`ValidCtxN.formed`), so the daimon valuation of a valid context is a related
valuation of it (`EqSubstN.daimonIds`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization (tailSub subst_rename_wk CtxFormed IsType TypeEq)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)

variable {Head L : Type} [LevelOrder L]

/-! ## Realizer types -/

namespace TypesRel

variable {T : RealizerSide Head L} {m : Nat} {Δ : Ctx Head m} {A A' A'' : Tm Head m}

/-- The universe of related realizer types. -/
theorem typed (h : TypesRel T Δ A A') :
    ∃ u, T.R.isUniverse u ∧ Typed T.R Δ A (.head u) ∧ Typed T.R Δ A' (.head u) := by
  obtain ⟨u, hu, rel⟩ := h
  exact ⟨u, hu, ((ECand.types T).typed rel).1, ((ECand.types T).typed rel).2⟩

theorem left (h : TypesRel T Δ A A') : IsType T.R Δ A := by
  obtain ⟨u, hu, tA, -⟩ := h.typed
  exact ⟨u, hu, tA⟩

theorem right (h : TypesRel T Δ A A') : IsType T.R Δ A' := by
  obtain ⟨u, hu, -, tA'⟩ := h.typed
  exact ⟨u, hu, tA'⟩

/-- Related realizer types are typed-equal. -/
theorem typeEq (h : TypesRel T Δ A A') : TypeEq T.R Δ A A' := by
  obtain ⟨u, hu, rel⟩ := h
  exact ⟨u, hu, (ECand.types T).equal rel⟩

/-- Related realizer types are related by the generic equality of types. -/
theorem convTy (h : TypesRel T Δ A A') : T.E.convTy Δ A A' := by
  obtain ⟨u, hu, rel⟩ := h
  exact T.laws.convTy_of_convTm ((ECand.types T).escape rel) hu

theorem symm (h : TypesRel T Δ A A') : TypesRel T Δ A' A := by
  obtain ⟨u, hu, rel⟩ := h
  exact ⟨u, hu, (ECand.types T).symm rel⟩

theorem refl_left (h : TypesRel T Δ A A') : TypesRel T Δ A A := by
  obtain ⟨u, hu, rel⟩ := h
  exact ⟨u, hu, (ECand.types T).refl_left rel⟩

theorem refl_right (h : TypesRel T Δ A A') : TypesRel T Δ A' A' :=
  h.symm.refl_left

/-- Related realizer types compose, at the join of their universes. -/
theorem trans (h : TypesRel T Δ A A') (h' : TypesRel T Δ A' A'') : TypesRel T Δ A A'' := by
  obtain ⟨u, hu, rel⟩ := h
  obtain ⟨v, hv, rel'⟩ := h'
  obtain ⟨w, join⟩ := T.levels.join_exists hu hv
  obtain ⟨uw, vw⟩ := T.levels.join_upper join
  exact ⟨w, (T.levels.join_level join).1,
    (ECand.types T).trans (types_cumul uw rel) (types_cumul vw rel')⟩

/-- Related realizer types stay related along a renaming into a formed
context. -/
theorem rename {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k} (ren : CtxRen Δ Θ ρ)
    (formed : CtxFormed T.R Θ) (h : TypesRel T Δ A A') :
    TypesRel T Θ (Presentation.rename ρ A) (Presentation.rename ρ A') := by
  obtain ⟨u, hu, rel⟩ := h
  exact ⟨u, hu, (ECand.types T).rename ren formed rel⟩

end TypesRel

variable {M : NModel Head L}

/-! ## Extension and lookup -/

section Valuations

variable {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m} {σ σ' : Sub Head n m}
  {Δ : Ctx Head r} {ς ς' : Sub Head n r}

/-- The realizer side of related valuations is a formed context. -/
theorem EqSubstN.formed : ∀ {n : Nat} {Γ : Ctx Head n} {σ σ' : Sub Head n m}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' → CtxFormed M.side.R Δ
  | _, .nil, _, _, _, _, e => e
  | _, .snoc _ _, _, _, _, _, e => EqSubstN.formed e.1

theorem EqSubstN.cons (e : EqSubstN M Γ ξ σ σ' Δ ς ς') {A : Tm Head n} {P : NPack M m}
    (den : DenN M ξ (Presentation.subst σ A) P) {a a' : Tm Head m} {s s' : Tm Head r}
    (h : P.Related a a' Δ (Presentation.subst ς A) s s') :
    EqSubstN M (.snoc Γ A) ξ (consSub a σ) (consSub a' σ') Δ (consSub s ς) (consSub s' ς') :=
  ⟨e, P, den, h⟩

/-- Related valuations send each variable to related values of its type, with
realizers related at its realizer type. -/
theorem EqSubstN.lookup : ∀ {n : Nat} {Γ : Ctx Head n} {σ σ' : Sub Head n m}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' → ∀ i : Fin n,
      ∃ P : NPack M m, DenN M ξ (Presentation.subst σ (Ctx.lookup Γ i)) P ∧
        P.Related (σ i) (σ' i) Δ (Presentation.subst ς (Ctx.lookup Γ i)) (ς i) (ς' i)
  | _, .nil, _, _, _, _, _, i => nomatch i
  | _, .snoc Γ A, σ, _, ς, _, e, i => by
      obtain ⟨tail, P, den, h⟩ := e
      refine Fin.cases ?_ (fun j => ?_) i
      · refine ⟨P, ?_, ?_⟩
        · simp only [Ctx.lookup, Fin.cases_zero]
          rw [subst_rename_wk]
          exact den
        · simp only [Ctx.lookup, Fin.cases_zero]
          rw [subst_rename_wk]
          exact h
      · obtain ⟨P', den', h'⟩ := EqSubstN.lookup tail j
        refine ⟨P', ?_, ?_⟩
        · simp only [Ctx.lookup, Fin.cases_succ]
          rw [subst_rename_wk]
          exact den'
        · simp only [Ctx.lookup, Fin.cases_succ]
          rw [subst_rename_wk]
          exact h'

/-- The first realizer half of related valuations is a typed substitution. -/
theorem EqSubstN.substMor (e : EqSubstN M Γ ξ σ σ' Δ ς ς') : SubstMor M.side.R Γ Δ ς := by
  intro i
  obtain ⟨P, -, -, h⟩ := e.lookup i
  exact ((P.real (σ i)).typed h).1

/-- The two realizer halves of related valuations are typed-equal. -/
theorem EqSubstN.substEq (e : EqSubstN M Γ ξ σ σ' Δ ς ς') : SubstEq M.side.R Γ Δ ς ς' := by
  refine ⟨e.substMor, fun i => ?_⟩
  obtain ⟨P, -, -, h⟩ := e.lookup i
  exact (P.real (σ i)).equal h

/-- The realizer instance of a typing under related valuations. -/
theorem EqSubstN.typed (e : EqSubstN M Γ ξ σ σ' Δ ς ς') {t A : Tm Head n}
    (typing : Typed M.side.R Γ t A) :
    Typed M.side.R Δ (Presentation.subst ς t) (Presentation.subst ς A) :=
  typing.substitute e.substMor

/-! ## Renamings of realizers -/

/-- **Related valuations follow renamings of their realizers into formed
contexts.** -/
theorem EqSubstN.renameReal : ∀ {n : Nat} {Γ : Ctx Head n} {σ σ' : Sub Head n m}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
      ∀ {k : Nat} {Θ : Ctx Head k} {ρ : Ren r k}, CtxRen Δ Θ ρ → CtxFormed M.side.R Θ →
        EqSubstN M Γ ξ σ σ' Θ (fun i => Presentation.rename ρ (ς i))
          (fun i => Presentation.rename ρ (ς' i))
  | _, .nil, _, _, _, _, _, _, _, _, _, formed => formed
  | _, .snoc _ A, σ, _, ς, _, e, _, _, ρ, ren, formed => by
      obtain ⟨tail, P, den, hab, hst⟩ := e
      refine ⟨EqSubstN.renameReal tail ren formed, P, den, hab, ?_⟩
      have h := (P.real (σ 0)).rename ren formed hst
      rw [rename_subst] at h
      exact h

end Valuations

/-! ## Morphisms of worlds -/

section Laws

variable (laws : M.Laws)
include laws

/-- **Related valuations follow world morphisms** on the value side: a renamed
type relates the renamed values, and a renamed valid value has every realizer
of the value. -/
theorem EqSubstN.rename : ∀ {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r},
    EqSubstN M Γ ξ σ σ' Δ ς ς' → ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k},
      Morph ξ ξ' ρ → EqSubstN M Γ ξ' (fun i => Presentation.rename ρ (σ i))
        (fun i => Presentation.rename ρ (σ' i)) Δ ς ς'
  | _, _, _, .nil, _, _, _, _, _, _, e, _, _, _, _ => e
  | _, _, _, .snoc Γ A, _, σ, _, _, _, _, e, _, _, ρ, w => by
      obtain ⟨tail, P, den, hab, hst⟩ := e
      obtain ⟨P', den', renamed, real⟩ := DenN.rename_real laws den w
      refine ⟨EqSubstN.rename tail w, P', ?_, renamed.rel hab,
        real (ValueSide.DenS.refl_left laws.value den hab) hst⟩
      rw [rename_subst] at den'
      exact den'

/-! ## Partial equivalence -/

/-- Related valuations of a valid context are symmetric. -/
theorem EqSubstN.symm : ∀ {n m r : Nat} {Γ : Ctx Head n}, ValidCtxN M Γ →
    ∀ {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r},
      EqSubstN M Γ ξ σ σ' Δ ς ς' → EqSubstN M Γ ξ σ' σ Δ ς' ς
  | _, _, _, .nil, _, _, _, _, _, _, _, e => e
  | _, _, _, .snoc Γ A, valid, _, σ, σ', _, ς, ς', e => by
      obtain ⟨validΓ, validA⟩ := valid
      obtain ⟨tail, P, den, hab, hst⟩ := e
      obtain ⟨Q, den₁, den₂, types⟩ := validA tail
      obtain rfl := ValueSide.DenS.deterministic laws.value den den₁
      refine ⟨EqSubstN.symm validΓ tail, P, den₂, ValueSide.DenS.symm laws.value den hab, ?_⟩
      rw [← ValueSide.DenS.real_eq_of_rel laws.value den hab]
      exact (P.real (σ 0)).conv tail.formed types.typeEq ((P.real (σ 0)).symm hst)

/-- Related valuations of a valid context compose. -/
theorem EqSubstN.trans : ∀ {n m r : Nat} {Γ : Ctx Head n}, ValidCtxN M Γ →
    ∀ {ξ : World M.reading m} {σ σ' σ'' : Sub Head n m} {Δ : Ctx Head r}
      {ς ς' ς'' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' → EqSubstN M Γ ξ σ' σ'' Δ ς' ς'' →
        EqSubstN M Γ ξ σ σ'' Δ ς ς''
  | _, _, _, .nil, _, _, _, _, _, _, _, _, _, e, _ => e
  | _, _, _, .snoc Γ A, valid, _, σ, σ', _, _, ς, ς', _, e, e' => by
      obtain ⟨validΓ, validA⟩ := valid
      obtain ⟨tail, P, den, hab, hst⟩ := e
      obtain ⟨tail', P', den', hbc, hst'⟩ := e'
      obtain ⟨Q, den₁, den₂, types⟩ := validA tail
      obtain rfl := ValueSide.DenS.deterministic laws.value den den₁
      obtain rfl := (ValueSide.DenS.deterministic laws.value den' den₂).symm
      refine ⟨EqSubstN.trans validΓ tail tail', P, den,
        ValueSide.DenS.trans laws.value den hab hbc, ?_⟩
      rw [← ValueSide.DenS.real_eq_of_rel laws.value den hab] at hst'
      exact (P.real (σ 0)).trans hst
        ((P.real (σ 0)).conv tail.formed types.typeEq.symm hst')

theorem EqSubstN.refl_left {n m r : Nat} {Γ : Ctx Head n} (valid : ValidCtxN M Γ)
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') : EqSubstN M Γ ξ σ σ Δ ς ς :=
  EqSubstN.trans laws valid e (EqSubstN.symm laws valid e)

theorem EqSubstN.refl_right {n m r : Nat} {Γ : Ctx Head n} (valid : ValidCtxN M Γ)
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') : EqSubstN M Γ ξ σ' σ' Δ ς' ς' :=
  EqSubstN.trans laws valid (EqSubstN.symm laws valid e) e

/-- The second realizer half of related valuations of a valid context is a
typed substitution too. -/
theorem EqSubstN.substMor_right {n m r : Nat} {Γ : Ctx Head n} (valid : ValidCtxN M Γ)
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') : SubstMor M.side.R Γ Δ ς' :=
  (EqSubstN.symm laws valid e).substMor

/-! ## The daimon valuation -/

/-- **The daimon valuation**: the daimon for every variable on the value side,
and the renamed variable on the realizer side, into a formed context that the
context renames into, is a related valuation of every valid context. -/
theorem EqSubstN.daimon : ∀ {n m r : Nat} {Γ : Ctx Head n}, ValidCtxN M Γ →
    ∀ (ξ : World M.reading m) {Δ : Ctx Head r} {ρ : Ren n r}, CtxRen Γ Δ ρ →
      CtxFormed M.side.R Δ →
        EqSubstN M Γ ξ (fun _ => .const M.star) (fun _ => .const M.star) Δ
          (fun i => .var (ρ i)) (fun i => .var (ρ i))
  | _, _, _, .nil, _, _, _, _, _, formed => formed
  | _, _, _, .snoc Γ A, valid, ξ, Δ, ρ, ren, formed => by
      obtain ⟨validΓ, validA⟩ := valid
      have renTail : CtxRen Γ Δ (fun i => ρ i.succ) := by
        intro i
        rw [ren i.succ]
        show Presentation.rename ρ (Presentation.rename wk (Ctx.lookup Γ i)) = _
        rw [rename_comp]
        rfl
      have tail := EqSubstN.daimon validΓ ξ renTail formed
      obtain ⟨P, den, -, -⟩ := validA tail
      refine ⟨tail, P, den, ValueSide.DenS.star_val laws.value den, ?_⟩
      have typing : Typed M.side.R Δ (.var (ρ 0))
          (Presentation.subst (tailSub fun i => .var (ρ i)) A) := by
        have t := Derivable.var (R := M.side.R) (Γ := Δ) (ρ 0)
        rw [ren 0] at t
        show Typed M.side.R Δ (.var (ρ 0)) (Presentation.subst (renSub fun i => ρ i.succ) A)
        rw [subst_renSub]
        simp only [Ctx.lookup, Fin.cases_zero, rename_comp] at t
        exact t
      exact (P.real _).var (ρ 0) typing

/-- **A valid context is formed in the realizer side**: the daimon valuation of
its prefix relates the realizer instance of each entry to itself as a type. -/
theorem ValidCtxN.formed : ∀ {n : Nat} {Γ : Ctx Head n}, ValidCtxN M Γ → CtxFormed M.side.R Γ
  | _, .nil, _ => .nil
  | _, .snoc Γ A, valid => by
      obtain ⟨validΓ, validA⟩ := valid
      have formed := ValidCtxN.formed validΓ
      obtain ⟨-, -, -, types⟩ :=
        validA (EqSubstN.daimon laws validΓ Consistency.World.closed (Normalization.CtxRen.id Γ) formed)
      have typeA := types.left
      rw [show (fun i : Fin _ => (Tm.var (idRen i) : Tm Head _)) = ids from rfl,
        subst_ids] at typeA
      exact .snoc formed typeA

/-- The daimon valuation of a valid context, with the identity on the realizer
side. -/
theorem EqSubstN.daimonIds {n : Nat} {Γ : Ctx Head n} (valid : ValidCtxN M Γ) :
    EqSubstN M Γ (Consistency.World.closed (S := M.reading)) (fun _ => .const M.star)
      (fun _ => .const M.star) Γ ids ids :=
  EqSubstN.daimon laws valid _ (Normalization.CtxRen.id Γ) (ValidCtxN.formed laws valid)

/-! ## Extension by a fresh variable -/

omit laws in
/-- Related valuations extend by related values, with a fresh variable of the
realizer instance of the type realizing the new variable on both sides. -/
theorem EqSubstN.consVar {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') {A : Tm Head n} (typeA : IsType M.side.R Δ (Presentation.subst ς A))
    {P : NPack M m} (den : DenN M ξ (Presentation.subst σ A) P) {a a' : Tm Head m}
    (h : P.rel a a') :
    EqSubstN M (.snoc Γ A) ξ (consSub a σ) (consSub a' σ')
      (.snoc Δ (Presentation.subst ς A)) (consSub (.var 0) fun i => Presentation.rename wk (ς i))
      (consSub (.var 0) fun i => Presentation.rename wk (ς' i)) := by
  have formed : CtxFormed M.side.R (.snoc Δ (Presentation.subst ς A)) := .snoc e.formed typeA
  refine (e.renameReal (Normalization.CtxRen.wk Δ _) formed).cons den ⟨h, ?_⟩
  have typing : Typed M.side.R (.snoc Δ (Presentation.subst ς A)) (.var 0)
      (Presentation.subst (fun i => Presentation.rename wk (ς i)) A) := by
    have t := Derivable.var (R := M.side.R) (Γ := .snoc Δ (Presentation.subst ς A)) 0
    rw [← rename_subst]
    exact t
  exact (P.real a).var 0 typing

end Laws

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
