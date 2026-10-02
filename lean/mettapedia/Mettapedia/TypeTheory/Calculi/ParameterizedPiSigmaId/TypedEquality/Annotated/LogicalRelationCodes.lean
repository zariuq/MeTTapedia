import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationAdequacy

/-!
# The quantifier over proposition codes, at its own type of codes

**The quantifier constant** (`Ideal.allConst A`) sends a code-valued family `f` over
a carrier `A` to the code of the dependent function type over `A` whose value at
`x` is the code `f x`, and is projected onto its declared type `(A → prop) → prop`,
with `prop` read as the universe of codes.

**Its constant case of the relation** (`RT.allCode`): at the universe of codes as
carrier, for every token of the constant typed at its declared type, the constant is
related to itself at `(prop → prop) → prop`. For related code-valued families `f`,
`f'`, the codes `all f` and `all f'` are related at `prop` by the clause of the
universe of codes: their decodings, head-expanded along the decoder's root step to
`Π (x : prop). holds (f x)` and `Π (x : prop). holds (f' x)`, are related as types.
At a family entry of the decoded type, the quantified codes range over all codes,
the quantifier's own codes among them; they are observed only through the entry's
input, which is part of the entry and so smaller than the token. The families'
values there are related by the clause of `f` and `f'` at `prop → prop` at the
function entries of the witness whose inputs the entry's input entails.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

namespace Impredicative
namespace Domain
namespace Ideal

/-- The function of the quantifier over a carrier `A`: a code-valued family goes to
the code of the dependent function type over `A` with the family's codes as values. -/
def allRaw (A : Ideal) : Ideal :=
  lam fun F => cpi A fun x => projT codesIdeal (app (principal F) x)

theorem allRaw_monotone (A : Ideal) :
    Monotone fun F => cpi A fun x => projT codesIdeal (app (principal F) x) := fun h =>
  former_mono (le_refl A) fun _ => projT_mono (app_mono (principal_mono h) (le_refl _))

/-- **The quantifier over a carrier**, projected onto `(A → prop) → prop`. -/
def allConst (A : Ideal) : Ideal :=
  projT (cpi (cpi A fun _ => codesIdeal) fun _ => codesIdeal) (allRaw A)

end Ideal
end Domain
end Impredicative

namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypedAt principal codesIdeal)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head} {P : ChurchRules R} {K : RigidTypes P}
  {H : HeadReduction P K} {L : Type} [LevelOrder L] (levels : LevelModel R L)

/-- A token of the universe of codes relates the type of codes to itself. -/
theorem RT.prop_self {n : Nat} {Γ : CCtx Head n} {u₀ : Head} (hu₀ : R.isUniverse u₀)
    (tProp : CTyped P Γ (.const K.prop) (.head u₀)) {d : Tok} (hd : codesIdeal.Mem d) :
    RT H Γ false d (.const K.prop) (.const K.prop) (.const K.prop) := by
  have propRed : CRedTy H Γ (.const K.prop) (.const K.prop) := CRedTy.refl ⟨u₀, hu₀, tProp⟩
  refine RT.closed' hd fun q hq => ?_
  rw [List.mem_singleton.1 hq]
  exact RT.ty_codes_iff.2 ⟨propRed, propRed⟩

include levels in
/-- **The quantifier over codes at its own type of codes.** For every token of the
quantifier constant over the universe of codes typed at `(prop → prop) → prop`, the
quantifier is related to itself there. -/
theorem RT.allCode {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) (all : DeclName)
    {u₀ : Head} (hu₀ : R.isUniverse u₀)
    (tProp : ∀ {m : Nat} {Δ : CCtx Head m}, CTyped P Δ (.const K.prop) (.head u₀))
    (tAll : CTyped P Γ (.const all) (.pi (.pi (.const K.prop) (.const K.prop)) (.const K.prop)))
    (decode : ∀ f : CTm Head n, P.computation.step (.app (.const K.holds) (.app (.const all) f))
      (.pi (.const K.prop) (.app (.const K.holds) (.app (f.rename wk) (.var 0)))))
    (admits : ∀ {f : CTm Head n}, CTyped P Γ f (.pi (.const K.prop) (.const K.prop)) →
      P.Admits Γ (.app (.const K.holds) (.app (.const all) f))
        (.pi (.const K.prop) (.app (.const K.holds) (.app (f.rename wk) (.var 0))))) :
    ∀ s, (Ideal.allConst codesIdeal).Mem s →
      TypedAt (Ideal.cpi (Ideal.cpi codesIdeal fun _ => codesIdeal) fun _ => codesIdeal) s →
        RT H Γ true s (.pi (.pi (.const K.prop) (.const K.prop)) (.const K.prop))
          (.const all) (.const all) := by
  intro s hs hsT
  obtain ⟨b, hb, hbu, hts⟩ := hsT
  have hbF : Ideal.Below b (Ideal.former .pi (Ideal.cpi codesIdeal fun _ => codesIdeal)
      fun _ => codesIdeal) := hb
  obtain ⟨X, Y, rfl, hXt, hYt⟩ := Ideal.tyTok_below_pi hbF hts
  -- the typed tokens
  have hYU : ∀ y ∈ Y, TyTok Elem.univ y := by
    intro y hy
    have hbelow : Ideal.Below (fnApp .pi b X) codesIdeal := by
      have h := Ideal.below_fam_fnApp (k := .pi) (y := principal X) hb
        (fun x hx => ent_of_mem hx)
      rwa [show Ideal.cpi (Ideal.cpi codesIdeal fun _ => codesIdeal) (fun _ => codesIdeal) =
        Ideal.former .pi (Ideal.cpi codesIdeal fun _ => codesIdeal) (fun _ => codesIdeal)
        from rfl, Ideal.fam_former_const] at h
    exact Ideal.typedAt_codes_iff.1 ⟨_, hbelow, Ideal.ty_fnApp (.inl rfl) hbu X, hYt y hy⟩
  have hdom : Ideal.Below (args .pi 0 b) (Ideal.former .pi codesIdeal fun _ => codesIdeal) :=
    Ideal.below_args_former hbF
  have hdomU : Ty (args .pi 0 b) Elem.univ := Ideal.ty_args_dom (.inl rfl) hbu
  have hXU : ∀ C Z W, Tok.fn .lam C Z W ∈ X → ∀ w ∈ W, TyTok Elem.univ w := by
    intro C Z W hx w hw
    obtain ⟨Z', W', e, -, hW'⟩ := Ideal.tyTok_below_pi hdom (hXt _ hx)
    injection e with _ eC eZ eW
    subst eC eZ eW
    have hbelow : Ideal.Below (fnApp .pi (args .pi 0 b) Z) codesIdeal := by
      have h := Ideal.below_fam_fnApp (k := .pi) (y := principal Z) hdom
        (fun x hx => ent_of_mem hx)
      rwa [Ideal.fam_former_const] at h
    exact Ideal.typedAt_codes_iff.1 ⟨_, hbelow, Ideal.ty_fnApp (.inl rfl) hdomU Z, hW' w hw⟩
  -- the value of the quantifier's function at the input
  have hY : Ideal.Below Y (Ideal.cpi codesIdeal fun x =>
      projT codesIdeal (Ideal.app (principal X) x)) :=
    (Ideal.mem_lam_fn (Ideal.allRaw_monotone codesIdeal)).1 (Ideal.projT_le _ _ _ hs)
  -- the syntactic facts
  have propRed : CRedTy H Γ (.const K.prop) (.const K.prop) := CRedTy.refl ⟨u₀, hu₀, tProp⟩
  obtain ⟨u, hu, tHolds⟩ := K.holds_typed Γ
  have tProp' : CTyped P (.snoc Γ (.const K.prop)) (.const K.prop) (.head u₀) := tProp
  obtain ⟨u', hu', tHolds'⟩ := K.holds_typed (.snoc Γ (.const K.prop))
  have holdsFam : ∀ {g : CTm Head n}, CTyped P Γ g (.pi (.const K.prop) (.const K.prop)) →
      CTyped P (.snoc Γ (.const K.prop)) (.app (.const K.holds) (.app (g.rename wk) (.var 0)))
        (.head u') := fun tg =>
    .appElim tHolds' (.appElim (CTyped.weaken tg) (.var 0))
  -- decoding a quantified code
  have decRed : ∀ {g : CTm Head n}, CTyped P Γ g (.pi (.const K.prop) (.const K.prop)) →
      CRedTy H Γ (.app (.const K.holds) (.app (.const all) g))
        (.pi (.const K.prop) (.app (.const K.holds) (.app (g.rename wk) (.var 0)))) := by
    intro g tg
    obtain ⟨w₁, join₁⟩ := levels.join_exists hu₀ hu'
    have tLeft : CTyped P Γ (.app (.const K.holds) (.app (.const all) g)) (.head u) :=
      .appElim tHolds (.appElim tAll tg)
    have tRight : CTyped P Γ (.pi (.const K.prop)
        (.app (.const K.holds) (.app (g.rename wk) (.var 0)))) (.head w₁) :=
      .piForm tProp hu₀ (holdsFam tg) hu' join₁
    obtain ⟨w₂, join₂⟩ := levels.join_exists (levels.join_level join₁).1 hu
    obtain ⟨c₁, c₂⟩ := levels.join_upper join₂
    exact ⟨.single (H.root (decode g)), w₂, (levels.join_level join₂).1,
      .rootAdmitted (decode g) (admits tg) (.cumul tLeft c₂) (.cumul tRight c₁)⟩
  -- the families' values at related codes, as far as the value tokens observe
  have extract : ∀ {Z : List Tok} {g h : CTm Head n},
      (∀ C Z'' W'', Tok.fn .lam C Z'' W'' ∈ X →
        (∀ z ∈ Z'', (projT codesIdeal (principal Z)).Mem z) → ∀ w'' ∈ W'',
          RT H Γ true w'' (.const K.prop) g h) →
      ∀ w, (projT codesIdeal (Ideal.app (principal X)
        (projT codesIdeal (principal Z)))).Mem w →
          RT H Γ false w (.app (.const K.holds) g) (.app (.const K.holds) g)
            (.app (.const K.holds) h) := by
    intro Z g h hw₀ w hw
    obtain ⟨v, hv, e⟩ := hw
    refine RT.closed' e fun q hq => ?_
    obtain ⟨Z', Y', hZ', hXZY, hq'⟩ := Ideal.mem_app.1 (hv q hq).1
    have hent : ∀ y' ∈ Y', ent (fnApp .lam X Z') y' = true := by
      have h' : ent X (.fn .lam [] Z' Y') = true := hXZY
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h'
      exact h'.2
    refine RT.closed' (ent_cut hq' hent) fun w'' hw'' => ?_
    obtain ⟨C, Z'', W'', hmem, hZ''Z', hw''W⟩ := mem_fnApp'.1 hw''
    exact RT.toCodes (typeKind_of_tyTok_univ (hXU _ _ _ hmem w'' hw''W)) propRed
      (hw₀ C Z'' W'' hmem (fun z hz => (projT codesIdeal (principal Z)).closed hZ' (hZ''Z' z hz))
        w'' hw''W)
  -- the type of code-valued families
  obtain ⟨w₃, join₃⟩ := levels.join_exists hu₀ hu₀
  have piProp : CIsType P Γ (.pi (.const K.prop) (.const K.prop)) :=
    ⟨w₃, (levels.join_level join₃).1, .piForm tProp hu₀ tProp' hu₀ join₃⟩
  have famOf : ∀ (g N : CTm Head n),
      CTm.inst0 N (.app (.const K.holds) (.app (g.rename wk) (.var 0))) =
        .app (.const K.holds) (.app g N) := by
    intro g N
    change CTm.app (.const K.holds) (.app (CTm.inst0 N (g.rename wk)) N) = _
    rw [CTm.inst0_rename_wk]
  -- the codes of related families are related
  have core : ∀ {f f' : CTm Head n}, CEqual P Γ f f' (.pi (.const K.prop) (.const K.prop)) →
      (∀ x ∈ X, RT H Γ true x (.pi (.const K.prop) (.const K.prop)) f f') →
        ∀ y ∈ Y, RT H Γ true y (.const K.prop) (.app (.const all) f) (.app (.const all) f') := by
    intro f f' hff hX y hy
    obtain ⟨tf, tf'⟩ := CEqual.typed levels hff formed
    refine RT.ofCodes (typeKind_of_tyTok_univ (hYU y hy)) propRed ?_
    refine RT.expand_ty levels (T := .const K.prop) (decRed tf) (decRed tf') ?_
    have eFam : CTypeEq P (.snoc Γ (.const K.prop))
        (.app (.const K.holds) (.app (f.rename wk) (.var 0)))
        (.app (.const K.holds) (.app (f'.rename wk) (.var 0))) :=
      ⟨u', hu', .appCong (.refl tHolds') (.appCong (CEqual.weaken hff) (.refl (.var 0)))⟩
    have PR : PiRed H Γ (.pi (.const K.prop) (.app (.const K.holds) (.app (f.rename wk) (.var 0))))
        (.pi (.const K.prop) (.app (.const K.holds) (.app (f'.rename wk) (.var 0))))
        (.const K.prop) (.app (.const K.holds) (.app (f.rename wk) (.var 0)))
        (.const K.prop) (.app (.const K.holds) (.app (f'.rename wk) (.var 0))) :=
      ⟨CRedTy.refl (CTypeEq.isType levels (decRed tf).2 formed).2,
        CRedTy.refl (CTypeEq.isType levels (decRed tf').2 formed).2, propRed.2, eFam⟩
    have valI : ∀ {N N' : CTm Head n}, CEqual P Γ N N' (.const K.prop) → ∀ {Z : List Tok},
        (∀ z ∈ Z, RT H Γ true z (.const K.prop) N N') →
        ∀ C Z'' W'', Tok.fn .lam C Z'' W'' ∈ X →
          (∀ z ∈ Z'', (projT codesIdeal (principal Z)).Mem z) → ∀ w'' ∈ W'',
            RT H Γ true w'' (.const K.prop) (.app f N) (.app f N') ∧
              RT H Γ true w'' (.const K.prop) (.app f' N) (.app f' N') := by
      intro N N' hNN Z hZ C Z'' W'' hmem hZ'' w'' hw''
      rcases RT.tm_lam_iff.1 (hX _ hmem) with hvac | hcl
      · exact ⟨RT.of_vacuous (vacuous_out hvac hw''), RT.of_vacuous (vacuous_out hvac hw'')⟩
      exact (hcl _ _ (CRedTy.refl piProp)).1 N N' hNN
        (fun z hz => RT.of_projT_principal _ hZ (hZ'' z hz)) w'' hw''
    have valII : ∀ {N : CTm Head n}, CTyped P Γ N (.const K.prop) → ∀ {Z : List Tok},
        (∀ z ∈ Z, RT H Γ true z (.const K.prop) N N) →
        ∀ C Z'' W'', Tok.fn .lam C Z'' W'' ∈ X →
          (∀ z ∈ Z'', (projT codesIdeal (principal Z)).Mem z) → ∀ w'' ∈ W'',
            RT H Γ true w'' (.const K.prop) (.app f N) (.app f' N) := by
      intro N tN Z hZ C Z'' W'' hmem hZ'' w'' hw''
      rcases RT.tm_lam_iff.1 (hX _ hmem) with hvac | hcl
      · exact RT.of_vacuous (vacuous_out hvac hw'')
      exact (hcl _ _ (CRedTy.refl piProp)).2 N tN
        (fun z hz => RT.of_projT_principal _ hZ (hZ'' z hz)) w'' hw''
    obtain ⟨v, hv, e⟩ := hY y hy
    refine RT.closed' e fun g hg => ?_
    rcases hv g hg with rfl | ⟨d, rfl, hd⟩ | ⟨D, Z, W, rfl, hD, hW⟩
    · exact RT.ty_pi_iff.2 ⟨_, _, _, _, PR⟩
    · exact RT.ty_argPi_iff.2 (.inr ⟨_, _, _, _, PR, fun c hc => absurd hc List.not_mem_nil,
        fun _ => RT.prop_self hu₀ tProp hd⟩)
    · refine RT.ty_fnPi_iff.2 (.inr ⟨_, _, _, _, PR, fun c hc => RT.prop_self hu₀ tProp (hD c hc),
        fun N N' hNN hZ w hw => ?_, fun N tN hZ w hw => ?_⟩)
      · rw [famOf f N, famOf f N', famOf f' N, famOf f' N']
        exact ⟨extract (fun C Z'' W'' hmem hZ'' w'' hw'' =>
            (valI hNN hZ C Z'' W'' hmem hZ'' w'' hw'').1) w (hW w hw),
          extract (fun C Z'' W'' hmem hZ'' w'' hw'' =>
            (valI hNN hZ C Z'' W'' hmem hZ'' w'' hw'').2) w (hW w hw)⟩
      · rw [famOf f N, famOf f' N]
        exact extract (fun C Z'' W'' hmem hZ'' w'' hw'' => valII tN hZ C Z'' W'' hmem hZ'' w'' hw'')
          w (hW w hw)
  -- the function clause
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  exact ⟨fun f f' hff hX y hy => ⟨core hff hX y hy, core hff hX y hy⟩,
    fun f tf hX y hy => core (.refl tf) hX y hy⟩

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
