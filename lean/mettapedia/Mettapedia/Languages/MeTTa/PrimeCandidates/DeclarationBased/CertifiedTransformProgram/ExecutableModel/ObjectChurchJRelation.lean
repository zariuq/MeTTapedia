import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.AlignedWitnesses
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Carriers

/-!
# The eliminator's case of the relation, in every extension of the object package

Every package containing the object package (`ObjectExtension`) reads the identity eliminator
as the object reading does, as its function at the reflexivity point
(`ObjectExtension.reading_j`). At the witnesses of that reading, the relation's motive
conversion at the reflexivity point applies. The object package is the extension with nothing
added.

**Typings of the eliminator's spines** (`cjSpine5_typed`, `cjSpine6_typed`): from typed
arguments, `J A x M d y : Π (p : Id A x y). M y p` and `J A x M d y p : M y p`.

**The eliminator's step at the reading's witnesses** (`RT.objectJ_at`,
`RT.objectJAligned`). Let the arguments be typed and the carrier, the motive, the method
and the path adequate (`JCase`), and let `σ`, `σ'` be related substitutions over an environment
fitting the context. At every token of the denotation of
`J A x M d y p`, the spines `J A x M d y p` and `J A x M d' y p'` (the method and the path
substituted by `σ'`, the rest by `σ`) are related at `M y p`. Each such token is entailed
by tokens `t` of the method typed at the motive at the path's point and its reflexivity
(`mem_appSpine_jAlignedConst`). At `t`:

* the path's reflexivity tag relates `p` and `p'` (`hp`);
* the method's adequacy relates `d` and `d'` at `M x (refl x)`, since the path's point is
  below `x` (`reflPoint_le_endpoints`);
* every token of a type witness of `t` comes from an entry of the motive whose inputs
  are aligned with typed point tokens of the path (`motive_entry`, `aligned_inputs`):
  exactly the hypotheses of `RT.motive_reflPoint`, with the carrier related to itself
  by its adequacy, which relate `M x (refl x)` and `M y p` there (`RT.objectJ_motive`);
* so the method's relation converts to `M y p`, and the eliminator's step
  (`RT.objectEliminator`) relates the spines.

**The eliminator's case of the fundamental lemma** (`Adequate.objectJ`): the spine
`J A x M d y p` is adequate at `M y p`. The spine with the right method and path is
related to the right spine by head expansion, both contracting to the right method.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypedAt principal SpineTyped)
open Package (jName)

namespace CodeModel

/-! ## Typings of the eliminator's spines -/

section Typings

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The parameters of the identity eliminator, annotated: the carrier, the base point, the
motive, the method, the endpoint and the path. -/
abbrev cJTypeTele : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.var 0))
    (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0)))
    (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))) (.var 3)) (.id (.var 4) (.var 3) (.var 0))

/-- The eliminator applied to the first five of its parameters. -/
theorem cjSpine_typed :
    CTyped objectChurch cJTypeTele
      (CTm.appSpine (.const jName) [.var 5, .var 4, .var 3, .var 2, .var 1])
      (.pi (.id (.var 5) (.var 4) (.var 1)) (.app (.app (.var 4) (.var 2)) (.var 0))) := by
  have j0 : CTyped objectChurch cJTypeTele (.const jName) cJType := cj_typed
  have j1 := CDerivable.appElim j0 (CDerivable.var (P := objectChurch) (Γ := cJTypeTele) 5)
  have j2 := CDerivable.appElim j1 (CDerivable.var (P := objectChurch) (Γ := cJTypeTele) 4)
  have j3 := CDerivable.appElim j2 (CDerivable.var (P := objectChurch) (Γ := cJTypeTele) 3)
  have j4 := CDerivable.appElim j3 (CDerivable.var (P := objectChurch) (Γ := cJTypeTele) 2)
  exact CDerivable.appElim j4 (CDerivable.var (P := objectChurch) (Γ := cJTypeTele) 1)

/-- The substitution of the eliminator's arguments for the variables of its context. -/
def jArgs (A x M d y p : CTm Tower.Head n) : CSub Tower.Head 6 n :=
  CTm.consSub p (CTm.consSub y (CTm.consSub d (CTm.consSub M (CTm.consSub x
    (CTm.consSub A Fin.elim0)))))

/-- Typed arguments of the eliminator are a typed substitution of its context. -/
theorem jArgs_mor {R' : Rules Tower.Head} {P : ChurchRules R'} {A x M d y p : CTm Tower.Head n}
    (tA : CTyped P Γ A cU0) (tx : CTyped P Γ x A)
    (tM : CTyped P Γ M (.pi A (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) cU0)))
    (td : CTyped P Γ d (.app (.app M x) (.refl x))) (ty : CTyped P Γ y A)
    (tp : CTyped P Γ p (.id A x y)) :
    CSubstMor P cJTypeTele Γ (jArgs A x M d y p) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact tp
  refine Fin.cases ?_ (fun i => ?_) i
  · exact ty
  refine Fin.cases ?_ (fun i => ?_) i
  · exact td
  refine Fin.cases ?_ (fun i => ?_) i
  · exact tM
  refine Fin.cases ?_ (fun i => ?_) i
  · exact tx
  refine Fin.cases ?_ (fun i => ?_) i
  · exact tA
  exact i.elim0

/-- **The eliminator at its first five arguments**:
`J A x M d y : Π (p : Id A x y). M y p`. -/
theorem cjSpine5_typed {R' : Rules Tower.Head} {P : ChurchRules R'} {A x M d y p : CTm Tower.Head n}
    (mor : CSubstMor P cJTypeTele Γ (jArgs A x M d y p))
    (sub : ChurchRulesSub objectChurch P := by exact ChurchRulesSub.refl _) :
    CTyped P Γ (CTm.appSpine (.const jName) [A, x, M, d, y])
      (.pi (.id A x y) (.app (.app (M.rename wk) (y.rename wk)) (.var 0))) :=
  CTyped.substitute (CDerivable.mono sub cjSpine_typed) mor

/-- **The eliminator at all its arguments**: `J A x M d y p : M y p`. -/
theorem cjSpine6_typed {R' : Rules Tower.Head} {P : ChurchRules R'} {A x M d y p : CTm Tower.Head n}
    (mor : CSubstMor P cJTypeTele Γ (jArgs A x M d y p)) (tp : CTyped P Γ p (.id A x y))
    (sub : ChurchRulesSub objectChurch P := by exact ChurchRulesSub.refl _) :
    CTyped P Γ (CTm.appSpine (.const jName) [A, x, M, d, y, p]) (.app (.app M y) p) := by
  have h := CDerivable.appElim (cjSpine5_typed mor sub) tp
  rwa [inst0_motive_family] at h

/-- The motive's type, substituted. -/
theorem motiveType_subst {m : Nat} (σ : CSub Tower.Head n m) (A x : CTm Tower.Head n) :
    (CTm.pi A (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) cU0)).subst σ =
      .pi (A.subst σ)
        (.pi (.id ((A.subst σ).rename wk) ((x.subst σ).rename wk) (.var 0)) cU0) := by
  show CTm.pi (A.subst σ) (.pi (.id ((A.rename wk).subst (CTm.liftSub σ))
    ((x.rename wk).subst (CTm.liftSub σ)) (.var 0)) cU0) = _
  rw [CTm.subst_liftSub_wk, CTm.subst_liftSub_wk]

end Typings

/-! ## The eliminator's step at the reading's witnesses -/

section Step

variable {X : ObjectExtension} {L : Type} [LevelOrder L] (levels : LevelModel X.rules L)
  {K : RigidTypes X.church} {H : HeadReduction X.church K}

/-- Finitely many tokens, each typed at one of finitely many compact types, are typed at
one compact type. -/
theorem typed_points {S : List Tok} (h : ∀ s ∈ S, ∃ c, Ty c Elem.univ ∧ TyTok c s) :
    ∃ c, Ty c Elem.univ ∧ ∀ s ∈ S, TyTok c s := by
  induction S with
  | nil => exact ⟨[], Ty.nil _, fun _ h => absurd h List.not_mem_nil⟩
  | cons s S ih =>
      obtain ⟨c₁, hc₁, hs⟩ := h s List.mem_cons_self
      obtain ⟨c₂, hc₂, hS⟩ := ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
      refine ⟨c₁ ++ c₂, Ty.append hc₁ hc₂, fun s' hs' => ?_⟩
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact hs.mono (Le.append_left _ _)
      · exact (hS s' hs').mono (Le.append_right _ _)

/-- Finitely many tokens, each typed at one of finitely many compact types whose tokens
all have a property, are typed at one compact type whose tokens have it. -/
theorem typed_points_with {S : List Tok} {Q : Tok → Prop}
    (h : ∀ s ∈ S, ∃ c, Ty c Elem.univ ∧ TyTok c s ∧ ∀ q ∈ c, Q q) :
    ∃ c, Ty c Elem.univ ∧ (∀ s ∈ S, TyTok c s) ∧ ∀ q ∈ c, Q q := by
  induction S with
  | nil => exact ⟨[], Ty.nil _, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | cons s S ih =>
      obtain ⟨c₁, hc₁, hs, hq₁⟩ := h s List.mem_cons_self
      obtain ⟨c₂, hc₂, hS, hq₂⟩ := ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
      refine ⟨c₁ ++ c₂, Ty.append hc₁ hc₂, fun s' hs' => ?_, fun q hq => ?_⟩
      · rcases List.mem_cons.1 hs' with rfl | hs'
        · exact hs.mono (Le.append_left _ _)
        · exact (hS s' hs').mono (Le.append_right _ _)
      · rcases List.mem_append.1 hq with hq | hq
        · exact hq₁ q hq
        · exact hq₂ q hq

/-- The hypotheses of the eliminator's case, over a context: typed arguments, and an
adequate motive, method, path and carrier. -/
structure JCase (X : ObjectExtension) {K : RigidTypes X.church} (H : HeadReduction X.church K) {n : Nat} (Γ : CCtx Tower.Head n)
    (A x M d y p : CTm Tower.Head n) : Prop where
  tA : CTyped X.church Γ A cU0
  tx : CTyped X.church Γ x A
  tM : CTyped X.church Γ M (.pi A (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) cU0))
  td : CTyped X.church Γ d (.app (.app M x) (.refl x))
  ty : CTyped X.church Γ y A
  tp : CTyped X.church Γ p (.id A x y)
  hM : Adequate X.reading H Γ M
    (.pi A (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) cU0))
  hd : Adequate X.reading H Γ d (.app (.app M x) (.refl x))
  hp : Adequate X.reading H Γ p (.id A x y)
  hA : Adequate X.reading H Γ A cU0

variable {n : Nat} {Γ : CCtx Tower.Head n} {A x M d y p : CTm Tower.Head n}
  {ρ : Env n} {m : Nat} {Δ : CCtx Tower.Head m} {σ σ' : CSub Tower.Head n m}

/-- The spine facts of the eliminator's spine in an environment fitting its context. -/
theorem JCase.spine (J : JCase X H Γ A x M d y p) (fits : Fits X.reading Γ ρ) :
    SpineTyped (jTypeI X.reading (.sort Tower.zero))
      [cinterp X.reading A ρ, cinterp X.reading x ρ,
        cinterp X.reading M ρ, cinterp X.reading d ρ,
        cinterp X.reading y ρ, cinterp X.reading p ρ] := by
  obtain ⟨-, -, sJ⟩ := CTyped.sound X.valid
    (cjSpine6_typed (jArgs_mor J.tA J.tx J.tM J.td J.ty J.tp) J.tp X.sub) fits
  exact (SpineFacts.constSpine
    (X.sub.constantType (objectChurch_declared (c := jName) (T := Package.jType) (by decide) rfl)) sJ).1.2

/-- The path's reflexivity tag relates the substituted paths. -/
theorem JCase.reflTag (J : JCase X H Γ A x M d y p) (fits : Fits X.reading Γ ρ)
    (formed : CCtxFormed X.church Δ) (hσ : SubstRel X.reading H Γ ρ Δ σ σ')
    (hpTag : (cinterp X.reading p ρ).Mem (.tag .refl)) :
    RT H Δ true (.tag .refl) (.id (A.subst σ) (x.subst σ) (y.subst σ)) (p.subst σ)
      (p.subst σ') :=
  J.hp ρ fits formed hσ (.tag .refl) hpTag ⟨[.tag .ident],
    fun _ h => by rw [List.mem_singleton.1 h]; exact Ideal.subset_closure (.inl rfl),
    Elem.ty_tag (k := .ident) trivial Elem.isUniv_univ, tyTok_tag_refl.2 List.mem_cons_self⟩

include levels in
/-- **The motive's instances at the base point and at the path are related as types**,
as far as every token of a type witness below the motive at the path's point and its
reflexivity observes: the motive's conversion at the reflexivity point, at the typed
point tokens of the path, whose carrier is related to itself by the carrier's
adequacy. -/
theorem RT.objectJ_motive (J : JCase X H Γ A x M d y p) (fits : Fits X.reading Γ ρ)
    (formed : CCtxFormed X.church Δ) (hσ : SubstRel X.reading H Γ ρ Δ σ σ')
    (hpTag : (cinterp X.reading p ρ).Mem (.tag .refl))
    {a : List Tok} (haBelow : Ideal.Below a (Ideal.app (Ideal.app (cinterp X.reading M ρ)
      (Ideal.reflPoint (cinterp X.reading p ρ)))
      (Ideal.refl (Ideal.reflPoint (cinterp X.reading p ρ)))))
    (hau : Ty a Elem.univ) :
    ∀ c ∈ a, RT H Δ false c
      (.app (.app (M.subst σ) (x.subst σ)) (.refl (x.subst σ)))
      (.app (.app (M.subst σ) (x.subst σ)) (.refl (x.subst σ)))
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) := by
  obtain ⟨tA, tx, tM, td, ty, tp, hM, hd, hp, hA⟩ := J
  have hpElem :
      projT (cinterp X.reading (.id A x y) ρ) (cinterp X.reading p ρ) =
        cinterp X.reading p ρ :=
    (CTyped.sound X.valid tp fits).2.1
  have hMElem := (CTyped.sound X.valid tM fits).2.1
  -- the substituted typings
  have tMσ : CTyped X.church Δ (M.subst σ) (.pi (A.subst σ)
      (.pi (.id ((A.subst σ).rename wk) ((x.subst σ).rename wk) (.var 0)) cU0)) := by
    have h := tM.substitute hσ.1.1
    rwa [motiveType_subst] at h
  have tpσ : CTyped X.church Δ (p.subst σ) (.id (A.subst σ) (x.subst σ) (y.subst σ)) :=
    tp.substitute hσ.1.1
  -- the path's reflexivity tag
  have hpRefl := JCase.reflTag ⟨tA, tx, tM, td, ty, tp, hM, hd, hp, hA⟩ fits formed hσ hpTag
  obtain ⟨B, x₁, y₁, r, r', hred⟩ := RT.tm_reflTag_iff.1 hpRefl
  obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align
    (CRedTy.refl (CTyped.isType levels tpσ formed)) hred.1
  obtain ⟨-, rp, -, erx, ery, -⟩ := hred
  -- the path's typed point tokens relate its point to the endpoints
  have points : ∀ q, Ideal.TypedPoint (cinterp X.reading (.id A x y) ρ)
      (cinterp X.reading p ρ) q →
      RT H Δ true q (A.subst σ) r (x.subst σ) ∧
        RT H Δ true q (A.subst σ) r (y.subst σ) := by
    intro q ⟨hq, hqT⟩
    have h := hp ρ fits formed hσ _ hq hqT
    rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B', x', y', r₁, r₁', hred', -, hpt⟩
    · have hq0 : ent [] q = true := by
        rw [ent_arg, List.all_nil, Bool.true_and] at hvac
        exact hvac
      exact ⟨RT.of_vacuous hq0, RT.of_vacuous hq0⟩
    · obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align
        (CRedTy.refl (CTyped.isType levels tpσ formed)) hred'.1
      obtain rfl := CRedTm.refl_align rp hred'.2.1
      obtain ⟨h₁, h₂, -⟩ := hpt rfl
      exact ⟨h₁, h₂⟩
  -- the motive, related to itself at its aligned entries
  intro c hc
  obtain ⟨Z₁, Z₂, hentry, hZ₁, hZ₂⟩ := Ideal.motive_entry (haBelow c hc)
  obtain ⟨S, hS, h₁, h₂⟩ := Ideal.aligned_inputs hpElem hZ₁ hZ₂
  obtain ⟨cS, hcS, hSc, hAc⟩ := typed_points_with
      (Q := fun q => RT H Δ false q (A.subst σ) (A.subst σ) (A.subst σ)) fun q hq => by
    obtain ⟨-, b, hb, hbu, hbq⟩ := hS q hq
    refine ⟨args .ident 0 b, ty_args_ident hbu, (tyTok_reflPoint.1 hbq).2.2.1, fun r hr => ?_⟩
    exact Adequate.toType levels X.soundnessFacts (X.sort _) hA fits formed hσ.left
      (Ideal.below_args_ident hb r hr) (ty_args_ident hbu r hr)
  have hMentry : RT H Δ true (.fn .lam [] Z₁ [.fn .lam [] Z₂ [c]])
      (.pi (A.subst σ) (.pi (.id ((A.subst σ).rename wk) ((x.subst σ).rename wk) (.var 0))
        (.head (.sort Tower.zero)))) (M.subst σ) (M.subst σ) := by
    rw [← hMElem] at hentry
    obtain ⟨w, hwM, hwT, hwe⟩ := Ideal.projT_eq_iSup.1 hentry
    have h := RT.closed' hwe fun e he => hM ρ fits formed hσ e (hwM e he) (hwT e he)
    rw [motiveType_subst] at h
    exact RT.left h
  exact RT.motive_reflPoint levels formed (X.sort Tower.zero) tMσ hMentry rp erx ery hcS hSc hAc
    (fun q hq => (points q (hS q hq)).1) (fun q hq => (points q (hS q hq)).2) h₁ h₂
    (fun w hw => by rw [List.mem_singleton.1 hw]; exact hau c hc) c List.mem_cons_self

include levels in
/-- **The eliminator's step at one witness token.** At a token of the method typed at the
motive at the path's point and its reflexivity, the path carrying the reflexivity tag:
the method's relation converts from `M x (refl x)` to `M y p`, and the spines
`J A x M d y p` and `J A x M d' y p'` are related at `M y p`. -/
theorem RT.objectJ_at
    (jPath : ∀ {m : Nat} {A x M d y q q' : CTm Tower.Head m}, H.step q q' →
      H.step (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q)
        (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q'))
    (J : JCase X H Γ A x M d y p) (fits : Fits X.reading Γ ρ)
    (formed : CCtxFormed X.church Δ) (hσ : SubstRel X.reading H Γ ρ Δ σ σ')
    {t : Tok} (hpTag : (cinterp X.reading p ρ).Mem (.tag .refl))
    (htd : (cinterp X.reading d ρ).Mem t)
    {a : List Tok} (haBelow : Ideal.Below a (Ideal.app (Ideal.app (cinterp X.reading M ρ)
      (Ideal.reflPoint (cinterp X.reading p ρ)))
      (Ideal.refl (Ideal.reflPoint (cinterp X.reading p ρ)))))
    (hau : Ty a Elem.univ) (hat : TyTok a t) :
    RT H Δ true t (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ))
      (CTm.appSpine (.const jName) [A.subst σ, x.subst σ, M.subst σ, d.subst σ, y.subst σ,
        p.subst σ])
      (CTm.appSpine (.const jName) [A.subst σ, x.subst σ, M.subst σ, d.subst σ', y.subst σ,
        p.subst σ']) ∧
    RT H Δ true t (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) (d.subst σ)
      (d.subst σ') := by
  obtain ⟨tA, tx, tM, td, ty, tp, hM, hd, hp, hA⟩ := J
  have hpElem :
      projT (cinterp X.reading (.id A x y) ρ) (cinterp X.reading p ρ) =
        cinterp X.reading p ρ :=
    (CTyped.sound X.valid tp fits).2.1
  have hle := (Ideal.reflPoint_le_endpoints hpElem).1
  -- the substituted typings
  have tAσ : CTyped X.church Δ (A.subst σ) cU0 := tA.substitute hσ.1.1
  have txσ : CTyped X.church Δ (x.subst σ) (A.subst σ) := tx.substitute hσ.1.1
  have tMσ : CTyped X.church Δ (M.subst σ) (.pi (A.subst σ)
      (.pi (.id ((A.subst σ).rename wk) ((x.subst σ).rename wk) (.var 0)) cU0)) := by
    have h := tM.substitute hσ.1.1
    rwa [motiveType_subst] at h
  have tdσ : CTyped X.church Δ (d.subst σ)
      (.app (.app (M.subst σ) (x.subst σ)) (.refl (x.subst σ))) := td.substitute hσ.1.1
  have tdσ' : CTyped X.church Δ (d.subst σ')
      (.app (.app (M.subst σ) (x.subst σ)) (.refl (x.subst σ))) :=
    (CEqual.typed levels (CDerivable.functional td hσ.1) formed).2
  have tyσ : CTyped X.church Δ (y.subst σ) (A.subst σ) := ty.substitute hσ.1.1
  have tpσ : CTyped X.church Δ (p.subst σ) (.id (A.subst σ) (x.subst σ) (y.subst σ)) :=
    tp.substitute hσ.1.1
  have epσ : CEqual X.church Δ (p.subst σ) (p.subst σ')
      (.id (A.subst σ) (x.subst σ) (y.subst σ)) := CDerivable.functional tp hσ.1
  -- the path's reflexivity tag
  have hpRefl := JCase.reflTag ⟨tA, tx, tM, td, ty, tp, hM, hd, hp, hA⟩ fits formed hσ hpTag
  obtain ⟨B, x₁, y₁, r, r', hred⟩ := RT.tm_reflTag_iff.1 hpRefl
  obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align
    (CRedTy.refl (CTyped.isType levels tpσ formed)) hred.1
  obtain ⟨-, rp, -, erx, ery, -⟩ := hred
  -- the method, related at the motive at the base point
  have htdT : TypedAt (cinterp X.reading (.app (.app M x) (.refl x)) ρ) t :=
    ⟨a, fun c hc => Ideal.app_mono (Ideal.app_mono (Ideal.le_refl _) hle)
      (Ideal.refl_mono hle) c (haBelow c hc), hau, hat⟩
  have hdσ := hd ρ fits formed hσ t htd htdT
  -- the motive, related to itself at its aligned entries
  have motive := RT.objectJ_motive levels ⟨tA, tx, tM, td, ty, tp, hM, hd, hp, hA⟩ fits formed hσ
    hpTag haBelow hau
  -- the motive's instances are equal types
  have eAB : CTypeEq X.church Δ (.app (.app (M.subst σ) (x.subst σ)) (.refl (x.subst σ)))
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) := by
    have exy : CEqual X.church Δ (x.subst σ) (y.subst σ) (A.subst σ) :=
      .trans (.symm erx) ery
    have hE : CTm.inst0 (x.subst σ)
        (.pi (.id ((A.subst σ).rename wk) ((x.subst σ).rename wk) (.var 0)) cU0) =
        (.pi (.id (A.subst σ) (x.subst σ) (x.subst σ)) cU0 : CTm Tower.Head m) := by
      change CTm.pi (.id (CTm.inst0 (x.subst σ) ((A.subst σ).rename wk))
        (CTm.inst0 (x.subst σ) ((x.subst σ).rename wk)) (x.subst σ)) cU0 = _
      rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]
    have e₁ := CDerivable.appCong (.refl tMσ) exy
    rw [hE] at e₁
    have eId : CTypeEq X.church Δ (.id (A.subst σ) (x.subst σ) (y.subst σ))
        (.id (A.subst σ) (x.subst σ) (x.subst σ)) :=
      ⟨.sort Tower.zero, X.sort _,
        .idCong (.refl tAσ) (X.sort _) (.refl txσ) (.trans (.symm ery) erx)⟩
    have e₂ : CEqual X.church Δ (.refl (x.subst σ)) (p.subst σ)
        (.id (A.subst σ) (x.subst σ) (x.subst σ)) :=
      .trans (.reflCong (.symm erx)) (CEqual.convType (.symm rp.2) eId)
    exact ⟨.sort Tower.zero, X.sort _, CDerivable.appCong e₁ e₂⟩
  have hdConv := (RT.conv_iff levels formed hau hat motive eAB).1 hdσ
  -- the eliminator's step
  have tS := cjSpine5_typed (jArgs_mor tAσ txσ tMσ tdσ tyσ tpσ) X.sub
  have tS' := cjSpine5_typed (jArgs_mor tAσ txσ tMσ tdσ' tyσ tpσ) X.sub
  exact ⟨RT.objectEliminator X.within (X.sort _) levels formed jPath tAσ txσ tMσ tdσ tdσ' tyσ tS tS' epσ hpRefl
    hdConv, hdConv⟩

include levels in
/-- **The eliminator's step of the relation at the witnesses of an extension's reading.** For an
adequate motive, method and path, at every token of the denotation of `J A x M d y p` the
spines `J A x M d y p` and `J A x M d' y p'` are related at `M y p`, where `d'` and `p'` are
substituted by the right one of two related substitutions and everything else by the left
one. -/
theorem RT.objectJAligned
    (jPath : ∀ {m : Nat} {A x M d y q q' : CTm Tower.Head m}, H.step q q' →
      H.step (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q)
        (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q'))
    (J : JCase X H Γ A x M d y p) (fits : Fits X.reading Γ ρ)
    (formed : CCtxFormed X.church Δ) (hσ : SubstRel X.reading H Γ ρ Δ σ σ')
    {s : Tok}
    (hs : (cinterp X.reading (CTm.appSpine (.const jName) [A, x, M, d, y, p]) ρ).Mem s) :
    RT H Δ true s (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ))
      (CTm.appSpine (.const jName) [A.subst σ, x.subst σ, M.subst σ, d.subst σ, y.subst σ,
        p.subst σ])
      (CTm.appSpine (.const jName) [A.subst σ, x.subst σ, M.subst σ, d.subst σ', y.subst σ,
        p.subst σ']) := by
  rw [cinterp_appSpine] at hs
  change (Ideal.appSpine (X.reading.const jName) _).Mem s at hs
  rw [X.reading_j] at hs
  obtain ⟨v, hvs, hv⟩ := mem_appSpine_jAlignedConst (J.spine fits) hs
  refine RT.closed' hvs fun t ht => ?_
  obtain ⟨hpTag, htd, a, haBelow, hau, hat⟩ := hv t ht
  exact (RT.objectJ_at levels jPath J fits formed hσ hpTag htd haBelow hau hat).1

include levels in
/-- **The eliminator's case of the fundamental lemma, in an extension.** For an
adequate motive, method and path, the eliminator's spine `J A x M d y p` is adequate at
`M y p`: related substitutions send it to related spines, as far as every token of its
denotation observes. The spine with only the method and the path substituted by the right
substitution is related to the left spine (`RT.objectJ_at`), and to the right spine by
head expansion: both contract to the right method along the right path's reduction to a
reflexivity. -/
theorem Adequate.objectJ
    (jPath : ∀ {m : Nat} {A x M d y q q' : CTm Tower.Head m}, H.step q q' →
      H.step (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q)
        (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q'))
    (J : JCase X H Γ A x M d y p) :
    Adequate X.reading H Γ (CTm.appSpine (.const jName) [A, x, M, d, y, p])
      (.app (.app M y) p) := by
  intro ρ fits m Δ σ σ' formed hσ s hs _
  obtain ⟨tA, tx, tM, td, ty, tp, hM, hd, hp, hA⟩ := J
  have J : JCase X H Γ A x M d y p := ⟨tA, tx, tM, td, ty, tp, hM, hd, hp, hA⟩
  rw [cinterp_appSpine] at hs
  change (Ideal.appSpine (X.reading.const jName) _).Mem s at hs
  rw [X.reading_j] at hs
  obtain ⟨v, hvs, hv⟩ := mem_appSpine_jAlignedConst (J.spine fits) hs
  refine RT.closed' hvs fun t ht => ?_
  obtain ⟨hpTag, htd, a, haBelow, hau, hat⟩ := hv t ht
  obtain ⟨step, hdd⟩ := RT.objectJ_at levels jPath J fits formed hσ hpTag htd haBelow hau hat
  -- the motive at the path, related to itself as far as the method's type witness observes
  have hMyp : ∀ c ∈ a, RT H Δ false c (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ))
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ))
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) := fun c hc =>
    RT.left (RT.symm_ty levels formed (hau c hc)
      (RT.objectJ_motive levels J fits formed hσ hpTag haBelow hau c hc))
  -- the substituted typings, left and right
  have hσr := hσ.symm levels formed
  have tAσ : CTyped X.church Δ (A.subst σ) cU0 := tA.substitute hσ.1.1
  have txσ : CTyped X.church Δ (x.subst σ) (A.subst σ) := tx.substitute hσ.1.1
  have tMσ : CTyped X.church Δ (M.subst σ) (.pi (A.subst σ)
      (.pi (.id ((A.subst σ).rename wk) ((x.subst σ).rename wk) (.var 0)) cU0)) := by
    have h := tM.substitute hσ.1.1
    rwa [motiveType_subst] at h
  have tdσ' : CTyped X.church Δ (d.subst σ')
      (.app (.app (M.subst σ) (x.subst σ)) (.refl (x.subst σ))) :=
    (CEqual.typed levels (CDerivable.functional td hσ.1) formed).2
  have tyσ : CTyped X.church Δ (y.subst σ) (A.subst σ) := ty.substitute hσ.1.1
  have tpσ : CTyped X.church Δ (p.subst σ) (.id (A.subst σ) (x.subst σ) (y.subst σ)) :=
    tp.substitute hσ.1.1
  have tAσ' : CTyped X.church Δ (A.subst σ') cU0 := tA.substitute hσr.1.1
  have txσ' : CTyped X.church Δ (x.subst σ') (A.subst σ') := tx.substitute hσr.1.1
  have tMσ' : CTyped X.church Δ (M.subst σ') (.pi (A.subst σ')
      (.pi (.id ((A.subst σ').rename wk) ((x.subst σ').rename wk) (.var 0)) cU0)) := by
    have h := tM.substitute hσr.1.1
    rwa [motiveType_subst] at h
  have tdσ'' : CTyped X.church Δ (d.subst σ')
      (.app (.app (M.subst σ') (x.subst σ')) (.refl (x.subst σ'))) := td.substitute hσr.1.1
  have tyσ' : CTyped X.church Δ (y.subst σ') (A.subst σ') := ty.substitute hσr.1.1
  have tpσ' :
      CTyped X.church Δ (p.subst σ') (.id (A.subst σ') (x.subst σ') (y.subst σ')) :=
    tp.substitute hσr.1.1
  -- the equalities between the two substitutions
  have eA : CTypeEq X.church Δ (A.subst σ) (A.subst σ') :=
    ⟨.sort Tower.zero, X.sort _, CDerivable.functional tA hσ.1⟩
  have ex : CEqual X.church Δ (x.subst σ) (x.subst σ') (A.subst σ) :=
    CDerivable.functional tx hσ.1
  have ey : CEqual X.church Δ (y.subst σ) (y.subst σ') (A.subst σ) :=
    CDerivable.functional ty hσ.1
  have tId : CTyped X.church Γ (.id A x y) cU0 := .idForm tA (X.sort _) tx ty
  have eId : CTypeEq X.church Δ (.id (A.subst σ) (x.subst σ) (y.subst σ))
      (.id (A.subst σ') (x.subst σ') (y.subst σ')) :=
    ⟨.sort Tower.zero, X.sort _, CDerivable.functional tId hσ.1⟩
  have tFam : CTyped X.church Γ (.app (.app M y) p) cU0 := by
    have h := CDerivable.appElim tM ty
    rw [show CTm.inst0 y (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) cU0) =
        (.pi (.id A x y) cU0 : CTm Tower.Head n) from by
      change CTm.pi (.id (CTm.inst0 y (A.rename wk)) (CTm.inst0 y (x.rename wk)) y) cU0 = _
      rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]] at h
    exact CDerivable.appElim h tp
  have eFam : CTypeEq X.church Δ (.app (.app (M.subst σ') (y.subst σ')) (p.subst σ'))
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) :=
    ⟨.sort Tower.zero, X.sort _, .symm (CDerivable.functional tFam hσ.1)⟩
  have epσ : CEqual X.church Δ (p.subst σ) (p.subst σ')
      (.id (A.subst σ) (x.subst σ) (y.subst σ)) := CDerivable.functional tp hσ.1
  have eFamp : CTypeEq X.church Δ (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ'))
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) := by
    have tMy := CDerivable.appElim tMσ tyσ
    rw [show CTm.inst0 (y.subst σ) (.pi (.id ((A.subst σ).rename wk) ((x.subst σ).rename wk)
        (.var 0)) cU0) = (.pi (.id (A.subst σ) (x.subst σ) (y.subst σ)) cU0 : CTm Tower.Head m)
      from by
        change CTm.pi (.id (CTm.inst0 (y.subst σ) ((A.subst σ).rename wk))
          (CTm.inst0 (y.subst σ) ((x.subst σ).rename wk)) (y.subst σ)) cU0 = _
        rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]] at tMy
    exact ⟨.sort Tower.zero, X.sort _, CDerivable.appCong (.refl tMy) (.symm epσ)⟩
  -- the right path reduces to a reflexivity whose point equals the endpoints
  have hpRefl := JCase.reflTag J fits formed hσ hpTag
  obtain ⟨B, x₁, y₁, r, r', hred⟩ := RT.tm_reflTag_iff.1 hpRefl
  obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align
    (CRedTy.refl (CTyped.isType levels tpσ formed)) hred.1
  obtain ⟨-, -, rp', erx, ery, err⟩ := hred
  have er'x : CEqual X.church Δ r' (x.subst σ) (A.subst σ) := .trans (.symm err) erx
  have er'y : CEqual X.church Δ r' (y.subst σ) (A.subst σ) := .trans (.symm err) ery
  have tr' : CTyped X.church Δ r' (A.subst σ) := (CEqual.typed levels er'x formed).1
  -- the spine with the right method and path contracts to the right method
  have redMix : CRedTm H Δ (CTm.appSpine (.const jName) [A.subst σ, x.subst σ, M.subst σ,
      d.subst σ', y.subst σ, p.subst σ']) (d.subst σ')
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) := by
    have mor : CSubstMor X.church cJTele Δ (CTm.consSub r' (CTm.consSub (y.subst σ)
      (CTm.consSub (d.subst σ') (CTm.consSub (M.subst σ) (CTm.consSub (x.subst σ)
        (CTm.consSub (A.subst σ) Fin.elim0)))))) := fun i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tr'
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tyσ
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tdσ'
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tMσ
      refine Fin.cases ?_ (fun i => ?_) i
      · exact txσ
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tAσ
      exact i.elim0
    have contractum := objectJ_contractum (X.sort _) formed mor er'x er'y
    have jStep := X.within.step <| objectChurch_jStep (CTm.consSub r' (CTm.consSub (y.subst σ) (CTm.consSub (d.subst σ')
        (CTm.consSub (M.subst σ) (CTm.consSub (x.subst σ)
          (CTm.consSub (A.subst σ) Fin.elim0))))))
    have c := CRedTm.eliminator levels formed jStep (objectChurch_jAdmits mor er'x er'y X.within)
      jPath (cjSpine5_typed (jArgs_mor tAσ txσ tMσ tdσ' tyσ tpσ) X.sub) rp'
      (by rw [inst0_motive_family]; exact contractum)
    rw [inst0_motive_family] at c
    exact c.convType eFamp
  -- the right spine contracts to the right method
  have redRight : CRedTm H Δ (CTm.appSpine (.const jName) [A.subst σ', x.subst σ', M.subst σ',
      d.subst σ', y.subst σ', p.subst σ']) (d.subst σ')
      (.app (.app (M.subst σ) (y.subst σ)) (p.subst σ)) := by
    have er'x' : CEqual X.church Δ r' (x.subst σ') (A.subst σ') :=
      CEqual.convType (.trans er'x ex) eA
    have er'y' : CEqual X.church Δ r' (y.subst σ') (A.subst σ') :=
      CEqual.convType (.trans er'y ey) eA
    have tr'' : CTyped X.church Δ r' (A.subst σ') := (CEqual.typed levels er'x' formed).1
    have mor : CSubstMor X.church cJTele Δ (CTm.consSub r' (CTm.consSub (y.subst σ')
      (CTm.consSub (d.subst σ') (CTm.consSub (M.subst σ') (CTm.consSub (x.subst σ')
        (CTm.consSub (A.subst σ') Fin.elim0)))))) := fun i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tr''
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tyσ'
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tdσ''
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tMσ'
      refine Fin.cases ?_ (fun i => ?_) i
      · exact txσ'
      refine Fin.cases ?_ (fun i => ?_) i
      · exact tAσ'
      exact i.elim0
    have contractum := objectJ_contractum (X.sort _) formed mor er'x' er'y'
    have jStep := X.within.step <| objectChurch_jStep (CTm.consSub r' (CTm.consSub (y.subst σ') (CTm.consSub (d.subst σ')
        (CTm.consSub (M.subst σ') (CTm.consSub (x.subst σ') (CTm.consSub (A.subst σ')
          Fin.elim0))))))
    have c := CRedTm.eliminator levels formed jStep (objectChurch_jAdmits mor er'x' er'y' X.within)
      jPath (cjSpine5_typed (jArgs_mor tAσ' txσ' tMσ' tdσ'' tyσ' tpσ') X.sub) (rp'.convType eId)
      (by rw [inst0_motive_family]; exact contractum)
    rw [inst0_motive_family] at c
    exact c.convType eFam
  -- the right method is related to itself, so the two spines are related
  have hd'd' := RT.left (RT.symm levels formed hau hat hMyp hdd)
  exact RT.trans levels formed hau hat hMyp step (RT.expand levels formed redMix redRight hd'd')

end Step

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
