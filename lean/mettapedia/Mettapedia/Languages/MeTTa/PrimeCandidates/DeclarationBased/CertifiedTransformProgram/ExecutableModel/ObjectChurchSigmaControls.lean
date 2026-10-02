import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchRelation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationSigma
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationSub

/-!
# Controls for the dependent pair types and the subtyping mode of the relation

For every weak-head reduction of the object package's annotated terms:

* **A pair related by components, at a dependent family** (`pairRefl_related`). At
  `Σ (x : num). Id num x x` and the second-component token
  `arg pair 1 [tag zero] (tag refl)`, typed at a compact witness of that type
  (`typed_depTokens`), `(0, refl 0)` is related to itself: its first projection
  reduces to `0`, and its second projection reduces to `refl 0` at the family's value
  `Id num N N` at every `N` with a common reduct with the first projection.
* **Negative: unrelated second components** (`pair_second_unrelated`). At `Σ num num`
  and the second-component token `arg pair 1 [] (tag zero)`, `(0, 0)` and `(0, 1)` are
  not related: the second projection of `(0, 1)` reduces to the normal successor.
* **The η pair** (`eta_related`). At `Σ num num → Σ num num` and the function token
  whose input and output are the two component tokens, typed at a compact witness of
  that type (`typed_etaToken`), `λ p. p` is related to `λ p. (fst p, snd p)`.
* **The subtyping mode** (`U0_below_U1`, `num_U1_of_U0`, `U1_not_below_U0`). `U₀` is
  usable at `U₁` at the tag of universes, and subsumption moves the numbers, related as
  a type of `U₀`, to a type of `U₁`; `U₁` is not usable at `U₀`.
* **The ground types kept apart** (`set_related`, `set_legacy_unrelated`). `set` is
  related to itself at the tag of ground types, and not to the legacy ground head:
  both are ground types, and the clause asks for one ground type.
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

namespace CodeModel
namespace SigmaControls

/-! ## The types and the tokens -/

section Types

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The pairs of numbers. -/
abbrev sigNum : CTm Tower.Head n := .sigma cnum cnum

/-- The pairs of a number and a path from it to itself. -/
abbrev sigId : CTm Tower.Head n := .sigma cnum (.id cnum (.var 0) (.var 0))

theorem sigNum_typed : CTyped objectChurch Γ sigNum cU0 := csigmaT cnum_typed cnum_typed

theorem sigId_typed : CTyped objectChurch Γ sigId cU0 :=
  csigmaT cnum_typed (cidT cnum_typed (.var 0) (.var 0))

end Types

/-- A compact witness of `Σ num num`. -/
def sigWitness : List Tok := Elem.former .sigma Elem.nat [([], Elem.nat)]

/-- The first-component token at `Σ num num`. -/
def fstToken : Tok := .arg .pair 0 [] (.tag .zero)

/-- The second-component token at `Σ num num`. -/
def sndToken : Tok := .arg .pair 1 [] (.tag .zero)

theorem ty_nat_univ : Ty Elem.nat Elem.univ := Elem.ty_tag (k := .nat) trivial Elem.isUniv_univ

theorem nat_mem_dom_sig : Tok.tag .nat ∈ args .sigma 0 sigWitness :=
  mem_args_of_arg (C := []) (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_map_of_mem List.mem_cons_self)))

theorem typed_sigTokens :
    Ty sigWitness Elem.univ ∧ TyTok sigWitness fstToken ∧ TyTok sigWitness sndToken := by
  refine ⟨Elem.ty_former (.inr rfl) Elem.isUniv_univ ty_nat_univ fun p hp => ?_, ?_, ?_⟩
  · rw [List.mem_singleton.1 hp]
    exact ⟨fun _ h => absurd h List.not_mem_nil, ty_nat_univ⟩
  · exact tyTok_fst.2 ⟨List.mem_cons_self, rfl, tyTok_tag_zero.2 nat_mem_dom_sig⟩
  · refine tyTok_snd.2 ⟨List.mem_cons_self, fun _ h => absurd h List.not_mem_nil, ?_⟩
    refine tyTok_tag_zero.2 (mem_fnApp.2 ⟨Elem.nat, [], Elem.nat, List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self), fun _ h => absurd h List.not_mem_nil,
      List.mem_cons_self⟩)

/-- A compact witness of `Σ (x : num). Id num x x`. -/
def depWitness : List Tok :=
  Elem.former .sigma Elem.nat [([.tag .zero], Elem.ident Elem.nat Elem.zero Elem.zero)]

/-- The second-component token at `Σ (x : num). Id num x x`, depending on the first
component at the tag `zero`. -/
def depSndToken : Tok := .arg .pair 1 [.tag .zero] (.tag .refl)

theorem typed_depTokens : Ty depWitness Elem.univ ∧ TyTok depWitness depSndToken := by
  have hzero : Ty Elem.zero Elem.nat := Elem.ty_zero List.mem_cons_self
  have hnat0 : Tok.tag .nat ∈ args .sigma 0 depWitness :=
    mem_args_of_arg (C := []) (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map_of_mem List.mem_cons_self)))
  refine ⟨Elem.ty_former (.inr rfl) Elem.isUniv_univ ty_nat_univ fun p hp => ?_, ?_⟩
  · rw [List.mem_singleton.1 hp]
    exact ⟨fun t ht => by rw [List.mem_singleton.1 ht]; exact tyTok_tag_zero.2 List.mem_cons_self,
      Elem.ty_ident Elem.isUniv_univ ty_nat_univ hzero hzero⟩
  · refine tyTok_snd.2 ⟨List.mem_cons_self, fun c hc => ?_, ?_⟩
    · rw [List.mem_singleton.1 hc]
      exact tyTok_tag_zero.2 hnat0
    · refine tyTok_tag_refl.2 (mem_fnApp.2 ⟨Elem.nat, [.tag .zero],
        Elem.ident Elem.nat Elem.zero Elem.zero, List.mem_cons_of_mem _
          (List.mem_append_right _ List.mem_cons_self), fun s hs => ent_of_mem hs,
        List.mem_cons_self⟩)

/-- A compact witness of `Σ num num → Σ num num`. -/
def etaWitness : List Tok := Elem.former .pi sigWitness [([fstToken, sndToken], sigWitness)]

/-- The function token of the η control: both component tokens in, both out. -/
def etaToken : Tok := .fn .lam [] [fstToken, sndToken] [fstToken, sndToken]

theorem typed_etaToken : Ty etaWitness Elem.univ ∧ TyTok etaWitness etaToken := by
  obtain ⟨hw, hf, hs⟩ := typed_sigTokens
  have comps : ∀ x ∈ [fstToken, sndToken], TyTok sigWitness x := fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hf
    · rw [List.mem_singleton.1 hx]; exact hs
  refine ⟨Elem.ty_former (.inl rfl) Elem.isUniv_univ hw fun p hp => ?_, ?_⟩
  · rw [List.mem_singleton.1 hp]
    exact ⟨comps, hw⟩
  · refine tyTok_lam.2 ⟨List.mem_cons_self, rfl, fun x hx => (comps x hx).mono
      (Elem.dom_former _ _ _).2, fun y hy => ?_⟩
    rw [show fnApp .pi etaWitness [fstToken, sndToken] =
        stepApp [([fstToken, sndToken], sigWitness)] [fstToken, sndToken] from
      Elem.fam_former _ _ _ _]
    exact (comps y hy).mono (Le.of_subset fun r hr =>
      mem_stepApp.2 ⟨_, List.mem_singleton_self _, Le.refl _, hr⟩)

variable {H : HeadReduction objectChurch objectRigid} {n : Nat} {Γ : CCtx Tower.Head n}

/-! ## Pairs related by components -/

/-- The pair `(0, refl 0)`. -/
abbrev pairRefl : CTm Tower.Head n := .pair czero (.refl czero)

theorem pairRefl_typed : CTyped objectChurch Γ pairRefl sigId :=
  .pairIntro sigId_typed (.sort _) czero_typed (.reflIntro czero_typed)

/-- **Positive, at a dependent family**: `(0, refl 0)` is related to itself at
`Σ (x : num). Id num x x`, by components. -/
theorem pairRefl_related {L : Type} [LevelOrder L] (levels : LevelModel objectRules L)
    (formed : CCtxFormed objectChurch Γ) :
    RT H Γ true depSndToken sigId pairRefl pairRefl := by
  have fstRed : CRedTm H Γ (.fst pairRefl) czero cnum :=
    ⟨.single (H.fstPair _ _), .betaFst sigId_typed (.sort _) czero_typed (.reflIntro czero_typed)⟩
  have zeroRel : RT H Γ true (.tag .zero) cnum (.fst pairRefl) (.fst pairRefl) :=
    RT.tm_zero_iff.2 ⟨CRedTy.refl ⟨_, .sort _, cnum_typed⟩, fstRed, fstRed⟩
  refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
  have e := H.red_normal (H.normal_sigma _ _) hT.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨.refl (.fstElim pairRefl_typed), fun c hc => ?_, fun h => absurd h (by decide),
    fun _ N Q hQ hNQ => ?_⟩
  · rw [List.mem_singleton.1 hc]
    exact zeroRel
  -- a term with a common reduct with the first projection is equal to `0`
  obtain ⟨Q', h0Q, hNQ'⟩ := CRedTm.join_of_red fstRed hQ hNQ
  have e0N : CEqual objectChurch Γ czero N cnum := .trans h0Q.2 (.symm hNQ'.2)
  have eId : CTypeEq objectChurch Γ (.id cnum czero czero) (.id cnum N N) :=
    ⟨.sort Tower.zero, .sort _, .idCong (.refl cnum_typed) (.sort _) e0N e0N⟩
  have sndRed : CRedTm H Γ (.snd pairRefl) (.refl czero) (.id cnum N N) :=
    ⟨.single (H.sndPair _ _),
      CEqual.convType (.betaSnd sigId_typed (.sort _) czero_typed (.reflIntro czero_typed)) eId⟩
  have idType : CIsType objectChurch Γ (.id cnum N N) := (CTypeEq.isType levels eId formed).2
  exact RT.tm_reflTag_iff.2 ⟨cnum, N, N, czero, czero,
    ⟨CRedTy.refl idType, sndRed, sndRed, e0N, e0N, .refl czero_typed⟩⟩

/-- **Negative**: pairs of numbers with unrelated second components are unrelated. -/
theorem pair_second_unrelated :
    ¬ RT H Γ true sndToken sigNum (.pair czero czero) (.pair czero (csuc czero)) := by
  intro h
  rcases RT.tm_argPair_iff.1 h with hvac | hcl
  · have e := vacuous_arg hvac
    rw [ent_nil_tag] at e
    cases e
  have tFst : CTyped objectChurch Γ (.fst (.pair czero czero)) cnum :=
    .fstElim (.pairIntro sigNum_typed (.sort _) czero_typed czero_typed)
  obtain ⟨-, -, -, h1⟩ := hcl cnum cnum (CRedTy.refl ⟨_, .sort _, sigNum_typed⟩)
  obtain ⟨-, -, r₂⟩ := RT.tm_zero_iff.1
    (h1 rfl (.fst (.pair czero czero)) _ (CRedTm.refl tFst) (CRedTm.refl tFst))
  -- the second projection of `(0, 1)` reduces to the normal successor `1`
  have e := H.nf_unique r₂.1 (.single (H.sndPair _ _)) H.normal_zero (H.normal_suc _)
  cases e

/-! ## The η pair -/

/-- **Positive**: `λ p. p` and `λ p. (fst p, snd p)` are related at
`Σ num num → Σ num num`. -/
theorem eta_related {L : Type} [LevelOrder L] (levels : LevelModel objectRules L)
    (formed : CCtxFormed objectChurch Γ) :
    RT H Γ true etaToken (.pi sigNum sigNum) (.lam sigNum (.var 0))
      (.lam sigNum (.pair (.fst (.var 0)) (.snd (.var 0)))) := by
  have tPi : CTyped objectChurch Γ (.pi sigNum sigNum) cU0 := cpiT sigNum_typed sigNum_typed
  have hT : CRedTy H Γ sigNum (.sigma cnum cnum) := CRedTy.refl ⟨_, .sort _, sigNum_typed⟩
  have tId : CTyped objectChurch (.snoc Γ sigNum) (.var 0) sigNum := .var 0
  have tEta : CTyped objectChurch (.snoc Γ sigNum) (.pair (.fst (.var 0)) (.snd (.var 0))) sigNum :=
    .pairIntro sigNum_typed (.sort _) (.fstElim tId) (.sndElim tId)
  have betaId : ∀ {N : CTm Tower.Head n}, CTyped objectChurch Γ N sigNum →
      CRedTm H Γ (.app (.lam sigNum (.var 0)) N) N sigNum := fun tN =>
    ⟨.single (H.beta _ _ _), .betaPi tPi (.sort _) tId tN⟩
  have betaEta : ∀ {N : CTm Tower.Head n}, CTyped objectChurch Γ N sigNum →
      CRedTm H Γ (.app (.lam sigNum (.pair (.fst (.var 0)) (.snd (.var 0)))) N)
        (.pair (.fst N) (.snd N)) sigNum := fun tN =>
    ⟨.single (H.beta _ _ _), .betaPi tPi (.sort _) tEta tN⟩
  have tPair : ∀ {N : CTm Tower.Head n}, CTyped objectChurch Γ N sigNum →
      CTyped objectChurch Γ (.pair (.fst N) (.snd N)) sigNum := fun tN =>
    .pairIntro sigNum_typed (.sort _) (.fstElim tN) (.sndElim tN)
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨fun N N' hNN hX y hy => ?_, fun N tN hX y hy => ?_⟩
  · obtain ⟨tN, tN'⟩ := CEqual.typed levels hNN formed
    have hy' : RT H Γ true y sigNum N N' := hX y hy
    exact ⟨RT.expand levels formed (betaId tN) (betaId tN') hy',
      RT.expand levels formed (betaEta tN) (betaEta tN')
        (RT.eta_right levels formed hT (tPair tN) tN' (RT.eta_left levels formed hT tN tN' hy'))⟩
  · exact RT.expand levels formed (betaId tN) (betaEta tN)
      (RT.eta_right levels formed hT tN tN (hX y hy))

/-! ## The subtyping mode -/

theorem cumul01 : objectRules.cumulative (.sort Tower.zero) (.sort (.succ Tower.zero)) :=
  fun _ => by simp [LevelExpr.eval, LevelTower.zero]

/-- **Positive**: `U₀` is usable at `U₁` at the tag of universes. -/
theorem U0_below_U1 : RTSub H Γ (.tag .univ) cU0 cU1 :=
  RTSub.univ_iff.2 ⟨.sort Tower.zero, .sort (.succ Tower.zero),
    CRedTy.refl ⟨_, .sort _, cU0_typed⟩, CRedTy.refl ⟨_, .sort _, CU_typed _⟩, .sort _, .sort _,
    .single (.inr cumul01)⟩

/-- **Subsumption at the instance**: the numbers, related as a type of `U₀`, are related
as a type of `U₁`. -/
theorem num_U1_of_U0 {L : Type} [LevelOrder L] (levels : LevelModel objectRules L)
    (formed : CCtxFormed objectChurch Γ) : RT H Γ true (.tag .nat) cU1 cnum cnum := by
  have numRed : CRedTy H Γ (cnum : CTm Tower.Head n) (.const objectRigid.num) :=
    CRedTy.refl ⟨_, .sort _, cnum_typed⟩
  have h0 : RT H Γ true (.tag .nat) cU0 cnum cnum :=
    RT.ofType rfl (.sort _) (CRedTy.refl ⟨_, .sort _, cU0_typed⟩)
      (RT.ty_nat_iff.2 ⟨numRed, numRed⟩)
  exact RT.subConv levels formed Elem.ty_univ_univ
    ((tyTok_tag_former (k := .nat) trivial).2 Elem.isUniv_univ)
    (fun s hs => by rw [List.mem_singleton.1 hs]; exact U0_below_U1) (.subUniv cumul01) h0

/-- Along the order of heads, universe levels do not decrease. -/
theorem headLe_level {h h' : Tower.Head}
    (chain : Relation.ReflTransGen (HeadLe objectRules) h h') :
    ∀ {l : LevelExpr Nat}, h = .sort l → ∃ l', h' = .sort l' ∧
      LevelExpr.eval (fun _ => 0) l ≤ LevelExpr.eval (fun _ => 0) l' := by
  induction chain with
  | refl => exact fun hl => ⟨_, hl, le_refl _⟩
  | @tail b c _ step ih =>
      intro l hl
      obtain ⟨l₁, rfl, hle⟩ := ih hl
      rcases step with (e | e) | e
      · exact ⟨l₁, e.symm, hle⟩
      · cases c with
        | legacyGround => exact e.elim
        | sort l₂ => exact ⟨l₂, rfl, hle.trans (le_of_eq (e _))⟩
      · cases c with
        | legacyGround => exact e.elim
        | sort l₂ => exact ⟨l₂, rfl, hle.trans (e _)⟩

/-- **Negative**: `U₁` is not usable at `U₀`. -/
theorem U1_not_below_U0 : ¬ RTSub H Γ (.tag .univ) cU1 cU0 := by
  intro h
  obtain ⟨h₁, h₂, r₁, r₂, -, -, chain⟩ := RTSub.univ_iff.1 h
  have e₁ := H.red_normal (H.normal_head _) r₁.1
  have e₂ := H.red_normal (H.normal_head _) r₂.1
  injection e₁ with _ e₁
  injection e₂ with _ e₂
  subst e₁ e₂
  obtain ⟨l', e, hle⟩ := headLe_level chain rfl
  injection e with e
  subst e
  simp [LevelExpr.eval, LevelTower.zero] at hle

/-! ## The ground types -/

/-- **Positive**: `set` is related to itself at the tag of ground types. -/
theorem set_related : RT H Γ false (.tag .ground) cset cset cset :=
  RT.ty_ground_iff.2 ⟨cset, .inl rfl, CRedTy.refl ⟨_, .sort _, cset_typed⟩,
    CRedTy.refl ⟨_, .sort _, cset_typed⟩⟩

/-- **Negative**: `set` and the legacy ground head are not related at the tag of ground
types. -/
theorem set_legacy_unrelated :
    ¬ RT H Γ false (.tag .ground) cset cset (.head .legacyGround) := by
  intro h
  obtain ⟨g, -, r₁, r₂⟩ := RT.ty_ground_iff.1 h
  have e₁ := H.red_normal (H.normal_ground (g := cset) (.inl rfl)) r₁.1
  have e₂ := H.red_normal (H.normal_ground (g := .head .legacyGround) (.inr rfl)) r₂.1
  rw [e₁] at e₂
  cases e₂

end SigmaControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
