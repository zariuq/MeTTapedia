import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectHeadReduction

/-!
# Controls for the witness-indexed relation at the object package

For every weak-head reduction of the object package's annotated terms:

* **Functions, positive and negative.** At the type `U₁ → U₁` and the token
  `fn lam [] [tag pi] [tag pi]`, typed at a compact type witness of `U₁ → U₁`
  (`typed_fnToken`), the identity `λ (X : U₁). X` is related to itself
  (`id_related`), and it is not related to the constant function
  `λ (X : U₁). U₀` (`id_const_unrelated`): at the dependent function type
  `U₀ → U₀`, the identity returns a dependent function type and the constant
  returns the universe `U₀`, a normal form that is no dependent function type.
* **Paths, positive and negative.** At `Id num 0 0` and the point token
  `arg refl 0 [] (tag zero)`, typed at a compact witness of `Id num 0 0`
  (`typed_pointToken`), `refl 0` is related to itself (`refl_zero_related`), and
  `refl 0` is not related to `refl 1` (`refl_zero_one_unrelated`): the point token
  compares the points `0` and `1` at the tag `zero`, and `1` is a normal successor.
* **Constructors of a declared datatype, positive and negative.** The numbers are the
  object package's declared datatype, with the constructors `zero` and `suc`. At the tag of
  `zero` as a declared constructor, zero is related to itself (`zero_ctor_related`), and zero
  and one, two different constructors, are not related (`zero_one_ctor_unrelated`). At the
  token saying that the field of `suc` is zero, one is related to itself
  (`one_field_related`), and one and two, whose fields zero and one are not related there, are
  not related (`one_two_field_unrelated`). Closure under entailment needs the field tokens:
  over a variable `x` of the numbers, the tag of `suc` relates `suc x` to itself, and the tag
  with the field token entails the field token, which does not, since `x` takes no step and
  is not zero (`closed_needs_fields`).
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
namespace RelationControls

/-! ## The tokens, typed -/

/-- A compact type witness of `U → U`. -/
def fnWitness : List Tok := Elem.former .pi Elem.univ [([.tag .pi], Elem.univ)]

/-- The function token of the controls at `U → U`. -/
def fnToken : Tok := .fn .lam [] [.tag .pi] [.tag .pi]

theorem typed_fnToken : Ty fnWitness Elem.univ ∧ TyTok fnWitness fnToken := by
  have hpi : TyTok Elem.univ (.tag .pi) := (tyTok_tag_former (k := .pi) trivial).2 Elem.isUniv_univ
  refine ⟨Elem.ty_former (.inl rfl) Elem.isUniv_univ Elem.ty_univ_univ fun p hp => ?_, ?_⟩
  · rw [List.mem_singleton.1 hp]
    exact ⟨fun t ht => by rw [List.mem_singleton.1 ht]; exact hpi, Elem.ty_univ_univ⟩
  · refine tyTok_lam.2 ⟨List.mem_cons_self, rfl, fun x hx => ?_, fun y hy => ?_⟩
    · rw [List.mem_singleton.1 hx]
      refine (tyTok_tag_former (k := .pi) trivial).2 (.inl ?_)
      exact mem_args_of_arg (C := []) (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map_of_mem List.mem_cons_self)))
    · rw [List.mem_singleton.1 hy]
      refine (tyTok_tag_former (k := .pi) trivial).2 (.inl ?_)
      exact mem_fnApp.2 ⟨Elem.univ, [.tag .pi], Elem.univ, List.mem_cons_of_mem _
        (List.mem_append_right _ List.mem_cons_self), fun s hs => ent_of_mem hs,
        List.mem_cons_self⟩

/-- A compact witness of `Id num 0 0`. -/
def pathWitness : List Tok := Elem.ident Elem.nat Elem.zero Elem.zero

/-- The point token of the controls at `Id num 0 0`. -/
def pointToken : Tok := .arg .refl 0 [] (.tag .zero)

theorem typed_pointToken : Ty pathWitness Elem.univ ∧ TyTok pathWitness pointToken := by
  have hzero : Ty Elem.zero Elem.nat := Elem.ty_zero List.mem_cons_self
  have hnat : Ty Elem.nat Elem.univ := Elem.ty_tag (k := .nat) trivial Elem.isUniv_univ
  refine ⟨Elem.ty_ident Elem.isUniv_univ hnat hzero hzero, ?_⟩
  refine tyTok_reflPoint.2 ⟨List.mem_cons_self, rfl, ?_, ?_, ?_⟩
  · refine tyTok_tag_zero.2 (mem_args_of_arg (C := []) (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem List.mem_cons_self)))))
  · exact ent_of_mem (mem_args_of_arg (C := Elem.nat) (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem List.mem_cons_self)))))
  · exact ent_of_mem (mem_args_of_arg (C := Elem.nat) (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_map_of_mem List.mem_cons_self))))

variable {H : HeadReduction objectChurch objectRigid} {n : Nat} {Γ : CCtx Tower.Head n}

/-! ## Functions -/

theorem piU1_type : CIsType objectChurch Γ (.pi cU1 cU1) :=
  ⟨.sort (.succ (.succ Tower.zero)), .sort _, cpiT (CU_typed _) (CU_typed _)⟩

theorem cU1_red : CRedTy H Γ (cU1 : CTm Tower.Head n) (.head (.sort (.succ Tower.zero))) :=
  CRedTy.refl ⟨.sort (.succ (.succ Tower.zero)), .sort _, CU_typed _⟩

/-- **Positive**: the identity on `U₁` is related to itself at `U₁ → U₁`. -/
theorem id_related {L : Type} [LevelOrder L] (levels : LevelModel objectRules L)
    (formed : CCtxFormed objectChurch Γ) :
    RT H Γ true fnToken (.pi cU1 cU1) (.lam cU1 (.var 0)) (.lam cU1 (.var 0)) := by
  have beta : ∀ {N : CTm Tower.Head n}, CTyped objectChurch Γ N cU1 →
      CRedTm H Γ (.app (.lam cU1 (.var 0)) N) N cU1 := fun tN =>
    ⟨.single (H.beta cU1 (.var 0) _),
      .betaPi (cpiT (CU_typed _) (CU_typed _)) (.sort _) (.var 0) tN⟩
  refine RT.tm_lam_iff.2 (.inr fun D E hred => ?_)
  have e := H.red_normal (H.normal_pi _ _) hred.1
  injection e with _ eD eE
  subst eD eE
  refine ⟨fun N N' hNN hX y hy => ?_, fun N tN hX y hy => ?_⟩
  · rw [List.mem_singleton.1 hy]
    obtain ⟨tN, tN'⟩ := CEqual.typed levels hNN formed
    have h := RT.expand levels formed (beta tN) (beta tN') (hX _ List.mem_cons_self)
    exact ⟨h, h⟩
  · rw [List.mem_singleton.1 hy]
    exact RT.expand levels formed (beta tN) (beta tN) (hX _ List.mem_cons_self)

/-- **Negative**: the identity on `U₁` and the constant function with value `U₀`
are not related at `U₁ → U₁`. -/
theorem id_const_unrelated :
    ¬ RT H Γ true fnToken (.pi cU1 cU1) (.lam cU1 (.var 0)) (.lam cU1 cU0) := by
  intro h
  rcases RT.tm_lam_iff.1 h with hvac | hcl
  · have e := vacuous_out hvac (List.mem_cons_self (a := (Tok.tag .pi : Tok)) (l := []))
    rw [ent_nil_tag] at e
    cases e
  obtain ⟨-, hii⟩ := hcl _ _ (CRedTy.refl piU1_type)
  have tN : CTyped objectChurch Γ (.pi cU0 cU0) cU1 := cpiT cU0_typed cU0_typed
  have tU0 : CTypeEq objectChurch Γ cU0 cU0 := ⟨.sort _, .sort _, .refl cU0_typed⟩
  have tU0' : CTypeEq objectChurch (.snoc Γ cU0) cU0 cU0 := ⟨.sort _, .sort _, .refl cU0_typed⟩
  have hN : RT H Γ true (.tag .pi) cU1 (.pi cU0 cU0) (.pi cU0 cU0) := by
    refine RT.ofType rfl (.sort _) cU1_red (RT.ty_pi_iff.2 ⟨cU0, cU0, cU0, cU0, ?_⟩)
    have r : CRedTy H Γ (.pi cU0 cU0 : CTm Tower.Head n) (.pi cU0 cU0) :=
      CRedTy.refl ⟨.sort _, .sort _, tN⟩
    exact ⟨r, r, tU0, tU0'⟩
  have happ := hii (.pi cU0 cU0) tN (fun x hx => by rw [List.mem_singleton.1 hx]; exact hN)
    (.tag .pi) List.mem_cons_self
  obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_iff.1 (RT.toType rfl cU1_red happ)
  rcases rtg_head hp.2.1.1 with e | ⟨c, s, rest⟩
  · cases e
  · have e := H.deterministic s (H.beta cU1 cU0 (.pi cU0 cU0))
    subst e
    have e' := H.red_normal (t := .head (.sort Tower.zero)) (H.normal_head _) rest
    cases e'

/-! ## Paths -/

theorem id00_type : CIsType objectChurch Γ (.id cnum czero czero) :=
  ⟨.sort _, .sort _, cidT cnum_typed czero_typed czero_typed⟩

theorem zero_related : RT H Γ true (.tag .zero) cnum czero czero :=
  RT.tm_zero_iff.2 ⟨CRedTy.refl ⟨.sort _, .sort _, cnum_typed⟩, CRedTm.refl czero_typed,
    CRedTm.refl czero_typed⟩

/-- **Positive**: `refl 0` is related to itself at `Id num 0 0`. -/
theorem refl_zero_related :
    RT H Γ true pointToken (.id cnum czero czero) (.refl czero) (.refl czero) := by
  have tRefl : CTyped objectChurch Γ (.refl czero) (.id cnum czero czero) := .reflIntro czero_typed
  refine RT.tm_argRefl_iff.2 (.inr ⟨cnum, czero, czero, czero, czero,
    ⟨CRedTy.refl id00_type, CRedTm.refl tRefl, CRedTm.refl tRefl, .refl czero_typed,
      .refl czero_typed, .refl czero_typed⟩, fun c hc => absurd hc List.not_mem_nil,
    fun _ => ⟨zero_related, zero_related, zero_related⟩⟩)

/-- **Negative**: `refl 0` and `refl 1` are not related at `Id num 0 0`. -/
theorem refl_zero_one_unrelated :
    ¬ RT H Γ true pointToken (.id cnum czero czero) (.refl czero) (.refl (csuc czero)) := by
  intro h
  rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B, x, y, r, r', hr, -, hpts⟩
  · have e := vacuous_arg hvac
    rw [ent_nil_tag] at e
    cases e
  have e₁ := H.red_normal (H.normal_id _ _ _) hr.1.1
  injection e₁ with _ eB ex ey
  subst eB ex ey
  have e₂ := H.red_normal (H.normal_refl _) hr.2.2.1.1
  injection e₂ with _ er'
  subst er'
  have e₃ := H.red_normal (H.normal_refl _) hr.2.1.1
  injection e₃ with _ er
  subst er
  obtain ⟨-, -, hzero⟩ := hpts rfl
  obtain ⟨-, -, h₁⟩ := RT.tm_zero_iff.1 hzero
  have e₄ := H.red_normal (t := .app (.const sucN) czero) (H.normal_suc _) h₁.1
  cases e₄

/-! ## Constructors of a declared datatype -/

/-- Zero, a constructor of the numbers with no field. -/
abbrev zeroK : Kind := .ctor numN zeroN []

/-- The successor, a constructor of the numbers with one recursive field. -/
abbrev sucK : Kind := .ctor numN sucN [.self]

theorem cnum_red : CRedTy H Γ (cnum : CTm Tower.Head n) (.const numN) :=
  CRedTy.refl ⟨.sort _, .sort _, cnum_typed⟩

/-- **Positive**: zero is related to itself as far as the tag of `zero` observes. -/
theorem zero_ctor_related : RT H Γ true (.tag zeroK) cnum czero czero :=
  RT.tm_ctorTag_iff.2 ⟨[], [], objectRigid.zero_ctor, cnum_red, CRedTm.refl czero_typed,
    CRedTm.refl czero_typed, .nil⟩

/-- **Negative**: two different constructors are not related: zero and one, as far as the tag
of `zero` observes. -/
theorem zero_one_ctor_unrelated : ¬ RT H Γ true (.tag zeroK) cnum czero (csuc czero) := by
  intro h
  obtain ⟨ms, ms', hs⟩ := RT.tm_ctorTag_iff.1 h
  obtain rfl : ms' = [] := List.eq_nil_of_length_eq_zero hs.2.2.2.2.length.2
  have e := H.red_normal (H.normal_suc czero) hs.2.2.2.1.1
  cases e

/-- **Positive**: one is related to itself as far as the token saying that the field of `suc`
is zero observes. -/
theorem one_field_related :
    RT H Γ true (.arg sucK 0 [] (.tag zeroK)) cnum (csuc czero) (csuc czero) := by
  have t₁ : CTyped objectChurch Γ (csuc czero) cnum := csuc_typed czero_typed
  refine RT.tm_field_iff.2 (.inr ⟨[czero], [czero], ⟨objectRigid.suc_ctor, cnum_red,
    CRedTm.refl t₁, CRedTm.refl t₁, .cons rfl (.refl czero_typed) .nil⟩,
    fun r hr => absurd hr List.not_mem_nil, fun A m m' hA => ?_⟩)
  obtain ⟨⟨f, hf, hA⟩, h₁, h₂⟩ := hA
  cases hf
  cases hA
  cases h₁
  cases h₂
  exact zero_ctor_related

/-- **Negative**: a constructor applied to fields that are not related is not related: one and
two have the fields zero and one, which are not related as far as the tag of `zero` observes,
so one and two are not related as far as the token saying that the field of `suc` is zero
observes. -/
theorem one_two_field_unrelated :
    ¬ RT H Γ true (.arg sucK 0 [] (.tag zeroK)) cnum (csuc czero) (csuc (csuc czero)) := by
  intro h
  rcases RT.tm_field_iff.1 h with hvac | ⟨ms, ms', hs, -, hfld⟩
  · have e := vacuous_arg hvac
    rw [ent_nil_tag] at e
    cases e
  have t₁ : CTyped objectChurch Γ (csuc czero) cnum := csuc_typed czero_typed
  have t₂ : CTyped objectChurch Γ (csuc (csuc czero)) cnum := csuc_typed t₁
  obtain rfl : ms = [czero] := CRedTm.ctor_align (ms := [czero]) objectRigid.suc_ctor rfl
    hs.2.2.2.2.length.1 (CRedTm.refl t₁) hs.2.2.1
  obtain rfl : ms' = [csuc czero] := CRedTm.ctor_align (ms := [csuc czero]) objectRigid.suc_ctor
    rfl hs.2.2.2.2.length.2 (CRedTm.refl t₂) hs.2.2.2.1
  exact zero_one_ctor_unrelated (hfld cnum czero (csuc czero) ⟨⟨.self, rfl, rfl⟩, rfl, rfl⟩)

omit H in
/-- **Negative**: closure under entailment needs the field tokens of a constructor. Over a
variable `x` of the numbers, the tag of `suc` relates `suc x` to itself; with the token saying
that the field of `suc` is zero it entails that token, which does not relate `suc x` to itself,
since `x` takes no step and is not zero. -/
theorem closed_needs_fields :
    ¬ ∀ (v : List Tok) (t : Tok) (T M M' : CTm Tower.Head (n + 1)), ent v t = true →
      (∀ s ∈ v, s = .tag t.kind → RT objectHeadReduction (.snoc Γ cnum) true s T M M') →
        RT objectHeadReduction (.snoc Γ cnum) true t T M M' := by
  intro h
  have tx : CTyped objectChurch (.snoc Γ cnum) (.var 0) cnum := .var 0
  have tsx : CTyped objectChurch (.snoc Γ cnum) (csuc (.var 0)) cnum := csuc_typed tx
  have hf := h [.tag sucK, .arg sucK 0 [] (.tag zeroK)] (.arg sucK 0 [] (.tag zeroK)) cnum
    (csuc (.var 0)) (csuc (.var 0)) (ent_of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
    fun s _ e => by
      subst e
      exact RT.tm_ctorTag_iff.2 ⟨[.var 0], [.var 0], objectRigid.suc_ctor, cnum_red,
        CRedTm.refl tsx, CRedTm.refl tsx, .cons rfl (.refl tx) .nil⟩
  rcases RT.tm_field_iff.1 hf with hvac | ⟨ms, ms', hs, -, hfld⟩
  · have e := vacuous_arg hvac
    rw [ent_nil_tag] at e
    cases e
  obtain rfl : ms = [.var 0] := CRedTm.ctor_align (ms := [.var 0]) objectRigid.suc_ctor rfl
    hs.2.2.2.2.length.1 (CRedTm.refl tsx) hs.2.2.1
  obtain rfl : ms' = [.var 0] := CRedTm.ctor_align (ms := [.var 0]) objectRigid.suc_ctor rfl
    hs.2.2.2.2.length.2 (CRedTm.refl tsx) hs.2.2.2.1
  obtain ⟨ms₀, ms₀', hz⟩ :=
    RT.tm_ctorTag_iff.1 (hfld cnum (.var 0) (.var 0) ⟨⟨.self, rfl, rfl⟩, rfl, rfl⟩)
  obtain rfl : ms₀ = [] := List.eq_nil_of_length_eq_zero hz.2.2.2.2.length.1
  have normal : objectHeadReduction.Normal (.var 0 : CTm Tower.Head (n + 1)) :=
    fun u => CWhStepR.not_of_whnf (var_whnf objectShape 0) u
  have e := objectHeadReduction.red_normal normal hz.2.2.1.1
  cases e

end RelationControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
