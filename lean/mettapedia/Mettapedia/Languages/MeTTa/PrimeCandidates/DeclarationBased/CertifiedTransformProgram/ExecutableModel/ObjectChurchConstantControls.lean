import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchConstants

/-!
# Controls for the adequacy of the object constants

**Positive: the iterator at a closed numeral** (`adequate_iterTwo`). The declared type of the
iterator is an adequate type (`adequateType_iterType`), assembled from the adequacy of the
numbers, of the universe, of variables, of applications of variables and of dependent
function and pair types; closed numerals are adequate (`adequate_cnumeral`). So the
iterator's constant is valid (`CStatement.Valid.constAt` at `constAdequateAt_iter`), and
its application to `2` is adequate at the iterator's type at a count.

**Positive: the successor move at one** (`sucMoveOne_related`). `sucMove 1 (refl 1)`
reduces, by the root step of `sucMove` and the root step of the eliminator, to
`refl (suc (add 0 1))` at `eqAt 2` (`sucMoveOne_reduces`), and is related to itself there at
the tag of reflexivity.

**Negative: a broken iteration step** (`brokenReading_not_constAdequate`). Under the
reading whose successor step returns the value and its evidence without applying the step,
the iterator is not adequate, although its declared type stays adequate
(`brokenReading_adequateType`). The reading's token at the count one (`badTok`,
`brokenReading_mem_badTok`) says the first component of the result is zero, while the
iterator's first component there reduces to the step's first component at zero, a normal
form other than zero.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypedAt principal natRecApprox
  natRec natI succI zeroI)
open Package (jName sucMoveName iterName)

namespace CodeModel
namespace ConstantControls

/-! ## Adequate types of the iterator's declared type -/

section Types

variable {H : HeadReduction objectChurch objectRigid}

/-- A variable of the universe `U₀` is an adequate type. -/
theorem adequateType_var {n : Nat} {Γ : CCtx Tower.Head n} (i : Fin n) (h : Γ.lookup i = cU0) :
    AdequateType objectChurchReading H Γ (.var i) := by
  have v : (CStatement.typing Γ (.var i) cU0).Valid objectChurchReading H := by
    rw [← h]
    exact CStatement.Valid.var i
  exact v.1.adequateType ConvRules.objectLevels objectChurch_soundnessFacts (.sort _)

/-- A family variable of `A → U₀` at a variable of `A` is an adequate type. -/
theorem adequateType_appVar {n : Nat} {Γ : CCtx Tower.Head n} (p x : Fin n) {A : CTm Tower.Head n}
    (hp : Γ.lookup p = .pi A cU0) (hx : Γ.lookup x = A) :
    AdequateType objectChurchReading H Γ (.app (.var p) (.var x)) := by
  have vp : (CStatement.typing Γ (.var p) (.pi A cU0)).Valid objectChurchReading H := by
    rw [← hp]
    exact CStatement.Valid.var p
  have tp : CTyped objectChurch Γ (.var p) (.pi A cU0) := by
    rw [← hp]
    exact .var p
  have vx : (CStatement.typing Γ (.var x) A).Valid objectChurchReading H := by
    rw [← hx]
    exact CStatement.Valid.var x
  have tx : CTyped objectChurch Γ (.var x) A := by
    rw [← hx]
    exact .var x
  exact (CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts vp vx tp tx).1.adequateType
    ConvRules.objectLevels objectChurch_soundnessFacts (.sort _)

/-- **The declared type of the iterator is an adequate type.** -/
theorem adequateType_iterType : AdequateType objectChurchReading H .nil (liftTm Package.iterType) := by
  have t₀ : CIsType objectChurch .nil (liftTm Package.iterType) := ⟨_, .sort _, citerType_formed⟩
  rw [show (liftTm Package.iterType : CTm Tower.Head 0) = .pi cnum (.pi cU0 (.pi (.pi (.var 0) cU0)
    (.pi cStep (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))))))
    from rfl] at t₀ ⊢
  obtain ⟨-, t₁⟩ := CIsType.pi_parts t₀
  obtain ⟨-, t₂⟩ := CIsType.pi_parts t₁
  obtain ⟨tP, t₃⟩ := CIsType.pi_parts t₂
  obtain ⟨tSt, t₄⟩ := CIsType.pi_parts t₃
  obtain ⟨-, t₅⟩ := CIsType.pi_parts t₄
  obtain ⟨-, t₆⟩ := CIsType.pi_parts t₅
  obtain ⟨-, tSt'⟩ := CIsType.pi_parts tSt
  refine AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts t₀
    (adequateType_typeAt (.base .num) .nil) ?_
  refine AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts t₁
    (AdequateType.universe ConvRules.objectLevels objectChurch_soundnessFacts (.sort _)) ?_
  refine AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts t₂
    (AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts tP (adequateType_var 0 rfl)
      (AdequateType.universe ConvRules.objectLevels objectChurch_soundnessFacts (.sort _))) ?_
  refine AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts t₃
    (AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts tSt (adequateType_var 1 rfl)
      (AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts tSt'
        (adequateType_appVar 1 0 rfl rfl)
        ((valid_sigmaFam (H := H) 3 2 rfl rfl).1.1.adequateType ConvRules.objectLevels
          objectChurch_soundnessFacts (.sort _)))) ?_
  refine AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts t₄
    (adequateType_var 2 rfl) ?_
  refine AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts t₅
    (adequateType_appVar 2 0 rfl rfl) ?_
  exact (valid_sigmaFam (H := H) 4 3 rfl rfl).1.1.adequateType ConvRules.objectLevels
    objectChurch_soundnessFacts (.sort _)

end Types

/-! ## Closed numerals -/

section Numerals

variable {H : HeadReduction objectChurch objectRigid}

/-- The closed numeral `k`. -/
def cnumeral {n : Nat} : Nat → CTm Tower.Head n
  | 0 => czero
  | k + 1 => csuc (cnumeral k)

theorem subst_cnumeral {n m : Nat} (σ : CSub Tower.Head n m) :
    ∀ k : Nat, (cnumeral k : CTm Tower.Head n).subst σ = cnumeral k
  | 0 => rfl
  | k + 1 => by
      show CTm.app (.const sucN) ((cnumeral k : CTm Tower.Head n).subst σ) = _
      rw [subst_cnumeral σ k]
      rfl

theorem cnumeral_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    ∀ k : Nat, CTyped objectChurch Γ (cnumeral k) cnum
  | 0 => czero_typed
  | k + 1 => csuc_typed (cnumeral_typed k)

/-- **A closed numeral is adequate** at the numbers: its tokens are the tag of its
constructor and its predecessor's tokens, related by the successor clause. -/
theorem adequate_cnumeral : ∀ k : Nat,
    Adequate objectChurchReading H .nil (cnumeral k) cnum
  | 0 => by
      intro ρ _ m Δ σ σ' _ _ s hs _
      have hs' : ent Elem.zero s = true := by
        have h : (objectChurchReading.const zeroN).Mem s := hs
        rwa [objectChurchReading_zero] at h
      refine RT.closed' hs' fun q hq => ?_
      rw [List.mem_singleton.1 hq]
      exact RT.tm_zero_iff.2 ⟨CRedTy.refl ⟨_, .sort _, cnum_typed⟩, CRedTm.refl czero_typed,
        CRedTm.refl czero_typed⟩
  | k + 1 => by
      intro ρ fits m Δ σ σ' formed hσ s hs hsT
      have ih := adequate_cnumeral k
      rw [subst_cnumeral, subst_cnumeral]
      have hs' : (succI (projT natI (cinterp objectChurchReading (cnumeral k) ρ))).Mem s := by
        have h : (Ideal.app (objectChurchReading.const sucN)
            (cinterp objectChurchReading (cnumeral k) ρ)).Mem s := hs
        rwa [objectChurchReading_suc, app_sucConst objectChurchReading numNames
          objectChurchReading_num] at h
      have red : SuccRed H Δ cnum (cnumeral (k + 1)) (cnumeral (k + 1)) (cnumeral k) (cnumeral k) :=
        ⟨CRedTy.refl ⟨_, .sort _, cnum_typed⟩, CRedTm.refl (cnumeral_typed (k + 1)),
          CRedTm.refl (cnumeral_typed (k + 1)), .refl (cnumeral_typed k)⟩
      obtain ⟨v, hv, e⟩ := hs'
      refine RT.closed' e fun g hg => ?_
      rcases hv g hg with rfl | ⟨s', rfl, hs'⟩
      · exact RT.tm_succTag_iff.2 ⟨_, _, red⟩
      · refine RT.tm_argSucc_iff.2 (.inr ⟨_, _, red, fun c hc => absurd hc List.not_mem_nil,
          fun _ => ?_⟩)
        obtain ⟨w, hw, ew⟩ := hs'
        refine RT.closed' ew fun g' hg' => ?_
        have h := ih ρ fits formed hσ g' (hw g' hg').1 (by rw [cinterp_cnum]; exact (hw g' hg').2)
        rwa [subst_cnumeral, subst_cnumeral] at h

end Numerals

/-! ## The iterator at a closed numeral -/

/-- **The iterator's constant is valid** at its declared type, in every context. -/
theorem valid_iterConst {n : Nat} {Γ : CCtx Tower.Head n} :
    (CStatement.typing Γ (.const iterName) (liftTm Package.iterType).liftClosed).Valid
      objectChurchReading objectHeadReduction :=
  CStatement.Valid.constAt ConvRules.objectLevels objectChurch_soundnessFacts constAdequateAt_iter
    (objectChurch_declared (by decide) (by decide))
    ⟨AdequateType.adequate ConvRules.objectLevels objectChurch_soundnessFacts (.sort _)
      adequateType_iterType,
      AdequateType.universe ConvRules.objectLevels objectChurch_soundnessFacts (.sort _)⟩
    citerType_formed (.sort _)

/-- **Positive control: the iterator at `2` is adequate** at its type at a count, with no
hypothesis: the iterator's constant case composed with the application case. -/
theorem adequate_iterTwo :
    Adequate objectChurchReading objectHeadReduction .nil
      (.app (.const iterName) (cnumeral 2)) iterTail.liftClosed := by
  have v := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts
    (A := cnum) (B := iterTail.liftClosed)
    (by rw [← liftClosed_iterType]; exact valid_iterConst)
    ⟨adequate_cnumeral 2, adequateType_typeAt (.base .num) .nil⟩
    citer_typed' (cnumeral_typed 2)
  rw [inst0_iterTail] at v
  exact v.1

/-! ## Positive: the successor move at one -/

section SucMoveOne

/-- `add 0 1 ≡ 1`. -/
theorem addZeroOne_eq : CEqual objectChurch .nil (cadd czero (cnumeral 1)) (cnumeral 1) cnum :=
  .trans (.rootAdmitted (caddSuc_step czero czero) (caddSuc_admits czero_typed czero_typed)
      (cadd_typed czero_typed (cnumeral_typed 1))
      (csuc_typed (cadd_typed czero_typed czero_typed)))
    (.appCong (A := cnum) (B := cnum) (.refl csucConst_typed)
      (.rootAdmitted (caddZero_step czero) (caddZero_admits czero_typed)
        (cadd_typed czero_typed czero_typed) czero_typed))

/-- `refl 1 : eqAt 1`, by the equation of `eqAt` and `add 0 1 ≡ 1`. -/
theorem reflOne_typed : CTyped objectChurch .nil (.refl (cnumeral 1)) (ceqAt (cnumeral 1)) := by
  have e₁ : CEqual objectChurch .nil (ceqAt (cnumeral 1)) (.id cnum (cadd czero (cnumeral 1))
      (cnumeral 1)) cU0 :=
    .rootAdmitted (ceqAt_step _) (ceqAt_admits (cnumeral_typed 1)) (ceqAt_typed (cnumeral_typed 1))
      (cidT cnum_typed (cadd_typed czero_typed (cnumeral_typed 1)) (cnumeral_typed 1))
  have e₂ : CEqual objectChurch .nil (.id cnum (cadd czero (cnumeral 1)) (cnumeral 1))
      (.id cnum (cnumeral 1) (cnumeral 1)) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) addZeroOne_eq (.refl (cnumeral_typed 1))
  exact .conv (.reflIntro (cnumeral_typed 1)) (.symm (.trans e₁ e₂)) (.sort _)

/-- The point of the successor move at one: `suc (add 0 1)`. -/
abbrev sucPoint : CTm Tower.Head 0 := csuc (cadd czero (cnumeral 1))

/-- **The successor move at one reduces to a reflexivity**: its root step to the
eliminator, then the eliminator's root step at the path `refl 1`, at `eqAt 2`. -/
theorem sucMoveOne_reduces :
    CRedTm objectHeadReduction .nil (.app (.app (.const sucMoveName) (cnumeral 1)) (.refl (cnumeral 1)))
      (.refl sucPoint) (ceqAt (cnumeral 2)) := by
  have rδ := sucMove_teleReduces objectHeadReduction (Δ := .nil) (cnumeral 1) (cnumeral_typed 1)
    (.refl (cnumeral 1)) reflOne_typed
  have jStep := objectChurch_jStep (n := 0) (CTm.consSub (cnumeral 1) (CTm.consSub (cnumeral 1)
    (CTm.consSub (.refl sucPoint) (CTm.consSub (cSucMotive.subst (CTm.consSub (.refl (cnumeral 1))
      (CTm.consSub (cnumeral 1) fun i => .var (Fin.elim0 i)))) (CTm.consSub (cadd czero (cnumeral 1))
        (CTm.consSub cnum Fin.elim0))))))
  have tJ := (CEqual.typed ConvRules.objectLevels rδ.2 .nil).2
  have ePoint : CTypeEq objectChurch .nil (.id cnum sucPoint sucPoint) (ceqAt (cnumeral 2)) := by
    have e₁ : CEqual objectChurch .nil (ceqAt (cnumeral 2)) (.id cnum (cadd czero (cnumeral 2))
        (cnumeral 2)) cU0 :=
      .rootAdmitted (ceqAt_step _) (ceqAt_admits (cnumeral_typed 2))
        (ceqAt_typed (cnumeral_typed 2))
        (cidT cnum_typed (cadd_typed czero_typed (cnumeral_typed 2)) (cnumeral_typed 2))
    have e₂ : CEqual objectChurch .nil (cadd czero (cnumeral 2)) sucPoint cnum :=
      .rootAdmitted (caddSuc_step czero (cnumeral 1))
        (caddSuc_admits czero_typed (cnumeral_typed 1)) (cadd_typed czero_typed (cnumeral_typed 2))
        (csuc_typed (cadd_typed czero_typed (cnumeral_typed 1)))
    have e₃ : CEqual objectChurch .nil sucPoint (cnumeral 2) cnum :=
      .appCong (A := cnum) (B := cnum) (.refl csucConst_typed) addZeroOne_eq
    exact ⟨.sort Tower.zero, .sort _, .symm (.trans e₁ (.idCong (.refl cnum_typed) (.sort _) e₂
      (.symm e₃)))⟩
  have tRefl : CTyped objectChurch .nil (.refl sucPoint) (ceqAt (cnumeral 2)) :=
    CTyped.convType (.reflIntro (csuc_typed (cadd_typed czero_typed (cnumeral_typed 1)))) ePoint
  have morδ : CSubstMor objectChurch cEqAtTele .nil
      (CTm.consSub (.refl (cnumeral 1)) (CTm.consSub (cnumeral 1) fun i => .var (Fin.elim0 i))) :=
    fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact reflOne_typed
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        exact cnumeral_typed 1
  have mor : CSubstMor objectChurch cJTele .nil (CTm.consSub (cnumeral 1) (CTm.consSub (cnumeral 1)
      (CTm.consSub (.refl sucPoint) (CTm.consSub (cSucMotive.subst (CTm.consSub (.refl (cnumeral 1))
        (CTm.consSub (cnumeral 1) fun i => .var (Fin.elim0 i)))) (CTm.consSub (cadd czero (cnumeral 1))
          (CTm.consSub cnum Fin.elim0)))))) := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact cnumeral_typed 1
    refine Fin.cases ?_ (fun i => ?_) i
    · exact cnumeral_typed 1
    refine Fin.cases ?_ (fun i => ?_) i
    · exact cSucReflCase_typed.substitute morδ
    refine Fin.cases ?_ (fun i => ?_) i
    · exact cSucMotive_typed.substitute morδ
    refine Fin.cases ?_ (fun i => ?_) i
    · exact cadd_typed czero_typed (cnumeral_typed 1)
    refine Fin.cases ?_ (fun i => ?_) i
    · exact cnum_typed
    exact i.elim0
  exact rδ.trans ⟨.single (objectHeadReduction.root jStep),
    .rootAdmitted jStep (objectChurch_jAdmits mor (.symm addZeroOne_eq) (.refl (cnumeral_typed 1)))
      tJ tRefl⟩

/-- **Positive control: the successor move at one is related to itself at `eqAt 2`** at the
tag of reflexivity: it reduces to `refl (suc (add 0 1))`, whose point is equal to both
endpoints of `Id num (add 0 2) 2`. -/
theorem sucMoveOne_related :
    RT objectHeadReduction .nil true (.tag .refl) (ceqAt (cnumeral 2))
      (.app (.app (.const sucMoveName) (cnumeral 1)) (.refl (cnumeral 1)))
      (.app (.app (.const sucMoveName) (cnumeral 1)) (.refl (cnumeral 1))) := by
  have hT : CRedTy objectHeadReduction .nil (ceqAt (cnumeral 2))
      (.id cnum (cadd czero (cnumeral 2)) (cnumeral 2)) :=
    ⟨.single (objectHeadReduction.root (ceqAt_step _)), .sort Tower.zero, .sort _,
      .rootAdmitted (ceqAt_step _) (ceqAt_admits (cnumeral_typed 2))
        (ceqAt_typed (cnumeral_typed 2))
        (cidT cnum_typed (cadd_typed czero_typed (cnumeral_typed 2)) (cnumeral_typed 2))⟩
  have e₂ : CEqual objectChurch .nil sucPoint (cadd czero (cnumeral 2)) cnum :=
    .symm (.rootAdmitted (caddSuc_step czero (cnumeral 1))
      (caddSuc_admits czero_typed (cnumeral_typed 1)) (cadd_typed czero_typed (cnumeral_typed 2))
      (csuc_typed (cadd_typed czero_typed (cnumeral_typed 1))))
  have e₃ : CEqual objectChurch .nil sucPoint (cnumeral 2) cnum :=
    .appCong (A := cnum) (B := cnum) (.refl csucConst_typed) addZeroOne_eq
  exact RT.tm_reflTag_iff.2 ⟨_, _, _, _, _, hT, sucMoveOne_reduces, sucMoveOne_reduces, e₂, e₃,
    .refl (csuc_typed (cadd_typed czero_typed (cnumeral_typed 1)))⟩

end SucMoveOne

/-! ## Negative: an iteration step that does not step -/

section Broken

/-- The iterator's successor step, broken: it returns the value and its evidence and never
applies the step. -/
def brokenSucc : Ideal :=
  cinterp objectChurchReading (lamsCtx iterStepTele (.pair (.var 1) (.var 0))) Env.nil

/-- The iterator's function with the broken successor step. -/
def brokenIterRaw : Ideal :=
  Ideal.lam fun N => natRec (iterZero objectChurchReading) (fun _ r => Ideal.app brokenSucc r)
    (principal N)

/-- **The object reading with the iterator's successor step broken.** -/
def brokenReading : Reading Tower.Head :=
  ⟨objectHead, fun c => if c = iterName then
    projT (cinterp objectChurchReading (liftTm Package.iterType) Env.nil) brokenIterRaw
    else objectChurchReading.const c⟩

theorem brokenReading_iter : brokenReading.const iterName =
    projT (cinterp objectChurchReading (liftTm Package.iterType) Env.nil) brokenIterRaw := by
  show (if iterName = iterName then _ else objectChurchReading.const iterName) = _
  exact if_pos rfl

/-- The broken reading interprets the iterator's declared type as the object reading does. -/
theorem brokenReading_cinterp_iterType :
    cinterp brokenReading (liftTm Package.iterType : CTm Tower.Head 0) =
      cinterp objectChurchReading (liftTm Package.iterType) := by
  refine cinterp_congr (Rd := brokenReading) (Rd' := objectChurchReading) rfl _ fun c hc => ?_
  have hs := stagedBelow_declType .iter c hc
  have hne : c ≠ iterName := by
    rintro rfl
    exact absurd hs (by decide)
  show (if c = iterName then _ else objectChurchReading.const c) = _
  exact if_neg hne

/-- The declared type of the iterator stays adequate under the broken reading. -/
theorem brokenReading_adequateType :
    AdequateType brokenReading objectHeadReduction .nil (liftTm Package.iterType) := by
  intro ρ _ m Δ σ σ' formed hσ r hr hrU
  rw [brokenReading_cinterp_iterType] at hr
  exact adequateType_iterType ρ trivial formed ⟨hσ.1, fun i => i.elim0⟩ r hr hrU

/-! ### The token the broken reading adds -/

/-- The numeral one, as a compact element. -/
def oneEl : List Tok := Elem.succ Elem.zero

/-- The first component observed as zero. -/
def outTok : Tok := .arg .pair 0 [] (.tag .zero)

/-- The iterator's token at the count one, the carrier observed as the numbers and the value
observed as zero, whose result has its first component zero: the broken step returns the
value. -/
def badTok : Tok :=
  .fn .lam [] oneEl [.fn .lam [] Elem.nat [.fn .lam [] [] [.fn .lam [] []
    [.fn .lam [] Elem.zero [.fn .lam [] [] [outTok]]]]]]

/-- A function entry of one output observes nothing exactly when its output does not. -/
theorem ent_nil_lam1 (X : List Tok) (y : Tok) : ent [] (.fn .lam [] X [y]) = ent [] y := by
  rw [ent_fn]
  simp [fnApp, fns]

theorem outTok_nonvac : ent [] outTok = false := by
  rw [outTok, ent_arg]
  simp [args, ent_tag, hasTag]

/-- The compact type witness of the token, one entry per level. -/
def w7 : List Tok := Elem.former .sigma Elem.nat []
def w6 : List Tok := Elem.former .pi [] [([], w7)]
def w5 : List Tok := Elem.former .pi Elem.nat [(Elem.zero, w6)]
def w4 : List Tok := Elem.former .pi [] [([], w5)]
def w3 : List Tok := Elem.former .pi [] [([], w4)]
def w2 : List Tok := Elem.former .pi Elem.univ [(Elem.nat, w3)]
def w1 : List Tok := Elem.former .pi Elem.nat [(oneEl, w2)]

theorem ty_oneEl : Ty oneEl Elem.nat :=
  (Elem.ty_succ List.mem_cons_self).2 (Elem.ty_zero List.mem_cons_self)

theorem ty_nil (a : List Tok) : Ty [] a := fun _ h => absurd h List.not_mem_nil

/-- The witness is a type. -/
theorem ty_w1 : Ty w1 Elem.univ := by
  have h7 : Ty w7 Elem.univ :=
    Elem.ty_former (.inr rfl) Elem.isUniv_univ Ideal.nat_type fun p hp => absurd hp List.not_mem_nil
  have entry : ∀ {a X W : List Tok}, Ty a Elem.univ → Ty X a → Ty W Elem.univ →
      Ty (Elem.former .pi a [(X, W)]) Elem.univ := fun ha hX hW =>
    Elem.ty_former (.inl rfl) Elem.isUniv_univ ha fun p hp => by
      rw [List.mem_singleton.1 hp]
      exact ⟨hX, hW⟩
  exact entry Ideal.nat_type ty_oneEl (entry Elem.ty_univ_univ Ideal.nat_type
    (entry (ty_nil _) (ty_nil _) (entry (ty_nil _) (ty_nil _)
      (entry Ideal.nat_type (Elem.ty_zero List.mem_cons_self) (entry (ty_nil _) (ty_nil _) h7)))))

/-- A function entry is typed at a dependent function type of one family entry with its
input and an output typing it. -/
theorem tyTok_lamEntry {a X W : List Tok} {y : Tok} (hX : Ty X a) (hW : TyTok W y) :
    TyTok (Elem.former .pi a [(X, W)]) (.fn .lam [] X [y]) := by
  refine tyTok_lam.2 ⟨List.mem_cons_self, rfl, fun x hx =>
    TyTok.mono (Elem.dom_former .pi a [(X, W)]).2 (hX x hx), fun y' hy' => ?_⟩
  rw [List.mem_singleton.1 hy']
  refine TyTok.mono (Le.of_subset fun t ht => ?_) hW
  show t ∈ Elem.fam .pi (Elem.former .pi a [(X, W)]) X
  rw [Elem.fam_former]
  exact mem_stepApp.2 ⟨(X, W), List.mem_singleton_self _, Le.refl X, ht⟩

/-- The token is typed at its witness. -/
theorem tyTok_badTok : TyTok w1 badTok := by
  have t7 : TyTok w7 outTok :=
    tyTok_fst.2 ⟨List.mem_cons_self, rfl, TyTok.mono (Elem.dom_former .sigma Elem.nat []).2
      (tyTok_tag_zero.2 List.mem_cons_self)⟩
  exact tyTok_lamEntry ty_oneEl (tyTok_lamEntry Ideal.nat_type (tyTok_lamEntry (ty_nil _)
    (tyTok_lamEntry (ty_nil _) (tyTok_lamEntry (Elem.ty_zero List.mem_cons_self)
      (tyTok_lamEntry (ty_nil _) t7)))))

/-- The carrier's value: the numbers observed in the universe. -/
abbrev aVal : Ideal := projT Ideal.univIdeal (principal Elem.nat)

theorem aVal_nat : aVal.Mem (.tag .nat) :=
  Ideal.subset_closure ⟨ent_of_mem List.mem_cons_self,
    Ideal.typedAt_univ_iff.2 (Ideal.nat_type _ List.mem_cons_self)⟩

theorem aVal_zero : (projT aVal (principal Elem.zero)).Mem (.tag .zero) :=
  Ideal.subset_closure ⟨ent_of_mem List.mem_cons_self, Elem.nat,
    fun t ht => by rw [List.mem_singleton.1 ht]; exact aVal_nat, Ideal.nat_type,
    tyTok_tag_zero.2 List.mem_cons_self⟩

/-- A dependent function type of one family entry is below the denotation of a dependent
function type whose domain holds the entry's dependency and whose family at its input holds
its output. -/
theorem below_piEntry {n : Nat} {A : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {ρ : Env n}
    {a X W : List Tok} (ha : Ideal.Below a (cinterp objectChurchReading A ρ))
    (hW : Ideal.Below W (cinterp objectChurchReading B
      (Env.cons (projT (cinterp objectChurchReading A ρ) (principal X)) ρ))) :
    Ideal.Below (Elem.former .pi a [(X, W)]) (cinterp objectChurchReading (.pi A B) ρ) := by
  have hF : Ideal.Monotone fun X =>
      cinterp objectChurchReading B (Env.cons (projT (cinterp objectChurchReading A ρ) (principal X)) ρ) :=
    fun h => (cinterp_cont_cons _ _ _).mono (Ideal.projT_mono (principal_mono h))
  intro t ht
  simp only [Elem.former, List.mem_cons, List.mem_append, List.mem_map] at ht
  rcases ht with rfl | ⟨d, hd, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Ideal.mem_former_tag _ _ _
  · exact Ideal.mem_former_dom.2 (ha d hd)
  · rcases hp with rfl | hp
    · exact (Ideal.mem_former_fn hF).2 ⟨ha, hW⟩
    · exact absurd hp List.not_mem_nil

/-- The witness is below the denotation of the iterator's declared type. -/
theorem below_w1 : Ideal.Below w1 (cinterp objectChurchReading (liftTm Package.iterType) Env.nil) := by
  have h7 : ∀ ρ : Env 6, (ρ 4).Mem (.tag .nat) → Ideal.Below w7
      (cinterp objectChurchReading (.sigma (.var 4) (.app (.var 4) (.var 0)) : CTm Tower.Head 6) ρ) := by
    intro ρ hρ t ht
    simp only [w7, Elem.former, Elem.nat, List.map_cons, List.map_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact Ideal.mem_former_tag _ _ _
    · exact Ideal.mem_former_dom.2 hρ
  have bnil : ∀ (I : Ideal), Ideal.Below [] I := fun _ _ h => absurd h List.not_mem_nil
  rw [show (liftTm Package.iterType : CTm Tower.Head 0) = .pi cnum (.pi cU0 (.pi (.pi (.var 0) cU0)
    (.pi cStep (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))))))
    from rfl]
  refine below_piEntry (fun t ht => ?_) (below_piEntry (fun t ht => ?_) (below_piEntry (bnil _)
    (below_piEntry (bnil _) (below_piEntry (fun t ht => ?_) (below_piEntry (bnil _)
      (h7 _ aVal_nat))))))
  · rw [List.mem_singleton.1 ht]
    exact (show (cinterp objectChurchReading (cnum : CTm Tower.Head 0) Env.nil).Mem (.tag .nat) by
      rw [cinterp_cnum]; exact ent_of_mem List.mem_cons_self)
  · rw [List.mem_singleton.1 ht]
    exact ent_of_mem List.mem_cons_self
  · rw [List.mem_singleton.1 ht]
    exact aVal_nat

/-- The token is typed at the iterator's declared type. -/
theorem typedAt_badTok :
    TypedAt (cinterp objectChurchReading (liftTm Package.iterType) Env.nil) badTok :=
  ⟨w1, below_w1, ty_w1, tyTok_badTok⟩

/-- A function entry of one output is in the denotation of an abstraction whose body at
the entry's input holds the output. -/
theorem mem_lamEntry {n : Nat} {A : CTm Tower.Head n} {b : CTm Tower.Head (n + 1)} {ρ : Env n}
    {X : List Tok} {y : Tok}
    (hy : (cinterp objectChurchReading b
      (Env.cons (projT (cinterp objectChurchReading A ρ) (principal X)) ρ)).Mem y) :
    (cinterp objectChurchReading (.lam A b) ρ).Mem (.fn .lam [] X [y]) := by
  have hmono : Ideal.Monotone fun X =>
      cinterp objectChurchReading b (Env.cons (projT (cinterp objectChurchReading A ρ) (principal X)) ρ) :=
    fun h => (cinterp_envCont _ b).mono (Env.Le.cons (Ideal.projT_mono (principal_mono h))
      (Env.Le.refl ρ))
  exact (Ideal.mem_lam_fn hmono).2 fun y' hy' => by rw [List.mem_singleton.1 hy']; exact hy

/-- **The broken reading holds the token**: at the count one the broken step returns the
value, whose first component is observed as zero. -/
theorem brokenReading_mem_badTok : (brokenReading.const iterName).Mem badTok := by
  rw [brokenReading_iter]
  refine Ideal.subset_closure ⟨?_, typedAt_badTok⟩
  have hmono : Ideal.Monotone fun N => natRec (iterZero objectChurchReading)
      (fun _ r => Ideal.app brokenSucc r) (principal N) := fun h =>
    (Ideal.cont_natRec (cont₂_constStep _)).mono (principal_mono h)
  refine (Ideal.mem_lam_fn hmono).2 fun y hy => ?_
  rw [List.mem_singleton.1 hy]
  refine Ideal.natRecApprox_le_natRec 2 _ _ ?_
  have hsucc : (principal oneEl).Mem (.tag .succ) := ent_of_mem List.mem_cons_self
  rw [natRecApprox]
  refine Ideal.le_join_right _ _ _ ?_
  rw [Ideal.whenTag_of_mem hsucc]
  show (Ideal.app brokenSucc _).Mem _
  have e : brokenSucc = Ideal.clam (cinterp objectChurchReading iterTail Env.nil) fun z =>
      cinterp objectChurchReading ((iterParams 1).lams (.pair (.var 1) (.var 0))) (Env.cons z Env.nil) :=
    rfl
  rw [e, Ideal.app_clam (cinterp_cont_cons _ _ _)]
  refine mem_lamEntry (mem_lamEntry (mem_lamEntry (mem_lamEntry (mem_lamEntry ?_))))
  exact Ideal.subset_closure (.inl ⟨.tag .zero, rfl, aVal_zero⟩)

/-! ### The relation refutes the token -/

/-- The context of the refutation: a family on the numbers, a step for it, and an evidence of
the family at zero. -/
abbrev brokenCtx : CCtx Tower.Head 3 :=
  .snoc (.snoc (.snoc .nil (.pi cnum cU0))
    (.pi cnum (.pi (.app (.var 1) (.var 0)) (.sigma cnum (.app (.var 3) (.var 0))))))
    (.app (.var 1) czero)

theorem brokenCtx_formed : CCtxFormed objectChurch brokenCtx := by
  refine .snoc (.snoc (.snoc .nil ⟨.sort (.succ Tower.zero), .sort _,
    cpiT (craise cnum_typed) cU0_typed⟩) ⟨.sort Tower.zero, .sort _, ?_⟩) ⟨.sort Tower.zero, .sort _, ?_⟩
  · exact cpiT cnum_typed (cpiT (.appElim (B := cU0) (.var 1) (.var 0))
      (csigmaT cnum_typed (.appElim (B := cU0) (.var 3) (.var 0))))
  · exact .appElim (B := cU0) (.var 1) czero_typed

/-- The function clause at a function entry of one output that observes something. -/
theorem RT.appOut {n : Nat} {Γ : CCtx Tower.Head n} {X : List Tok} {y : Tok}
    {T D M M' N N' : CTm Tower.Head n} {E : CTm Tower.Head (n + 1)}
    (h : RT objectHeadReduction Γ true (.fn .lam [] X [y]) T M M')
    (hT : CRedTy objectHeadReduction Γ T (.pi D E)) (hNN : CEqual objectChurch Γ N N' D)
    (hN : ∀ x ∈ X, RT objectHeadReduction Γ true x D N N') (hy : ent [] y = false) :
    RT objectHeadReduction Γ true y (CTm.inst0 N E) (.app M N) (.app M N') := by
  rcases RT.tm_lam_iff.1 h with hvac | hcl
  · rw [vacuous_out hvac List.mem_cons_self] at hy
    exact absurd hy (by decide)
  · exact ((hcl D E hT).1 N N' hNN hN y List.mem_cons_self).1

/-- The substitution of the refutation's successor equation: the evidence, zero, the step,
the family, the numbers and the recursive value at zero. -/
abbrev brokenSub : CSub Tower.Head 6 3 :=
  CTm.consSub (.var 0) (CTm.consSub czero (CTm.consSub (.var 1) (CTm.consSub (.var 2)
    (CTm.consSub cnum (CTm.consSub (.app (.const iterName) czero) fun i => .var (Fin.elim0 i))))))

/-- **Negative control: the broken iteration step is not adequate.** Under the reading whose
successor step returns the value without applying the step, the iterator's constant is not
related to itself at its declared type, although every premise of its adequacy holds: at the
count one, the numbers, a family, a step, zero and an evidence, the reading's token says the
result's first component is zero, while the iterator applies the step, so the first
component reduces to the step's first component at zero, a normal form that is not zero. -/
theorem brokenReading_not_constAdequate :
    ¬ ConstAdequateAt brokenReading objectHeadReduction iterName := by
  intro h
  have typed : TypedAt (cinterp brokenReading (liftTm Package.iterType) Env.nil) badTok := by
    rw [brokenReading_cinterp_iterType]
    exact typedAt_badTok
  have hrel := h (objectChurch_declared (T := Package.iterType) (by decide) (by decide)) (.sort _)
    citerType_formed brokenReading_adequateType brokenCtx_formed badTok brokenReading_mem_badTok typed
  rw [liftClosed_iterType] at hrel
  -- the applications and their types
  have t₀ : CTyped objectChurch brokenCtx (.const iterName) (.pi cnum iterTail.liftClosed) :=
    citer_typed'
  have t₁ := CDerivable.appElim t₀ (cnumeral_typed 1)
  have t₂ := CDerivable.appElim t₁ cnum_typed
  have t₃ := CDerivable.appElim t₂ (CDerivable.var 2)
  have t₄ := CDerivable.appElim t₃ (CDerivable.var 1)
  have t₅ := CDerivable.appElim t₄ czero_typed
  have t₆ := CDerivable.appElim t₅ (CDerivable.var 0)
  have ty : ∀ {T t : CTm Tower.Head 3}, CTyped objectChurch brokenCtx t T →
      CRedTy objectHeadReduction brokenCtx T T := fun tt =>
    CRedTy.refl (CTyped.isType ConvRules.objectLevels tt brokenCtx_formed)
  have numRed : CRedTy objectHeadReduction brokenCtx (cnum : CTm Tower.Head 3) cnum := ty czero_typed
  -- the arguments, related as far as the token's inputs observe
  have succRed : SuccRed objectHeadReduction brokenCtx cnum (cnumeral 1) (cnumeral 1) czero czero :=
    ⟨numRed, CRedTm.refl (cnumeral_typed 1), CRedTm.refl (cnumeral_typed 1), .refl czero_typed⟩
  have zeroRed : ZeroRed objectHeadReduction brokenCtx cnum czero czero :=
    ⟨numRed, CRedTm.refl czero_typed, CRedTm.refl czero_typed⟩
  have hOne : ∀ x ∈ oneEl, RT objectHeadReduction brokenCtx true x cnum (cnumeral 1) (cnumeral 1) := by
    intro x hx
    simp only [oneEl, Elem.succ, Elem.zero, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact RT.tm_succTag_iff.2 ⟨_, _, succRed⟩
    · exact RT.tm_argSucc_iff.2 (.inr ⟨_, _, succRed, fun c hc => absurd hc List.not_mem_nil,
        fun _ => RT.tm_zero_iff.2 zeroRed⟩)
  have hNum : ∀ x ∈ Elem.nat, RT objectHeadReduction brokenCtx true x cU0 cnum cnum := by
    intro x hx
    rw [List.mem_singleton.1 hx]
    exact RT.ofType rfl (.sort Tower.zero)
      (CRedTy.refl (CIsType.head_of_universe ConvRules.objectLevels (.sort _)))
      (RT.ty_nat_iff.2 ⟨numRed, numRed⟩)
  have hZero : ∀ x ∈ Elem.zero, RT objectHeadReduction brokenCtx true x cnum czero czero := by
    intro x hx
    rw [List.mem_singleton.1 hx]
    exact RT.tm_zero_iff.2 zeroRed
  have hNil : ∀ {D N : CTm Tower.Head 3}, ∀ x ∈ ([] : List Tok),
      RT objectHeadReduction brokenCtx true x D N N := fun _ hx => absurd hx List.not_mem_nil
  -- the function clauses, one argument at a time
  have r₁ := RT.appOut hrel (ty t₀) (.refl (cnumeral_typed 1)) hOne
    (by simp only [ent_nil_lam1, outTok_nonvac])
  have r₂ := RT.appOut r₁ (ty t₁) (.refl cnum_typed) hNum (by simp only [ent_nil_lam1, outTok_nonvac])
  have r₃ := RT.appOut r₂ (ty t₂) (.refl (CDerivable.var 2)) hNil
    (by simp only [ent_nil_lam1, outTok_nonvac])
  have r₄ := RT.appOut r₃ (ty t₃) (.refl (CDerivable.var 1)) hNil
    (by simp only [ent_nil_lam1, outTok_nonvac])
  have r₅ := RT.appOut r₄ (ty t₄) (.refl czero_typed) hZero
    (by simp only [ent_nil_lam1, outTok_nonvac])
  have r₆ := RT.appOut r₅ (ty t₅) (.refl (CDerivable.var 0)) hNil outTok_nonvac
  -- the first component is related to zero, so it reduces to zero
  rcases RT.tm_argPair_iff.1 r₆ with hvac | hcl
  · exact Bool.false_ne_true (outTok_nonvac.symm.trans hvac)
  obtain ⟨-, hz, -⟩ := RT.tm_zero_iff.1 ((hcl _ _ (ty t₆)).2.2.1 rfl)
  -- but it reduces, by the successor equation, β and the zero equation, to the step's value
  have s₁ := objectHeadReduction.root (iterSuc_step (m := 3) czero cnum (.var 2) (.var 1) czero (.var 0))
  have s₂ := objectHeadReduction.beta
    ((.sigma (.var 4) (.app (.var 4) (.var 0)) : CTm Tower.Head 6).subst brokenSub)
    ((.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 3)) (.fst (.var 0)))
      (.snd (.var 0)) : CTm Tower.Head 7).subst (CTm.liftSub brokenSub))
    ((.app (.app (.var 2) (.var 1)) (.var 0) : CTm Tower.Head 6).subst brokenSub)
  have s₃ := objectHeadReduction.root (iterZero_step (m := 3) cnum (.var 2) (.var 1)
    (.fst (.app (.app (.var 1) czero) (.var 0))) (.snd (.app (.app (.var 1) czero) (.var 0))))
  have red : Relation.ReflTransGen objectHeadReduction.step
      (.fst (CTm.appSpine (.const iterName) [cnumeral 1, cnum, .var 2, .var 1, czero, .var 0]))
      (.fst (.app (.app (.var 1) czero) (.var 0)) : CTm Tower.Head 3) :=
    (((Relation.ReflTransGen.single (objectHeadReduction.fst s₁)).tail
      (objectHeadReduction.fst s₂)).tail (objectHeadReduction.fst s₃)).tail
      (objectHeadReduction.fstPair _ _)
  have normal : objectHeadReduction.Normal (.fst (.app (.app (.var 1) czero) (.var 0)) :
      CTm Tower.Head 3) := fun u =>
    CWhStepR.not_of_whnf ((Neutral.fst (Neutral.app (Neutral.app (Neutral.var 1)))).whnf objectShape) u
  have e := objectHeadReduction.nf_unique hz.1 red objectHeadReduction.normal_zero normal
  cases e

end Broken

end ConstantControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
