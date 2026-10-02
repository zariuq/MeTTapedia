import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Structural
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction

/-!
# Types, formed contexts and syntactic validity of the annotated judgment

Annotated types are terms of a universe, equality of types is equality at some
universe, and a formed context has a type at every entry. Context conversion
replaces the last entry by an equal type, or by a type usable at it.

**Syntactic validity** (`CDerivable.presupposed`): in a formed context, the type
of a typed term is a type, both sides of an equality are typed at its type, and
both sides of a subtyping statement are types, for every rule package whose
universes have a level model. It is the annotated form of
`Derivable.presupposed`; the abstraction rules give their right side's typing
through context conversion along the equality of the two domains.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (LevelModel HeadSame)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {R : Rules Head}

/-! ## Types -/

/-- `A` is a type: a term of some universe. -/
def CIsType (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (A : CTm Head n) : Prop :=
  ∃ u, R.isUniverse u ∧ CTyped P Γ A (.head u)

/-- Equality of types: equality at some universe. -/
def CTypeEq (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (A B : CTm Head n) : Prop :=
  ∃ u, R.isUniverse u ∧ CEqual P Γ A B (.head u)

section Types

variable {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n}

theorem CTypeEq.symm {A B : CTm Head n} (equal : CTypeEq P Γ A B) : CTypeEq P Γ B A := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, .symm e⟩

theorem CTypeEq.trans (levels : LevelModel R L) {A B C : CTm Head n}
    (first : CTypeEq P Γ A B) (second : CTypeEq P Γ B C) : CTypeEq P Γ A C := by
  obtain ⟨u, hu, e₁⟩ := first
  obtain ⟨v, hv, e₂⟩ := second
  obtain ⟨w, join⟩ := levels.join_exists hu hv
  obtain ⟨uw, vw⟩ := levels.join_upper join
  exact ⟨w, (levels.join_level join).1, .trans (.cumulEq e₁ uw) (.cumulEq e₂ vw)⟩

theorem CIsType.refl {A : CTm Head n} (formed : CIsType P Γ A) : CTypeEq P Γ A A := by
  obtain ⟨u, hu, t⟩ := formed
  exact ⟨u, hu, .refl t⟩

theorem CTyped.convType {t A B : CTm Head n} (typing : CTyped P Γ t A)
    (equal : CTypeEq P Γ A B) : CTyped P Γ t B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .conv typing e hu

theorem CEqual.convType {a b A B : CTm Head n} (equality : CEqual P Γ a b A)
    (equal : CTypeEq P Γ A B) : CEqual P Γ a b B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .convEq equality e hu

/-- Types equal at a universe are usable at each other. -/
theorem CTypeEq.below {A B : CTm Head n} (equal : CTypeEq P Γ A B) : CBelow P Γ A B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .subEqual e hu

/-- A type is usable at itself. -/
theorem CIsType.below_refl {A : CTm Head n} (type : CIsType P Γ A) : CBelow P Γ A A :=
  type.refl.below

/-- A chain of conversions and subtyping steps that ends in a type is one
subtyping statement. -/
theorem CTypeLe.toBelow {X Y : CTm Head n} (le : CTypeLe P Γ X Y) (typeY : CIsType P Γ Y) :
    CBelow P Γ X Y := by
  induction le with
  | refl => exact typeY.below_refl
  | conv e hu _ ih => exact .subTrans (.subEqual e hu) (ih typeY)
  | sub le _ ih => exact .subTrans le (ih typeY)

theorem CTypeEq.rename {m : Nat} {Δ : CCtx Head m} {ρ : Ren n m} {A B : CTm Head n}
    (equal : CTypeEq P Γ A B) (c : CCtxRen Γ Δ ρ) : CTypeEq P Δ (A.rename ρ) (B.rename ρ) := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, e.rename c⟩

theorem CIsType.rename {m : Nat} {Δ : CCtx Head m} {ρ : Ren n m} {A : CTm Head n}
    (formed : CIsType P Γ A) (c : CCtxRen Γ Δ ρ) : CIsType P Δ (A.rename ρ) := by
  obtain ⟨u, hu, t⟩ := formed
  exact ⟨u, hu, t.rename c⟩

theorem CIsType.pi_parts {A : CTm Head n} {B : CTm Head (n + 1)}
    (formed : CIsType P Γ (.pi A B)) : CIsType P Γ A ∧ CIsType P (.snoc Γ A) B := by
  obtain ⟨_, _, typing⟩ := formed
  obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := typing.generation
  exact ⟨⟨u, hu, tA⟩, v, hv, tB⟩

theorem CIsType.sigma_parts {A : CTm Head n} {B : CTm Head (n + 1)}
    (formed : CIsType P Γ (.sigma A B)) : CIsType P Γ A ∧ CIsType P (.snoc Γ A) B := by
  obtain ⟨_, _, typing⟩ := formed
  obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := typing.generation
  exact ⟨⟨u, hu, tA⟩, v, hv, tB⟩

/-- Instantiating equal families at one argument. -/
theorem CTypeEq.instantiate {A a : CTm Head n} {B B' : CTm Head (n + 1)}
    (equal : CTypeEq P (.snoc Γ A) B B') (typing : CTyped P Γ a A) :
    CTypeEq P Γ (CTm.inst0 a B) (CTm.inst0 a B') := by
  obtain ⟨v, hv, e⟩ := equal
  exact ⟨v, hv, e.instantiate typing⟩

/-- Instantiating one family at equal arguments. -/
theorem CIsType.instantiateEq {A a a' : CTm Head n} {B : CTm Head (n + 1)}
    (family : CIsType P (.snoc Γ A) B) (typing : CTyped P Γ a A) (equal : CEqual P Γ a a' A) :
    CTypeEq P Γ (CTm.inst0 a B) (CTm.inst0 a' B) := by
  obtain ⟨v, hv, tB⟩ := family
  exact ⟨v, hv, tB.instantiateEq typing equal⟩

end Types

/-! ## Formed contexts -/

/-- Every entry is a type. -/
inductive CCtxFormed (P : ChurchRules R) : {n : Nat} → CCtx Head n → Prop where
  | nil : CCtxFormed P .nil
  | snoc {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} :
      CCtxFormed P Γ → CIsType P Γ A → CCtxFormed P (.snoc Γ A)

theorem CCtxFormed.lookup {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n}
    (formed : CCtxFormed P Γ) (i : Fin n) : CIsType P Γ (Γ.lookup i) := by
  induction formed with
  | nil => exact i.elim0
  | @snoc n Γ A _ typeA ih =>
      refine Fin.cases ?_ ?_ i
      · exact typeA.rename (CCtxRen.wk Γ A)
      · intro j
        exact (ih j).rename (CCtxRen.wk Γ A)

/-! ## Context conversion -/

section ContextConversion

variable {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n}

theorem CSubstMor.ctxConv (equal : CTypeEq P Γ A' A) :
    CSubstMor P (.snoc Γ A) (.snoc Γ A') CTm.ids := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · show CTyped P (.snoc Γ A') (.var 0) ((A.rename wk).subst CTm.ids)
    rw [CTm.subst_ids]
    exact CTyped.convType (.var 0) (equal.rename (CCtxRen.wk Γ A'))
  · show CTyped P (.snoc Γ A') (.var j.succ) (((Γ.lookup j).rename wk).subst CTm.ids)
    rw [CTm.subst_ids]
    exact .var j.succ

theorem CSubstMor.ctxBelow (le : CBelow P Γ A' A) :
    CSubstMor P (.snoc Γ A) (.snoc Γ A') CTm.ids := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · show CTyped P (.snoc Γ A') (.var 0) ((A.rename wk).subst CTm.ids)
    rw [CTm.subst_ids]
    exact .sub (.var 0) (le.rename (CCtxRen.wk Γ A'))
  · show CTyped P (.snoc Γ A') (.var j.succ) (((Γ.lookup j).rename wk).subst CTm.ids)
    rw [CTm.subst_ids]
    exact .var j.succ

/-- Changing the last context entry to an equal type. -/
theorem CTyped.ctxConv {t T : CTm Head (n + 1)} (typing : CTyped P (.snoc Γ A) t T)
    (equal : CTypeEq P Γ A A') : CTyped P (.snoc Γ A') t T := by
  simpa using typing.substitute (CSubstMor.ctxConv equal.symm)

theorem CEqual.ctxConv {a b T : CTm Head (n + 1)} (equality : CEqual P (.snoc Γ A) a b T)
    (equal : CTypeEq P Γ A A') : CEqual P (.snoc Γ A') a b T := by
  simpa using equality.substitute (CSubstMor.ctxConv equal.symm)

theorem CBelow.ctxConv {B C : CTm Head (n + 1)} (le : CBelow P (.snoc Γ A) B C)
    (equal : CTypeEq P Γ A A') : CBelow P (.snoc Γ A') B C := by
  simpa using le.substitute (CSubstMor.ctxConv equal.symm)

theorem CTypeEq.ctxConv {B C : CTm Head (n + 1)} (equality : CTypeEq P (.snoc Γ A) B C)
    (equal : CTypeEq P Γ A A') : CTypeEq P (.snoc Γ A') B C := by
  obtain ⟨u, hu, e⟩ := equality
  exact ⟨u, hu, e.ctxConv equal⟩

theorem CIsType.ctxConv {B : CTm Head (n + 1)} (formed : CIsType P (.snoc Γ A) B)
    (equal : CTypeEq P Γ A A') : CIsType P (.snoc Γ A') B := by
  obtain ⟨u, hu, t⟩ := formed
  exact ⟨u, hu, t.ctxConv equal⟩

/-- Changing the last context entry to a type usable at it. -/
theorem CTyped.ctxBelow {t T : CTm Head (n + 1)} (typing : CTyped P (.snoc Γ A) t T)
    (le : CBelow P Γ A' A) : CTyped P (.snoc Γ A') t T := by
  simpa using typing.substitute (CSubstMor.ctxBelow le)

theorem CBelow.ctxBelow {B C : CTm Head (n + 1)} (le : CBelow P (.snoc Γ A) B C)
    (below : CBelow P Γ A' A) : CBelow P (.snoc Γ A') B C := by
  simpa using le.substitute (CSubstMor.ctxBelow below)

end ContextConversion

/-! ## Syntactic validity -/

/-- What a statement presupposes in a formed context. -/
abbrev CPresupposed (P : ChurchRules R) : CStatement Head → Prop
  | .typing Γ _ A => CCtxFormed P Γ → CIsType P Γ A
  | .equality Γ a b A => CCtxFormed P Γ → CTyped P Γ a A ∧ CTyped P Γ b A ∧ CIsType P Γ A
  | .sub Γ A B => CCtxFormed P Γ → CIsType P Γ A ∧ CIsType P Γ B

/-- **Syntactic validity** of the annotated judgment. -/
theorem CDerivable.presupposed {P : ChurchRules R} (levels : LevelModel R L)
    {statement : CStatement Head} (derivation : CDerivable P statement) :
    CPresupposed P statement := by
  have universeType : ∀ {n : Nat} {Γ : CCtx Head n} {u : Head}, R.isUniverse u →
      CIsType P Γ (.head u) := fun hu => by
    obtain ⟨v, hv, typing, _⟩ := levels.successor hu
    exact ⟨v, hv, .headType typing⟩
  induction derivation with
  | headType head => exact fun _ => universeType (levels.ground_typing head)
  | var i => exact fun formed => formed.lookup i
  | const _ typedType hu _ =>
      exact fun _ => ⟨_, hu, CTyped.rename (ρ := Fin.elim0) typedType (fun i => i.elim0)⟩
  | piForm _ _ _ _ join => exact fun _ => universeType (levels.join_level join).1
  | sigmaForm _ _ _ _ join => exact fun _ => universeType (levels.join_level join).1
  | lamIntro _ _ tPi hu _ _ _ _ => exact fun _ => ⟨_, hu, tPi⟩
  | appElim _ ta ihF _ =>
      intro formed
      obtain ⟨_, v, hv, tB⟩ := CIsType.pi_parts (ihF formed)
      exact ⟨v, hv, CTyped.instantiate tB ta⟩
  | pairIntro tS hu _ _ _ _ _ => exact fun _ => ⟨_, hu, tS⟩
  | fstElim _ ihP => exact fun formed => (CIsType.sigma_parts (ihP formed)).1
  | sndElim tp ihP =>
      intro formed
      obtain ⟨_, v, hv, tB⟩ := CIsType.sigma_parts (ihP formed)
      exact ⟨v, hv, CTyped.instantiate tB (.fstElim tp)⟩
  | idForm _ hu _ _ _ _ _ => exact fun _ => universeType hu
  | reflIntro ta ihA =>
      intro formed
      obtain ⟨u, hu, tA⟩ := ihA formed
      exact ⟨u, hu, .idForm tA hu ta ta⟩
  | sub _ _ _ ihLe => exact fun formed => (ihLe formed).2
  | conv _ _ hu _ ihE => exact fun formed => ⟨_, hu, (ihE formed).2.1⟩
  | refl ta ihA => exact fun formed => ⟨ta, ta, ihA formed⟩
  | symm _ ih =>
      intro formed
      obtain ⟨ta, tb, tA⟩ := ih formed
      exact ⟨tb, ta, tA⟩
  | trans _ _ ih₁ ih₂ =>
      exact fun formed => ⟨(ih₁ formed).1, (ih₂ formed).2.1, (ih₁ formed).2.2⟩
  | convEq _ e hu ih ihE =>
      intro formed
      obtain ⟨ta, tb, _⟩ := ih formed
      exact ⟨.conv ta e hu, .conv tb e hu, ⟨_, hu, (ihE formed).2.1⟩⟩
  | subEq _ le ih ihLe =>
      intro formed
      obtain ⟨ta, tb, _⟩ := ih formed
      exact ⟨.sub ta le, .sub tb le, (ihLe formed).2⟩
  | headEq _ typing typing' ih _ => exact fun formed => ⟨typing, typing', ih formed⟩
  | piCong eA hu _ hv join ihA ihB =>
      intro formed
      obtain ⟨tA, tA', _⟩ := ihA formed
      obtain ⟨tB, tB', _⟩ := ihB (.snoc formed ⟨_, hu, tA⟩)
      exact ⟨.piForm tA hu tB hv join, .piForm tA' hu (CTyped.ctxConv tB' ⟨_, hu, eA⟩) hv join,
        universeType (levels.join_level join).1⟩
  | sigmaCong eA hu _ hv join ihA ihB =>
      intro formed
      obtain ⟨tA, tA', _⟩ := ihA formed
      obtain ⟨tB, tB', _⟩ := ihB (.snoc formed ⟨_, hu, tA⟩)
      exact ⟨.sigmaForm tA hu tB hv join,
        .sigmaForm tA' hu (CTyped.ctxConv tB' ⟨_, hu, eA⟩) hv join,
        universeType (levels.join_level join).1⟩
  | idCong eA hu _ _ ihA iha ihb =>
      intro formed
      obtain ⟨tA, tA', _⟩ := ihA formed
      obtain ⟨ta, ta', _⟩ := iha formed
      obtain ⟨tb, tb', _⟩ := ihb formed
      exact ⟨.idForm tA hu ta tb, .idForm tA' hu (.conv ta' eA hu) (.conv tb' eA hu),
        universeType hu⟩
  | lamCong eA hw tPi hu _ ihA _ ihBody =>
      intro formed
      obtain ⟨tA, tA', _⟩ := ihA formed
      obtain ⟨_, ⟨v, hv, tB⟩⟩ := CIsType.pi_parts ⟨_, hu, tPi⟩
      obtain ⟨tb, tb', _⟩ := ihBody (.snoc formed ⟨_, hw, tA⟩)
      have eAA' : CTypeEq P _ _ _ := ⟨_, hw, eA⟩
      have tB' := CTyped.ctxConv tB eAA'
      obtain ⟨z, join⟩ := levels.join_exists hw hv
      have hz := (levels.join_level join).1
      have right : CTyped P _ (.lam _ _) (.pi _ _) :=
        .lamIntro tA' hw (.piForm tA' hw tB' hv join) hz (CTyped.ctxConv tb' eAA')
      exact ⟨.lamIntro tA hw tPi hu tb, .conv right (.piCong (.symm eA) hw (.refl tB') hv join) hz,
        ⟨_, hu, tPi⟩⟩
  | appCong _ ea ihF ihA =>
      intro formed
      obtain ⟨tf, tg, typePi⟩ := ihF formed
      obtain ⟨ta, tb, _⟩ := ihA formed
      obtain ⟨_, family⟩ := CIsType.pi_parts typePi
      obtain ⟨v, hv, tB⟩ := family
      exact ⟨.appElim tf ta,
        CTyped.convType (.appElim tg tb) (CIsType.instantiateEq ⟨v, hv, tB⟩ ta ea).symm,
        ⟨v, hv, CTyped.instantiate tB ta⟩⟩
  | pairCong tS hu ea _ _ iha ihb =>
      intro formed
      obtain ⟨ta, ta', _⟩ := iha formed
      obtain ⟨tb, tb', _⟩ := ihb formed
      obtain ⟨_, family⟩ := CIsType.sigma_parts ⟨_, hu, tS⟩
      exact ⟨.pairIntro tS hu ta tb,
        .pairIntro tS hu ta' (CTyped.convType tb' (CIsType.instantiateEq family ta ea)),
        ⟨_, hu, tS⟩⟩
  | fstCong _ ih =>
      intro formed
      obtain ⟨tp, tq, typeSigma⟩ := ih formed
      exact ⟨.fstElim tp, .fstElim tq, (CIsType.sigma_parts typeSigma).1⟩
  | sndCong e ih =>
      intro formed
      obtain ⟨tp, tq, typeSigma⟩ := ih formed
      obtain ⟨_, family⟩ := CIsType.sigma_parts typeSigma
      obtain ⟨v, hv, tB⟩ := family
      exact ⟨.sndElim tp, CTyped.convType (.sndElim tq)
          (CIsType.instantiateEq ⟨v, hv, tB⟩ (.fstElim tp) (.fstCong e)).symm,
        ⟨v, hv, CTyped.instantiate tB (.fstElim tp)⟩⟩
  | reflCong e ih =>
      intro formed
      obtain ⟨ta, tb, u, hu, tA⟩ := ih formed
      exact ⟨.reflIntro ta,
        .conv (.reflIntro tb) (.idCong (.refl tA) hu (.symm e) (.symm e)) hu,
        ⟨u, hu, .idForm tA hu ta ta⟩⟩
  | betaPi tPi hu tb ta _ _ _ =>
      intro _
      obtain ⟨⟨w, hw, tA⟩, v, hv, family⟩ := CIsType.pi_parts ⟨_, hu, tPi⟩
      exact ⟨.appElim (.lamIntro tA hw tPi hu tb) ta, CTyped.instantiate tb ta,
        ⟨v, hv, CTyped.instantiate family ta⟩⟩
  | betaFst tS hu ta tb _ _ _ =>
      intro _
      exact ⟨.fstElim (.pairIntro tS hu ta tb), ta, (CIsType.sigma_parts ⟨_, hu, tS⟩).1⟩
  | betaSnd tS hu ta tb _ _ _ =>
      intro _
      obtain ⟨_, family⟩ := CIsType.sigma_parts ⟨_, hu, tS⟩
      obtain ⟨v, hv, tB⟩ := family
      exact ⟨CTyped.convType (.sndElim (.pairIntro tS hu ta tb))
          (CIsType.instantiateEq ⟨v, hv, tB⟩ (.fstElim (.pairIntro tS hu ta tb))
            (.betaFst tS hu ta tb)),
        tb, ⟨v, hv, CTyped.instantiate tB ta⟩⟩
  | root _ _ _ tl tr _ ihL _ => exact fun formed => ⟨tl, tr, ihL formed⟩
  | etaPi tf tg _ ihF _ _ => exact fun formed => ⟨tf, tg, ihF formed⟩
  | etaSigma tp tq _ _ ihP _ _ _ => exact fun formed => ⟨tp, tq, ihP formed⟩
  | subEqual _ hu ih =>
      intro formed
      obtain ⟨tA, tB, _⟩ := ih formed
      exact ⟨⟨_, hu, tA⟩, ⟨_, hu, tB⟩⟩
  | subUniv c =>
      obtain ⟨hu, hv, _⟩ := levels.cumulative_universe c
      exact fun _ => ⟨universeType hu, universeType hv⟩
  | subPi tPi hu tPi' hu' _ _ _ _ _ _ _ => exact fun _ => ⟨⟨_, hu, tPi⟩, ⟨_, hu', tPi'⟩⟩
  | subSigma tS hu tS' hu' _ _ _ _ _ _ => exact fun _ => ⟨⟨_, hu, tS⟩, ⟨_, hu', tS'⟩⟩
  | subTrans _ _ ih₁ ih₂ => exact fun formed => ⟨(ih₁ formed).1, (ih₂ formed).2⟩

section Presupposed

variable {P : ChurchRules R} (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
include levels

theorem CTyped.isType {t T : CTm Head n} (typing : CTyped P Γ t T) (formed : CCtxFormed P Γ) :
    CIsType P Γ T :=
  CDerivable.presupposed levels typing formed

theorem CEqual.typed {a b A : CTm Head n} (equal : CEqual P Γ a b A) (formed : CCtxFormed P Γ) :
    CTyped P Γ a A ∧ CTyped P Γ b A :=
  let ⟨ta, tb, _⟩ := CDerivable.presupposed levels equal formed
  ⟨ta, tb⟩

theorem CIsType.head_of_universe {u : Head} (hu : R.isUniverse u) : CIsType P Γ (.head u) := by
  obtain ⟨v, hv, typing, _⟩ := levels.successor hu
  exact ⟨v, hv, .headType typing⟩

theorem CTypeEq.isType {A B : CTm Head n} (equal : CTypeEq P Γ A B) (formed : CCtxFormed P Γ) :
    CIsType P Γ A ∧ CIsType P Γ B := by
  obtain ⟨u, hu, e⟩ := equal
  obtain ⟨tA, tB⟩ := CEqual.typed levels e formed
  exact ⟨⟨u, hu, tA⟩, ⟨u, hu, tB⟩⟩

theorem CBelow.isTypes {A B : CTm Head n} (le : CBelow P Γ A B) (formed : CCtxFormed P Γ) :
    CIsType P Γ A ∧ CIsType P Γ B :=
  CDerivable.presupposed levels le formed

end Presupposed

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
