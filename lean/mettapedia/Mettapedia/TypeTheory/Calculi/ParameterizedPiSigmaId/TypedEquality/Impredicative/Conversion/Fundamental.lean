import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Spines

/-!
# The fundamental lemma of the conversion model

Every derivable statement of an object package is valid in the conversion model
when the package is sound for it (`TypedSoundN`): its universe rules hold on
both sides of the model, each of its root steps preserves meaning, and each of
its constants is a valid term of its declared type. Along with each judgment
the lemma carries the valid parts of its subjects and types written as type
formers.

Validity is two-sided. A valid term's instances under related valuations are
related values of the instance of its type, and its realizer instances are
related by the equality candidate of its value at the realizer instance of the
type; a valid equality relates the two sides' instances in the same way, and
a valid inclusion includes relations and evaluated candidates. So the lemma
proves on the realizer side that typed terms are related by the candidates of
their values, and in particular by the generic equality of the realizer side.

## Root steps read with their typing

A root step preserves meaning in one of two ways:

* semantically (`RootSemanticN`): its two sides are validly equal wherever each
  is a valid term of one type;
* at its typed instances (`TypedRootN`): its two sides are validly equal
  wherever each is a valid term of one type and the redex has the typing facts
  of a spine of a declared constant (`SpineFactsN`).

Along with each typing the lemma carries the spine facts of its subject, and
the fact that a head's type lies structurally above a universe
(`HeadFactsN`), which the realizer side of head equality needs; along with each
inclusion its structural form (`ValidLeStructN`).

The untyped reading of soundness, in which every root step must preserve meaning
semantically (`SoundN`), is kept as a definition; it implies soundness
(`SoundN.typed`).

## Consequences

At the daimon valuation, with the identity on the realizer side, the realizer
instances of a typed term, an equality or a type equality are the terms
themselves. So in a formed context of a sound package:

* derivably equal terms are related by the generic equality of the realizer
  side (`Equal.escapeN`), and so are derivably equal types (`TypeEq.escapeN`);
* a typed term is related to itself by the candidate of its evaluated value at
  its own type (`Typed.shapeN`): the candidate records the weak-head shape.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization (WhRed CtxFormed IsType TypeEq)
open UniverseLevel (LevelOrder)
open Consistency (World)

variable {Head L : Type} [LevelOrder L] {M : NModel Head L}

variable (M) in
/-- What a statement means in the conversion model, with the valid parts of its
subjects and types. -/
def StatementValidN : Statement Head → Prop
  | .typing Γ t A => ValidCtxNN M Γ → ValidTmN M Γ t A ∧ StructuredN M Γ t ∧ StructuredN M Γ A
  | .equality Γ a b A => ValidCtxNN M Γ →
      ValidEqN M Γ a b A ∧ StructuredN M Γ a ∧ StructuredN M Γ b ∧ StructuredN M Γ A
  | .sub Γ A B => ValidCtxNN M Γ → ValidLeN M Γ A B ∧ StructuredN M Γ A ∧ StructuredN M Γ B

/-! ## Soundness, with root steps read with their typing -/

/-- A root step preserves meaning at its typed instances: its two sides are
validly equal wherever each is a valid term of one type and the redex has the
typing facts of a spine of a declared constant of `R`. -/
def TypedRootN (R : Rules Head) (M : NModel Head L) {n : Nat} (l r : Tm Head n) : Prop :=
  ∀ {Γ : Ctx Head n} {A : Tm Head n}, SpineFactsN R M Γ l A → ValidTmN M Γ l A →
    ValidTmN M Γ r A → ValidEqN M Γ l r A

/-- **An object package sound for the conversion model, its root steps read with
their typing**: its universe rules hold on the value side and on the realizer
side, each of its root steps preserves meaning semantically or at its typed
instances, and each of its constants is a valid term of its declared type. -/
structure TypedSoundN (R : Rules Head) (M : NModel Head L) : Prop where
  laws : M.Laws
  headTyping : ∀ {h u : Head}, R.headTyping h u → M.rules.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → M.rules.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → M.rules.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → M.rules.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → M.rules.headEq h h'
  headTyping' : ∀ {h u : Head}, R.headTyping h u → M.side.R.headTyping h u
  isUniverse' : ∀ {u : Head}, R.isUniverse u → M.side.R.isUniverse u
  join' : ∀ {u v w : Head}, R.join u v w → M.side.R.join u v w
  cumulative' : ∀ {u v : Head}, R.cumulative u v → M.side.R.cumulative u v
  headEq' : ∀ {h h' : Head}, R.headEq h h' → M.side.R.headEq h h'
  root : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
    RootSemanticN M l r ∨ TypedRootN R M l r
  constants : ∀ {name : DeclName} {type : Tm Head 0}, R.constantType name = some type →
    ValidTmN M .nil (.const name) type

/-- **The untyped reading of soundness**: the package is sound and every one of
its root steps preserves meaning semantically, read without its typing. -/
def SoundN (R : Rules Head) (M : NModel Head L) : Prop :=
  TypedSoundN R M ∧ ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r → RootSemanticN M l r

/-- A package sound in the untyped reading is sound. -/
theorem SoundN.typed {R : Rules Head} (sound : SoundN R M) : TypedSoundN R M :=
  sound.1

/-- What a statement means in the conversion model, with the valid parts of its
subjects and types, the typing facts of spines and heads along typings, and the
structural form of inclusions. -/
def StatementValidTN (R : Rules Head) (M : NModel Head L) : Statement Head → Prop
  | .typing Γ t A => ValidCtxNN M Γ →
      ValidTmN M Γ t A ∧ StructuredN M Γ t ∧ StructuredN M Γ A ∧ SpineFactsN R M Γ t A ∧
        HeadFactsN M Γ t A
  | .equality Γ a b A => ValidCtxNN M Γ →
      ValidEqN M Γ a b A ∧ StructuredN M Γ a ∧ StructuredN M Γ b ∧ StructuredN M Γ A
  | .sub Γ A B => ValidCtxNN M Γ →
      ValidLeN M Γ A B ∧ StructuredN M Γ A ∧ StructuredN M Γ B ∧ ValidLeStructN M Γ A B

/-- The meaning of a statement with its extra facts gives its meaning. -/
theorem StatementValidTN.forget {R : Rules Head} :
    ∀ {st : Statement Head}, StatementValidTN R M st → StatementValidN M st
  | .typing _ _ _, h => fun ctx =>
      have h' := h ctx
      ⟨h'.1, h'.2.1, h'.2.2.1⟩
  | .equality _ _ _ _, h => h
  | .sub _ _ _, h => fun ctx =>
      have h' := h ctx
      ⟨h'.1, h'.2.1, h'.2.2.1⟩

/-! ## Conversion of the last entry of a context -/

section Convert

variable (laws : M.Laws)
include laws

/-- Valid parts of a type are kept by conversion of the last entry of its
context. -/
theorem StructuredN.convert {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {u : Head}
    (ctx : ValidCtxN M Γ) (eqA : ValidEqN M Γ A A' (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) {B : Tm Head (n + 1)} (parts : StructuredN M (.snoc Γ A) B) :
    StructuredN M (.snoc Γ A') B := by
  have converted := StructuredN.subst B parts (ValidMorN.convert laws ctx eqA hu hu')
    fun _ => trivial
  rwa [subst_ids] at converted

/-- Valid terms are kept by conversion of the last entry of their context. -/
theorem ValidTmN.convert {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {u : Head}
    (ctx : ValidCtxN M Γ) (eqA : ValidEqN M Γ A A' (.head u)) (hu : M.rules.isUniverse u)
    (hu' : M.side.R.isUniverse u) {t B : Tm Head (n + 1)} (valid : ValidTmN M (.snoc Γ A) t B) :
    ValidTmN M (.snoc Γ A') t B := by
  have converted := valid.subst (ValidMorN.convert laws ctx eqA hu hu')
  rwa [subst_ids, subst_ids] at converted

end Convert

/-! ## The fundamental lemma -/

/-- **The fundamental lemma, with root steps read with their typing**: every
derivable statement of a package sound with typed root steps is valid in the
conversion model, with the typing facts of spines and heads along typings and
the structural form of inclusions. -/
theorem Derivable.validTN {R : Rules Head} (sound : TypedSoundN R M) {st : Statement Head}
    (derivation : Derivable R st) : StatementValidTN R M st := by
  have laws := sound.laws
  induction derivation with
  | headType typing =>
      exact fun _ => ⟨ValidTmN.headType laws (sound.headTyping typing) (sound.headTyping' typing),
        trivial, trivial, SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.head (M.levels.ground_typing (sound.headTyping typing))⟩
  | var i =>
      intro ctx
      exact ⟨ValidTmN.var laws ctx i, trivial, (ctx.lookup i).2,
        SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | const declared _ hu ihType =>
      intro _
      obtain ⟨validType, partsType, _⟩ := ihType trivial
      exact ⟨(sound.constants declared).rename (ValidRenN.elim0 _), trivial,
        StructuredN.liftClosed partsType _,
        SpineFactsN.const laws declared (validType.rename (ValidRenN.elim0 _))
          (sound.isUniverse hu),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | piForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have tyA : ValidTyN M _ _ := validA.validTy (sound.isUniverse hu) (sound.isUniverse' hu)
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      exact ⟨ValidTmN.piForm laws validA (sound.isUniverse hu) (sound.isUniverse' hu) validB
          (sound.isUniverse hv) (sound.isUniverse' hv) (sound.join join) (sound.join' join),
        ⟨⟨tyA, partsA⟩, validB.validTy (sound.isUniverse hv) (sound.isUniverse' hv), partsB⟩,
        trivial, SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have tyA : ValidTyN M _ _ := validA.validTy (sound.isUniverse hu) (sound.isUniverse' hu)
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      exact ⟨ValidTmN.sigmaForm laws validA (sound.isUniverse hu) (sound.isUniverse' hu) validB
          (sound.isUniverse hv) (sound.isUniverse' hv) (sound.join join) (sound.join' join),
        ⟨⟨tyA, partsA⟩, validB.validTy (sound.isUniverse hv) (sound.isUniverse' hv), partsB⟩,
        trivial, SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | lamIntro _ hu _ ihPi ihBody =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨validBody, _, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      exact ⟨ValidTmN.lam laws (validPi.validTy (sound.isUniverse hu) (sound.isUniverse' hu))
          validBody, trivial, partsPi',
        SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | appElim _ _ ihG ihA =>
      intro ctx
      obtain ⟨validG, _, partsPi, spineG, _⟩ := ihG ctx
      obtain ⟨_, tyB, partsB⟩ := partsPi
      obtain ⟨validA, partsa, _⟩ := ihA ctx
      exact ⟨ValidTmN.app laws validG validA tyB, trivial,
        StructuredN.inst0 partsB validA partsa, SpineFactsN.app laws spineG validA,
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | pairIntro _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      obtain ⟨validA, _, _⟩ := ihA ctx
      obtain ⟨validB, _, _⟩ := ihB ctx
      exact ⟨ValidTmN.pair laws (validS.validTy (sound.isUniverse hu) (sound.isUniverse' hu))
          validA validB, trivial, partsS,
        SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | fstElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS, _⟩ := ih ctx
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      exact ⟨ValidTmN.fst laws valid tyA, trivial, partsA,
        SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | sndElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS, _⟩ := ih ctx
      obtain ⟨⟨tyA, _⟩, tyB, partsB⟩ := partsS
      exact ⟨ValidTmN.snd laws valid tyA tyB, trivial,
        StructuredN.inst0 partsB (ValidTmN.fst laws valid tyA) trivial,
        SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | idForm _ hu _ _ ihA iha ihb =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      obtain ⟨valida, _, _⟩ := iha ctx
      obtain ⟨validb, _, _⟩ := ihb ctx
      exact ⟨ValidTmN.idForm laws validA (sound.isUniverse hu) (sound.isUniverse' hu) valida validb,
        ⟨⟨validA.validTy (sound.isUniverse hu) (sound.isUniverse' hu), partsA⟩, valida, validb⟩,
        trivial, SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | reflIntro _ ih =>
      intro ctx
      obtain ⟨valid, _, partsA, _⟩ := ih ctx
      have tyA : ValidTyN M _ _ := valid.1
      exact ⟨ValidTmN.refl laws valid, trivial, ⟨⟨tyA, partsA⟩, valid, valid⟩,
        SpineFactsN.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e),
        HeadFactsN.of_ne fun _ e => by cases e⟩
  | sub _ _ ihT ihLe =>
      intro ctx
      obtain ⟨valid, parts, _, spine, heads⟩ := ihT ctx
      obtain ⟨le, _, partsB, leStruct⟩ := ihLe ctx
      exact ⟨ValidTmN.below laws valid le, parts, partsB, SpineFactsN.below laws spine leStruct,
        heads.below leStruct⟩
  | conv _ _ hu ihT ihE =>
      intro ctx
      obtain ⟨valid, parts, _, spine, heads⟩ := ihT ctx
      obtain ⟨eq, _, partsB, _⟩ := ihE ctx
      have leStruct : ValidLeStructN M _ _ _ := ValidLeStructN.ofEq laws eq (sound.isUniverse hu)
      exact ⟨ValidTmN.conv laws valid eq (sound.isUniverse hu) (sound.isUniverse' hu), parts,
        partsB, SpineFactsN.below laws spine leStruct, heads.below leStruct⟩
  | refl _ ih =>
      intro ctx
      obtain ⟨valid, parts, partsA, _⟩ := ih ctx
      exact ⟨ValidEqN.refl valid, parts, parts, partsA⟩
  | symm _ ih =>
      intro ctx
      obtain ⟨eq, partsL, partsR, partsA⟩ := ih ctx
      exact ⟨ValidEqN.symm laws eq, partsR, partsL, partsA⟩
  | trans _ _ ih₁ ih₂ =>
      intro ctx
      obtain ⟨eq₁, partsL, _, partsA⟩ := ih₁ ctx
      obtain ⟨eq₂, _, partsR, _⟩ := ih₂ ctx
      exact ⟨ValidEqN.trans laws eq₁ eq₂, partsL, partsR, partsA⟩
  | convEq _ _ hu ih ihT =>
      intro ctx
      obtain ⟨eq, partsL, partsR, _⟩ := ih ctx
      obtain ⟨eqT, _, partsB, _⟩ := ihT ctx
      exact ⟨ValidEqN.conv laws eq eqT (sound.isUniverse hu) (sound.isUniverse' hu), partsL,
        partsR, partsB⟩
  | subEq _ _ ihE ihLe =>
      intro ctx
      obtain ⟨eq, partsL, partsR, _⟩ := ihE ctx
      obtain ⟨le, _, partsB, _⟩ := ihLe ctx
      exact ⟨ValidEqN.below laws eq le, partsL, partsR, partsB⟩
  | headEq same _ _ ih ih' =>
      intro ctx
      obtain ⟨valid, _, partsA, _, heads⟩ := ih ctx
      obtain ⟨valid', _, _⟩ := ih' ctx
      exact ⟨ValidEqN.headEq laws (sound.headEq same) (sound.headEq' same) valid valid'
          fun e => heads.type_universe laws e, trivial, trivial, partsA⟩
  | piCong _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      have hu₁ := sound.isUniverse hu
      have hu₂ := sound.isUniverse' hu
      have hv₁ := sound.isUniverse hv
      have hv₂ := sound.isUniverse' hv
      have tyA : ValidTyN M _ _ := eqA.1.validTy hu₁ hu₂
      obtain ⟨eqB, partsB, partsB', _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have validB' := ValidTmN.convert laws ctx.valid eqA hu₁ hu₂ eqB.2.1
      exact ⟨ValidEqN.piCong laws eqA hu₁ hu₂ eqB hv₁ hv₂ (sound.join join) (sound.join' join)
          (ValidTmN.piForm laws eqA.2.1 hu₁ hu₂ validB' hv₁ hv₂ (sound.join join)
            (sound.join' join)),
        ⟨⟨tyA, partsA⟩, eqB.1.validTy hv₁ hv₂, partsB⟩,
        ⟨⟨eqA.2.1.validTy hu₁ hu₂, partsA'⟩, validB'.validTy hv₁ hv₂,
          StructuredN.convert laws ctx.valid eqA hu₁ hu₂ partsB'⟩, trivial⟩
  | sigmaCong _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      have hu₁ := sound.isUniverse hu
      have hu₂ := sound.isUniverse' hu
      have hv₁ := sound.isUniverse hv
      have hv₂ := sound.isUniverse' hv
      have tyA : ValidTyN M _ _ := eqA.1.validTy hu₁ hu₂
      obtain ⟨eqB, partsB, partsB', _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have validB' := ValidTmN.convert laws ctx.valid eqA hu₁ hu₂ eqB.2.1
      exact ⟨ValidEqN.sigmaCong laws eqA hu₁ hu₂ eqB hv₁ hv₂ (sound.join join)
          (sound.join' join)
          (ValidTmN.sigmaForm laws eqA.2.1 hu₁ hu₂ validB' hv₁ hv₂ (sound.join join)
            (sound.join' join)),
        ⟨⟨tyA, partsA⟩, eqB.1.validTy hv₁ hv₂, partsB⟩,
        ⟨⟨eqA.2.1.validTy hu₁ hu₂, partsA'⟩, validB'.validTy hv₁ hv₂,
          StructuredN.convert laws ctx.valid eqA hu₁ hu₂ partsB'⟩, trivial⟩
  | idCong _ hu _ _ ihA iha ihb =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      obtain ⟨eqa, _, _, _⟩ := iha ctx
      obtain ⟨eqb, _, _, _⟩ := ihb ctx
      have hu₁ := sound.isUniverse hu
      have hu₂ := sound.isUniverse' hu
      have valida' := ValidTmN.conv laws eqa.2.1 eqA hu₁ hu₂
      have validb' := ValidTmN.conv laws eqb.2.1 eqA hu₁ hu₂
      exact ⟨ValidEqN.idCong laws eqA hu₁ hu₂ eqa eqb
          (ValidTmN.idForm laws eqA.2.1 hu₁ hu₂ valida' validb'),
        ⟨⟨eqA.1.validTy hu₁ hu₂, partsA⟩, eqa.1, eqb.1⟩,
        ⟨⟨eqA.2.1.validTy hu₁ hu₂, partsA'⟩, valida', validb'⟩, trivial⟩
  | lamCong _ hu _ ihPi ihBody =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨eqBody, _, _, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      exact ⟨ValidEqN.lam laws (validPi.validTy (sound.isUniverse hu) (sound.isUniverse' hu))
          eqBody, trivial, trivial, partsPi'⟩
  | appCong _ _ ihF ihA =>
      intro ctx
      obtain ⟨eqF, _, _, partsPi⟩ := ihF ctx
      obtain ⟨_, tyB, partsB⟩ := partsPi
      obtain ⟨eqA, partsa, _, _⟩ := ihA ctx
      exact ⟨ValidEqN.app laws eqF eqA tyB, trivial, trivial,
        StructuredN.inst0 partsB eqA.1 partsa⟩
  | pairCong _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      have partsS' := partsS
      obtain ⟨_, tyB, _⟩ := partsS
      obtain ⟨eqA, _, _, _⟩ := ihA ctx
      obtain ⟨eqB, _, _, _⟩ := ihB ctx
      exact ⟨ValidEqN.pair laws (validS.validTy (sound.isUniverse hu) (sound.isUniverse' hu))
          tyB eqA eqB, trivial, trivial, partsS'⟩
  | fstCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      exact ⟨ValidEqN.fst laws eq tyA, trivial, trivial, partsA⟩
  | sndCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, _⟩, tyB, partsB⟩ := partsS
      exact ⟨ValidEqN.snd laws eq tyA tyB, trivial, trivial,
        StructuredN.inst0 partsB (ValidTmN.fst laws eq.1 tyA) trivial⟩
  | reflCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsA⟩ := ih ctx
      have tyA : ValidTyN M _ _ := eq.1.1
      exact ⟨ValidEqN.reflCong laws eq, trivial, trivial, ⟨⟨tyA, partsA⟩, eq.1, eq.1⟩⟩
  | betaPi _ hu _ _ ihPi ihBody ihA =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      obtain ⟨⟨tyA, partsA⟩, _, partsB⟩ := partsPi
      obtain ⟨validBody, partsBody, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      obtain ⟨validA, partsa, _⟩ := ihA ctx
      exact ⟨ValidEqN.beta laws (validPi.validTy (sound.isUniverse hu) (sound.isUniverse' hu))
          validBody validA, trivial,
        StructuredN.inst0 partsBody validA partsa, StructuredN.inst0 partsB validA partsa⟩
  | betaFst _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, _, _⟩ := ihS ctx
      obtain ⟨validA, partsa, partsA, _⟩ := ihA ctx
      obtain ⟨validB, _, _⟩ := ihB ctx
      exact ⟨ValidEqN.betaFst laws (validS.validTy (sound.isUniverse hu) (sound.isUniverse' hu))
          validA validB, trivial, partsa, partsA⟩
  | betaSnd _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, _, _⟩ := ihS ctx
      obtain ⟨validA, _, _⟩ := ihA ctx
      obtain ⟨validB, partsb, partsB, _⟩ := ihB ctx
      exact ⟨ValidEqN.betaSnd laws (validS.validTy (sound.isUniverse hu) (sound.isUniverse' hu))
          validA validB, trivial, partsb, partsB⟩
  | root step _ _ ihL ihR =>
      intro ctx
      obtain ⟨validL, partsL, partsA, spineL, _⟩ := ihL ctx
      obtain ⟨validR, partsR, _⟩ := ihR ctx
      rcases sound.root step with semantic | typed
      · exact ⟨semantic validL validR, partsL, partsR, partsA⟩
      · exact ⟨typed spineL validL validR, partsL, partsR, partsA⟩
  | etaPi _ _ _ ihF ihG ihApps =>
      intro ctx
      obtain ⟨validF, partsF, partsPi, _⟩ := ihF ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨validG, partsG, _⟩ := ihG ctx
      obtain ⟨eqApps, _, _, _⟩ := ihApps ⟨ctx, tyA, partsA⟩
      exact ⟨ValidEqN.etaPi laws validF validG eqApps, partsF, partsG, partsPi'⟩
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      intro ctx
      obtain ⟨validP, partsP, partsS, _⟩ := ihP ctx
      obtain ⟨validQ, partsQ, _⟩ := ihQ ctx
      obtain ⟨eqFst, _, _, _⟩ := ihFst ctx
      obtain ⟨eqSnd, _, _, _⟩ := ihSnd ctx
      exact ⟨ValidEqN.etaSigma laws validP validQ eqFst eqSnd, partsP, partsQ, partsS⟩
  | subEqual _ hu ih =>
      intro ctx
      obtain ⟨eq, partsA, partsB, _⟩ := ih ctx
      exact ⟨ValidLeN.ofEq laws eq (sound.isUniverse hu) (sound.isUniverse' hu), partsA, partsB,
        ValidLeStructN.ofEq laws eq (sound.isUniverse hu)⟩
  | subUniv c =>
      exact fun _ => ⟨ValidLeN.univ laws (sound.cumulative c) (sound.cumulative' c), trivial,
        trivial, ValidLeStructN.univ (sound.cumulative c)⟩
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      obtain ⟨validPi', partsPi', _⟩ := ihPi' ctx
      have partsPiL := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨eqA, _, _, _⟩ := ihA ctx
      obtain ⟨leB, _, _, leStructB⟩ := ihB ⟨ctx, tyA, partsA⟩
      have tyPi : ValidTyN M _ _ := validPi.validTy (sound.isUniverse hu) (sound.isUniverse' hu)
      have tyPi' : ValidTyN M _ _ :=
        validPi'.validTy (sound.isUniverse hu') (sound.isUniverse' hu')
      exact ⟨ValidLeN.pi laws tyPi tyPi' eqA (sound.isUniverse hw) (sound.isUniverse' hw) leB,
        partsPiL, partsPi',
        ValidLeStructN.pi laws tyPi tyPi' eqA (sound.isUniverse hw) leStructB⟩
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      obtain ⟨validS', partsS', _⟩ := ihS' ctx
      have partsSL := partsS
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      obtain ⟨leA, _, _, leStructA⟩ := ihA ctx
      obtain ⟨leB, _, _, leStructB⟩ := ihB ⟨ctx, tyA, partsA⟩
      have tyS : ValidTyN M _ _ := validS.validTy (sound.isUniverse hu) (sound.isUniverse' hu)
      have tyS' : ValidTyN M _ _ := validS'.validTy (sound.isUniverse hu') (sound.isUniverse' hu')
      exact ⟨ValidLeN.sigma laws tyS tyS' leA leB, partsSL, partsS',
        ValidLeStructN.sigma tyS tyS' leStructA leStructB⟩
  | subTrans _ _ ih₁ ih₂ =>
      intro ctx
      obtain ⟨le₁, partsA, _, leStruct₁⟩ := ih₁ ctx
      obtain ⟨le₂, _, partsC, leStruct₂⟩ := ih₂ ctx
      exact ⟨ValidLeN.trans le₁ le₂, partsA, partsC, ValidLeStructN.trans leStruct₁ leStruct₂⟩

/-- **The fundamental lemma**: every derivable statement of a sound package is
valid in the conversion model. -/
theorem Derivable.validN {R : Rules Head} (sound : TypedSoundN R M) {st : Statement Head}
    (derivation : Derivable R st) : StatementValidN M st :=
  (Derivable.validTN sound derivation).forget

/-! ## Typings, equalities, inclusions and contexts -/

section Corollaries

variable {R : Rules Head} (sound : TypedSoundN R M)
include sound

/-- A derivable typing of a sound package is valid in a context that is valid
with its parts. -/
theorem Typed.validN {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (typing : Typed R Γ t A)
    (ctx : ValidCtxNN M Γ) : ValidTmN M Γ t A :=
  (Derivable.validTN sound typing ctx).1

/-- A derivable equality of a sound package is valid in a context that is valid
with its parts. -/
theorem Equal.validN {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} (equal : Equal R Γ a b A)
    (ctx : ValidCtxNN M Γ) : ValidEqN M Γ a b A :=
  (Derivable.validTN sound equal ctx).1

/-- A derivable inclusion of a sound package is valid in a context that is valid
with its parts. -/
theorem Below.validN {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (below : Below R Γ A B)
    (ctx : ValidCtxNN M Γ) : ValidLeN M Γ A B :=
  (Derivable.validTN sound below ctx).1

/-- A derivable typing of a sound package has the typing facts of spines in a
context that is valid with its parts. -/
theorem Typed.spineFactsN {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (typing : Typed R Γ t A)
    (ctx : ValidCtxNN M Γ) : SpineFactsN R M Γ t A :=
  (Derivable.validTN sound typing ctx).2.2.2.1

/-- A formed context of a sound package is valid with its parts. -/
theorem CtxFormed.validN : ∀ {n : Nat} {Γ : Ctx Head n}, CtxFormed R Γ → ValidCtxNN M Γ
  | _, _, .nil => trivial
  | _, _, .snoc formed ⟨_, hu, typedA⟩ => by
      have ctx := CtxFormed.validN formed
      obtain ⟨validA, partsA, _⟩ := Derivable.validTN sound typedA ctx
      exact ⟨ctx, validA.validTy (sound.isUniverse hu) (sound.isUniverse' hu), partsA⟩

/-- A derivable equality of types of a sound package is valid at the universe
it holds at, in a context that is valid with its parts. -/
theorem TypeEq.validN {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (equal : TypeEq R Γ A B)
    (ctx : ValidCtxNN M Γ) :
    ∃ u, M.rules.isUniverse u ∧ M.side.R.isUniverse u ∧ ValidEqN M Γ A B (.head u) := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, sound.isUniverse hu, sound.isUniverse' hu, Equal.validN sound e ctx⟩

end Corollaries

/-! ## Consequences at the daimon valuation -/

section Consequences

variable {R : Rules Head} (sound : TypedSoundN R M)
include sound

/-- The daimon valuation of a formed context of a sound package, with the
identity on the realizer side, relates the context to itself. -/
theorem CtxFormed.daimonIdsN {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed R Γ) :
    EqSubstN M Γ (World.closed (S := M.reading)) (fun _ => .const M.star)
      (fun _ => .const M.star) Γ ids ids :=
  EqSubstN.daimonIds sound.laws (CtxFormed.validN sound formed).valid

/-- **The evaluated candidate records the shape**: a term typed in a formed
context of a sound package is related to itself, at its own type, by the
candidate of its value at the daimon valuation. -/
theorem Typed.shapeN {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (formed : CtxFormed R Γ)
    (typing : Typed R Γ t A) :
    ∃ P : NPack M 0,
      DenN M (World.closed (S := M.reading)) (Presentation.subst (fun _ => .const M.star) A) P ∧
        P.Val (Presentation.subst (fun _ => .const M.star) t) ∧
        (P.real (Presentation.subst (fun _ => .const M.star) t)).rel Γ A t t := by
  have valid := Typed.validN sound typing (CtxFormed.validN sound formed)
  have e := CtxFormed.daimonIdsN sound formed
  obtain ⟨P, den, -, -⟩ := valid.1 e
  obtain ⟨hv, real⟩ := valid.2 e den
  rw [subst_ids, subst_ids] at real
  exact ⟨P, den, ValueSide.DenS.refl_left sound.laws.value den hv, real⟩

/-- **Escape**: derivably equal terms of a formed context of a sound package are
related by the generic equality of the realizer side. -/
theorem Equal.escapeN {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n} (formed : CtxFormed R Γ)
    (equal : Equal R Γ t u A) : M.side.E.convTm Γ t u A := by
  have valid := Equal.validN sound equal (CtxFormed.validN sound formed)
  have e := CtxFormed.daimonIdsN sound formed
  obtain ⟨P, den, -, -⟩ := valid.1.1 e
  have real := (valid.2.2 e den).2
  rw [subst_ids, subst_ids, subst_ids] at real
  exact (P.real _).escape real

/-- **Escape for types**: derivably equal types of a formed context of a sound
package are related by the generic equality of the realizer side. -/
theorem TypeEq.escapeN {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (formed : CtxFormed R Γ)
    (equal : TypeEq R Γ A B) : M.side.E.convTy Γ A B := by
  obtain ⟨u, hu, hu', valid⟩ := TypeEq.validN sound equal (CtxFormed.validN sound formed)
  have types := (valid.universe hu (CtxFormed.daimonIdsN sound formed)).2
  rw [subst_ids, subst_ids] at types
  exact TypesRel.convTy ⟨u, hu', types⟩

end Consequences

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
