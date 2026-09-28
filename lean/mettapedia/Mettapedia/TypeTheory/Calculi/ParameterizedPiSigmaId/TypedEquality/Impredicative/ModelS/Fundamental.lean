import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Formers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Pairs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Equality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Root
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Telescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Normalization
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Spines

/-!
# The fundamental lemma of model S, and strong normalization

Every derivable statement of an object package is valid in model S when the
package is sound for it (`TypedSoundS`): its universe rules are the model's,
each of its root steps preserves meaning, and each of its constants is a valid
term of its declared type. Along with each judgment the lemma carries the valid parts of
its subjects and types written as type formers.

A term of a universe is valid only when related valuations give it instances of
one pack and one shape at every world reached by a morphism. The formation
rules at a universe give both (`family_related`, `ValueSide.interp_ident`): the domains
of a dependent function or pair type are of one shape by the validity of the
domain, and its codomains at related arguments by the validity of the codomain
under the extended valuations, both lifted to the level of the join by
cumulativity. Heads are universes of one level or leaves, decodings and
identity types are leaves, and a code and its decoding are of one shape.

A formed context is valid, since each entry is typed at a universe. A typed
term in a formed context is therefore valid, and a valid term is strongly
normalizing, and so is its type: the daimon valuation, with variables as
realizers, is a related valuation of every valid context, under which the
realizer instance of a term is the term itself.

## Root steps read with their typing

A root step preserves meaning in one of two ways:

* semantically (`RootSemanticS`): its two sides are validly equal wherever each
  is a valid term of one type;
* at its typed instances (`TypedRootS`): its two sides are validly equal
  wherever each is a valid term of one type and the redex has the typing facts
  of a spine of a declared constant (`SpineFacts`).

Identity elimination at reflexivity is of the second kind: read without its
typing its root obligation fails. The fundamental lemma supplies the facts:
along with each typing it carries the spine facts of its subject, and along
with each inclusion its structural form (`ValidLeStructS`). A constant starts a
spine; an application extends it; inclusion and conversion carry the facts to
the new type.

The untyped reading of soundness, in which every root step must preserve meaning
semantically (`SoundS`), is kept as a named predicate: it implies soundness
(`SoundS.typed`), and the object package with identity elimination is sound
but not in that reading (`ExecutableModel.CodeModel.objectRules_not_soundS_vmodel`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization (WhRed CtxFormed IsType)
open UniverseLevel (LevelOrder)
open Consistency (World)
open StrongNormalization
open TelescopeAbstraction (closeType applyClosed applyClosed_subst)
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

variable (M) in
/-- What a statement means in model S, with the valid parts of its subjects and
types. -/
def StatementValidSS : Statement Head → Prop
  | .typing Γ t A => ValidCtxSS M Γ → ValidTmS M Γ t A ∧ StructuredS M Γ t ∧ StructuredS M Γ A
  | .equality Γ a b A => ValidCtxSS M Γ →
      ValidEqS M Γ a b A ∧ StructuredS M Γ a ∧ StructuredS M Γ b ∧ StructuredS M Γ A
  | .sub Γ A B => ValidCtxSS M Γ → ValidLeS M Γ A B ∧ StructuredS M Γ A ∧ StructuredS M Γ B

/-! ## Soundness, with root steps read with their typing -/

/-- A root step preserves meaning at its typed instances: its two sides are
validly equal wherever each is a valid term of one type and the redex has the
typing facts of a spine of a declared constant of `R`. -/
def TypedRootS (R : Rules Head) (M : SModel Head L) {n : Nat} (l r : Tm Head n) : Prop :=
  ∀ {Γ : Ctx Head n} {A : Tm Head n}, SpineFacts R M Γ l A → ValidTmS M Γ l A →
    ValidTmS M Γ r A → ValidEqS M Γ l r A

/-- **An object package sound for model S, its root steps read with their
typing**: its universe rules are the model's, each of its root steps preserves
meaning semantically or at its typed instances, and each of its constants is a
valid term of its declared type. -/
structure TypedSoundS (R : Rules Head) (M : SModel Head L) : Prop where
  laws : M.Laws
  headTyping : ∀ {h u : Head}, R.headTyping h u → M.rules.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → M.rules.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → M.rules.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → M.rules.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → M.rules.headEq h h'
  root : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
    RootSemanticS M l r ∨ TypedRootS R M l r
  constants : ∀ {name : DeclName} {type : Tm Head 0}, R.constantType name = some type →
    ValidTmS M .nil (.const name) type

/-- **The untyped reading of soundness**: the package is sound and every one of
its root steps preserves meaning semantically, read without its typing. -/
def SoundS (R : Rules Head) (M : SModel Head L) : Prop :=
  TypedSoundS R M ∧ ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r → RootSemanticS M l r

/-- A package sound in the untyped reading is sound. -/
theorem SoundS.typed {R : Rules Head} (sound : SoundS R M) : TypedSoundS R M :=
  sound.1

/-- What a statement means in model S, with the valid parts of its subjects and
types, the typing facts of spines along typings, and the structural form of
inclusions. -/
def StatementValidTS (R : Rules Head) (M : SModel Head L) : Statement Head → Prop
  | .typing Γ t A => ValidCtxSS M Γ →
      ValidTmS M Γ t A ∧ StructuredS M Γ t ∧ StructuredS M Γ A ∧ SpineFacts R M Γ t A
  | .equality Γ a b A => ValidCtxSS M Γ →
      ValidEqS M Γ a b A ∧ StructuredS M Γ a ∧ StructuredS M Γ b ∧ StructuredS M Γ A
  | .sub Γ A B => ValidCtxSS M Γ →
      ValidLeS M Γ A B ∧ StructuredS M Γ A ∧ StructuredS M Γ B ∧ ValidLeStructS M Γ A B

/-- The meaning of a statement with its extra facts gives its meaning. -/
theorem StatementValidTS.forget {R : Rules Head} :
    ∀ {st : Statement Head}, StatementValidTS R M st → StatementValidSS M st
  | .typing _ _ _, h => fun ctx =>
      have h' := h ctx
      ⟨h'.1, h'.2.1, h'.2.2.1⟩
  | .equality _ _ _ _, h => h
  | .sub _ _ _, h => fun ctx =>
      have h' := h ctx
      ⟨h'.1, h'.2.1, h'.2.2.1⟩

/-- Structure of a type is kept by conversion of the context it lives in. -/
theorem StructuredS.convert (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {u : Head} (ctx : ValidCtxS M Γ) (eqA : ValidEqS M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) {B : Tm Head (n + 1)} (parts : StructuredS M (.snoc Γ A) B) :
    StructuredS M (.snoc Γ A') B := by
  have converted := StructuredS.subst B parts (ValidMorS.convert laws ctx eqA hu)
    fun _ => trivial
  rwa [subst_ids] at converted

theorem ValidTmS.convert (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {u : Head} (ctx : ValidCtxS M Γ) (eqA : ValidEqS M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) {t B : Tm Head (n + 1)} (valid : ValidTmS M (.snoc Γ A) t B) :
    ValidTmS M (.snoc Γ A') t B := by
  have converted := valid.subst (ValidMorS.convert laws ctx eqA hu)
  rwa [subst_ids, subst_ids] at converted

/-- **The fundamental lemma, with root steps read with their typing**: every
derivable statement of a package sound with typed root steps is valid in model
S, with the typing facts of spines along typings and the structural form of
inclusions. -/
theorem Derivable.validTS {R : Rules Head} (sound : TypedSoundS R M) {st : Statement Head}
    (derivation : Derivable R st) : StatementValidTS R M st := by
  have laws := sound.laws
  induction derivation with
  | headType typing =>
      exact fun _ => ⟨ValidTmS.headType laws (sound.headTyping typing), trivial, trivial,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | var i =>
      intro ctx
      exact ⟨ValidTmS.var laws ctx i, trivial, (ctx.lookup i).2,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | const declared _ hu ihType =>
      intro _
      obtain ⟨validType, partsType, _⟩ := ihType trivial
      exact ⟨(sound.constants declared).rename (ValidRenS.elim0 _), trivial,
        StructuredS.liftClosed partsType _,
        SpineFacts.const laws declared (validType.rename (ValidRenS.elim0 _))
          (sound.isUniverse hu)⟩
  | piForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have tyA : ValidTyS M _ _ := validA.validTy hu'
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have hv' := sound.isUniverse hv
      exact ⟨ValidTmS.piForm laws validA hu' validB hv' (sound.join join),
        ⟨⟨tyA, partsA⟩, validB.validTy hv', partsB⟩, trivial,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have tyA : ValidTyS M _ _ := validA.validTy hu'
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have hv' := sound.isUniverse hv
      exact ⟨ValidTmS.sigmaForm laws validA hu' validB hv' (sound.join join),
        ⟨⟨tyA, partsA⟩, validB.validTy hv', partsB⟩, trivial,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | lamIntro _ hu _ ihPi ihBody =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨validBody, _, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      exact ⟨ValidTmS.lam laws (validPi.validTy (sound.isUniverse hu)) validBody, trivial,
        partsPi', SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | appElim _ _ ihG ihA =>
      intro ctx
      obtain ⟨validG, _, partsPi, spineG⟩ := ihG ctx
      obtain ⟨_, tyB, partsB⟩ := partsPi
      obtain ⟨validA, partsa, _⟩ := ihA ctx
      exact ⟨ValidTmS.app laws validG validA tyB, trivial,
        StructuredS.inst0 partsB validA partsa, SpineFacts.app laws spineG validA⟩
  | pairIntro _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      obtain ⟨validA, _, _⟩ := ihA ctx
      obtain ⟨validB, _, _⟩ := ihB ctx
      exact ⟨ValidTmS.pair laws (validS.validTy (sound.isUniverse hu)) validA validB,
        trivial, partsS, SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | fstElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS, _⟩ := ih ctx
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      exact ⟨ValidTmS.fst laws valid tyA, trivial, partsA,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | sndElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS, _⟩ := ih ctx
      obtain ⟨⟨tyA, _⟩, tyB, partsB⟩ := partsS
      exact ⟨ValidTmS.snd laws valid tyA tyB, trivial,
        StructuredS.inst0 partsB (ValidTmS.fst laws valid tyA) trivial,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | idForm _ hu _ _ ihA iha ihb =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      obtain ⟨valida, _, _⟩ := iha ctx
      obtain ⟨validb, _, _⟩ := ihb ctx
      have hu' := sound.isUniverse hu
      exact ⟨ValidTmS.idForm laws validA hu' valida validb,
        ⟨⟨validA.validTy hu', partsA⟩, valida, validb⟩, trivial,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | reflIntro _ ih =>
      intro ctx
      obtain ⟨valid, _, partsA, _⟩ := ih ctx
      have tyA : ValidTyS M _ _ := valid.1
      exact ⟨ValidTmS.refl laws valid, trivial, ⟨⟨tyA, partsA⟩, valid, valid⟩,
        SpineFacts.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | sub _ _ ihT ihLe =>
      intro ctx
      obtain ⟨valid, parts, _, spine⟩ := ihT ctx
      obtain ⟨le, _, partsB, leStruct⟩ := ihLe ctx
      exact ⟨ValidTmS.below laws valid le, parts, partsB, SpineFacts.below laws spine leStruct⟩
  | conv _ _ hu ihT ihE =>
      intro ctx
      obtain ⟨valid, parts, _, spine⟩ := ihT ctx
      obtain ⟨eq, _, partsB, _⟩ := ihE ctx
      have hu' := sound.isUniverse hu
      exact ⟨ValidTmS.conv laws valid eq hu', parts, partsB,
        SpineFacts.below laws spine (ValidLeStructS.ofEq laws eq hu')⟩
  | refl _ ih =>
      intro ctx
      obtain ⟨valid, parts, partsA, _⟩ := ih ctx
      exact ⟨ValidEqS.refl valid, parts, parts, partsA⟩
  | symm _ ih =>
      intro ctx
      obtain ⟨eq, partsL, partsR, partsA⟩ := ih ctx
      exact ⟨ValidEqS.symm laws eq, partsR, partsL, partsA⟩
  | trans _ _ ih₁ ih₂ =>
      intro ctx
      obtain ⟨eq₁, partsL, _, partsA⟩ := ih₁ ctx
      obtain ⟨eq₂, _, partsR, _⟩ := ih₂ ctx
      exact ⟨ValidEqS.trans laws eq₁ eq₂, partsL, partsR, partsA⟩
  | convEq _ _ hu ih ihT =>
      intro ctx
      obtain ⟨eq, partsL, partsR, _⟩ := ih ctx
      obtain ⟨eqT, _, partsB, _⟩ := ihT ctx
      exact ⟨ValidEqS.conv laws eq eqT (sound.isUniverse hu), partsL, partsR, partsB⟩
  | subEq _ _ ihE ihLe =>
      intro ctx
      obtain ⟨eq, partsL, partsR, _⟩ := ihE ctx
      obtain ⟨le, _, partsB, _⟩ := ihLe ctx
      exact ⟨ValidEqS.below laws eq le, partsL, partsR, partsB⟩
  | headEq same _ _ ih ih' =>
      intro ctx
      obtain ⟨valid, _, partsA, _⟩ := ih ctx
      obtain ⟨valid', _, _⟩ := ih' ctx
      exact ⟨ValidEqS.headEq laws (sound.headEq same) valid valid', trivial, trivial, partsA⟩
  | piCong _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have hv' := sound.isUniverse hv
      have tyA : ValidTyS M _ _ := eqA.1.validTy hu'
      obtain ⟨eqB, partsB, partsB', _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have validB' := ValidTmS.convert laws ctx.valid eqA hu' eqB.2.1
      exact ⟨ValidEqS.piCong laws eqA hu' eqB hv' (sound.join join)
          (ValidTmS.piForm laws eqA.2.1 hu' validB' hv' (sound.join join)),
        ⟨⟨tyA, partsA⟩, eqB.1.validTy hv', partsB⟩,
        ⟨⟨eqA.2.1.validTy hu', partsA'⟩, validB'.validTy hv',
          StructuredS.convert laws ctx.valid eqA hu' partsB'⟩, trivial⟩
  | sigmaCong _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have hv' := sound.isUniverse hv
      have tyA : ValidTyS M _ _ := eqA.1.validTy hu'
      obtain ⟨eqB, partsB, partsB', _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have validB' := ValidTmS.convert laws ctx.valid eqA hu' eqB.2.1
      exact ⟨ValidEqS.sigmaCong laws eqA hu' eqB hv' (sound.join join)
          (ValidTmS.sigmaForm laws eqA.2.1 hu' validB' hv' (sound.join join)),
        ⟨⟨tyA, partsA⟩, eqB.1.validTy hv', partsB⟩,
        ⟨⟨eqA.2.1.validTy hu', partsA'⟩, validB'.validTy hv',
          StructuredS.convert laws ctx.valid eqA hu' partsB'⟩, trivial⟩
  | idCong _ hu _ _ ihA iha ihb =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      obtain ⟨eqa, _, _, _⟩ := iha ctx
      obtain ⟨eqb, _, _, _⟩ := ihb ctx
      have hu' := sound.isUniverse hu
      have valida' := ValidTmS.conv laws eqa.2.1 eqA hu'
      have validb' := ValidTmS.conv laws eqb.2.1 eqA hu'
      exact ⟨ValidEqS.idCong laws eqA hu' eqa eqb
          (ValidTmS.idForm laws eqA.2.1 hu' valida' validb'),
        ⟨⟨eqA.1.validTy hu', partsA⟩, eqa.1, eqb.1⟩,
        ⟨⟨eqA.2.1.validTy hu', partsA'⟩, valida', validb'⟩, trivial⟩
  | lamCong _ hu _ ihPi ihBody =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨eqBody, _, _, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      exact ⟨ValidEqS.lam laws (validPi.validTy (sound.isUniverse hu)) eqBody, trivial,
        trivial, partsPi'⟩
  | appCong _ _ ihF ihA =>
      intro ctx
      obtain ⟨eqF, _, _, partsPi⟩ := ihF ctx
      obtain ⟨_, tyB, partsB⟩ := partsPi
      obtain ⟨eqA, partsa, _, _⟩ := ihA ctx
      exact ⟨ValidEqS.app laws eqF eqA tyB, trivial, trivial,
        StructuredS.inst0 partsB eqA.1 partsa⟩
  | pairCong _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      have partsS' := partsS
      obtain ⟨_, tyB, _⟩ := partsS
      obtain ⟨eqA, _, _, _⟩ := ihA ctx
      obtain ⟨eqB, _, _, _⟩ := ihB ctx
      exact ⟨ValidEqS.pair laws (validS.validTy (sound.isUniverse hu)) tyB eqA eqB,
        trivial, trivial, partsS'⟩
  | fstCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      exact ⟨ValidEqS.fst laws eq tyA, trivial, trivial, partsA⟩
  | sndCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, _⟩, tyB, partsB⟩ := partsS
      exact ⟨ValidEqS.snd laws eq tyA tyB, trivial, trivial,
        StructuredS.inst0 partsB (ValidTmS.fst laws eq.1 tyA) trivial⟩
  | reflCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsA⟩ := ih ctx
      have tyA : ValidTyS M _ _ := eq.1.1
      exact ⟨ValidEqS.reflCong laws eq, trivial, trivial, ⟨⟨tyA, partsA⟩, eq.1, eq.1⟩⟩
  | betaPi _ _ _ _ ihPi ihBody ihA =>
      intro ctx
      obtain ⟨_, partsPi, _⟩ := ihPi ctx
      obtain ⟨⟨tyA, partsA⟩, _, partsB⟩ := partsPi
      obtain ⟨validBody, partsBody, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      obtain ⟨validA, partsa, _⟩ := ihA ctx
      exact ⟨ValidEqS.beta laws validBody validA, trivial,
        StructuredS.inst0 partsBody validA partsa, StructuredS.inst0 partsB validA partsa⟩
  | betaFst _ _ _ _ _ ihA ihB =>
      intro ctx
      obtain ⟨validA, partsa, partsA, _⟩ := ihA ctx
      obtain ⟨validB, _, _⟩ := ihB ctx
      exact ⟨ValidEqS.betaFst laws validA validB, trivial, partsa, partsA⟩
  | betaSnd _ _ _ _ _ ihA ihB =>
      intro ctx
      obtain ⟨validA, _, _⟩ := ihA ctx
      obtain ⟨validB, partsb, partsB, _⟩ := ihB ctx
      exact ⟨ValidEqS.betaSnd laws validA validB, trivial, partsb, partsB⟩
  | root step _ _ ihL ihR =>
      intro ctx
      obtain ⟨validL, partsL, partsA, spineL⟩ := ihL ctx
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
      exact ⟨ValidEqS.etaPi laws validF validG eqApps, partsF, partsG, partsPi'⟩
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      intro ctx
      obtain ⟨validP, partsP, partsS, _⟩ := ihP ctx
      obtain ⟨validQ, partsQ, _⟩ := ihQ ctx
      obtain ⟨eqFst, _, _, _⟩ := ihFst ctx
      obtain ⟨eqSnd, _, _, _⟩ := ihSnd ctx
      exact ⟨ValidEqS.etaSigma laws validP validQ eqFst eqSnd, partsP, partsQ, partsS⟩
  | subEqual _ hu ih =>
      intro ctx
      obtain ⟨eq, partsA, partsB, _⟩ := ih ctx
      have hu' := sound.isUniverse hu
      exact ⟨ValidLeS.ofEq laws eq hu', partsA, partsB, ValidLeStructS.ofEq laws eq hu'⟩
  | subUniv c =>
      exact fun _ => ⟨ValidLeS.univ laws (sound.cumulative c), trivial, trivial,
        ValidLeStructS.univ (sound.cumulative c)⟩
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      obtain ⟨validPi', partsPi', _⟩ := ihPi' ctx
      have partsPiL := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨eqA, _, _, _⟩ := ihA ctx
      obtain ⟨leB, _, _, leStructB⟩ := ihB ⟨ctx, tyA, partsA⟩
      have tyPi : ValidTyS M _ _ := validPi.validTy (sound.isUniverse hu)
      have tyPi' : ValidTyS M _ _ := validPi'.validTy (sound.isUniverse hu')
      exact ⟨ValidLeS.pi laws tyPi tyPi' eqA (sound.isUniverse hw) leB, partsPiL, partsPi',
        ValidLeStructS.pi laws tyPi tyPi' eqA (sound.isUniverse hw) leStructB⟩
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      obtain ⟨validS', partsS', _⟩ := ihS' ctx
      have partsSL := partsS
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      obtain ⟨leA, _, _, leStructA⟩ := ihA ctx
      obtain ⟨leB, _, _, leStructB⟩ := ihB ⟨ctx, tyA, partsA⟩
      have tyS : ValidTyS M _ _ := validS.validTy (sound.isUniverse hu)
      have tyS' : ValidTyS M _ _ := validS'.validTy (sound.isUniverse hu')
      exact ⟨ValidLeS.sigma laws tyS tyS' leA leB, partsSL, partsS',
        ValidLeStructS.sigma tyS tyS' leStructA leStructB⟩
  | subTrans _ _ ih₁ ih₂ =>
      intro ctx
      obtain ⟨le₁, partsA, _, leStruct₁⟩ := ih₁ ctx
      obtain ⟨le₂, _, partsC, leStruct₂⟩ := ih₂ ctx
      exact ⟨ValidLeS.trans le₁ le₂, partsA, partsC, ValidLeStructS.trans leStruct₁ leStruct₂⟩

/-- **The fundamental lemma**: every derivable statement of a sound package is
valid in model S. -/
theorem Derivable.validS {R : Rules Head} (sound : TypedSoundS R M) {st : Statement Head}
    (derivation : Derivable R st) : StatementValidSS M st :=
  (Derivable.validTS sound derivation).forget

/-! ## Typings, contexts and strong normalization -/

/-- A derivable typing of a sound package is valid in a context that is valid
with its parts. -/
theorem Typed.validS {R : Rules Head} (sound : TypedSoundS R M) {n : Nat} {Γ : Ctx Head n}
    {t A : Tm Head n} (typing : Typed R Γ t A) (ctx : ValidCtxSS M Γ) : ValidTmS M Γ t A :=
  (Derivable.validTS sound typing ctx).1

/-- A derivable typing of a sound package has the typing facts of spines in a
context that is valid with its parts. -/
theorem Typed.spineFacts {R : Rules Head} (sound : TypedSoundS R M) {n : Nat} {Γ : Ctx Head n}
    {t A : Tm Head n} (typing : Typed R Γ t A) (ctx : ValidCtxSS M Γ) : SpineFacts R M Γ t A :=
  (Derivable.validTS sound typing ctx).2.2.2

/-- A formed context of a sound package is valid with its parts. -/
theorem CtxFormed.validS {R : Rules Head} (sound : TypedSoundS R M) :
    ∀ {n : Nat} {Γ : Ctx Head n}, CtxFormed R Γ → ValidCtxSS M Γ
  | _, _, .nil => trivial
  | _, _, .snoc formed ⟨_, hu, typedA⟩ => by
      have ctx := CtxFormed.validS sound formed
      obtain ⟨validA, partsA, _⟩ := Derivable.validTS sound typedA ctx
      exact ⟨ctx, validA.validTy (sound.isUniverse hu), partsA⟩

/-- **Strong normalization.** In a package sound for model S, every term typed
in a formed context is strongly normalizing under the realizer side's
reduction, and so is its type. -/
theorem Typed.sn {R : Rules Head} (sound : TypedSoundS R M) {n : Nat} {Γ : Ctx Head n}
    {t A : Tm Head n} (formed : CtxFormed R Γ) (typed : Typed R Γ t A) :
    SN M.realizers.rules t ∧ SN M.realizers.rules A :=
  have ctx := CtxFormed.validS sound formed
  (Typed.validS sound typed ctx).normalizes sound.laws ctx.valid

/-- Both sides of a derivable equality in a formed context are strongly
normalizing, and so is their type. -/
theorem Equal.sn {R : Rules Head} (sound : TypedSoundS R M) {n : Nat} {Γ : Ctx Head n}
    {a b A : Tm Head n} (formed : CtxFormed R Γ) (equal : Derivable R (.equality Γ a b A)) :
    SN M.realizers.rules a ∧ SN M.realizers.rules b ∧ SN M.realizers.rules A :=
  have ctx := CtxFormed.validS sound formed
  (Derivable.validTS sound equal ctx).1.normalizes sound.laws ctx.valid

/-- Both sides of a derivable inclusion in a formed context are strongly
normalizing. -/
theorem Below.sn {R : Rules Head} (sound : TypedSoundS R M) {n : Nat} {Γ : Ctx Head n}
    {A B : Tm Head n} (formed : CtxFormed R Γ) (below : Derivable R (.sub Γ A B)) :
    SN M.realizers.rules A ∧ SN M.realizers.rules B :=
  have ctx := CtxFormed.validS sound formed
  (Derivable.validTS sound below ctx).1.normalizes sound.laws ctx.valid

/-! ## Definitions by one equation -/

/-- A constant defined by one equation `f x₁ ⋯ x_k ⟶ rhs`, whose declared type
and right-hand side are typed in a sound package without it, is a valid term of
its declared type: its full application computes on the value side to the
right-hand side, which is valid by the fundamental lemma of that package, and
its realizer instances lie in every candidate containing the right-hand side's
instances. -/
theorem ValidTmS.definition {R₀ : Rules Head} (sound₀ : TypedSoundS R₀ M) {f : DeclName}
    {k : Nat} {Θ : Ctx Head k} {C rhs : Tm Head k}
    (typed : ∃ w, R₀.isUniverse w ∧ Typed R₀ .nil (closeType Θ C) (.head w))
    (body : Typed R₀ Θ rhs C)
    (rule : ∀ {n : Nat} (σ : Sub Head k n),
      WhRed M.rules M.roles (applyClosed Θ σ (.const f)) (Presentation.subst σ rhs))
    (realRule : ∀ {r : Nat} (ς : Sub Head k r), (∀ i, SN M.realizers.rules (ς i)) →
      ∀ X : M.Cand, X.mem (Presentation.subst ς rhs) → X.mem (applyClosed Θ ς (.const f))) :
    ValidTmS M .nil (.const f) (closeType Θ C) := by
  obtain ⟨w, hw, typedC⟩ := typed
  obtain ⟨validC, partsC, _⟩ := Derivable.validTS sound₀ typedC trivial
  have validType : ValidTyS M .nil (closeType Θ C) := validC.validTy (sound₀.isUniverse hw)
  obtain ⟨ctx, _, _⟩ := ValidTyS.close_parts Θ validType partsC
  refine ValidTmS.close sound₀.laws Θ validType partsC
    (ValidTmS.of_red sound₀.laws (fun σ => ?_) (fun ς sns X h => ?_)
      (Typed.validS sound₀ body ctx))
  · rw [applyClosed_subst]
    exact rule σ
  · rw [applyClosed_subst]
    exact realRule ς sns X h

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
