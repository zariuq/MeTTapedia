import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantRenaming

/-!
# Model SN read through a renaming of constants

A package may declare several constants that the model reads alike, for
instance one constant for each instance of a declaration with level parameters.
A map `f` on declared names reads each constant `c` of the package as the
constant `f c` of the model: a statement is read after renaming its constants.

The package is **sound for the model through `f`** (`TypedSoundSR`) when its
universe rules are the model's, each of its constants `c`, declared at `T`,
renames to a valid term `f c` of `T` renamed, and each of its root steps renames
to a step that preserves meaning, semantically or at its typed instances. The
typing facts of a spine are those of the renamed spine at the renamed declared
type of its head (`SpineFactsR`).

**The fundamental lemma through a renaming** (`Derivable.validTSR`): every
derivable statement of such a package is valid in the model once renamed, with
the typing facts of spines along typings and the structural form of inclusions.
So a term typed in a formed context is strongly normalizing once renamed
(`Typed.snR`).

With the identity renaming this is the fundamental lemma of model SN.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization (WhRed CtxFormed IsType appSpine Tm.mapConst_appSpine
  appSpine_const_injective appSpine_const_eq_app)
open UniverseLevel (LevelOrder)
open Consistency (World)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-! ## Spines read through a renaming -/

/-- The typing facts of a spine of a declared constant, read through a renaming:
under related valuations of the renamed context, the instances of the renamed
arguments are valid inputs of the renamed declared telescope and the rest of it
is included in the instance of the renamed type, or that instance is
hereditarily total. -/
def SpineFactsR (R : Rules Head) (M : SNModel Head L) (f : DeclName → DeclName) {n : Nat}
    (Γ : Ctx Head n) (t A : Tm Head n) : Prop :=
  ∀ {c : DeclName} {args : List (Tm Head n)} {T : Tm Head 0},
    t = appSpine (.const c) args → R.constantType c = some T →
      ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
        EqSubstS M (Γ.mapConst f) ξ σ σ' ς →
          SpineOK M ξ (liftClosed (T.mapConst f))
              (args.map fun a => Presentation.subst σ (a.mapConst f))
              (args.map fun a => Presentation.subst ς (a.mapConst f))
              (Presentation.subst σ (A.mapConst f)) ∨
            Shape M.value (DenS M.value) .total ξ (Presentation.subst σ (A.mapConst f))
              (Presentation.subst σ (A.mapConst f))

namespace SpineFactsR

variable {R : Rules Head} {f : DeclName → DeclName}

/-- A term that is neither a constant nor an application has the facts
vacuously. -/
theorem of_ne {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (notConst : ∀ c : DeclName, t ≠ .const c) (notApp : ∀ g a : Tm Head n, t ≠ .app g a) :
    SpineFactsR R M f Γ t A := by
  intro c args T e
  rcases Normalization.appSpine_const_cases c args with e' | ⟨g, a, e'⟩
  · exact absurd (e.trans e') (notConst c)
  · exact absurd (e.trans e') (notApp g a)

/-- **A declared constant starts a spine.** -/
theorem const (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0}
    {u : Head} (declared : R.constantType name = some type)
    (validType : ValidTmS M (Γ.mapConst f) (liftClosed (type.mapConst f)) (.head u))
    (hu : M.rules.isUniverse u) :
    SpineFactsR R M f Γ (.const name) (liftClosed type) := by
  intro c args T e declared' m r ξ σ σ' ς eq
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective (as := []) e
  obtain rfl := Option.some.inj (declared.symm.trans declared')
  refine .inl ?_
  have related : (universeAt M (M.levels.level u) ξ).rel
      (Presentation.subst σ (liftClosed (type.mapConst f)))
      (Presentation.subst σ' (liftClosed (type.mapConst f))) :=
    (ValidTmS.universe validType hu eq).1
  rw [subst_liftClosed, subst_liftClosed] at related
  rw [Presentation.Tm.mapConst_liftClosed, subst_liftClosed]
  exact SLe.of_universe laws.value related

/-- **An application extends a spine.** -/
theorem app (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n}
    {B : Tm Head (n + 1)} (facts : SpineFactsR R M f Γ g (.pi A B))
    (validA : ValidTmS M (Γ.mapConst f) (a.mapConst f) (A.mapConst f)) :
    SpineFactsR R M f Γ (.app g a) (inst0 a B) := by
  intro c args T e declared m r ξ σ σ' ς eq
  obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app e.symm
  have valid : ∀ {P : Pack M.value m},
      DenS M.value ξ (Presentation.subst σ (A.mapConst f)) P →
      P.Val (Presentation.subst σ (a.mapConst f)) ∧
        (P.real (Presentation.subst σ (a.mapConst f))).mem
          (Presentation.subst ς (a.mapConst f)) := fun den =>
    ⟨den.refl_left laws.value (validA.2 eq den).1, (validA.2 eq den).2⟩
  rw [Presentation.Tm.mapConst_inst0, subst_inst0, List.map_append, List.map_append]
  rcases facts rfl declared eq with h | t
  · exact SpineOK.app laws h valid
  · obtain ⟨P, hP⟩ := t.total_interp
    obtain ⟨Q, rfl, iQ⟩ := (DenS.facts laws.value).piPack hP .refl
    exact .inr (total_cod laws t .refl iQ.dom_id (valid iQ.dom_id).1)

/-- **The facts pass along structural inclusion** of the type. -/
theorem below (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (facts : SpineFactsR R M f Γ t A)
    (le : ValidLeStructS M (Γ.mapConst f) (A.mapConst f) (B.mapConst f)) :
    SpineFactsR R M f Γ t B := by
  intro c args T e declared m r ξ σ σ' ς eq
  rcases facts e declared eq with h | t
  · exact .inl (h.mono (le eq))
  · exact .inr ((le eq).total laws t)

end SpineFactsR

/-! ## Soundness through a renaming -/

/-- A root step preserves meaning at its typed instances through a renaming: its
two renamed sides are validly equal wherever each is a valid term of one type
and the redex has the typing facts of a spine read through the renaming. -/
def TypedRootSR (R : Rules Head) (M : SNModel Head L) (f : DeclName → DeclName) {n : Nat}
    (l r : Tm Head n) : Prop :=
  ∀ {Γ : Ctx Head n} {A : Tm Head n}, SpineFactsR R M f Γ l A →
    ValidTmS M (Γ.mapConst f) (l.mapConst f) (A.mapConst f) →
    ValidTmS M (Γ.mapConst f) (r.mapConst f) (A.mapConst f) →
    ValidEqS M (Γ.mapConst f) (l.mapConst f) (r.mapConst f) (A.mapConst f)

/-- **An object package sound for model SN through a renaming of its
constants**: its universe rules are the model's, each of its root steps renames
to a step that preserves meaning semantically or at its typed instances, and
each of its constants renames to a valid term of its renamed declared type. -/
structure TypedSoundSR (R : Rules Head) (M : SNModel Head L) (f : DeclName → DeclName) :
    Prop where
  laws : M.Laws
  headTyping : ∀ {h u : Head}, R.headTyping h u → M.rules.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → M.rules.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → M.rules.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → M.rules.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → M.rules.headEq h h'
  root : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
    RootSemanticS M (l.mapConst f) (r.mapConst f) ∨ TypedRootSR R M f l r
  constants : ∀ {name : DeclName} {type : Tm Head 0}, R.constantType name = some type →
    ValidTmS M .nil (.const (f name)) (type.mapConst f)

/-- What a statement means in model SN through a renaming: its renaming is valid,
with the valid parts of its subjects and types, the typing facts of spines along
typings, and the structural form of inclusions. -/
def StatementValidTSR (R : Rules Head) (M : SNModel Head L) (f : DeclName → DeclName) :
    Statement Head → Prop
  | .typing Γ t A => ValidCtxSS M (Γ.mapConst f) →
      ValidTmS M (Γ.mapConst f) (t.mapConst f) (A.mapConst f) ∧
        StructuredS M (Γ.mapConst f) (t.mapConst f) ∧
        StructuredS M (Γ.mapConst f) (A.mapConst f) ∧ SpineFactsR R M f Γ t A
  | .equality Γ a b A => ValidCtxSS M (Γ.mapConst f) →
      ValidEqS M (Γ.mapConst f) (a.mapConst f) (b.mapConst f) (A.mapConst f) ∧
        StructuredS M (Γ.mapConst f) (a.mapConst f) ∧
        StructuredS M (Γ.mapConst f) (b.mapConst f) ∧
        StructuredS M (Γ.mapConst f) (A.mapConst f)
  | .sub Γ A B => ValidCtxSS M (Γ.mapConst f) →
      ValidLeS M (Γ.mapConst f) (A.mapConst f) (B.mapConst f) ∧
        StructuredS M (Γ.mapConst f) (A.mapConst f) ∧
        StructuredS M (Γ.mapConst f) (B.mapConst f) ∧
        ValidLeStructS M (Γ.mapConst f) (A.mapConst f) (B.mapConst f)

/-- **The fundamental lemma through a renaming of constants**: every derivable
statement of a package sound for model SN through a renaming is valid in the
model once renamed, with the typing facts of spines along typings and the
structural form of inclusions. -/
theorem Derivable.validTSR {R : Rules Head} {f : DeclName → DeclName}
    (sound : TypedSoundSR R M f) {st : Statement Head} (derivation : Derivable R st) :
    StatementValidTSR R M f st := by
  have laws := sound.laws
  induction derivation with
  | headType typing =>
      exact fun _ => ⟨ValidTmS.headType laws (sound.headTyping typing), trivial, trivial,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | @var n Γ i =>
      intro ctx
      have valid := ValidTmS.var laws ctx i
      have parts := (ctx.lookup i).2
      rw [Ctx.lookup_mapConst] at valid parts
      exact ⟨valid, trivial, parts,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | @const n Γ name type u declared _ hu ihType =>
      intro _
      obtain ⟨validType, partsType, _⟩ := ihType trivial
      have validC := (sound.constants declared).rename (ValidRenS.elim0 (Γ.mapConst f))
      have validT := validType.rename (ValidRenS.elim0 (Γ.mapConst f))
      refine ⟨?_, trivial, ?_, ?_⟩
      · rw [Presentation.Tm.mapConst_liftClosed]
        exact validC
      · rw [Presentation.Tm.mapConst_liftClosed]
        exact StructuredS.liftClosed partsType _
      · exact SpineFactsR.const laws declared validT (sound.isUniverse hu)
  | piForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have tyA : ValidTyS M _ _ := validA.validTy hu'
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have hv' := sound.isUniverse hv
      exact ⟨ValidTmS.piForm laws validA hu' validB hv' (sound.join join),
        ⟨⟨tyA, partsA⟩, validB.validTy hv', partsB⟩, trivial,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have tyA : ValidTyS M _ _ := validA.validTy hu'
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have hv' := sound.isUniverse hv
      exact ⟨ValidTmS.sigmaForm laws validA hu' validB hv' (sound.join join),
        ⟨⟨tyA, partsA⟩, validB.validTy hv', partsB⟩, trivial,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | lamIntro _ hu _ ihPi ihBody =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨validBody, _, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      exact ⟨ValidTmS.lam laws (validPi.validTy (sound.isUniverse hu)) validBody, trivial,
        partsPi', SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | appElim _ _ ihG ihA =>
      intro ctx
      obtain ⟨validG, _, partsPi, spineG⟩ := ihG ctx
      obtain ⟨_, tyB, partsB⟩ := partsPi
      obtain ⟨validA, partsa, _⟩ := ihA ctx
      refine ⟨?_, trivial, ?_, SpineFactsR.app laws spineG validA⟩
      · rw [Presentation.Tm.mapConst_inst0]
        exact ValidTmS.app laws validG validA tyB
      · rw [Presentation.Tm.mapConst_inst0]
        exact StructuredS.inst0 partsB validA partsa
  | pairIntro _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      obtain ⟨validA, _, _⟩ := ihA ctx
      obtain ⟨validB, _, _⟩ := ihB ctx
      rw [Presentation.Tm.mapConst_inst0] at validB
      exact ⟨ValidTmS.pair laws (validS.validTy (sound.isUniverse hu)) validA validB,
        trivial, partsS, SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | fstElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS, _⟩ := ih ctx
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      exact ⟨ValidTmS.fst laws valid tyA, trivial, partsA,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | sndElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS, _⟩ := ih ctx
      obtain ⟨⟨tyA, _⟩, tyB, partsB⟩ := partsS
      refine ⟨?_, trivial, ?_,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
      · rw [Presentation.Tm.mapConst_inst0]
        exact ValidTmS.snd laws valid tyA tyB
      · rw [Presentation.Tm.mapConst_inst0]
        exact StructuredS.inst0 partsB (ValidTmS.fst laws valid tyA) trivial
  | idForm _ hu _ _ ihA iha ihb =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      obtain ⟨valida, _, _⟩ := iha ctx
      obtain ⟨validb, _, _⟩ := ihb ctx
      have hu' := sound.isUniverse hu
      exact ⟨ValidTmS.idForm laws validA hu' valida validb,
        ⟨⟨validA.validTy hu', partsA⟩, valida, validb⟩, trivial,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | reflIntro _ ih =>
      intro ctx
      obtain ⟨valid, _, partsA, _⟩ := ih ctx
      have tyA : ValidTyS M _ _ := valid.1
      exact ⟨ValidTmS.refl laws valid, trivial, ⟨⟨tyA, partsA⟩, valid, valid⟩,
        SpineFactsR.of_ne (fun _ e => by cases e) (fun _ _ e => by cases e)⟩
  | sub _ _ ihT ihLe =>
      intro ctx
      obtain ⟨valid, parts, _, spine⟩ := ihT ctx
      obtain ⟨le, _, partsB, leStruct⟩ := ihLe ctx
      exact ⟨ValidTmS.below laws valid le, parts, partsB, SpineFactsR.below laws spine leStruct⟩
  | conv _ _ hu ihT ihE =>
      intro ctx
      obtain ⟨valid, parts, _, spine⟩ := ihT ctx
      obtain ⟨eq, _, partsB, _⟩ := ihE ctx
      have hu' := sound.isUniverse hu
      exact ⟨ValidTmS.conv laws valid eq hu', parts, partsB,
        SpineFactsR.below laws spine (ValidLeStructS.ofEq laws eq hu')⟩
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
      refine ⟨?_, trivial, trivial, ?_⟩
      · rw [Presentation.Tm.mapConst_inst0]
        exact ValidEqS.app laws eqF eqA tyB
      · rw [Presentation.Tm.mapConst_inst0]
        exact StructuredS.inst0 partsB eqA.1 partsa
  | pairCong _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      have partsS' := partsS
      obtain ⟨_, tyB, _⟩ := partsS
      obtain ⟨eqA, _, _, _⟩ := ihA ctx
      obtain ⟨eqB, _, _, _⟩ := ihB ctx
      rw [Presentation.Tm.mapConst_inst0] at eqB
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
      refine ⟨?_, trivial, trivial, ?_⟩
      · rw [Presentation.Tm.mapConst_inst0]
        exact ValidEqS.snd laws eq tyA tyB
      · rw [Presentation.Tm.mapConst_inst0]
        exact StructuredS.inst0 partsB (ValidTmS.fst laws eq.1 tyA) trivial
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
      refine ⟨?_, trivial, ?_, ?_⟩
      · rw [Presentation.Tm.mapConst_inst0, Presentation.Tm.mapConst_inst0]
        exact ValidEqS.beta laws validBody validA
      · rw [Presentation.Tm.mapConst_inst0]
        exact StructuredS.inst0 partsBody validA partsa
      · rw [Presentation.Tm.mapConst_inst0]
        exact StructuredS.inst0 partsB validA partsa
  | betaFst _ _ _ _ _ ihA ihB =>
      intro ctx
      obtain ⟨validA, partsa, partsA, _⟩ := ihA ctx
      obtain ⟨validB, _, _⟩ := ihB ctx
      rw [Presentation.Tm.mapConst_inst0] at validB
      exact ⟨ValidEqS.betaFst laws validA validB, trivial, partsa, partsA⟩
  | betaSnd _ _ _ _ _ ihA ihB =>
      intro ctx
      obtain ⟨validA, _, _⟩ := ihA ctx
      obtain ⟨validB, partsb, partsB, _⟩ := ihB ctx
      rw [Presentation.Tm.mapConst_inst0] at validB partsB ⊢
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
      simp only [Presentation.Tm.mapConst, Presentation.Tm.mapConst_rename] at eqApps
      exact ⟨ValidEqS.etaPi laws validF validG eqApps, partsF, partsG, partsPi'⟩
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      intro ctx
      obtain ⟨validP, partsP, partsS, _⟩ := ihP ctx
      obtain ⟨validQ, partsQ, _⟩ := ihQ ctx
      obtain ⟨eqFst, _, _, _⟩ := ihFst ctx
      obtain ⟨eqSnd, _, _, _⟩ := ihSnd ctx
      simp only [Presentation.Tm.mapConst, Presentation.Tm.mapConst_inst0] at eqSnd
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

/-! ## Typings, contexts and strong normalization through a renaming -/

/-- A derivable typing is valid once renamed, in a renamed context that is valid
with its parts. -/
theorem Typed.validSR {R : Rules Head} {f : DeclName → DeclName} (sound : TypedSoundSR R M f)
    {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (typing : Typed R Γ t A)
    (ctx : ValidCtxSS M (Γ.mapConst f)) :
    ValidTmS M (Γ.mapConst f) (t.mapConst f) (A.mapConst f) :=
  (Derivable.validTSR sound typing ctx).1

/-- A derivable typing has the typing facts of spines read through the
renaming. -/
theorem Typed.spineFactsR {R : Rules Head} {f : DeclName → DeclName}
    (sound : TypedSoundSR R M f) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typed R Γ t A) (ctx : ValidCtxSS M (Γ.mapConst f)) :
    SpineFactsR R M f Γ t A :=
  (Derivable.validTSR sound typing ctx).2.2.2

/-- A formed context is valid with its parts once renamed. -/
theorem CtxFormed.validSR {R : Rules Head} {f : DeclName → DeclName}
    (sound : TypedSoundSR R M f) :
    ∀ {n : Nat} {Γ : Ctx Head n}, CtxFormed R Γ → ValidCtxSS M (Γ.mapConst f)
  | _, _, .nil => trivial
  | _, _, .snoc formed ⟨_, hu, typedA⟩ => by
      have ctx := CtxFormed.validSR sound formed
      obtain ⟨validA, partsA, _⟩ := Derivable.validTSR sound typedA ctx
      exact ⟨ctx, validA.validTy (sound.isUniverse hu), partsA⟩

/-- **Strong normalization through a renaming.** Every term typed in a formed
context is strongly normalizing once renamed, and so is its type. -/
theorem Typed.snR {R : Rules Head} {f : DeclName → DeclName} (sound : TypedSoundSR R M f)
    {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (formed : CtxFormed R Γ)
    (typed : Typed R Γ t A) :
    SN M.realizers.rules (t.mapConst f) ∧ SN M.realizers.rules (A.mapConst f) :=
  have ctx := CtxFormed.validSR sound formed
  (Typed.validSR sound typed ctx).normalizes sound.laws ctx.valid

/-- Both sides of a derivable equality in a formed context are strongly
normalizing once renamed, and so is their type. -/
theorem Equal.snR {R : Rules Head} {f : DeclName → DeclName} (sound : TypedSoundSR R M f)
    {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} (formed : CtxFormed R Γ)
    (equal : Derivable R (.equality Γ a b A)) :
    SN M.realizers.rules (a.mapConst f) ∧ SN M.realizers.rules (b.mapConst f) ∧
      SN M.realizers.rules (A.mapConst f) :=
  have ctx := CtxFormed.validSR sound formed
  (Derivable.validTSR sound equal ctx).1.normalizes sound.laws ctx.valid

/-! ## Reading the facts of a renamed spine in a package -/

/-- **The facts of a spine read through a renaming are the facts of the renamed
spine** in a package that declares the renamed head at the renamed type. -/
theorem SpineFactsR.spineFacts {R R₀ : Rules Head} {f : DeclName → DeclName} {n : Nat}
    {Γ : Ctx Head n} {c : DeclName} {args : List (Tm Head n)} {A : Tm Head n}
    (facts : SpineFactsR R M f Γ (appSpine (.const c) args) A)
    (agrees : ∀ {T₀ : Tm Head 0}, R₀.constantType (f c) = some T₀ →
      ∃ T, R.constantType c = some T ∧ T.mapConst f = T₀) :
    SpineFacts R₀ M (Γ.mapConst f) ((appSpine (.const c) args).mapConst f) (A.mapConst f) := by
  intro c' args' T₀ e declared₀ m r ξ σ σ' ς eq
  rw [Tm.mapConst_appSpine] at e
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
  obtain ⟨T, declared, rfl⟩ := agrees declared₀
  have h := facts rfl declared eq
  simp only [List.map_map, Function.comp_def] at h ⊢
  exact h

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
