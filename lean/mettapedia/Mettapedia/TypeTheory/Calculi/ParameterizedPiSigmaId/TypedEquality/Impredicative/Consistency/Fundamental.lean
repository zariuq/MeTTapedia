import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Functions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Pairs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Equality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Formers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Root
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Telescopes

/-!
# The fundamental lemma of the consistency model

Every derivable statement of an object package is valid in the model when the
package is sound for it: its universe rules are the model's, each of its root
steps preserves meaning, and each of its constants is a valid term of its
declared type. A root step can preserve meaning by being a step of the model's
own computation, or, for a decoding of a code, by the coherence of the two
interpretations.

Along with each judgment the lemma carries the valid parts of its subjects and
types written as type formers (`Structured`). The rules that need the parts of
a dependent function or pair type have that type written in one of their
premises, whose derivation supplies them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization
open TelescopeAbstraction (closeType applyClosed applyClosed_subst)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-- What a statement means in the model, with the valid parts of its subjects
and types. -/
def StatementValidS (M : Model Head L) : Statement Head → Prop
  | .typing Γ t A => ValidCtxS M Γ → ValidTm M Γ t A ∧ Structured M Γ t ∧ Structured M Γ A
  | .equality Γ a b A => ValidCtxS M Γ →
      ValidEq M Γ a b A ∧ Structured M Γ a ∧ Structured M Γ b ∧ Structured M Γ A
  | .sub Γ A B => ValidCtxS M Γ → ValidLe M Γ A B ∧ Structured M Γ A ∧ Structured M Γ B

/-- A root step preserves meaning when its two sides are validly equal wherever
each is a valid term of one type. -/
def RootSemantic (M : Model Head L) {n : Nat} (l r : Tm Head n) : Prop :=
  ∀ {Γ : Ctx Head n} {A : Tm Head n}, ValidTm M Γ l A → ValidTm M Γ r A → ValidEq M Γ l r A

/-- A root step read in the model, as a step of the model's own computation or
a decoding of its codes, preserves meaning. -/
theorem ModelRoot.semantic (laws : M.Laws) {D : Decoders Head} (decodes : Decodes M D)
    {n : Nat} {l r : Tm Head n} (root : ModelRoot M D l r) : RootSemantic M l r :=
  fun validL validR => ValidEq.root laws decodes root validL validR

/-- An object package sound for the model: its universe rules are the model's,
each of its root steps preserves meaning, and each of its constants is a valid
term of its declared type. These are local obligations, one per rule, step and
constant; the fundamental lemma below consumes them. -/
structure Sound (R : Rules Head) (M : Model Head L) : Prop where
  laws : M.Laws
  headTyping : ∀ {h u : Head}, R.headTyping h u → M.rules.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → M.rules.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → M.rules.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → M.rules.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → M.rules.headEq h h'
  root : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r → RootSemantic M l r
  constants : ∀ {name : DeclName} {type : Tm Head 0}, R.constantType name = some type →
    ValidTm M .nil (.const name) type

/-- Structure of a type is kept by conversion of the context it lives in. -/
theorem Structured.convert (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {u : Head} (ctx : ValidCtx M Γ) (eqA : ValidEq M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) {B : Tm Head (n + 1)} (parts : Structured M (.snoc Γ A) B) :
    Structured M (.snoc Γ A') B := by
  have converted := Structured.subst B parts (ValidMor.convert laws ctx eqA hu) fun _ => trivial
  rwa [subst_ids] at converted

theorem ValidTm.convert (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {u : Head} (ctx : ValidCtx M Γ) (eqA : ValidEq M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) {t B : Tm Head (n + 1)} (valid : ValidTm M (.snoc Γ A) t B) :
    ValidTm M (.snoc Γ A') t B := by
  have converted := valid.subst (ValidMor.convert laws ctx eqA hu)
  rwa [subst_ids, subst_ids] at converted

/-- The fundamental lemma: every derivable statement of a sound object package
is valid in the model. -/
theorem Derivable.valid {R : Rules Head}
    (sound : Sound R M) {st : Statement Head} (derivation : Derivable R st) :
    StatementValidS M st := by
  have laws := sound.laws
  induction derivation with
  | headType typing =>
      exact fun _ => ⟨ValidTm.headType laws (sound.headTyping typing), trivial, trivial⟩
  | var i =>
      intro ctx
      exact ⟨ValidTm.var laws ctx i, trivial, (ctx.lookup i).2⟩
  | const declared _ _ ihType =>
      intro _
      obtain ⟨_, partsType, _⟩ := ihType trivial
      exact ⟨(sound.constants declared).rename (ValidRen.elim0 _), trivial,
        Structured.liftClosed partsType _⟩
  | piForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have tyA : ValidTy M _ _ := validA.validTy hu'
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have hv' := sound.isUniverse hv
      exact ⟨ValidTm.piForm laws validA hu' validB hv' (sound.join join),
        ⟨⟨tyA, partsA⟩, validB.validTy hv', partsB⟩, trivial⟩
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have tyA : ValidTy M _ _ := validA.validTy hu'
      obtain ⟨validB, partsB, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have hv' := sound.isUniverse hv
      exact ⟨ValidTm.sigmaForm laws validA hu' validB hv' (sound.join join),
        ⟨⟨tyA, partsA⟩, validB.validTy hv', partsB⟩, trivial⟩
  | lamIntro _ hu _ ihPi ihBody =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨validBody, _, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      exact ⟨ValidTm.lam laws (validPi.validTy (sound.isUniverse hu)) validBody, trivial, partsPi'⟩
  | appElim _ _ ihG ihA =>
      intro ctx
      obtain ⟨validG, _, partsPi⟩ := ihG ctx
      obtain ⟨_, tyB, partsB⟩ := partsPi
      obtain ⟨validA, partsa, _⟩ := ihA ctx
      exact ⟨ValidTm.app laws validG validA tyB, trivial, Structured.inst0 partsB validA partsa⟩
  | pairIntro _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      obtain ⟨validA, _, _⟩ := ihA ctx
      obtain ⟨validB, _, _⟩ := ihB ctx
      exact ⟨ValidTm.pair laws (validS.validTy (sound.isUniverse hu)) validA validB,
        trivial, partsS⟩
  | fstElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      exact ⟨ValidTm.fst laws valid tyA, trivial, partsA⟩
  | sndElim _ ih =>
      intro ctx
      obtain ⟨valid, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, _⟩, tyB, partsB⟩ := partsS
      exact ⟨ValidTm.snd laws valid tyA tyB, trivial,
        Structured.inst0 partsB (ValidTm.fst laws valid tyA) trivial⟩
  | idForm _ hu _ _ ihA iha ihb =>
      intro ctx
      obtain ⟨validA, partsA, _⟩ := ihA ctx
      obtain ⟨valida, _, _⟩ := iha ctx
      obtain ⟨validb, _, _⟩ := ihb ctx
      have hu' := sound.isUniverse hu
      exact ⟨ValidTm.idForm laws validA hu' valida validb,
        ⟨⟨validA.validTy hu', partsA⟩, valida, validb⟩, trivial⟩
  | reflIntro _ ih =>
      intro ctx
      obtain ⟨valid, _, partsA⟩ := ih ctx
      have tyA : ValidTy M _ _ := valid.1
      exact ⟨ValidTm.refl laws valid, trivial, ⟨⟨tyA, partsA⟩, valid, valid⟩⟩
  | sub _ _ ihT ihLe =>
      intro ctx
      obtain ⟨valid, parts, _⟩ := ihT ctx
      obtain ⟨le, _, partsB⟩ := ihLe ctx
      exact ⟨ValidTm.below valid le, parts, partsB⟩
  | conv _ _ hu ihT ihE =>
      intro ctx
      obtain ⟨valid, parts, _⟩ := ihT ctx
      obtain ⟨eq, _, partsB, _⟩ := ihE ctx
      exact ⟨ValidTm.conv laws valid eq (sound.isUniverse hu), parts, partsB⟩
  | refl _ ih =>
      intro ctx
      obtain ⟨valid, parts, partsA⟩ := ih ctx
      exact ⟨ValidEq.refl valid, parts, parts, partsA⟩
  | symm _ ih =>
      intro ctx
      obtain ⟨eq, partsL, partsR, partsA⟩ := ih ctx
      exact ⟨ValidEq.symm laws eq, partsR, partsL, partsA⟩
  | trans _ _ ih₁ ih₂ =>
      intro ctx
      obtain ⟨eq₁, partsL, _, partsA⟩ := ih₁ ctx
      obtain ⟨eq₂, _, partsR, _⟩ := ih₂ ctx
      exact ⟨ValidEq.trans laws eq₁ eq₂, partsL, partsR, partsA⟩
  | convEq _ _ hu ih ihT =>
      intro ctx
      obtain ⟨eq, partsL, partsR, _⟩ := ih ctx
      obtain ⟨eqT, _, partsB, _⟩ := ihT ctx
      exact ⟨ValidEq.conv laws eq eqT (sound.isUniverse hu), partsL, partsR, partsB⟩
  | subEq _ _ ihE ihLe =>
      intro ctx
      obtain ⟨eq, partsL, partsR, _⟩ := ihE ctx
      obtain ⟨le, _, partsB⟩ := ihLe ctx
      exact ⟨ValidEq.below eq le, partsL, partsR, partsB⟩
  | headEq same _ _ ih ih' =>
      intro ctx
      obtain ⟨valid, _, partsA⟩ := ih ctx
      obtain ⟨valid', _, _⟩ := ih' ctx
      exact ⟨ValidEq.headEq laws (sound.headEq same) valid valid', trivial, trivial, partsA⟩
  | piCong _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have hv' := sound.isUniverse hv
      have tyA : ValidTy M _ _ := eqA.1.validTy hu'
      obtain ⟨eqB, partsB, partsB', _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have validB' := ValidTm.convert laws ctx.valid eqA hu' eqB.2.1
      exact ⟨ValidEq.piCong laws eqA hu' eqB hv' (sound.join join)
          (ValidTm.piForm laws eqA.2.1 hu' validB' hv' (sound.join join)),
        ⟨⟨tyA, partsA⟩, eqB.1.validTy hv', partsB⟩,
        ⟨⟨eqA.2.1.validTy hu', partsA'⟩, validB'.validTy hv',
          Structured.convert laws ctx.valid eqA hu' partsB'⟩, trivial⟩
  | sigmaCong _ hu _ hv join ihA ihB =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      have hu' := sound.isUniverse hu
      have hv' := sound.isUniverse hv
      have tyA : ValidTy M _ _ := eqA.1.validTy hu'
      obtain ⟨eqB, partsB, partsB', _⟩ := ihB ⟨ctx, tyA, partsA⟩
      have validB' := ValidTm.convert laws ctx.valid eqA hu' eqB.2.1
      exact ⟨ValidEq.sigmaCong laws eqA hu' eqB hv' (sound.join join)
          (ValidTm.sigmaForm laws eqA.2.1 hu' validB' hv' (sound.join join)),
        ⟨⟨tyA, partsA⟩, eqB.1.validTy hv', partsB⟩,
        ⟨⟨eqA.2.1.validTy hu', partsA'⟩, validB'.validTy hv',
          Structured.convert laws ctx.valid eqA hu' partsB'⟩, trivial⟩
  | idCong _ hu _ _ ihA iha ihb =>
      intro ctx
      obtain ⟨eqA, partsA, partsA', _⟩ := ihA ctx
      obtain ⟨eqa, _, _, _⟩ := iha ctx
      obtain ⟨eqb, _, _, _⟩ := ihb ctx
      have hu' := sound.isUniverse hu
      have valida' := ValidTm.conv laws eqa.2.1 eqA hu'
      have validb' := ValidTm.conv laws eqb.2.1 eqA hu'
      exact ⟨ValidEq.idCong laws eqA hu' eqa eqb (ValidTm.idForm laws eqA.2.1 hu' valida' validb'),
        ⟨⟨eqA.1.validTy hu', partsA⟩, eqa.1, eqb.1⟩,
        ⟨⟨eqA.2.1.validTy hu', partsA'⟩, valida', validb'⟩, trivial⟩
  | lamCong _ hu _ ihPi ihBody =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨eqBody, _, _, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      exact ⟨ValidEq.lam laws (validPi.validTy (sound.isUniverse hu)) eqBody, trivial, trivial,
        partsPi'⟩
  | appCong _ _ ihF ihA =>
      intro ctx
      obtain ⟨eqF, _, _, partsPi⟩ := ihF ctx
      obtain ⟨_, tyB, partsB⟩ := partsPi
      obtain ⟨eqA, partsa, _, _⟩ := ihA ctx
      exact ⟨ValidEq.app laws eqF eqA tyB, trivial, trivial,
        Structured.inst0 partsB eqA.1 partsa⟩
  | pairCong _ hu _ _ ihS ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      have partsS' := partsS
      obtain ⟨_, tyB, _⟩ := partsS
      obtain ⟨eqA, _, _, _⟩ := ihA ctx
      obtain ⟨eqB, _, _, _⟩ := ihB ctx
      exact ⟨ValidEq.pair laws (validS.validTy (sound.isUniverse hu)) tyB eqA eqB,
        trivial, trivial, partsS'⟩
  | fstCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      exact ⟨ValidEq.fst laws eq tyA, trivial, trivial, partsA⟩
  | sndCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsS⟩ := ih ctx
      obtain ⟨⟨tyA, _⟩, tyB, partsB⟩ := partsS
      exact ⟨ValidEq.snd laws eq tyA tyB, trivial, trivial,
        Structured.inst0 partsB (ValidTm.fst laws eq.1 tyA) trivial⟩
  | reflCong _ ih =>
      intro ctx
      obtain ⟨eq, _, _, partsA⟩ := ih ctx
      have tyA : ValidTy M _ _ := eq.1.1
      exact ⟨ValidEq.reflCong laws eq, trivial, trivial, ⟨⟨tyA, partsA⟩, eq.1, eq.1⟩⟩
  | betaPi _ _ _ _ ihPi ihBody ihA =>
      intro ctx
      obtain ⟨_, partsPi, _⟩ := ihPi ctx
      obtain ⟨⟨tyA, partsA⟩, _, partsB⟩ := partsPi
      obtain ⟨validBody, partsBody, _⟩ := ihBody ⟨ctx, tyA, partsA⟩
      obtain ⟨validA, partsa, _⟩ := ihA ctx
      exact ⟨ValidEq.beta validBody validA, trivial,
        Structured.inst0 partsBody validA partsa, Structured.inst0 partsB validA partsa⟩
  | betaFst _ _ _ _ _ ihA _ =>
      intro ctx
      obtain ⟨validA, partsa, partsA⟩ := ihA ctx
      exact ⟨ValidEq.betaFst validA, trivial, partsa, partsA⟩
  | betaSnd _ _ _ _ _ _ ihB =>
      intro ctx
      obtain ⟨validB, partsb, partsB⟩ := ihB ctx
      exact ⟨ValidEq.betaSnd validB, trivial, partsb, partsB⟩
  | root step _ _ ihL ihR =>
      intro ctx
      obtain ⟨validL, partsL, partsA⟩ := ihL ctx
      obtain ⟨validR, partsR, _⟩ := ihR ctx
      exact ⟨sound.root step validL validR, partsL, partsR,
        partsA⟩
  | etaPi _ _ _ ihF ihG ihApps =>
      intro ctx
      obtain ⟨validF, partsF, partsPi⟩ := ihF ctx
      have partsPi' := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨validG, partsG, _⟩ := ihG ctx
      obtain ⟨eqApps, _, _, _⟩ := ihApps ⟨ctx, tyA, partsA⟩
      exact ⟨ValidEq.etaPi laws validF validG eqApps, partsF, partsG, partsPi'⟩
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      intro ctx
      obtain ⟨validP, partsP, partsS⟩ := ihP ctx
      obtain ⟨validQ, partsQ, _⟩ := ihQ ctx
      obtain ⟨eqFst, _, _, _⟩ := ihFst ctx
      obtain ⟨eqSnd, _, _, _⟩ := ihSnd ctx
      exact ⟨ValidEq.etaSigma laws validP validQ eqFst eqSnd, partsP, partsQ, partsS⟩
  | subEqual _ hu ih =>
      intro ctx
      obtain ⟨eq, partsA, partsB, _⟩ := ih ctx
      exact ⟨ValidLe.ofEq laws eq (sound.isUniverse hu), partsA, partsB⟩
  | subUniv c => exact fun _ => ⟨ValidLe.univ laws (sound.cumulative c), trivial, trivial⟩
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      intro ctx
      obtain ⟨validPi, partsPi, _⟩ := ihPi ctx
      obtain ⟨validPi', partsPi', _⟩ := ihPi' ctx
      have partsPiL := partsPi
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsPi
      obtain ⟨eqA, _, _, _⟩ := ihA ctx
      obtain ⟨leB, _, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      exact ⟨ValidLe.pi laws (validPi.validTy (sound.isUniverse hu))
          (validPi'.validTy (sound.isUniverse hu')) eqA (sound.isUniverse hw) leB,
        partsPiL, partsPi'⟩
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      intro ctx
      obtain ⟨validS, partsS, _⟩ := ihS ctx
      obtain ⟨validS', partsS', _⟩ := ihS' ctx
      have partsSL := partsS
      obtain ⟨⟨tyA, partsA⟩, _, _⟩ := partsS
      obtain ⟨leA, _, _⟩ := ihA ctx
      obtain ⟨leB, _, _⟩ := ihB ⟨ctx, tyA, partsA⟩
      exact ⟨ValidLe.sigma laws (validS.validTy (sound.isUniverse hu))
          (validS'.validTy (sound.isUniverse hu')) leA leB, partsSL, partsS'⟩
  | subTrans _ _ ih₁ ih₂ =>
      intro ctx
      obtain ⟨le₁, partsA, _⟩ := ih₁ ctx
      obtain ⟨le₂, _, partsC⟩ := ih₂ ctx
      exact ⟨ValidLe.trans le₁ le₂, partsA, partsC⟩

/-- A derivable typing of a sound package is valid in a context that is valid
with its parts. -/
theorem Typed.valid {R : Rules Head} (sound : Sound R M)
    {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (typing : Typed R Γ t A)
    (ctx : ValidCtxS M Γ) : ValidTm M Γ t A :=
  (Derivable.valid sound typing ctx).1

/-- A constant defined by one equation `f x₁ ⋯ x_k ⟶ rhs`, whose declared type
and right-hand side are typed in a sound package without it, is a valid term of
its declared type: its full application computes to the right-hand side, which
is valid by the fundamental lemma of that package. -/
theorem ValidTm.definition {R₀ : Rules Head}
    (sound₀ : Sound R₀ M) {f : DeclName} {k : Nat} {Θ : Ctx Head k} {C rhs : Tm Head k}
    (typed : ∃ w, R₀.isUniverse w ∧ Typed R₀ .nil (closeType Θ C) (.head w))
    (body : Typed R₀ Θ rhs C)
    (rule : ∀ {n : Nat} (σ : Sub Head k n),
      WhRed M.rules M.roles (applyClosed Θ σ (.const f)) (Presentation.subst σ rhs)) :
    ValidTm M .nil (.const f) (closeType Θ C) := by
  obtain ⟨w, hw, typedC⟩ := typed
  obtain ⟨validC, partsC, _⟩ := Derivable.valid sound₀ typedC trivial
  have validType : ValidTy M .nil (closeType Θ C) := validC.validTy (sound₀.isUniverse hw)
  obtain ⟨ctx, _, _⟩ := ValidTy.close_parts Θ validType partsC
  refine ValidTm.close sound₀.laws Θ validType partsC
    (ValidTm.of_red (fun σ => ?_) (Typed.valid sound₀ body ctx))
  rw [applyClosed_subst]
  exact rule σ

/-- In a package sound for the model, no closed term inhabits `holds c` for a
closed code `c` whose truth value is false. -/
theorem no_closed_proof {R : Rules Head} (sound : Sound R M)
    {c : Tm Head 0} {P : Prop} (truth : Truth M.reading World.closed c P) (false_ : ¬ P)
    (t : Tm Head 0) : ¬ Typed R .nil t (.app (.const M.holds) c) := by
  intro typing
  obtain ⟨validH, rel⟩ := Typed.valid sound typing trivial
  have e : EqSubst M .nil World.closed ids ids := trivial
  obtain ⟨R', den, _⟩ := validH e
  have related := rel e den
  rw [subst_ids] at den related
  obtain ⟨_, interp⟩ := den
  obtain ⟨rfl, _⟩ := InterpAt.holds_inv sound.laws interp
  obtain ⟨P', truth', holds⟩ := related
  rw [Truth.deterministic sound.laws.reading truth' truth] at holds
  exact false_ holds

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
