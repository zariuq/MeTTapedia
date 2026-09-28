import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypeInclusion

/-!
# The fundamental lemma

Every derivable statement is valid: in a valid context a derivable typing is a
valid term at a valid type, and a derivable equality is a valid equality. The
model is built over the given generic equality, and the declared constants are
assumed semantic.

Every formed context is valid, and the identity substitution of a formed
context is valid, so derivable statements escape to the generic equality at
their own context: this is where the consequences come from.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- What a statement means in the model. -/
def StatementValid (S : Setting Head L) : Statement Head → Prop
  | .typing Γ t A => ValidCtx S Γ → ValidTm S Γ t A
  | .equality Γ a b A => ValidCtx S Γ → ValidEq S Γ a b A
  | .sub Γ A B => ValidCtx S Γ → ValidTyLe S Γ A B

/-- A rule package with the model's universe rules, and some of its constants and
root computations. -/
structure RulesSub (R' R : Rules Head) : Prop where
  headTyping : ∀ {h u : Head}, R'.headTyping h u → R.headTyping h u
  isUniverse : ∀ {u : Head}, R'.isUniverse u → R.isUniverse u
  join : ∀ {u v w : Head}, R'.join u v w → R.join u v w
  cumulative : ∀ {u v : Head}, R'.cumulative u v → R.cumulative u v
  headEq : ∀ {h h' : Head}, R'.headEq h h' → R.headEq h h'
  constantType : ∀ {name : DeclName} {type : Tm Head 0},
    R'.constantType name = some type → R.constantType name = some type
  computation : ∀ {n : Nat} {l r : Tm Head n}, R'.computation.step l r → R.computation.step l r

theorem RulesSub.refl (R : Rules Head) : RulesSub R R :=
  ⟨id, id, id, id, id, id, id⟩

/-- A package contained in one contained in a third is contained in the third. -/
theorem RulesSub.trans {R₁ R₂ R₃ : Rules Head} (first : RulesSub R₁ R₂)
    (second : RulesSub R₂ R₃) : RulesSub R₁ R₃ :=
  ⟨fun h => second.headTyping (first.headTyping h), fun h => second.isUniverse (first.isUniverse h),
    fun h => second.join (first.join h), fun h => second.cumulative (first.cumulative h),
    fun h => second.headEq (first.headEq h), fun h => second.constantType (first.constantType h),
    fun h => second.computation (first.computation h)⟩

/-- Derivations persist into a larger rule package. -/
theorem Derivable.mono {R' R : Rules Head} (sub : RulesSub R' R) {st : Statement Head}
    (derivation : Derivable R' st) : Derivable R st := by
  induction derivation with
  | headType typing => exact .headType (sub.headTyping typing)
  | var i => exact .var i
  | const declared _ hu ih => exact .const (sub.constantType declared) ih (sub.isUniverse hu)
  | piForm _ hu _ hv join ihA ihB =>
      exact .piForm ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      exact .sigmaForm ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | lamIntro _ hu _ ihPi ihBody => exact .lamIntro ihPi (sub.isUniverse hu) ihBody
  | appElim _ _ ihF ihA => exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS ihA ihB => exact .pairIntro ihS (sub.isUniverse hu) ihA ihB
  | fstElim _ ih => exact .fstElim ih
  | sndElim _ ih => exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb => exact .idForm ihA (sub.isUniverse hu) iha ihb
  | reflIntro _ ih => exact .reflIntro ih
  | conv _ _ hu ihT ihE => exact .conv ihT ihE (sub.isUniverse hu)
  | refl _ ih => exact .refl ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihT => exact .convEq ih ihT (sub.isUniverse hu)
  | headEq same _ _ ih ih' => exact .headEq (sub.headEq same) ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      exact .piCong ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      exact .sigmaCong ihA (sub.isUniverse hu) ihB (sub.isUniverse hv) (sub.join join)
  | idCong _ hu _ _ ihA iha ihb => exact .idCong ihA (sub.isUniverse hu) iha ihb
  | lamCong _ hu _ ihPi ihBody => exact .lamCong ihPi (sub.isUniverse hu) ihBody
  | appCong _ _ ihF ihA => exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS ihA ihB => exact .pairCong ihS (sub.isUniverse hu) ihA ihB
  | fstCong _ ih => exact .fstCong ih
  | sndCong _ ih => exact .sndCong ih
  | reflCong _ ih => exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody ihA => exact .betaPi ihPi (sub.isUniverse hu) ihBody ihA
  | betaFst _ hu _ _ ihS ihA ihB => exact .betaFst ihS (sub.isUniverse hu) ihA ihB
  | betaSnd _ hu _ _ ihS ihA ihB => exact .betaSnd ihS (sub.isUniverse hu) ihA ihB
  | root step _ _ ihL ihR => exact .root (sub.computation step) ihL ihR
  | etaPi _ _ _ ihF ihG ihApps => exact .etaPi ihF ihG ihApps
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd => exact .etaSigma ihP ihQ ihFst ihSnd
  | sub _ _ ihT ihLe => exact .sub ihT ihLe
  | subEq _ _ ihE ihLe => exact .subEq ihE ihLe
  | subEqual _ hu ih => exact .subEqual ih (sub.isUniverse hu)
  | subUniv c => exact .subUniv (sub.cumulative c)
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      exact .subPi ihPi (sub.isUniverse hu) ihPi' (sub.isUniverse hu') ihA (sub.isUniverse hw) ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      exact .subSigma ihS (sub.isUniverse hu) ihS' (sub.isUniverse hu') ihA ihB
  | subTrans _ _ ih₁ ih₂ => exact .subTrans ih₁ ih₂

section Fundamental

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The fundamental lemma, for derivations of a rule package inside the model's
whose constants are semantic. -/
theorem Derivable.valid_sub {R' : Rules Head} (sub : RulesSub R' S.R)
    (constants' : SemanticConstantsOf S R') {st : Statement Head}
    (derivation : Derivable R' st) : StatementValid S st := by
  induction derivation with
  | headType typing => exact fun _ => ValidTm.headType laws (sub.headTyping typing)
  | var i => exact fun valid => ValidTm.var laws valid i
  | const declared typing hu ihType =>
      exact fun _ => ValidTm.const laws (ihType trivial) (sub.isUniverse hu)
        (constants' declared typing hu)
  | piForm _ hu _ hv join ihA ihB =>
      intro valid
      have validA := ihA valid
      exact ValidTm.pi laws validA (sub.isUniverse hu)
        (ihB ⟨valid, validA.validTy laws (sub.isUniverse hu)⟩) (sub.isUniverse hv) (sub.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro valid
      have validA := ihA valid
      exact ValidTm.sigma laws validA (sub.isUniverse hu)
        (ihB ⟨valid, validA.validTy laws (sub.isUniverse hu)⟩) (sub.isUniverse hv) (sub.join join)
  | lamIntro _ hu _ ihPi ihBody =>
      intro valid
      have validPi := ihPi valid
      exact ValidTm.lam laws validPi (sub.isUniverse hu)
        (ihBody ⟨valid, ((validPi.validTy laws (sub.isUniverse hu)).pi_inv laws).1⟩)
  | appElim _ _ ihG ihA => exact fun valid => ValidTm.app laws (ihG valid) (ihA valid)
  | pairIntro _ hu _ _ ihSigma ihA ihB =>
      exact fun valid => ValidTm.pair laws (ihSigma valid) (sub.isUniverse hu) (ihA valid) (ihB valid)
  | fstElim _ ih => exact fun valid => (ih valid).fst laws
  | sndElim _ ih => exact fun valid => (ih valid).snd laws
  | idForm _ hu _ _ ihA iha ihb =>
      exact fun valid => ValidTm.ident laws (ihA valid) (sub.isUniverse hu) (iha valid) (ihb valid)
  | reflIntro _ ih => exact fun valid => (ih valid).refl laws
  | conv _ _ hu ihT ihE =>
      exact fun valid => (ihT valid).conv laws ((ihE valid).tyEq laws (sub.isUniverse hu))
  | refl _ ih => exact fun valid => (ih valid).eq_self
  | symm _ ih => exact fun valid => (ih valid).symm laws
  | trans _ _ ih₁ ih₂ => exact fun valid => (ih₁ valid).trans laws (ih₂ valid)
  | convEq _ _ hu ih ihT =>
      exact fun valid => (ih valid).conv laws ((ihT valid).tyEq laws (sub.isUniverse hu))
  | sub _ _ ihT ihLe => exact fun valid => (ihT valid).below (ihLe valid)
  | subEq _ _ ihE ihLe => exact fun valid => (ihE valid).below (ihLe valid)
  | subEqual e hu ihE =>
      exact fun valid => ValidTyLe.ofEq laws (.subEqual (Derivable.mono sub e) (sub.isUniverse hu))
        ((ihE valid).tyEq laws (sub.isUniverse hu))
  | subUniv c => exact fun _ => ValidTyLe.univ laws (sub.cumulative c)
  | subTrans _ _ ih₁ ih₂ => exact fun valid => (ih₁ valid).trans (ih₂ valid)
  | subPi tPi hu tPi' hu' eA hw leB ihPi ihPi' ihA ihB =>
      intro valid
      have eqA := (ihA valid).tyEq laws (sub.isUniverse hw)
      exact ValidTyLe.pi laws
        (.subPi (Derivable.mono sub tPi) (sub.isUniverse hu) (Derivable.mono sub tPi')
          (sub.isUniverse hu') (Derivable.mono sub eA) (sub.isUniverse hw)
          (Derivable.mono sub leB))
        ((ihPi valid).validTy laws (sub.isUniverse hu))
        ((ihPi' valid).validTy laws (sub.isUniverse hu')) eqA (ihB ⟨valid, eqA.left⟩)
  | subSigma tS hu tS' hu' leA leB ihS ihS' ihA ihB =>
      intro valid
      have leAv := ihA valid
      exact ValidTyLe.sigma laws
        (.subSigma (Derivable.mono sub tS) (sub.isUniverse hu) (Derivable.mono sub tS')
          (sub.isUniverse hu') (Derivable.mono sub leA) (Derivable.mono sub leB))
        ((ihS valid).validTy laws (sub.isUniverse hu))
        ((ihS' valid).validTy laws (sub.isUniverse hu')) leAv (ihB ⟨valid, leAv.left⟩)
  | headEq same _ _ ih ih' =>
      exact fun valid => ValidEq.headEq laws (sub.headEq same) (ih valid) (ih' valid)
  | piCong _ hu _ hv join ihA ihB =>
      intro valid
      have equalA := ihA valid
      exact ValidEq.pi laws equalA (sub.isUniverse hu)
        (ihB ⟨valid, equalA.left.validTy laws (sub.isUniverse hu)⟩) (sub.isUniverse hv)
        (sub.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      intro valid
      have equalA := ihA valid
      exact ValidEq.sigma laws equalA (sub.isUniverse hu)
        (ihB ⟨valid, equalA.left.validTy laws (sub.isUniverse hu)⟩) (sub.isUniverse hv)
        (sub.join join)
  | idCong _ hu _ _ ihA iha ihb =>
      exact fun valid => ValidEq.ident laws (ihA valid) (sub.isUniverse hu) (iha valid) (ihb valid)
  | lamCong _ hu _ ihPi ihBody =>
      intro valid
      have validPi := ihPi valid
      exact ValidEq.lam laws validPi (sub.isUniverse hu)
        (ihBody ⟨valid, ((validPi.validTy laws (sub.isUniverse hu)).pi_inv laws).1⟩)
  | appCong _ _ ihF ihA => exact fun valid => ValidEq.app laws (ihF valid) (ihA valid)
  | pairCong _ hu _ _ ihSigma ihA ihB =>
      exact fun valid => ValidEq.pair laws (ihSigma valid) (sub.isUniverse hu) (ihA valid) (ihB valid)
  | fstCong _ ih => exact fun valid => (ih valid).fst laws
  | sndCong _ ih => exact fun valid => (ih valid).snd laws
  | reflCong _ ih => exact fun valid => (ih valid).refl laws
  | betaPi _ hu _ _ ihPi ihBody ihA =>
      intro valid
      have validPi := ihPi valid
      exact ValidEq.beta laws validPi (sub.isUniverse hu)
        (ihBody ⟨valid, ((validPi.validTy laws (sub.isUniverse hu)).pi_inv laws).1⟩) (ihA valid)
  | betaFst _ hu _ _ ihSigma ihA ihB =>
      exact fun valid => ValidEq.betaFst laws (ihSigma valid) (sub.isUniverse hu) (ihA valid)
        (ihB valid)
  | betaSnd _ hu _ _ ihSigma ihA ihB =>
      exact fun valid => ValidEq.betaSnd laws (ihSigma valid) (sub.isUniverse hu) (ihA valid)
        (ihB valid)
  | root step _ _ ihL ihR =>
      exact fun valid => ValidEq.root laws (sub.computation step) (ihL valid) (ihR valid)
  | etaPi _ _ _ ihF ihG ihApps =>
      intro valid
      have validF := ihF valid
      exact ValidEq.etaPi laws validF (ihG valid) (ihApps ⟨valid, (validF.type.pi_inv laws).1⟩)
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      exact fun valid => ValidEq.etaSigma laws (ihP valid) (ihQ valid) (ihFst valid) (ihSnd valid)

variable (constants : SemanticConstants S)
include constants

/-- The fundamental lemma. -/
theorem Derivable.valid {st : Statement Head} (derivation : Derivable S.R st) :
    StatementValid S st :=
  Derivable.valid_sub laws (RulesSub.refl S.R) constants derivation

theorem Typed.valid {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typed S.R Γ t A) (valid : ValidCtx S Γ) : ValidTm S Γ t A :=
  Derivable.valid laws constants typing valid

theorem Equal.valid {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (equal : Equal S.R Γ a b A) (valid : ValidCtx S Γ) : ValidEq S Γ a b A :=
  Derivable.valid laws constants equal valid

/-- Every formed context is valid. -/
theorem CtxFormed.valid {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ValidCtx S Γ := by
  induction formed with
  | nil => trivial
  | snoc _ type ih =>
      obtain ⟨u, hu, typing⟩ := type
      exact ⟨ih, (Typed.valid laws constants typing ih).validTy laws hu⟩

end Fundamental

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
