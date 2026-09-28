import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Judgment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws

/-!
# The typed judgments along morphisms of rule packages

A morphism of rule packages (`Rules.Morphism`) maps universe heads so that the
universe rules, the declared constants and the root computations of the
source hold in the target. Every derivable statement of the source, typing,
typed equality or subtyping, is derivable in the target after its heads are
mapped (`Derivable.mapHead`). This is the transport of the formation-sensitive
judgment (`FormationSensitive.Typing.mapHead`) for the selected judgment with
typed equality.

With the identity head map a morphism is an inclusion of packages, and the
statements are unchanged (`Typed.of_morphism`, `Equal.of_morphism`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

variable {HeadOne HeadTwo : Type}

/-- A statement with its heads mapped. -/
def Statement.mapHead (map : HeadOne → HeadTwo) : Statement HeadOne → Statement HeadTwo
  | .typing Γ t A => .typing (Γ.mapHead map) (t.mapHead map) (A.mapHead map)
  | .equality Γ a b A => .equality (Γ.mapHead map) (a.mapHead map) (b.mapHead map) (A.mapHead map)
  | .sub Γ A B => .sub (Γ.mapHead map) (A.mapHead map) (B.mapHead map)

/-- **Transport along a morphism of rule packages.** Every derivable statement
of the source package is derivable in the target package with its heads
mapped. -/
theorem Derivable.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map) {st : Statement HeadOne}
    (derivation : Derivable source st) : Derivable target (st.mapHead map) := by
  induction derivation with
  | headType typing => exact .headType (morphism.headTyping typing)
  | @var n Γ i =>
      simp only [Statement.mapHead, Tm.mapHead]
      rw [← Ctx.lookup_mapHead]
      exact .var i
  | const declared _ hu ihType =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_liftClosed, Ctx.mapHead] at ihType ⊢
      exact .const (morphism.constantType declared) ihType (morphism.isUniverse hu)
  | piForm _ hu _ hv join ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihA ihB ⊢
      exact .piForm ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv) (morphism.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihA ihB ⊢
      exact .sigmaForm ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv)
        (morphism.join join)
  | lamIntro _ hu _ ihPi ihBody =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihPi ihBody ⊢
      exact .lamIntro ihPi (morphism.isUniverse hu) ihBody
  | appElim _ _ ihF ihA =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ihF ihA ⊢
      exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .pairIntro ihS (morphism.isUniverse hu) ihA ihB
  | fstElim _ ih =>
      simp only [Statement.mapHead, Tm.mapHead] at ih ⊢
      exact .fstElim ih
  | sndElim _ ih =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ih ⊢
      exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb =>
      simp only [Statement.mapHead, Tm.mapHead] at ihA iha ihb ⊢
      exact .idForm ihA (morphism.isUniverse hu) iha ihb
  | reflIntro _ ih =>
      simp only [Statement.mapHead, Tm.mapHead] at ih ⊢
      exact .reflIntro ih
  | sub _ _ ihT ihLe =>
      simp only [Statement.mapHead] at ihT ihLe ⊢
      exact .sub ihT ihLe
  | conv _ _ hu ihT ihE =>
      simp only [Statement.mapHead, Tm.mapHead] at ihT ihE ⊢
      exact .conv ihT ihE (morphism.isUniverse hu)
  | refl _ ih =>
      simp only [Statement.mapHead] at ih ⊢
      exact .refl ih
  | symm _ ih =>
      simp only [Statement.mapHead] at ih ⊢
      exact .symm ih
  | trans _ _ ih₁ ih₂ =>
      simp only [Statement.mapHead] at ih₁ ih₂ ⊢
      exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihT =>
      simp only [Statement.mapHead, Tm.mapHead] at ih ihT ⊢
      exact .convEq ih ihT (morphism.isUniverse hu)
  | subEq _ _ ihE ihLe =>
      simp only [Statement.mapHead] at ihE ihLe ⊢
      exact .subEq ihE ihLe
  | headEq same _ _ ih ih' =>
      simp only [Statement.mapHead, Tm.mapHead] at ih ih' ⊢
      exact .headEq (morphism.headEq same) ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihA ihB ⊢
      exact .piCong ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv) (morphism.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihA ihB ⊢
      exact .sigmaCong ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv)
        (morphism.join join)
  | idCong _ hu _ _ ihA iha ihb =>
      simp only [Statement.mapHead, Tm.mapHead] at ihA iha ihb ⊢
      exact .idCong ihA (morphism.isUniverse hu) iha ihb
  | lamCong _ hu _ ihPi ihBody =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihPi ihBody ⊢
      exact .lamCong ihPi (morphism.isUniverse hu) ihBody
  | appCong _ _ ihF ihA =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ihF ihA ⊢
      exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .pairCong ihS (morphism.isUniverse hu) ihA ihB
  | fstCong _ ih =>
      simp only [Statement.mapHead, Tm.mapHead] at ih ⊢
      exact .fstCong ih
  | sndCong _ ih =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ih ⊢
      exact .sndCong ih
  | reflCong _ ih =>
      simp only [Statement.mapHead, Tm.mapHead] at ih ⊢
      exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody ihA =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0, Ctx.mapHead] at ihPi ihBody ihA ⊢
      exact .betaPi ihPi (morphism.isUniverse hu) ihBody ihA
  | betaFst _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .betaFst ihS (morphism.isUniverse hu) ihA ihB
  | betaSnd _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .betaSnd ihS (morphism.isUniverse hu) ihA ihB
  | root step _ _ ihL ihR =>
      simp only [Statement.mapHead] at ihL ihR ⊢
      exact .root (morphism.computation step) ihL ihR
  | etaPi _ _ _ ihF ihG ihApps =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_rename, Ctx.mapHead] at ihF ihG ihApps ⊢
      exact .etaPi ihF ihG ihApps
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      simp only [Statement.mapHead, Tm.mapHead, Tm.mapHead_inst0] at ihP ihQ ihFst ihSnd ⊢
      exact .etaSigma ihP ihQ ihFst ihSnd
  | subEqual _ hu ih =>
      simp only [Statement.mapHead, Tm.mapHead] at ih ⊢
      exact .subEqual ih (morphism.isUniverse hu)
  | subUniv c =>
      simp only [Statement.mapHead, Tm.mapHead]
      exact .subUniv (morphism.cumulative c)
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihPi ihPi' ihA ihB ⊢
      exact .subPi ihPi (morphism.isUniverse hu) ihPi' (morphism.isUniverse hu') ihA
        (morphism.isUniverse hw) ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      simp only [Statement.mapHead, Tm.mapHead, Ctx.mapHead] at ihS ihS' ihA ihB ⊢
      exact .subSigma ihS (morphism.isUniverse hu) ihS' (morphism.isUniverse hu') ihA ihB
  | subTrans _ _ ih₁ ih₂ =>
      simp only [Statement.mapHead] at ih₁ ih₂ ⊢
      exact .subTrans ih₁ ih₂

theorem Typed.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map) {n : Nat}
    {Γ : Ctx HeadOne n} {t A : Tm HeadOne n} (typed : Typed source Γ t A) :
    Typed target (Γ.mapHead map) (t.mapHead map) (A.mapHead map) :=
  Derivable.mapHead morphism typed

theorem Equal.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map) {n : Nat}
    {Γ : Ctx HeadOne n} {a b A : Tm HeadOne n} (equal : Equal source Γ a b A) :
    Equal target (Γ.mapHead map) (a.mapHead map) (b.mapHead map) (A.mapHead map) :=
  Derivable.mapHead morphism equal

/-- Along a morphism with the identity head map, typings are unchanged. -/
theorem Typed.of_morphism {source target : Rules HeadOne}
    (morphism : source.Morphism target (fun head => head)) {n : Nat}
    {Γ : Ctx HeadOne n} {t A : Tm HeadOne n} (typed : Typed source Γ t A) :
    Typed target Γ t A := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead morphism

theorem Equal.of_morphism {source target : Rules HeadOne}
    (morphism : source.Morphism target (fun head => head)) {n : Nat}
    {Γ : Ctx HeadOne n} {a b A : Tm HeadOne n} (equal : Equal source Γ a b A) :
    Equal target Γ a b A := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using equal.mapHead morphism

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
