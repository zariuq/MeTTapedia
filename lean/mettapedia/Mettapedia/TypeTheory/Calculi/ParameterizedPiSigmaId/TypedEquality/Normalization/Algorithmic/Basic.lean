import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.TypeForms

/-!
# Typings and soundness of the algorithmic equality

Compared types are types, compared terms are typed at the type they are
compared at, and a derivation of the algorithmic equality in a formed context
is an equality of the typed equality: for types and terms through the
kernel's conversion relation, which it refines, and for spines directly, with
the left spine's head assigning the type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

section Typings

variable {R : Rules Head} {roles : Roles Head}

theorem Algorithmic.types_isType {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (derivation : Algorithmic R roles (.types Γ A B)) : IsType R Γ A ∧ IsType R Γ B := by
  cases derivation with
  | types rA rB _ _ _ => exact ⟨rA.sourceType, rB.sourceType⟩

theorem Algorithmic.terms_typed {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (derivation : Algorithmic R roles (.terms Γ t u A)) : Typed R Γ t A ∧ Typed R Γ u A := by
  cases derivation with
  | terms rA _ rt ru _ =>
      exact ⟨Typed.convType rt.source rA.typeEq.symm, Typed.convType ru.source rA.typeEq.symm⟩

theorem Algorithmic.termsW_typed {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (derivation : Algorithmic R roles (.termsW Γ t u A)) : Typed R Γ t A ∧ Typed R Γ u A := by
  cases derivation with
  | univ _ tt tu _ => exact ⟨tt, tu⟩
  | eta _ tf _ tg _ _ => exact ⟨tf, tg⟩
  | sigmaEta tp _ tq _ _ _ => exact ⟨tp, tq⟩
  | refl tx tx' _ => exact ⟨tx, tx'⟩
  | spine _ _ _ tt tu _ => exact ⟨tt, tu⟩

theorem Algorithmic.spinesW_form {n : Nat} {Γ : Ctx Head n} {t u U : Tm Head n}
    (derivation : Algorithmic R roles (.spinesW Γ t u U)) : IsTypeForm roles U := by
  cases derivation with
  | spinesW _ _ form => exact form

end Typings

/-! ## Soundness -/

variable {S : Setting Head L}

/-- What a derivation of the algorithmic equality gives in a formed context. -/
def AlgorithmicSound (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A B => CtxFormed S.R Γ → TypeEq S.R Γ A B
  | .typesW Γ A B => CtxFormed S.R Γ → ∀ {u : Head}, S.R.isUniverse u →
      Typed S.R Γ A (.head u) → Typed S.R Γ B (.head u) → Equal S.R Γ A B (.head u)
  | .terms Γ t u A => CtxFormed S.R Γ → Equal S.R Γ t u A
  | .termsW Γ t u A => CtxFormed S.R Γ → Equal S.R Γ t u A
  | .spines Γ t u U => CtxFormed S.R Γ →
      Typed S.R Γ t U ∧ Typed S.R Γ u U ∧ Equal S.R Γ t u U
  | .spinesW Γ t u U => CtxFormed S.R Γ →
      Typed S.R Γ t U ∧ Typed S.R Γ u U ∧ Equal S.R Γ t u U

section Soundness

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts roots heads algebra

theorem Algorithmic.sound_terms {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (formed : CtxFormed S.R Γ) (derivation : Algorithmic S.R S.roles (.terms Γ t u A)) :
    Equal S.R Γ t u A :=
  Algorithm.sound facts roots heads algebra derivation.refines formed
    derivation.terms_typed.1 derivation.terms_typed.2

theorem Algorithmic.sound_termsW {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (formed : CtxFormed S.R Γ) (derivation : Algorithmic S.R S.roles (.termsW Γ t u A)) :
    Equal S.R Γ t u A :=
  Algorithm.sound facts roots heads algebra derivation.refines formed
    derivation.termsW_typed.1 derivation.termsW_typed.2

theorem Algorithmic.sound_types {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (derivation : Algorithmic S.R S.roles (.types Γ A B)) :
    TypeEq S.R Γ A B := by
  obtain ⟨⟨u, hu, tA⟩, ⟨v, hv, tB⟩⟩ := derivation.types_isType
  obtain ⟨w, join⟩ := S.levels.join_exists hu hv
  obtain ⟨cu, cv⟩ := S.levels.join_upper join
  exact ⟨w, (S.levels.join_level join).1,
    Algorithm.sound facts roots heads algebra derivation.refines formed
      (S.levels.join_level join).1 (.cumul tA cu) (.cumul tB cv)⟩

/-- Every derivation of the algorithmic equality is sound. -/
theorem Algorithmic.sound {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : AlgorithmicSound S st := by
  induction derivation with
  | types rA rB fA fB d _ =>
      exact fun formed => Algorithmic.sound_types facts roots heads algebra formed
        (.types rA rB fA fB d)
  | heads same tA tB hu =>
      exact fun formed _ hv tA' tB' => Algorithm.sound facts roots heads algebra
        (Algorithmic.heads (roles := S.roles) same tA tB hu).refines formed hv tA' tB'
  | pi isA dA dB _ _ =>
      exact fun formed _ hu tA tB => Algorithm.sound facts roots heads algebra
        (Algorithmic.pi (roles := S.roles) isA dA dB).refines formed hu tA tB
  | sigma isA dA dB _ _ =>
      exact fun formed _ hu tA tB => Algorithm.sound facts roots heads algebra
        (Algorithmic.sigma (roles := S.roles) isA dA dB).refines formed hu tA tB
  | id dA dx dy _ _ _ =>
      exact fun formed _ hu tA tB => Algorithm.sound facts roots heads algebra
        (Algorithmic.id (roles := S.roles) dA dx dy).refines formed hu tA tB
  | inductiveType role isT =>
      exact fun formed _ hu tA tB => Algorithm.sound facts roots heads algebra
        (Algorithmic.inductiveType (R := S.R) role isT).refines formed hu tA tB
  | neutralTypes nA nB hu d _ =>
      exact fun formed _ hv tA tB => Algorithm.sound facts roots heads algebra
        (Algorithmic.neutralTypes (R := S.R) nA nB hu d).refines formed hv tA tB
  | terms rA fA rt ru d _ =>
      exact fun formed => Algorithmic.sound_terms facts roots heads algebra formed
        (.terms rA fA rt ru d)
  | univ hu tt tu d _ =>
      exact fun formed => Algorithmic.sound_termsW facts roots heads algebra formed
        (.univ hu tt tu d)
  | eta isA tf funF tg funG d _ =>
      exact fun formed => Algorithmic.sound_termsW facts roots heads algebra formed
        (.eta isA tf funF tg funG d)
  | sigmaEta tp pairP tq pairQ d₁ d₂ _ _ =>
      exact fun formed => Algorithmic.sound_termsW facts roots heads algebra formed
        (.sigmaEta tp pairP tq pairQ d₁ d₂)
  | refl tx tx' d _ =>
      exact fun formed => Algorithmic.sound_termsW facts roots heads algebra formed
        (.refl tx tx' d)
  | spine sA fT fU tt tu d _ =>
      exact fun formed => Algorithmic.sound_termsW facts roots heads algebra formed
        (.spine sA fT fU tt tu d)
  | var i => exact fun _ => ⟨.var i, .var i, .refl (.var i)⟩
  | const _ typed => exact fun _ => ⟨typed, typed, .refl typed⟩
  | app _ da ihf _ =>
      intro formed
      obtain ⟨tf, tg, efg⟩ := ihf formed
      obtain ⟨ta, tb⟩ := da.terms_typed
      have eab := Algorithmic.sound_terms facts roots heads algebra formed da
      obtain ⟨s, hs, tPi⟩ := Typed.isType tf formed
      obtain ⟨_, ⟨v, hv, tB⟩⟩ := IsType.pi_parts ⟨s, hs, tPi⟩
      have change := TypeEq.of_instantiateEq tB hv tb (.symm eab)
      exact ⟨.appElim tf ta, Typed.convType (.appElim tg tb) change, .appCong efg eab⟩
  | fst _ ih =>
      intro formed
      obtain ⟨tp, tq, epq⟩ := ih formed
      exact ⟨.fstElim tp, .fstElim tq, .fstCong epq⟩
  | snd _ ih =>
      intro formed
      obtain ⟨tp, tq, epq⟩ := ih formed
      obtain ⟨s, hs, tSigma⟩ := Typed.isType tp formed
      obtain ⟨_, ⟨v, hv, tB⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have change := TypeEq.of_instantiateEq tB hv (.fstElim tq) (.symm (.fstCong epq))
      exact ⟨.sndElim tp, Typed.convType (.sndElim tq) change, .sndCong epq⟩
  | spinesW _ rU _ ih =>
      intro formed
      obtain ⟨tt, tu, e⟩ := ih formed
      exact ⟨Typed.convType tt rU.typeEq, Typed.convType tu rU.typeEq,
        Equal.convType e rU.typeEq⟩

end Soundness

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
