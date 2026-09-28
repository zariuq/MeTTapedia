import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Synthesis

/-!
# The kernel's checking algorithm, as a relation

The kernel's subtype test, and its synthesis and checking, as relations over
the rule package's reduction and its conversion algorithm (`Algorithm`). They
carry no typing premises: they describe what the kernel computes.

* The subtype test tries conversion first, then compares weak-head normal
  forms: universes by their order, dependent function types by convertible
  domains and codomains below, dependent pair types componentwise.
* Synthesis and checking follow the kernel's bidirectional typing
  (`KernelTyping`), with every reduction, conversion and subtype condition
  decided by the algorithm instead of by the typed equality.

For a rule package with the facts about the weak-head forms of its types, whose
declared constant types are types, a derivation in a formed context is a typing
derivation (`CheckingAlgorithm.sound`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- The kernel's subtype test: conversion, or weak-head normal forms that are
universes in order, dependent function types with convertible domains and
codomains below, or dependent pair types with both components below. -/
inductive BelowAlgorithm (R : Rules Head) :
    {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Prop where
  | conv {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} :
      Algorithm R (.types Γ A B) → BelowAlgorithm R Γ A B
  | universes {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u v : Head} :
      Reduces R A (.head u) → Reduces R B (.head v) → R.cumulative u v →
      BelowAlgorithm R Γ A B
  | pi {n : Nat} {Γ : Ctx Head n} {A B A₁ A₂ : Tm Head n} {B₁ B₂ : Tm Head (n + 1)} :
      Reduces R A (.pi A₁ B₁) → Reduces R B (.pi A₂ B₂) → Algorithm R (.types Γ A₁ A₂) →
      BelowAlgorithm R (.snoc Γ A₁) B₁ B₂ → BelowAlgorithm R Γ A B
  | sigma {n : Nat} {Γ : Ctx Head n} {A B A₁ A₂ : Tm Head n} {B₁ B₂ : Tm Head (n + 1)} :
      Reduces R A (.sigma A₁ B₁) → Reduces R B (.sigma A₂ B₂) → BelowAlgorithm R Γ A₁ A₂ →
      BelowAlgorithm R (.snoc Γ A₁) B₁ B₂ → BelowAlgorithm R Γ A B

/-- The kernel's synthesis and checking. Synthesis computes a type for
variables, constants, heads, type formers over types, reflexivity proofs,
eliminations of synthesized terms and abstractions applied to synthesized
arguments; checking tests an abstraction, a pair or a reflexivity proof against
the weak-head normal form of the expected type, and any term by synthesizing a
type that passes the subtype test. -/
inductive CheckingAlgorithm (R : Rules Head) :
    Mode → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Prop where
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      CheckingAlgorithm R .synth Γ (.var i) (Ctx.lookup Γ i)
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} :
      R.constantType name = some type →
      CheckingAlgorithm R .synth Γ (.const name) (liftClosed type)
  | head {n : Nat} {Γ : Ctx Head n} {h u : Head} :
      R.headTyping h u → CheckingAlgorithm R .synth Γ (.head h) (.head u)
  | pi {n : Nat} {Γ : Ctx Head n} {A TA : Tm Head n} {B TB : Tm Head (n + 1)} {u v w : Head} :
      CheckingAlgorithm R .synth Γ A TA → Reduces R TA (.head u) → R.isUniverse u →
      CheckingAlgorithm R .synth (.snoc Γ A) B TB → Reduces R TB (.head v) → R.isUniverse v →
      R.join u v w → CheckingAlgorithm R .synth Γ (.pi A B) (.head w)
  | sigma {n : Nat} {Γ : Ctx Head n} {A TA : Tm Head n} {B TB : Tm Head (n + 1)}
      {u v w : Head} :
      CheckingAlgorithm R .synth Γ A TA → Reduces R TA (.head u) → R.isUniverse u →
      CheckingAlgorithm R .synth (.snoc Γ A) B TB → Reduces R TB (.head v) → R.isUniverse v →
      R.join u v w → CheckingAlgorithm R .synth Γ (.sigma A B) (.head w)
  | id {n : Nat} {Γ : Ctx Head n} {A TA a b : Tm Head n} {u : Head} :
      CheckingAlgorithm R .synth Γ A TA → Reduces R TA (.head u) → R.isUniverse u →
      CheckingAlgorithm R .check Γ a A → CheckingAlgorithm R .check Γ b A →
      CheckingAlgorithm R .synth Γ (.id A a b) (.head u)
  | refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      CheckingAlgorithm R .synth Γ a A → CheckingAlgorithm R .synth Γ (.refl a) (.id A a a)
  | app {n : Nat} {Γ : Ctx Head n} {f a F A : Tm Head n} {B : Tm Head (n + 1)} :
      CheckingAlgorithm R .synth Γ f F → Reduces R F (.pi A B) →
      CheckingAlgorithm R .check Γ a A →
      CheckingAlgorithm R .synth Γ (.app f a) (inst0 a B)
  | fst {n : Nat} {Γ : Ctx Head n} {p P A : Tm Head n} {B : Tm Head (n + 1)} :
      CheckingAlgorithm R .synth Γ p P → Reduces R P (.sigma A B) →
      CheckingAlgorithm R .synth Γ (.fst p) A
  | snd {n : Nat} {Γ : Ctx Head n} {p P A : Tm Head n} {B : Tm Head (n + 1)} :
      CheckingAlgorithm R .synth Γ p P → Reduces R P (.sigma A B) →
      CheckingAlgorithm R .synth Γ (.snd p) (inst0 (.fst p) B)
  /-- An abstraction applied to a synthesized argument: its body is synthesized
  over the argument's type. -/
  | redex {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} {b B : Tm Head (n + 1)} :
      CheckingAlgorithm R .synth Γ a A → CheckingAlgorithm R .synth (.snoc Γ A) b B →
      CheckingAlgorithm R .synth Γ (.app (.lam b) a) (inst0 a B)
  | lamCheck {n : Nat} {Γ : Ctx Head n} {body : Tm Head (n + 1)} {E A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Reduces R E (.pi A B) → CheckingAlgorithm R .check (.snoc Γ A) body B →
      CheckingAlgorithm R .check Γ (.lam body) E
  | pairCheck {n : Nat} {Γ : Ctx Head n} {a b E A : Tm Head n} {B : Tm Head (n + 1)} :
      Reduces R E (.sigma A B) → CheckingAlgorithm R .check Γ a A →
      CheckingAlgorithm R .check Γ b (inst0 a B) → CheckingAlgorithm R .check Γ (.pair a b) E
  | reflCheck {n : Nat} {Γ : Ctx Head n} {x E A a b : Tm Head n} :
      Reduces R E (.id A a b) → CheckingAlgorithm R .check Γ x A →
      Algorithm R (.compare Γ x a A) → Algorithm R (.compare Γ x b A) →
      CheckingAlgorithm R .check Γ (.refl x) E
  | switch {n : Nat} {Γ : Ctx Head n} {t T E : Tm Head n} :
      CheckingAlgorithm R .synth Γ t T → BelowAlgorithm R Γ T E →
      CheckingAlgorithm R .check Γ t E

/-- The declared type of every constant is a type. -/
def DeclaredTypesFormed (R : Rules Head) : Prop :=
  ∀ {name : DeclName} {type : Tm Head 0}, R.constantType name = some type →
    ∃ u, R.isUniverse u ∧ Typed R .nil type (.head u)

/-! ## Soundness -/

variable {S : Setting Head L}

section Soundness

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts roots heads

/-- Reducing a type gives an equal type. -/
theorem Reduces.typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A A' : Tm Head n}
    (red : Reduces S.R A A') (type : IsType S.R Γ A) : TypeEq S.R Γ A A' := by
  obtain ⟨u, hu, tA⟩ := type
  exact ⟨u, hu, (Reduces.preserve facts roots heads formed red tA).2⟩

include algebra

/-- Types the conversion algorithm relates are equal. -/
theorem Algorithm.typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A B : Tm Head n}
    (derivation : Algorithm S.R (.types Γ A B)) (typeA : IsType S.R Γ A)
    (typeB : IsType S.R Γ B) : TypeEq S.R Γ A B := by
  obtain ⟨u, hu, tA⟩ := typeA
  obtain ⟨v, hv, tB⟩ := typeB
  obtain ⟨w, join⟩ := S.levels.join_exists hu hv
  obtain ⟨cu, cv⟩ := S.levels.join_upper join
  exact ⟨w, (S.levels.join_level join).1,
    Algorithm.sound facts roots heads algebra derivation formed
      (S.levels.join_level join).1 (.cumul tA cu) (.cumul tB cv)⟩

/-- The kernel's subtype test is sound. -/
theorem BelowAlgorithm.sound {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (derivation : BelowAlgorithm S.R Γ A B) :
    CtxFormed S.R Γ → IsType S.R Γ A → IsType S.R Γ B → Below S.R Γ A B := by
  induction derivation with
  | conv d =>
      intro formed typeA typeB
      exact (Algorithm.typeEq facts roots heads algebra formed d typeA typeB).below
  | universes rA rB c =>
      intro formed typeA typeB
      have eA := Reduces.typeEq facts roots heads formed rA typeA
      have eB := Reduces.typeEq facts roots heads formed rB typeB
      exact .subTrans eA.below (.subTrans (.subUniv c) eB.symm.below)
  | @pi n Γ A B A₁ A₂ B₁ B₂ rA rB dA _ ih =>
      intro formed typeA typeB
      have eA := Reduces.typeEq facts roots heads formed rA typeA
      have eB := Reduces.typeEq facts roots heads formed rB typeB
      have type₁ := (TypeEq.isType eA formed).2
      have type₂ := (TypeEq.isType eB formed).2
      obtain ⟨⟨u₁, hu₁, tA₁⟩, ⟨v₁, hv₁, tB₁⟩⟩ := IsType.pi_parts type₁
      obtain ⟨⟨u₂, hu₂, tA₂⟩, ⟨v₂, hv₂, tB₂⟩⟩ := IsType.pi_parts type₂
      have e₁₂ := Algorithm.typeEq facts roots heads algebra formed dA
        ⟨u₁, hu₁, tA₁⟩ ⟨u₂, hu₂, tA₂⟩
      have leB := ih (.snoc formed ⟨u₁, hu₁, tA₁⟩) ⟨v₁, hv₁, tB₁⟩
        ⟨v₂, hv₂, Typed.ctxConv tB₂ e₁₂.symm⟩
      obtain ⟨s₁, hs₁, tPi₁⟩ := type₁
      obtain ⟨s₂, hs₂, tPi₂⟩ := type₂
      obtain ⟨w, hw, e⟩ := e₁₂
      exact .subTrans eA.below (.subTrans (.subPi tPi₁ hs₁ tPi₂ hs₂ e hw leB) eB.symm.below)
  | @sigma n Γ A B A₁ A₂ B₁ B₂ rA rB _ _ ihA ihB =>
      intro formed typeA typeB
      have eA := Reduces.typeEq facts roots heads formed rA typeA
      have eB := Reduces.typeEq facts roots heads formed rB typeB
      have type₁ := (TypeEq.isType eA formed).2
      have type₂ := (TypeEq.isType eB formed).2
      obtain ⟨⟨u₁, hu₁, tA₁⟩, ⟨v₁, hv₁, tB₁⟩⟩ := IsType.sigma_parts type₁
      obtain ⟨⟨u₂, hu₂, tA₂⟩, ⟨v₂, hv₂, tB₂⟩⟩ := IsType.sigma_parts type₂
      have leA := ihA formed ⟨u₁, hu₁, tA₁⟩ ⟨u₂, hu₂, tA₂⟩
      have leB := ihB (.snoc formed ⟨u₁, hu₁, tA₁⟩) ⟨v₁, hv₁, tB₁⟩
        ⟨v₂, hv₂, Typed.ctxBelow tB₂ leA⟩
      obtain ⟨s₁, hs₁, tPi₁⟩ := type₁
      obtain ⟨s₂, hs₂, tPi₂⟩ := type₂
      exact .subTrans eA.below (.subTrans (.subSigma tPi₁ hs₁ tPi₂ hs₂ leA leB) eB.symm.below)

omit facts roots heads algebra in
/-- What a derivation of the checking algorithm establishes: a synthesized type
is a type of the term, and so is a checked type that is a type. -/
def CheckingSound (S : Setting Head L) (mode : Mode) {n : Nat} (Γ : Ctx Head n)
    (t T : Tm Head n) : Prop :=
  match mode with
  | .synth => CtxFormed S.R Γ → Typed S.R Γ t T
  | .check => CtxFormed S.R Γ → IsType S.R Γ T → Typed S.R Γ t T

/-- The kernel's checking algorithm is sound. -/
theorem CheckingAlgorithm.sound (declared : DeclaredTypesFormed S.R) {mode : Mode} {n : Nat}
    {Γ : Ctx Head n} {t T : Tm Head n} (derivation : CheckingAlgorithm S.R mode Γ t T) :
    CheckingSound S mode Γ t T := by
  induction derivation with
  | var i => exact fun _ => .var i
  | const known =>
      intro _
      obtain ⟨u, hu, typing⟩ := declared known
      exact .const known typing hu
  | head typing => exact fun _ => .headType typing
  | @pi n Γ A TA B TB u v w _ rA hu _ rB hv join ihA ihB =>
      intro formed
      have tA₀ := ihA formed
      have tA' : Typed S.R Γ A (.head u) :=
        Typed.convType tA₀ (Reduces.typeEq facts roots heads formed rA
          (Typed.isType tA₀ formed))
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u, hu, tA'⟩
      have tB₀ := ihB formedA
      have tB' : Typed S.R (.snoc Γ A) B (.head v) :=
        Typed.convType tB₀ (Reduces.typeEq facts roots heads formedA rB
          (Typed.isType tB₀ formedA))
      exact .piForm tA' hu tB' hv join
  | @sigma n Γ A TA B TB u v w _ rA hu _ rB hv join ihA ihB =>
      intro formed
      have tA₀ := ihA formed
      have tA' : Typed S.R Γ A (.head u) :=
        Typed.convType tA₀ (Reduces.typeEq facts roots heads formed rA
          (Typed.isType tA₀ formed))
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u, hu, tA'⟩
      have tB₀ := ihB formedA
      have tB' : Typed S.R (.snoc Γ A) B (.head v) :=
        Typed.convType tB₀ (Reduces.typeEq facts roots heads formedA rB
          (Typed.isType tB₀ formedA))
      exact .sigmaForm tA' hu tB' hv join
  | @id n Γ A TA a b u _ rA hu _ _ ihA iha ihb =>
      intro formed
      have tA₀ := ihA formed
      have tA' : Typed S.R Γ A (.head u) :=
        Typed.convType tA₀ (Reduces.typeEq facts roots heads formed rA
          (Typed.isType tA₀ formed))
      exact .idForm tA' hu (iha formed ⟨u, hu, tA'⟩) (ihb formed ⟨u, hu, tA'⟩)
  | refl _ ih => exact fun formed => .reflIntro (ih formed)
  | @app n Γ f a F A B _ red _ ihf iha =>
      intro formed
      have tf := ihf formed
      have eF := Reduces.typeEq facts roots heads formed red
        (Typed.isType tf formed)
      have tf' := Typed.convType tf eF
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (TypeEq.isType eF formed).2
      exact .appElim tf' (iha formed ⟨u, hu, tA⟩)
  | @fst n Γ p P A B _ red ih =>
      intro formed
      have tp := ih formed
      have eP := Reduces.typeEq facts roots heads formed red
        (Typed.isType tp formed)
      exact .fstElim (Typed.convType tp eP)
  | @snd n Γ p P A B _ red ih =>
      intro formed
      have tp := ih formed
      have eP := Reduces.typeEq facts roots heads formed red
        (Typed.isType tp formed)
      exact .sndElim (Typed.convType tp eP)
  | @redex n Γ a A b B _ _ iha ihb =>
      intro formed
      have ta := iha formed
      obtain ⟨u, hu, tA⟩ := Typed.isType ta formed
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u, hu, tA⟩
      have tb := ihb formedA
      obtain ⟨v, hv, tB⟩ := Typed.isType tb formedA
      obtain ⟨w, join⟩ := S.levels.join_exists hu hv
      exact .appElim (.lamIntro (.piForm tA hu tB hv join) (S.levels.join_level join).1 tb) ta
  | @lamCheck n Γ body E A B red _ ih =>
      intro formed typeE
      have eE := Reduces.typeEq facts roots heads formed red typeE
      have typePi := (TypeEq.isType eE formed).2
      obtain ⟨⟨u, hu, tA⟩, ⟨v, hv, tB⟩⟩ := IsType.pi_parts typePi
      obtain ⟨s, hs, tPi⟩ := typePi
      have tb := ih (.snoc formed ⟨u, hu, tA⟩) ⟨v, hv, tB⟩
      exact Typed.convType (.lamIntro tPi hs tb) eE.symm
  | @pairCheck n Γ a b E A B red _ _ iha ihb =>
      intro formed typeE
      have eE := Reduces.typeEq facts roots heads formed red typeE
      have typeSigma := (TypeEq.isType eE formed).2
      obtain ⟨⟨u, hu, tA⟩, ⟨v, hv, tB⟩⟩ := IsType.sigma_parts typeSigma
      obtain ⟨s, hs, tSigma⟩ := typeSigma
      have ta := iha formed ⟨u, hu, tA⟩
      have tb := ihb formed ⟨v, hv, tB.substitute (SubstMor.single ta)⟩
      exact Typed.convType (.pairIntro tSigma hs ta tb) eE.symm
  | @reflCheck n Γ x E A a b red _ dxa dxb ih =>
      intro formed typeE
      have eE := Reduces.typeEq facts roots heads formed red typeE
      obtain ⟨s, hs, tId⟩ := (TypeEq.isType eE formed).2
      obtain ⟨u, tA, hu, ta, tb, _⟩ := Typed.generation tId
      have tx := ih formed ⟨u, hu, tA⟩
      have exa := Algorithm.sound facts roots heads algebra dxa formed tx ta
      have exb := Algorithm.sound facts roots heads algebra dxb formed tx tb
      have change : TypeEq S.R Γ (.id A x x) (.id A a b) :=
        ⟨u, hu, .idCong (.refl tA) hu exa exb⟩
      exact Typed.convType (Typed.convType (.reflIntro tx) change) eE.symm
  | @switch n Γ t T E _ le ih =>
      intro formed typeE
      have tt := ih formed
      exact .sub tt (BelowAlgorithm.sound facts roots heads algebra le formed
        (Typed.isType tt formed) typeE)

end Soundness

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
