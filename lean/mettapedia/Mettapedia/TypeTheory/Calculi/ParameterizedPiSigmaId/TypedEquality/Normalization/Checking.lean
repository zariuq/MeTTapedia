import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.BelowDecidability

/-!
# Completeness of the kernel's bidirectional typing

The kernel types a term in one of two modes. Synthesis computes a type;
checking tests a term against an expected type. On the bidirectional fragment,
where abstractions, pairs and reflexivity proofs stand in checking positions,
the kernel's typing is complete: a term of the fragment in synthesis position
that has any type has a synthesized type, and a term of the fragment in
checking position is checked at every type it has. Together with soundness,
checking a term of the fragment against a type holds exactly when the term has
that type.

The three mode switches are each a theorem here:

* from checking to synthesis, a synthesized type must be usable at the expected
  one, and every type of a synthesized term is above its synthesized type;
* from synthesis to checking, the argument of an application is checked against
  the domain of the function's synthesized type, which is complete because the
  synthesized type lies below every type of the function;
* formation, that a term is a type, holds exactly when its synthesized type
  reduces to a universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- The terms the kernel types, by mode. In synthesis mode: variables,
constants, heads, type formers over synthesizable types with checkable
endpoints, applications of synthesizable terms to checkable arguments,
projections of synthesizable terms, and abstractions with synthesizable bodies
applied to synthesizable arguments. In checking mode: abstractions, pairs and
reflexivity proofs over checkable components, and every synthesizable term. -/
inductive Bidirectional : Mode → {n : Nat} → Tm Head n → Prop where
  | var {n : Nat} (i : Fin n) : Bidirectional .synth (.var i)
  | const {n : Nat} (name : DeclName) : Bidirectional .synth (n := n) (.const name)
  | head {n : Nat} (h : Head) : Bidirectional .synth (n := n) (.head h)
  | pi {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Bidirectional .synth A → Bidirectional .synth B → Bidirectional .synth (.pi A B)
  | sigma {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Bidirectional .synth A → Bidirectional .synth B → Bidirectional .synth (.sigma A B)
  | id {n : Nat} {A a b : Tm Head n} :
      Bidirectional .synth A → Bidirectional .check a → Bidirectional .check b →
      Bidirectional .synth (.id A a b)
  | app {n : Nat} {f a : Tm Head n} :
      Bidirectional .synth f → Bidirectional .check a → Bidirectional .synth (.app f a)
  | fst {n : Nat} {p : Tm Head n} : Bidirectional .synth p → Bidirectional .synth (.fst p)
  | snd {n : Nat} {p : Tm Head n} : Bidirectional .synth p → Bidirectional .synth (.snd p)
  | redex {n : Nat} {b : Tm Head (n + 1)} {a : Tm Head n} :
      Bidirectional .synth b → Bidirectional .synth a →
      Bidirectional .synth (.app (.lam b) a)
  | lam {n : Nat} {b : Tm Head (n + 1)} :
      Bidirectional .check b → Bidirectional .check (.lam b)
  | pair {n : Nat} {a b : Tm Head n} :
      Bidirectional .check a → Bidirectional .check b → Bidirectional .check (.pair a b)
  | refl {n : Nat} {x : Tm Head n} :
      Bidirectional .check x → Bidirectional .check (.refl x)
  | synthesized {n : Nat} {t : Tm Head n} :
      Bidirectional .synth t → Bidirectional .check t

/-! ## Weak-head forms of the expected type -/

section Forms

variable (facts : FormFacts S.R S.roles)
include facts

/-- A type equal to a universe reduces to a universe. -/
theorem IsType.universe_whnf {n : Nat} {Γ : Ctx Head n} {X : Tm Head n}
    (formed : CtxFormed S.R Γ) (isX : IsType S.R Γ X) {u : Head} (hu : S.R.isUniverse u)
    (e : TypeEq S.R Γ X (.head u)) :
    ∃ u₀, RedTy S.R S.roles Γ X (.head u₀) ∧ S.R.isUniverse u₀ := by
  obtain ⟨X', red, form⟩ := facts.typeForm isX formed
  obtain ⟨h', rfl, same⟩ := (facts.forms
    (TypeEq.trans S.levels (TypeEq.symm e) red.typeEq) formed (.inl ⟨_, rfl⟩) form).head_left
  exact ⟨h', red, (HeadSame.level S.levels same).1.mp hu⟩

/-- A type is an identity type in weak-head normal form, or equal to none. -/
theorem IsType.id_or {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} (formed : CtxFormed S.R Γ)
    (isX : IsType S.R Γ X) :
    (∃ C a b, RedTy S.R S.roles Γ X (.id C a b)) ∨ ∀ C a b, ¬ TypeEq S.R Γ X (.id C a b) := by
  obtain ⟨X', red, form⟩ := facts.typeForm isX formed
  have toForm : ∀ {C a b : Tm Head n}, TypeEq S.R Γ X (.id C a b) →
      ∃ C' a' b', X' = .id C' a' b' := fun e => by
    obtain ⟨C', a', b', same, _⟩ := (facts.forms
      (TypeEq.trans S.levels (TypeEq.symm e) red.typeEq) formed
      (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) form).id_left
    exact ⟨C', a', b', same⟩
  rcases form with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨C, a, b, rfl⟩ | neutral |
    ⟨_, _, _, rfl⟩
  · exact .inr fun _ _ _ e => by obtain ⟨_, _, _, same⟩ := toForm e; cases same
  · exact .inr fun _ _ _ e => by obtain ⟨_, _, _, same⟩ := toForm e; cases same
  · exact .inr fun _ _ _ e => by obtain ⟨_, _, _, same⟩ := toForm e; cases same
  · exact .inl ⟨C, a, b, red⟩
  · exact .inr fun _ _ _ e => by
      obtain ⟨_, _, _, same⟩ := toForm e
      exact neutral.not_former.2.2.2 _ _ _ same
  · exact .inr fun _ _ _ e => by obtain ⟨_, _, _, same⟩ := toForm e; cases same

end Forms

/-! ## Completeness -/

/-- What completeness gives for a term of the fragment: in synthesis mode a
synthesized type whenever the term has a type, in checking mode a check at
every type of the term. -/
def KernelComplete (S : Setting Head L) (mode : Mode) {n : Nat} (t : Tm Head n) : Prop :=
  match mode with
  | .synth => ∀ {Γ : Ctx Head n} {E : Tm Head n}, CtxFormed S.R Γ → Typed S.R Γ t E →
      ∃ T, Synth S.R S.roles Γ t T
  | .check => ∀ {Γ : Ctx Head n} {E : Tm Head n}, CtxFormed S.R Γ → Typed S.R Γ t E →
      Check S.R S.roles Γ t E

section Completeness

variable (facts : FormFacts S.R S.roles)
  (algebra : CumulativeAlgebra S.R)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
include facts algebra headsTyped

/-- A synthesized type of a term typed at a universe reduces to a universe. -/
theorem Synth.universe_whnf {n : Nat} {Γ : Ctx Head n} {A T : Tm Head n}
    (synth : Synth S.R S.roles Γ A T) (formed : CtxFormed S.R Γ) {u : Head}
    (typing : Typed S.R Γ A (.head u)) (hu : S.R.isUniverse u) :
    ∃ u₀, RedTy S.R S.roles Γ T (.head u₀) ∧ S.R.isUniverse u₀ := by
  obtain ⟨tT, principal⟩ := Synth.principal facts algebra headsTyped synth formed
  have isT := Typed.isType tT formed
  obtain ⟨u₁, hu₁, eT, _⟩ := Below.universe_target facts
    (TypeLe.toBelow (principal typing) (universe_type hu)) formed hu
    (IsType.refl (universe_type hu))
  exact IsType.universe_whnf facts formed isT hu₁ eT

/-- The kernel's typing is complete on the bidirectional fragment. -/
theorem Bidirectional.complete {mode : Mode} {n : Nat} {t : Tm Head n}
    (fragment : Bidirectional mode t) : KernelComplete S mode t := by
  have principal := fun {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
      (synth : Synth S.R S.roles Γ t T) (formed : CtxFormed S.R Γ) =>
    Synth.principal facts algebra headsTyped synth formed
  induction fragment with
  | var i =>
      intro Γ E _ _
      exact ⟨_, .var i⟩
  | const name =>
      intro Γ E _ typing
      obtain ⟨_, _, declared, tType, hu, _⟩ := Typed.generation typing
      exact ⟨_, .const declared tType hu⟩
  | head h =>
      intro Γ E _ typing
      obtain ⟨_, headTyping, _⟩ := Typed.generation typing
      exact ⟨_, .head headTyping⟩
  | pi _ _ ihA ihB =>
      intro Γ E formed typing
      obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := Typed.generation typing
      obtain ⟨TA, sA⟩ := ihA formed tA
      obtain ⟨u₀, rA, hu₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sA formed tA hu
      have formedA : CtxFormed S.R (.snoc Γ _) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨TB, sB⟩ := ihB formedA tB
      obtain ⟨v₀, rB, hv₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sB formedA tB hv
      obtain ⟨_, join⟩ := S.levels.join_exists hu₀ hv₀
      exact ⟨_, .pi sA rA hu₀ sB rB hv₀ join⟩
  | sigma _ _ ihA ihB =>
      intro Γ E formed typing
      obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := Typed.generation typing
      obtain ⟨TA, sA⟩ := ihA formed tA
      obtain ⟨u₀, rA, hu₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sA formed tA hu
      have formedA : CtxFormed S.R (.snoc Γ _) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨TB, sB⟩ := ihB formedA tB
      obtain ⟨v₀, rB, hv₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sB formedA tB hv
      obtain ⟨_, join⟩ := S.levels.join_exists hu₀ hv₀
      exact ⟨_, .sigma sA rA hu₀ sB rB hv₀ join⟩
  | id _ _ _ ihA iha ihb =>
      intro Γ E formed typing
      obtain ⟨u, tA, hu, ta, tb, _⟩ := Typed.generation typing
      obtain ⟨TA, sA⟩ := ihA formed tA
      obtain ⟨u₀, rA, hu₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sA formed tA hu
      exact ⟨_, .id sA rA hu₀ (iha formed ta) (ihb formed tb)⟩
  | app _ _ ihf iha =>
      intro Γ E formed typing
      obtain ⟨A', B', tf, ta, _⟩ := Typed.generation typing
      obtain ⟨F, sf⟩ := ihf formed tf
      obtain ⟨tF, principalF⟩ := principal sf formed
      have typePi := Typed.isType tf formed
      obtain ⟨A₁, B₁, eF, eA₁, _⟩ := Below.pi_inv facts
        (TypeLe.toBelow (principalF tf) typePi) formed (IsType.refl typePi)
      rcases IsType.pi_or facts formed (Typed.isType tF formed) with
        ⟨A₀, B₀, red⟩ | notPi
      · obtain ⟨e₀₁, _⟩ := TypeEq.pi_injective facts
          (TypeEq.trans S.levels (TypeEq.symm red.typeEq) eF) formed
        have ta₀ : Typed S.R Γ _ A₀ :=
          Typed.convType ta (TypeEq.symm (TypeEq.trans S.levels e₀₁ eA₁))
        exact ⟨_, .app sf red (iha formed ta₀)⟩
      · exact absurd eF (notPi A₁ B₁)
  | fst _ ihp =>
      intro Γ E formed typing
      obtain ⟨A', B', tp, _⟩ := Typed.generation typing
      obtain ⟨P, sp⟩ := ihp formed tp
      obtain ⟨tP, principalP⟩ := principal sp formed
      have typeSigma := Typed.isType tp formed
      obtain ⟨A₁, B₁, eP, _, _⟩ := Below.sigma_inv facts
        (TypeLe.toBelow (principalP tp) typeSigma) formed (IsType.refl typeSigma)
      rcases IsType.sigma_or facts formed (Typed.isType tP formed) with
        ⟨_, _, red⟩ | notSigma
      · exact ⟨_, .fst sp red⟩
      · exact absurd eP (notSigma A₁ B₁)
  | snd _ ihp =>
      intro Γ E formed typing
      obtain ⟨A', B', tp, _⟩ := Typed.generation typing
      obtain ⟨P, sp⟩ := ihp formed tp
      obtain ⟨tP, principalP⟩ := principal sp formed
      have typeSigma := Typed.isType tp formed
      obtain ⟨A₁, B₁, eP, _, _⟩ := Below.sigma_inv facts
        (TypeLe.toBelow (principalP tp) typeSigma) formed (IsType.refl typeSigma)
      rcases IsType.sigma_or facts formed (Typed.isType tP formed) with
        ⟨_, _, red⟩ | notSigma
      · exact ⟨_, .snd sp red⟩
      · exact absurd eP (notSigma A₁ B₁)
  | redex _ _ ihb iha =>
      intro Γ E formed typing
      obtain ⟨A', B', tLam, ta, _⟩ := Typed.generation typing
      obtain ⟨A'', B'', _, _, _, tb, lePi⟩ := Typed.generation tLam
      obtain ⟨TA, sa⟩ := iha formed ta
      obtain ⟨tTA, principalA⟩ := principal sa formed
      have isTA := Typed.isType tTA formed
      obtain ⟨e₁, _⟩ := TypeLe.pi_parts facts lePi
        (Typed.isType tLam formed) formed
      have le : Below S.R Γ TA A'' := .subTrans (TypeLe.toBelow (principalA ta)
        (Typed.isType ta formed)) (TypeEq.below (TypeEq.symm e₁))
      obtain ⟨TB, sb⟩ := ihb (.snoc formed isTA) (Typed.ctxBelow tb le)
      exact ⟨_, .redex sa (IsType.refl isTA) sb⟩
  | lam _ ihb =>
      intro Γ E formed typing
      obtain ⟨A, B, u, tPi, hu, tb, le⟩ := Typed.generation typing
      have isE := Typed.isType typing formed
      have leE := TypeLe.toBelow le isE
      obtain ⟨A₂, B₂, eE, eA, leB⟩ :=
        Below.pi_source facts leE formed (IsType.refl ⟨u, hu, tPi⟩)
      rcases IsType.pi_or facts formed isE with ⟨A₁, B₁, red⟩ | notPi
      · obtain ⟨e₁₂, eB₁₂⟩ := TypeEq.pi_injective facts
          (TypeEq.trans S.levels (TypeEq.symm red.typeEq) eE) formed
        have eA₁ : TypeEq S.R Γ A A₁ := TypeEq.trans S.levels eA (TypeEq.symm e₁₂)
        have tb₁ : Typed S.R (.snoc Γ A₁) _ B₁ := Typed.convType
          (Typed.ctxBelow (.sub tb leB) (TypeEq.below (TypeEq.symm eA₁))) (TypeEq.symm eB₁₂)
        obtain ⟨isA₁, _⟩ := IsType.pi_parts red.targetType
        exact .lamCheck red (ihb (.snoc formed isA₁) tb₁)
      · exact absurd eE (notPi A₂ B₂)
  | pair _ _ iha ihb =>
      intro Γ E formed typing
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le⟩ := Typed.generation typing
      have isE := Typed.isType typing formed
      have leE := TypeLe.toBelow le isE
      obtain ⟨A₂, B₂, eE, leA, leB⟩ :=
        Below.sigma_source facts leE formed (IsType.refl ⟨u, hu, tSigma⟩)
      rcases IsType.sigma_or facts formed isE with ⟨A₁, B₁, red⟩ | notSigma
      · obtain ⟨e₁₂, eB₁₂⟩ := TypeEq.sigma_injective facts
          (TypeEq.trans S.levels (TypeEq.symm red.typeEq) eE) formed
        have ta₁ : Typed S.R Γ _ A₁ := Typed.convType (.sub ta leA) (TypeEq.symm e₁₂)
        have tb₁ : Typed S.R Γ _ (inst0 _ B₁) := Typed.convType
          (.sub tb (Derivable.substitutes leB (SubstMor.single ta)))
          (TypeEq.symm (TypeEq.instantiate eB₁₂ ta₁))
        exact .pairCheck red (iha formed ta₁) (ihb formed tb₁)
      · exact absurd eE (notSigma A₂ B₂)
  | refl _ ihx =>
      intro Γ E formed typing
      obtain ⟨A, tx, le⟩ := Typed.generation typing
      have isE := Typed.isType typing formed
      have eE := TypeLe.id_eq facts le isE formed
      rcases IsType.id_or facts formed isE with ⟨C, a, b, red⟩ | notId
      · obtain ⟨eA, ea, eb⟩ := TypeEq.id_injective facts
          (TypeEq.trans S.levels eE red.typeEq) formed
        exact .reflCheck red (ihx formed (Typed.convType tx eA)) (Equal.convType ea eA)
          (Equal.convType eb eA)
      · exact absurd (TypeEq.symm eE) (notId _ _ _)
  | synthesized _ ih =>
      intro Γ E formed typing
      obtain ⟨T, s⟩ := ih formed typing
      exact .switch s (TypeLe.toBelow ((principal s formed).2 typing)
        (Typed.isType typing formed))

/-- On the bidirectional fragment, checking a term against a type of a formed
context succeeds exactly when the term has that type. -/
theorem Check.iff_typed {n : Nat} {Γ : Ctx Head n} {t E : Tm Head n}
    (fragment : Bidirectional .check t) (formed : CtxFormed S.R Γ) :
    Check S.R S.roles Γ t E ↔ Typed S.R Γ t E :=
  ⟨fun check => Check.sound facts algebra headsTyped check formed,
    fun typing => Bidirectional.complete facts algebra headsTyped fragment formed typing⟩

/-- On the bidirectional fragment, a term in synthesis position has a
synthesized type exactly when it has a type, and then the synthesized type is
below all of its types. -/
theorem Synth.exists_iff_typable {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}
    (fragment : Bidirectional .synth t) (formed : CtxFormed S.R Γ) :
    (∃ T, Synth S.R S.roles Γ t T) ↔ ∃ E, Typed S.R Γ t E :=
  ⟨fun ⟨T, s⟩ => ⟨T, (Synth.principal facts algebra headsTyped s formed).1⟩,
    fun ⟨_, typing⟩ =>
      Bidirectional.complete facts algebra headsTyped fragment formed typing⟩

/-- Formation: a term of the fragment in synthesis position is a type exactly
when it has a synthesized type that reduces to a universe. -/
theorem Synth.isType_iff {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (fragment : Bidirectional .synth A) (formed : CtxFormed S.R Γ) :
    IsType S.R Γ A ↔
      ∃ T u, Synth S.R S.roles Γ A T ∧ RedTy S.R S.roles Γ T (.head u) ∧ S.R.isUniverse u := by
  constructor
  · rintro ⟨u, hu, tA⟩
    obtain ⟨T, sA⟩ := Bidirectional.complete facts algebra headsTyped fragment formed tA
    obtain ⟨u₀, rT, hu₀⟩ :=
      Synth.universe_whnf facts algebra headsTyped sA formed tA hu
    exact ⟨T, u₀, sA, rT, hu₀⟩
  · rintro ⟨T, u, sA, rT, hu⟩
    exact ⟨u, hu, Typed.convType (Synth.principal facts algebra headsTyped sA formed).1
      rT.typeEq⟩

end Completeness

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
