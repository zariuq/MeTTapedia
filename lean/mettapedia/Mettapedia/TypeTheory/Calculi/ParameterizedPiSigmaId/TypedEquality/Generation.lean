import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural

/-!
# Generation for typed equality

Every typing derivation of a term ends with the rule of the term's former,
followed by the rules that do not follow the syntax: conversion by typed
equality at a universe, raising a universe head, and subtyping. `TypeLe` is the
closure of those rules, and `GenerationAt` states, for each former, what the rule
of that former needs together with the closure step to the final type.

One induction over derivations proves generation for every former at once.
Nothing here depends on normalization: inverting a `TypeLe` step, for
instance between two dependent function types, needs injectivity, which comes
from the normalization model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

variable {Head : Type}

/-- The closure of the two typing rules that do not follow the syntax. -/
inductive TypeLe (R : Rules Head) {n : Nat} (Γ : Ctx Head n) : Tm Head n → Tm Head n → Prop where
  | refl (A : Tm Head n) : TypeLe R Γ A A
  | conv {A B C : Tm Head n} {u : Head} : Equal R Γ A B (.head u) → R.isUniverse u →
      TypeLe R Γ B C → TypeLe R Γ A C
  | cumul {u v : Head} {C : Tm Head n} : R.cumulative u v → TypeLe R Γ (.head v) C →
      TypeLe R Γ (.head u) C
  | sub {A B C : Tm Head n} : Below R Γ A B → TypeLe R Γ B C → TypeLe R Γ A C

variable {R : Rules Head}

theorem TypeLe.trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (first : TypeLe R Γ A B) (second : TypeLe R Γ B C) : TypeLe R Γ A C := by
  induction first with
  | refl => exact second
  | conv e hu _ ih => exact .conv e hu (ih second)
  | cumul c _ ih => exact .cumul c (ih second)
  | sub le _ ih => exact .sub le (ih second)

theorem TypeLe.of_equal {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (equal : Equal R Γ A B (.head u)) (hu : R.isUniverse u) : TypeLe R Γ A B :=
  .conv equal hu (.refl B)

theorem TypeLe.of_cumulative {n : Nat} {Γ : Ctx Head n} {u v : Head} (c : R.cumulative u v) :
    TypeLe R Γ (.head u) (.head v) :=
  .cumul c (.refl _)

theorem TypeLe.of_below {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (le : Below R Γ A B) :
    TypeLe R Γ A B :=
  .sub le (.refl _)

/-- A typing extends along the closure. -/
theorem Typed.subsume {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (typing : Typed R Γ t A) (le : TypeLe R Γ A B) : Typed R Γ t B := by
  induction le generalizing t with
  | refl => exact typing
  | conv e hu _ ih => exact ih (.conv typing e hu)
  | cumul c _ ih => exact ih (.cumul typing c)
  | sub le _ ih => exact ih (.sub typing le)

/-- An equality extends along the closure. -/
theorem Equal.subsume {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    (equal : Equal R Γ a b A) (le : TypeLe R Γ A B) : Equal R Γ a b B := by
  induction le generalizing a b with
  | refl => exact equal
  | conv e hu _ ih => exact ih (.convEq equal e hu)
  | cumul c _ ih => exact ih (.cumulEq equal c)
  | sub le _ ih => exact ih (.subEq equal le)

/-- What a typing of a term says, by the term's former. -/
def GenerationAt (R : Rules Head) {n : Nat} (Γ : Ctx Head n) : Tm Head n → Tm Head n → Prop
  | .var i, T => TypeLe R Γ (Ctx.lookup Γ i) T
  | .const name, T => ∃ type u, R.constantType name = some type ∧
      Typed R .nil type (.head u) ∧ R.isUniverse u ∧ TypeLe R Γ (liftClosed type) T
  | .head h, T => ∃ u, R.headTyping h u ∧ TypeLe R Γ (.head u) T
  | .pi A B, T => ∃ u v w, Typed R Γ A (.head u) ∧ R.isUniverse u ∧
      Typed R (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧ R.join u v w ∧ TypeLe R Γ (.head w) T
  | .sigma A B, T => ∃ u v w, Typed R Γ A (.head u) ∧ R.isUniverse u ∧
      Typed R (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧ R.join u v w ∧ TypeLe R Γ (.head w) T
  | .id A a b, T => ∃ u, Typed R Γ A (.head u) ∧ R.isUniverse u ∧ Typed R Γ a A ∧
      Typed R Γ b A ∧ TypeLe R Γ (.head u) T
  | .lam body, T => ∃ A B u, Typed R Γ (.pi A B) (.head u) ∧ R.isUniverse u ∧
      Typed R (.snoc Γ A) body B ∧ TypeLe R Γ (.pi A B) T
  | .app f a, T => ∃ A B, Typed R Γ f (.pi A B) ∧ Typed R Γ a A ∧ TypeLe R Γ (inst0 a B) T
  | .pair a b, T => ∃ A B u, Typed R Γ (.sigma A B) (.head u) ∧ R.isUniverse u ∧
      Typed R Γ a A ∧ Typed R Γ b (inst0 a B) ∧ TypeLe R Γ (.sigma A B) T
  | .fst p, T => ∃ A B, Typed R Γ p (.sigma A B) ∧ TypeLe R Γ A T
  | .snd p, T => ∃ A B, Typed R Γ p (.sigma A B) ∧ TypeLe R Γ (inst0 (.fst p) B) T
  | .refl a, T => ∃ A, Typed R Γ a A ∧ TypeLe R Γ (.id A a a) T

/-- Generation is stable along the closure. -/
theorem GenerationAt.mono {n : Nat} {Γ : Ctx Head n} {t T T' : Tm Head n}
    (generation : GenerationAt R Γ t T) (le : TypeLe R Γ T T') : GenerationAt R Γ t T' := by
  cases t with
  | var i => exact TypeLe.trans generation le
  | const name =>
      obtain ⟨type, u, d, typing, hu, le'⟩ := generation
      exact ⟨type, u, d, typing, hu, le'.trans le⟩
  | head h =>
      obtain ⟨u, typing, le'⟩ := generation
      exact ⟨u, typing, le'.trans le⟩
  | pi A B =>
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le'⟩ := generation
      exact ⟨u, v, w, tA, hu, tB, hv, join, le'.trans le⟩
  | sigma A B =>
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le'⟩ := generation
      exact ⟨u, v, w, tA, hu, tB, hv, join, le'.trans le⟩
  | id A a b =>
      obtain ⟨u, tA, hu, ta, tb, le'⟩ := generation
      exact ⟨u, tA, hu, ta, tb, le'.trans le⟩
  | lam body =>
      obtain ⟨A, B, u, tPi, hu, tb, le'⟩ := generation
      exact ⟨A, B, u, tPi, hu, tb, le'.trans le⟩
  | app f a =>
      obtain ⟨A, B, tf, ta, le'⟩ := generation
      exact ⟨A, B, tf, ta, le'.trans le⟩
  | pair a b =>
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le'⟩ := generation
      exact ⟨A, B, u, tSigma, hu, ta, tb, le'.trans le⟩
  | fst p =>
      obtain ⟨A, B, tp, le'⟩ := generation
      exact ⟨A, B, tp, le'.trans le⟩
  | snd p =>
      obtain ⟨A, B, tp, le'⟩ := generation
      exact ⟨A, B, tp, le'.trans le⟩
  | refl a =>
      obtain ⟨A, ta, le'⟩ := generation
      exact ⟨A, ta, le'.trans le⟩

/-- What a derivation says: generation for typings, nothing for equalities. -/
def Generation (R : Rules Head) : Statement Head → Prop
  | .typing Γ t T => GenerationAt R Γ t T
  | .equality _ _ _ _ => True
  | .sub _ _ _ => True

/-- Generation for every derivable typing. -/
theorem Derivable.generation {st : Statement Head} (derivation : Derivable R st) :
    Generation R st := by
  induction derivation with
  | headType typing => exact ⟨_, typing, .refl _⟩
  | var i => exact .refl _
  | const declared typing hu => exact ⟨_, _, declared, typing, hu, .refl _⟩
  | piForm tA hu tB hv join => exact ⟨_, _, _, tA, hu, tB, hv, join, .refl _⟩
  | sigmaForm tA hu tB hv join => exact ⟨_, _, _, tA, hu, tB, hv, join, .refl _⟩
  | lamIntro tPi hu tb => exact ⟨_, _, _, tPi, hu, tb, .refl _⟩
  | appElim tf ta => exact ⟨_, _, tf, ta, .refl _⟩
  | pairIntro tSigma hu ta tb => exact ⟨_, _, _, tSigma, hu, ta, tb, .refl _⟩
  | fstElim tp => exact ⟨_, _, tp, .refl _⟩
  | sndElim tp => exact ⟨_, _, tp, .refl _⟩
  | idForm tA hu ta tb => exact ⟨_, tA, hu, ta, tb, .refl _⟩
  | reflIntro ta => exact ⟨_, ta, .refl _⟩
  | sub _ le ih => exact GenerationAt.mono ih (.of_below le)
  | conv _ e hu ih => exact GenerationAt.mono ih (.of_equal e hu)
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | convEq => trivial
  | subEq => trivial
  | headEq => trivial
  | piCong => trivial
  | sigmaCong => trivial
  | idCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | pairCong => trivial
  | fstCong => trivial
  | sndCong => trivial
  | reflCong => trivial
  | betaPi => trivial
  | betaFst => trivial
  | betaSnd => trivial
  | root => trivial
  | etaPi => trivial
  | etaSigma => trivial
  | subEqual => trivial
  | subUniv => trivial
  | subPi => trivial
  | subSigma => trivial
  | subTrans => trivial

/-! ## Induction on subtyping derivations

Subtyping is a statement form of the judgment, so its derivations are
derivations of the judgment. Induction on them is the induction on the five
subtyping rules, the other rules not concluding a subtyping statement. -/

/-- Induction on a derivation of `Γ ⊢ A ⊑ B`. -/
theorem Below.induction {motive : (n : Nat) → Ctx Head n → Tm Head n → Tm Head n → Prop}
    (equal : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head},
      Equal R Γ A B (.head u) → R.isUniverse u → motive n Γ A B)
    (univ : ∀ {n : Nat} {Γ : Ctx Head n} {u v : Head}, R.cumulative u v →
      motive n Γ (.head u) (.head v))
    (pi : ∀ {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      {u u' w : Head},
      Typed R Γ (.pi A B) (.head u) → R.isUniverse u →
      Typed R Γ (.pi A' B') (.head u') → R.isUniverse u' →
      Equal R Γ A A' (.head w) → R.isUniverse w →
      Below R (.snoc Γ A) B B' → motive (n + 1) (.snoc Γ A) B B' →
      motive n Γ (.pi A B) (.pi A' B'))
    (sigma : ∀ {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      {u u' : Head},
      Typed R Γ (.sigma A B) (.head u) → R.isUniverse u →
      Typed R Γ (.sigma A' B') (.head u') → R.isUniverse u' →
      Below R Γ A A' → Below R (.snoc Γ A) B B' → motive n Γ A A' →
      motive (n + 1) (.snoc Γ A) B B' → motive n Γ (.sigma A B) (.sigma A' B'))
    (trans : ∀ {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n},
      Below R Γ A B → Below R Γ B C → motive n Γ A B → motive n Γ B C → motive n Γ A C)
    {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (le : Below R Γ A B) : motive n Γ A B := by
  have key : ∀ {st : Statement Head}, Derivable R st →
      (match st with
        | @Statement.sub _ k Δ X Y => motive k Δ X Y
        | _ => True) := by
    intro st d
    induction d with
    | subEqual e hu _ => exact equal e hu
    | subUniv c => exact univ c
    | subPi tPi hu tPi' hu' eA hw leB _ _ _ ihB => exact pi tPi hu tPi' hu' eA hw leB ihB
    | subSigma tS hu tS' hu' leA leB _ _ ihA ihB => exact sigma tS hu tS' hu' leA leB ihA ihB
    | subTrans le₁ le₂ ih₁ ih₂ => exact trans le₁ le₂ ih₁ ih₂
    | headType => trivial
    | var => trivial
    | const => trivial
    | piForm => trivial
    | sigmaForm => trivial
    | lamIntro => trivial
    | appElim => trivial
    | pairIntro => trivial
    | fstElim => trivial
    | sndElim => trivial
    | idForm => trivial
    | reflIntro => trivial
    | sub => trivial
    | conv => trivial
    | refl => trivial
    | symm => trivial
    | trans => trivial
    | convEq => trivial
    | subEq => trivial
    | headEq => trivial
    | piCong => trivial
    | sigmaCong => trivial
    | idCong => trivial
    | lamCong => trivial
    | appCong => trivial
    | pairCong => trivial
    | fstCong => trivial
    | sndCong => trivial
    | reflCong => trivial
    | betaPi => trivial
    | betaFst => trivial
    | betaSnd => trivial
    | root => trivial
    | etaPi => trivial
    | etaSigma => trivial
  exact key le

/-- Generation for a typing. -/
theorem Typed.generation {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
    (typing : Typed R Γ t T) : GenerationAt R Γ t T :=
  Derivable.generation typing

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
