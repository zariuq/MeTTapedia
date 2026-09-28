import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Relation

/-!
# Contexts of equal types

What the algorithmic equality needs from the typed equality besides the facts
about the weak-head forms of types (`FormFacts`): contexts whose entries are
equal types have the same typings, equalities and typed reductions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Contexts of equal types -/

/-- Contexts of equal types, entry by entry, each equality stated in the
second context. -/
inductive CtxEq (R : Rules Head) : {n : Nat} → Ctx Head n → Ctx Head n → Prop where
  | nil : CtxEq R .nil .nil
  | snoc {n : Nat} {Γ Δ : Ctx Head n} {A B : Tm Head n} :
      CtxEq R Γ Δ → TypeEq R Δ B A → CtxEq R (.snoc Γ A) (.snoc Δ B)

section Stability

variable {R : Rules Head}

theorem CtxEq.lookup {n : Nat} {Γ Δ : Ctx Head n} (equal : CtxEq R Γ Δ) :
    ∀ i, TypeEq R Δ (Ctx.lookup Δ i) (Ctx.lookup Γ i) := by
  induction equal with
  | nil => intro i; exact i.elim0
  | @snoc n Γ Δ A B _ last ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact last.rename (CtxRen.wk Δ B)
      · exact (ih j).rename (CtxRen.wk Δ B)

theorem CtxEq.substMor {n : Nat} {Γ Δ : Ctx Head n} (equal : CtxEq R Γ Δ) :
    SubstMor R Γ Δ ids := by
  intro i
  rw [subst_ids]
  exact Typed.convType (Derivable.var i) (equal.lookup i)

theorem CtxEq.refl {n : Nat} : ∀ (Γ : Ctx Head n), CtxFormed R Γ → CtxEq R Γ Γ
  | .nil, _ => .nil
  | .snoc Γ _, .snoc formed isType => .snoc (CtxEq.refl Γ formed) isType.refl

theorem Typed.stable {n : Nat} {Γ Δ : Ctx Head n} {t A : Tm Head n} (typing : Typed R Γ t A)
    (equal : CtxEq R Γ Δ) : Typed R Δ t A := by
  simpa only [subst_ids] using Typed.substitute typing equal.substMor

theorem Equal.stable {n : Nat} {Γ Δ : Ctx Head n} {a b A : Tm Head n} (equality : Equal R Γ a b A)
    (equal : CtxEq R Γ Δ) : Equal R Δ a b A := by
  simpa only [subst_ids] using Equal.substitute equality equal.substMor

theorem TypeEq.stable {n : Nat} {Γ Δ : Ctx Head n} {A B : Tm Head n} (equality : TypeEq R Γ A B)
    (equal : CtxEq R Γ Δ) : TypeEq R Δ A B := by
  obtain ⟨u, hu, e⟩ := equality
  exact ⟨u, hu, Equal.stable e equal⟩

theorem IsType.stable {n : Nat} {Γ Δ : Ctx Head n} {A : Tm Head n} (isType : IsType R Γ A)
    (equal : CtxEq R Γ Δ) : IsType R Δ A := by
  obtain ⟨u, hu, t⟩ := isType
  exact ⟨u, hu, Typed.stable t equal⟩

theorem RedTm.stable {roles : Roles Head} {n : Nat} {Γ Δ : Ctx Head n} {t u A : Tm Head n}
    (red : RedTm R roles Γ t u A) (equal : CtxEq R Γ Δ) : RedTm R roles Δ t u A :=
  ⟨red.red, Typed.stable red.source equal, Typed.stable red.target equal,
    Equal.stable red.equal equal⟩

theorem RedTy.stable {roles : Roles Head} {n : Nat} {Γ Δ : Ctx Head n} {A B : Tm Head n}
    (red : RedTy R roles Γ A B) (equal : CtxEq R Γ Δ) : RedTy R roles Δ A B := by
  obtain ⟨u, hu, tA, tB, e⟩ := red.sort
  exact ⟨red.red, u, hu, Typed.stable tA equal, Typed.stable tB equal, Equal.stable e equal⟩

theorem CtxEq.snocSame {n : Nat} {Γ Δ : Ctx Head n} {A : Tm Head n} (equal : CtxEq R Γ Δ)
    (isType : IsType R Γ A) : CtxEq R (.snoc Γ A) (.snoc Δ A) :=
  .snoc equal (isType.stable equal).refl

end Stability

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
