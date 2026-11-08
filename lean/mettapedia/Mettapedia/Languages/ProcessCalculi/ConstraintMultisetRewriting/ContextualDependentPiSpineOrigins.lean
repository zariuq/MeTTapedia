import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineVariables

/-!
# Outer and rigid-variable origins in a dependent Pi spine

Every final variable is uniquely either an outer-context variable or one
introduced by the telescope. The origin equivalence is computed from the
actual spine. Reindexing preserves the local origins and their declaration
types, while outer variables follow the supplied substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpine

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax

variable {Head : Type} {rules : Rules Head}

private def moveFirst {n : Nat} (Tail : Type) : (Fin n ⊕ (Unit ⊕ Tail)) ≃ (Fin (n + 1) ⊕ Tail) where
  toFun
    | .inl index => .inl index.succ
    | .inr (.inl _) => .inl 0
    | .inr (.inr index) => .inr index
  invFun
    | .inl index => Fin.cases (.inr (.inl ())) (fun previous => .inl previous) index
    | .inr index => .inr (.inr index)
  left_inv := by
    intro origin
    rcases origin with index | (⟨⟩ | index) <;> rfl
  right_inv := by
    intro origin
    rcases origin with index | index
    · exact Fin.cases rfl (fun _ => rfl) index
    · rfl

namespace Spine

def Local : {Γ : Context rules} → {type : TypeOver Γ} → Spine type → Type
  | _, _, .stop _ => Empty
  | _, _, .bind _ rest => Unit ⊕ rest.Local

def originEquiv : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    (Fin Γ.arity ⊕ spine.Local) ≃ Fin spine.target.arity
  | _, _, .stop _ =>
      ⟨Sum.elim id Empty.elim, Sum.inl,
        (by intro origin; rcases origin with index | impossible; rfl; exact impossible.elim), fun _ => rfl⟩
  | _, _, .bind _ rest => (moveFirst rest.Local).trans rest.originEquiv

theorem outer_origin {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ index, spine.originEquiv (.inl index) = spine.outerRen index := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih => intro index; exact ih index.succ

def localIndex {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (index : spine.Local) : Fin spine.target.arity :=
  spine.originEquiv (.inr index)

theorem localIndex_head {Γ : Context rules} (shape : ContextualDependentPiShape.Shape Γ) (rest : Spine shape.codomain) :
    (Spine.bind shape rest).localIndex (.inl ()) = rest.outerRen 0 := rest.outer_origin 0

theorem localIndex_tail {Γ : Context rules} (shape : ContextualDependentPiShape.Shape Γ) (rest : Spine shape.codomain)
    (index : rest.Local) : (Spine.bind shape rest).localIndex (.inr index) = rest.localIndex index := rfl

theorem localIndex_injective {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) : Function.Injective spine.localIndex := by
  intro first second same
  exact Sum.inr.inj (spine.originEquiv.injective same)

theorem outer_ne_local {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (outer : Fin Γ.arity) (localIndex : spine.Local) : spine.outerRen outer ≠ spine.localIndex localIndex := by
  intro same
  rw [← spine.outer_origin] at same
  have impossible := spine.originEquiv.injective same
  cases impossible

theorem variable_cases {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (index : Fin spine.target.arity) :
    (∃ outer, spine.outerRen outer = index) ∨ ∃ localIndex, spine.localIndex localIndex = index := by
  obtain ⟨origin, image⟩ := spine.originEquiv.surjective index
  rcases origin with outer | localIndex
  · exact .inl ⟨outer, (spine.outer_origin outer).symm.trans image⟩
  · exact .inr ⟨localIndex, image⟩

def localReindexEquiv : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    {Δ : Context rules} → (base : Δ ⟶ Γ) → (spine.reindex base).Local ≃ spine.Local
  | _, _, .stop _, _, _ => Equiv.refl Empty
  | _, _, .bind shape rest, _, base => Equiv.sumCongr (Equiv.refl Unit) (rest.localReindexEquiv (rawLift base shape.domain))

theorem map_local {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (index : (spine.reindex base).Local),
      (spine.map base).substitution (spine.localIndex (spine.localReindexEquiv base index)) =
        .var ((spine.reindex base).localIndex index) := by
  induction spine with
  | stop type => intro Δ base index; exact index.elim
  | bind shape rest ih =>
      intro Δ base index
      rcases index with ⟨⟩ | index
      · change (rest.map (rawLift base shape.domain)).substitution (rest.originEquiv (.inl 0)) =
          .var ((rest.reindex (rawLift base shape.domain)).originEquiv (.inl 0))
        rw [rest.outer_origin, (rest.reindex (rawLift base shape.domain)).outer_origin, rest.map_outer]
        rfl
      · exact ih (rawLift base shape.domain) index

theorem local_lookup_reindex {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (index : (spine.reindex base).Local),
      Ctx.lookup (spine.reindex base).target.raw ((spine.reindex base).localIndex index) =
        subst (spine.map base).substitution (Ctx.lookup spine.target.raw (spine.localIndex (spine.localReindexEquiv base index))) := by
  induction spine with
  | stop type => intro Δ base index; exact index.elim
  | bind shape rest ih =>
      intro Δ base index
      rcases index with ⟨⟩ | index
      · change Ctx.lookup (rest.reindex (rawLift base shape.domain)).target.raw
          ((rest.reindex (rawLift base shape.domain)).originEquiv (.inl 0)) =
          subst (rest.map (rawLift base shape.domain)).substitution (Ctx.lookup rest.target.raw (rest.originEquiv (.inl 0)))
        rw [rest.outer_origin, (rest.reindex (rawLift base shape.domain)).outer_origin,
          (rest.reindex (rawLift base shape.domain)).outerRen_compatible, rest.outerRen_compatible, rest.map_outer_term]
        change Presentation.rename _ (Presentation.rename wk (subst base.substitution shape.domain.code)) =
          Presentation.rename _ (subst (liftSub base.substitution) (Presentation.rename wk shape.domain.code))
        rw [subst_liftSub_wk]
      · exact ih (rawLift base shape.domain) index

end Spine
end ContextualDependentPiSpine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
