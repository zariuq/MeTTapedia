import Mettapedia.Languages.Agda.Adequacy.StaticRetraction
import Mettapedia.Languages.Agda.StaticSpecification.Context
import Mettapedia.Languages.Agda.Structural.ContextGeometry

/-!
# Raw static telescopes and lookup correspondence

Embedding retains every stored annotated declaration. Lookup agrees at both
the newest and older variables, including the weakening into the full scope.
The environment equations concern raw syntax; they do not admit an arbitrary
telescope or substitution as well typed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

def embedContext : {n : Nat} → StaticSpecification.RawContext n → Structural.ContextGeometry.RawContext n
  | _, .nil => .nil
  | _, .snoc prior type => .snoc (embedContext prior) (embedTy type)

def decodeContext : {n : Nat} → Structural.ContextGeometry.RawContext n →
    Option (StaticSpecification.RawContext n)
  | _, .nil => some .nil
  | _, .snoc prior type => do
      let prior ← decodeContext prior
      let type ← decodeTy type
      pure (.snoc prior type)

@[simp] theorem decodeContext_embedContext {n : Nat} (context : StaticSpecification.RawContext n) :
    decodeContext (embedContext context) = some context := by
  induction context with
  | nil => rfl
  | snoc prior type ih =>
      simp only [embedContext, decodeContext, ih, decodeTy_embedTy]
      rfl

theorem embedContext_of_decode {n : Nat} (context : Structural.ContextGeometry.RawContext n)
    {source : StaticSpecification.RawContext n} (decoded : decodeContext context = some source) :
    embedContext source = context := by
  induction context with
  | nil => cases Option.some.inj decoded; rfl
  | snoc prior type ih =>
      change (decodeContext prior).bind (fun prior =>
        (decodeTy type).bind (fun type => some (StaticSpecification.RawContext.snoc prior type))) =
          some source at decoded
      obtain ⟨prior', parsedPrior, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨type', parsedType, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      cases Option.some.inj decoded
      exact congrArg₂ Telescope.RawContext.snoc (ih parsedPrior) (embedTy_of_decode type parsedType)

theorem decodeContext_eq_some_iff {n : Nat} (context : Structural.ContextGeometry.RawContext n)
    (source : StaticSpecification.RawContext n) :
    decodeContext context = some source ↔ embedContext source = context := by
  constructor
  · exact embedContext_of_decode context
  · intro same; rw [← same, decodeContext_embedContext]

theorem embedContext_injective {n : Nat} : Function.Injective (embedContext (n := n)) := by
  intro first second same
  have decoded := congrArg decodeContext same
  simpa only [decodeContext_embedContext, Option.some.injEq] using decoded

theorem embedContext_lookup {n : Nat} (context : StaticSpecification.RawContext n) (index : Fin n) :
    embedTy (context.lookup index) =
      Structural.ContextGeometry.lookup (embedContext context) (embedVar index) := by
  induction context with
  | nil => exact Fin.elim0 index
  | snoc prior type ih =>
      refine Fin.cases ?_ (fun i => ?_) index
      · exact embedTy_weaken type
      · change embedTy (prior.lookup i).weaken =
          weaken (Structural.ContextGeometry.lookup (embedContext prior) (embedVar i))
        rw [embedTy_weaken, ih]
        rfl

theorem embedContext_lookup_subst {n m : Nat} (context : StaticSpecification.RawContext n)
    (index : Fin n) (σ : StaticSpecification.Substitution n m) :
    embedTy ((context.lookup index).subst σ) =
      bind (embedSub σ) (Structural.ContextGeometry.lookup (embedContext context) (embedVar index)) := by
  rw [embedTy_subst, embedContext_lookup]

/-- Exact preservation and reflection of the raw variable-type equation. -/
theorem renaming_respects_iff {n m : Nat} (Γ : StaticSpecification.RawContext n)
    (Δ : StaticSpecification.RawContext m) (ρ : StaticSpecification.Renaming n m) :
    StaticSpecification.Renaming.Respects Γ Δ ρ ↔
      ∀ v : Var (scope n) Structural.Srt.term,
        Structural.ContextGeometry.lookup (embedContext Δ) (embedRen ρ _ v) =
          rename (embedRen ρ) (Structural.ContextGeometry.lookup (embedContext Γ) v) := by
  constructor
  · intro respects v
    rw [← embed_readVar v, embedRen_var, ← embedContext_lookup, ← embedContext_lookup]
    rw [respects, embedTy_rename]
  · intro respects i
    apply embedTy_injective
    rw [embedTy_rename, embedContext_lookup, embedContext_lookup]
    rw [← embedRen_var]
    exact respects (embedVar i)

theorem embedSub_empty {m : Nat} :
    embedSub (Fin.elim0 : StaticSpecification.Substitution 0 m) =
      Telescope.emptySub (S := sig) Structural.Srt.term m :=
  Telescope.emptySub_unique _

/-- Source extension of an environment agrees with raw telescope pairing. -/
theorem embedSub_pair {n m : Nat} (σ : StaticSpecification.Substitution n m)
    (term : StaticSpecification.Term m) :
    embedSub (Fin.cases term σ) = Telescope.pair (embedSub σ) (embedTerm term) := by
  funext s v
  cases v <;> rfl

theorem embedSub_projection {n : Nat} :
    embedSub (fun i : Fin n => StaticSpecification.Term.var i.succ) =
      Telescope.projection (S := sig) Structural.Srt.term n := by
  funext s v
  have same := scope_sort v
  subst s
  rw [← embed_readVar v, embedSub_var]
  rfl

theorem embedSub_lift_telescope {n m : Nat} (σ : StaticSpecification.Substitution n m) :
    embedSub (StaticSpecification.Substitution.lift σ) = Telescope.lift (embedSub σ) :=
  embedSub_lift σ

theorem embedSub_comp_telescope {n m k : Nat} (σ : StaticSpecification.Substitution n m)
    (τ : StaticSpecification.Substitution m k) :
    embedSub (fun i => (σ i).subst τ) = Telescope.comp (embedSub σ) (embedSub τ) :=
  embedSub_comp σ τ

/-- The source variable environment embeds as the actual telescope identity. -/
theorem embedSub_identity_telescope {n : Nat} :
    embedSub (StaticSpecification.Term.var : StaticSpecification.Substitution n n) =
      Telescope.identity (S := sig) Structural.Srt.term n := embedSub_id

end Mettapedia.Languages.Agda.StaticAdequacy
