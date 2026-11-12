import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowUpdateRank

/-!
# Narrowing declarations at any position, as an update of the store

`ContextualDependentEtaDepth.narrowUpdate` narrows the newest declaration. Here the declarations lowered are
anywhere in the context: a **narrowing** of a context is the same telescope with some declarations that are
universes lowered (`ContextualDependentCumulative.CtxNarrows`); declarations that depend on a lowered one keep
their codes.

* `Narrowing`, `Narrowing.context`, `Narrowing.hom`: a narrowing of a context, and the morphism from it, which is
  the identity on codes.
* **`narrowingUpdate`**: reading the store over the narrowed context is an update with exactly the store's
  solutions, where every solution of the store is, as a typed substitution, equal to one into the narrowed context
  (`forced`).
* It keeps the weight rank (`narrowingUpdate_rank`) and the permuted Miller class (`narrowingUpdate_keeps`): it is
  a reading of the store, at any position.

What remains for a rule is the hypothesis `forced` from the shape of an equation, at an unknown that is not the
newest and under abstractions, and the declarations of applied unknowns, which are not universes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentRank
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentUniverseInjective
open ContextualDependentMillerClosure ContextualDependentCumulativeClosure ContextualDependentShortClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A narrowing of a context**: the same telescope with some universe declarations lowered. -/
structure Narrowing (Γ : Context S.R) where
  raw : Ctx Head Γ.arity
  formed : CtxFormed S.R raw
  narrows : CtxNarrows S.R Γ.raw raw

/-- The narrowed context. -/
def Narrowing.context {Γ : Context S.R} (narrowing : Narrowing Γ) : Context S.R :=
  ⟨Γ.arity, narrowing.raw, narrowing.formed⟩

/-- **The morphism from the narrowed context**: the identity on codes. -/
def Narrowing.hom {Γ : Context S.R} (narrowing : Narrowing Γ) : narrowing.context ⟶ Γ where
  substitution := ids
  typed := narrowing.narrows.substMor

theorem Narrowing.hom_substitution {Γ : Context S.R} (narrowing : Narrowing Γ) :
    narrowing.hom.substitution = ids := rfl

/-- **Narrowing declarations at any position**, as an update with exactly the store's solutions, where every
solution is equal to a substitution into the narrowed context. -/
def narrowingUpdate {Γ : Context S.R} (narrowing : Narrowing Γ) (problem : EquationStore (TotalTerm Γ))
    (forced : ∀ (Δ : Context S.R) (σ : Δ ⟶ Γ), (frames S.levels).Models σ problem →
      ∃ τ : Δ ⟶ narrowing.context, homTypedEquality S.R σ (τ ≫ narrowing.hom)) :
    Update S.levels problem where
  target := narrowing.context
  answer := narrowing.hom
  remaining := (frames S.levels).applyStore narrowing.hom problem
  sound := fun _ residual solved =>
    (Frames.models_applyStore (X := frames S.levels) narrowing.hom residual problem).mp solved
  complete := by
    intro Δ σ solved
    obtain ⟨τ, same⟩ := forced Δ σ solved
    exact ⟨τ,
      (Frames.models_applyStore (X := frames S.levels) narrowing.hom τ problem).mpr
        ((Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels same) problem).mp solved),
      act_equal_of_substEq S.levels same⟩

section Rank

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **A side keeps its normal weight** along the morphism from a narrowed context. -/
theorem sideWeight_narrowing {Γ : Context S.R} (narrowing : Narrowing Γ) (side : TotalTerm Γ) :
    sideWeight facts roots heads algebra rigid complete (side.reindex narrowing.hom) =
      sideWeight facts roots heads algebra rigid complete side := by
  have chosen := Classical.choose_spec
    (long_exists facts roots heads algebra rigid complete Γ.formed side.2.typed)
  have narrowed := NormalForm.narrow facts chosen narrowing.narrows Γ.formed narrowing.formed
  have normal : NormalForm S.R S.roles narrowing.context.raw (side.reindex narrowing.hom).2.code
      (Classical.choose (long_exists facts roots heads algebra rigid complete Γ.formed side.2.typed))
      (side.reindex narrowing.hom).1.code := by
    change NormalForm S.R S.roles narrowing.raw (subst narrowing.hom.substitution side.2.code) _
      (subst narrowing.hom.substitution side.1.code)
    rw [Narrowing.hom_substitution, subst_ids, subst_ids]
    exact narrowed
  rw [sideWeight_eq facts roots heads algebra rigid complete _ normal]
  rfl

include facts roots heads algebra complete in
/-- The transported store has the normal weight of the store. -/
theorem narrowing_weight {Γ : Context S.R} (narrowing : Narrowing Γ) :
    ∀ problem : EquationStore (TotalTerm Γ),
      storeWeight facts roots heads algebra rigid complete
          ((frames S.levels).applyStore narrowing.hom problem) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      change equationWeight facts roots heads algebra rigid complete
          (equation.1.reindex narrowing.hom, equation.2.reindex narrowing.hom) +
          storeWeight facts roots heads algebra rigid complete
            ((frames S.levels).applyStore narrowing.hom rest) =
        equationWeight facts roots heads algebra rigid complete equation +
          storeWeight facts roots heads algebra rigid complete rest
      rw [narrowing_weight narrowing rest]
      unfold equationWeight
      rw [sideWeight_narrowing facts roots heads algebra rigid complete narrowing equation.1,
        sideWeight_narrowing facts roots heads algebra rigid complete narrowing equation.2]

include facts roots heads algebra complete in
/-- **Narrowing declarations at any position keeps the weight rank**: it is a reading of the store. -/
theorem narrowingUpdate_rank {Γ : Context S.R} (narrowing : Narrowing Γ) (problem : EquationStore (TotalTerm Γ))
    (forced : ∀ (Δ : Context S.R) (σ : Δ ⟶ Γ), (frames S.levels).Models σ problem →
      ∃ τ : Δ ⟶ narrowing.context, homTypedEquality S.R σ (τ ≫ narrowing.hom)) :
    weightRank facts roots heads algebra rigid complete (narrowingUpdate narrowing problem forced).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change (Γ.arity, storeWeight facts roots heads algebra rigid complete
    ((frames S.levels).applyStore narrowing.hom problem)) =
      (Γ.arity, storeWeight facts roots heads algebra rigid complete problem)
  rw [narrowing_weight facts roots heads algebra rigid complete narrowing problem]

end Rank

/-- **Narrowing declarations at any position keeps the permuted Miller class**: the transported sides have the
codes of the sides. -/
theorem narrowingUpdate_keeps {Γ : Context S.R} (narrowing : Narrowing Γ) (problem : EquationStore (TotalTerm Γ))
    (forced : ∀ (Δ : Context S.R) (σ : Δ ⟶ Γ), (frames S.levels).Models σ problem →
      ∃ τ : Δ ⟶ narrowing.context, homTypedEquality S.R σ (τ ≫ narrowing.hom))
    (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (narrowingUpdate narrowing problem forced).remaining :=
  PermutedMiller.applyStore_of_sides narrowing.hom permuted fun equation member => by
    have sides := PermutedMiller.sides_of_mem permuted member
    have code : ∀ c : Tm Head Γ.arity, subst narrowing.hom.substitution c = c := fun c => by
      rw [Narrowing.hom_substitution]
      exact subst_ids c
    have left : ((equation.1.reindex narrowing.hom, equation.2.reindex narrowing.hom) :
        Equation (TotalTerm narrowing.context)).1.2.code = equation.1.2.code := code _
    have right : ((equation.1.reindex narrowing.hom, equation.2.reindex narrowing.hom) :
        Equation (TotalTerm narrowing.context)).2.2.code = equation.2.2.code := code _
    unfold FragmentSidesMiller
    rw [left, right]
    exact sides

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
