import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowUpdate

/-!
# Narrowing the newest declaration keeps the weight rank and the permuted Miller class

The update of `ContextualDependentEtaDepth.narrowUpdate` transports the store along a morphism that is the identity
on codes (`narrowHom_substitution`). An η-long normal form over the wide context is one over the narrowed context
(`NormalForm.narrow`), so every side keeps its normal weight (`sideWeight_narrow`) and the update keeps both
components of the weight rank (`narrowUpdate_rank`). So the update is a reading of the store, as the least
annotation is: a round of the family on its residual store, when it progresses, lowers the rank of the store. The
transported sides have the codes of the sides, so the permuted Miller class is kept (`narrowUpdate_keeps`).

**Where the update applies** (`holds_forced`, `narrowAt`): at an equation annotated at a universe whose left side
is a type of the smaller universe and whose right side holds the newest unknown at a type position
(`ContextualDependentUniverseInjective.HoldsVar`). The conditions are on the codes of the store. They cover an
equation at the top of the store and the newest unknown; an unknown that is not the newest, an applied unknown and
an equation under an abstraction are not covered.
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

/-- **The morphism from the narrowed context is the identity on codes.** -/
theorem narrowHom_substitution (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head}
    (smallCode : small.code = .head u) (wideCode : wide.code = .head v) (lower : S.R.cumulative u v) :
    (narrowHom Γ wide small smallCode wideCode lower).substitution = ids := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

section Rank

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **A side keeps its normal weight** along the morphism from the narrowed context. -/
theorem sideWeight_narrow (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head}
    (smallCode : small.code = .head u) (wideCode : wide.code = .head v) (lower : S.R.cumulative u v)
    (side : TotalTerm (extend Γ wide)) :
    sideWeight facts roots heads algebra rigid complete
        (side.reindex (narrowHom Γ wide small smallCode wideCode lower)) =
      sideWeight facts roots heads algebra rigid complete side := by
  have chosen := Classical.choose_spec
    (long_exists facts roots heads algebra rigid complete (extend Γ wide).formed side.2.typed)
  have narrows : CtxNarrows S.R (extend Γ wide).raw (extend Γ small).raw := by
    change CtxNarrows S.R (.snoc Γ.raw wide.code) (.snoc Γ.raw small.code)
    rw [wideCode, smallCode]
    exact .lower (CtxNarrows.refl Γ.raw) lower
  have narrowed := NormalForm.narrow facts chosen narrows (extend Γ wide).formed (extend Γ small).formed
  have normal : NormalForm S.R S.roles (extend Γ small).raw
      (side.reindex (narrowHom Γ wide small smallCode wideCode lower)).2.code
      (Classical.choose (long_exists facts roots heads algebra rigid complete (extend Γ wide).formed side.2.typed))
      (side.reindex (narrowHom Γ wide small smallCode wideCode lower)).1.code := by
    change NormalForm S.R S.roles (extend Γ small).raw
      (subst (narrowHom Γ wide small smallCode wideCode lower).substitution side.2.code) _
      (subst (narrowHom Γ wide small smallCode wideCode lower).substitution side.1.code)
    rw [narrowHom_substitution, subst_ids, subst_ids]
    exact narrowed
  rw [sideWeight_eq facts roots heads algebra rigid complete _ normal]
  rfl

include facts roots heads algebra complete in
/-- The transported store has the normal weight of the store. -/
theorem narrow_weight (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head}
    (smallCode : small.code = .head u) (wideCode : wide.code = .head v) (lower : S.R.cumulative u v) :
    ∀ problem : EquationStore (TotalTerm (extend Γ wide)),
      storeWeight facts roots heads algebra rigid complete
          ((frames S.levels).applyStore (narrowHom Γ wide small smallCode wideCode lower) problem) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      change equationWeight facts roots heads algebra rigid complete
          (equation.1.reindex (narrowHom Γ wide small smallCode wideCode lower),
            equation.2.reindex (narrowHom Γ wide small smallCode wideCode lower)) +
          storeWeight facts roots heads algebra rigid complete
            ((frames S.levels).applyStore (narrowHom Γ wide small smallCode wideCode lower) rest) =
        equationWeight facts roots heads algebra rigid complete equation +
          storeWeight facts roots heads algebra rigid complete rest
      rw [narrow_weight Γ wide small smallCode wideCode lower rest]
      unfold equationWeight
      rw [sideWeight_narrow facts roots heads algebra rigid complete Γ wide small smallCode wideCode lower
          equation.1,
        sideWeight_narrow facts roots heads algebra rigid complete Γ wide small smallCode wideCode lower equation.2]

/-- **Narrowing the newest declaration keeps the weight rank**: it is a reading of the store, not a step. -/
theorem narrowUpdate_rank (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head}
    (smallCode : small.code = .head u) (wideCode : wide.code = .head v) (lower : S.R.cumulative u v)
    (hv : S.R.isUniverse v) (problem : EquationStore (TotalTerm (extend Γ wide)))
    (forced : ∀ (Δ : Context S.R) (σ : Δ ⟶ extend Γ wide), (frames S.levels).Models σ problem →
      ∃ value, Typed S.R Δ.raw value (.head u) ∧ TypeEq S.R Δ.raw value (σ.substitution 0)) :
    weightRank facts roots heads algebra rigid complete
        (narrowUpdate facts roots heads algebra rigid complete Γ wide small smallCode wideCode lower hv problem
          forced).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change ((extend Γ small).arity, storeWeight facts roots heads algebra rigid complete
    ((frames S.levels).applyStore (narrowHom Γ wide small smallCode wideCode lower) problem)) =
      ((extend Γ wide).arity, storeWeight facts roots heads algebra rigid complete problem)
  rw [narrow_weight facts roots heads algebra rigid complete Γ wide small smallCode wideCode lower problem]

/-- **Narrowing the newest declaration keeps the permuted Miller class**: the transported sides have the codes of
the sides. -/
theorem narrowUpdate_keeps (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head}
    (smallCode : small.code = .head u) (wideCode : wide.code = .head v) (lower : S.R.cumulative u v)
    (hv : S.R.isUniverse v) (problem : EquationStore (TotalTerm (extend Γ wide)))
    (forced : ∀ (Δ : Context S.R) (σ : Δ ⟶ extend Γ wide), (frames S.levels).Models σ problem →
      ∃ value, Typed S.R Δ.raw value (.head u) ∧ TypeEq S.R Δ.raw value (σ.substitution 0))
    (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels
      (narrowUpdate facts roots heads algebra rigid complete Γ wide small smallCode wideCode lower hv problem
        forced).remaining :=
  PermutedMiller.applyStore_of_sides (narrowHom Γ wide small smallCode wideCode lower) permuted
    fun equation member => by
      have sides := PermutedMiller.sides_of_mem permuted member
      have code : ∀ c : Tm Head (extend Γ wide).arity,
          subst (narrowHom Γ wide small smallCode wideCode lower).substitution c = c := fun c => by
        rw [narrowHom_substitution]
        exact subst_ids c
      have left : ((equation.1.reindex (narrowHom Γ wide small smallCode wideCode lower),
          equation.2.reindex (narrowHom Γ wide small smallCode wideCode lower)) :
            Equation (TotalTerm (extend Γ small))).1.2.code = equation.1.2.code := code _
      have right : ((equation.1.reindex (narrowHom Γ wide small smallCode wideCode lower),
          equation.2.reindex (narrowHom Γ wide small smallCode wideCode lower)) :
            Equation (TotalTerm (extend Γ small))).2.2.code = equation.2.2.code := code _
      unfold FragmentSidesMiller
      rw [left, right]
      exact sides

include facts roots heads algebra rigid complete in
/-- **Where the update applies.** An equation of the store, annotated at a universe, whose left side is a type of
the smaller universe and whose right side holds the newest unknown at a type position: in every solution the value
of the newest unknown is equal to a type of the smaller universe. -/
theorem holds_forced {Γ : Context S.R} {wide : TypeOver Γ} {problem : EquationStore (TotalTerm (extend Γ wide))}
    {u a : Head} (hu : S.R.isUniverse u) (ha : S.R.isUniverse a)
    {equation : Equation (TotalTerm (extend Γ wide))} (member : equation ∈ problem)
    (annotated : equation.1.1.code = .head a)
    (small : Typed S.R (extend Γ wide).raw equation.1.2.code (.head u))
    (holds : HoldsVar (Head := Head) (0 : Fin (Γ.arity + 1)) equation.2.2.code)
    (Δ : Context S.R) (σ : Δ ⟶ extend Γ wide) (solved : (frames S.levels).Models σ problem) :
    ∃ value, Typed S.R Δ.raw value (.head u) ∧ TypeEq S.R Δ.raw value (σ.substitution 0) := by
  obtain ⟨_, equal⟩ :=
    (ContextualDependentRigidFormers.solves_raw (S := S) σ equation).mp (solved equation member)
  rw [annotated] at equal
  exact HoldsVar.small facts roots heads algebra rigid complete holds Δ.formed hu σ.substitution
    (small.substitute σ.typed) ⟨a, ha, equal⟩

/-- **The narrowing update at an equation that forces it**: the newest unknown is declared at a universe, a
smaller universe lies below it, and an equation of the store, annotated at a universe, has a left side that is a
type of the smaller universe and a right side that holds the newest unknown at a type position. -/
def narrowAt (Γ : Context S.R) (wide small : TypeOver Γ) {u v a : Head} (smallCode : small.code = .head u)
    (wideCode : wide.code = .head v) (lower : S.R.cumulative u v) (hu : S.R.isUniverse u)
    (hv : S.R.isUniverse v) (ha : S.R.isUniverse a) (problem : EquationStore (TotalTerm (extend Γ wide)))
    {equation : Equation (TotalTerm (extend Γ wide))} (member : equation ∈ problem)
    (annotated : equation.1.1.code = .head a)
    (typed : Typed S.R (extend Γ wide).raw equation.1.2.code (.head u))
    (holds : HoldsVar (Head := Head) (0 : Fin (Γ.arity + 1)) equation.2.2.code) : Update S.levels problem :=
  narrowUpdate facts roots heads algebra rigid complete Γ wide small smallCode wideCode lower hv problem
    (holds_forced facts roots heads algebra rigid complete hu ha member annotated typed holds)

end Rank

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
