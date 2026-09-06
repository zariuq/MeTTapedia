import Mettapedia.Logic.HOL.Soundness
import Mettapedia.GSLT.Core.GSLT
import Mathlib.Logic.Relation

/-!
# Using intrinsic HOL proofs to establish operational invariants

A derivation, satisfaction of its assumptions, and interpretation of the
operational symbols are separate inputs. Soundness turns the derivation into
one-step preservation; induction then transports the property along finite
runs. No external proof format or source-checker adapter is assumed here.

The model may be a non-full Henkin model. Operational states must have
admissible interpretations. Runs that additionally use equations require a
separate equation-invariance premise.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.TransitionInvariant

universe u v w z

variable {Base : Type u} {Const : Ty Base → Type v}
  {Γ : Ctx Base} {σ : Ty Base}

/-- The closed-over-two-states formula saying that a relation preserves a
predicate. The surrounding HOL context is retained. -/
def preservationFormula (relation : Term Const Γ (σ ⇒ σ ⇒ .prop))
    (predicate : Term Const Γ (σ ⇒ .prop)) : Formula Const Γ :=
  .all (.all
    (.imp
      (.app (.app (weaken (weaken relation)) (.var (.vs .vz))) (.var .vz))
      (.imp (.app (weaken (weaken predicate)) (.var (.vs .vz)))
        (.app (weaken (weaken predicate)) (.var .vz)))))

/-- Quantified preservation has precisely its independently interpreted
relational meaning, over the model's admitted state domain. -/
theorem denote_preservationFormula (M : HenkinModel.{u, v, w} Base Const)
    (ρ : HenkinModel.Valuation M Γ)
    (relation : Term Const Γ (σ ⇒ σ ⇒ .prop))
    (predicate : Term Const Γ (σ ⇒ .prop)) :
    (HenkinModel.denote M (preservationFormula relation predicate) ρ).down ↔
      ∀ x, M.adm σ x → ∀ y, M.adm σ y →
        (HenkinModel.denote M relation ρ x y).down →
        (HenkinModel.denote M predicate ρ x).down →
        (HenkinModel.denote M predicate ρ y).down := by
  simp only [preservationFormula, HenkinModel.denote, PreModel.denote_all,
    PreModel.denote_imp]
  simp only [PreModel.denote, Soundness.denote_weaken]
  rfl

/-- Pointwise implication between two relations on the same typed states. -/
def refinementFormula (source target : Term Const Γ (σ ⇒ σ ⇒ .prop)) :
    Formula Const Γ :=
  .all (.all
    (.imp (.app (.app (weaken (weaken source)) (.var (.vs .vz))) (.var .vz))
      (.app (.app (weaken (weaken target)) (.var (.vs .vz))) (.var .vz))))

theorem denote_refinementFormula (M : HenkinModel.{u, v, w} Base Const)
    (ρ : HenkinModel.Valuation M Γ)
    (source target : Term Const Γ (σ ⇒ σ ⇒ .prop)) :
    (HenkinModel.denote M (refinementFormula source target) ρ).down ↔
      ∀ x, M.adm σ x → ∀ y, M.adm σ y →
        (HenkinModel.denote M source ρ x y).down →
        (HenkinModel.denote M target ρ x y).down := by
  simp only [refinementFormula, HenkinModel.denote, PreModel.denote_all,
    PreModel.denote_imp]
  simp only [PreModel.denote, Soundness.denote_weaken]
  rfl

/-- An actual intrinsic HOL derivation of invariant transport along relation
refinement. Its conclusion is composed from two distinct assumptions exposing
the independently justified semantic interfaces used by the consumer. -/
theorem preservation_of_refinement
    (source target : Const (σ ⇒ σ ⇒ .prop)) (predicate : Const (σ ⇒ .prop)) :
    Derivation Const
      [refinementFormula (Γ := Γ) (.const source) (.const target),
        preservationFormula (.const target) (.const predicate)]
      (preservationFormula (.const source) (.const predicate)) := by
  apply Derivation.allI
  apply Derivation.allI
  apply Derivation.impI
  apply Derivation.impI
  let localHypotheses : List (Formula Const (σ :: σ :: Γ)) :=
    [.app (.const predicate) (.var (.vs .vz)),
      .app (.app (.const source) (.var (.vs .vz))) (.var .vz)] ++
      weakenHyps (weakenHyps
        [refinementFormula (.const source) (.const target),
          preservationFormula (.const target) (.const predicate)])
  change Derivation Const localHypotheses (.app (.const predicate) (.var .vz))
  have sourceHypothesis : Derivation Const localHypotheses
      (.app (.app (.const source) (.var (.vs .vz))) (.var .vz)) :=
    .hyp (by simp [localHypotheses])
  have predicateHypothesis : Derivation Const localHypotheses
      (.app (.const predicate) (.var (.vs .vz))) :=
    .hyp (by simp [localHypotheses])
  have refinement : Derivation Const localHypotheses
      (refinementFormula (.const source) (.const target)) :=
    .hyp (by simp [localHypotheses, weakenHyps, refinementFormula, weaken, rename,
      Rename.lift, Rename.weaken])
  have preservation : Derivation Const localHypotheses
      (preservationFormula (.const target) (.const predicate)) :=
    .hyp (by simp [localHypotheses, weakenHyps, preservationFormula, weaken, rename,
      Rename.lift, Rename.weaken])
  have refinementAtSource := Derivation.allE
    (.var (.vs .vz) : Term Const (σ :: σ :: Γ) σ) refinement
  have refinementAtPair : Derivation Const localHypotheses
      (.imp (.app (.app (.const source) (.var (.vs .vz))) (.var .vz))
        (.app (.app (.const target) (.var (.vs .vz))) (.var .vz))) := by
    simpa [refinementFormula, instantiate, subst, Subst.single, Subst.lift,
      weaken, rename, Rename.lift, Rename.weaken] using
      (Derivation.allE (.var .vz) refinementAtSource)
  have preservationAtSource := Derivation.allE
    (.var (.vs .vz) : Term Const (σ :: σ :: Γ) σ) preservation
  have preservationAtPair : Derivation Const localHypotheses
      (.imp (.app (.app (.const target) (.var (.vs .vz))) (.var .vz))
        (.imp (.app (.const predicate) (.var (.vs .vz)))
          (.app (.const predicate) (.var .vz)))) := by
    simpa [preservationFormula, instantiate, subst, Subst.single, Subst.lift,
      weaken, rename, Rename.lift, Rename.weaken] using
      (Derivation.allE (.var .vz) preservationAtSource)
  exact .impE (.impE preservationAtPair (.impE refinementAtPair sourceHypothesis))
    predicateHypothesis

/-- An intrinsic proof supplies a genuine operational preservation theorem
when its hypotheses and symbol interpretation are independently validated. -/
theorem step_preserves
    {State : Type z} {step : State → State → Prop} {property : State → Prop}
    {relation : Term Const Γ (σ ⇒ σ ⇒ .prop)}
    {predicate : Term Const Γ (σ ⇒ .prop)}
    {hypotheses : List (Formula Const Γ)}
    (derivation : Derivation Const hypotheses
      (preservationFormula relation predicate))
    (M : HenkinModel.{u, v, w} Base Const)
    (ρ : HenkinModel.Valuation M Γ)
    (valuation : HenkinModel.ValuationAdmissible M ρ)
    (assumptions : Soundness.SatisfiesHyps M ρ hypotheses)
    (interpret : State → Ty.denote M.Carrier σ)
    (admissible : ∀ state, M.adm σ (interpret state))
    (relation_meaning : ∀ source target,
      (HenkinModel.denote M relation ρ (interpret source) (interpret target)).down ↔
        step source target)
    (predicate_meaning : ∀ state,
      (HenkinModel.denote M predicate ρ (interpret state)).down ↔ property state)
    {source target : State} (transition : step source target)
    (holds : property source) : property target := by
  have valid := Soundness.derivation_sound derivation valuation assumptions
  have preserved := (denote_preservationFormula M ρ relation predicate).mp valid
  exact (predicate_meaning target).mp
    (preserved (interpret source) (admissible source) (interpret target)
      (admissible target) ((relation_meaning source target).mpr transition)
      ((predicate_meaning source).mpr holds))

/-- The same proof-use contract applies to every finite run of the specified
relation, without requiring a full-domain model or termination of all runs. -/
theorem finite_run_preserves
    {State : Type z} {step : State → State → Prop} {property : State → Prop}
    {relation : Term Const Γ (σ ⇒ σ ⇒ .prop)}
    {predicate : Term Const Γ (σ ⇒ .prop)}
    {hypotheses : List (Formula Const Γ)}
    (derivation : Derivation Const hypotheses
      (preservationFormula relation predicate))
    (M : HenkinModel.{u, v, w} Base Const)
    (ρ : HenkinModel.Valuation M Γ)
    (valuation : HenkinModel.ValuationAdmissible M ρ)
    (assumptions : Soundness.SatisfiesHyps M ρ hypotheses)
    (interpret : State → Ty.denote M.Carrier σ)
    (admissible : ∀ state, M.adm σ (interpret state))
    (relation_meaning : ∀ source target,
      (HenkinModel.denote M relation ρ (interpret source) (interpret target)).down ↔
        step source target)
    (predicate_meaning : ∀ state,
      (HenkinModel.denote M predicate ρ (interpret state)).down ↔ property state)
    {source target : State} (run : Relation.ReflTransGen step source target)
    (holds : property source) : property target := by
  induction run with
  | refl => exact holds
  | tail run transition inductionHypothesis =>
      exact step_preserves derivation M ρ valuation assumptions interpret
        admissible relation_meaning predicate_meaning transition inductionHypothesis

/-- Equations can be interleaved with operational steps only after the
property's equation invariance has also been proved. -/
theorem finite_run_modulo_preserves
    {system : Mettapedia.GSLT.GSLT.{z}} {property : system.Term → Prop}
    {relation : Term Const Γ (σ ⇒ σ ⇒ .prop)}
    {predicate : Term Const Γ (σ ⇒ .prop)}
    {hypotheses : List (Formula Const Γ)}
    (derivation : Derivation Const hypotheses
      (preservationFormula relation predicate))
    (M : HenkinModel.{u, v, w} Base Const)
    (ρ : HenkinModel.Valuation M Γ)
    (valuation : HenkinModel.ValuationAdmissible M ρ)
    (assumptions : Soundness.SatisfiesHyps M ρ hypotheses)
    (interpret : system.Term → Ty.denote M.Carrier σ)
    (admissible : ∀ state, M.adm σ (interpret state))
    (relation_meaning : ∀ source target,
      (HenkinModel.denote M relation ρ (interpret source) (interpret target)).down ↔
        system.Step source target)
    (predicate_meaning : ∀ state,
      (HenkinModel.denote M predicate ρ (interpret state)).down ↔ property state)
    (equations : ∀ {source target}, system.Equiv source target →
      (property source ↔ property target))
    {source target : system.Term}
    (run : Relation.ReflTransGen
      (fun first last => system.Equiv first last ∨ system.Step first last)
      source target)
    (holds : property source) : property target := by
  induction run with
  | refl => exact holds
  | tail run transition inductionHypothesis =>
      rcases transition with equivalent | transition
      · exact (equations equivalent).mp inductionHypothesis
      · exact step_preserves derivation M ρ valuation assumptions interpret
          admissible relation_meaning predicate_meaning transition inductionHypothesis

#print axioms step_preserves
#print axioms preservation_of_refinement
#print axioms finite_run_preserves
#print axioms finite_run_modulo_preserves

end Mettapedia.Logic.HOL.TransitionInvariant
