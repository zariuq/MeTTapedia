import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbControls

/-!
# Strict initiality: which principal answers are initial

A solved run of the tree's driver ends with a principal answer (`Frames.Principal`): every solution factors through
it. It is **the initial solution** (`InitialSolution`) when, in addition, the factor is unique up to the fibre's
equality; `Principal.initial` gives this for an answer that is an epimorphism on terms.

* **Covered answers are epimorphisms** (`epi_of_covered`): when every unknown of the answer's telescope is the image
  of an unknown of the store's telescope, declared at a family with the same domains and a codomain above, two
  morphisms that agree on the answer's image agree on every term. Equality at the larger family is equality at the
  smaller one for terms of the smaller (`Lowers.equal_iff`).
* **Principal and covered is initial** (`initial_of_covered`). The identity (`id_covered`) and a codomain lowering
  (`CodomainLowering.covered`) are covered.
* **Solving in place is not initial** (`level_answer_not_initial`): the greatest-lower-bound rule on two level
  variables keeps the solved unknown `X` declared; the identity and the morphism sending `X` to `Y` give the same
  composite with the answer and are not equal. Strict initiality needs the solved unknowns deleted from the answer's
  telescope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Covered answers -/

section Covered

/-- **Every unknown of `Δ` is the image of an unknown of `Θ`**, declared at a family with the same domains and a
codomain above. -/
def Covered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) : Prop :=
  ∀ j : Fin Δ.arity, ∃ (i : Fin Θ.arity) (ps : List Head) (c c' : Head), σ.substitution i = .var j ∧
    Ctx.lookup Δ.raw j = famCode ps c ∧ Ctx.lookup Θ.raw i = famCode ps c' ∧ AllUniverses S.R ps ∧
    S.R.isUniverse c ∧ S.R.isUniverse c' ∧ S.R.cumulative c c'

/-- The total term of an unknown at its declaration. -/
noncomputable def unknownTerm (Θ : Context S.R) (i : Fin Θ.arity) : TotalTerm Θ :=
  ⟨⟨Ctx.lookup Θ.raw i, Classical.choose (Θ.formed.lookup i), (Classical.choose_spec (Θ.formed.lookup i)).1,
      (Classical.choose_spec (Θ.formed.lookup i)).2⟩,
    ⟨.var i, Derivable.var (R := S.R) (Γ := Θ.raw) i⟩⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Covered answers are epimorphisms on terms.** -/
theorem epi_of_covered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (covered : Covered σ) :
    EpiOnTerms (frames S.levels) σ := by
  intro b g h agree
  refine act_equal_of_substEq S.levels ⟨g.typed, fun j => ?_⟩
  obtain ⟨i, ps, c, c', hi, dj, di, ups, uc, uc', below⟩ := covered j
  have e := (agree (unknownTerm Θ i)).2
  change Equal S.R b.raw (Presentation.subst g.substitution (Presentation.subst σ.substitution (.var i)))
    (Presentation.subst h.substitution (Presentation.subst σ.substitution (.var i)))
    (Presentation.subst g.substitution (Presentation.subst σ.substitution (Ctx.lookup Θ.raw i))) at e
  rw [di, famCode_subst, famCode_subst] at e
  change Equal S.R b.raw (Presentation.subst g.substitution (σ.substitution i))
    (Presentation.subst h.substitution (σ.substitution i)) (famCode ps c') at e
  rw [hi] at e
  change Equal S.R b.raw (g.substitution j) (h.substitution j) (famCode ps c') at e
  rw [dj, famCode_subst]
  have tg : Typed S.R b.raw (g.substitution j) (famCode ps c) := by
    have typed := g.typed j
    rw [dj, famCode_subst] at typed
    exact typed
  have th : Typed S.R b.raw (h.substitution j) (famCode ps c) := by
    have typed := h.typed j
    rw [dj, famCode_subst] at typed
    exact typed
  exact (Lowers.equal_iff facts roots heads algebra rigid complete (lowers_famCode ps uc uc' below) b.formed
    (famCode_isType ps ups uc b.formed) (famCode_isType ps ups uc' b.formed) tg th).mp e

include facts roots heads algebra rigid complete in
/-- **A principal answer that is covered is the initial solution.** -/
theorem initial_of_covered {Δ Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {σ : Δ ⟶ Θ}
    (principal : (frames S.levels).Principal problem σ) (covered : Covered σ) :
    InitialSolution (frames S.levels) problem σ :=
  Principal.initial principal (epi_of_covered facts roots heads algebra rigid complete σ covered)

end Covered

/-! ## Positive examples -/

section Examples

/-- **The identity is covered**, on a telescope of universe families. -/
theorem id_covered {Θ : Context S.R}
    (families : ∀ i : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw i = famCode ps c ∧
      AllUniverses S.R ps ∧ S.R.isUniverse c) : Covered (𝟙 Θ) := by
  intro j
  obtain ⟨ps, c, dj, ups, uc⟩ := families j
  exact ⟨j, ps, c, c, rfl, dj, dj, ups, uc, uc, S.levels.cumulative_refl uc⟩

/-- **A codomain lowering is covered**, on a telescope of universe families. -/
theorem CodomainLowering.covered {Θ : Context S.R} (ℓ : CodomainLowering Θ)
    (families : ∀ i : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw i = famCode ps c ∧
      AllUniverses S.R ps ∧ S.R.isUniverse c) : Covered ℓ.hom := by
  intro j
  by_cases hj : j = ℓ.index
  · subst hj
    exact ⟨ℓ.index, ℓ.ps, ℓ.lower, ℓ.upper, rfl, ℓ.lookup_self, ℓ.declared, ℓ.universes, ℓ.universe_lower,
      ℓ.universe_upper, ℓ.below⟩
  · obtain ⟨ps, c, dj, ups, uc⟩ := families j
    exact ⟨j, ps, c, c, rfl, (ℓ.lookup_ne hj).trans dj, dj, ups, uc, uc, S.levels.cumulative_refl uc⟩

end Examples

/-! ## Solving in place is not initial -/

namespace Controls

open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- The telescope after the greatest-lower-bound rule on `levelStore`: `X Y : U0 → U0`. -/
noncomputable abbrev levelTarget : Context setting.R := levelGlbUpdate.target

/-- The unknowns `X` and `Y` of the target. -/
def targetX : Fin levelTarget.arity := ⟨1, by show 1 < 2; decide⟩
def targetY : Fin levelTarget.arity := ⟨0, by show 0 < 2; decide⟩

/-- Both unknowns of the target are declared at `U0 → U0`. -/
theorem levelTarget_lookup : ∀ i : Fin levelTarget.arity, Ctx.lookup levelTarget.raw i = famCode [U0] U0 := by
  decide +kernel

/-- `X := Y`, `Y := Y`, on the target. -/
noncomputable def levelMerge : levelTarget ⟶ levelTarget where
  substitution := fun _ => .var targetY
  typed := by
    intro i
    have typed := Derivable.var (R := setting.R) (Γ := levelTarget.raw) targetY
    rw [levelTarget_lookup targetY] at typed
    change Typed setting.R levelTarget.raw (.var targetY) (Presentation.subst _ (Ctx.lookup levelTarget.raw i))
    rw [levelTarget_lookup i, famCode_subst]
    exact typed

/-- **The merge fixes the answer**: the answer's image mentions `Y` only. -/
theorem levelMerge_answer :
    ∀ i : Fin ctxAB.arity, Presentation.subst levelMerge.substitution (levelGlbUpdate.answer.substitution i) =
      levelGlbUpdate.answer.substitution i := by
  decide +kernel

/-- The merge fixes every term of the answer's image, up to the fibre's equality. -/
theorem levelMerge_agrees (t : TotalTerm ctxAB) :
    (frames setting.levels).E ((frames setting.levels).act levelMerge ((frames setting.levels).act levelGlbUpdate.answer t))
      ((frames setting.levels).act levelGlbUpdate.answer t) := by
  have codes : ∀ code : Tm Tower.Head ctxAB.arity,
      Presentation.subst levelMerge.substitution (Presentation.subst levelGlbUpdate.answer.substitution code) =
        Presentation.subst levelGlbUpdate.answer.substitution code := by
    intro code
    rw [subst_comp]
    congr 1
    funext i
    exact levelMerge_answer i
  refine ⟨?_, ?_⟩
  · change TypeEq setting.R levelTarget.raw
      (Presentation.subst levelMerge.substitution (Presentation.subst levelGlbUpdate.answer.substitution t.1.code))
      (Presentation.subst levelGlbUpdate.answer.substitution t.1.code)
    rw [codes]
    exact ⟨t.1.level, t.1.universeWitness, .refl (t.1.formed.substitute levelGlbUpdate.answer.typed)⟩
  · change Equal setting.R levelTarget.raw
      (Presentation.subst levelMerge.substitution (Presentation.subst levelGlbUpdate.answer.substitution t.2.code))
      (Presentation.subst levelGlbUpdate.answer.substitution t.2.code)
      (Presentation.subst levelMerge.substitution (Presentation.subst levelGlbUpdate.answer.substitution t.1.code))
    rw [codes, codes]
    exact .refl (t.2.typed.substitute levelGlbUpdate.answer.typed)

/-- **The answer of the greatest-lower-bound rule on two level variables is not the initial solution**: it keeps
the solved unknown `X` declared, and the identity and the merge `X := Y` give the same composite with it. -/
theorem level_answer_not_initial :
    ¬ InitialSolution (frames setting.levels) levelStore levelGlbUpdate.answer := by
  intro initial
  have agreeId : Agree (frames setting.levels) levelGlbUpdate.answer
      ((frames setting.levels).comp (𝟙 levelTarget) levelGlbUpdate.answer) :=
    agree_id_comp (X := frames setting.levels) levelGlbUpdate.answer
  have agreeMerge : Agree (frames setting.levels) levelGlbUpdate.answer
      ((frames setting.levels).comp levelMerge levelGlbUpdate.answer) := by
    intro t
    rw [(frames setting.levels).act_comp]
    exact ((frames setting.levels).equivalence _).symm (levelMerge_agrees t)
  have both := initial.unique levelTarget levelGlbUpdate.answer (𝟙 levelTarget) levelMerge agreeId agreeMerge
  have atX := (both (unknownTerm levelTarget targetX)).2
  change Equal setting.R levelTarget.raw (Presentation.subst ids (.var targetX)) (.var targetY)
    (Presentation.subst ids (Ctx.lookup levelTarget.raw targetX)) at atX
  rw [subst_ids, subst_ids] at atX
  exact Miller.var_ne_var ContextualDependentPiSpine.Controls.rigid TowerModel.complete levelTarget.formed
    (by decide) atX

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
