import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthArgGap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSigma

/-!
# A gap in the spine decomposition: spines of one local at a Σ base, and its repair

Over `A : U0, F : A → A`, at `Π (h : A → Σ (x : U0). U0) (y : A). Σ (x : U0). U0`, the equation
**`λ h y. h y ≐ λ h y. h (F y)`** (`sigmaStore`) is in the dynamic pattern fragment (`sigma_in_fragment`) and solvable
by `F := λ y. y` (`sigma_solvable`). Its sides are spines of the local `h`, of one skeleton, η-long at the
annotation's Π count, at the base `Σ (x : U0). U0`. The η-expansion of the η-depth families stops at Π types, and both
decompositions between spines of one local read spines only at a rigid base (a universe, an identity type or a
local), so at a Σ base they read no pieces at any budget (`sigma_parts_none`), and the piece family is stuck in its
first round (`sigma_piece_stuck`). The same holds for `λ h y z. h y ≐ λ h y z. h z`, whose arguments are distinct
locals (`sigmaDistinct_piece_stuck`).

**The repair.** The Σ family, which η-expands spines of a bound local at a Σ base into the pairs of their projections,
commits on the first store (`sigma_sigma_committed`) and refutes the second with a certified refutation
(`sigmaDistinct_sigma_refuted`), so that store is unsolvable (`sigmaDistinct_unsolvable`). It keeps the outcomes of the
piece family on R119's 44 census stores (`sigma_of_final`).

**Projections along reducts.** At `Π (h : Π (G : U0 → U1). G A) (y : A). Σ U0 U0`, the equation
`λ h y. h (λ x. x → Σ U0 U0) y ≐ λ h y. h (λ x. x → Σ U0 U0) (F y)` (`comboStore`) is in the fragment
(`combo_in_fragment`) and solvable (`combo_solvable`). Its η-expanded form at the Σ base decomposes into the
projections of the two spines, and R99's projection reading reads the binders of the local's type literally, which
here hide behind the redex `(λ x. x → Σ U0 U0) A`, so it reads no pieces at any budget (`combo_projection_none`). The
reading along the reducts of the instantiated types reads projections of spines too (`DepRel.proj`), and on the
η-expanded form the piece family commits (`pairedCombo_piece_committed`); the Σ family moves in its first round on the
store itself (`combo_sigma_moves`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.SigmaControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls

/-- `Π (h : A → Σ (x : U0). U0) (y : A). Σ (x : U0). U0` over `A, F : A → A`. -/
def sigmaHigher : TypeOver ctxAF := formIn ctxAF
  (.pi (.pi (.var 1) (.sigma u0 u0)) (.pi (.var 2) (.sigma u0 u0))) (by decide +kernel)

/-- `λ h y. h y ≐ λ h y. h (F y)` at a Σ base. -/
def sigmaEquation : Equation (TotalTerm ctxAF) :=
  (termIn ctxAF sigmaHigher (.lam (.lam (.app (.var 1) (.var 0)))) (by decide +kernel),
    termIn ctxAF sigmaHigher (.lam (.lam (.app (.var 1) (.app (.var 2) (.var 0))))) (by decide +kernel))
def sigmaStore : EquationStore (TotalTerm ctxAF) := [sigmaEquation]

theorem sigma_in_fragment : InFragmentStore sigmaStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl sigmaEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem sigma_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution sigmaEquation.1.2.code) (subst answer.substitution sigmaEquation.2.2.code)
      (subst answer.substitution sigmaEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable**, by `F := λ y. y`. -/
theorem sigma_solvable : (frames setting.levels).Solvable sigmaStore := by
  refine ⟨ctxA, answer, (models_iff setting.levels answer sigmaStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(sigmaHigher.reindex answer).isType.refl, ?_⟩
  have check := sigma_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution sigmaEquation.1.2.code) (subst answer.substitution sigmaEquation.2.2.code)
      (subst answer.substitution sigmaEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ctxA.formed (sigmaEquation.1.2.reindex answer).typed (sigmaEquation.2.2.reindex answer).typed

/-- **Neither decomposition between spines of one local reads pieces** on the equation, at any budget. -/
theorem sigma_parts_none (fuel : Nat) :
    ContextualDependentSpinesMany.dependentUnder [] sigmaEquation.1.1.code sigmaEquation.1.2.code
        sigmaEquation.2.2.code = none ∧
      dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer fuel [] sigmaEquation.1.1.code
        sigmaEquation.1.2.code sigmaEquation.2.2.code = none :=
  ⟨by decide +kernel, rfl⟩

/-- **The piece family is stuck in its first round** on the store, at budget 16. -/
theorem sigma_piece_stuck : isStuck (run (pieceTower.solver 16) sigmaStore 1) = true := by decide +kernel

/-- `Π (h : A → Σ (x : U0). U0) (y z : A). Σ (x : U0). U0` over `A`. -/
def sigmaHigherYZ : TypeOver ctxA := formIn ctxA
  (.pi (.pi (.var 0) (.sigma u0 u0)) (.pi (.var 1) (.pi (.var 2) (.sigma u0 u0)))) (by decide +kernel)

/-- `λ h y z. h y ≐ λ h y z. h z` at a Σ base. -/
def sigmaDistinct : EquationStore (TotalTerm ctxA) :=
  [(termIn ctxA sigmaHigherYZ (.lam (.lam (.lam (.app (.var 2) (.var 1))))) (by decide +kernel),
    termIn ctxA sigmaHigherYZ (.lam (.lam (.lam (.app (.var 2) (.var 0))))) (by decide +kernel))]

/-- **The piece family is stuck in its first round on the distinct store too**, at budget 16. -/
theorem sigmaDistinct_piece_stuck : isStuck (run (pieceTower.solver 16) sigmaDistinct 1) = true := by
  decide +kernel

/-! ## The repair -/

/-- **The Σ family commits on the store.** -/
theorem sigma_sigma_committed : (run (sigmaTower.solver 16) sigmaStore 8).readout = .commit := by decide +kernel

/-- **The Σ family refutes the distinct store**, with a certified refutation. -/
theorem sigmaDistinct_sigma_refuted : (run (sigmaTower.solver 16) sigmaDistinct 8).readout = .refuted := by
  decide +kernel

theorem sigmaDistinct_unsolvable : ¬ (frames setting.levels).Solvable sigmaDistinct :=
  Outcome.readout_eq_refuted sigmaDistinct_sigma_refuted

/-! ## Projections of spines whose local type hides a binder behind a redex -/

/-- `Π (h : Π (G : U0 → U1). G A) (y : A). Σ U0 U0` over `A, F : A → A`. -/
def comboHigher : TypeOver ctxAF := formIn ctxAF
  (.pi (.pi (.pi u0 u1) (.app (.var 0) (.var 2))) (.pi (.var 2) (.sigma u0 u0))) (by decide +kernel)

/-- `λ x. x → Σ U0 U0`. -/
def arrowSigma {n : Nat} : Tower.Tm n := .lam (.pi (.var 0) (.sigma u0 u0))

/-- `λ h y. h (λ x. x → Σ U0 U0) y ≐ λ h y. h (λ x. x → Σ U0 U0) (F y)`. -/
def comboEquation : Equation (TotalTerm ctxAF) :=
  (termIn ctxAF comboHigher (.lam (.lam (.app (.app (.var 1) arrowSigma) (.var 0)))) (by decide +kernel),
    termIn ctxAF comboHigher (.lam (.lam (.app (.app (.var 1) arrowSigma) (.app (.var 2) (.var 0)))))
      (by decide +kernel))
def comboStore : EquationStore (TotalTerm ctxAF) := [comboEquation]

theorem combo_in_fragment : InFragmentStore comboStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl comboEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem combo_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution comboEquation.1.2.code) (subst answer.substitution comboEquation.2.2.code)
      (subst answer.substitution comboEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable**, by `F := λ y. y`. -/
theorem combo_solvable : (frames setting.levels).Solvable comboStore := by
  refine ⟨ctxA, answer, (models_iff setting.levels answer comboStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(comboHigher.reindex answer).isType.refl, ?_⟩
  have check := combo_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution comboEquation.1.2.code) (subst answer.substitution comboEquation.2.2.code)
      (subst answer.substitution comboEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ctxA.formed (comboEquation.1.2.reindex answer).typed (comboEquation.2.2.reindex answer).typed

/-- Its η-expanded form at the Σ base, the pair of projections of each side. -/
def pairedCombo : EquationStore (TotalTerm ctxAF) :=
  [(termIn ctxAF comboHigher (.lam (.lam (.pair (.fst (.app (.app (.var 1) arrowSigma) (.var 0)))
      (.snd (.app (.app (.var 1) arrowSigma) (.var 0)))))) (by decide +kernel),
    termIn ctxAF comboHigher (.lam (.lam (.pair (.fst (.app (.app (.var 1) arrowSigma) (.app (.var 2) (.var 0))))
      (.snd (.app (.app (.var 1) arrowSigma) (.app (.var 2) (.var 0))))))) (by decide +kernel))]

/-- **On the η-expanded form the piece family commits**: it decomposes the pairs, then reads the projections of the
spines along the reducts of the instantiated types. -/
theorem pairedCombo_piece_committed : (run (pieceTower.solver 16) pairedCombo 8).readout = .commit := by
  decide +kernel

/-- **The Σ family moves in its first round on the store.** -/
theorem combo_sigma_moves : isStuck (run (sigmaTower.solver 16) comboStore 1) = false := by decide +kernel

/-- **R99's projection reading reads no pieces on the first projections**, at any budget: it reads the binders of
the local's type literally. -/
theorem combo_projection_none :
    ContextualDependentConstantHeadsProjections.projUnder [] comboEquation.1.1.code
      (.lam (.lam (.fst (.app (.app (.var 1) arrowSigma) (.var 0)))))
      (.lam (.lam (.fst (.app (.app (.var 1) arrowSigma) (.app (.var 2) (.var 0)))))) = none := by
  decide +kernel

open ContextualDependentIntersectionGeneral.InPlaceControls ContextualDependentIntersectionGeneral.DeadControls in
/-- **R119's census under the Σ family.** -/
theorem sigma_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run (sigmaTower.solver 16) problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := PieceControls.piece_of_final final
  refine ⟨decided, ?_⟩
  have pieceDecided : (run (pieceTower.solver 16) problem 8).Decided := by rw [same]; exact decided
  rw [← same]
  exact sigma_run_of_piece (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem
    pieceDecided

end ContextualDependentEtaDepth.SigmaControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
