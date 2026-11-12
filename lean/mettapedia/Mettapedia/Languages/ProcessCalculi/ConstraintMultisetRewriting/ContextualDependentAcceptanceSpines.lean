import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptanceFinalSigma
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsSpines

/-!
# The row of spines of one local, by shape; a conditional decision from the rows outside the shapes

R121's covered rows (`PieceCoveredHead`) held one row conditioned on an executable reading: the η-long sides are read
by `dependentUnderN` from some budget on. On a census head with normal codes that condition is exactly the shape of two
spines of one bound local at a rigid base (`LocalSpines`): the shape is read from some budget on
(`localSpines_reads`), and a reading has the shape (`pieceCovered_iff_shapeCovered`). So the covered rows are stated by
shape alone (`ShapeCoveredHead`): every row is a predicate on the codes of the census head, with no budget in it.

**A conditional decision** (`tower_sigma_decided_of_unread`): if every census head of a constant preparation outside
the shapes is read from some budget on, the Σ family decides every store of the dynamic pattern fragment, with a
principal answer or a certified refutation, constant at every larger budget. The hypothesis holds the pattern rows, the
rows at a Σ base, and the rows at a base type that is not rigid, among them the base types that are applications, at
which the Σ family is stuck (`ContextualDependentEtaDepth.BaseControls`). At the tower the hypothesis fails: the
conclusion would decide `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentCoverageReadersHalf ContextualDependentConstantHeads ContextualDependentMillerClosure
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4 ContextualDependentSpinesMany

/-- **The η-long sides of an equation with equal annotations are typed at its left annotation.** -/
theorem expanded_typed {Γ : Context setting.R} (equation : Equation (TotalTerm Γ))
    (types : TypeEq setting.R Γ.raw equation.1.1.code equation.2.1.code) :
    TypedEquality.Typed setting.R Γ.raw (expandTo (piCount equation.1.1.code) equation.1.2.code)
        equation.1.1.code ∧
      TypedEquality.Typed setting.R Γ.raw (expandTo (piCount equation.1.1.code) equation.2.2.code)
        equation.1.1.code :=
  ⟨(Equal.typed (expand_equal TowerModel.facts _ Γ.formed equation.1.2.typed le_rfl) Γ.formed).2,
    (Equal.typed (expand_equal TowerModel.facts _ Γ.formed
      (Typed.convType equation.2.2.typed (TypeEq.symm types)) le_rfl) Γ.formed).2⟩

/-- **The row of spines of one local is read by shape**: on an equation with normal codes and equal annotations whose
η-long sides are spines of one bound local at a rigid base, the reading along the reducts of the instantiated types
reads the sides from some budget on. -/
theorem localSpines_reads {Γ : Context setting.R} {equation : Equation (TotalTerm Γ)}
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R Γ.raw equation.1.1.code equation.2.1.code)
    (shape : LocalSpines 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)) :
    ∃ bound, ∀ larger, bound ≤ larger → (dependentUnderN (S := setting)
      ContextualDependentInversion.Controls.reducer larger [] equation.1.1.code
      (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome :=
  tower_dependentUnderN_reads shape Γ.formed (LocalTypes.nil _) rfl
    (fun _ member => absurd member List.not_mem_nil) normal.1 (expanded_typed equation types).1
    (expanded_typed equation types).2

/-- **The census rows read, by shape alone**: R121's rows, with the row of spines of one local read along reducts
stated by its shape. -/
def ShapeCoveredHead {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Prop :=
  CoveredHead equation ∨
    (dependentUnder [] equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome ∨
    (underParts (S := setting) equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome ∨
    LocalSpines 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)

/-- **On normal codes with equal annotations the covered rows are the rows by shape.** -/
theorem pieceCovered_iff_shapeCovered {Γ : Context setting.R} {equation : Equation (TotalTerm Γ)}
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R Γ.raw equation.1.1.code equation.2.1.code) :
    PieceCoveredHead equation ↔ ShapeCoveredHead equation := by
  constructor
  · rintro (covered | spine | under | ⟨bound, reads⟩)
    · exact .inl covered
    · exact .inr (.inl spine)
    · exact .inr (.inr (.inl under))
    · obtain ⟨pieces, found⟩ := Option.isSome_iff_exists.mp (reads bound le_rfl)
      exact .inr (.inr (.inr (dependentUnderN_rel _ bound [] _ _ _ found).localSpines))
  · rintro (covered | spine | under | shape)
    · exact .inl covered
    · exact .inr (.inl spine)
    · exact .inr (.inr (.inl under))
    · exact .inr (.inr (.inr (localSpines_reads normal types shape)))

/-- **A census head in a row by shape is read** by the Σ family from some budget on. -/
theorem tower_sigmaReads_of_shape {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (covered : ShapeCoveredHead equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerSigmaReads larger problem :=
  tower_sigmaReads_of_covered constant member normal types
    ((pieceCovered_iff_shapeCovered normal types).mpr covered)

/-- **Conditional decision for the tower's Σ family, from the census rows outside the shapes**: if every census head
of a constant preparation whose η-long opened sides are of a census kind and outside the rows by shape is read from
some budget on, the family decides every store of the dynamic pattern fragment, with a principal answer or a certified
refutation, constant at every larger budget. At the tower the hypothesis fails: the conclusion would decide
`crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_sigma_decided_of_unread
    (unread : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ContextualDependentShortClosure.FragmentSidesMiller equation →
          Kind (openedFlexible (piCount equation.1.1.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.1.2.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.2.2.code)) →
          ¬ ShapeCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerSigmaReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (sigmaTower.solver larger) problem larger = run (sigmaTower.solver budget) problem budget ∧
      ((∃ state finished, run (sigmaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (sigmaTower.solver larger) problem larger = .refuted absent)) :=
  tower_sigma_decided_of_uncovered_kinds (fun permuted nonempty threshold constant equation member normal head sides
      kind covered =>
      unread permuted nonempty threshold constant equation member normal head sides kind fun shape =>
        covered ((pieceCovered_iff_shapeCovered normal head.1).mpr shape))
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
