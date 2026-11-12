import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptanceSpines

/-!
# The census row of spines of one local at every base type; a conditional decision for the base family

**The row.** A census head of a constant preparation whose η-long sides are spines of one bound local, with equally
many arguments and at least one, at an annotation that is a base type as it stands (`AnySpines`), is read by the base
family from some budget on (`tower_baseReads_of_anySpines`). The row has no condition on the head of the base type: a
universe, an identity type, a bound local, a metavariable, an application or a projection of either. It contains the
two stores on which the Σ family is stuck (`ContextualDependentEtaDepth.BaseControls`).

**A conditional decision for the base family, from the census rows outside the shapes**
(`tower_base_decided_of_unread`): if every census head of a constant preparation outside the rows by shape
(`BaseCoveredHead`) is read from some budget on, the family decides every store of the dynamic pattern fragment, with
a principal answer or a certified refutation, constant at every larger budget. The hypothesis holds the pattern rows,
the rows at a Σ base, and elimination spines that mix projections and applications. At the tower it fails: the
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
open ContextualDependentRank ContextualDependentSpinesMany ContextualDependentCoverageReadersHalf
open ContextualDependentConstantHeads ContextualDependentMillerClosure
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4

/-- The tower's decomposition at every base type. -/
abbrev towerDecomposeBase (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  decomposeBase (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices fuel problem

/-- **A store is read by the base family** from some budget on, when an equation of its η-long prepared store with
homogeneous twins, at one budget past the twins' constancy, is eventually read by the decomposition at every base
type. -/
theorem tower_baseReads_of_fixed {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPreparedTwins larger problem = towerPreparedTwins threshold problem)
    {equation : Equation (TotalTerm (towerPreparedTwins threshold problem).target)}
    (member : equation ∈ expandStore TowerModel.facts (towerPreparedTwins threshold problem).remaining)
    {bound : Nat}
    (read : ∀ larger, bound ≤ larger → (baseNormal (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices larger equation).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem := by
  refine ⟨max threshold bound, fun larger enough => Or.inr ?_⟩
  change (towerDecomposeBase larger (expandStore TowerModel.facts (towerPreparedTwins larger problem).remaining)).isSome
  rw [constant larger ((le_max_left _ _).trans enough)]
  exact decomposeBase_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices larger member
    (read larger ((le_max_right _ _).trans enough))

/-- **A census head whose η-long sides are eventually read as spines of one local at a base type is read** by the
base family from some budget on. -/
theorem tower_baseReads_of_spines {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (split : ∃ bound, ∀ larger, bound ≤ larger → (spinesUnderN (S := setting)
      ContextualDependentInversion.Controls.reducer larger [] equation.1.1.code
      (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem := by
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types
    (fun A l r => ∃ bound, ∀ larger, bound ≤ larger → (spinesUnderN (S := setting)
      ContextualDependentInversion.Controls.reducer larger [] A (expandTo (piCount A) l)
      (expandTo (piCount A) r)).isSome) split
  obtain ⟨settled, twinsConst⟩ := tower_preparedTwins_const problem
  have fixed := twinsConst (max bound settled) (le_max_right _ _)
  have kept : ∀ larger, max bound settled ≤ larger →
      towerPreparedTwins larger problem = towerPreparedTwins (max bound settled) problem := fun larger enough =>
    (twinsConst larger ((le_max_right _ _).trans enough)).trans fixed.symm
  obtain ⟨twin, twinMember, same, readBound, twinRead⟩ := twins (max bound settled) (le_max_left _ _)
  have expandedMember := longUpdate_mem (S := setting) TowerModel.facts twinMember
  have sameExpanded : (expandSide TowerModel.facts twin.2).1.code = (expandSide TowerModel.facts twin.1).1.code := same
  have rightCode : (expandSide TowerModel.facts twin.2).2.code = expandTo (piCount twin.1.1.code) twin.2.2.code := by
    change expandTo (piCount twin.2.1.code) twin.2.2.code = _
    rw [same]
  obtain ⟨settledRead, readConst⟩ := (readSpines_const (S := setting) ContextualDependentInversion.Controls.reducer
    ContextualDependentDecisiveFragment.Controls.stable (expandSide TowerModel.facts twin.1).1.code
    (expandSide TowerModel.facts twin.1).2.code (expandSide TowerModel.facts twin.2).2.code).spec
  have readAt : (readSpines (S := setting) ContextualDependentInversion.Controls.reducer (max settledRead readBound)
      (expandSide TowerModel.facts twin.1).1.code (expandSide TowerModel.facts twin.1).2.code
      (expandSide TowerModel.facts twin.2).2.code).isSome := by
    rw [← Option.isSome_map (f := Subtype.val), readSpines_val, rightCode]
    exact twinRead _ (le_max_right _ _)
  obtain ⟨read, readComputed⟩ := Option.isSome_iff_exists.mp readAt
  have readKept : ∀ larger, max settledRead readBound ≤ larger →
      readSpines (S := setting) ContextualDependentInversion.Controls.reducer larger
        (expandSide TowerModel.facts twin.1).1.code (expandSide TowerModel.facts twin.1).2.code
        (expandSide TowerModel.facts twin.2).2.code = some read := fun larger enough =>
    ((readConst larger ((le_max_left _ _).trans enough)).trans
      (readConst _ (le_max_left _ _)).symm).trans readComputed
  have typed := read.property.typed TowerModel.facts TowerModel.roots TowerModel.heads
    (towerPreparedTwins (max bound settled) problem).target.formed (LocalTypes.nil _)
    (expandSide TowerModel.facts twin.1).2.typed
    (by have tr := (expandSide TowerModel.facts twin.2).2.typed; rw [sameExpanded] at tr; exact tr)
  obtain ⟨formedBound, formed⟩ := tower_formNormal_eventually read.val typed
  exact tower_baseReads_of_fixed kept expandedMember (bound := max (max settledRead readBound) formedBound)
    fun larger enough =>
    baseNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices larger sameExpanded (readKept larger ((le_max_left _ _).trans enough))
      fun typed' =>
        formNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
          ContextualDependentPiSpine.Controls.rigid TowerModel.complete
          ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
          ExecutableTowerChoices.choices larger read.val typed'
          (formed larger ((le_max_right _ _).trans enough))

/-- **The row of spines of one local at every base type is read**: a census head with normal codes whose η-long
sides are spines of one bound local at a base type as it stands is read by the base family from some budget on. -/
theorem tower_baseReads_of_anySpines {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (shape : AnySpines 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem :=
  tower_baseReads_of_spines constant member types
    (tower_spinesUnderN_reads shape (towerPrepare threshold problem).target.formed (LocalTypes.nil _) rfl
      (fun _ inside => absurd inside List.not_mem_nil) normal.1 (expanded_typed equation types).1
      (expanded_typed equation types).2)

/-! ## The row read on the opened sides -/

/-- **The shape of the opened sides is the shape of the sides**: at a depth no greater than the annotation's Π count
and the sides' abstraction depths. -/
theorem anySpines_of_opened {Head : Type} {n d : Nat} {annotation left right : Tm Head n}
    (typeDepth : d ≤ piCount annotation) (leftDepth : d ≤ ContextualDependentPatternSolver.lamDepth left)
    (rightDepth : d ≤ ContextualDependentPatternSolver.lamDepth right)
    (shape : AnySpines d (piOpen d annotation) (ContextualDependentCensus.openNormal d left)
      (ContextualDependentCensus.openNormal d right)) :
    AnySpines 0 annotation left right := by
  suffices every : ∀ j k, k + j = d →
      AnySpines k (piOpen k annotation) (ContextualDependentCensus.openNormal k left)
        (ContextualDependentCensus.openNormal k right) from every d 0 (by omega)
  intro j
  induction j with
  | zero =>
      intro k same
      obtain rfl : k = d := by omega
      exact shape
  | succ j ih =>
      intro k same
      have inner := ih (k + 1) (by omega)
      obtain ⟨D, typeCode⟩ := piOpen_pi (code := annotation) (count := k) (by omega)
      rw [typeCode, openNormal_lam (code := left) (count := k) (by omega),
        openNormal_lam (code := right) (count := k) (by omega)]
      exact .under inner

/-- **The census row in the census's own terms**: a census head with normal codes whose η-long opened sides are
spines of one bound local, with equally many arguments and at least one, at an annotation whose type under its Π
binders is a base type as it stands, is read by the base family from some budget on. -/
theorem tower_baseReads_of_sameLocal {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    {h : Fin ((towerPrepare threshold problem).target.arity + piCount equation.1.1.code)}
    {as bs : List (Tower.Tm ((towerPrepare threshold problem).target.arity + piCount equation.1.1.code))}
    (leftSpine : ContextualDependentCensus.openNormal (piCount equation.1.1.code)
      (expandTo (piCount equation.1.1.code) equation.1.2.code) = appSpine (.var h) as)
    (rightSpine : ContextualDependentCensus.openNormal (piCount equation.1.1.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code) = appSpine (.var h) bs)
    (base : anyBase (piOpen (piCount equation.1.1.code) equation.1.1.code) = true)
    (bound : h.val < piCount equation.1.1.code) (nonempty : as ≠ []) (same : as.length = bs.length) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem :=
  tower_baseReads_of_anySpines constant member normal types
    (anySpines_of_opened le_rfl (lamDepth_expandTo _ _) (lamDepth_expandTo _ _)
      (by rw [leftSpine, rightSpine]; exact .base base bound nonempty same))

/-! ## A conditional decision for the base family, from the census rows outside the shapes -/

/-- **The census rows read by the base family, by shape alone**: the Σ family's rows, and spines of one bound local at
every base type. -/
def BaseCoveredHead {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Prop :=
  ShapeCoveredHead equation ∨
    AnySpines 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)

/-- **A census head in a row by shape is read** by the base family from some budget on. -/
theorem tower_baseReads_of_covered {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (covered : BaseCoveredHead equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem := by
  rcases covered with shape | spines
  · obtain ⟨bound, reads⟩ := tower_sigmaReads_of_shape constant member normal types shape
    exact ⟨bound, fun larger enough => .inl (reads larger enough)⟩
  · exact tower_baseReads_of_anySpines constant member normal types spines

/-- **Conditional decision for the tower's base family, from the census rows outside the shapes**: if every census
head of a constant preparation whose η-long opened sides are of a census kind and outside the rows by shape is read
from some budget on, the family decides every store of the dynamic pattern fragment, with a principal answer or a
certified refutation, constant at every larger budget. At the tower the hypothesis fails: the conclusion would decide
`crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_base_decided_of_unread
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
          ¬ BaseCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (baseTower.solver larger) problem larger = run (baseTower.solver budget) problem budget ∧
      ((∃ state finished, run (baseTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (baseTower.solver larger) problem larger = .refuted absent)) :=
  tower_base_decided_of_baseReads (fun {_} {problem} permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : BaseCoveredHead equation
      · exact tower_baseReads_of_covered constant member normal head.1 covered
      · have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
          (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
          TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing threshold problem
          permuted
        have sides := PermutedMiller.sides_of_mem prepared member
        exact unread permuted nonempty threshold constant equation member normal head sides
          (eta_kind sides normal.2.1 normal.2.2.2) covered)
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
