import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsBase
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseGap

/-!
# The census rows at a Σ base

At a Σ base the Σ family η-expands a spine of a bound local into the pair of its projections (`sigmaTo`), and the
formers reading then reads a pair against a pair. R121 proved the step and its controls; the census lemma was open.

* **The Σ step keeps normal codes** (`normal_sigmaTo`): the projections of a normal spine of a local are normal.
* **The row** (`tower_sigmaReads_of_pairs`): a census head of a constant preparation whose η-long sides, η-expanded
  at the Σ base, are read by the formers reading (`underParts`), is read by the Σ family from some budget on. The row
  holds a pair against a pair, a pair against a spine of a bound local, and two spines of bound locals, at a Σ base
  under the annotation's Π binders. The proof follows the equation through the two stores: the η-long prepared store
  of the problem, then the preparation, twin collapse and η-expansion of the Σ-expanded store, all of which leave its
  normal codes in place.
* **A conditional decision for the base family, from the census rows outside all the rows read**
  (`CensusCoveredHead`, `tower_base_decided_of_uncovered`). At the tower its hypothesis fails: the conclusion would
  decide `crossStore`, solvable and without principal answer
  (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
  `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).

Controls: the row holds on R121's Σ store (`sigma_row`) and fails at a base type that is an application
(`applied_row_none`).
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
open ContextualDependentExecutableJoin (Normal)
open ContextualDependentIntersectionGeneral (EqualStrengthening)

/-! ## The Σ step keeps normal codes -/

/-- **η-expansion at a Σ base keeps normal codes.** -/
theorem normal_sigmaTo {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty) {n : Nat}
    (depth : Nat) (T t : Tm Head n) (normal : Normal R t) : Normal R (sigmaTo depth T t) := by
  by_cases under : ∃ A B body, T = .pi A B ∧ t = .lam body
  · obtain ⟨A, B, body, rfl, rfl⟩ := under
    exact (normal_lam_iff empty).mpr (normal_sigmaTo empty (depth + 1) B body ((normal_lam_iff empty).mp normal))
  · by_cases sig : ∃ A B, T = .sigma A B
    · obtain ⟨A, B, rfl⟩ := sig
      rw [sigmaTo_sigma]
      split
      · rename_i bound
        obtain ⟨j, head, _⟩ := boundSpine_spec bound
        have notPair := isPair_of_spineHead head
        exact (normal_pair_iff empty).mpr
          ⟨(normal_fst_iff empty).mpr ⟨notPair, normal⟩, (normal_snd_iff empty).mpr ⟨notPair, normal⟩⟩
      · exact normal
    · rw [sigmaTo_base under sig]
      exact normal
termination_by sizeOf T

/-! ## The Σ-expanded store -/

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (strengthening : EqualStrengthening S.R)

omit [DecidableRel S.R.cumulative] in
/-- **An equation of the prepared store with homogeneous twins has its η-long, Σ-expanded form in the Σ-expanded
store**, with these codes. -/
theorem sigmaUpdate_mem_codes (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {twin : Equation (TotalTerm
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).target)}
    (member : twin ∈ (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining) :
    ∃ moved ∈ (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining,
      moved.1.1.code = twin.1.1.code ∧
      moved.1.2.code = sigmaTo 0 twin.1.1.code (expandTo (piCount twin.1.1.code) twin.1.2.code) ∧
      moved.2.1.code = twin.2.1.code ∧
      moved.2.2.code = sigmaTo 0 twin.2.1.code (expandTo (piCount twin.2.1.code) twin.2.2.code) :=
  ⟨_, List.mem_map_of_mem (longUpdate_mem facts member), rfl, rfl, rfl, rfl⟩

/-- **The Σ reader at a fixed Σ-expanded store**: a reader of the piece family on the Σ-expanded store reads the
store for the Σ family. -/
theorem sigmaReads_of_const (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {fixed : Update S.levels problem}
    (same : sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem = fixed)
    (reads : PieceReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel fixed.remaining) :
    SigmaReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem := by
  subst same
  exact .inr reads

end General

/-! ## The row -/

/-- The tower's η-long prepared store, η-expanded at Σ bases. -/
noncomputable abbrev towerSigmaUpdate (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Update setting.levels problem :=
  sigmaUpdate (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel problem

/-- **A homogeneous equation of a prepared store whose η-long sides are read by the formers reading is read** by the
piece family from some budget on, when the prepared store with homogeneous twins no longer changes. -/
theorem tower_pieceReads_of_preparedFormers {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ))
    {fuel : Nat}
    (constant : ∀ larger, fuel ≤ larger → towerPreparedTwins larger store = towerPreparedTwins fuel store)
    {prepared : Equation (TotalTerm (towerPrepare fuel store).target)}
    (member : prepared ∈ (towerPrepare fuel store).remaining) (same : prepared.2.1.code = prepared.1.1.code)
    (split : (underParts (S := setting) prepared.1.1.code (expandTo (piCount prepared.1.1.code) prepared.1.2.code)
      (expandTo (piCount prepared.1.1.code) prepared.2.2.code)).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger store := by
  have inTwins := collapseOne_mem (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer fuel member
  rw [collapseOne_homogeneous_self (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.reducer fuel prepared same] at inTwins
  obtain ⟨twin, twinMember, same, twinSplit⟩ : ∃ twin ∈ (towerPreparedTwins fuel store).remaining,
      twin.2.1.code = twin.1.1.code ∧
        (underParts (S := setting) twin.1.1.code (expandTo (piCount twin.1.1.code) twin.1.2.code)
          (expandTo (piCount twin.1.1.code) twin.2.2.code)).isSome := ⟨prepared, inTwins, same, split⟩
  obtain ⟨pieces, found⟩ := Option.isSome_iff_exists.mp twinSplit
  have expandedMember := longUpdate_mem (S := setting) TowerModel.facts twinMember
  have sameExpanded : (expandSide TowerModel.facts twin.2).1.code = (expandSide TowerModel.facts twin.1).1.code := same
  have rightCode : (expandSide TowerModel.facts twin.2).2.code = expandTo (piCount twin.1.1.code) twin.2.2.code := by
    change expandTo (piCount twin.2.1.code) twin.2.2.code = _
    rw [same]
  have foundExpanded : underParts (S := setting) (expandSide TowerModel.facts twin.1).1.code
      (expandSide TowerModel.facts twin.1).2.code (expandSide TowerModel.facts twin.2).2.code = some pieces := by
    rw [rightCode]
    exact found
  have typed := underParts_typed TowerModel.facts TowerModel.algebra _ _ _
    (towerPreparedTwins fuel store).target.formed foundExpanded
    (expandSide TowerModel.facts twin.1).2.typed
    (by have tr := (expandSide TowerModel.facts twin.2).2.typed; rw [sameExpanded] at tr; exact tr)
  obtain ⟨formedBound, formed⟩ := tower_formNormal_eventually pieces typed
  exact tower_pieceReads_of_fixed constant expandedMember (bound := formedBound) fun larger enough =>
    normalWeighed_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices larger
      (Or.inl (underNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
        ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
        ExecutableTowerChoices.choices larger sameExpanded foundExpanded fun typed' =>
          formNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
            ContextualDependentPiSpine.Controls.rigid TowerModel.complete
            ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
            ExecutableTowerChoices.choices larger pieces typed' (formed larger enough)))

/-- **The census rows at a Σ base are read**: a census head of a constant preparation whose η-long sides, η-expanded
at the Σ base, are read by the formers reading, is read by the Σ family from some budget on. -/
theorem tower_sigmaReads_of_pairs {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (split : (underParts (S := setting) equation.1.1.code
      (expandTo (piCount equation.1.1.code)
        (sigmaTo 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)))
      (expandTo (piCount equation.1.1.code)
        (sigmaTo 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.2.2.code)))).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerSigmaReads larger problem := by
  have empty := ContextualDependentMillerClosure.computation_empty ContextualDependentPiSpine.Controls.rigid
  obtain ⟨bound₁, twins⟩ := tower_twins_keep constant member types
    (fun A l r => (Normal Tower.rules A ∧ Normal Tower.rules l ∧ Normal Tower.rules r) ∧
      (underParts (S := setting) A (expandTo (piCount A) (sigmaTo 0 A (expandTo (piCount A) l)))
        (expandTo (piCount A) (sigmaTo 0 A (expandTo (piCount A) r)))).isSome)
    ⟨⟨normal.1, normal.2.1, normal.2.2.2⟩, split⟩
  obtain ⟨settled, sigmaConst⟩ := (sigmaUpdate_const (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))
    ContextualDependentDecisiveFragment.Controls.stable problem).spec
  obtain ⟨twin, twinMember, same, ⟨normalA, normalL, normalR⟩, twinSplit⟩ :=
    twins (max bound₁ settled) (le_max_left _ _)
  -- the Σ-expanded η-long twin is an equation of the Σ-expanded store, with normal codes
  obtain ⟨moved, movedMember, codeA, codeL, codeA', codeR⟩ := sigmaUpdate_mem_codes (S := setting) TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) (max bound₁ settled) twinMember
  have movedNormal : NormalCodes moved := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [codeA]
      exact normalA
    · rw [codeL]
      exact normal_sigmaTo empty 0 _ _ (normal_expandTo empty _ normalL)
    · rw [codeA', same]
      exact normalA
    · rw [codeR]
      exact normal_sigmaTo empty 0 _ _ (normal_expandTo empty _ normalR)
  have movedShape : moved.2.1.code = moved.1.1.code ∧
      (underParts (S := setting) moved.1.1.code (expandTo (piCount moved.1.1.code) moved.1.2.code)
        (expandTo (piCount moved.1.1.code) moved.2.2.code)).isSome := by
    refine ⟨by rw [codeA', codeA]; exact same, ?_⟩
    rw [codeA, codeL, codeR, same]
    exact twinSplit
  -- it is kept by the preparation of that store, and read there
  obtain ⟨settled₂, twinsConst₂⟩ := tower_preparedTwins_const (towerSigmaUpdate (max bound₁ settled) problem).remaining
  obtain ⟨prepared, preparedMember, preparedSame, preparedSplit⟩ := tower_prepare_keeps_codes settled₂ movedMember
    movedNormal (fun A l A' r => A' = A ∧
      (underParts (S := setting) A (expandTo (piCount A) l) (expandTo (piCount A) r)).isSome) movedShape
  obtain ⟨boundP, reads⟩ := tower_pieceReads_of_preparedFormers _ twinsConst₂ preparedMember preparedSame
    preparedSplit
  refine ⟨max (max bound₁ settled) boundP, fun larger enough => ?_⟩
  exact sigmaReads_of_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening larger
    ((sigmaConst larger ((le_max_right _ _).trans ((le_max_left _ _).trans enough))).trans
      (sigmaConst (max bound₁ settled) (le_max_right _ _)).symm)
    (reads larger ((le_max_right _ _).trans enough))

/-! ## A conditional decision for the base family, from the census rows outside all the rows read -/

/-- **The census rows read by the base family**: the rows by shape, and the rows at a Σ base. -/
def CensusCoveredHead {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Prop :=
  BaseCoveredHead equation ∨
    (underParts (S := setting) equation.1.1.code
      (expandTo (piCount equation.1.1.code)
        (sigmaTo 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)))
      (expandTo (piCount equation.1.1.code)
        (sigmaTo 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.2.2.code)))).isSome

/-- **A census head in a row read is read** by the base family from some budget on. -/
theorem tower_baseReads_of_censusCovered {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (covered : CensusCoveredHead equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem := by
  rcases covered with rows | pairs
  · exact tower_baseReads_of_covered constant member normal types rows
  · obtain ⟨bound, reads⟩ := tower_sigmaReads_of_pairs constant member normal types pairs
    exact ⟨bound, fun larger enough => .inl (reads larger enough)⟩

/-- **Conditional decision for the tower's base family, from the census rows outside all the rows read**: if every
census head of a constant preparation whose η-long opened sides are of a census kind and outside the rows read is read
from some budget on, the family decides every store of the dynamic pattern fragment, with a principal answer or a
certified refutation, constant at every larger budget. At the tower the hypothesis fails: the conclusion would decide
`crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_base_decided_of_uncovered
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
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
          ¬ CensusCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (baseTower.solver larger) problem larger = run (baseTower.solver budget) problem budget ∧
      ((∃ state finished, run (baseTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (baseTower.solver larger) problem larger = .refuted absent)) :=
  tower_base_decided_of_baseReads (fun {_} {problem} permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : CensusCoveredHead equation
      · exact tower_baseReads_of_censusCovered constant member normal head.1 covered
      · have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
          (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
          TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing threshold problem
          permuted
        have sides := PermutedMiller.sides_of_mem prepared member
        exact uncovered permuted nonempty threshold constant equation member normal head sides
          (eta_kind sides normal.2.1 normal.2.2.2) covered)
    inside

/-! ## Controls -/

/-- **The row holds on R121's store at a Σ base.** -/
theorem sigma_row : (underParts (S := setting) SigmaControls.sigmaEquation.1.1.code
    (expandTo (piCount SigmaControls.sigmaEquation.1.1.code) (sigmaTo 0 SigmaControls.sigmaEquation.1.1.code
      (expandTo (piCount SigmaControls.sigmaEquation.1.1.code) SigmaControls.sigmaEquation.1.2.code)))
    (expandTo (piCount SigmaControls.sigmaEquation.1.1.code) (sigmaTo 0 SigmaControls.sigmaEquation.1.1.code
      (expandTo (piCount SigmaControls.sigmaEquation.1.1.code) SigmaControls.sigmaEquation.2.2.code)))).isSome =
    true := by decide +kernel

/-- **The row fails at a base type that is an application.** -/
theorem applied_row_none : underParts (S := setting) BaseControls.appliedEquation.1.1.code
    (expandTo (piCount BaseControls.appliedEquation.1.1.code) (sigmaTo 0 BaseControls.appliedEquation.1.1.code
      (expandTo (piCount BaseControls.appliedEquation.1.1.code) BaseControls.appliedEquation.1.2.code)))
    (expandTo (piCount BaseControls.appliedEquation.1.1.code) (sigmaTo 0 BaseControls.appliedEquation.1.1.code
      (expandTo (piCount BaseControls.appliedEquation.1.1.code) BaseControls.appliedEquation.2.2.code))) =
    none := by decide +kernel

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
