import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthPieces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptanceFinal

/-!
# The census rows of decompositions, read by the piece family

**Completeness of the decomposition at normal annotations.** The pieces are formed as soon as the type former forms
each normalized annotation (`formPieces_isSome`, `formNormal_isSome`). On the tower the normalizer eventually returns a
normal reduct of every type, and the type former eventually forms every normal type, so the pieces of every typed list
are eventually formed (`tower_normalCode_formed`, `tower_formNormal_eventually`). Hence a decomposition at normal
annotations reads an equation as soon as its pieces are read, whatever their annotations (`spineNormal_isSome`,
`underNormal_isSome`), and the search reads a store with such an equation (`decomposeNormal_isSome`).

**Three census rows.** A census head of a constant preparation whose η-long sides are spines of one local with pieces
(`dependentUnder`), formers with pieces under the abstractions (`underParts`), or spines of one local eventually read
along the reducts of the instantiated types (`dependentUnderN`), is read by the piece family from some budget on
(`tower_pieceReads_of_spine`, `tower_pieceReads_of_under`, `tower_pieceReads_of_args`).

**A conditional decision for the piece family, from the census rows not yet read**
(`tower_piece_decided_of_uncovered`, `tower_piece_decided_of_uncovered_kinds`): the covered rows (`PieceCoveredHead`)
are the skeleton family's three rows and these three. At the tower the hypothesis fails: the conclusion would decide
`crossStore`, solvable and without principal answer
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

/-! ## Completeness of the decomposition at normal annotations -/

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (reducer : ExecutableReduction.Reducer S.R)
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)

/-- **Pieces are formed** when every annotation is. -/
theorem formPieces_isSome (fuel : Nat) {Θ : Context S.R} :
    ∀ (pieces : List (Piece Head Θ.arity)) (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw),
      (∀ piece ∈ pieces,
        (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
          piece.leftType).isSome ∧
        (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
          piece.rightType).isSome) →
      (formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces typed).isSome
  | [], _, _ => rfl
  | piece :: rest, typed, formed => by
      have here := formed piece List.mem_cons_self
      obtain ⟨leftType, leftComputed⟩ := Option.isSome_iff_exists.mp here.1
      obtain ⟨rightType, rightComputed⟩ := Option.isSome_iff_exists.mp here.2
      obtain ⟨store, restComputed⟩ := Option.isSome_iff_exists.mp (formPieces_isSome fuel rest
        (fun other member => typed other (List.mem_cons_of_mem _ member))
        (fun other member => formed other (List.mem_cons_of_mem _ member)))
      simp only [formPieces]
      rw [leftComputed, rightComputed, restComputed]
      rfl

/-- **Pieces at normal annotations are formed** when every normalized annotation is. -/
theorem formNormal_isSome (fuel : Nat) {Θ : Context S.R} (pieces : List (Piece Head Θ.arity))
    (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw)
    (formed : ∀ piece ∈ pieces,
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
        (normalCode reducer fuel piece.leftType)).isSome ∧
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
        (normalCode reducer fuel piece.rightType)).isSome) :
    (formNormal facts roots heads algebra rigid complete reducer declared choices fuel pieces typed).isSome := by
  unfold formNormal formRelated
  rw [Option.isSome_map]
  exact formPieces_isSome facts roots heads algebra rigid complete reducer declared choices fuel _ _
    (fun q member => by
      obtain ⟨piece, inside, rfl⟩ := List.mem_map.mp member
      exact formed piece inside)

/-- **The decomposition between spines of one local at normal annotations reads an equation** whose pieces are
formed. -/
theorem spineNormal_isSome (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (same : equation.2.1.code = equation.1.1.code) {pieces : List (Piece Head Θ.arity)}
    (found : dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (formed : ∀ typed, (formNormal facts roots heads algebra rigid complete reducer declared choices fuel pieces
      typed).isSome) :
    (spineNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome := by
  unfold spineNormal
  rw [dif_pos same]
  split
  · rename_i read computed
    rw [found] at computed
    cases computed
    rw [Option.isSome_map]
    exact formed _
  · rename_i computed
    rw [found] at computed
    cases computed

/-- **The decomposition under abstractions at normal annotations reads an equation** whose pieces are formed. -/
theorem underNormal_isSome (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (same : equation.2.1.code = equation.1.1.code) {pieces : List (Piece Head Θ.arity)}
    (found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (formed : ∀ typed, (formNormal facts roots heads algebra rigid complete reducer declared choices fuel pieces
      typed).isSome) :
    (underNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome := by
  unfold underNormal
  rw [dif_pos same]
  split
  · rename_i read computed
    rw [found] at computed
    cases computed
    rw [Option.isSome_map]
    exact formed _
  · rename_i computed
    rw [found] at computed
    cases computed

/-- **The decomposition along the reducts of the instantiated types reads an equation** whose pieces are read and
formed. -/
theorem argsNormal_isSome (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (same : equation.2.1.code = equation.1.1.code)
    {read : {pieces : List (Piece Head Θ.arity) //
      DepRel S.R [] equation.1.1.code equation.1.2.code equation.2.2.code pieces}}
    (found : readArgs reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code = some read)
    (formed : ∀ typed, (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
      typed).isSome) :
    (argsNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome := by
  unfold argsNormal
  rw [dif_pos same, found]
  simp only [Option.bind_some]
  rw [Option.isSome_map]
  exact formed _

theorem normalWeighed_isSome (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (read : (underNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome ∨
      (spineNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome ∨
      (argsNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome) :
    (normalWeighed facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome := by
  unfold normalWeighed
  cases computed : underNormal facts roots heads algebra rigid complete reducer declared choices fuel equation with
  | some weighed => rfl
  | none =>
      cases spineComputed : spineNormal facts roots heads algebra rigid complete reducer declared choices fuel
          equation with
      | some weighed => rfl
      | none =>
          rcases read with under | spine | args
          · rw [computed] at under
            cases under
          · rw [spineComputed] at spine
            cases spine
          · exact args

/-- **The search reads a store with an equation that decomposes at normal annotations.** -/
theorem decomposeNormal_isSome (fuel : Nat) {Θ : Context S.R} :
    ∀ {problem : EquationStore (TotalTerm Θ)} {equation : Equation (TotalTerm Θ)}, equation ∈ problem →
      (normalWeighed facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome →
      (decomposeNormal facts roots heads algebra rigid complete reducer declared choices fuel problem).isSome
  | [], _, member, _ => absurd member List.not_mem_nil
  | first :: rest, equation, member, read => by
      simp only [decomposeNormal]
      unfold decomposeStep
      cases computed : normalWeighed facts roots heads algebra rigid complete reducer declared choices fuel first with
      | some weighed => rfl
      | none =>
          rcases List.mem_cons.mp member with rfl | later
          · rw [computed] at read
            cases read
          · dsimp only
            rw [Option.isSome_map]
            exact decomposeNormal_isSome fuel later read

end General

/-! ## The tower -/

section Tower

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4

/-- **On the tower every normalized type is eventually formed.** -/
theorem tower_normalCode_formed {Θ : Context setting.R} {code : Tower.Tm Θ.arity}
    (isType : IsType setting.R Θ.raw code) :
    ∃ bound, ∀ larger, bound ≤ larger →
      (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
        ContextualDependentInversion.Controls.reducer larger Θ
        (normalCode ContextualDependentInversion.Controls.reducer larger code)).isSome := by
  obtain ⟨f₁, result, normal, _, stable₁⟩ :=
    ContextualDependentExecutableConversion.red_eventually_type (L := Nat) Θ.formed isType
  have reduced : ∀ larger, f₁ ≤ larger →
      normalCode ContextualDependentInversion.Controls.reducer larger code = result.val := by
    intro larger enough
    unfold normalCode
    rw [show ContextualDependentInversion.Controls.reducer larger code = some result from stable₁ larger enough]
    rfl
  have equal := normalCode_typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    ContextualDependentInversion.Controls.reducer f₁ Θ.formed isType
  rw [reduced f₁ le_rfl] at equal
  have isNormal := ContextualDependentExecutableChecking.isType_right (L := Nat) Θ.formed equal
  obtain ⟨f₂, formed, stable₂⟩ := ContextualDependentExecutableDiscovery.formType_stable (fun _ => (0 : Nat))
    (Γ := Θ) normal isNormal
  refine ⟨max f₁ f₂, fun larger enough => ?_⟩
  rw [reduced larger ((le_max_left _ _).trans enough)]
  exact Option.isSome_iff_exists.mpr ⟨formed, stable₂ larger ((le_max_right _ _).trans enough)⟩

/-- **On the tower the pieces of every typed list are eventually formed at normal annotations.** -/
theorem tower_formNormal_eventually {Θ : Context setting.R} :
    ∀ (pieces : List (Piece (LevelTower.Head Nat) Θ.arity)), (∀ piece ∈ pieces, piece.Typed setting.R Θ.raw) →
      ∃ bound, ∀ larger, bound ≤ larger → ∀ piece ∈ pieces,
        (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
          TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
          ContextualDependentInversion.Controls.reducer larger Θ
          (normalCode ContextualDependentInversion.Controls.reducer larger piece.leftType)).isSome ∧
        (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
          TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
          ContextualDependentInversion.Controls.reducer larger Θ
          (normalCode ContextualDependentInversion.Controls.reducer larger piece.rightType)).isSome
  | [], _ => ⟨0, fun _ _ _ member => absurd member List.not_mem_nil⟩
  | piece :: rest, typed => by
      obtain ⟨b₁, left⟩ := tower_normalCode_formed (Typed.isType (typed piece List.mem_cons_self).1 Θ.formed)
      obtain ⟨b₂, right⟩ := tower_normalCode_formed (Typed.isType (typed piece List.mem_cons_self).2 Θ.formed)
      obtain ⟨b₃, others⟩ := tower_formNormal_eventually rest fun other member =>
        typed other (List.mem_cons_of_mem _ member)
      refine ⟨max b₁ (max b₂ b₃), fun larger enough other member => ?_⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨left larger ((le_max_left _ _).trans enough),
          right larger (((le_max_left _ _).trans (le_max_right _ _)).trans enough)⟩
      · exact others larger (((le_max_right _ _).trans (le_max_right _ _)).trans enough) other later

/-- The tower's decomposition at normal annotations. -/
abbrev towerDecomposeNormal (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  decomposeNormal (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices fuel problem

theorem tower_preparedTwins_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    ∃ threshold, ∀ larger, threshold ≤ larger →
      towerPreparedTwins larger problem = towerPreparedTwins threshold problem :=
  (preparedTwins_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))
    ContextualDependentDecisiveFragment.Controls.stable problem).spec

/-- **A store is read by the piece family** from some budget on, when an equation of its η-long prepared store with
homogeneous twins, at one budget past the twins' constancy, is eventually read by the decomposition at normal
annotations. -/
theorem tower_pieceReads_of_fixed {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPreparedTwins larger problem = towerPreparedTwins threshold problem)
    {equation : Equation (TotalTerm (towerPreparedTwins threshold problem).target)}
    (member : equation ∈ expandStore TowerModel.facts (towerPreparedTwins threshold problem).remaining)
    {bound : Nat}
    (read : ∀ larger, bound ≤ larger → (normalWeighed (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices larger equation).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem := by
  refine ⟨max threshold bound, fun larger enough => Or.inr ?_⟩
  change (towerDecomposeNormal larger (expandStore TowerModel.facts (towerPreparedTwins larger problem).remaining)).isSome
  rw [constant larger ((le_max_left _ _).trans enough)]
  exact decomposeNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices larger member
    (read larger ((le_max_right _ _).trans enough))

/-- **A census head whose η-long sides are spines of one local with pieces is read** by the piece family from some
budget on. -/
theorem tower_pieceReads_of_spine {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (split : (dependentUnder [] equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem := by
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types
    (fun A l r => (dependentUnder [] A (expandTo (piCount A) l) (expandTo (piCount A) r)).isSome) split
  obtain ⟨settled, twinsConst⟩ := tower_preparedTwins_const problem
  have fixed := twinsConst (max bound settled) (le_max_right _ _)
  have kept : ∀ larger, max bound settled ≤ larger →
      towerPreparedTwins larger problem = towerPreparedTwins (max bound settled) problem := fun larger enough =>
    (twinsConst larger ((le_max_right _ _).trans enough)).trans fixed.symm
  obtain ⟨twin, twinMember, same, twinSplit⟩ := twins (max bound settled) (le_max_left _ _)
  obtain ⟨pieces, found⟩ := Option.isSome_iff_exists.mp twinSplit
  have expandedMember := longUpdate_mem (S := setting) TowerModel.facts twinMember
  have sameExpanded : (expandSide TowerModel.facts twin.2).1.code = (expandSide TowerModel.facts twin.1).1.code := same
  have rightCode : (expandSide TowerModel.facts twin.2).2.code = expandTo (piCount twin.1.1.code) twin.2.2.code := by
    change expandTo (piCount twin.2.1.code) twin.2.2.code = _
    rw [same]
  have foundExpanded : dependentUnder [] (expandSide TowerModel.facts twin.1).1.code
      (expandSide TowerModel.facts twin.1).2.code (expandSide TowerModel.facts twin.2).2.code = some pieces := by
    rw [rightCode]
    exact found
  have typed := dependentUnder_typed TowerModel.facts [] _ _ _ (towerPreparedTwins (max bound settled) problem).target.formed
    (LocalTypes.nil _) foundExpanded (expandSide TowerModel.facts twin.1).2.typed
    (by have tr := (expandSide TowerModel.facts twin.2).2.typed; rw [sameExpanded] at tr; exact tr)
  obtain ⟨formedBound, formed⟩ := tower_formNormal_eventually pieces typed
  exact tower_pieceReads_of_fixed kept expandedMember (bound := formedBound) fun larger enough =>
    normalWeighed_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices larger
      (Or.inr (Or.inl (spineNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
        ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
        ExecutableTowerChoices.choices larger sameExpanded foundExpanded fun typed' =>
          formNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
            ContextualDependentPiSpine.Controls.rigid TowerModel.complete
            ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
            ExecutableTowerChoices.choices larger pieces typed' (formed larger enough))))

/-- **A census head whose η-long sides are eventually read as spines of one local along the reducts of the
instantiated types is read** by the piece family from some budget on. -/
theorem tower_pieceReads_of_args {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (split : ∃ bound, ∀ larger, bound ≤ larger → (dependentUnderN (S := setting)
      ContextualDependentInversion.Controls.reducer larger [] equation.1.1.code
      (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem := by
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types
    (fun A l r => ∃ bound, ∀ larger, bound ≤ larger → (dependentUnderN (S := setting)
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
  obtain ⟨settledRead, readConst⟩ := (readArgs_const (S := setting) ContextualDependentInversion.Controls.reducer
    ContextualDependentDecisiveFragment.Controls.stable (expandSide TowerModel.facts twin.1).1.code
    (expandSide TowerModel.facts twin.1).2.code (expandSide TowerModel.facts twin.2).2.code).spec
  have readAt : (readArgs (S := setting) ContextualDependentInversion.Controls.reducer (max settledRead readBound)
      (expandSide TowerModel.facts twin.1).1.code (expandSide TowerModel.facts twin.1).2.code
      (expandSide TowerModel.facts twin.2).2.code).isSome := by
    rw [← Option.isSome_map (f := Subtype.val), readArgs_val, rightCode]
    exact twinRead _ (le_max_right _ _)
  obtain ⟨read, readComputed⟩ := Option.isSome_iff_exists.mp readAt
  have readKept : ∀ larger, max settledRead readBound ≤ larger →
      readArgs (S := setting) ContextualDependentInversion.Controls.reducer larger
        (expandSide TowerModel.facts twin.1).1.code (expandSide TowerModel.facts twin.1).2.code
        (expandSide TowerModel.facts twin.2).2.code = some read := fun larger enough =>
    ((readConst larger ((le_max_left _ _).trans enough)).trans
      (readConst _ (le_max_left _ _)).symm).trans readComputed
  have typed := read.property.typed TowerModel.facts TowerModel.roots TowerModel.heads
    (towerPreparedTwins (max bound settled) problem).target.formed (LocalTypes.nil _)
    (expandSide TowerModel.facts twin.1).2.typed
    (by have tr := (expandSide TowerModel.facts twin.2).2.typed; rw [sameExpanded] at tr; exact tr)
  obtain ⟨formedBound, formed⟩ := tower_formNormal_eventually read.val typed
  exact tower_pieceReads_of_fixed kept expandedMember (bound := max (max settledRead readBound) formedBound)
    fun larger enough =>
    normalWeighed_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices larger
      (Or.inr (Or.inr (argsNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
        ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
        ExecutableTowerChoices.choices larger sameExpanded (readKept larger ((le_max_left _ _).trans enough))
        fun typed' =>
          formNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
            ContextualDependentPiSpine.Controls.rigid TowerModel.complete
            ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
            ExecutableTowerChoices.choices larger read.val typed'
            (formed larger ((le_max_right _ _).trans enough)))))

/-- **A census head whose η-long sides are formers with pieces under the abstractions is read** by the piece family
from some budget on. -/
theorem tower_pieceReads_of_under {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (split : (underParts (S := setting) equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem := by
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types
    (fun A l r => (underParts (S := setting) A (expandTo (piCount A) l) (expandTo (piCount A) r)).isSome) split
  obtain ⟨settled, twinsConst⟩ := tower_preparedTwins_const problem
  have fixed := twinsConst (max bound settled) (le_max_right _ _)
  have kept : ∀ larger, max bound settled ≤ larger →
      towerPreparedTwins larger problem = towerPreparedTwins (max bound settled) problem := fun larger enough =>
    (twinsConst larger ((le_max_right _ _).trans enough)).trans fixed.symm
  obtain ⟨twin, twinMember, same, twinSplit⟩ := twins (max bound settled) (le_max_left _ _)
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
    (towerPreparedTwins (max bound settled) problem).target.formed foundExpanded
    (expandSide TowerModel.facts twin.1).2.typed
    (by have tr := (expandSide TowerModel.facts twin.2).2.typed; rw [sameExpanded] at tr; exact tr)
  obtain ⟨formedBound, formed⟩ := tower_formNormal_eventually pieces typed
  exact tower_pieceReads_of_fixed kept expandedMember (bound := formedBound) fun larger enough =>
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

/-! ## A conditional decision for the piece family, from the census rows not yet read -/

/-- **The census rows read by the piece family**, on one equation. -/
def PieceCoveredHead {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Prop :=
  CoveredHead equation ∨
    (dependentUnder [] equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome ∨
    (underParts (S := setting) equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome ∨
    ∃ bound, ∀ larger, bound ≤ larger → (dependentUnderN (S := setting)
      ContextualDependentInversion.Controls.reducer larger [] equation.1.1.code
      (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome

/-- **A covered census head is read** by the piece family from some budget on. -/
theorem tower_pieceReads_of_covered {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (covered : PieceCoveredHead equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem := by
  rcases covered with skeleton | spine | under | args
  · obtain ⟨bound, reads⟩ := tower_skeletonReads_of_covered constant member normal types skeleton
    exact ⟨bound, fun larger enough => .inl (reads larger enough)⟩
  · exact tower_pieceReads_of_spine constant member types spine
  · exact tower_pieceReads_of_under constant member types under
  · exact tower_pieceReads_of_args constant member types args

/-- **Conditional decision for the tower's piece family, from the census rows not yet read**: if every census head of
a constant preparation outside the covered rows is read from some budget on, the family decides every store of the
dynamic pattern fragment, with a principal answer or a certified refutation, constant at every larger budget. At the
tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_piece_decided_of_uncovered
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ¬ PieceCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (pieceTower.solver larger) problem larger = run (pieceTower.solver budget) problem budget ∧
      ((∃ state finished, run (pieceTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (pieceTower.solver larger) problem larger = .refuted absent)) :=
  tower_piece_decided_of_pieceReads (fun permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : PieceCoveredHead equation
      · exact tower_pieceReads_of_covered constant member normal head.1 covered
      · exact uncovered permuted nonempty threshold constant equation member normal head covered)
    inside

/-- **The same conditional decision, with the census kind of the η-long opened sides available.** Its hypothesis
fails at the tower for the same reason (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). -/
theorem tower_piece_decided_of_uncovered_kinds
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
          ¬ PieceCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (pieceTower.solver larger) problem larger = run (pieceTower.solver budget) problem budget ∧
      ((∃ state finished, run (pieceTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (pieceTower.solver larger) problem larger = .refuted absent)) :=
  tower_piece_decided_of_uncovered (fun {_} {problem} permuted nonempty threshold constant equation member normal
      head covered => by
      have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
        TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing threshold problem permuted
      have sides := PermutedMiller.sides_of_mem prepared member
      exact uncovered permuted nonempty threshold constant equation member normal head sides
        (eta_kind sides normal.2.1 normal.2.2.2) covered)
    inside

end Tower

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
