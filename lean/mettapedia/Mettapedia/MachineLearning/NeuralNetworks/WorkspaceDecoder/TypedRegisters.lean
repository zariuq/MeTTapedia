import Mathlib.Data.List.Sort
import Mettapedia.GSLT.LanguageDef.Pure.BetaAtomicRoot
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics

/-!
# Typed registers and sealed-interface inheritance

Open registers are indexed by the actual hole identities exposed by an atomic
root.  No truncation or modulo allocation is used.  Workspace decoders only
score the sealed legal-action enumeration; sorting those scores changes order,
not support.  Consequently the existing soundness, completeness, and ordering
theorems apply for every parameter value, gate value, and recurrence depth.

The register and trust results are architectural.  They make no linear or
nonlinear neural-network training claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRoot

universe uState uHole uHead uProgram uContent uParams uGates

/-! ## Hole-indexed register allocation -/

/-- The register addresses currently allocated by an atomic construction
state.  The subtype retains the root's exact hole identity and its proof of
being open; it does not compress `Nat` identities into a finite residue. -/
def OpenHole (root : AtomicRoot) (state : root.State) :=
  { hole : root.Hole // hole ∈ root.holes state }

/-- A typed register file stores content at exactly the currently open hole
identities.  Slot metadata can be carried by `Content`; allocation itself is
independent of any linear or nonlinear scoring model. -/
abbrev TypedRegisterFile (root : AtomicRoot) (state : root.State)
    (Content : Type uContent) :=
  OpenHole root state → Content

/-- Allocation preserves the fixed hole address exactly.  For the Pure beta
root this codomain is `Nat`, matching the sealed interned-name discipline. -/
def OpenHole.address {root : AtomicRoot} {state : root.State} :
    OpenHole root state → root.Hole :=
  Subtype.val

/-- Hole-indexed allocation is injective: distinct open registers cannot share
an address.  This architectural fact is independent of workspace dynamics. -/
theorem openHole_address_injective (root : AtomicRoot) (state : root.State) :
    Function.Injective (@OpenHole.address root state) :=
  Subtype.val_injective

/-- Hole-indexed allocation is total over the sealed open-hole list: every
exposed hole has a register carrying that exact address. -/
theorem openHole_address_total (root : AtomicRoot) (state : root.State)
    (hole : root.Hole) (hopen : hole ∈ root.holes state) :
    ∃ register : OpenHole root state, register.address = hole :=
  ⟨⟨hole, hopen⟩, rfl⟩

/-- The sealed Pure beta root's actual open-register capacity is one.  This is
proved from `PureBetaAtomicRoot.holes`, whose constructors expose either one
`Nat` hole identity or none; it is not inferred from the numeric identity. -/
def pureBetaRegisterCapacity : Nat := 1

/-- Every Pure beta atomic state, and therefore every reachable one, respects
the sealed one-open-hole capacity.  The capacity is not budget-parametric in
the current root interface. -/
theorem betaAtomicRoot_openHole_bound (goal : Mettapedia.GSLT.LanguageDef.Pure.Expr)
    (state : (betaAtomicRoot goal).State) :
    ((betaAtomicRoot goal).holes state).length ≤ pureBetaRegisterCapacity := by
  rcases state with ⟨core, tokensEmitted, maxLen⟩
  cases core <;> simp [betaAtomicRoot, holes, pureBetaRegisterCapacity]

/-- Allocation soundness against the sealed bound: at every Pure beta state,
addresses are injective and total and the number of exposed registers is at
most the derived capacity one.  This is stronger than a reachable-state-only
statement. -/
theorem betaAtomicRoot_allocationSound
    (goal : Mettapedia.GSLT.LanguageDef.Pure.Expr)
    (state : (betaAtomicRoot goal).State) :
    Function.Injective (@OpenHole.address (betaAtomicRoot goal) state) ∧
      (∀ hole, hole ∈ (betaAtomicRoot goal).holes state →
        ∃ register : OpenHole (betaAtomicRoot goal) state,
          register.address = hole) ∧
      ((betaAtomicRoot goal).holes state).length ≤ pureBetaRegisterCapacity := by
  exact ⟨openHole_address_injective _ _,
    fun hole hopen => openHole_address_total _ _ hole hopen,
    betaAtomicRoot_openHole_bound goal state⟩

/-- Negative allocation boundary: reducing unbounded `Nat` hole identities
modulo a one-slot capacity is not injective, so it cannot implement fixed hole
addresses even though only one hole is simultaneously open. -/
theorem moduloOne_not_injective_negativeExample :
    ¬ Function.Injective (fun hole : Nat => hole % pureBetaRegisterCapacity) := by
  intro hinjective
  have heq : (0 : Nat) = 1 := hinjective (by simp [pureBetaRegisterCapacity])
  omega

/-! ## A workspace decoder is only a legal-action scorer -/

/-- Workspace decoder data over a sealed atomic root.  Parameters, gates, and
recurrence depth are all consumed by `score`; no assumption is made that this
score was produced by a linear or nonlinear trained network. -/
structure LegalActionWorkspaceDecoder (root : AtomicRoot) where
  Params : Type uParams
  Gates : Type uGates
  parameters : Params
  gates : Gates
  recurrenceDepth : Nat
  score : Params → Gates → Nat → root.State →
    RefineAction root.Hole root.Head → ℝ

namespace LegalActionWorkspaceDecoder

variable {root : AtomicRoot} (decoder : LegalActionWorkspaceDecoder root)

/-- The decoder ranking sorts exactly the sealed legal-action enumeration by
its score.  Sorting can change order but cannot add or delete an action. -/
noncomputable def ranking (state : root.State) :
    List (RefineAction root.Hole root.Head) :=
  (root.legalActions state).insertionSort fun first second =>
    decoder.score decoder.parameters decoder.gates decoder.recurrenceDepth state first ≤
      decoder.score decoder.parameters decoder.gates decoder.recurrenceDepth state second

/-- For every parameter value, gate value, and recurrence depth, a workspace
ranking is a permutation of the sealed legal-action support. -/
theorem legalActions_perm_ranking (state : root.State) :
    (root.legalActions state).Perm (decoder.ranking state) := by
  exact (List.perm_insertionSort
    (fun first second =>
      decoder.score decoder.parameters decoder.gates decoder.recurrenceDepth state first ≤
        decoder.score decoder.parameters decoder.gates decoder.recurrenceDepth state second)
    (root.legalActions state)).symm

/-- Every workspace ranking lists exactly the legal actions.  This coverage is
architectural and does not depend on score calibration or training. -/
theorem ranking_listsAllLegalActions :
    root.asRefinementInterface.ListsAllLegalActions decoder.ranking := by
  unfold RefinementInterface.ListsAllLegalActions
  change ∀ (state : root.State) (action : RefineAction root.Hole root.Head),
    action ∈ decoder.ranking state ↔
      action.hole ∈ root.holes state ∧
        action.head ∈ root.legalHeads state action.hole
  intro state action
  rw [← (decoder.legalActions_perm_ranking state).mem_iff]
  exact root.mem_legalActions_iff state action

/-- Accepted-language inheritance: for any workspace parameters, gates, and
depth, ranked acceptance is exactly sealed checker acceptance.  The decoder can
reorder search but cannot change the accepted language. -/
theorem rankedAccepts_iff_accepts (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    root.asRefinementInterface.RankedAccepts decoder.ranking budget trace program ↔
      root.asRefinementInterface.Accepts budget trace program := by
  exact laws.interfaceLaws.rankedAccepts_iff_accepts
    decoder.ranking decoder.ranking_listsAllLegalActions

/-- Ordering invariance inherited from the sealed atomic theorem: replacing
the legal-action enumeration by any workspace-scored order cannot change
ranked acceptance, for arbitrary parameters, gates, and depth. -/
theorem orderingInvariant (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    root.asRefinementInterface.RankedAccepts root.legalActions budget trace program ↔
      root.asRefinementInterface.RankedAccepts decoder.ranking budget trace program := by
  apply laws.rankedAcceptance_invariant_of_legalActions
  · intro state action
    rfl
  · exact decoder.legalActions_perm_ranking

/-- Trust-boundary soundness inherited from the sealed interface: every program
accepted through an arbitrary workspace scorer is root-well-formed.  This is
not a claim about score accuracy. -/
theorem rankedAccepts_sound (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program}
    (haccepted :
      root.asRefinementInterface.RankedAccepts decoder.ranking budget trace program) :
    root.wellFormed program := by
  apply laws.interfaceLaws.accepts_sound
  exact (decoder.rankedAccepts_iff_accepts laws).mp haccepted

/-- Recall inheritance from sealed completeness: every well-formed in-budget
program's canonical trace remains accepted through any workspace parameters,
gates, and recurrence depth.  Recall is safe by construction. -/
theorem wellFormed_rankedAccepts (laws : AtomicRootLaws root)
    {budget : Nat} {program : root.Program}
    (hbudget : root.budgetOK budget) (hwellFormed : root.wellFormed program)
    (hcost : root.programCost program ≤ budget) :
    root.asRefinementInterface.RankedAccepts decoder.ranking budget
      (root.encode program) program := by
  apply (decoder.rankedAccepts_iff_accepts laws).mpr
  exact laws.interfaceLaws.wellFormed_reachable hbudget hwellFormed hcost

/-- Architecture-swap scope crown: any two workspace scorers, regardless of
parameters, gates, or recurrence depths, observe the same accepted language;
the inherited soundness and recall theorems remain available for each. -/
theorem architectureSwap_safe (laws : AtomicRootLaws root)
    (other : LegalActionWorkspaceDecoder root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    (root.asRefinementInterface.RankedAccepts decoder.ranking budget trace program ↔
      root.asRefinementInterface.RankedAccepts other.ranking budget trace program) ∧
    (root.asRefinementInterface.RankedAccepts decoder.ranking budget trace program →
      root.wellFormed program) ∧
    (root.budgetOK budget → root.wellFormed program →
      root.programCost program ≤ budget →
      root.asRefinementInterface.RankedAccepts decoder.ranking budget
        (root.encode program) program) := by
  constructor
  · rw [decoder.rankedAccepts_iff_accepts laws,
      other.rankedAccepts_iff_accepts laws]
  constructor
  · exact decoder.rankedAccepts_sound laws
  · exact decoder.wellFormed_rankedAccepts laws

end LegalActionWorkspaceDecoder

/-! ## Positive scorer fixture -/

/-- A score fixture that consumes all architecture fields.  It is only a
structural witness for inheritance, not a trained decoder. -/
noncomputable def betaDepthScoreFixture
    (goal : Mettapedia.GSLT.LanguageDef.Pure.Expr) :
    LegalActionWorkspaceDecoder (betaAtomicRoot goal) where
  Params := ℝ
  Gates := ℝ
  parameters := 2
  gates := 1 / 2
  recurrenceDepth := 3
  score := fun parameter gate depth _state action => by
    change RefineAction Nat Nat at action
    exact parameter * gate * (depth : ℝ) + (action.hole : ℝ) + (action.head : ℝ)

/-- Positive architectural fixture: the concrete Pure beta scorer inherits
ordering invariance from `betaAtomicLaws` without inspecting its scores. -/
theorem betaDepthScoreFixture_orderingInvariant
    (goal : Mettapedia.GSLT.LanguageDef.Pure.Expr)
    {budget : Nat}
    {trace : List (RefineAction (betaAtomicRoot goal).Hole (betaAtomicRoot goal).Head)}
    {program : (betaAtomicRoot goal).Program} :
    (betaAtomicRoot goal).asRefinementInterface.RankedAccepts
        (betaAtomicRoot goal).legalActions budget trace program ↔
      (betaAtomicRoot goal).asRefinementInterface.RankedAccepts
        (betaDepthScoreFixture goal).ranking budget trace program := by
  exact (betaDepthScoreFixture goal).orderingInvariant (betaAtomicLaws goal)

#print axioms openHole_address_injective
#print axioms openHole_address_total
#print axioms betaAtomicRoot_allocationSound
#print axioms moduloOne_not_injective_negativeExample
#print axioms LegalActionWorkspaceDecoder.rankedAccepts_iff_accepts
#print axioms LegalActionWorkspaceDecoder.orderingInvariant
#print axioms LegalActionWorkspaceDecoder.rankedAccepts_sound
#print axioms LegalActionWorkspaceDecoder.wellFormed_rankedAccepts
#print axioms LegalActionWorkspaceDecoder.architectureSwap_safe
#print axioms betaDepthScoreFixture_orderingInvariant

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
